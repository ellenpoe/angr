import angr
import claripy
from . import Analysis
import IPython
from copy import copy, deepcopy

def add_constraints(solver, constraints):
    solver.add(*constraints)

class SkippyMemWrite:
    def __init__(self, addr, size, rbp=None):
        self.addr = addr
        self.size = size
        self.rbp = rbp

    def clobber(self, state, memory_bank):
        addr = self.addr
        if self.rbp is not None:
            addr = addr.replace(self.rbp, state.regs.rbp.ast)
        memcell = state.mem[addr]
        clobber_bvs = claripy.BVS("clobber_bvs", self.size*8)
        if self.size == 4:
            memcell.uint32_t = clobber_bvs
        elif self.size == 8:
            memcell.uint64_t = clobber_bvs
        else:
            print "skippy doesn't know how to deal with weird-sized writes"
            return None
        return clobber_bvs

class SkippySatCheckerChain:
    def __init__(self, my_sat_checker, prev_chain_link=None):
        self.my_sat_checker = my_sat_checker
        self.prev_chain_link = prev_chain_link
        self.counter = 0
        pass

    def is_satisfiable(self, proj, state_to_check):
        for _ in self.check_satisfiability(proj, state_to_check):
            return True;
        return False;

    def check_satisfiability(self, proj, state_to_check):
        if self.prev_chain_link is not None:
            all_starting_constraints = self.prev_chain_link.check_satisfiability(proj, state_to_check)
        else:
            all_starting_constraints = [frozenset()]

        for starting_constraints in all_starting_constraints:
            for constraints in self.my_sat_checker.check_satisfiability(proj, state_to_check, starting_constraints):
                yield frozenset(constraints | starting_constraints)

        return

class SkippySatChecker:
    def __init__(self, clobbered_mem_map, clobbered_reg_map, loop, rbp, exit_addr):
        self.initial_state = None
        self.clobbered_mem_map = clobbered_mem_map
        self.clobbered_reg_map = clobbered_reg_map
        self.loop = loop
        self.rbp = rbp
        self.exit_addr = exit_addr

    def set_initial_state(self, initial_state):
        self.initial_state = initial_state;

    def check_satisfiability(self, proj, state_to_check, initial_constraints):
        if self.initial_state is None:
            print "didn't have initial state!"
            raise StopIteration
        initial_state = self.initial_state.copy()

        initial_state.se.simplify()
        add_constraints(initial_state.se, state_to_check.se.constraints)
        add_constraints(initial_state.se, initial_constraints)
        initial_state.se.simplify()

        initial_state.globals['no-skip'] = True

        def exit_action(state):
            state.globals['sat-exiting'] = state.addr
        exit_blocks = [finish.addr for start,finish in self.loop.break_edges]
        for addr in exit_blocks:
            initial_state.inspect.b('instruction', when=angr.BP_BEFORE, instruction=addr, action=exit_action)

        simgr = proj.factory.simgr(initial_state)

        while len(simgr.active) > 0 and len(simgr.active) < 10:
            simgr.step()
            for state in simgr.active:
                if 'sat-exiting' not in state.globals.keys():
                    continue
                if state.globals['sat-exiting'] != self.exit_addr:
                    simgr.stash(filter_func=lambda s: s == state)
                    continue

                # print 'output:', state.posix.dump_fd(0).strip()
                candidate = state.copy()
                final_state = state_to_check.copy()

                value_constraints = []
                clobbered_vals = []
                for addr, clobbered_val in self.clobbered_mem_map.iteritems():
                    memcell = candidate.memory.load(addr=addr.replace(self.rbp, self.initial_state.regs.rbp), size=clobbered_val.size()/8)
                    value_constraints.append(memcell == clobbered_val)
                    clobbered_vals.append(clobbered_val)

                for addr, clobbered_val in self.clobbered_reg_map.iteritems():
                    value_constraints.append(candidate.registers.mem[addr].object == clobbered_val)
                    clobbered_vals.append(clobbered_val)

                final_state_constraints = frozenset(final_state.se.constraints)
                new_constraints = [c for c in candidate.se.constraints if c not in final_state_constraints]

                # final_state.se.simplify()
                add_constraints(final_state.se, value_constraints)
                add_constraints(final_state.se, new_constraints)
                # final_state.se.simplify()
                # print new_constraints
                if final_state.se.satisfiable():
                    yield frozenset(new_constraints + value_constraints)
                simgr.stash(filter_func=lambda s: s == state)

    def _value_in_ast(self, value, ast):
        if isinstance(value, (int, long)):
            return False
        elif ast is value:
            return True
        elif ast.depth > 1:
            return any([self._value_in_ast(arg, value) for arg in ast.args])
        else:
            return False

    def _constraints_involving_vals(self, constraints, values):
        for constraint in constraints:
            for value in values:
                if self._value_in_ast(value, constraint):
                    constraints.append(constraint)
        return constraints

class SkippyHook:
    def __init__(self, loop, rbp, mem_writes, reg_writes):
        self.loop = loop
        self.rbp = rbp
        self.mem_writes = mem_writes
        self.reg_writes = reg_writes

    def get_hook_addr(self):
        return self.loop.entry.addr

    def skip_loop(self, state):
        if 'no-skip' in state.globals.keys():
            print 'not skipping'
            return

        clobbered_mem_map = {}
        clobbered_reg_map = {}

        for mem_write in self.mem_writes:
            clobbered_mem_map[mem_write.addr] = mem_write.clobber(state, state.mem)
        for reg_write in self.reg_writes:
            clobbered_reg_map[reg_write.addr] = reg_write.clobber(state, state.registers.mem)

        successors = []
        for start, finish in self.loop.break_edges:
            new_state = state.copy()
            new_state.regs.ip = finish.addr
            new_state.scratch.guard = new_state.se.true
            new_state.history.jumpkind = 'Ijk_Boring'

            new_state.globals['new_sat_check'] = SkippySatChecker(clobbered_mem_map, clobbered_reg_map, self.loop, self.rbp, finish.addr)

            successors.append(new_state)

        return successors

class Skippy(Analysis):

    def __init__(self, loop_finder, loop_to_skip):
        super(Skippy, self).__init__()
        self.loop_finder = loop_finder
        self.hooks = []
        for loop in [loop_to_skip]:
            analysis_result = self._analyze_loop(loop)
            if analysis_result is not None:
                mem_writes, reg_writes, rbp = analysis_result
                self.hooks.append(SkippyHook(loop, rbp, mem_writes, reg_writes))

    def get_hooks(self):
        return self.hooks

    def _analyze_loop(self, loop):
        state = self.project.factory.blank_state(addr=loop.entry.addr)
        rbp = claripy.BVS("const_rbp", state.regs.rbp.size())

        exit_blocks = [finish.addr for start,finish in loop.break_edges]
        continue_blocks = [start.addr for start,finish in loop.continue_edges]

        mem_writes = set()
        reg_writes = set()

        def write_action(state):
            addr = state.inspect.mem_write_address.replace(state.regs.rbp, rbp)
            size = state.inspect.mem_write_length
            if not size.concrete:
                print "skippy doesn't know how to deal with symbolic-size writes"
                return

            if self._concrete_or_rbp(rbp, addr):
                mem_writes.add(SkippyMemWrite(addr, size.args[0], rbp=rbp))
            else:
                print "skippy doesn't know how to deal with symbolic writes yet"

        def reg_write_action(state):
            addr = state.inspect.reg_write_offset
            reg_writes.add(SkippyMemWrite(addr, 8)) # Only support x86_64 for now

        def continuing(state):
            state.globals['continuing'] = True

        def exiting(state):
            state.globals['exiting'] = True

        state.inspect.b('mem_write', when=angr.BP_AFTER, action=write_action)
        state.inspect.b('reg_write', when=angr.BP_AFTER, action=reg_write_action)
        for addr in continue_blocks:
            state.inspect.b('instruction', when=angr.BP_BEFORE, instruction=addr, action=continuing)
        for addr in exit_blocks:
            state.inspect.b('instruction', when=angr.BP_BEFORE, instruction=addr, action=exiting)

        whitelist = set()
        for block in loop.body_nodes:
            whitelist |= set(range(block.addr, block.addr + block.size))

        def filter_func_rough(state):
            if 'exiting' in state.globals.keys():
                return 'exiting'
            if 'continuing' in state.globals.keys():
                return 'continuing'
            return None

        def filter_func_fine(state):
            for start,finish in loop.break_edges:
                if state.addr >= finish.addr and state.addr < finish.addr+finish.size:
                    return None
            return 'exited'
        simgr = self.project.factory.simgr(state)
        while len(simgr.active) != 0:
            simgr.step(filter_func=filter_func_rough, num_inst=1)
        while len(simgr.stashes['exiting']) != 0:
            simgr.step(filter_func=filter_func_fine, num_inst=1, stash='exiting')

        return mem_writes, reg_writes, rbp

    def _concrete_or_rbp(self, rbp, val):
        if isinstance(val, (int, long)):
            return True
        elif val.concrete:
            return True
        elif val is rbp:
            return True
        elif val.depth > 1:
            return all([self._concrete_or_rbp(rbp, arg) for arg in val.args])
        else:
            return False

from angr.analyses import AnalysesHub
AnalysesHub.register_default('Skippy', Skippy)
