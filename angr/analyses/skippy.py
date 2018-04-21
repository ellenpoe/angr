import angr
import claripy
from . import Analysis
import IPython
from copy import copy, deepcopy
import itertools

def add_constraints(solver, constraints):
    solver.add(*constraints)

class SkippyMemWrite:
    def __init__(self, addr, size, rbp=None):
        self.addr = addr
        self.size = size
        self.rbp = rbp
        self.offset = None

    def clobber(self, state, memory_bank):
        addr = self.addr
        if self.rbp is not None:
            addr = addr.replace(self.rbp, state.regs.rbp.ast)
        memcell = state.mem[addr]
        clobber_bvs = claripy.BVS("clobber_bvs", self.size*8)
        if self.size == 1:
            memcell.uint8_t = clobber_bvs
        elif self.size == 2:
            memcell.uint16_t = clobber_bvs
        elif self.size == 4:
            memcell.uint32_t = clobber_bvs
        elif self.size == 8:
            memcell.uint64_t = clobber_bvs
        else:
            print "skippy doesn't know how to deal with weird-sized writes"
            return None

        if self.offset is not None:
            state.se.add(clobber_bvs == self.offset + state.memory.load(addr=addr, size=self.size))
        return addr, clobber_bvs

    def set_offset(self, offset):
        self.offset = offset

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
            all_starting_constraints = [None]

        for starting_constraints in all_starting_constraints:
            constraints = []
            for constraint_set in self.my_sat_checker.check_satisfiability(proj, state_to_check, starting_constraints):
                if starting_constraints is not None:
                    yield claripy.And(claripy.And(*constraint_set), starting_constraints)
                else:
                    yield claripy.And(*constraint_set)

        return

class SkippySatChecker:
    def __init__(self, clobbered_mem_map, clobbered_reg_map, loop, rbp, exit_addr):
        self.initial_state = None
        self.clobbered_mem_map = clobbered_mem_map
        self.clobbered_reg_map = clobbered_reg_map
        self.loop = loop
        self.rbp = rbp
        self.exit_addr = exit_addr
        self.exit_state_cache = {}

    def set_initial_state(self, initial_state):
        self.initial_state = initial_state;

    def check_satisfiability(self, proj, state_to_check, initial_constraints):
        if self.initial_state is None:
            print "didn't have initial state!"
            raise StopIteration

        initial_state = self.initial_state.copy()

        if state_to_check not in self.exit_state_cache.keys():
            self.exit_state_cache[state_to_check] = []

        all_initial_constraints = state_to_check.se.constraints + [claripy.Not(claripy.Or(*self.exit_state_cache[state_to_check]))]
        if initial_constraints is not None:
            all_initial_constraints += [initial_constraints]
        add_constraints(initial_state.se, all_initial_constraints)
        self.exit_state_cache[state_to_check].append(all_initial_constraints)

        print 'trying to satisfy', state_to_check.posix.dump_fd(0).strip()
        print 'using constrained input', initial_state.posix.dump_fd(0).strip()

        initial_state.globals['no-skip'] = True

        def exit_action(state):
            state.globals['sat-exiting'] = state.addr
        exit_blocks = [finish.addr for start,finish in self.loop.break_edges]
        for addr in exit_blocks:
            initial_state.inspect.b('instruction', when=angr.BP_BEFORE, instruction=addr, action=exit_action)

        simgr = proj.factory.simgr(initial_state, veritesting=True)

        while len(simgr.active) > 0:
            simgr.step()
            for state in simgr.active:
                if 'sat-exiting' not in state.globals.keys():
                    continue
                if state.globals['sat-exiting'] != self.exit_addr:
                    simgr.drop(filter_func=lambda s: s == state)
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

                initial_state_constraints = frozenset(self.initial_state.se.constraints)
                new_constraints = [c for c in candidate.se.constraints if c not in initial_state_constraints]

                to_yield = frozenset(new_constraints + value_constraints)

                add_constraints(final_state.se, to_yield)
                if initial_constraints is not None:
                    final_state.se.add(initial_constraints)

                if final_state.se.satisfiable():
                    yield to_yield

                simgr.drop(filter_func=lambda s: s == state)

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

        try:
            for mem_write in self.mem_writes:
                addr, val = mem_write.clobber(state, state.mem)
                clobbered_mem_map[addr] = val
            for reg_write in self.reg_writes:
                addr, val = reg_write.clobber(state, state.registers.mem)
                clobbered_reg_map[addr] = val
        except Exception as e:
            print 'exception during clobbering', e

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

    def __init__(self, loop_finder, loops_to_skip):
        super(Skippy, self).__init__()
        self.loop_finder = loop_finder
        self.hooks = []
        for loop in loops_to_skip:
            analysis_result = self._analyze_loop(loop)
            if analysis_result is not None:
                mem_writes, reg_writes, rbp = analysis_result
                self.hooks.append(SkippyHook(loop, rbp, mem_writes, reg_writes))

    def get_hooks(self):
        return self.hooks

    def _analyze_loop(self, loop):
        initial_state = self.project.factory.entry_state(addr=loop.entry.addr)
        const_rbp = claripy.BVS("const_rbp", initial_state.regs.rbp.size())
        initial_state_rbp = initial_state.regs.rbp

        exit_blocks = [finish.addr for start,finish in loop.break_edges]
        continue_blocks = [start.addr for start,finish in loop.continue_edges]

        mem_writes = list()
        reg_writes = list()

        written_mem_addresses = set()
        written_reg_addresses = set()

        def write_action(state):
            if state.inspect.mem_write_address in written_mem_addresses:
                return
            else:
                written_mem_addresses.add(state.inspect.mem_write_address)

            rbp_offsets = state.se.eval_upto(initial_state_rbp - state.inspect.mem_write_address, n=2)
            rbp_offset = rbp_offsets[0]

            if abs(rbp_offset) < 0x10000:
                addr = const_rbp - rbp_offset
            else:
                return
                # addr = state.inspect.mem_write_address
            # print addr, state.inspect.mem_write_address
            size = state.inspect.mem_write_length
            if not size.concrete:
                print "skippy doesn't know how to deal with symbolic-size writes"
                return

            if self._concrete_or_rbp(const_rbp, addr):
                mem_writes.append(SkippyMemWrite(addr, size.args[0], rbp=const_rbp))
            else:
                print "skippy doesn't know how to deal with symbolic writes yet"

        def reg_write_action(state):
            if state.inspect.reg_write_offset in written_reg_addresses:
                return
            else:
                written_reg_addresses.add(state.inspect.reg_write_offset)

            addr = state.inspect.reg_write_offset
            reg_writes.append(SkippyMemWrite(addr, 8)) # Only support x86_64 for now

        def continuing(state):
            state.globals['continuing'] = True

        def exiting(state):
            state.globals['exiting'] = True

        initial_state.inspect.b('mem_write', when=angr.BP_AFTER, action=write_action)
        initial_state.inspect.b('reg_write', when=angr.BP_AFTER, action=reg_write_action)
        for addr in continue_blocks:
            initial_state.inspect.b('instruction', when=angr.BP_BEFORE, instruction=addr, action=continuing)
        for addr in exit_blocks:
            initial_state.inspect.b('instruction', when=angr.BP_BEFORE, instruction=addr, action=exiting)

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

        simgr = self.project.factory.simgr(initial_state)
        while len(simgr.active) != 0:
            simgr.step(filter_func=filter_func_rough, num_inst=1)
        while len(simgr.stashes['exiting']) != 0:
            simgr.step(filter_func=filter_func_fine, num_inst=1, stash='exiting')

        return mem_writes, reg_writes, const_rbp

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
