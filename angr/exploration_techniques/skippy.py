import angr
import claripy
import IPython
import itertools
from copy import copy

from . import ExplorationTechnique
from ..analyses.skippy import SkippySatCheckerChain

class Skippy(ExplorationTechnique):

    def __init__(self, skippy_analysis):
        super(Skippy, self).__init__()
        self.skippy_analysis = skippy_analysis

    def setup(self, simgr):
        for hook in self.skippy_analysis.get_hooks():
            self.project.hook(hook.get_hook_addr(), hook=hook.skip_loop)

    def step_state(self, simgr, state, successor_func=None, **kwargs):
        if 'new_sat_check' not in state.globals.keys():
            state.globals['new_sat_check'] = None
        if 'sat_chain' not in state.globals.keys():
            state.globals['sat_chain'] = None

        update = simgr.step_state(state, **kwargs)
        # IPython.embesd()
        for new_state in list(itertools.chain(*update.values())):
            # new_state.globals['sat_checks'] = copy(new_state.globals['sat_checks'])
            if new_state.globals['new_sat_check'] is not None:
                sat_check = new_state.globals['new_sat_check']
                sat_check.set_initial_state(state)
                new_state.globals['sat_chain'] = SkippySatCheckerChain(sat_check, prev_chain_link=new_state.globals['sat_chain'])
            new_state.globals['new_sat_check'] = None

        return update
