import angr
import claripy
import IPython
import itertools
from copy import copy

from . import ExplorationTechnique

class Skippy(ExplorationTechnique):

    def __init__(self, skippy_analysis):
        super(Skippy, self).__init__()
        self.skippy_analysis = skippy_analysis

    def setup(self, simgr):
        for hook in self.skippy_analysis.get_hooks():
            self.project.hook(hook.get_hook_addr(), hook=hook.skip_loop)

    def step_state(self, simgr, state, successor_func=None, **kwargs):
        if 'new_sat_checks' not in state.globals.keys():
            state.globals['new_sat_checks'] = []
        if 'sat_checks' not in state.globals.keys():
            state.globals['sat_checks'] = []

        before_sat_checkers = len(state.globals['sat_checks'])

        update = simgr.step_state(state, **kwargs)
        # IPython.embesd()
        for new_state in list(itertools.chain(*update.values())):
            new_state.globals['sat_checks'] = copy(new_state.globals['sat_checks'])
            if len(new_state.globals['new_sat_checks']) > 0:
                for sat_check in new_state.globals['new_sat_checks']:
                    sat_check.set_initial_state(state)
                    new_state.globals['sat_checks'].append(sat_check)
            new_state.globals['new_sat_checks'] = []

        return update
