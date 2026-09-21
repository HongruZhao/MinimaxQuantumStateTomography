"""Existing Pauli channel and rank-free checked spectral PLS projection."""
import numpy as np
from baseline import FastChannel
from projections import Partial


class Channel(FastChannel):
    def pls(self, b):
        partial = Partial()
        if self.k == self.n:
            a = (self.d + 1) * b - np.eye(self.d)
        else:
            a = self.apply(b, 'inverse')
        x = partial.density(a)
        self.last_pls = dict(expansions=partial.expansions, active_rank=partial.ranks[-1],
                             projection_calls=partial.calls)
        return x
