"""The common spectral selection in Supplement S.7.6.

All three estimator labels execute this same fresh reconstruction at k=n.
Independent numerical validation is outside solver timing.
"""
import time


def solve_global(c, b, T):
    if c.k != c.n:
        raise ValueError('The common spectral solution requires k=n.')
    start = time.perf_counter()
    x = c.pls(b)
    stats = dict(solver='shared_global_spectral', converged=True,
                 status='converged', iterations=0, eta=0.,
                 gap=0., epsilon_Q=min(1., c.d / T),
                 certificate='Analytic common spectral minimizer; numerical gaps independently checked.',
                 pls_projection=dict(c.last_pls),
                 wall_seconds=time.perf_counter() - start)
    return x, stats
