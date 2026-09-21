"""Paper objectives, shared global shortcut, and independent diagnostics.

No solver receives the true state, its rank, eigenbasis, or spectrum.
Numerical stopping gaps use floating point, not interval arithmetic.
"""
import time
import numpy as np
from scipy.linalg import eigh
from baseline import herm, trnorm, opnorm
from channel import Channel
from projections import Partial, scipy_nuclear, scipy_density
from global_solution import solve_global
import omd_tolerance
from solvers import fw, full_gap, objective, inner

METHODS = ('PLS', 'OMD', 'MW-PLS')


def solve_estimator(c, b, T, method, tol_factor=1., maxiter=300000,
                    max_seconds=1200., omd_maxiter=20000):
    if method not in METHODS:
        raise ValueError(method)
    if not 0 < tol_factor <= 1 or T < 1:
        raise ValueError('Use T>=1 and a positive tolerance factor at most one.')
    # Dispatch BEFORE selecting an iterative solver. The timed code is identical.
    if c.k == c.n:
        return solve_global(c, b, T)
    start = time.perf_counter()
    if method == 'PLS':
        x = c.pls(b)
        stats = dict(solver='spectral_pls', status='converged', converged=True,
                     iterations=0, pls_projection=dict(c.last_pls))
    elif method == 'OMD':
        partial = Partial()
        omd_tolerance.project_density = partial.density
        omd_tolerance.nuclear_project = scipy_nuclear
        y = (c.d + 1) * b - np.eye(c.d)
        x, stats = omd_tolerance.solve(c, y, T, regfrac=tol_factor,
                                      tolfrac=tol_factor, maxiter=omd_maxiter,
                                      return_witness=True)
        gamma = min(1., np.sqrt(c.d / T))
        stats.update(solver='omd_admm', eta=.005 * gamma,
                     original_gap_tolerance=tol_factor * gamma,
                     regularized_gap_tolerance=tol_factor * gamma,
                     status='converged' if stats['converged'] else 'iteration_limit',
                     initialization='fresh PLS included',
                     maxiter=omd_maxiter, projection_calls=partial.calls)
    else:
        x, stats = fw(c, b, T, step_rule='line_search', initialization='identity',
                      tol_factor=tol_factor, maxiter=maxiter, max_seconds=max_seconds)
    stats['wall_seconds'] = time.perf_counter() - start
    return x, stats


def independent_validation(c, b, T, x, method, stats, rho=None):
    """Recompute full spectra and the original objective on the returned state."""
    trace_error = float(abs(np.trace(x) - 1))
    hermitian_error = float(np.linalg.norm(x - x.conj().T))
    eigs = eigh(herm(x), eigvals_only=True, driver='evd')
    feasible = trace_error < 1e-9 and hermitian_error < 1e-9 and eigs[0] > -1e-9
    y = (c.d + 1) * b - np.eye(c.d)
    lx = c.apply(x)
    mw_gap, _, _ = full_gap(c, x, y)
    result = dict(feasible=bool(feasible), trace_error=trace_error,
                  hermitian_error=hermitian_error, min_eigenvalue=float(eigs[0]),
                  mw_gap=mw_gap, mw_objective=objective(x, lx, y),
                  omd_objective=opnorm(y - lx))
    accepted = feasible and bool(stats['converged'])
    if c.k == c.n:
        w = eigh(herm(y), eigvals_only=True, driver='evd')
        threshold = float(np.max((np.cumsum(w[::-1]) - 1) / np.arange(1, c.d + 1)))
        optimum = max(0., threshold, -float(w[0]))
        gold = scipy_density(y, driver='evd')
        discrepancy = float(np.linalg.norm(x - gold))
        gap = max(0., result['omd_objective'] - optimum)
        result.update(global_omd_optimum=optimum, omd_gap=gap,
                      global_full_projection_difference=discrepancy)
        accepted = accepted and discrepancy < 1e-8 and gap < 1e-8 and mw_gap < 1e-8
    elif method == 'PLS':
        gold = scipy_density(c.apply(b, 'inverse'), driver='evd')
        discrepancy = float(np.linalg.norm(x - gold))
        result['pls_full_projection_difference'] = discrepancy
        accepted = accepted and discrepancy < 1e-8
    elif method == 'MW-PLS':
        result['stopping_threshold'] = stats['epsilon_Q']
        # Numerical slack is recorded; do not hide a failed statistical threshold.
        accepted = accepted and mw_gap <= stats['epsilon_Q'] + 1e-11
    else:
        raw_dual = stats['_dual_witness']
        h = herm(raw_dual) / max(1., trnorm(raw_dual))
        lh = c.apply(h)
        linear = inner(h, y)
        lower = max(0., linear - float(eigh(lh, eigvals_only=True, driver='evd')[-1]))
        eta = stats['eta']
        v = scipy_density(lh / (2 * eta), driver='evd')
        regularized_lower = linear + eta * inner(v, v) - inner(lh, v)
        raw_gap = result['omd_objective'] - lower
        regularized_gap = result['omd_objective'] + eta * inner(x, x) - regularized_lower
        result.update(omd_gap=max(0., raw_gap), regularized_gap=max(0., regularized_gap),
                      omd_dual_lower=lower, dual_trace_norm=trnorm(h),
                      stopping_threshold=stats['original_gap_tolerance'])
        accepted = (accepted and raw_gap >= -1e-9 and regularized_gap >= -1e-9
                    and raw_gap <= stats['original_gap_tolerance'] + 1e-11
                    and regularized_gap <= stats['regularized_gap_tolerance'] + 1e-11)
    if rho is not None:
        result['trace_norm_error'] = trnorm(x - rho)
        result['frobenius_error'] = float(np.linalg.norm(x - rho))
    result['accepted'] = bool(accepted)
    return result
