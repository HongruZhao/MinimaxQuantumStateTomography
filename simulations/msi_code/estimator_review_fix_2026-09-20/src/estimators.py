"""Paper estimators with caller-derived accuracy and instance-bound validation.

These are floating-point checks, not interval-arithmetic certificates.
"""
import math
import time
import numpy as np
from scipy.linalg import eigh
from baseline import herm, trnorm, opnorm
from channel import Channel
from projections import Partial, scipy_nuclear
from global_solution import solve_global
import omd_tolerance
from solvers import fw
from run_identity import (accuracy_spec, problem_identity, source_hashes,
                          canonical_hash, array_hash)

METHODS = ('PLS', 'OMD', 'MW-PLS')


def solve_estimator(c, b, T, method, tol_factor=1., maxiter=300000,
                    max_seconds=1200., omd_maxiter=20000):
    if method not in METHODS:
        raise ValueError(method)
    request = accuracy_spec(c.d, T, tol_factor)
    problem = problem_identity(c, b, T, method)
    config = dict(tol_factor=float(tol_factor), maxiter=int(maxiter),
                  max_seconds=float(max_seconds), omd_maxiter=int(omd_maxiter))
    if maxiter < 1 or omd_maxiter < 1 or not math.isfinite(max_seconds) or max_seconds <= 0:
        raise ValueError('Iteration and time caps must be positive and finite.')
    if c.k == c.n:
        x, stats = solve_global(c, b, T)
    else:
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
            x, stats = omd_tolerance.solve(
                c, y, T, eta=request['eta'], regularized_tol_factor=tol_factor,
                original_tol_factor=tol_factor, maxiter=omd_maxiter, return_witness=True)
            stats.update(solver='omd_admm',
                         status='converged' if stats['converged'] else 'iteration_limit',
                         initialization='fresh PLS included', maxiter=omd_maxiter,
                         projection_calls=partial.calls)
        else:
            x, stats = fw(c, b, T, step_rule='line_search', initialization='identity',
                         tol_factor=tol_factor, maxiter=maxiter, max_seconds=max_seconds)
        stats['wall_seconds'] = time.perf_counter() - start
    stats.update(problem=problem, requested_accuracy=request, solver_configuration=config,
                 solver_configuration_sha256=canonical_hash(config),
                 source_sha256=source_hashes(), estimate_sha256=array_hash(x))
    if c.k == c.n:
        stats.update(epsilon_Q=request['epsilon_Q'],
                     original_gap_tolerance=request['original_gap_tolerance'],
                     regularized_gap_tolerance=request['regularized_gap_tolerance'])
    if '_dual_witness' in stats:
        stats['dual_witness_sha256'] = array_hash(stats['_dual_witness'])
    return x, stats


def reference_density_projection(a):
    """Full eigenspectrum and scalar bisection, separate from Partial.density."""
    w, v = eigh(herm(a), driver='evd')
    lo, hi = float(w[0] - 1.), float(w[-1])
    for _ in range(100):
        theta = (lo + hi) / 2
        if np.maximum(w - theta, 0).sum() > 1:
            lo = theta
        else:
            hi = theta
    weights = np.maximum(w - (lo + hi) / 2, 0)
    weights /= weights.sum()
    return herm((v * weights) @ v.conj().T)


def mathematical_validation(c, b, T, x, method, *, tol_factor=1., dual_witness=None, rho=None):
    """Recompute fitting conditions using the caller's d,T,tolerance only.

    This does not authenticate provenance. Historical arrays can be rechecked
    without claiming they were produced by the new source. Production code
    uses independent_validation, which additionally binds the result.
    """
    if method not in METHODS:
        raise ValueError(method)
    request = accuracy_spec(c.d, T, tol_factor)
    problem_identity(c, b, T, method)
    if np.shape(x) != (c.d, c.d) or not np.all(np.isfinite(x)):
        return dict(mathematical_checks_passed=False, reason='nonfinite_or_invalid_estimate')
    trace_error = float(abs(np.trace(x) - 1))
    hermitian_error = float(np.linalg.norm(x - x.conj().T))
    eigs = eigh(herm(x), eigvals_only=True, driver='evd')
    feasible = trace_error < 1e-9 and hermitian_error < 1e-9 and eigs[0] > -1e-9
    y = (c.d + 1) * b - np.eye(c.d)
    lx = c.apply(x)
    gradient = herm(lx - y)
    raw_mw_gap = float(np.vdot(gradient, x).real -
                       eigh(gradient, eigvals_only=True, driver='evd')[0])
    mw_gap = max(0., raw_mw_gap)
    objective = float(.5 * np.vdot(x, lx).real - np.vdot(y, x).real)
    result = dict(feasible=bool(feasible), trace_error=trace_error,
                  hermitian_error=hermitian_error, min_eigenvalue=float(eigs[0]),
                  mw_gap=mw_gap, raw_mw_gap=raw_mw_gap, mw_objective=objective,
                  omd_objective=opnorm(y - lx), independent_accuracy=request)
    passed = bool(feasible)
    if c.k == c.n:
        w = eigh(herm(y), eigvals_only=True, driver='evd')
        threshold = float(np.max((np.cumsum(w[::-1]) - 1) / np.arange(1, c.d + 1)))
        optimum = max(0., threshold, -float(w[0]))
        discrepancy = float(np.linalg.norm(x - reference_density_projection(y)))
        gap = max(0., result['omd_objective'] - optimum)
        result.update(global_omd_optimum=optimum, omd_gap=gap,
                      global_full_projection_difference=discrepancy)
        passed = (passed and discrepancy < 1e-8 and raw_mw_gap >= -1e-9
                  and gap <= min(1e-8, request['original_gap_tolerance'])
                  and mw_gap <= min(1e-8, request['epsilon_Q']))
    elif method == 'PLS':
        gold = reference_density_projection(c.apply(b, 'inverse'))
        discrepancy = float(np.linalg.norm(x - gold))
        result['pls_full_projection_difference'] = discrepancy
        passed = passed and discrepancy < 1e-8
    elif method == 'MW-PLS':
        result['stopping_threshold'] = request['epsilon_Q']
        passed = passed and raw_mw_gap >= -1e-9 and mw_gap <= request['epsilon_Q']
    elif dual_witness is None or np.shape(dual_witness) != (c.d, c.d) or not np.all(np.isfinite(dual_witness)):
        result['reason'] = 'missing_or_invalid_dual_witness'
        passed = False
    else:
        h = herm(dual_witness)
        h /= max(1., trnorm(h))
        lh = c.apply(h)
        linear = float(np.vdot(h, y).real)
        lower = max(0., linear - float(eigh(lh, eigvals_only=True, driver='evd')[-1]))
        eta = request['eta']
        v = reference_density_projection(lh / (2 * eta))
        regularized_lower = linear + eta * float(np.vdot(v, v).real) - float(np.vdot(lh, v).real)
        raw_gap = result['omd_objective'] - lower
        regularized_gap = result['omd_objective'] + eta * float(np.vdot(x, x).real) - regularized_lower
        result.update(omd_gap=max(0., raw_gap), regularized_gap=max(0., regularized_gap),
                      raw_omd_gap=raw_gap, raw_regularized_gap=regularized_gap,
                      omd_dual_lower=lower, dual_trace_norm=trnorm(h), checked_eta=eta,
                      stopping_threshold=request['original_gap_tolerance'])
        passed = (passed and raw_gap >= -1e-9 and regularized_gap >= -1e-9
                  and raw_gap <= request['original_gap_tolerance']
                  and regularized_gap <= request['regularized_gap_tolerance'])
    if rho is not None:
        result['trace_norm_error'] = trnorm(x - rho)
        result['frobenius_error'] = float(np.linalg.norm(x - rho))
    result['mathematical_checks_passed'] = bool(passed)
    return result


def independent_validation(c, b, T, x, method, stats, rho=None, *, tol_factor=1.):
    """Enforce caller-derived budgets and check the recorded problem identity."""
    request = accuracy_spec(c.d, T, tol_factor)
    result = mathematical_validation(c, b, T, x, method, tol_factor=tol_factor,
                                    dual_witness=stats.get('_dual_witness'), rho=rho)
    errors = []
    for name, expected in [('problem', problem_identity(c, b, T, method)),
                           ('requested_accuracy', request), ('source_sha256', source_hashes()),
                           ('estimate_sha256', array_hash(x))]:
        if stats.get(name) != expected:
            errors.append(name + '_mismatch')
    config = stats.get('solver_configuration')
    if not isinstance(config, dict) or config.get('tol_factor') != tol_factor:
        errors.append('solver_configuration_mismatch')
    else:
        try:
            if stats.get('solver_configuration_sha256') != canonical_hash(config):
                errors.append('solver_configuration_hash_mismatch')
        except (ValueError, TypeError):
            errors.append('invalid_solver_configuration')
    fields = []
    if method == 'MW-PLS':
        fields = ['epsilon_Q']
    elif method == 'OMD':
        fields = ['original_gap_tolerance', 'regularized_gap_tolerance']
        if stats.get('eta') != (0. if c.k == c.n else request['eta']):
            errors.append('eta_mismatch')
        if c.k != c.n and ('_dual_witness' not in stats or
                           stats.get('dual_witness_sha256') != array_hash(stats['_dual_witness'])):
            errors.append('dual_witness_mismatch')
    for field in fields:
        value = stats.get(field)
        if not isinstance(value, (int, float)) or not math.isfinite(value) or not 0 <= value <= request[field]:
            errors.append(field + '_invalid_or_exceeds_request')
        else:
            key = {'epsilon_Q': 'mw_gap', 'original_gap_tolerance': 'omd_gap',
                   'regularized_gap_tolerance': 'regularized_gap'}[field]
            if key == 'regularized_gap' and c.k == c.n:
                key = 'omd_gap'
            if result.get(key, float('inf')) > value:
                errors.append(field + '_not_met')
    result['metadata_errors'] = errors
    result['accepted'] = bool(result['mathematical_checks_passed'] and not errors
                              and stats.get('converged') is True)
    return result
