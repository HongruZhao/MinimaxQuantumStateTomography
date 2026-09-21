"""Problem identity and fail-closed reuse of numerical results."""
import hashlib
import json
import math
from pathlib import Path

import numpy as np

SRC = Path(__file__).resolve().parent


class StaleResultError(RuntimeError):
    pass


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_hashes():
    paths = sorted(SRC.glob('*.py')) + sorted(SRC.glob('*.npz'))
    return {p.name: file_hash(p) for p in paths}


def array_hash(value):
    a = np.ascontiguousarray(value, dtype=np.complex128)
    h = hashlib.sha256()
    h.update(json.dumps(list(a.shape)).encode())
    h.update(a.tobytes())
    return h.hexdigest()


def accuracy_spec(d, T, tol_factor=1.):
    if isinstance(T, bool) or not isinstance(T, (int, np.integer)) or T < 1:
        raise ValueError('T must be a positive integer.')
    if not math.isfinite(tol_factor) or not 0 < tol_factor <= 1:
        raise ValueError('tol_factor must be finite and in (0,1].')
    gamma = min(1., math.sqrt(d / int(T)))
    epsilon = min(1., d / int(T))
    return dict(tol_factor=float(tol_factor), paper_omd_limit=gamma,
                paper_mw_limit=epsilon, original_gap_tolerance=tol_factor * gamma,
                regularized_gap_tolerance=tol_factor * gamma,
                epsilon_Q=tol_factor * epsilon, eta=.005 * tol_factor * gamma)


def problem_identity(c, b, T, method):
    if np.shape(b) != (c.d, c.d) or not np.all(np.isfinite(b)):
        raise ValueError('The empirical mean must be a finite d-by-d matrix.')
    return dict(n=int(c.n), k=int(c.k), d=int(c.d), T=int(T), method=method,
                empirical_mean_sha256=array_hash(b))


def cache_identity(config, inputs):
    identity = dict(schema=2, source_sha256=source_hashes(),
                    configuration=config, inputs=inputs)
    identity['fingerprint'] = canonical_hash(identity)
    return identity


def check_cached_result(status_path, identity):
    """Return a completed matching result; reject stale/incomplete identities.

    A mismatch never deletes or overwrites a prior result. Use a new run name
    or revision directory to recompute with changed code/configuration/data.
    """
    path = Path(status_path)
    if not path.exists():
        return None
    prior = json.loads(path.read_text())
    if prior.get('cache_identity') != identity:
        raise StaleResultError('Source/configuration/input mismatch at ' + str(path) +
                               '; use a new run name or revision directory.')
    if prior.get('status') != 'complete':
        return None
    claimed = prior.get('result_sha256')
    if claimed != canonical_hash({k: v for k, v in prior.items() if k != 'result_sha256'}):
        raise StaleResultError('Completed summary missing or inconsistent digest: ' + str(path))
    artifacts = prior.get('artifact_sha256')
    if not isinstance(artifacts, dict) or not artifacts:
        raise StaleResultError('Completed result has no saved-output hashes: ' + str(path))
    for name, expected in artifacts.items():
        member = Path(name)
        if member.is_absolute() or '..' in member.parts:
            raise StaleResultError('Invalid cached output path.')
        target = path.parent / member
        if not target.is_file() or file_hash(target) != expected:
            raise StaleResultError('Cached output missing or modified: ' + str(target))
    return prior


def artifact_hashes(folder, patterns=('*.npz',)):
    root = Path(folder)
    return {str(p.relative_to(root)): file_hash(p)
            for pattern in patterns for p in sorted(root.glob(pattern)) if p.is_file()}


def seal_result(row):
    row['result_sha256'] = canonical_hash({k: v for k, v in row.items() if k != 'result_sha256'})
    return row
