"""Independent Born datasets and an exact finite global-projector sampler."""
from itertools import combinations, product
from pathlib import Path
import hashlib
import numpy as np
from baseline import herm
from large_simulation import records as periodic_records


def state(n, family):
    d = 2 ** n
    eigenvalues = np.zeros(d)
    if family in ('rank8_diagonal', 'rank8_rotated'):
        eigenvalues[:min(8, d)] = 1. / min(8, d)
    elif family == 'polynomial_rotated':
        eigenvalues = np.arange(1, d + 1, dtype=float) ** -2
        eigenvalues /= eigenvalues.sum()
    else:
        raise ValueError(family)
    v = np.eye(d, dtype=complex)
    if family.endswith('rotated'):
        rng = np.random.default_rng([20260920, n, 992])
        a = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        v, r = np.linalg.qr(a)
        v = v * (np.diag(r) / np.abs(np.diag(r)))
    return herm((v * eigenvalues) @ v.conj().T), v, eigenvalues


def stabilizer_states(n):
    """All stabilizer rays via canonical affine supports and quadratic phases.

    For each binary subspace in reduced row-echelon form, choose its unique
    coset representatives (zero pivot coordinates). On r free binary variables
    enumerate phases i^(sum a_j t_j) (-1)^(sum b_ij t_i t_j). The amplitude at
    t=0 fixes global phase. This is used only for small global-design studies.
    """
    if not 1 <= n <= 4:
        raise ValueError('This explicit reference sampler is limited to n<=4.')
    vectors = []
    d = 2 ** n
    for rank in range(n + 1):
        for pivots in combinations(range(n), rank):
            free = [j for j in range(n) if j not in pivots]
            slots = [(i, j) for i, pivot in enumerate(pivots) for j in free if j > pivot]
            for entries in product((0, 1), repeat=len(slots)):
                rows = [1 << p for p in pivots]
                for (i, j), bit in zip(slots, entries):
                    rows[i] |= bit << j
                bits = np.array(list(product((0, 1), repeat=rank)), dtype=int).reshape(2 ** rank, rank)
                positions = np.zeros(2 ** rank, dtype=int)
                for i, row in enumerate(rows):
                    positions ^= bits[:, i] * row
                pairs = list(combinations(range(rank), 2))
                phase_vectors = []
                for linear in product(range(4), repeat=rank):
                    base = bits @ np.asarray(linear, dtype=int)
                    for quadratic in product((0, 1), repeat=len(pairs)):
                        exponent = base.copy()
                        for (i, j), bit in zip(pairs, quadratic):
                            exponent += 2 * bit * bits[:, i] * bits[:, j]
                        phase_vectors.append((1j ** (exponent % 4)) / np.sqrt(2 ** rank))
                phases = np.asarray(phase_vectors)
                for offset_bits in product((0, 1), repeat=len(free)):
                    offset = sum(bit << j for bit, j in zip(offset_bits, free))
                    block = np.zeros((len(phases), d), dtype=complex)
                    block[:, positions ^ offset] = phases
                    vectors.append(block)
    states = np.concatenate(vectors)
    expected = 2 ** n * int(np.prod([2 ** j + 1 for j in range(1, n + 1)]))
    assert len(states) == expected
    return states


def global_records(n, rho, sizes, seed, cache_dir=None):
    cache = Path(cache_dir) / ('stabilizer_states_n%d.npz' % n) if cache_dir else None
    if cache is not None and cache.exists():
        with np.load(cache) as data:
            vectors = data['vectors']
    else:
        vectors = stabilizer_states(n)
    d = 2 ** n
    probabilities = (d / len(vectors)) * np.einsum('bi,ij,bj->b', vectors.conj(), rho, vectors).real
    assert probabilities.min() > -1e-13 and abs(probabilities.sum() - 1) < 1e-11
    probabilities = np.maximum(probabilities, 0)
    probabilities /= probabilities.sum()
    rng = np.random.default_rng(seed)
    counts = np.zeros(len(vectors), dtype=np.int64)
    means, all_counts = [], []
    previous = 0
    for target in sizes:
        counts += rng.multinomial(int(target - previous), probabilities)
        means.append(herm((vectors.T * counts) @ vectors.conj()) / target)
        all_counts.append(counts.copy())
        previous = target
    info = dict(sampling='Exact global-Clifford Born projector law, aggregated multinomial counts',
                number_of_reference_projectors=len(vectors),
                vector_sha256=hashlib.sha256(vectors.tobytes()).hexdigest())
    return np.asarray(means), np.asarray(all_counts), info


def sample_means(n, k, family, sizes, rep, cache_dir=None):
    rho, v, eigenvalues = state(n, family)
    family_code = {'rank8_diagonal': 0, 'rank8_rotated': 1, 'polynomial_rotated': 2}[family]
    seed = [20260920, n, k, family_code, rep]
    if k == n:
        means, counts, info = global_records(n, rho, sizes, seed, cache_dir)
    elif k == 2:
        means = periodic_records(n, v, eigenvalues, sizes, seed)
        counts = np.empty((0,), dtype=np.int64)
        info = dict(sampling='Original periodic two-layer Born sampler, independent uniform two-qubit Clifford draws')
    else:
        raise ValueError('This new convergence study uses k=2 or the global design.')
    info.update(seed=seed, nested_prefixes=True)
    return rho, means, counts, info
