"""Independent Pauli-label propagation at the actual paper dimension."""
from pathlib import Path
import sys
import json
import numpy as np
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))
from channel import Channel


def selected_multipliers(n, k, labels):
    count = 4**n
    dist = np.zeros((len(labels), count))
    dist[np.arange(len(labels)), labels] = 1
    dist = dist.reshape((len(labels),) + (4,) * n)
    blocks = [[(j*k + k//2 + a) % n for a in range(k)] for j in range(n//k)]
    blocks += [[j*k+a for a in range(k)] for j in range(n//k)]
    for block in blocks:
        axes = [0] + [1+q for q in block] + [1+q for q in range(n) if q not in block]
        a = dist.transpose(axes).reshape(len(labels), 4**k, -1).copy()
        a[:, 1:, :] = a[:, 1:, :].sum(axis=1, keepdims=True)/(4**k-1)
        dist = a.reshape((len(labels),) + (4,)*n).transpose(np.argsort(axes))
    indices = np.arange(count)
    diagonal = np.ones(count, dtype=bool)
    for q in range(n):
        digit = (indices >> (2*q)) & 3
        diagonal &= (digit == 0) | (digit == 3)
    return dist.reshape(len(labels), count)[:, diagonal].sum(axis=1)


if __name__ == '__main__':
    rng = np.random.default_rng(20260920123)
    labels = np.unique(np.r_[0, 4**8-1, [1 << (2*j) for j in range(8)],
                            rng.integers(4**8, size=54)]).astype(int)
    checks = []
    for k in [2, 4, 8]:
        c = Channel(8, k)
        expected = selected_multipliers(8, k, labels)
        error = float(np.max(abs(c.m.ravel()[labels] - expected)))
        assert error < 1e-12
        checks.append(dict(n=8, k=k, number_of_labels=len(labels),
                           max_absolute_difference=error, passed=True))
    result = dict(status='passed', labels=labels.tolist(), checks=checks)
    (ROOT/'reports/n8_channel_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
