"""Check preserved arrays for complete paired records without rerunning solvers."""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np


def file_hash(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def audit(root):
    checked = []
    files = {}
    max_error_disagreement = 0.
    for phase in ['main_100_phase_a', 'main_100_phase_b']:
        for path in sorted((root / phase).glob('case_*/rep_*/summary.json')):
            row = json.loads(path.read_text())
            if row['status'] != 'complete':
                continue
            d = row['d']
            assert 8 <= d <= 1024
            folder = path.parent
            source = folder / 'input.npz'
            with np.load(source, allow_pickle=False) as data:
                mean = data['mean']
                assert (int(data['n']), int(data['k']), int(data['T'])) == (row['n'], row['k'], row['T'])
                assert mean.shape == (d, d) and np.isfinite(mean).all()
                assert hashlib.sha256(mean.tobytes()).hexdigest() == row['input_sha256']
                assert abs(np.trace(mean) - 1) < 1e-9
            files[str(source.relative_to(root))] = file_hash(source)
            assert len(row['methods']) == 7
            for name, method in row['methods'].items():
                assert method['status'] == 'complete'
                estimate = folder / (name + '.npz')
                with np.load(estimate, allow_pickle=False) as data:
                    x = data['estimate']
                    assert x.shape == (d, d) and np.isfinite(x).all()
                    assert abs(np.trace(x) - 1) < 1e-9
                    assert np.linalg.norm(x - x.conj().T) < 1e-9
                    diff = x.copy()
                    indices = np.arange(8)
                    diff[indices, indices] -= 1 / 8
                    error_squared = float(np.vdot(diff, diff).real)
                    delta = abs(error_squared - method['validation']['squared_frobenius_error'])
                    assert delta < 1e-10
                    max_error_disagreement = max(max_error_disagreement, delta)
                files[str(estimate.relative_to(root))] = file_hash(estimate)
            checked.append(dict(case_index=row['case_index'], rep=row['rep']))
    assert len({(r['case_index'], r['rep']) for r in checked}) == len(checked)
    return dict(status='passed' if len(checked) == 1000 else 'partial',
                complete_paired_records_checked=len(checked), required_paired_records=1000,
                arrays_checked=len(files), max_squared_error_disagreement=max_error_disagreement,
                checked_records=checked, file_sha256=files,
                scope='Saved input bytes, input metadata, estimate shape/finiteness/Hermitian symmetry/trace and squared-Frobenius error checked. No solver rerun or independent PSD/eigenvalue certificate.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.root)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'complete_paired_records_checked', 'arrays_checked', 'max_squared_error_disagreement']}, indent=2))
