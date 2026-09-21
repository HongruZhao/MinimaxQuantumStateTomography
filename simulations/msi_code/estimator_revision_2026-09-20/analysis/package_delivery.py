"""Package corrected sources and result summaries, then verify a fresh extraction.

Dense raw result arrays stay in the local/MSI results directories. Their remote
hash manifest and download-verification receipt are included in this archive.
"""
import hashlib
import json
from pathlib import Path
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent.parent
PREFIX = ROOT.name
ARCHIVE = ROOT / 'output/MSI_ESTIMATORS_CODE_AND_RESULTS_SUMMARY.zip'


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    paths = set()
    for folder in ['src', 'configs', 'jobs', 'analysis', 'figures',
                   'original/msi_snapshot', 'output/pdf']:
        paths.update(p for p in (ROOT / folder).rglob('*')
                     if p.is_file() and '__pycache__' not in p.parts)
    paths.update(p for p in (ROOT / 'results').rglob('*.json') if p.is_file())
    paths.update(p for p in (ROOT / 'reports').glob('*')
                 if p.is_file() and p.name not in
                 ['package_verification.json', 'delivery_sync_verification.json'])
    paths.update(ROOT / name for name in ['README.md', 'PROTOCOL.md',
                 'WORK_STATUS.md', 'requirements-simulation.txt',
                 'requirements-analysis.txt'])
    manifest = {str(p.relative_to(ROOT)): {'bytes': p.stat().st_size,
                                         'sha256': sha256(p)}
                for p in sorted(paths)}
    note = (
        '# Portable code and result-summary delivery\n\n'
        'This archive includes corrected solver code, configurations, reports,\n'
        'plots, per-dataset JSON summaries/histories, and provenance.\n'
        'Dense raw results/*.npz arrays are excluded. All raw arrays are kept\n'
        'in the corresponding local and MSI revision directories; all 1646\n'
        'raw-file hashes are listed in reports/raw_results_manifest.json.\n'
        'src/clifford_representatives.npz IS included as sampler input.\n\n'
        'INCLUDED_FILES_SHA256.json covers every included payload file.\n'
        'The package verifier checks CRC, safe paths, fresh extraction, sizes,\n'
        'and every included-file hash. See reports/package_verification.json\n'
        'alongside the archive for the external archive hash/receipt.\n'
    )
    ARCHIVE.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(ARCHIVE, 'w', zipfile.ZIP_DEFLATED, compresslevel=6) as z:
        for path in sorted(paths):
            z.write(path, PREFIX + '/' + str(path.relative_to(ROOT)))
        z.writestr(PREFIX + '/INCLUDED_FILES_SHA256.json',
                   json.dumps(manifest, indent=2) + '\n')
        z.writestr(PREFIX + '/PACKAGE_CONTENTS.md', note)
    with tempfile.TemporaryDirectory(prefix='shadow-estimator-package-') as temp:
        extraction = Path(temp)
        with zipfile.ZipFile(ARCHIVE) as z:
            assert z.testzip() is None
            names = z.namelist()
            assert len(names) == len(set(names))
            assert all(not Path(n).is_absolute() and '..' not in Path(n).parts
                       for n in names)
            z.extractall(extraction)
        for name, expected in manifest.items():
            path = extraction / PREFIX / name
            assert path.stat().st_size == expected['bytes'], name
            assert sha256(path) == expected['sha256'], name
    receipt = dict(status='passed', archive=str(ARCHIVE.relative_to(ROOT)),
                   archive_bytes=ARCHIVE.stat().st_size, archive_sha256=sha256(ARCHIVE),
                   verified_payload_files=len(manifest), zip_members=len(manifest)+2,
                   safe_paths=True, crc_passed=True, fresh_extraction=True,
                   all_payload_hashes_matched=True, raw_result_arrays_included=False)
    (ROOT / 'reports/package_verification.json').write_text(
        json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
