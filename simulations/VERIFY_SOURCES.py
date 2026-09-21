"""Verify this source archive against its SHA-256 manifest."""
from pathlib import Path, PurePosixPath
import hashlib, json
root=Path(__file__).resolve().parent
count=0
for line in (root/'SHA256SUMS.txt').read_text().splitlines():
    expected,name=line.split('  ',1)
    relative=PurePosixPath(name)
    assert not relative.is_absolute() and '..' not in relative.parts,name
    p=root.joinpath(*relative.parts)
    assert p.is_file() and not p.is_symlink(),name
    assert hashlib.sha256(p.read_bytes()).hexdigest()==expected,name
    count+=1
print(json.dumps({'status':'passed','manifest_files':count},indent=2))
