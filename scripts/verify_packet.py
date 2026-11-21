#!/usr/bin/env python3
"""Verify bytes of all included exhibits against the frozen source manifest."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent.parent
m=json.loads((root/'SOURCE_MANIFEST.json').read_text(encoding='utf8'))
listed=set()
fail=[]
for row in m['entries']:
 rel=Path(row['path'])
 if rel.is_absolute() or '..' in rel.parts:
  fail.append(('unsafe path',str(rel)));continue
 listed.add(str(rel))
 p=root/rel
 if not p.is_file() or p.is_symlink():
  fail.append(('missing/nonregular',str(rel)));continue
 actual=hashlib.sha256(p.read_bytes()).hexdigest()
 if actual!=row['sha256'] or p.stat().st_size!=row['size_bytes']:
  fail.append(('hash/size mismatch',str(rel)))
actual={str(p.relative_to(root)) for p in (root/'exhibits').rglob('*') if p.is_file()}
for x in sorted(actual-listed):fail.append(('unlisted',x))
for x in sorted(listed-actual):fail.append(('listed not exhibit',x))
print('Verified',len(listed)-len(fail),'/',len(listed),'listed exhibit files')
for kind,path in fail[:30]:print('FAIL',kind,path,file=sys.stderr)
sys.exit(1 if fail else 0)
