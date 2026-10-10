#!/usr/bin/env python3
"""Package reviewed source and recorded evidence, including GitHub configuration."""
from datetime import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
def load(name):
    return json.loads((ROOT/name).read_text(encoding='utf-8'))
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def write_json(path, data):
    path.write_bytes((json.dumps(data, indent=2, ensure_ascii=False)+'\n').encode('utf-8'))

result = load('verification-result.json')
version = result['version']
if any(result.get(key) != 'passed' for key in ('lean_build', 'axiom_audit', 'nanoda')):
    raise SystemExit('Recorded final proof verification has not passed')
for name, expected in load('logs/verified-source-hashes.json').items():
    if sha(ROOT/name) != expected:
        raise SystemExit(f'Verified Lean source changed: {name}')

paper_names = sorted(load('paper/package-manifest.json'))
write_json(ROOT/'paper/package-manifest.json',
           {name: sha(ROOT/'paper'/name) for name in paper_names})
root_names = [
    'README.md', 'README.zh-CN.md', 'CITATION.cff', '.zenodo.json', 'LICENSE',
    'LICENSE-PAPER.md', 'VERIFICATION.md', 'verification-pins.json',
    'verification-result.json', 'lean-toolchain', 'lakefile.toml',
    'lake-manifest.json', 'env.sh', '.gitignore', '.gitattributes',
    'Challenge.lean', 'Solution.lean', 'AxiomAudit.lean', 'Makefile',
    'CHANGELOG.md', 'RELEASE_CHECKLIST.md', 'RELEASE_NOTES.md',
]
log_names = [
    'build.log', 'axioms.log', 'trust-audit.log', 'source-audit.log',
    'lean-version.log', 'nanoda.log', 'nanoda-theorems.txt', 'nanoda-config.json',
    'proof-export-summary.json', 'verified-source-hashes.json',
    'clean-build.log', 'clean-build-final.log', 'clean-axioms.log',
    'metadata-validation.log', 'repository-preparation.json',
]
files = [ROOT/name for name in root_names]
files += [ROOT/'paper'/name for name in paper_names]
files.append(ROOT/'paper/package-manifest.json')
files += sorted((ROOT/'TwentyFour').glob('*.lean'))
files += sorted(p for p in (ROOT/'scripts').iterdir() if p.suffix in ('.py', '.sh'))
files += [ROOT/'logs'/name for name in log_names]
files = sorted(set(files), key=lambda p: p.relative_to(ROOT).as_posix())
for path in files:
    if not path.is_file():
        raise SystemExit(f'Missing package input: {path.relative_to(ROOT)}')
manifest = {'files': [
    {'path': p.relative_to(ROOT).as_posix(), 'sha256': sha(p), 'bytes': p.stat().st_size}
    for p in files
]}
write_json(ROOT/'package-manifest.json', manifest)
subprocess.run([sys.executable, str(ROOT/'scripts/check-release.py')], check=True)
files.append(ROOT/'package-manifest.json')

prefix = f'nonfree-G24r-v{version}/'
out = ROOT.parent/f'nonfree-G24r-v{version}.zip'
timestamp = datetime.fromisoformat(result['verified_on']).timetuple()[:6]
with zipfile.ZipFile(out, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for path in sorted(files, key=lambda p: p.relative_to(ROOT).as_posix()):
        info = zipfile.ZipInfo(prefix+path.relative_to(ROOT).as_posix(), timestamp)
        info.create_system = 3
        mode = 0o100755 if path.suffix in ('.py', '.sh') else 0o100644
        info.external_attr = mode << 16
        info.compress_type = zipfile.ZIP_DEFLATED
        archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
with zipfile.ZipFile(out) as archive:
    if archive.testzip():
        raise SystemExit('ZIP integrity check failed')
    if set(archive.namelist()) != {prefix+p.relative_to(ROOT).as_posix() for p in files}:
        raise SystemExit('ZIP file list differs from the reviewed package')
    for path in files:
        if archive.read(prefix+path.relative_to(ROOT).as_posix()) != path.read_bytes():
            raise SystemExit(f'ZIP content differs: {path.relative_to(ROOT)}')
digest = sha(out)
out.with_suffix('.sha256').write_bytes(f'{digest}  {out.name}\n'.encode('ascii'))
print(json.dumps({'path': str(out), 'bytes': out.stat().st_size, 'sha256': digest,
                  'files': len(files), 'integrity': 'passed'}, indent=2))
