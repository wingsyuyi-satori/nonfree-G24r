#!/usr/bin/env python3
"""Check release metadata, recorded proof hashes, and exact manuscript data."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = 'https://github.com/wingsyuyi-satori/nonfree-G24r'
THEOREMS = [
    'twentyfour_not_free', 'twentyfour_hasRelation',
    'twentyfour_boundedRelation', 'twentyfour_complex_not_free',
    'twentyfour_twoStep',
]

def fail(message):
    raise SystemExit(message)

def load(name):
    return json.loads((ROOT/name).read_text(encoding='utf-8'))

def check_hash(name, expected):
    path = (ROOT/name).resolve()
    if not path.is_relative_to(ROOT) or not path.is_file():
        fail(f'Missing or invalid release path: {name}')
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        fail(f'File hash differs from the recorded artifact: {name}')
    return len(data)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--skip-package-manifest', action='store_true',
                    help='check inputs before regenerating the release manifest')
args = parser.parse_args()
result = load('verification-result.json')
version = result['version']
if any(result.get(name) != 'passed' for name in ('lean_build', 'axiom_audit', 'nanoda')):
    fail('The recorded proof verification is incomplete.')
verified = load('logs/verified-source-hashes.json')
sources = {p.relative_to(ROOT).as_posix() for p in (ROOT/'TwentyFour').glob('*.lean')}
sources.update(('Challenge.lean', 'Solution.lean', 'AxiomAudit.lean'))
if set(verified) != sources:
    fail('The recorded Lean source list does not match the delivered modules.')
for name, expected in verified.items():
    check_hash(name, expected)
print(f'PASS: all {len(verified)} Lean sources match the recorded proof verification')

for name, expected in load('paper/package-manifest.json').items():
    check_hash('paper/'+name, expected)
if not (ROOT/'paper/main.pdf').read_bytes().startswith(b'%PDF-'):
    fail('The manuscript PDF is invalid.')

pins = load('verification-pins.json')
if (ROOT/'lean-toolchain').read_text(encoding='utf-8').strip() != pins['project_lean']:
    fail('Lean toolchain and verification pins disagree.')
manifest = load('lake-manifest.json')
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
if mathlib['rev'] != pins['mathlib']:
    fail('The Mathlib lockfile and verification pins disagree.')

zenodo = load('.zenodo.json')
cff = (ROOT/'CITATION.cff').read_text(encoding='utf-8')
def cff_field(name):
    match = re.search(r'^'+re.escape(name)+r':\s*(.*?)\s*$', cff, re.MULTILINE)
    if not match:
        fail(f'Missing citation field: {name}')
    return match.group(1).strip('\"\'')
preferred = cff.split('preferred-citation:\n', 1)
if len(preferred) != 2:
    fail('The preferred preprint citation is missing.')
def paper_cff_field(name):
    match = re.search(r'^  '+re.escape(name)+r':\s*(.*?)\s*$', preferred[1], re.MULTILINE)
    if not match:
        fail(f'Missing preferred citation field: {name}')
    return match.group(1).strip('\"\'')
if paper_cff_field('title') != zenodo['title'] or cff_field('version') != version or zenodo['version'] != version or paper_cff_field('version') != version:
    fail('Preferred paper citation/version and Zenodo metadata disagree.')
if cff_field('repository-code') != REPOSITORY or REPOSITORY not in zenodo['description']:
    fail('Repository URL is missing or inconsistent.')
if cff_field('type') != 'software' or cff_field('license').lower() != 'mit':
    fail('The software citation or its MIT license is incorrect.')
if zenodo['license'].lower() != 'cc-by-4.0' or paper_cff_field('license') != 'CC-BY-4.0':
    fail('Preprint licenses disagree.')
if zenodo['upload_type'] != 'publication' or zenodo.get('publication_type') != 'preprint' or zenodo['access_right'] != 'open':
    fail('Zenodo resource type or access differs from the published preprint.')
doi = '10.5281/zenodo.23280225'
record = 'https://zenodo.org/records/23280225'
if zenodo.get('doi') != doi or paper_cff_field('doi') != doi or paper_cff_field('url') != record:
    fail('The published paper DOI or record URL is missing or inconsistent.')
if zenodo.get('publication_date') != '2026-10-10' or paper_cff_field('date-published') != '2026-10-10':
    fail('The preprint publication date is inconsistent.')
creator = zenodo['creators'][0]
if creator['name'] != 'Wang, Ziheng' or creator['affiliation'] != result['affiliation']:
    fail('Zenodo authorship differs from the supplied research artifact.')
if creator.get('orcid') != '0009-0002-4179-4161' or 'https://orcid.org/'+creator['orcid'] not in cff:
    fail('The citation ORCID differs from the published record.')
if 'family-names: Wang' not in cff or 'given-names: Ziheng' not in cff or creator['affiliation'] not in cff:
    fail('Citation authorship differs from the supplied research artifact.')
if result['paper_license'] != 'CC-BY-4.0' or 'CC BY 4.0' not in (ROOT/'LICENSE-PAPER.md').read_text(encoding='utf-8'):
    fail('The separate manuscript license is missing.')
lakefile = (ROOT/'lakefile.toml').read_text(encoding='utf-8')
if not re.search(r'^version\s*=\s*"'+re.escape(version)+r'"\s*$', lakefile, re.MULTILINE):
    fail('Lake package and citation versions disagree.')
for name in ('README.md', 'README.zh-CN.md'):
    readme = (ROOT/name).read_text(encoding='utf-8')
    if REPOSITORY not in readme:
        fail(f'The public repository link is missing from {name}')
    if doi not in readme or record not in readme:
        fail(f'The published DOI or Zenodo record link is missing from {name}')
print('PASS: versions, paper DOI, repository URL, author, affiliation, ORCID, and licenses agree')

subprocess.run([sys.executable, str(ROOT/'paper/verify_certificate.py'), '--check'], check=True)
subprocess.run([sys.executable, str(ROOT/'scripts/check-trust.py'),
                '--axioms', str(ROOT/'logs/axioms.log'), '--expect', *THEOREMS], check=True)
if not args.skip_package_manifest:
    files = load('package-manifest.json')['files']
    paths = [item['path'] for item in files]
    if len(paths) != len(set(paths)):
        fail('Duplicate path in package manifest.')
    for item in files:
        if check_hash(item['path'], item['sha256']) != item['bytes']:
            fail(f"Incorrect byte count: {item['path']}")
    required = {'.gitattributes', 'RELEASE_NOTES.md',
                'scripts/check-release.py', 'logs/repository-preparation.json'}
    if not required.issubset(paths):
        fail('The release manifest omits repository preparation files.')
    print(f'PASS: all {len(files)} packaged files match their SHA-256 manifest')
print('PASS: release checks completed; historical Lean/nanoda evidence is source-matched')
