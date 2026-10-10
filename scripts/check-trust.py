#!/usr/bin/env python3
"""Conservative source + #print axioms audit. It does not replace Lean's kernel."""
import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
FORBIDDEN = {'sorry', 'admit', 'axiom', 'native_decide', 'trustCompiler', 'ofReduceBool'}

def remove_comments_and_strings(s):
    out = []
    i = depth = 0
    quote = line = False
    while i < len(s):
        c, pair = s[i], s[i:i+2]
        if line:
            out.append('\n' if c == '\n' else ' ')
            if c == '\n': line = False
            i += 1
        elif depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if c == '\n' else ' '); i += 1
        elif quote:
            if c == '\\': out.extend('  '); i += 2
            elif c == '"': quote = False; out.append(' '); i += 1
            else: out.append('\n' if c == '\n' else ' '); i += 1
        elif pair == '--': line = True; out.extend('  '); i += 2
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif c == '"': quote = True; out.append(' '); i += 1
        else: out.append(c); i += 1
    return ''.join(out)

def check_sources():
    paths = sorted((ROOT / 'TwentyFour').rglob('*.lean')) + [ROOT / name for name in ['Challenge.lean', 'Solution.lean', 'AxiomAudit.lean'] if (ROOT / name).is_file()]
    if not paths: raise SystemExit('No Lean sources found')
    bad = []
    for path in paths:
        text = remove_comments_and_strings(path.read_text(encoding='utf-8'))
        for match in re.finditer(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler|ofReduceBool)\b', text):
            bad.append(f'{path.relative_to(ROOT)}:{text[:match.start()].count(chr(10))+1}: {match.group()}')
    if bad:
        raise SystemExit('Forbidden proof/trust source token(s):\n' + '\n'.join(bad))
    print(f'PASS: checked {len(paths)} project source files for forbidden proof/trust tokens')

def check_axioms(log, expected):
    text = pathlib.Path(log).read_text(encoding='utf-8')
    seen = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        names = {x.strip() for x in raw.split(',') if x.strip()}
        seen[name] = names
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        seen[name] = set()
    if not seen: raise SystemExit('No #print axioms result found in audit log')
    for name, names in seen.items():
        if names - ALLOWED: raise SystemExit(f'Forbidden axioms in {name}: {sorted(names - ALLOWED)}')
    missing = set(expected) - set(seen)
    if missing: raise SystemExit(f'Missing axiom audit: {sorted(missing)}')
    print(f'PASS: {len(seen)} declarations depend only on {sorted(ALLOWED)} (or fewer)')

p = argparse.ArgumentParser()
p.add_argument('--axioms')
p.add_argument('--expect', nargs='*', default=[])
a = p.parse_args()
check_sources()
if a.axioms: check_axioms(a.axioms, a.expect)
