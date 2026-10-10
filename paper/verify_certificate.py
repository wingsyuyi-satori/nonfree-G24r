#!/usr/bin/env python3
"""Exact, standard-library verification of all finite manuscript data."""
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
import argparse
import json
if not __debug__:
    raise SystemExit('Run this verifier without -O; its exact checks use assertions.')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='verify that checked outputs match the committed files without rewriting them')
args = parser.parse_args()
ROOT = Path(__file__).resolve().parent
DATA = json.loads((ROOT/'data/compact_certificate.json').read_text(encoding='utf-8'))
def emit_output(name, text):
    data = text.encode('utf-8')
    path = ROOT/name
    if args.check:
        if path.read_bytes() != data:
            raise SystemExit(f'Checked output differs from committed file: {name}')
    else:
        path.write_bytes(data)
I = (Q(1),Q(0),Q(0),Q(1))
def mul(X,Y):
    a,b,c,d = X; e,f,g,h = Y
    return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)
def inv(X):
    a,b,c,d = X
    assert a*d-b*c == 1
    return d,-b,-c,a
def power(q,g,n):
    return (Q(1),Q(0),Q(n),Q(1)) if g=='a' else (Q(1),n*q,Q(0),Q(1))
def evaluate(q,word):
    X=I
    for g,n in word: X=mul(X,power(q,g,n))
    return X
def inverse_word(word):return [(g,-n) for g,n in reversed(word)]
def reduced(word):
    return bool(word) and all(n != 0 for g,n in word) and all(word[j][0]!=word[j+1][0] for j in range(len(word)-1))
M=DATA['modulus']; rules=DATA['rules']; words=DATA['exception_words']
assert DATA['s']==24 and M==40320 and len(rules)==48
covered=set(); exceptional=set()
for w,m,y,D in rules:
    assert w>0 and m>0 and y>0 and D>0
    assert M%(24*m)==0 and D==gcd(w,24*m)
    assert (m*gcd(w,24))%(y*D)==0
    assert (24*m*y-D)%w==0 or (24*m*y+D)%w==0
    covered.update(a for a in range(M) if (a-w)%(24*m)==0 or (a+w)%(24*m)==0)
    exceptional.update(n for n in (w,D) if n>6)
omitted=sorted(set(range(M))-covered)
assert omitted==[1261,6299,34021,39059]
assert all(a%1260 in (1,1259) for a in omitted)
assert exceptional==set(map(int,words)) and len(words)==23
matrices={}; lengths={}
for key,word in sorted(words.items(),key=lambda kv:int(kv[0])):
    r=int(key); q=Q(24,r); X=evaluate(q,word)
    assert reduced(word) and word[0][0]==word[-1][0]=='b'
    assert X[1]==0 and X[0]*X[3]==1
    C=word+[('a',1)]+inverse_word(word)
    relation=C+[('a',1)]+inverse_word(C)+[('a',-1)]
    assert reduced(relation) and len(relation)<=64
    assert evaluate(q,relation)==I
    matrices[key]=[str(x) for x in X];lengths[key]=len(relation)
report={'rules':len(rules),'modulus':M,'covered':len(covered),'omitted':omitted,
        'exceptions':sorted(exceptional),'max_relation_syllables':max(lengths.values()),
        'exception_matrices':matrices,'relation_syllables':lengths,
        'status':'all exact finite checks passed'}
emit_output('data/verification.json', json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('exception_matrices','relation_syllables')},indent=2))

def frac(q):
    q=Q(q)
    return str(q.numerator) if q.denominator==1 else ('-' if q<0 else '')+r'\frac{'+str(abs(q.numerator))+'}{'+str(q.denominator)+'}'
# Tables are regenerated from the checked certificate; no manual retyping.
t=[r'\begin{center}\small',r'\begin{tabular}{rrrrr@{\qquad}rrrrr}',r'\toprule',r'$i$&$w$&$m$&$y$&$D$&$i$&$w$&$m$&$y$&$D$\\',r'\midrule']
for i in range(24):
    row=[i+1,*rules[i],i+25,*rules[i+24]]
    t.append('&'.join(map(str,row))+r'\\')
t.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
emit_output('data/rules_table.tex', '\n'.join(t)+'\n')
t=[r'\begin{center}\small',r'\begin{tabular}{r@{\quad}l@{\quad}r}',r'\toprule',r'$r$&$(e_1,\ldots,e_L)$&$L$\\',r'\midrule']
for key,word in sorted(words.items(),key=lambda kv:int(kv[0])):
    t.append(key+'&$('+','.join(str(n) for g,n in word)+')$&'+str(len(word))+r'\\[2pt]')
t.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
emit_output('data/words_table.tex', '\n'.join(t)+'\n')
t=[r'\begin{center}',r'\renewcommand{\arraystretch}{1.4}',r'\begin{tabular}{r@{\qquad}r@{\qquad}r@{\qquad}r}',r'\toprule',r'$r$&$\alpha$&$\beta$&$4L+4$\\',r'\midrule']
for key,X in matrices.items():
    t.append(key+'&$'+frac(X[0])+'$&$'+frac(X[2])+'$&'+str(lengths[key])+r'\\')
t.extend([r'\bottomrule',r'\end{tabular}',r'\end{center}'])
emit_output('data/matrices_table.tex', '\n'.join(t)+'\n')
