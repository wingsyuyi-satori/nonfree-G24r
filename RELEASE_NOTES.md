# v0.1.0

Nonfreeness for rational two-parabolic groups with numerator 24.

For every integer r with |r| > 6, the displayed matrices A and B at parameter
24/r generate an abstractly nonfree group over both the rationals and the
complex numbers. Each parameter admits a nonempty, freely reduced, nontrivial
relation with at most 64 alternating nonzero generator-power syllables. For
|r| > 17, the parameter is a two-step relation number.

This release contains the English manuscript and editable LaTeX sources, all
48 covering rules and 23 exceptional words, an exact Python verifier, and the
Lean 4.24.0 / Mathlib v4.24.0 formalization with pinned dependencies.

The supplied verification evidence records a Lean build, a clean project
rebuild using the external Mathlib cache, a 22-declaration axiom audit, and
independent nanoda replay of eight selected declarations and their transitive
dependencies: 18,169 declarations checked with no errors. The delivered Lean
sources match the recorded source hashes. See [VERIFICATION.md](VERIFICATION.md)
for scope and reproduction commands.

Author: Ziheng Wang. AI assistance: GPT-6-Astra.
Software and Lean sources: MIT. Accompanying manuscript: CC BY 4.0.

Repository: https://github.com/wingsyuyi-satori/nonfree-G24r.
The manuscript and accompanying Lean project were published together as a
preprint on Zenodo on 2026-10-10.
DOI: [10.5281/zenodo.23280225](https://doi.org/10.5281/zenodo.23280225).
Record: https://zenodo.org/records/23280225.
The Zenodo files preserve the submitted v0.1.0 snapshot; this repository also
contains citation and metadata updates made after publication.
