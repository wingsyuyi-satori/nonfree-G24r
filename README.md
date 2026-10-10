# Nonfreeness for rational two-parabolic groups with numerator 24

## Lean formalization

Author: **Ziheng Wang**  
Affiliation: University of Chinese Academy of Sciences, Hangzhou Institute for Advanced Study, Hangzhou, China  
AI assistance: **GPT-6-Astra**.

[中文说明](README.zh-CN.md) · [Paper PDF](paper/main.pdf) · [LaTeX source](paper/main.tex)

Public repository: [wingsyuyi-satori/nonfree-G24r](https://github.com/wingsyuyi-satori/nonfree-G24r).
Version: **0.1.0**. The paper and Lean project will be archived together as a software record on Zenodo; the DOI will be added after the deposit.

This pinned Lean 4 / Mathlib project verifies the following results for

$$
 A=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
 B_q=\begin{pmatrix}1&q\\0&1\end{pmatrix},\qquad G_q=\langle A,B_q\rangle.
$$

## Verified statements

For every integer denominator `r`:

- `twentyfour_not_free`: if `|r| > 6`, the generated subgroup of `SL(2, ℚ)` is **not an abstract free group**.
- `twentyfour_complex_not_free`: the same conclusion for the actual displayed matrices in `SL(2, ℂ)`. The faithful rational-to-complex map and the generated-subgroup isomorphism are formalized.
- `twentyfour_hasRelation`: if `|r| > 6`, a genuine nonidentity element of `FreeGroup Bool` evaluates to the identity at `q = 24/r`.
- `twentyfour_boundedRelation`: this relation can be nonempty, freely reduced, and have at most **64 alternating nonzero generator-power syllables**. This is not a bound on the number of letters after expanding the powers.
- `twentyfour_twoStep`: if `|r| > 17`, there is a lower-triangular word with one, three, or five alternating nonzero powers, starting and ending with `B`.

`Challenge.lean` states these targets independently using Mathlib only. `Solution.lean` proves the exact target propositions. Specification-to-implementation identifications are themselves checked by Lean. `AxiomAudit.lean` reports the complete axiom dependencies of the headlines and key intermediate results.

## Proof organization

- `Core`: matrices, free-group words, reduction, triangularization, and explicit relations.
- `SimpleDirect`: the branch-free five-block identity for `R = 1 + 1260x`, with a nontrivial twelve-syllable relation for every nonzero integer `x`.
- `GoodRuleArithmetic` / `GoodRule`: normalization and the general covering rule.
- `FiniteCover`: 48 rules and the complete certificate modulo 40320, leaving four residue classes.
- `FiniteWords`: exact certificates for 23 exceptional absolute denominators.
- `CoverBridge` / `CoverRelations` / `Main`: the universal all-integer proof.
- `FreeGroupHopf` / `NonFree`: finite permutation models, Hopficity, and the passage from a relation to abstract nonfreeness.
- `ComplexVersion`: the faithful complex-matrix formulation.
- `Bounded` / `TwoStep`: uniform syllable bounds and the explicit cofinite two-step theorem.
- `Parametric` / `ParametricArithmetic`: general five-block machinery and supplementary earlier constructions. The final omitted-residue proof uses `SimpleDirect`, not the earlier 3-adic branch construction.

All finite certificates use ordinary `decide`, producing proof terms checked by the kernel. The delivered proofs use no `sorry`, custom axioms, `native_decide`, or compiler-oracle placeholders.

## Verification and its limits

The supplied research artifact records its final Lean build, axiom audit, and direct independent nanoda replay in `verification-result.json` and `logs/`. The eight exported declarations and their transitive dependencies were replayed by nanoda: **18,169 declarations, no errors**. Axiom dependencies are restricted to `propext`, `Classical.choice`, and `Quot.sound`. Repository preparation confirmed that all 19 Lean source hashes match this evidence and reran the exact finite certificate checks; it did not repeat the Lean build or nanoda replay on the preparation machine.

A clean project build was also performed without copying any project `.olean` files, reusing the downloaded pinned Mathlib dependency cache. This is not a claim that all external dependencies were rebuilt from source.

The project follows the specification/proof/audit separation illustrated by [anthropics/formal-math](https://github.com/anthropics/formal-math). **Full comparator/Palomar acceptance was not completed on the original verification host.** That workflow's pinned checker expected `String.ofList`, absent in Lean 4.24, and the original host lacked the required Landlock support. No checker was modified and no sandbox was bypassed. Details and exact reference versions are in `VERIFICATION.md`.

## Repository checks

For the checks that require only Python **3.9 or newer**:

```sh
python3 scripts/check-release.py
```

This checks the recorded Lean source hashes, manuscript file hashes, metadata consistency, every packaged file, and all 40320 finite residue classes and 23 exceptional words. It also compares regenerated tables and reports with their committed bytes. Run `python3 scripts/make-delivery.py` to regenerate the source ZIP and SHA-256 checksum after reviewing changes to packaging or metadata; changes to Lean proof sources require new verification evidence first.

## Reproduce the Lean checks

Install the official [elan toolchain manager](https://github.com/leanprover/elan), Git, Python 3, and Bash. The project pins Lean **4.24.0** and Mathlib **v4.24.0**; `lake-manifest.json` pins all transitive packages.

```sh
lake exe cache get
lake build Solution
bash scripts/verify.sh \
  twentyfour_not_free twentyfour_hasRelation twentyfour_boundedRelation \
  twentyfour_complex_not_free twentyfour_twoStep
```

`env.sh` can use a local toolchain when present; otherwise it uses the normal installed Lean/elan commands. No unbundled private tool directory is required. Initial downloads and finite-certificate builds can take several minutes.

## Reproduce independent kernel replay

Install [Rust/cargo](https://rust-lang.org/tools/install/), then build the pinned matching exporter and checker:

```sh
bash scripts/bootstrap-checkers.sh
bash scripts/verify-nanoda.sh Solution \
  twentyfour_not_free twentyfour_hasRelation twentyfour_boundedRelation \
  twentyfour_complex_not_free twentyfour_twoStep \
  TwentyFour.simple_direct_power_identity \
  TwentyFour.simple_direct_scaled_certificate \
  TwentyFour.simple_direct_four_residues_certificate
```

The script regenerates `logs/proofs.ndjson` and runs nanoda with a strict standard-axiom whitelist. The large generated export is excluded from the source archive; its size, SHA-256, and selected declarations are recorded in `logs/proof-export-summary.json`. Exact tool commits are in `verification-pins.json`; further verification detail is in `VERIFICATION.md`.

## Citation, metadata, and licenses

`CITATION.cff` and `.zenodo.json` describe the same software title, author, affiliation, version, and MIT license. The preferred paper citation uses the manuscript title above. The repository URL is recorded in the citation metadata and archive description. A DOI will be added after Zenodo assigns it; no email or ORCID is supplied.

- Software and Lean sources: **MIT**, copyright 2026 Ziheng Wang; see `LICENSE`.
- Accompanying manuscript and the source/PDF under `paper/`: **CC BY 4.0**; see `LICENSE-PAPER.md`.

The source archive excludes tool binaries, downloaded dependencies, build caches, reference repositories, and exploratory failures. Its SHA-256 file manifest is `package-manifest.json`.
