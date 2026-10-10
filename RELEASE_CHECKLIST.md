# GitHub and Zenodo release checklist

Version: 0.1.0. Author: Ziheng Wang.
Repository: https://github.com/wingsyuyi-satori/nonfree-G24r

The planned Zenodo record archives the paper and Lean project together as
**software**. Code is MIT; the manuscript is separately CC BY 4.0. The archive
description discloses this distinction and the GPT-6-Astra assistance.

1. Review the manuscript, `Challenge.lean`, citation metadata, licenses, and
   [verification scope](VERIFICATION.md).
2. Run `python3 scripts/check-release.py`. Preserve the proof source hashes and
   historical verification logs; update verification evidence if proofs change.
3. Run `python3 scripts/make-delivery.py` to generate
   `nonfree-G24r-v0.1.0.zip` and its SHA-256 checksum in the parent directory.
   The ZIP includes hidden metadata, release notes, the manuscript, all Lean
   modules, scripts, and selected text verification logs. It excludes Git
   history, tool binaries, downloaded packages, and build caches.
4. Submit the reviewed files to the repository. The supplied verification
   evidence and manual reproduction commands remain available.
   `RELEASE_NOTES.md` is the prepared release description. Build and packaging
   scripts create no GitHub release or DOI.
5. For GitHub-to-Zenodo archiving, first enable this repository in Zenodo, then
   create the release tagged `v0.1.0`. Alternatively, upload the prepared ZIP
   manually as one software record and use `.zenodo.json` for its metadata.
6. When a real DOI is assigned, add it to the citation metadata and README.
   An archived release snapshot is fixed; any later source revision should be
   associated with its own version. Keep the DOI's version association clear.

Zenodo uses `.zenodo.json` for GitHub archiving when both it and `CITATION.cff`
are present. Keep their shared fields synchronized. See the official
[metadata guide](https://help.zenodo.org/docs/github/describe-software/zenodo-json/)
and [archiving guide](https://help.zenodo.org/docs/github/archive-software/).

The archive is not evidence of journal peer review or journal submission.
