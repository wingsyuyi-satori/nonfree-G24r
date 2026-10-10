# GitHub and Zenodo release checklist

Version: 0.1.0. Author: Ziheng Wang.
Repository: https://github.com/wingsyuyi-satori/nonfree-G24r

The paper and Lean project were published together as a **preprint** on Zenodo
on 2026-10-10: [10.5281/zenodo.23280225](https://doi.org/10.5281/zenodo.23280225).
Code is MIT; the manuscript is separately CC BY 4.0. The archive description
discloses this distinction and the GPT-6-Astra assistance.

1. Review the manuscript, `Challenge.lean`, citation metadata, licenses, and
   [verification scope](VERIFICATION.md).
2. Run `python3 scripts/check-release.py`. Preserve the proof source hashes and
   historical verification logs; update verification evidence if proofs change.
3. `python3 scripts/make-delivery.py` generates a ZIP and its SHA-256 checksum
   in the parent directory from the current repository contents.
   The ZIP includes hidden metadata, release notes, the manuscript, all Lean
   modules, scripts, and selected text verification logs. It excludes Git
   history, tool binaries, downloaded packages, and build caches.
   The submitted v0.1.0 archive predates the DOI metadata updates. Preserve that
   original archive; a regenerated ZIP includes the current metadata.
4. Submit the reviewed files to the repository. The supplied verification
   evidence and manual reproduction commands remain available.
   `RELEASE_NOTES.md` is the prepared release description. Build and packaging
   scripts create no GitHub release or DOI.
5. The v0.1.0 deposit was published manually as one preprint record. The paper
   DOI and record link are now recorded in both READMEs, `CITATION.cff`, and
   `.zenodo.json`.
6. For future research revisions, update the version and publish a new Zenodo
   version. Keep each DOI associated with the files for that version.

`.zenodo.json` describes the combined preprint deposit. `CITATION.cff` describes
the Lean software and supplies that preprint as its preferred citation. Keep
the preferred paper title, DOI, author, affiliation, and version synchronized.
Zenodo uses `.zenodo.json` for GitHub archiving when both files are present. See the official
[metadata guide](https://help.zenodo.org/docs/github/describe-software/zenodo-json/)
and [archiving guide](https://help.zenodo.org/docs/github/archive-software/).

The archive is not evidence of journal peer review or journal submission.
