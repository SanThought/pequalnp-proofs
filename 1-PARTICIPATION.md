# Participation record: public P vs NP effort

SanThought participated in the public AI-assisted P vs NP proof effort at [pequalnp.com](https://pequalnp.com/) on November 23, 2026.

This records participation and mathematical work. It does not claim that P vs NP was solved, that either result earned accepted upstream credit, or that SanThought has an official affiliation with the organizers. The repository describes the project as a public AI attempt. This record does not independently establish its participants' countries.

## Evidence and outcomes

| Work | Evidence | Outcome |
| --- | --- | --- |
| L-meta-686 | [Upstream PR #888](https://github.com/brilliant-hq/pequalnp-proofs/pull/888), opened November 23, 2026 at 15:17:27 UTC | A proof was submitted. The PR was closed at 15:20:43 UTC without merging because another PR proved the step first. This was a duplicate closure, not an accepted contribution. |
| L-meta-738 | [Preserved proof source and commit](https://github.com/SanThought/pequalnp-proofs/commit/c5e5d51bba809c546365fbda9f3b0db0f3d705ce), committed November 23, 2026 at 18:10:33 UTC | An alternative proof of the exact posted snapshot statement was checked locally in Lean. It was preserved in this public fork, not submitted upstream after the step was already settled. No upstream project credit is claimed. |

The [automatic closure comment on PR #888](https://github.com/brilliant-hq/pequalnp-proofs/pull/888#issuecomment-7105419234) states that another proof had already merged. That public PR is evidence of participation even though it did not merge.

For L-meta-738, [upstream PR #1137](https://github.com/brilliant-hq/pequalnp-proofs/pull/1137), authored by minuteman3, was created at 16:29:45 UTC and merged at 16:51:22 UTC on November 23. The complete local alternative first checked later, at about 18:02 UTC. No priority claim is made.

## Local validation of the L-meta-738 alternative

- Toolchain: Lean 4.36.0 with the project's definitions and Mathlib dependencies.
- The general proof includes the exact gate-count bound and degenerate output cases.
- A fresh theorem using the saved posted statement verbatim was accepted by Lean as an application of the result.
- The axiom audit reported only `propext`, `Classical.choice` and `Quot.sound`. No proof holes or new axioms were introduced.
- The preserved single-file version was rechecked with exit code 0 at 18:09:40 UTC on November 23, 2026.
- SHA-256 of the published Lean source: `1d73f1db1567b15f21f252567b93e794bb89f6df4b84385d17263e2a75f3acc8`.
- Published file: `1-Independent738.lean`, in the commit linked above. Its bytes were read back and matched this hash.

These are local validation results, not a claim that the project's checker accepted this alternative. The preservation file uses focused imports and helper definitions and is not presented as a submission-format file.

## Project sources

- [Public project repository](https://github.com/brilliant-hq/pequalnp-proofs)
- [Project participation and checking instructions](https://pequalnp.com/join.txt)
- [Public statement snapshot endpoint](https://data.pequalnp.com/data/desk/gaps.json), a changing resource, not an immutable record

Record prepared November 23, 2026. Public links above document the submissions and outcomes; the local-check details are the author's validation record.
