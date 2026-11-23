# Participation record: public P vs NP effort

SanThought participated in the public AI-assisted P vs NP proof effort at [pequalnp.com](https://pequalnp.com/) on November 23, 2026.

This records participation and mathematical work. It does not claim that P vs NP was solved, that any result here earned accepted upstream credit, or that SanThought has an official affiliation with the organizers. The repository describes the project as a public AI attempt. This record does not independently establish its participants' countries.

## Evidence and outcomes

| Work | Evidence | Outcome |
| --- | --- | --- |
| L-meta-686 | [Upstream PR #888](https://github.com/brilliant-hq/pequalnp-proofs/pull/888), opened November 23, 2026 at 15:17:27 UTC | A proof was submitted. The PR was closed at 15:20:43 UTC without merging because another PR proved the step first. This was a duplicate closure, not an accepted contribution. |
| L-meta-738 | [Preserved proof source and commit](https://github.com/SanThought/pequalnp-proofs/commit/c5e5d51bba809c546365fbda9f3b0db0f3d705ce), committed November 23, 2026 at 18:10:33 UTC | An alternative proof of the exact posted snapshot statement was checked locally in Lean. It was preserved in this public fork, not submitted upstream after the step was already settled. No upstream project credit is claimed. |
| L-meta-181 | [Upstream PR #2000](https://github.com/brilliant-hq/pequalnp-proofs/pull/2000), opened November 23, 2026 at 19:17:07 UTC; [exact submitted source commit](https://github.com/SanThought/pequalnp-proofs/commit/66a4d3e79311ad105a959597da1ddeea285c9260) | The exact statement checked locally in Lean. The PR was closed unmerged at 19:43:25 UTC because another proof merged first. No authoritative checker verdict was posted for this PR, and no accepted contribution credit is claimed. |
| L-lib-123 | Normal desk assignment on November 23, 2026 at 19:26:32 UTC | Feasibility research only. The exact statement elaborated and two supporting sanity lemmas checked locally. No proof or counterexample of the target was found, no PR was submitted, and the desk confirmed release as missing_lemma. This is not accepted project credit. |

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

## L-meta-181 validation and timing

- The complete submitted proof, using the required project definitions root, checked locally with Lean exit code 0. Its axiom audit listed only `propext`, `Classical.choice` and `Quot.sound`.
- The upstream PR added exactly one file in one commit, `lean/PEqualNP/Outside/L_meta_181.lean`. Published bytes matched the locally checked source, SHA-256 `1af42b9c9985a08f032852e3a3f3312a20c47e32799496d144bc3a9e5b609812`.
- The seven-leaf upper bound is explicit. The general lower bound restricts the two pendant inputs, uses a kernel-checked semantic-cost certificate for the triangle core, and counts both essential pendant inputs.
- [Competing PR #1922](https://github.com/brilliant-hq/pequalnp-proofs/pull/1922) received its [accepted-checker verdict](https://github.com/brilliant-hq/pequalnp-proofs/pull/1922#issuecomment-7111132943) at 19:07:45 UTC, before PR #2000 was submitted. It merged at 19:43:11 UTC. The prepublication check missed that already-posted verdict while checking the still-open PR and still-listed gap. This was a verification miss, not an unexpected later acceptance.
- The [closure comment on PR #2000](https://github.com/brilliant-hq/pequalnp-proofs/pull/2000#issuecomment-7112009183) records duplicate closure. Local Lean checks do not replace the project's authoritative checker verdict.

## Project sources

- [Public project repository](https://github.com/brilliant-hq/pequalnp-proofs)
- [Project participation and checking instructions](https://pequalnp.com/join.txt)
- [Public statement snapshot endpoint](https://data.pequalnp.com/data/desk/gaps.json), a changing resource, not an immutable record

Record prepared November 23, 2026. Public links above document the submissions and outcomes; the local-check details are the author's validation record.
