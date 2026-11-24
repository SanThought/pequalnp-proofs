# Overnight research closeout, November 24, 2026

Closeout prepared for the work window ending at 08:00 America/Bogota. No solution of P versus NP, no complete proof of an assigned open target, and no new upstream accepted credit is claimed from this night. This notebook separates checked partial theorems from searches that did not finish.

## Main checked results

### Symmetric permanent-level spaces

For complex symmetric 4 by 4 matrices with permanent(J+t)=24 throughout a linear subspace:

- General case: dimension is at most 4, allowing arbitrary diagonals. Together with the checked two-dimensional star plane, our proved interval for the maximum dimension is 2 through 4. The three-dimensional existence question remains open.
- Zero-diagonal case: dimension is at most 2, globally over all such subspaces. The star plane reaches 2, so this restricted result is sharp.
- The star plane is maximal under inclusion. This is not the same as being maximum-dimensional among all subspaces.
- There is a complex line of valid directions with nonzero diagonals. Thus the zero-diagonal restriction cannot simply be assumed for all valid directions.

Each linked notebook includes its checked source, successful compiler log, assumptions and exact remaining gap:

https://github.com/SanThought/pequalnp-proofs/blob/main/1-GENERAL-SYMMETRIC232-2026-11-24.md

https://github.com/SanThought/pequalnp-proofs/blob/main/1-ZERO-DIAGONAL232-2026-11-24.md

https://github.com/SanThought/pequalnp-proofs/blob/main/2-STAR232-2026-11-24.md

https://github.com/SanThought/pequalnp-proofs/blob/main/1-DIAGONAL-LINE232-2026-11-24.md

The main next mathematical question is how the cubic and quartic permanent coefficients restrict a three-dimensional totally isotropic subspace of the nine-dimensional tangent space. The quadratic constraint alone gives only the checked bound 4. A failed small-coordinate extension search is not a classification.

### Graph circuit bounds

- Full ten-vertex Petersen edge function: at least 15 non-NOT gates. A circuit of total size at most 19 therefore has at most four NOT gates. The target exclusion with one through four NOT gates remains unresolved.
- Incidence-graph degree-sensitive bound: at least n+minimum-degree-1 gates under the proved graph and circuit hypotheses. For the projective-plane parameters in the notebook this gives 2N+q. This is conditional on the incidence structure, not a construction of an arbitrary-order plane.
- For each fixed nested-AND-pair budget K, an explicit linear-in-size bound on unclean edges. The constant depends on K through the checked recurrence. This does not supply one constant uniform over unrestricted nesting.

https://github.com/SanThought/pequalnp-proofs/blob/main/4-2-PETERSEN2592-2026-11-24.md

https://github.com/SanThought/pequalnp-proofs/blob/main/2-FIXEDK1764-2026-11-24.md

### Boundary baselines and helpers

The 17-input patch has a checked 24-gate circuit, while its requested budget is 23. The Heawood boundary table has a checked 27-gate circuit, while its parent budget is 26. Neither one-gate gap was closed.

Other checked helpers cover a finite patch-completion list, a general independent-set completion fact, semantic factor purity, and eleven possible semantics for a second leading NOT gate. The exact finite Petersen List.any-to-OR rewrite was checked locally but not submitted as a duplicate of ten already-open exact pull requests.

https://github.com/SanThought/pequalnp-proofs/blob/main/2-supplemental-boundaries-2026-11-24.md

https://github.com/SanThought/pequalnp-proofs/blob/main/2-2-late-boundaries-2026-11-24.md

## Final assigned steps

L-meta-2542 and L-meta-3202 received bounded SAT searches on all 512 truth-table inputs. Both timed out without a witness or unsatisfiability certificate. The encodings cover clean binary topological circuits and do not establish equivalence to every formal circuit allowed by the assigned statement. Their code and logs are preserved in the companion diagnostic archive, not offered as a proof.

L-meta-3275 already had a transport reduction in upstream PR6259 covering all 21 cases through six first-AND lower bounds present on main. A local attempt to assemble those existing proofs into one file timed out twice. It was not a checked proof and was not submitted. This route is attribution-heavy assembly of existing work, not a new mathematical result.

https://github.com/brilliant-hq/pequalnp-proofs/pull/6259

https://github.com/brilliant-hq/pequalnp-proofs/pull/6260

All final allocations were released. No paid compute was used. Public notebook and archive snapshots preserve the successful Lean checks separately from unsuccessful diagnostics. No timeout is an impossibility proof.

## Anthropic reference

The vp-vnp README was revisited during the night. It describes an AI-written research artifact claiming an algebraic complexity separation, explicitly says no human mathematician has checked it, and says it does not settle P versus NP. We did not independently build the full artifact and do not upgrade its claim into an independently verified result.

https://github.com/anthropics/formal-math/blob/main/vp-vnp/README.md
