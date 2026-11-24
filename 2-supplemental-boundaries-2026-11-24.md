# Supplemental checked boundaries

SanThought, November 24, 2026.

These are supporting results from the overnight research, not complete proofs of the assigned open steps. No upstream acceptance or P vs NP solution is claimed.

## The 17-input plane patch, L-meta-2644

`Baseline24.lean` checks the exact 20 positive masks, 44 negative masks, monotone fan-in-two condition, backward wiring, and circuit size for a concrete **24-gate** witness. The assigned target is **23 gates**, so this misses the target by one. Its final axiom audit lists only `propext`.

`Classification32.lean` checks a finite classification of the 32 point-subset completions: each is contained in a listed negative mask or is one of eight exceptions. `IndependentCompletion.lean` proves the general fact that an independent input is contained in the completion of its point set, and that monotonicity lets rejection tests on completions reject smaller independent inputs. These two results are supporting pieces. The archive does not contain a checked theorem identifying the explicit 32-mask list with all completions of the encoded patch graph.

An independent Python enumeration found that the only independent inputs not contained in a negative test are the eight six-bit exception masks. That full enumeration is diagnostic, not a Lean certificate. Attempts to check all 131072 inputs in one theorem were too slow and are not included as completed results. No 23-gate witness was found. Search timeouts are not impossibility proofs.

## Semantic factors, L-meta-2008

`SemanticFactors.lean` proves that a monotone Boolean function with equal all-false/all-true endpoint values in one block is independent of that block. It also proves that two nonconstant factors at a non-cross AND must be pure on opposite blocks. This clarifies the semantic dependence condition in the assignment. It does **not** bound the global cost of the exceptional cross gates or prove the requested projective-plane circuit lower bound.

## Fixed nesting budget, L-meta-1764

`FixedKGirth1764.lean`, `FixedKBounds1764.lean`, and `FixedKConstant1764.lean` extend the previously published `BoundedGeneral1764.lean`. They give the girth-at-least-five form, elementary monotonicity of the recurrence, and existence of a constant for each **fixed** nesting-pair budget K. The constant still depends on K. They do **not** establish the single constant uniform over unrestricted nesting required by the full target.

## Checking

Sources and successful check logs are bundled in `supplemental-boundaries-2026-11-24.zip`. Use the project's pinned Lean 4.36.0 environment and dependency paths. The files in separate topic directories are independent, and the fixed-K snapshots include the earlier proof directly. Audit output is included in the logs. Only standard axioms occur in successful final checks.

These are research artifacts on SanThought's fork, not submission-format proofs or a claim of original authorship over inherited frameworks. The earlier fixed-K base proof and its provenance remain documented in this repository's fixed-K notebook.
