# Late checked boundaries, November 24, 2026

These are checked partial results, not solutions of the assigned statements. No upstream proof submission or accepted credit is claimed.

## Complex symmetric permanent probe 232

`ZeroDiagonal.lean` proves an exact expansion of permanent(J + zM) for a symmetric 4 by 4 matrix with zero diagonal. If this is 24 for every complex z, its six upper-triangular entries b,c,d,f,g,i satisfy

    b+c+d+f+g+i = 0
    b^2+b*c+b*d+b*f+b*g-c*g-d*f = 0.

The file is self-contained and includes the explicit 24-permutation expansion from our earlier StarMaximal work. `zero3.log` records a successful Lean check with only propext, Classical.choice and Quot.sound. This is a necessary-condition result for zero-diagonal directions. It does not establish a subspace dimension bound and does not settle the general probe, which allows nonzero diagonals.

Earlier maximal two-dimensional star-plane result:
https://github.com/SanThought/pequalnp-proofs/commit/b1ef137a3b47266df0e11c742c304a77d6baa85a

## Heawood search 2876

`Baseline27.lean` gives a monotone two-input, reads-back circuit of exactly 27 gates, checked on all 21 edge rows and 37 explicit maximal-independent-set rows. `baseline1.log` has exit 0 and only propext. The desired parent budget is 26, and the assigned internal-prefix target is 25 gates with crossing wires. Neither is solved. No formal theorem identifying the boundary lists with all minimal or maximal rows is claimed here.

A 100-second SAT search for a 25-gate two-output prefix timed out. A separate 110-second stochastic 26-gate search stayed one boundary row wrong. Ten restricted repairs found no witness. These are diagnostics, not global unsatisfiability certificates. Existing reductions already cover the bit encoding and orbit transport, so no duplicate reduction was submitted:
https://github.com/brilliant-hq/pequalnp-proofs/pull/5732
https://github.com/brilliant-hq/pequalnp-proofs/pull/5812

## Two leading NOT gates, Petersen-minus-vertex 3057

`SecondNotNormalization.lean` proves that the second NOT, after NOT x0, has only eleven distinct input semantics: a negated original input, x0, or constant true. Arbitrary extra pins are ignored by NOT, and an absent first pin reads false. `norm3.log` records a successful check with standard axioms only.

`NotBudget.lean` proves a conditional counting helper: a 13-non-NOT lower bound, two initial NOT gates, and at most 13 suffix gates force exactly 13 non-NOT suffix gates. It also converts FanInTwo plus absence of NOT gates to Monotone2. The lower bound is an assumption of this helper, not a new proof of the full assigned 3057 statement. The concrete leading pin lists are used only for operation counting. `budget3.log` records a successful check with standard axioms only.

## Reproduction

Sources were checked using Lean 4.36.0 and the existing pequalnp-proofs Mathlib environment. No sorry or new axiom is introduced. Logs are original compiler output. All source snapshots and successful logs are in the accompanying archive. Search code is included separately as diagnostic code, not as a verified solver or certificate.
