# General symmetric permanent-level dimension bound

November 24, 2026. Checked partial result for L-gct-232, not a proof of the full probe.

## The theorem

Let L be any complex linear subspace of symmetric 4 by 4 matrices. If permanent(J+t)=24 for every t in L, where J is the all-ones matrix, then dim(L) is at most 4. Unlike the zero-diagonal theorem, this result allows arbitrary diagonal entries.

The open probe asks whether a three-dimensional such subspace exists. A bound of 4 does not answer it. Together with our checked two-dimensional example, the currently proved bounds from this work are 2 ≤ maximum possible dimension ≤ 4. No proof of the full probe or its negation, upstream submission, or accepted credit is claimed.

## Checked proof route

The line condition permanent(J+zt)=24 forces the sum of all sixteen matrix entries to vanish. In ten symmetric coordinates this eliminates the last diagonal entry, leaving nine coordinates. The second coefficient of the permanent gives a quadratic form q in these coordinates. Its polar form is nondegenerate over the complex numbers.

The source proves nondegeneracy directly by testing against each of the nine coordinate vectors and recovering every input coordinate by explicit rational linear combinations. It does not rely on a numerical rank calculation. Polarization makes the coordinate subspace totally isotropic, so it lies in its orthogonal complement. In a nondegenerate nine-dimensional space this forces dimension at most 4. Finally, the nine-coordinate map is injective on the original matrix subspace, because symmetry and the zero-sum constraint recover the omitted entries.

All steps, including the full actual-matrix coordinate bridge, are in `FullQuadratic.lean`. The final theorem is `Gct232Full.symmetric_level_bound`. `full5.log` records a successful Lean 4.36.0 check and the final axioms: propext, Classical.choice, Quot.sound. There is no sorry or new axiom.

The archive also preserves `Proof3055.lean` and its successful `proof1.log`: the assigned finite Petersen List.any-to-OR rewrite was locally checked by simplification, with propext only. Ten existing exact pull requests were already open, so no duplicate upstream submission was made. This small rewrite is not the research goal or a new lower bound.

## Related checked work

Sharp bound of 2 for all zero-diagonal symmetric subspaces:
https://github.com/SanThought/pequalnp-proofs/commit/c974db9cfdb39f232ea45cc1908028f1ac96be69

Two-dimensional star plane and its maximality under inclusion:
https://github.com/SanThought/pequalnp-proofs/commit/b1ef137a3b47266df0e11c742c304a77d6baa85a

Neither maximality under inclusion nor the zero-diagonal restriction proves the general maximum dimension is 2.
