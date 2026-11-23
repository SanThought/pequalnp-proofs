import PEqualNP.Defs

-- Partial research for L-meta-1321, not a proof of its assigned count bound.
-- No upstream PR, accepted contribution credit, or novelty is claimed.
-- The missing step is a shared-circuit count without bounded pivot multiplicity.
-- Checked with Lean 4.36.0 and the retained project definitions.
-- Axiom audits list only propext, Classical.choice, and Quot.sound.
-- Context: https://pequalnp.com/ and the public brilliant-hq/pequalnp-proofs project.

namespace SanThought.Meta1321

/-- Any family of line neighborhoods in a rectangle-free incidence graph has
its intersection represented by at most three of its lines. This does not
prove the shared-circuit counting bound of L-meta-1321. -/
theorem pivot_compression
    {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (W : Finset (Fin N)) :
    ∃ U : Finset (Fin N), U ⊆ W ∧ U.card ≤ 3 ∧
      ∀ p, (∃ l ∈ W, ¬ I p l) ↔ ∃ l ∈ U, ¬ I p l := by
  classical
  by_cases hW : W.card ≤ 1
  · exact ⟨W, Finset.Subset.rfl, by omega, fun _ => Iff.rfl⟩
  have htwo : 1 < W.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  by_cases hx : ∃ p, I p a ∧ I p b
  · obtain ⟨q, hqa, hqb⟩ := hx
    have unique : ∀ p, I p a → I p b → p = q := by
      intro p hpa hpb
      by_contra hpq
      exact hI p q a b hpq hab ⟨hpa, hpb, hqa, hqb⟩
    by_cases hq : ∃ c ∈ W, ¬ I q c
    · obtain ⟨c, hc, hqc⟩ := hq
      refine ⟨{a, b, c}, ?_, ?_, ?_⟩
      · intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl | rfl <;> assumption
      · exact le_trans (Finset.card_insert_le ..) (by
          have := Finset.card_insert_le b ({c} : Finset (Fin N))
          simp only [Finset.card_singleton] at this
          omega)
      · intro p
        constructor
        · intro _
          by_cases hpa : I p a
          · by_cases hpb : I p b
            · have hpq := unique p hpa hpb
              subst p
              exact ⟨c, by simp, hqc⟩
            · exact ⟨b, by simp, hpb⟩
          · exact ⟨a, by simp, hpa⟩
        · rintro ⟨l, hl, hn⟩
          exact ⟨l, by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hl
            rcases hl with rfl | rfl | rfl <;> assumption, hn⟩
    · refine ⟨{a, b}, ?_, ?_, ?_⟩
      · intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl <;> assumption
      · have := Finset.card_insert_le a ({b} : Finset (Fin N))
        simp only [Finset.card_singleton] at this
        omega
      · intro p
        constructor
        · rintro ⟨c, hc, hpc⟩
          by_cases hpa : I p a
          · by_cases hpb : I p b
            · have hpq := unique p hpa hpb
              subst p
              exact False.elim (hq ⟨c, hc, hpc⟩)
            · exact ⟨b, by simp, hpb⟩
          · exact ⟨a, by simp, hpa⟩
        · rintro ⟨l, hl, hn⟩
          exact ⟨l, by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hl
            rcases hl with rfl | rfl <;> assumption, hn⟩
  · refine ⟨{a, b}, ?_, ?_, ?_⟩
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> assumption
    · have := Finset.card_insert_le a ({b} : Finset (Fin N))
      simp only [Finset.card_singleton] at this
      omega
    · intro p
      constructor
      · intro _
        by_cases hpa : I p a
        · exact ⟨b, by simp, fun hpb => hx ⟨p, hpa, hpb⟩⟩
        · exact ⟨a, by simp, hpa⟩
      · rintro ⟨l, hl, hn⟩
        exact ⟨l, by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl <;> assumption, hn⟩

/-- Choosing these representatives for every wire preserves the exact
singleton-pair eligibility predicate. Soundness for the smaller sets follows
by set inclusion, but there is still no multiplicity bound across wires. -/
theorem family_compression
    {N J : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hI : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (W : Fin J → Finset (Fin N)) :
    ∃ U : Fin J → Finset (Fin N),
      (∀ j, U j ⊆ W j ∧ (U j).card ≤ 3) ∧
      (∀ j p, (∃ l ∈ W j, ¬ I p l) ↔ ∃ l ∈ U j, ¬ I p l) ∧
      (∀ (j : Fin J) (z : Fin N → Bool),
        (∃ l ∈ U j, ∀ p, I p l → z p = false) →
        ∃ l ∈ W j, ∀ p, I p l → z p = false) := by
  classical
  choose U hU using fun j => pivot_compression I hI (W j)
  refine ⟨U, fun j => ⟨(hU j).1, (hU j).2.1⟩,
    fun j => (hU j).2.2, ?_⟩
  rintro j z ⟨l, hl, hz⟩
  exact ⟨l, (hU j).1 hl, hz⟩

#print axioms pivot_compression
#print axioms family_compression
end SanThought.Meta1321
