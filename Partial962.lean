import Mathlib.Data.Finset.Max
import PEqualNP.Defs

-- Partial feasibility research only, not a proof of the assigned L-meta-962 statement.
-- Checked locally with Lean 4.36.0; no upstream acceptance or contribution credit claimed.
-- Final result bounds degree-at-least-two vertices by 256 for circuits with at most four gates.
-- Missing: pendant-vertex reduction, finite classification, and checked certificates.
-- Monotonicity proof structure adapted from the Apache-2.0 pequalnp-proofs project,
-- file lean/PEqualNP/Outside/L_meta_562.lean. See the participation record for provenance.

namespace PEqualNP.Outside.L_meta_962
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

def Independent {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w

def Maximal {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  Independent G I ∧ ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v

lemma extend_independent {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : Independent G S) : ∃ I, S ⊆ I ∧ Maximal G I := by
  classical
  let F := Finset.univ.filter (fun I : Finset (Fin n) => S ⊆ I ∧ Independent G I)
  have hn : F.Nonempty := ⟨S, by simp [F, hS]⟩
  obtain ⟨I, hi, hmax⟩ := Finset.exists_max_image F Finset.card hn
  have hh : S ⊆ I ∧ Independent G I := by simpa [F] using hi
  refine ⟨I, hh.1, hh.2, ?_⟩
  intro u hu
  by_contra! ha
  have hind : Independent G (insert u I) := by
    intro v hv w hw
    simp only [Finset.mem_insert] at hv hw
    rcases hv with rfl | hv <;> rcases hw with rfl | hw
    · exact fun h => G.irrefl h
    · exact ha w hw
    · exact fun h => ha v hv (G.adj_symm h)
    · exact hh.2 v hv w hw
  have hm := hmax (insert u I) (by simp [F, hind, hh.1.trans (Finset.subset_insert u I)])
  rw [Finset.card_insert_of_notMem hu] at hm
  omega

lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

lemma eval_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (hU : C.eval U = true) : C.eval V = true := by
  simp only [eval, decide_eq_true_eq] at hU ⊢
  rcases hU with ⟨v,hv,hU⟩ | ⟨i,hi,hU⟩
  · exact Or.inl ⟨v,hv,hUV hU⟩
  · exact Or.inr ⟨i,hi,gateVal_mono_U C hUV i hU⟩

lemma false_independent {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (h : ∀ I, Maximal G I → C.eval I = false)
    (S : Finset (Fin n)) (hs : Independent G S) : C.eval S = false := by
  obtain ⟨I, hSI, hi⟩ := extend_independent G S hs
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm := eval_mono_U C hSI ht
  rw [h I hi] at hm
  contradiction

def Separates {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I, Maximal G I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

def MaskLe {n : ℕ} (C : AndCountCircuit n) (v w : Fin n) : Prop :=
  ∀ i, (v ∈ C.leftVars i → w ∈ C.leftVars i) ∧
       (v ∈ C.rightVars i → w ∈ C.rightVars i)

lemma out_empty {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (h : Separates G C) : C.outVars = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hind : Independent G {v} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact fun hh => G.irrefl hh
  have hf := false_independent G C (fun I hi => (h I hi).1) {v} hind
  have ht : C.eval {v} = true := by simp [eval, hv]
  rw [hf] at ht
  contradiction

lemma side_masked {n k : ℕ} (I : Finset (Fin n)) (v w : Fin n) (hw : w ∈ I)
    (B : Finset (Fin n)) (hp : v ∈ B → w ∈ B)
    (F : Finset (Fin k)) (i : Fin k) (vals : Fin k → Bool) :
    sideTrue (insert v I) B F i vals = sideTrue I B F i vals := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨u,hu,hi⟩ | hh)
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inl ⟨w,hp hu,hw⟩
      · exact Or.inl ⟨u,hu,hi⟩
    · exact Or.inr hh
  · rintro (⟨u,hu,hi⟩ | hh)
    · exact Or.inl ⟨u,hu,Finset.mem_insert_of_mem hi⟩
    · exact Or.inr hh

lemma mask_forces_membership {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (h : Separates G C) (v w : Fin n) (hm : MaskLe C v w)
    (I : Finset (Fin n)) (hi : Maximal G I) (hw : w ∈ I) : v ∈ I := by
  by_contra hv
  have hf (d : ℕ) : C.gateValFuel (insert v I) d = C.gateValFuel I d := by
    induction d with
    | zero => rfl
    | succ d ih =>
      funext i
      simp only [gateValFuel, ih, side_masked I v w hw _ (hm i).1,
        side_masked I v w hw _ (hm i).2]
  have he : C.eval (insert v I) = C.eval I := by
    simp only [eval, out_empty G C h, Finset.notMem_empty, false_and, gateVal, hf]
  have ht := (h I hi).2 v hv
  rw [he, (h I hi).1] at ht
  contradiction

lemma adjacent_not_masked {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (h : Separates G C) (v w : Fin n) (hadj : G.Adj v w) : ¬ MaskLe C v w := by
  intro hm
  have hs : Independent G {w} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact fun hh => G.irrefl hh
  obtain ⟨I,hw,hi⟩ := extend_independent G {w} hs
  have hwI : w ∈ I := hw (by simp)
  have hvI := mask_forces_membership G C h v w hm I hi hwI
  exact hi.1 v hvI w hwI hadj

lemma mask_neighborhood {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (h : Separates G C) (v w : Fin n) (hm : MaskLe C v w) :
    ∀ u, G.Adj v u → G.Adj w u := by
  intro u hvu
  by_contra hwu
  have hs : Independent G {w,u} := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun hh => G.irrefl hh
    · exact hwu
    · exact fun hh => hwu (G.adj_symm hh)
    · exact fun hh => G.irrefl hh
  obtain ⟨I,hsub,hi⟩ := extend_independent G {w,u} hs
  have hw : w ∈ I := hsub (by simp)
  have hu : u ∈ I := hsub (by simp)
  have hv := mask_forces_membership G C h v w hm I hi hw
  exact hi.1 v hv u hu hvu

lemma equivalent_masks_low_degree {n : ℕ} (G : SimpleGraph (Fin n))
    (sq : ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b →
      G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (C : AndCountCircuit n) (h : Separates G C) (v w : Fin n) (hne : v ≠ w)
    (hvw : MaskLe C v w) :
    ∀ a b, G.Adj v a → G.Adj v b → a = b := by
  intro a b hva hvb
  by_contra hab
  have hwa := mask_neighborhood G C h v w hvw a hva
  have hwb := mask_neighborhood G C h v w hvw b hvb
  exact sq v a w b hne hab hva (G.adj_symm hwa) hwb (G.adj_symm hvb)

def High {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b

lemma core_card_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (sq : ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b →
      G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (C : AndCountCircuit n) (h : Separates G C) :
    Nat.card {v : Fin n // High G v} ≤ 2 ^ (2 * C.size) := by
  classical
  let code (v : {v : Fin n // High G v}) (i : Fin C.size) : Bool × Bool :=
    (decide (v.val ∈ C.leftVars i), decide (v.val ∈ C.rightVars i))
  have inj : Function.Injective code := by
    intro v w he
    apply Subtype.ext
    by_contra hne
    have hm : MaskLe C v.val w.val := by
      intro i
      have hh := congrFun he i
      have hl := congrArg Prod.fst hh
      have hr := congrArg Prod.snd hh
      change decide (_ ∈ _) = decide (_ ∈ _) at hl hr
      exact ⟨(decide_eq_decide.mp hl).mp, (decide_eq_decide.mp hr).mp⟩
    obtain ⟨a,b,hab,hva,hvb⟩ := v.property
    exact hab (equivalent_masks_low_degree G sq C h v.val w.val hne hm a b hva hvb)
  have hc := Fintype.card_le_of_injective code inj
  rw [Nat.card_eq_fintype_card]
  have he : 4 ^ C.size = 2 ^ (2 * C.size) := by
    calc 4 ^ C.size = (2 ^ 2) ^ C.size := rfl
         _ = 2 ^ (2 * C.size) := (Nat.pow_mul 2 2 C.size).symm
  simpa only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    show (2 : ℕ) * 2 = 4 from rfl, he] using hc

lemma core_at_most_256 {n : ℕ} (G : SimpleGraph (Fin n))
    (sq : ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b →
      G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (C : AndCountCircuit n) (h : Separates G C) (hs : C.size ≤ 4) :
    Nat.card {v : Fin n // High G v} ≤ 256 := by
  have hc := core_card_bound G sq C h
  have hp : 2 ^ (2 * C.size) ≤ 2 ^ (2 * 4) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hs)
  exact hc.trans hp

end PEqualNP.Outside.L_meta_962
