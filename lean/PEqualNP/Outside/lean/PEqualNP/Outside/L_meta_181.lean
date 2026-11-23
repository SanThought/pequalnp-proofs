import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.BitVec
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_181
def cost (n : Nat) : Nat :=
  if (57896044618658097711785492504343953926634992332820282019728792003956564819969 : Nat).testBit n then 0 else
  if (1766847064804095338292937922828216753893183071823361306064178494985764864 : Nat).testBit n then 1 else
  if (9117372569392856764669015109861959849500382286899122289979294063395260732456 : Nat).testBit n then 2 else
  if (47758897661557701488759287235646426057205668319895424902736186453577012177302 : Nat).testBit n then 3 else
  if (539305075065820977669866285898436195709996913423557566370083258761216 : Nat).testBit n then 4 else
  5
def low1 : List Nat := [15,51,85,170,204,240]
def low2 : List Nat := [3,5,10,12,17,34,48,63,68,80,95,119,136,160,175,187,192,207,221,238,243,245,250,252]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma cost_class : ∀ a : Fin 256, cost a.val = 0 ∨ (cost a.val = 1 ∧ a.val ∈ low1) ∨ (cost a.val = 2 ∧ a.val ∈ low2) ∨ 3 ≤ cost a.val := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma cost_one_pairs : ∀ a ∈ low1, ∀ b : Fin 256, cost (a &&& b.val) ≤ 1 + cost b.val ∧ cost (a ||| b.val) ≤ 1 + cost b.val := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma cost_two_pairs : ∀ a ∈ low2, ∀ b ∈ low2, cost (a &&& b) ≤ 4 ∧ cost (a ||| b) ≤ 4 := by decide
set_option maxRecDepth 10000 in
lemma cost_zero : ∀ a : Fin 256, cost a.val = 0 → a.val = 0 ∨ a.val = 255 := by decide
set_option maxRecDepth 10000 in
lemma cost_bound : ∀ a : Fin 256, cost a.val ≤ 5 := by decide
set_option maxRecDepth 10000 in
lemma cost_zero_pairs : ∀ a : Fin 256, cost a.val = 0 → ∀ b : Fin 256,
 cost (a.val &&& b.val) ≤ cost b.val ∧ cost (a.val ||| b.val) ≤ cost b.val := by
 intro a ha b
 have hh := cost_zero a ha
 rcases hh with h | h <;> rw [h] <;> revert b <;> decide
lemma cost_subadd (a b : Fin 256) : cost (a.val &&& b.val) ≤ cost a.val + cost b.val ∧
 cost (a.val ||| b.val) ≤ cost a.val + cost b.val := by
 by_cases ha : cost a.val = 0
 · simpa [ha] using cost_zero_pairs a ha b
 by_cases hb : cost b.val = 0
 · simpa [hb, Nat.and_comm, Nat.or_comm] using cost_zero_pairs b hb a
 rcases cost_class a with h | ⟨h, hm⟩ | ⟨h, hm⟩ | h
 · contradiction
 · simpa [h] using cost_one_pairs a.val hm b
 · rcases cost_class b with h' | ⟨h', hm'⟩ | ⟨h', hm'⟩ | h'
   · contradiction
   · simpa [h', Nat.add_comm, Nat.and_comm, Nat.or_comm] using cost_one_pairs b.val hm' a
   · simpa [h,h'] using cost_two_pairs a.val hm b.val hm'
   · have hc := cost_bound ⟨a.val &&& b.val, lt_of_le_of_lt Nat.and_le_left a.isLt⟩
     have hd := cost_bound ⟨a.val ||| b.val, Nat.or_lt_two_pow (n := 8) a.isLt b.isLt⟩
     dsimp at hc hd
     omega
 · rcases cost_class b with h' | ⟨h', hm'⟩ | ⟨h', hm'⟩ | h'
   · contradiction
   · simpa [h', Nat.add_comm, Nat.and_comm, Nat.or_comm] using cost_one_pairs b.val hm' a
   · have hc := cost_bound ⟨a.val &&& b.val, lt_of_le_of_lt Nat.and_le_left a.isLt⟩
     have hd := cost_bound ⟨a.val ||| b.val, Nat.or_lt_two_pow (n := 8) a.isLt b.isLt⟩
     dsimp at hc hd
     omega
   · have hc := cost_bound ⟨a.val &&& b.val, lt_of_le_of_lt Nat.and_le_left a.isLt⟩
     have hd := cost_bound ⟨a.val ||| b.val, Nat.or_lt_two_pow (n := 8) a.isLt b.isLt⟩
     dsimp at hc hd
     omega
open PEqualNP.MetaComplexity

def inp (m : Fin 8) (i : Fin 5) : Bool := if i.val < 3 then m.val.testBit i.val else false
def litMask (i : Fin 5) (b : Bool) : BitVec 8 :=
 if i.val = 0 then (if b then 170 else 85) else
 if i.val = 1 then (if b then 204 else 51) else
 if i.val = 2 then (if b then 240 else 15) else (if b then 0 else 255)
def sem : DMFormula 5 → BitVec 8
 | .lit i b => litMask i b
 | .and a b => sem a &&& sem b
 | .or a b => sem a ||| sem b

def core : DMFormula 5 → Nat
 | .lit i _ => if i.val < 3 then 1 else 0
 | .and a b | .or a b => core a + core b

def cnt (j : Fin 5) : DMFormula 5 → Nat
 | .lit i _ => if i = j then 1 else 0
 | .and a b | .or a b => cnt j a + cnt j b

lemma lit_sem : ∀ (i : Fin 5) (b : Bool) (m : Fin 8),
 (litMask i b).getLsbD m.val = (if b then inp m i else !(inp m i)) := by decide

lemma sem_correct (f : DMFormula 5) (m : Fin 8) :
 (sem f).getLsbD m.val = f.eval (inp m) := by
 induction f with
 | lit i b => exact lit_sem i b m
 | and a b ha hb => simp only [sem, BitVec.getLsbD_and, DMFormula.eval, ha, hb]
 | or a b ha hb => simp only [sem, BitVec.getLsbD_or, DMFormula.eval, ha, hb]

lemma lit_cost : ∀ (i : Fin 5) (b : Bool), cost (litMask i b).toNat ≤ if i.val < 3 then 1 else 0 := by decide

lemma cost_core (f : DMFormula 5) : cost (sem f).toNat ≤ core f := by
 induction f with
 | lit i b => exact lit_cost i b
 | and a b ha hb =>
   have h := (cost_subadd ⟨(sem a).toNat, (sem a).isLt⟩ ⟨(sem b).toNat, (sem b).isLt⟩).1
   simpa only [sem, core, BitVec.toNat_and] using (h.trans (Nat.add_le_add ha hb))
 | or a b ha hb =>
   have h := (cost_subadd ⟨(sem a).toNat, (sem a).isLt⟩ ⟨(sem b).toNat, (sem b).isLt⟩).2
   simpa only [sem, core, BitVec.toNat_or] using (h.trans (Nat.add_le_add ha hb))
def bull (x : Fin 5 → Bool) : Bool :=
 (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4)
lemma triangle_read : ∀ m : Fin 8, (232 : BitVec 8).getLsbD m.val = bull (inp m) := by decide
lemma core_lower (f : DMFormula 5) (hf : ∀ x, f.eval x = bull x) : 5 ≤ core f := by
 have hs : sem f = (232 : BitVec 8) := by
   apply BitVec.eq_of_getLsbD_eq
   intro i hi
   rw [sem_correct f ⟨i,hi⟩, hf, ← triangle_read ⟨i,hi⟩]
 have h := cost_core f
 rw [hs] at h
 have hh : cost (232 : BitVec 8).toNat = 5 := by decide
 rwa [hh] at h
lemma leaf_partition (f : DMFormula 5) : core f + cnt 3 f + cnt 4 f = f.leaves := by
 induction f with
 | lit i b =>
   have h : (if i.val < 3 then 1 else 0) + (if i = 3 then 1 else 0) + (if i = 4 then 1 else 0) = 1 := by
     revert i; decide
   exact h
 | and a b ha hb => simp only [core, cnt, DMFormula.leaves]; omega
 | or a b ha hb => simp only [core, cnt, DMFormula.leaves]; omega
lemma absent_eval (j : Fin 5) (f : DMFormula 5) (h : cnt j f = 0)
 (x y : Fin 5 → Bool) (hxy : ∀ i, i ≠ j → x i = y i) : f.eval x = f.eval y := by
 induction f with
 | lit i b =>
   have hi : i ≠ j := by intro e; simp [cnt,e] at h
   simp only [DMFormula.eval, hxy i hi]
 | and a b ha hb =>
   simp only [cnt] at h
   simp only [DMFormula.eval, ha (by omega), hb (by omega)]
 | or a b ha hb =>
   simp only [cnt] at h
   simp only [DMFormula.eval, ha (by omega), hb (by omega)]
lemma pendant_essential : ∀ j : Fin 5, j = 3 ∨ j = 4 →
 ∃ x y : Fin 5 → Bool, (∀ i, i ≠ j → x i = y i) ∧ bull x ≠ bull y := by
 intro j hj
 rcases hj with rfl | rfl
 · refine ⟨(fun i => decide (i = 0)), (fun i => decide (i = 0 ∨ i = 3)), ?_, ?_⟩
   · decide
   · decide
 · refine ⟨(fun i => decide (i = 1)), (fun i => decide (i = 1 ∨ i = 4)), ?_, ?_⟩
   · decide
   · decide
lemma pendant_present (j : Fin 5) (hj : j = 3 ∨ j = 4) (f : DMFormula 5)
 (hf : ∀ x, f.eval x = bull x) : 1 ≤ cnt j f := by
 by_contra h
 have hz : cnt j f = 0 := by omega
 obtain ⟨x,y,hxy,hne⟩ := pendant_essential j hj
 have he := absent_eval j f hz x y hxy
 rw [hf, hf] at he
 exact hne he
lemma lower (f : DMFormula 5) (hf : ∀ x, f.eval x = bull x) : 7 ≤ f.leaves := by
 have h0 := core_lower f hf
 have h3 := pendant_present 3 (Or.inl rfl) f hf
 have h4 := pendant_present 4 (Or.inr rfl) f hf
 have hp := leaf_partition f
 omega




def upper : DMFormula 5 :=
  .or (.and (.lit 0 true) (.or (.lit 1 true) (.or (.lit 2 true) (.lit 3 true))))
      (.and (.lit 1 true) (.or (.lit 2 true) (.lit 4 true)))
lemma upper_leaves : upper.leaves = 7 := rfl
lemma upper_eval (x : Fin 5 → Bool) : upper.eval x =
  ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4)) := by
  simp only [upper, DMFormula.eval, ite_true]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> decide

end PEqualNP.Outside.L_meta_181

theorem PEqualNP.Outside.L_meta_181 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 7 ≤ s := by
 intro s
 constructor
 · rintro ⟨f,hf,he⟩
   exact (PEqualNP.Outside.L_meta_181.lower f he).trans hf
 · intro hs
   refine ⟨PEqualNP.Outside.L_meta_181.upper, ?_, ?_⟩
   · simpa only [PEqualNP.Outside.L_meta_181.upper_leaves] using hs
   · exact PEqualNP.Outside.L_meta_181.upper_eval
