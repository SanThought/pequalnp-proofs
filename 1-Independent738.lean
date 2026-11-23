import Mathlib.Data.Fintype.BigOperators
import Aesop
import Lean.Elab.Tactic.Omega
import PEqualNP.Defs.LineDegree

namespace Transposition738.Builder
open PEqualNP.CircuitLowerBounds
attribute [local instance] lineDegreeGateOpDecEq

inductive Ref where
  | bot | top | wire : ℕ → Ref
  deriving DecidableEq

def Ref.value (vs : List Bool) : Ref → Bool
  | .bot => false
  | .top => true
  | .wire i => vs.getD i false

def Ref.Valid (n : ℕ) : Ref → Prop
  | .bot | .top => True
  | .wire i => i < n

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map (fun i => vs.getD i false))]) x

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run, List.foldl_cons]
    rw [← run, ih]
    simp
    omega

lemma run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp [run, List.foldl_append]

lemma run_singleton (g : Gate) (x : List Bool) :
    run [g] x = x ++ [g.op.eval (g.inputs.map (fun i => x.getD i false))] := rfl

lemma run_extends (gs : List Gate) (x : List Bool) : ∃ z, run gs x = x ++ z := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨z, hz⟩ := ih (x ++ [g.op.eval (g.inputs.map (fun i => x.getD i false))])
    exact ⟨_ :: z, by simpa [run, List.append_assoc] using hz⟩

lemma Ref.value_append (a : Ref) (vs ws : List Bool) (h : a.Valid vs.length) :
    a.value (vs ++ ws) = a.value vs := by
  cases a with
  | bot => rfl
  | top => rfl
  | wire i => simp only [value]; simp only [List.getD]; rw [List.getElem?_append_left h]

lemma Ref.value_run (a : Ref) (gs : List Gate) (vs : List Bool) (h : a.Valid vs.length) :
    a.value (run gs vs) = a.value vs := by
  obtain ⟨z, hz⟩ := run_extends gs vs
  rw [hz]
  exact a.value_append vs z h

-- Gate wire numbering depends on the point-input count.
def meet (n : ℕ) (gs : List Gate) : Ref → Ref → List Gate × Ref
  | .bot, _ | _, .bot => (gs, .bot)
  | .top, b => (gs, b)
  | a, .top => (gs, a)
  | .wire i, .wire j => (gs ++ [⟨.and, [i,j]⟩], .wire (n + gs.length))

def join (n : ℕ) (gs : List Gate) : Ref → Ref → List Gate × Ref
  | .top, _ | _, .top => (gs, .top)
  | .bot, b => (gs, b)
  | a, .bot => (gs, a)
  | .wire i, .wire j => (gs ++ [⟨.or, [i,j]⟩], .wire (n + gs.length))

lemma meet_cost (n : ℕ) (gs : List Gate) (a b : Ref) :
    (meet n gs a b).1.length ≤ gs.length + 1 := by
  cases a <;> cases b <;> simp [meet]

lemma join_cost (n : ℕ) (gs : List Gate) (a b : Ref) :
    (join n gs a b).1.length ≤ gs.length + 1 := by
  cases a <;> cases b <;> simp [join]

lemma meet_correct (n : ℕ) (gs : List Gate) (a b : Ref)
    (x : List Bool) (hx : x.length = n) :
    (meet n gs a b).2.value (run (meet n gs a b).1 x) =
      (a.value (run gs x) && b.value (run gs x)) := by
  cases a <;> cases b <;> simp [meet, Ref.value]
  rw [run_append, run_singleton]
  have hl := run_length gs x
  simp only [hx] at hl
  rw [List.getElem?_append_right (by omega)]
  simp [hl, GateOp.eval]

lemma join_correct (n : ℕ) (gs : List Gate) (a b : Ref)
    (x : List Bool) (hx : x.length = n) :
    (join n gs a b).2.value (run (join n gs a b).1 x) =
      (a.value (run gs x) || b.value (run gs x)) := by
  cases a <;> cases b <;> simp [join, Ref.value]
  rw [run_append, run_singleton]
  have hl := run_length gs x
  simp only [hx] at hl
  rw [List.getElem?_append_right (by omega)]
  simp [hl, GateOp.eval]

lemma meet_valid (n : ℕ) (gs : List Gate) (a b : Ref)
    (ha : a.Valid (n + gs.length)) (hb : b.Valid (n + gs.length)) :
    (meet n gs a b).2.Valid (n + (meet n gs a b).1.length) := by
  cases a <;> cases b <;> simp_all [meet, Ref.Valid]

lemma join_valid (n : ℕ) (gs : List Gate) (a b : Ref)
    (ha : a.Valid (n + gs.length)) (hb : b.Valid (n + gs.length)) :
    (join n gs a b).2.Valid (n + (join n gs a b).1.length) := by
  cases a <;> cases b <;> simp_all [join, Ref.Valid]

lemma meet_prefix (n : ℕ) (gs : List Gate) (a b : Ref) :
    ∃ hs, (meet n gs a b).1 = gs ++ hs := by
  cases a <;> cases b <;> simp [meet]

lemma join_prefix (n : ℕ) (gs : List Gate) (a b : Ref) :
    ∃ hs, (join n gs a b).1 = gs ++ hs := by
  cases a <;> cases b <;> simp [join]

lemma meet_monotone (n : ℕ) (gs : List Gate) (a b : Ref)
    (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ g ∈ (meet n gs a b).1, g.op = .and ∨ g.op = .or := by
  cases a <;> cases b <;> simp_all [meet] <;> aesop

lemma join_monotone (n : ℕ) (gs : List Gate) (a b : Ref)
    (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ g ∈ (join n gs a b).1, g.op = .and ∨ g.op = .or := by
  cases a <;> cases b <;> simp_all [join] <;> aesop

lemma meet_fanin (n : ℕ) (gs : List Gate) (a b : Ref)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ g ∈ (meet n gs a b).1, g.inputs.length ≤ 2 := by
  cases a <;> cases b <;> simp_all [meet] <;> aesop

lemma join_fanin (n : ℕ) (gs : List Gate) (a b : Ref)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ g ∈ (join n gs a b).1, g.inputs.length ≤ 2 := by
  cases a <;> cases b <;> simp_all [join] <;> aesop

lemma meet_preserves (n : ℕ) (gs : List Gate) (a b c : Ref)
    (x : List Bool) (hx : x.length = n) (hc : c.Valid (n + gs.length)) :
    c.value (run (meet n gs a b).1 x) = c.value (run gs x) := by
  obtain ⟨hs, hh⟩ := meet_prefix n gs a b
  rw [hh, run_append]
  apply Ref.value_run
  simpa [run_length, hx] using hc

lemma join_preserves (n : ℕ) (gs : List Gate) (a b c : Ref)
    (x : List Bool) (hx : x.length = n) (hc : c.Valid (n + gs.length)) :
    c.value (run (join n gs a b).1 x) = c.value (run gs x) := by
  obtain ⟨hs, hh⟩ := join_prefix n gs a b
  rw [hh, run_append]
  apply Ref.value_run
  simpa [run_length, hx] using hc


-- This algorithm is only research scaffolding until its global invariant is proved.
def combine (n : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref) : List Gate × Ref :=
  match rs with
  | [] => (gs, if op = .and then .top else .bot)
  | [a] => (gs,a)
  | [a,b] => if op = .and then meet n gs a b else join n gs a b
  | _ => (gs,.bot)

lemma combine_cost (n : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref) :
    (combine n op gs rs).1.length ≤ gs.length + 1 := by
  cases rs with
  | nil => simp [combine]
  | cons a rs =>
    cases rs with
    | nil => simp [combine]
    | cons b rs =>
      cases rs with
      | nil => simp only [combine]; split
               · exact meet_cost _ _ _ _
               · exact join_cost _ _ _ _
      | cons c rs => simp [combine]

lemma combine_prefix (n : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref) :
    ∃ hs, (combine n op gs rs).1 = gs ++ hs := by
  cases rs with
  | nil => exact ⟨[], by simp [combine]⟩
  | cons a rs =>
    cases rs with
    | nil => exact ⟨[], by simp [combine]⟩
    | cons b rs =>
      cases rs with
      | nil => simp only [combine]; split
               · exact meet_prefix _ _ _ _
               · exact join_prefix _ _ _ _
      | cons c rs => exact ⟨[], by simp [combine]⟩

lemma combine_monotone (n : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref)
    (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ g ∈ (combine n op gs rs).1, g.op = .and ∨ g.op = .or := by
  cases rs with
  | nil => simpa only [combine] using h
  | cons a rs =>
    cases rs with
    | nil => exact h
    | cons b rs =>
      cases rs with
      | nil => simp only [combine]; split
               · exact meet_monotone _ _ _ _ h
               · exact join_monotone _ _ _ _ h
      | cons c rs => exact h

lemma combine_fanin (n : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ g ∈ (combine n op gs rs).1, g.inputs.length ≤ 2 := by
  cases rs with
  | nil => exact h
  | cons a rs =>
    cases rs with
    | nil => exact h
    | cons b rs =>
      cases rs with
      | nil => simp only [combine]; split
               · exact meet_fanin _ _ _ _ h
               · exact join_fanin _ _ _ _ h
      | cons c rs => exact h

structure State where
  gates : List Gate
  refs : List Ref

def copyStep (P : ℕ) (ds : List ℕ) (s : State) (jg : ℕ × Gate) : State :=
  let (j,g) := jg
  if ds.getD j 0 = 0 then
    let r := combine P g.op s.gates (g.inputs.map (fun i => s.refs.getD i .bot))
    ⟨r.1, s.refs ++ [r.2]⟩
  else ⟨s.gates, s.refs ++ [.bot]⟩

def copyPoints (P L : ℕ) (C : Circuit) : State :=
  let n := P+L
  let ds := C.lineDegrees n (Finset.Ico P n)
  (C.gates.zipIdx.map (fun (g,j) => (n+j,g))).foldl (copyStep P ds)
    ⟨[], (List.range P).map Ref.wire ++ List.replicate L .bot⟩

def send (P : ℕ) (s : State) (i : ℕ) (r : Ref) : State :=
  let z := join P s.gates (s.refs.getD i .bot) r
  ⟨z.1, s.refs.set i z.2⟩

def reverseStep (P : ℕ) (ds : List ℕ) (points : List Ref)
    (jg : ℕ × Gate) (s : State) : State :=
  let (j,g) := jg
  if ds.getD j 0 = 0 then s else
  let ys := g.inputs.filter (fun i => i < j ∧ 0 < ds.getD i 0)
  let c := s.refs.getD j .bot
  if g.op = .or then ys.foldl (fun z i => send P z i c) s else
  match ys with
  | [i] =>
    let zs := g.inputs.filter (fun k => ¬(k < j ∧ 0 < ds.getD k 0))
    let r := combine P .and s.gates
      (c :: zs.map (fun k => if k < j then points.getD k .bot else .bot))
    send P ⟨r.1,s.refs⟩ i r.2
  | _ => s

def reverseContexts (P L : ℕ) (C : Circuit) : State :=
  let n := P+L
  let ds := C.lineDegrees n (Finset.Ico P n)
  let pts := copyPoints P L C
  let ctx := (List.replicate (n+C.gates.length) Ref.bot).set C.output .top
  (C.gates.zipIdx.map (fun (g,j) => (n+j,g))).foldr
    (reverseStep P ds pts.refs) ⟨pts.gates,ctx⟩

def candidate (P L : ℕ) (C : Circuit) : Circuit :=
  ⟨(reverseContexts P L C).gates,0⟩

def trueCoefficients (P L : ℕ) (C : Circuit) : Finset (Fin L) :=
  Finset.univ.filter (fun i => (reverseContexts P L C).refs.getD (P+i.val) .bot = .top)

def coefficientOutput (P L : ℕ) (C : Circuit) (i : Fin L) : ℕ :=
  match (reverseContexts P L C).refs.getD (P+i.val) .bot with
  | .wire j => j
  | _ => P + (candidate P L C).size

def State.Good (s : State) : Prop :=
  (∀ g ∈ s.gates, g.op = .and ∨ g.op = .or) ∧ (∀ g ∈ s.gates, g.inputs.length ≤ 2)

lemma send_cost (P : ℕ) (s : State) (i : ℕ) (r : Ref) :
    (send P s i r).gates.length ≤ s.gates.length + 1 := join_cost _ _ _ _

lemma send_cost_first (P : ℕ) (s : State) (i : ℕ) (r : Ref)
    (hi : s.refs.getD i .bot = .bot) : (send P s i r).gates = s.gates := by
  simp only [send, hi]
  cases r <;> rfl

lemma send_refs_length (P : ℕ) (s : State) (i : ℕ) (r : Ref) :
    (send P s i r).refs.length = s.refs.length := by simp [send]

lemma copyStep_refs_length (P : ℕ) (ds : List ℕ) (s : State) (jg : ℕ × Gate) :
    (copyStep P ds s jg).refs.length = s.refs.length + 1 := by
  rcases jg with ⟨j,g⟩
  dsimp only [copyStep]
  split <;> simp

lemma copyStep_cost (P : ℕ) (ds : List ℕ) (s : State) (jg : ℕ × Gate) :
    (copyStep P ds s jg).gates.length ≤ s.gates.length + if ds.getD jg.1 0 = 0 then 1 else 0 := by
  rcases jg with ⟨j,g⟩
  dsimp only [copyStep]
  split
  · simp only [State.gates]
    exact combine_cost _ _ _ _
  · simp

lemma copyFold_cost (P : ℕ) (ds : List ℕ) (ls : List (ℕ × Gate)) (s : State) :
    (ls.foldl (copyStep P ds) s).gates.length ≤
      s.gates.length + (ls.filter (fun jg => ds.getD jg.1 0 = 0)).length := by
  induction ls generalizing s with
  | nil => simp
  | cons jg ls ih =>
    have hi := ih (copyStep P ds s jg)
    have hc := copyStep_cost P ds s jg
    change (ls.foldl (copyStep P ds) (copyStep P ds s jg)).gates.length ≤ _
    by_cases hz : ds.getD jg.1 0 = 0
    · simp only [List.filter_cons, hz, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, List.length_cons] at *
      omega
    · simp only [List.filter_cons, hz, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, List.length_cons] at *
      omega

lemma copyFold_refs_length (P : ℕ) (ds : List ℕ) (ls : List (ℕ × Gate)) (s : State) :
    (ls.foldl (copyStep P ds) s).refs.length = s.refs.length + ls.length := by
  induction ls generalizing s with
  | nil => simp
  | cons jg ls ih =>
    change (ls.foldl (copyStep P ds) (copyStep P ds s jg)).refs.length = _
    rw [ih, copyStep_refs_length]
    simp
    omega

lemma copyPoints_refs_length (P L : ℕ) (C : Circuit) :
    (copyPoints P L C).refs.length = P+L+C.gates.length := by
  unfold copyPoints
  rw [copyFold_refs_length]
  simp

lemma good_combine (P : ℕ) (s : State) (op : GateOp) (rs : List Ref) (ctx : List Ref)
    (h : s.Good) : (State.mk (combine P op s.gates rs).1 ctx).Good := by
  exact ⟨combine_monotone _ _ _ _ h.1, combine_fanin _ _ _ _ h.2⟩

lemma good_join (P : ℕ) (s : State) (a b : Ref) (ctx : List Ref) (h : s.Good) :
    (State.mk (join P s.gates a b).1 ctx).Good := by
  exact ⟨join_monotone _ _ _ _ h.1, join_fanin _ _ _ _ h.2⟩

lemma good_copyStep (P : ℕ) (ds : List ℕ) (s : State) (jg : ℕ × Gate)
    (h : s.Good) : (copyStep P ds s jg).Good := by
  rcases jg with ⟨j,g⟩
  dsimp only [copyStep]
  split
  · exact good_combine _ _ _ _ _ h
  · exact h

lemma good_send (P : ℕ) (s : State) (i : ℕ) (r : Ref) (h : s.Good) :
    (send P s i r).Good := good_join _ _ _ _ _ h

lemma good_foldl {α : Type} (f : State → α → State) (ls : List α) (s : State)
    (hf : ∀ z a, z.Good → (f z a).Good) (hs : s.Good) : (ls.foldl f s).Good := by
  induction ls generalizing s with
  | nil => exact hs
  | cons a ls ih => exact ih _ (hf _ _ hs)

lemma good_foldr {α : Type} (f : α → State → State) (ls : List α) (s : State)
    (hf : ∀ a z, z.Good → (f a z).Good) (hs : s.Good) : (ls.foldr f s).Good := by
  induction ls with
  | nil => exact hs
  | cons a ls ih => exact hf _ _ ih

lemma good_copyPoints (P L : ℕ) (C : Circuit) : (copyPoints P L C).Good := by
  apply good_foldl
  · exact fun _ _ h => good_copyStep _ _ _ _ h
  · constructor <;> simp

lemma good_reverseStep (P : ℕ) (ds : List ℕ) (points : List Ref) (jg : ℕ × Gate)
    (s : State) (h : s.Good) : (reverseStep P ds points jg s).Good := by
  rcases jg with ⟨j,g⟩
  dsimp only [reverseStep]
  split
  · exact h
  · split
    · apply good_foldl
      · exact fun _ _ hh => good_send _ _ _ _ hh
      · exact h
    · split
      · apply good_send
        exact good_combine _ _ _ _ _ h
      · exact h

lemma good_reverseContexts (P L : ℕ) (C : Circuit) : (reverseContexts P L C).Good := by
  apply good_foldr
  · exact fun _ _ h => good_reverseStep _ _ _ _ _ h
  · exact good_copyPoints _ _ _

lemma candidate_monotone (P L : ℕ) (C : Circuit) : IsMonotoneCircuit (candidate P L C) :=
  (good_reverseContexts P L C).1

lemma candidate_fanin (P L : ℕ) (C : Circuit) :
    ∀ g ∈ (candidate P L C).gates, g.inputs.length ≤ 2 :=
  (good_reverseContexts P L C).2

example : (candidate 2 2 ⟨[⟨.and,[0,2]⟩,⟨.and,[1,3]⟩,⟨.or,[4,5]⟩],6⟩).size = 0 := by decide
example : coefficientOutput 2 2 ⟨[⟨.and,[0,2]⟩,⟨.and,[1,3]⟩,⟨.or,[4,5]⟩],6⟩ ⟨0,by omega⟩ = 0 := by decide
example : coefficientOutput 2 2 ⟨[⟨.and,[0,2]⟩,⟨.and,[1,3]⟩,⟨.or,[4,5]⟩],6⟩ ⟨1,by omega⟩ = 1 := by decide


lemma Ref.valid_mono (r : Ref) {n m : ℕ} (h : n ≤ m) (hr : r.Valid n) : r.Valid m := by
  cases r <;> simp_all [Ref.Valid] <;> omega

lemma valid_getD (rs : List Ref) (n i : ℕ) (h : ∀ r ∈ rs, r.Valid n) :
    (rs.getD i .bot).Valid n := by
  by_cases hi : i < rs.length
  · rw [List.getD_eq_getElem rs Ref.bot hi]
    exact h _ (List.getElem_mem hi)
  · simp [List.getD_eq_default, Nat.le_of_not_lt hi, Ref.Valid]

lemma combine_valid (n : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref)
    (hr : ∀ r ∈ rs, r.Valid (n+gs.length)) :
    (combine n op gs rs).2.Valid (n+(combine n op gs rs).1.length) := by
  cases rs with
  | nil => dsimp [combine]; split <;> trivial
  | cons a rs =>
    cases rs with
    | nil => exact hr a (by simp)
    | cons b rs =>
      cases rs with
      | nil =>
        simp only [combine]
        have ha := hr a (by simp)
        have hb := hr b (by simp)
        split
        · exact meet_valid _ _ _ _ ha hb
        · exact join_valid _ _ _ _ ha hb
      | cons c rs => trivial

def State.Valid (P : ℕ) (s : State) : Prop := ∀ r ∈ s.refs, r.Valid (P+s.gates.length)

lemma combine_preserves_valid (P : ℕ) (op : GateOp) (gs : List Gate)
    (rs : List Ref) (r : Ref) (hr : r.Valid (P+gs.length)) :
    r.Valid (P+(combine P op gs rs).1.length) := by
  obtain ⟨hs,hh⟩ := combine_prefix P op gs rs
  apply r.valid_mono _ hr
  rw [hh, List.length_append]
  omega

lemma valid_copyStep (P : ℕ) (ds : List ℕ) (s : State) (jg : ℕ × Gate)
    (h : s.Valid P) : (copyStep P ds s jg).Valid P := by
  rcases jg with ⟨j,g⟩
  dsimp only [copyStep]
  split
  · intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact combine_preserves_valid _ _ _ _ _ (h r hr)
    · apply combine_valid
      intro r hr
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
      exact valid_getD _ _ _ h
  · intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact h _ hr
    · trivial

lemma valid_copyFold (P : ℕ) (ds : List ℕ) (ls : List (ℕ × Gate)) (s : State)
    (h : s.Valid P) : (ls.foldl (copyStep P ds) s).Valid P := by
  induction ls generalizing s with
  | nil => exact h
  | cons a ls ih => exact ih _ (valid_copyStep _ _ _ _ h)

lemma valid_copyPoints (P L : ℕ) (C : Circuit) : (copyPoints P L C).Valid P := by
  apply valid_copyFold
  intro r hr
  simp only [List.mem_append, List.mem_map, List.mem_replicate] at hr
  rcases hr with ⟨i,hi,rfl⟩ | ⟨_,rfl⟩
  · simpa [Ref.Valid] using List.mem_range.mp hi
  · trivial


lemma combine_correct (n : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref)
    (hop : op = .and ∨ op = .or) (hr : rs.length ≤ 2) (x : List Bool) (hx : x.length = n) :
    (combine n op gs rs).2.value (run (combine n op gs rs).1 x) =
      op.eval (rs.map (Ref.value (run gs x))) := by
  cases rs with
  | nil => rcases hop with rfl | rfl <;> rfl
  | cons a rs =>
    cases rs with
    | nil => rcases hop with rfl | rfl <;> simp [combine, GateOp.eval]
    | cons b rs =>
      cases rs with
      | nil =>
        rcases hop with rfl | rfl
        · simpa only [combine, ite_true, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true] using meet_correct n gs a b x hx
        · simpa only [combine, reduceCtorEq, ite_false, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false] using join_correct n gs a b x hx
      | cons c rs => simp at hr

lemma combine_preserves_value (P : ℕ) (op : GateOp) (gs : List Gate) (rs : List Ref)
    (r : Ref) (x : List Bool) (hx : x.length = P) (hr : r.Valid (P+gs.length)) :
    r.value (run (combine P op gs rs).1 x) = r.value (run gs x) := by
  obtain ⟨hs,hh⟩ := combine_prefix P op gs rs
  rw [hh, run_append]
  apply Ref.value_run
  simpa [run_length, hx] using hr


lemma map_values_preserved (P : ℕ) (op : GateOp) (s : State) (rs : List Ref)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P) :
    s.refs.map (Ref.value (run (combine P op s.gates rs).1 x)) =
      s.refs.map (Ref.value (run s.gates x)) := by
  apply List.map_congr_left
  intro r hr
  exact combine_preserves_value _ _ _ _ _ _ hx (hs r hr)

lemma getD_map_values (s : State) (x : List Bool) (i : ℕ) :
    (s.refs.getD i .bot).value (run s.gates x) =
      (s.refs.map (Ref.value (run s.gates x))).getD i false := by
  exact (List.getD_map (f := Ref.value (run s.gates x)) (d := Ref.bot)
    (l := s.refs) (n := i)).symm

lemma copyStep_values_zero (P : ℕ) (ds : List ℕ) (s : State) (j : ℕ) (g : Gate)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P)
    (hz : ds.getD j 0 = 0) (hop : g.op = .and ∨ g.op = .or)
    (hlen : g.inputs.length ≤ 2) :
    (copyStep P ds s (j,g)).refs.map (Ref.value (run (copyStep P ds s (j,g)).gates x)) =
      s.refs.map (Ref.value (run s.gates x)) ++
        [g.op.eval (g.inputs.map (fun i =>
          (s.refs.map (Ref.value (run s.gates x))).getD i false))] := by
  simp only [copyStep, hz, ite_true, List.map_append, List.map_cons, List.map_nil]
  rw [map_values_preserved _ _ _ _ x hx hs,
    combine_correct _ _ _ _ hop (by simpa using hlen) x hx]
  simp only [List.map_map]
  congr 2
  congr 1
  apply List.map_congr_left
  intro i _
  exact getD_map_values _ _ _

lemma copyStep_values_positive (P : ℕ) (ds : List ℕ) (s : State) (j : ℕ) (g : Gate)
    (x : List Bool) (hz : ds.getD j 0 ≠ 0) :
    (copyStep P ds s (j,g)).refs.map (Ref.value (run (copyStep P ds s (j,g)).gates x)) =
      s.refs.map (Ref.value (run s.gates x)) ++ [false] := by
  simp only [copyStep, hz, ite_false, List.map_append, List.map_cons, List.map_nil, Ref.value]


def maskedStep (ds : List ℕ) (vs : List Bool) (jg : ℕ × Gate) : List Bool :=
  vs ++ [if ds.getD jg.1 0 = 0 then
    jg.2.op.eval (jg.2.inputs.map (fun i => vs.getD i false)) else false]

lemma copyFold_values (P : ℕ) (ds : List ℕ) (s : State) (ls : List (ℕ × Gate))
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P)
    (hg : ∀ jg ∈ ls, (jg.2.op = .and ∨ jg.2.op = .or) ∧ jg.2.inputs.length ≤ 2) :
    (ls.foldl (copyStep P ds) s).refs.map
        (Ref.value (run (ls.foldl (copyStep P ds) s).gates x)) =
      ls.foldl (maskedStep ds) (s.refs.map (Ref.value (run s.gates x))) := by
  induction ls generalizing s with
  | nil => rfl
  | cons jg ls ih =>
    simp only [List.foldl_cons]
    rw [ih _ (valid_copyStep P ds s jg hs) (fun a ha => hg a (by simp [ha]))]
    rcases jg with ⟨j,g⟩
    obtain ⟨hop,hlen⟩ := hg (j,g) (by simp)
    by_cases hz : ds.getD j 0 = 0
    · rw [copyStep_values_zero _ _ _ _ _ _ hx hs hz hop hlen]
      simp only [maskedStep, hz, ite_true]
    · rw [copyStep_values_positive _ _ _ _ _ _ hz]
      simp only [maskedStep, hz, ite_false]

lemma copyPoints_values (P L : ℕ) (C : Circuit)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (x : List Bool) (hx : x.length = P) :
    (copyPoints P L C).refs.map (Ref.value (run (copyPoints P L C).gates x)) =
      (C.gates.zipIdx.map (fun (g,j) => (P+L+j,g))).foldl
        (maskedStep (C.lineDegrees (P+L) (Finset.Ico P (P+L))))
        (x ++ List.replicate L false) := by
  unfold copyPoints
  rw [copyFold_values P _ _ _ x hx]
  · congr 1
    simp only [run, List.foldl_nil, List.map_append, List.map_map, List.map_replicate, Ref.value]
    congr 1
    apply List.ext_getElem
    · simp [hx]
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
      exact List.getD_eq_getElem x false hj
  · intro r hr
    simp only [List.mem_append, List.mem_map, List.mem_replicate] at hr
    rcases hr with ⟨i,hi,rfl⟩ | ⟨_,rfl⟩
    · simpa [Ref.Valid] using List.mem_range.mp hi
    · trivial
  · intro jg hjg
    obtain ⟨⟨g,j⟩,hg,rfl⟩ := List.mem_map.mp hjg
    have hmem : g ∈ C.gates := by
      exact List.fst_mem_of_mem_zipIdx hg
    exact ⟨hm g hmem,hf g hmem⟩


-- `seen` records syntactic contributions even when their value is identically false.
def State.UnseenBot (s : State) (seen : Finset ℕ) : Prop :=
  ∀ i, i ∉ seen → s.refs.getD i .bot = .bot

lemma send_unseenBot (P : ℕ) (s : State) (seen : Finset ℕ) (i : ℕ) (r : Ref)
    (hs : s.UnseenBot seen) : (send P s i r).UnseenBot (insert i seen) := by
  intro j hj
  have hji : j ≠ i := by intro he; subst j; simp at hj
  have hjn : j ∉ seen := fun h => hj (Finset.mem_insert_of_mem h)
  dsimp only [send]
  simp only [List.getD]
  rw [List.getElem?_set_ne (Ne.symm hji)]
  exact hs j hjn

lemma send_cost_potential (P : ℕ) (s : State) (seen : Finset ℕ) (i : ℕ) (r : Ref)
    (hs : s.UnseenBot seen) :
    (send P s i r).gates.length + (insert i seen).card ≤
      s.gates.length + seen.card + 1 := by
  by_cases hi : i ∈ seen
  · rw [Finset.insert_eq_of_mem hi]
    have hc := send_cost P s i r
    omega
  · rw [send_cost_first P s i r (hs i hi), Finset.card_insert_of_notMem hi]
    omega

def sendList (P : ℕ) (s : State) (cs : List (ℕ × Ref)) : State :=
  cs.foldl (fun s ir => send P s ir.1 ir.2) s

lemma sendList_unseenBot (P : ℕ) (s : State) (seen : Finset ℕ) (cs : List (ℕ × Ref))
    (hs : s.UnseenBot seen) :
    (sendList P s cs).UnseenBot (seen ∪ (cs.map Prod.fst).toFinset) := by
  induction cs generalizing s seen with
  | nil => simpa [sendList] using hs
  | cons ir cs ih =>
    change (sendList P (send P s ir.1 ir.2) cs).UnseenBot _
    have hh := ih (send P s ir.1 ir.2) (insert ir.1 seen) (send_unseenBot P s seen ir.1 ir.2 hs)
    convert hh using 1
    ext j
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    tauto

lemma sendList_cost_potential (P : ℕ) (s : State) (seen : Finset ℕ) (cs : List (ℕ × Ref))
    (hs : s.UnseenBot seen) :
    (sendList P s cs).gates.length + (seen ∪ (cs.map Prod.fst).toFinset).card ≤
      s.gates.length + seen.card + cs.length := by
  induction cs generalizing s seen with
  | nil => simp [sendList]
  | cons ir cs ih =>
    change (sendList P (send P s ir.1 ir.2) cs).gates.length + _ ≤ _
    have hh := ih (send P s ir.1 ir.2) (insert ir.1 seen) (send_unseenBot P s seen ir.1 ir.2 hs)
    have hc := send_cost_potential P s seen ir.1 ir.2 hs
    have he : seen ∪ ((ir :: cs).map Prod.fst).toFinset = insert ir.1 seen ∪ (cs.map Prod.fst).toFinset := by
      ext j
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
      tauto
    rw [he]
    simp only [List.length_cons]
    omega


def AgreeZero (ds : List ℕ) (vs ws : List Bool) : Prop :=
  vs.length = ws.length ∧ ∀ i, ds.getD i 0 = 0 → vs.getD i false = ws.getD i false

lemma maskedStep_agrees (ds : List ℕ) (vs ws : List Bool) (j : ℕ) (g : Gate)
    (ha : AgreeZero ds vs ws) (hlen : vs.length = j)
    (hz : ds.getD j 0 = 0 → ∀ i ∈ g.inputs, i < j → ds.getD i 0 = 0) :
    AgreeZero ds (maskedStep ds vs (j,g))
      (ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) := by
  have hws : ws.length = j := ha.1.symm.trans hlen
  constructor
  · simp [maskedStep, ha.1]
  · intro i hi
    dsimp only [maskedStep]
    by_cases hij : i < j
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ha.2 i hi
    · by_cases hie : i = j
      · subst i
        rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero, ha.1.symm, hi, ite_true]
        congr 1
        apply List.map_congr_left
        intro k hk
        by_cases hkj : k < j
        · exact ha.2 k (hz hi k hk hkj)
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

lemma maskedFold_agrees (ds : List ℕ) (ls : List (ℕ × Gate)) (vs ws : List Bool)
    (ha : AgreeZero ds vs ws)
    (hindex : ∀ k (hk : k < ls.length), (ls[k]).1 = vs.length+k)
    (hz : ∀ jg ∈ ls, ds.getD jg.1 0 = 0 →
      ∀ i ∈ jg.2.inputs, i < jg.1 → ds.getD i 0 = 0) :
    AgreeZero ds (ls.foldl (maskedStep ds) vs)
      (ls.foldl (fun ws jg => ws ++ [jg.2.op.eval (jg.2.inputs.map (fun i => ws.getD i false))]) ws) := by
  induction ls generalizing vs ws with
  | nil => exact ha
  | cons jg ls ih =>
    have hj : jg.1 = vs.length := by
      have hh := hindex 0 (by simp)
      change jg.1 = vs.length + 0 at hh
      omega
    apply ih
    · exact maskedStep_agrees ds vs ws jg.1 jg.2 ha hj.symm (hz jg (by simp))
    · intro k hk
      have hh := hindex (k+1) (by simp; omega)
      simpa [maskedStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · exact fun a ha => hz a (by simp [ha])


lemma valid_send (P : ℕ) (s : State) (i : ℕ) (r : Ref)
    (hs : s.Valid P) (hr : r.Valid (P+s.gates.length)) : (send P s i r).Valid P := by
  intro a ha
  have hv := join_valid P s.gates (s.refs.getD i .bot) r (valid_getD _ _ _ hs) hr
  by_cases he : a = (join P s.gates (s.refs.getD i .bot) r).2
  · simpa only [he,send] using hv
  · have hb : a ∈ s.refs := by
      have hh := List.mem_or_eq_of_mem_set ha
      aesop
    obtain ⟨zs,hz⟩ := join_prefix P s.gates (s.refs.getD i .bot) r
    apply a.valid_mono _ (hs a hb)
    change P + s.gates.length ≤ P + (join P s.gates (s.refs.getD i .bot) r).1.length
    rw [hz,List.length_append]
    omega

lemma send_values (P : ℕ) (s : State) (i : ℕ) (r : Ref)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P) :
    (send P s i r).refs.map (Ref.value (run (send P s i r).gates x)) =
      (s.refs.map (Ref.value (run s.gates x))).set i
        ((s.refs.getD i .bot).value (run s.gates x) || r.value (run s.gates x)) := by
  dsimp only [send]
  rw [List.map_set]
  rw [join_correct P s.gates _ _ x hx]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact join_preserves P s.gates _ _ a x hx (hs a ha)

lemma send_value_at (P : ℕ) (s : State) (i : ℕ) (r : Ref)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P) (hi : i < s.refs.length) :
    ((send P s i r).refs.getD i .bot).value (run (send P s i r).gates x) =
      ((s.refs.getD i .bot).value (run s.gates x) || r.value (run s.gates x)) := by
  rw [getD_map_values,send_values P s i r x hx hs]
  simp [List.getD, hi]

lemma send_value_other (P : ℕ) (s : State) (i j : ℕ) (r : Ref)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P) (hji : j ≠ i) :
    ((send P s i r).refs.getD j .bot).value (run (send P s i r).gates x) =
      (s.refs.getD j .bot).value (run s.gates x) := by
  rw [getD_map_values,send_values P s i r x hx hs, getD_map_values]
  simp only [List.getD]
  rw [List.getElem?_set_ne (Ne.symm hji)]
  exact (getD_map_values s x j).symm


lemma valid_combine_state (P : ℕ) (s : State) (op : GateOp) (rs ctx : List Ref)
    (hs : s.Valid P) (hctx : ∀ r ∈ ctx, r.Valid (P+s.gates.length)) :
    (State.mk (combine P op s.gates rs).1 ctx).Valid P := by
  intro r hr
  exact combine_preserves_valid _ _ _ _ _ (hctx _ hr)

lemma valid_reverseStep (P : ℕ) (ds : List ℕ) (points : List Ref) (jg : ℕ × Gate)
    (s : State) (hs : s.Valid P)
    (hp : ∀ r ∈ points, r.Valid (P+s.gates.length)) :
    (reverseStep P ds points jg s).Valid P := by
  rcases jg with ⟨j,g⟩
  dsimp only [reverseStep]
  split
  · exact hs
  · split
    · have hc := valid_getD s.refs (P+s.gates.length) j hs
      generalize g.inputs.filter (fun i => decide (i < j ∧ 0 < ds.getD i 0)) = ys
      have hh : ∀ (ls : List ℕ) (z : State), z.Valid P →
          (s.refs.getD j .bot).Valid (P+z.gates.length) →
          (ls.foldl (fun z i => send P z i (s.refs.getD j .bot)) z).Valid P := by
        intro ls
        induction ls with
        | nil => intros; assumption
        | cons i ls ih =>
          intro z hz hc
          apply ih
          · exact valid_send _ _ _ _ hz hc
          · obtain ⟨zs,he⟩ := join_prefix P z.gates (z.refs.getD i .bot) (s.refs.getD j .bot)
            apply Ref.valid_mono _ _ hc
            change P+z.gates.length ≤ P+(join P z.gates (z.refs.getD i .bot) (s.refs.getD j .bot)).1.length
            rw [he,List.length_append]
            omega
      exact hh _ _ hs hc
    · split
      · apply valid_send
        · exact valid_combine_state _ _ _ _ _ hs hs
        · apply combine_valid
          intro r hr
          simp only [List.mem_cons, List.mem_map] at hr
          rcases hr with rfl | ⟨k,_,rfl⟩
          · exact valid_getD _ _ _ hs
          · split
            · exact valid_getD _ _ _ hp
            · trivial
      · exact hs


-- Weighted reverse propagation, with factors stored as shared point-side references.
def weightedSend (P : ℕ) (s : State) (i : ℕ) (c w : Ref) : State :=
  let z := meet P s.gates c w
  send P ⟨z.1,s.refs⟩ i z.2

lemma weightedSend_valid (P : ℕ) (s : State) (i : ℕ) (c w : Ref)
    (hs : s.Valid P) (hc : c.Valid (P+s.gates.length)) (hw : w.Valid (P+s.gates.length)) :
    (weightedSend P s i c w).Valid P := by
  apply valid_send
  · intro r hr
    obtain ⟨zs,hz⟩ := meet_prefix P s.gates c w
    apply r.valid_mono _ (hs r hr)
    rw [hz,List.length_append]
    omega
  · exact meet_valid _ _ _ _ hc hw

lemma weightedSend_values (P : ℕ) (s : State) (i : ℕ) (c w : Ref)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P) :
    (weightedSend P s i c w).refs.map (Ref.value (run (weightedSend P s i c w).gates x)) =
      (s.refs.map (Ref.value (run s.gates x))).set i
        ((s.refs.getD i .bot).value (run s.gates x) ||
          (c.value (run s.gates x) && w.value (run s.gates x))) := by
  unfold weightedSend
  have hh : (State.mk (meet P s.gates c w).1 s.refs).Valid P := by
    intro r hr
    obtain ⟨zs,hz⟩ := meet_prefix P s.gates c w
    apply r.valid_mono _ (hs r hr)
    rw [hz,List.length_append]
    omega
  rw [send_values P _ _ _ x hx hh]
  have he : s.refs.map (Ref.value (run (meet P s.gates c w).1 x)) =
      s.refs.map (Ref.value (run s.gates x)) := by
    apply List.map_congr_left
    exact fun r hr => meet_preserves P s.gates c w r x hx (hs r hr)
  simp only [State.refs, State.gates]
  rw [he,meet_correct P s.gates c w x hx,
    meet_preserves P s.gates c w (s.refs.getD i .bot) x hx (valid_getD _ _ _ hs)]

lemma weightedSend_prefix (P : ℕ) (s : State) (i : ℕ) (c w : Ref) :
    ∃ zs, (weightedSend P s i c w).gates = s.gates ++ zs := by
  obtain ⟨as,ha⟩ := meet_prefix P s.gates c w
  obtain ⟨bs,hb⟩ := join_prefix P (meet P s.gates c w).1
    (s.refs.getD i .bot) (meet P s.gates c w).2
  exact ⟨as++bs, by simpa only [weightedSend,send,ha,List.append_assoc] using hb⟩


lemma meet_cost_weight (P : ℕ) (gs : List Gate) (c w : Ref) :
    (meet P gs c w).1.length ≤ gs.length + if w = .top then 0 else 1 := by
  cases c <;> cases w <;> simp [meet]

lemma weightedSend_unseenBot (P : ℕ) (s : State) (seen : Finset ℕ) (i : ℕ) (c w : Ref)
    (hs : s.UnseenBot seen) : (weightedSend P s i c w).UnseenBot (insert i seen) := by
  apply send_unseenBot
  exact hs

lemma weightedSend_cost_potential (P : ℕ) (s : State) (seen : Finset ℕ) (i : ℕ) (c w : Ref)
    (hs : s.UnseenBot seen) :
    (weightedSend P s i c w).gates.length + (insert i seen).card ≤
      s.gates.length + seen.card + 1 + if w = .top then 0 else 1 := by
  have hm := meet_cost_weight P s.gates c w
  have hh := send_cost_potential P (State.mk (meet P s.gates c w).1 s.refs) seen i
    (meet P s.gates c w).2 hs
  dsimp only [weightedSend]
  dsimp only [State.gates] at hh
  omega

def weightedSendList (P : ℕ) (s : State) (c : Ref) (es : List (ℕ × Ref)) : State :=
  es.foldl (fun z e => weightedSend P z e.1 c e.2) s

lemma weightedSendList_cost_potential (P : ℕ) (s : State) (seen : Finset ℕ)
    (c : Ref) (es : List (ℕ × Ref)) (hs : s.UnseenBot seen) :
    (weightedSendList P s c es).gates.length + (seen ∪ (es.map Prod.fst).toFinset).card ≤
      s.gates.length + seen.card + es.length + (es.filter (fun e => e.2 ≠ .top)).length := by
  induction es generalizing s seen with
  | nil => simp [weightedSendList]
  | cons e es ih =>
    change (weightedSendList P (weightedSend P s e.1 c e.2) c es).gates.length + _ ≤ _
    have hh := ih (weightedSend P s e.1 c e.2) (insert e.1 seen)
      (weightedSend_unseenBot P s seen e.1 c e.2 hs)
    have hc := weightedSend_cost_potential P s seen e.1 c e.2 hs
    have he : seen ∪ ((e :: es).map Prod.fst).toFinset = insert e.1 seen ∪ (es.map Prod.fst).toFinset := by
      ext j
      simp only [List.map_cons,List.toFinset_cons,Finset.mem_union,Finset.mem_insert]
      tauto
    rw [he]
    by_cases ht : e.2 = .top
    · simp only [List.length_cons,List.filter_cons,ht,ne_eq,not_true_eq_false,decide_false,
        Bool.false_eq_true,ite_false,ite_true] at *
      omega
    · simp only [List.length_cons,List.filter_cons,ht,ne_eq,not_false_eq_true,decide_true,
        ite_true,ite_false,Bool.true_eq] at *
      omega


lemma weightedSendList_unseenBot (P : ℕ) (s : State) (seen : Finset ℕ)
    (c : Ref) (es : List (ℕ × Ref)) (hs : s.UnseenBot seen) :
    (weightedSendList P s c es).UnseenBot (seen ∪ (es.map Prod.fst).toFinset) := by
  induction es generalizing s seen with
  | nil => simpa [weightedSendList] using hs
  | cons e es ih =>
    change (weightedSendList P (weightedSend P s e.1 c e.2) c es).UnseenBot _
    have hh := ih (weightedSend P s e.1 c e.2) (insert e.1 seen)
      (weightedSend_unseenBot P s seen e.1 c e.2 hs)
    convert hh using 1
    ext j
    simp only [List.map_cons,List.toFinset_cons,Finset.mem_union,Finset.mem_insert]
    tauto

def weightedSweep (P : ℕ) : List (ℕ × List (ℕ × Ref)) → State → State
  | [], s => s
  | (j,es) :: gs, s =>
    let z := weightedSweep P gs s
    weightedSendList P z (z.refs.getD j .bot) es

def receivers (gs : List (ℕ × List (ℕ × Ref))) : Finset ℕ :=
  (gs.flatMap (fun g => g.2.map Prod.fst)).toFinset

def edgeCost (gs : List (ℕ × List (ℕ × Ref))) : ℕ :=
  (gs.map (fun g => g.2.length)).sum +
    (gs.map (fun g => (g.2.filter (fun e => e.2 ≠ .top)).length)).sum

lemma receivers_cons (j : ℕ) (es : List (ℕ × Ref)) (gs : List (ℕ × List (ℕ × Ref))) :
    receivers ((j,es)::gs) = (es.map Prod.fst).toFinset ∪ receivers gs := by
  simp [receivers]

lemma weightedSweep_unseenBot (P : ℕ) (gs : List (ℕ × List (ℕ × Ref)))
    (s : State) (seen : Finset ℕ) (hs : s.UnseenBot seen) :
    (weightedSweep P gs s).UnseenBot (seen ∪ receivers gs) := by
  induction gs with
  | nil => simpa [weightedSweep,receivers] using hs
  | cons g gs ih =>
    rcases g with ⟨j,es⟩
    have hh := weightedSendList_unseenBot P (weightedSweep P gs s) (seen ∪ receivers gs)
      ((weightedSweep P gs s).refs.getD j .bot) es ih
    change (weightedSendList P (weightedSweep P gs s)
      ((weightedSweep P gs s).refs.getD j .bot) es).UnseenBot _
    have he : seen ∪ receivers ((j,es)::gs) =
        (seen ∪ receivers gs) ∪ (es.map Prod.fst).toFinset := by
      rw [receivers_cons]
      ext i
      simp only [Finset.mem_union]
      tauto
    rw [he]
    exact hh
    /-
    simp only [Finset.mem_union]
    tauto -/

lemma weightedSweep_cost (P : ℕ) (gs : List (ℕ × List (ℕ × Ref)))
    (s : State) (seen : Finset ℕ) (hs : s.UnseenBot seen) :
    (weightedSweep P gs s).gates.length + (seen ∪ receivers gs).card ≤
      s.gates.length + seen.card + edgeCost gs := by
  induction gs with
  | nil => simp [weightedSweep,receivers,edgeCost]
  | cons g gs ih =>
    have hb := weightedSweep_unseenBot P gs s seen hs
    have hh := weightedSendList_cost_potential P (weightedSweep P gs s) (seen ∪ receivers gs)
      ((weightedSweep P gs s).refs.getD g.1 .bot) g.2 hb
    have he : seen ∪ receivers (g::gs) = (seen ∪ receivers gs) ∪ (g.2.map Prod.fst).toFinset := by
      simp only [receivers,List.flatMap_cons,List.toFinset_append]
      ext i
      simp only [Finset.mem_union]
      tauto
    change (weightedSendList P (weightedSweep P gs s)
      ((weightedSweep P gs s).refs.getD g.1 .bot) g.2).gates.length + _ ≤ _
    rw [he]
    have hc : edgeCost (g::gs) = edgeCost gs + g.2.length +
        (g.2.filter (fun e => e.2 ≠ .top)).length := by simp [edgeCost]; omega
    rw [hc]
    omega


lemma weightedSendList_prefix (P : ℕ) (es : List (ℕ × Ref)) (s : State) (c : Ref) :
    ∃ zs, (weightedSendList P s c es).gates = s.gates ++ zs := by
  induction es generalizing s with
  | nil => exact ⟨[],by simp [weightedSendList]⟩
  | cons e es ih =>
    obtain ⟨as,ha⟩ := weightedSend_prefix P s e.1 c e.2
    obtain ⟨bs,hb⟩ := ih (weightedSend P s e.1 c e.2)
    exact ⟨as++bs,by simpa [weightedSendList,ha,List.append_assoc] using hb⟩

lemma weightedSend_preserves_valid (P : ℕ) (s : State) (i : ℕ) (c w r : Ref)
    (hr : r.Valid (P+s.gates.length)) : r.Valid (P+(weightedSend P s i c w).gates.length) := by
  obtain ⟨zs,hz⟩ := weightedSend_prefix P s i c w
  apply r.valid_mono _ hr
  rw [hz,List.length_append]
  omega

lemma weightedSendList_valid (P : ℕ) (es : List (ℕ × Ref)) (s : State) (c : Ref)
    (hs : s.Valid P) (hc : c.Valid (P+s.gates.length))
    (he : ∀ e ∈ es, e.2.Valid (P+s.gates.length)) :
    (weightedSendList P s c es).Valid P := by
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih =>
    apply ih
    · exact weightedSend_valid P s e.1 c e.2 hs hc (he e (by simp))
    · exact weightedSend_preserves_valid _ _ _ _ _ _ hc
    · intro a ha
      exact weightedSend_preserves_valid _ _ _ _ _ _ (he a (by simp [ha]))

lemma weightedSend_preserves_value (P : ℕ) (s : State) (i : ℕ) (c w r : Ref)
    (x : List Bool) (hx : x.length = P) (hr : r.Valid (P+s.gates.length)) :
    r.value (run (weightedSend P s i c w).gates x) = r.value (run s.gates x) := by
  obtain ⟨zs,hz⟩ := weightedSend_prefix P s i c w
  rw [hz,run_append]
  apply Ref.value_run
  simpa [run_length,hx] using hr

lemma weightedSweep_prefix (P : ℕ) (gs : List (ℕ × List (ℕ × Ref))) (s : State) :
    ∃ zs, (weightedSweep P gs s).gates = s.gates ++ zs := by
  induction gs with
  | nil => exact ⟨[],by simp [weightedSweep]⟩
  | cons g gs ih =>
    obtain ⟨as,ha⟩ := ih
    obtain ⟨bs,hb⟩ := weightedSendList_prefix P g.2 (weightedSweep P gs s)
      ((weightedSweep P gs s).refs.getD g.1 .bot)
    exact ⟨as++bs, by simpa [weightedSweep,ha,List.append_assoc] using hb⟩

lemma weightedSweep_valid (P : ℕ) (gs : List (ℕ × List (ℕ × Ref))) (s : State)
    (hs : s.Valid P) (hw : ∀ g ∈ gs, ∀ e ∈ g.2, e.2.Valid (P+s.gates.length)) :
    (weightedSweep P gs s).Valid P := by
  induction gs with
  | nil => exact hs
  | cons g gs ih =>
    have hz := ih (fun a ha => hw a (by simp [ha]))
    apply weightedSendList_valid
    · exact hz
    · exact valid_getD _ _ _ hz
    · intro e he
      obtain ⟨zs,heq⟩ := weightedSweep_prefix P gs s
      apply Ref.valid_mono _ _ (hw g (by simp) e he)
      rw [heq,List.length_append]
      omega

end Transposition738.Builder

namespace Transposition738.ReverseCut

def active (n : ℕ) (ctx val : ℕ → Bool) : Bool :=
  decide (∃ i, i < n ∧ ctx i = true ∧ val i = true)

def put (ctx : ℕ → Bool) (i : ℕ) (r : Bool) : ℕ → Bool :=
  fun j => if j = i then ctx j || r else ctx j

lemma active_succ (n : ℕ) (ctx val : ℕ → Bool) :
    active (n+1) ctx val = (active n ctx val || (ctx n && val n)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [active, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i,hi,hc,hv⟩
    by_cases h : i < n
    · exact Or.inl ⟨i,h,hc,hv⟩
    · have : i = n := by omega
      subst i
      exact Or.inr ⟨hc,hv⟩
  · rintro (⟨i,hi,hc,hv⟩ | ⟨hc,hv⟩)
    · exact ⟨i,by omega,hc,hv⟩
    · exact ⟨n,by omega,hc,hv⟩

lemma active_put (n : ℕ) (ctx val : ℕ → Bool) (i : ℕ) (r : Bool) (hi : i < n) :
    active n (put ctx i r) val = (active n ctx val || (r && val i)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [active, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨j,hj,hc,hv⟩
    by_cases hji : j = i
    · subst j
      simp only [put, ite_true, Bool.or_eq_true] at hc
      rcases hc with hc | hr
      · exact Or.inl ⟨i,hi,hc,hv⟩
      · exact Or.inr ⟨hr,hv⟩
    · simp only [put,hji,ite_false] at hc
      exact Or.inl ⟨j,hj,hc,hv⟩
  · rintro (⟨j,hj,hc,hv⟩ | ⟨hr,hv⟩)
    · refine ⟨j,hj,?_,hv⟩
      by_cases hji : j = i
      · subst j; simp [put,hc]
      · simp [put,hji,hc]
    · exact ⟨i,hi,by simp [put,hr],hv⟩

lemma eliminate_or (n : ℕ) (ctx val : ℕ → Bool) (i j : ℕ)
    (hi : i < n) (hj : j < n) (hv : val n = (val i || val j)) :
    active (n+1) ctx val = active n (put (put ctx i (ctx n)) j (ctx n)) val := by
  rw [active_succ,active_put n _ _ j _ hj, active_put n _ _ i _ hi,hv]
  cases active n ctx val <;> cases ctx n <;> cases val i <;> cases val j <;> rfl

lemma eliminate_and (n : ℕ) (ctx val : ℕ → Bool) (i : ℕ) (factor : Bool)
    (hi : i < n) (hv : val n = (val i && factor)) :
    active (n+1) ctx val = active n (put ctx i (ctx n && factor)) val := by
  rw [active_succ,active_put n _ _ i _ hi,hv]
  cases active n ctx val <;> cases ctx n <;> cases val i <;> cases factor <;> rfl

lemma eliminate_alias (n : ℕ) (ctx val : ℕ → Bool) (i : ℕ)
    (hi : i < n) (hv : val n = val i) :
    active (n+1) ctx val = active n (put ctx i (ctx n)) val := by
  rw [active_succ,active_put n _ _ i _ hi,hv]

lemma eliminate_false (n : ℕ) (ctx val : ℕ → Bool) (hv : val n = false) :
    active (n+1) ctx val = active n ctx val := by
  simp [active_succ,hv]


def weighted (es : List (ℕ × Bool)) (val : ℕ → Bool) : Bool :=
  es.foldr (fun e a => (val e.1 && e.2) || a) false

def propagate (es : List (ℕ × Bool)) (c : Bool) (ctx : ℕ → Bool) : ℕ → Bool :=
  es.foldl (fun z e => put z e.1 (c && e.2)) ctx

lemma propagate_active (n : ℕ) (es : List (ℕ × Bool)) (c : Bool) (ctx val : ℕ → Bool)
    (he : ∀ e ∈ es, e.1 < n) :
    active n (propagate es c ctx) val = (active n ctx val || (c && weighted es val)) := by
  induction es generalizing ctx with
  | nil => simp [propagate,weighted]
  | cons e es ih =>
    change active n (propagate es c (put ctx e.1 (c && e.2))) val = _
    rw [ih _ (fun a ha => he a (by simp [ha])), active_put n ctx val e.1 _ (he e (by simp))]
    simp only [weighted,List.foldr_cons]
    cases active n ctx val <;> cases c <;> cases val e.1 <;> cases e.2 <;> cases weighted es val <;> rfl

lemma eliminate_weighted (n : ℕ) (es : List (ℕ × Bool)) (ctx val : ℕ → Bool)
    (he : ∀ e ∈ es, e.1 < n) (hv : val n = weighted es val) :
    active (n+1) ctx val = active n (propagate es (ctx n) ctx) val := by
  rw [active_succ,propagate_active n es _ _ _ he,hv]

lemma propagate_other (es : List (ℕ × Bool)) (c : Bool) (ctx : ℕ → Bool) (i : ℕ)
    (hi : ∀ e ∈ es, e.1 ≠ i) : propagate es c ctx i = ctx i := by
  induction es generalizing ctx with
  | nil => rfl
  | cons e es ih =>
    change propagate es c (put ctx e.1 (c && e.2)) i = _
    rw [ih _ (fun a ha => hi a (by simp [ha]))]
    simp only [put,Ne.symm (hi e (by simp)),ite_false]

-- Eliminate gates numbered n through n+gs.length-1 in reverse order.
def sweep (n : ℕ) : List (List (ℕ × Bool)) → (ℕ → Bool) → (ℕ → Bool)
  | [], ctx => ctx
  | es :: gs, ctx =>
    let z := sweep (n+1) gs ctx
    propagate es (z n) z

lemma sweep_active (n : ℕ) (gs : List (List (ℕ × Bool))) (ctx val : ℕ → Bool)
    (hvalid : ∀ k (hk : k < gs.length), ∀ e ∈ gs[k], e.1 < n+k)
    (hval : ∀ k (hk : k < gs.length), val (n+k) = weighted gs[k] val) :
    active (n+gs.length) ctx val = active n (sweep n gs ctx) val := by
  induction gs generalizing n with
  | nil => simp [sweep]
  | cons es gs ih =>
    have hv : ∀ k (hk : k < gs.length), ∀ e ∈ gs[k], e.1 < (n+1)+k := by
      intro k hk e he
      have hh := hvalid (k+1) (by simp; omega) e he
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have he : ∀ k (hk : k < gs.length), val ((n+1)+k) = weighted gs[k] val := by
      intro k hk
      have hh := hval (k+1) (by simp; omega)
      change val (n+(k+1)) = weighted gs[k] val at hh
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have hi := ih (n+1) hv he
    have hn : n+(es::gs).length = (n+1)+gs.length := by simp; omega
    rw [hn,hi]
    change active (n+1) (sweep (n+1) gs ctx) val = _
    apply eliminate_weighted
    · intro e he
      have hh := hvalid 0 (by simp) e he
      simpa using hh
    · have hh := hval 0 (by simp)
      simpa using hh


def rootContext (out : ℕ) : ℕ → Bool := fun i => decide (i = out)

lemma active_root (n out : ℕ) (val : ℕ → Bool) (ho : out < n) :
    active n (rootContext out) val = val out := by
  apply Bool.eq_iff_iff.mpr
  simp only [active,rootContext,decide_eq_true_eq]
  constructor
  · rintro ⟨i,_,rfl,hv⟩
    exact hv
  · intro hv
    exact ⟨out,ho,rfl,hv⟩

lemma transposition (n : ℕ) (gs : List (List (ℕ × Bool))) (val : ℕ → Bool) (out : ℕ)
    (ho : out < n+gs.length)
    (hvalid : ∀ k (hk : k < gs.length), ∀ e ∈ gs[k], e.1 < n+k)
    (hval : ∀ k (hk : k < gs.length), val (n+k) = weighted gs[k] val) :
    val out = active n (sweep n gs (rootContext out)) val := by
  rw [← active_root (n+gs.length) out val ho]
  exact sweep_active n gs _ val hvalid hval

lemma sweep_eq_of_weights (n : ℕ) (gs : List (List (ℕ × Bool))) (ctx ctx' : ℕ → Bool)
    (h : ctx = ctx') : sweep n gs ctx = sweep n gs ctx' := by rw [h]

end Transposition738.ReverseCut

namespace Transposition738.Builder
open PEqualNP.CircuitLowerBounds

def ctxValue (s : State) (x : List Bool) : ℕ → Bool :=
  fun i => (s.refs.getD i .bot).value (run s.gates x)

lemma weightedSend_ctxValue (P : ℕ) (s : State) (i : ℕ) (c w : Ref)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P) (hi : i < s.refs.length) :
    ctxValue (weightedSend P s i c w) x =
      ReverseCut.put (ctxValue s x) i (c.value (run s.gates x) && w.value (run s.gates x)) := by
  funext j
  unfold ctxValue
  rw [getD_map_values,weightedSend_values P s i c w x hx hs]
  by_cases hji : j = i
  · subst j
    simp [List.getD,hi,ReverseCut.put]
  · simp only [List.getD]
    rw [List.getElem?_set_ne (Ne.symm hji)]
    exact (getD_map_values s x j).symm.trans (by simp [ReverseCut.put,hji])

lemma weightedSend_refs_length (P : ℕ) (s : State) (i : ℕ) (c w : Ref) :
    (weightedSend P s i c w).refs.length = s.refs.length := by simp [weightedSend,send]

lemma weightedSendList_refs_length (P : ℕ) (s : State) (c : Ref) (es : List (ℕ × Ref)) :
    (weightedSendList P s c es).refs.length = s.refs.length := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact (ih _).trans (weightedSend_refs_length _ _ _ _ _)

lemma weightedSendList_ctxValue (P : ℕ) (s : State) (c : Ref) (es : List (ℕ × Ref))
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P) (hc : c.Valid (P+s.gates.length))
    (hw : ∀ e ∈ es, e.2.Valid (P+s.gates.length))
    (hi : ∀ e ∈ es, e.1 < s.refs.length) :
    ctxValue (weightedSendList P s c es) x =
      ReverseCut.propagate (es.map (fun e => (e.1,e.2.value (run s.gates x))))
        (c.value (run s.gates x)) (ctxValue s x) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    change ctxValue (weightedSendList P (weightedSend P s e.1 c e.2) c es) x = _
    rw [ih]
    · rw [weightedSend_ctxValue P s e.1 c e.2 x hx hs (hi e (by simp))]
      have he : es.map (fun a => (a.1,a.2.value (run (weightedSend P s e.1 c e.2).gates x))) =
          es.map (fun a => (a.1,a.2.value (run s.gates x))) := by
        apply List.map_congr_left
        intro a ha
        rw [weightedSend_preserves_value P s e.1 c e.2 a.2 x hx (hw a (by simp [ha]))]
      rw [he,weightedSend_preserves_value P s e.1 c e.2 c x hx hc]
      rfl
    · exact weightedSend_valid _ _ _ _ _ hs hc (hw e (by simp))
    · exact weightedSend_preserves_valid _ _ _ _ _ _ hc
    · intro a ha
      exact weightedSend_preserves_valid _ _ _ _ _ _ (hw a (by simp [ha]))
    · intro a ha
      rw [weightedSend_refs_length]
      exact hi a (by simp [ha])


lemma weightedSweep_refs_length (P : ℕ) (s : State) (gs : List (ℕ × List (ℕ × Ref))) :
    (weightedSweep P gs s).refs.length = s.refs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => exact (weightedSendList_refs_length _ _ _ _).trans ih

lemma weightedSweep_preserves_value (P : ℕ) (gs : List (ℕ × List (ℕ × Ref))) (s : State)
    (r : Ref) (x : List Bool) (hx : x.length = P) (hr : r.Valid (P+s.gates.length)) :
    r.value (run (weightedSweep P gs s).gates x) = r.value (run s.gates x) := by
  obtain ⟨zs,hz⟩ := weightedSweep_prefix P gs s
  rw [hz,run_append]
  apply Ref.value_run
  simpa [run_length,hx] using hr

-- General realization theorem for a weighted reverse DAG.
def realizeEdges (s : State) (x : List Bool) (es : List (ℕ × Ref)) : List (ℕ × Bool) :=
  es.map (fun e => (e.1,e.2.value (run s.gates x)))

def semanticSweep : List (ℕ × List (ℕ × Bool)) → (ℕ → Bool) → (ℕ → Bool)
  | [], ctx => ctx
  | (j,es)::gs, ctx =>
    let z := semanticSweep gs ctx
    ReverseCut.propagate es (z j) z

lemma weightedSweep_ctxValue (P : ℕ) (gs : List (ℕ × List (ℕ × Ref))) (s : State)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P)
    (hw : ∀ g ∈ gs, ∀ e ∈ g.2, e.2.Valid (P+s.gates.length))
    (hi : ∀ g ∈ gs, ∀ e ∈ g.2, e.1 < s.refs.length) :
    ctxValue (weightedSweep P gs s) x =
      semanticSweep (gs.map (fun g => (g.1,realizeEdges s x g.2))) (ctxValue s x) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨j,es⟩
    have hz := weightedSweep_valid P gs s hs (fun a ha => hw a (by simp [ha]))
    change ctxValue (weightedSendList P (weightedSweep P gs s)
      ((weightedSweep P gs s).refs.getD j .bot) es) x = _
    rw [weightedSendList_ctxValue P _ _ _ x hx hz (valid_getD _ _ _ hz)]
    · have he : realizeEdges (weightedSweep P gs s) x es = realizeEdges s x es := by
        apply List.map_congr_left
        intro a ha
        rw [weightedSweep_preserves_value P gs s a.2 x hx (hw (j,es) (by simp) a ha)]
      change ReverseCut.propagate (realizeEdges (weightedSweep P gs s) x es)
        (ctxValue (weightedSweep P gs s) x j) (ctxValue (weightedSweep P gs s) x) = _
      rw [he,ih (fun a ha => hw a (by simp [ha])) (fun a ha => hi a (by simp [ha]))]
      rfl
    · intro e he
      obtain ⟨zs,heq⟩ := weightedSweep_prefix P gs s
      apply Ref.valid_mono _ _ (hw (j,es) (by simp) e he)
      rw [heq,List.length_append]
      omega
    · intro e he
      rw [weightedSweep_refs_length]
      exact hi (j,es) (by simp) e he


lemma semanticSweep_indexed (n : ℕ) (gs : List (List (ℕ × Bool))) (ctx : ℕ → Bool) :
    semanticSweep (gs.zipIdx n |>.map (fun (es,j) => (j,es))) ctx =
      ReverseCut.sweep n gs ctx := by
  induction gs generalizing n with
  | nil => rfl
  | cons es gs ih =>
    simp only [List.zipIdx_cons,List.map_cons,semanticSweep,ReverseCut.sweep]
    rw [ih]

lemma weighted_transposition (P n : ℕ) (gs : List (List (ℕ × Ref))) (s : State)
    (x : List Bool) (hx : x.length = P) (hs : s.Valid P)
    (hw : ∀ es ∈ gs, ∀ e ∈ es, e.2.Valid (P+s.gates.length))
    (hi : ∀ k (hk : k < gs.length), ∀ e ∈ gs[k], e.1 < n+k)
    (hl : n+gs.length ≤ s.refs.length)
    (val : ℕ → Bool) (out : ℕ) (ho : out < n+gs.length)
    (hctx : ctxValue s x = ReverseCut.rootContext out)
    (hval : ∀ k (hk : k < gs.length),
      val (n+k) = ReverseCut.weighted (realizeEdges s x gs[k]) val) :
    val out = ReverseCut.active n
      (ctxValue (weightedSweep P (gs.zipIdx n |>.map (fun (es,j) => (j,es))) s) x) val := by
  rw [weightedSweep_ctxValue P _ s x hx hs]
  · have he : (List.map (fun (g : ℕ × List (ℕ × Ref)) => (g.1,realizeEdges s x g.2))
        (List.map (fun (es,j) => (j,es)) (gs.zipIdx n))) =
        ((gs.map (realizeEdges s x)).zipIdx n |>.map (fun (es,j) => (j,es))) := by
      simp only [List.map_map,List.zipIdx_map]
      rfl
    rw [he,semanticSweep_indexed,hctx]
    apply ReverseCut.transposition n (gs.map (realizeEdges s x)) val out
    · simpa using ho
    · intro k hk e he
      simp only [List.getElem_map] at he
      obtain ⟨e,hee,rfl⟩ := List.mem_map.mp he
      exact hi k (by simpa using hk) e hee
    · intro k hk
      simpa using hval k (by simpa using hk)
  · intro g hg
    obtain ⟨⟨es,j⟩,he,rfl⟩ := List.mem_map.mp hg
    exact hw es (List.fst_mem_of_mem_zipIdx he)
  · intro g hg e he
    obtain ⟨⟨es,j⟩,hj,rfl⟩ := List.mem_map.mp hg
    have hm := List.fst_eq_of_mem_zipIdx hj
    have hjl := List.snd_lt_of_mem_zipIdx hj
    have hjn := List.le_snd_of_mem_zipIdx hj
    have hb : e.1 < n+(j-n) := by
      apply hi (j-n) (by omega)
      simpa only [← hm] using he
    omega


lemma weightedSend_good (P : ℕ) (s : State) (i : ℕ) (c w : Ref) (hs : s.Good) :
    (weightedSend P s i c w).Good := by
  apply good_send
  exact ⟨meet_monotone _ _ _ _ hs.1,meet_fanin _ _ _ _ hs.2⟩

lemma weightedSendList_good (P : ℕ) (s : State) (c : Ref) (es : List (ℕ × Ref))
    (hs : s.Good) : (weightedSendList P s c es).Good := by
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih => exact ih _ (weightedSend_good _ _ _ _ _ hs)

lemma weightedSweep_good (P : ℕ) (s : State) (gs : List (ℕ × List (ℕ × Ref)))
    (hs : s.Good) : (weightedSweep P gs s).Good := by
  induction gs with
  | nil => exact hs
  | cons g gs ih => exact weightedSendList_good _ _ _ _ ih

def startContexts (gs : List Gate) (m out : ℕ) : State :=
  ⟨gs,(List.replicate m Ref.bot).set out .top⟩

lemma startContexts_valid (P : ℕ) (gs : List Gate) (m out : ℕ) :
    (startContexts gs m out).Valid P := by
  intro r hr
  have hh := List.mem_or_eq_of_mem_set hr
  rcases hh with h | rfl
  · have he := List.mem_replicate.mp h
    rcases he with ⟨_,rfl⟩
    trivial
  · trivial

lemma startContexts_unseenBot (gs : List Gate) (m out : ℕ) :
    (startContexts gs m out).UnseenBot {out} := by
  intro i hi
  have hio : i ≠ out := by simpa using hi
  change ((List.replicate m Ref.bot).set out .top).getD i .bot = .bot
  simp only [List.getD]
  rw [List.getElem?_set_ne (Ne.symm hio)]
  by_cases him : i < m <;> simp [him]

lemma startContexts_ctxValue (P : ℕ) (gs : List Gate) (m out : ℕ) (x : List Bool)
    (ho : out < m) : ctxValue (startContexts gs m out) x = ReverseCut.rootContext out := by
  funext i
  unfold ctxValue startContexts ReverseCut.rootContext
  by_cases hio : i = out
  · subst i
    simp [List.getD,ho,Ref.value]
  · simp only [List.getD]
    rw [List.getElem?_set_ne (Ne.symm hio)]
    by_cases him : i < m <;> simp [him,hio,Ref.value]

lemma weighted_total_bound (P : ℕ) (gs : List (ℕ × List (ℕ × Ref)))
    (pointGates : List Gate) (m out original lines pointCount yCount : ℕ)
    (hcopy : pointGates.length ≤ pointCount)
    (htotal : pointCount+yCount = original)
    (hcost : edgeCost gs ≤ 2*yCount)
    (hvertices : yCount+lines ≤ ({out} ∪ receivers gs).card) :
    (weightedSweep P gs (startContexts pointGates m out)).gates.length + lines ≤ original+1 := by
  have hh := weightedSweep_cost P gs (startContexts pointGates m out) {out}
    (startContexts_unseenBot pointGates m out)
  change (weightedSweep P gs (startContexts pointGates m out)).gates.length +
    ({out} ∪ receivers gs).card ≤ pointGates.length + 1 + edgeCost gs at hh
  omega

end Transposition738.Builder

-- Independent alternative checked locally on 2026-11-23.
-- L-meta-738 was already settled upstream by PR 1137.
-- This file is not an upstream submission and carries no project credit.
-- Focused imports match the local Lean 4.36.0 verification environment.
namespace Transposition738
open PEqualNP.CircuitLowerBounds

inductive Formula (P L : Type) where
  | point : P → Formula P L
  | line : L → Formula P L
  | bot : Formula P L
  | top : Formula P L
  | meet : Formula P L → Formula P L → Formula P L
  | join : Formula P L → Formula P L → Formula P L

def Formula.degree {P L : Type} : Formula P L → ℕ
  | .point _ => 0
  | .line _ => 1
  | .bot => 0
  | .top => 0
  | .meet a b => a.degree + b.degree
  | .join a b => max a.degree b.degree

def Formula.eval {P L : Type} (x : P → Bool) (y : L → Bool) : Formula P L → Bool
  | .point p => x p
  | .line l => y l
  | .bot => false
  | .top => true
  | .meet a b => a.eval x y && b.eval x y
  | .join a b => a.eval x y || b.eval x y

lemma Formula.eval_degree_zero {P L : Type} (f : Formula P L) (h : f.degree = 0)
    (x : P → Bool) (y z : L → Bool) : f.eval x y = f.eval x z := by
  induction f with
  | point p => rfl
  | line l => simp [degree] at h
  | bot => rfl
  | top => rfl
  | meet a b iha ihb =>
    have ha : a.degree = 0 := by simp [degree] at h; omega
    have hb : b.degree = 0 := by simp [degree] at h; omega
    simp only [eval, iha ha, ihb hb]
  | join a b iha ihb =>
    have ha : a.degree = 0 := by simp [degree] at h; omega
    have hb : b.degree = 0 := by simp [degree] at h; omega
    simp only [eval, iha ha, ihb hb]

def Formula.coeff {P L : Type} [DecidableEq L] (x : P → Bool) : Formula P L → L → Bool
  | .point _, _ => false
  | .line i, j => decide (i = j)
  | .bot, _ => false
  | .top, _ => false
  | .meet a b, j => (a.coeff x j && b.eval x (fun _ => false)) ||
      (a.eval x (fun _ => false) && b.coeff x j)
  | .join a b, j => a.coeff x j || b.coeff x j

lemma Formula.coeff_degree_zero {P L : Type} [DecidableEq L] (f : Formula P L)
    (h : f.degree = 0) (x : P → Bool) (j : L) : f.coeff x j = false := by
  induction f with
  | point p => rfl
  | line l => simp [degree] at h
  | bot => rfl
  | top => rfl
  | meet a b iha ihb =>
    have ha : a.degree = 0 := by simp [degree] at h; omega
    have hb : b.degree = 0 := by simp [degree] at h; omega
    simp [coeff, iha ha, ihb hb]
  | join a b iha ihb =>
    have ha : a.degree = 0 := by simp [degree] at h; omega
    have hb : b.degree = 0 := by simp [degree] at h; omega
    simp [coeff, iha ha, ihb hb]

lemma Formula.linearization {P L : Type} [Fintype L] [DecidableEq L] (f : Formula P L)
    (h : f.degree ≤ 1) (x : P → Bool) (y : L → Bool) :
    f.eval x y = (f.eval x (fun _ => false) ||
      decide (∃ j, y j = true ∧ f.coeff x j = true)) := by
  induction f with
  | point p => simp [eval, coeff]
  | line l => simp [eval, coeff]
  | bot => simp [eval, coeff]
  | top => simp [eval, coeff]
  | meet a b iha ihb =>
    have hz : a.degree = 0 ∨ b.degree = 0 := by simp [degree] at h; omega
    have ha : a.degree ≤ 1 := by simp [degree] at h; omega
    have hb : b.degree ≤ 1 := by simp [degree] at h; omega
    rcases hz with hz | hz
    · have hc : ∀ j, a.coeff x j = false := a.coeff_degree_zero hz x
      simp only [eval, coeff, hc, Bool.false_and, Bool.false_or]
      rw [a.eval_degree_zero hz x y (fun _ => false), ihb hb]
      cases he : a.eval x (fun _ => false) <;> simp
    · have hc : ∀ j, b.coeff x j = false := b.coeff_degree_zero hz x
      simp only [eval, coeff, hc, Bool.and_false, Bool.or_false]
      rw [b.eval_degree_zero hz x y (fun _ => false), iha ha]
      cases he : b.eval x (fun _ => false) <;> simp
  | join a b iha ihb =>
    have ha : a.degree ≤ 1 := by exact (max_le_iff.mp h).1
    have hb : b.degree ≤ 1 := by exact (max_le_iff.mp h).2
    simp only [eval, coeff]
    rw [iha ha, ihb hb]
    cases he : a.eval x (fun _ => false) <;>
      cases hf : b.eval x (fun _ => false) <;>
      simp only [Bool.false_or, Bool.true_or, Bool.or_true]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    aesop

def Formula.all {P L : Type} (fs : List (Formula P L)) : Formula P L :=
  fs.foldr .meet .top

def Formula.any {P L : Type} (fs : List (Formula P L)) : Formula P L :=
  fs.foldr .join .bot

lemma Formula.eval_all {P L : Type} (fs : List (Formula P L)) (x : P → Bool) (y : L → Bool) :
    (Formula.all fs).eval x y = (fs.map (Formula.eval x y)).all id := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
    change (a.eval x y && (Formula.all fs).eval x y) = _
    rw [ih]; rfl

lemma Formula.eval_any {P L : Type} (fs : List (Formula P L)) (x : P → Bool) (y : L → Bool) :
    (Formula.any fs).eval x y = (fs.map (Formula.eval x y)).any id := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
    change (a.eval x y || (Formula.any fs).eval x y) = _
    rw [ih]; rfl

lemma Formula.degree_all {P L : Type} (fs : List (Formula P L)) :
    (Formula.all fs).degree = (fs.map Formula.degree).sum := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
    change a.degree + (Formula.all fs).degree = _
    rw [ih]; rfl

lemma Formula.degree_any {P L : Type} (fs : List (Formula P L)) :
    (Formula.any fs).degree = (fs.map Formula.degree).foldr max 0 := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
    change max a.degree (Formula.any fs).degree = _
    rw [ih]; rfl

def expandGate {P L : Type} (g : Gate) (fs : List (Formula P L)) : Formula P L :=
  let args := g.inputs.map (fun i => fs.getD i .bot)
  match g.op with
  | .and => Formula.all args
  | .or => Formula.any args
  | _ => .bot

lemma eval_expandGate {P L : Type} (g : Gate) (fs : List (Formula P L))
    (hg : g.op = .and ∨ g.op = .or) (x : P → Bool) (y : L → Bool) :
    (expandGate g fs).eval x y = g.op.eval
      (g.inputs.map (fun i => (fs.map (Formula.eval x y)).getD i false)) := by
  have hm : ∀ i, (fs.getD i Formula.bot).eval x y =
      (fs.map (Formula.eval x y)).getD i false := by
    intro i
    simpa only [Formula.eval] using (List.getD_map (f := Formula.eval x y) (d := Formula.bot) (l := fs) (n := i)).symm
  have he : (g.inputs.map (fun i => fs.getD i Formula.bot)).map (Formula.eval x y) =
      g.inputs.map (fun i => (fs.map (Formula.eval x y)).getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hm i)
  rcases hg with h | h
  · simp only [expandGate, h, Formula.eval_all, GateOp.eval, he]
  · simp only [expandGate, h, Formula.eval_any, GateOp.eval, he]

lemma degree_expandGate {P L : Type} (g : Gate) (fs : List (Formula P L))
    (hg : g.op = .and ∨ g.op = .or) :
    (expandGate g fs).degree = g.lineDegree (fs.map Formula.degree) := by
  have hm : ∀ i, (fs.getD i Formula.bot).degree = (fs.map Formula.degree).getD i 0 := by
    intro i
    simpa only [Formula.degree] using (List.getD_map (f := Formula.degree) (d := Formula.bot) (l := fs) (n := i)).symm
  have he : (g.inputs.map (fun i => fs.getD i Formula.bot)).map Formula.degree =
      g.inputs.map (fun i => (fs.map Formula.degree).getD i 0) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hm i)
  rcases hg with h | h
  · simp only [expandGate, h, Formula.degree_all, Gate.lineDegree, he, reduceIte]
  · simp only [expandGate, h, Formula.degree_any, Gate.lineDegree, he, reduceCtorEq, if_false]


def expandList {P L : Type} (gs : List Gate) (fs : List (Formula P L)) : List (Formula P L) :=
  gs.foldl (fun fs g => fs ++ [expandGate g fs]) fs

lemma eval_expandList {P L : Type} (gs : List Gate) (fs : List (Formula P L))
    (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (x : P → Bool) (y : L → Bool) :
    (expandList gs fs).map (Formula.eval x y) =
      gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map (fun i => vs.getD i false))])
        (fs.map (Formula.eval x y)) := by
  induction gs generalizing fs with
  | nil => rfl
  | cons g gs ih =>
    simp only [expandList, List.foldl_cons]
    rw [← expandList, ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.map_append, List.map_cons, List.map_nil, eval_expandGate g fs (hg g (by simp))]

lemma degree_expandList {P L : Type} (gs : List Gate) (fs : List (Formula P L))
    (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (expandList gs fs).map Formula.degree =
      gs.foldl (fun ds g => ds ++ [g.lineDegree ds]) (fs.map Formula.degree) := by
  induction gs generalizing fs with
  | nil => rfl
  | cons g gs ih =>
    simp only [expandList, List.foldl_cons]
    rw [← expandList, ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.map_append, List.map_cons, List.map_nil, degree_expandGate g fs (hg g (by simp))]

def initialFormula (n : ℕ) (marked : Finset ℕ) : List (Formula ℕ ℕ) :=
  (List.range n).map (fun i => if i ∈ marked then .line i else .point i)

def unfoldCircuit (C : Circuit) (n : ℕ) (marked : Finset ℕ) : Formula ℕ ℕ :=
  (expandList C.gates (initialFormula n marked)).getD C.output .bot

lemma degree_initialFormula (n : ℕ) (marked : Finset ℕ) :
    (initialFormula n marked).map Formula.degree =
      (List.range n).map (fun i => if i ∈ marked then 1 else 0) := by
  simp only [initialFormula, List.map_map]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  split <;> rfl

lemma degree_unfoldCircuit (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (hm : IsMonotoneCircuit C) : (unfoldCircuit C n marked).degree = C.lineDeg n marked := by
  unfold unfoldCircuit Circuit.lineDeg Circuit.lineDegrees
  rw [← degree_initialFormula n marked, ← degree_expandList C.gates (initialFormula n marked) hm]
  exact (List.getD_map (f := Formula.degree) (d := Formula.bot) (l := expandList C.gates (initialFormula n marked)) (n := C.output)).symm

lemma eval_unfoldCircuit (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (hm : IsMonotoneCircuit C) (x y : ℕ → Bool) :
    (unfoldCircuit C n marked).eval x y = C.eval
      ((List.range n).map (fun i => if i ∈ marked then y i else x i)) := by
  unfold unfoldCircuit Circuit.eval Circuit.wires
  have he := List.getD_map (f := Formula.eval x y) (d := Formula.bot)
    (l := expandList C.gates (initialFormula n marked)) (n := C.output)
  change (expandList C.gates (initialFormula n marked) |>.getD C.output Formula.bot).eval x y = _
  rw [← he, eval_expandList C.gates (initialFormula n marked) hm x y]
  congr 2
  simp only [initialFormula, List.map_map]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  split <;> rfl



def splitInitial (P L : ℕ) : List (Formula (Fin P) (Fin L)) :=
  List.ofFn (fun i : Fin P => Formula.point i) ++ List.ofFn (fun i : Fin L => Formula.line i)

def splitUnfold (P L : ℕ) (C : Circuit) : Formula (Fin P) (Fin L) :=
  (expandList C.gates (splitInitial P L)).getD C.output .bot

lemma splitInitial_eval (P L : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) :
    (splitInitial P L).map (Formula.eval x y) = List.ofFn x ++ List.ofFn y := by
  simp [splitInitial, List.map_ofFn, Function.comp_def, Formula.eval]

lemma splitInitial_degree (P L : ℕ) :
    (splitInitial P L).map Formula.degree =
      (List.range (P + L)).map (fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0) := by
  simp only [splitInitial, List.map_append, List.map_ofFn, Function.comp_def, Formula.degree]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    by_cases hp : i < P
    · rw [List.getElem_append_left (by simpa using hp)]
      simp [hp, Finset.mem_Ico, Formula.degree, Nat.not_le.mpr hp]
    · have hq : i - P < L := by simp only [List.length_append, List.length_ofFn] at hi; omega
      rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt hp)]
      simp [hq, Formula.degree, Finset.mem_Ico, Nat.le_of_not_lt hp, show i < P+L by simpa using hi]

lemma splitUnfold_eval (P L : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    (splitUnfold P L C).eval x y = C.eval (List.ofFn x ++ List.ofFn y) := by
  unfold splitUnfold Circuit.eval Circuit.wires
  rw [← List.getD_map (f := Formula.eval x y) (d := Formula.bot),
    eval_expandList C.gates (splitInitial P L) hm x y, splitInitial_eval]
  rfl

lemma splitUnfold_degree (P L : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C) :
    (splitUnfold P L C).degree = C.lineDeg (P + L) (Finset.Ico P (P+L)) := by
  unfold splitUnfold Circuit.lineDeg Circuit.lineDegrees
  rw [← splitInitial_degree, ← degree_expandList C.gates (splitInitial P L) hm]
  exact (List.getD_map (f := Formula.degree) (d := Formula.bot)
    (l := expandList C.gates (splitInitial P L)) (n := C.output)).symm

lemma circuit_linearization (P L : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C)
    (hd : HasLineDegree (P+L) (Finset.Ico P (P+L)) C 1)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    C.eval (List.ofFn x ++ List.ofFn y) =
      (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) ||
        decide (∃ j : Fin L, y j = true ∧ (splitUnfold P L C).coeff x j = true)) := by
  have h := Formula.linearization (splitUnfold P L C)
    (by rw [splitUnfold_degree P L C hm]; exact hd) x y
  rw [splitUnfold_eval P L C hm, splitUnfold_eval P L C hm] at h
  apply Bool.eq_iff_iff.mpr
  have hh := Bool.eq_iff_iff.mp h
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using hh

end Transposition738

namespace Transposition738.Reachability
open PEqualNP.CircuitLowerBounds

def scan {α β : Type} (f : β → List α → α) (gs : List β) (xs : List α) : List α :=
  gs.foldl (fun xs g => xs ++ [f g xs]) xs

lemma scan_length {α β : Type} (f : β → List α → α) (gs : List β) (xs : List α) :
    (scan f gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [scan]
  | cons g gs ih =>
    change (scan f gs (xs ++ [f g xs])).length = _
    rw [ih]
    simp
    omega

lemma scan_append {α β : Type} (f : β → List α → α) (gs hs : List β) (xs : List α) :
    scan f (gs ++ hs) xs = scan f hs (scan f gs xs) := by
  simp [scan, List.foldl_append]

lemma scan_extends {α β : Type} (f : β → List α → α) (gs : List β) (xs : List α) :
    ∃ ys, scan f gs xs = xs ++ ys := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp [scan]⟩
  | cons g gs ih =>
    obtain ⟨ys, hy⟩ := ih (xs ++ [f g xs])
    exact ⟨_ :: ys, by simpa [scan, List.append_assoc] using hy⟩

lemma scan_getD_old {α β : Type} (f : β → List α → α) (gs : List β) (xs : List α)
    (i : ℕ) (d : α) (hi : i < xs.length) :
    (scan f gs xs).getD i d = xs.getD i d := by
  obtain ⟨ys, hy⟩ := scan_extends f gs xs
  rw [hy]
  exact List.getD_append _ _ _ _ hi

lemma scan_getD_gate {α β : Type} (f : β → List α → α) (gs : List β) (xs : List α)
    (j : Fin gs.length) (d : α) :
    (scan f gs xs).getD (xs.length + j.val) d =
      f (gs.get j) (scan f (gs.take j.val) xs) := by
  induction gs generalizing xs with
  | nil => exact Fin.elim0 j
  | cons g gs ih =>
    cases j with
    | mk j hj =>
      cases j with
      | zero =>
        change (scan f gs (xs ++ [f g xs])).getD xs.length d = _
        rw [scan_getD_old f gs _ _ d (by simp)]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp [scan]
      | succ j =>
        have h : j < gs.length := by simpa using hj
        change (scan f gs (xs ++ [f g xs])).getD (xs.length + (j + 1)) d = _
        have he : xs.length + (j + 1) = (xs ++ [f g xs]).length + j := by simp; omega
        rw [he, ih _ ⟨j,h⟩]
        rfl

lemma Gate.input_degree_le (g : Gate) (ds : List ℕ) (i : ℕ)
    (hi : i ∈ g.inputs) : ds.getD i 0 ≤ g.lineDegree ds := by
  unfold Gate.lineDegree
  have hm : ds.getD i 0 ∈ g.inputs.map (fun j => ds.getD j 0) := List.mem_map.mpr ⟨i,hi,rfl⟩
  split
  · exact List.single_le_sum (fun a _ => Nat.zero_le a) _ hm
  · generalize g.inputs.map (fun j => ds.getD j 0) = ls at *
    induction ls with
    | nil => simp at hm
    | cons a ls ih =>
      simp only [List.mem_cons] at hm
      rcases hm with h | h
      · subst a; exact Nat.le_max_left _ _
      · exact le_trans (ih h) (Nat.le_max_right _ _)

lemma lineDegrees_length (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    (C.lineDegrees n marked).length = n + C.gates.length := by
  change (scan (fun g d => g.lineDegree d) C.gates _).length = _
  rw [scan_length]
  simp

lemma prefix_degrees_agree (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (j : ℕ) (hj : j ≤ C.gates.length) (i : ℕ) (hi : i < n + j) :
    (C.lineDegrees n marked).getD i 0 =
      (scan (fun g d => g.lineDegree d) (C.gates.take j)
        ((List.range n).map (fun k => if k ∈ marked then 1 else 0))).getD i 0 := by
  unfold Circuit.lineDegrees
  change (scan (fun g d => g.lineDegree d) C.gates _).getD i 0 = _
  conv_lhs => rw [← List.take_append_drop j C.gates]
  rw [scan_append]
  apply scan_getD_old
  rw [scan_length]
  simpa [List.length_take, Nat.min_eq_left hj] using hi

lemma degree_gate_eq (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (j : Fin C.gates.length) :
    (C.lineDegrees n marked).getD (n + j.val) 0 =
      (C.gates.get j).lineDegree
        (scan (fun g d => g.lineDegree d) (C.gates.take j.val)
          ((List.range n).map (fun k => if k ∈ marked then 1 else 0))) := by
  have h := scan_getD_gate (fun g d => g.lineDegree d) C.gates
    ((List.range n).map (fun k => if k ∈ marked then 1 else 0)) j 0
  simpa [scan, Circuit.lineDegrees] using h

def Edge (C : Circuit) (n : ℕ) (a b : ℕ) : Prop :=
  a < b ∧ ∃ j : Fin C.gates.length, b = n + j.val ∧ a ∈ (C.gates.get j).inputs

lemma degree_le_of_edge (C : Circuit) (n : ℕ) (marked : Finset ℕ) (a b : ℕ)
    (h : Edge C n a b) :
    (C.lineDegrees n marked).getD a 0 ≤ (C.lineDegrees n marked).getD b 0 := by
  rcases h with ⟨hab,j,rfl,ha⟩
  rw [degree_gate_eq]
  rw [prefix_degrees_agree C n marked j.val (Nat.le_of_lt j.isLt) a hab]
  exact Gate.input_degree_le _ _ _ ha

lemma degree_le_of_path (C : Circuit) (n : ℕ) (marked : Finset ℕ) (a b : ℕ)
    (h : Relation.ReflTransGen (Edge C n) a b) :
    (C.lineDegrees n marked).getD a 0 ≤ (C.lineDegrees n marked).getD b 0 := by
  induction h with
  | refl => exact le_refl _
  | tail h he ih => exact le_trans ih (degree_le_of_edge C n marked _ _ he)

lemma reached_degree_le_one (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (hdeg : HasLineDegree n marked C 1) (a : ℕ)
    (h : Relation.ReflTransGen (Edge C n) a C.output) :
    (C.lineDegrees n marked).getD a 0 ≤ 1 :=
  le_trans (degree_le_of_path C n marked _ _ h) hdeg

lemma edge_strict (C : Circuit) (n : ℕ) {a b : ℕ} (h : Edge C n a b) : a < b := h.1

lemma path_le (C : Circuit) (n : ℕ) {a b : ℕ}
    (h : Relation.ReflTransGen (Edge C n) a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail h he ih => exact le_trans ih (Nat.le_of_lt he.1)

lemma output_is_last (C : Circuit) (n : ℕ) (hne : C.gates ≠ [])
    (hall : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Edge C n) (n + j.val) C.output) :
    C.output = n + C.gates.length - 1 := by
  have ht : 0 < C.gates.length := List.length_pos_iff.mpr hne
  let j : Fin C.gates.length := ⟨C.gates.length - 1, by omega⟩
  have hlow := path_le C n (hall j)
  have hupper : ∀ a b, Edge C n a b → b < n + C.gates.length := by
    intro a b he
    rcases he with ⟨_,k,rfl,_⟩
    omega
  have ho : C.output < n + C.gates.length := by
    have hp := hall j
    have hh : ∀ b, Relation.ReflTransGen (Edge C n) (n + j.val) b →
        b < n + C.gates.length := by
      intro b hb
      induction hb with
      | refl => dsimp [j]; omega
      | tail h he ih => exact hupper _ _ he
    exact hh _ hp
  dsimp [j] at hlow
  omega

lemma input_degree (C : Circuit) (n : ℕ) (marked : Finset ℕ) (i : ℕ) (hi : i < n) :
    (C.lineDegrees n marked).getD i 0 = if i ∈ marked then 1 else 0 := by
  change (scan (fun g d => g.lineDegree d) C.gates _).getD i 0 = _
  rw [scan_getD_old _ _ _ _ _ (by simpa)]
  simp only [List.getD]
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp [hi]

lemma marked_input_positive (C : Circuit) (n : ℕ) (marked : Finset ℕ) (i : ℕ)
    (hi : i < n) (hm : i ∈ marked) : (C.lineDegrees n marked).getD i 0 = 1 := by
  rw [input_degree C n marked i hi, if_pos hm]

lemma no_reached_line_if_degree_zero (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (hdeg : C.lineDeg n marked = 0) (i : ℕ) (hi : i < n) (hm : i ∈ marked) :
    ¬ Relation.ReflTransGen (Edge C n) i C.output := by
  intro hp
  have h := degree_le_of_path C n marked _ _ hp
  rw [marked_input_positive C n marked i hi hm] at h
  change 1 ≤ C.lineDeg n marked at h
  omega

lemma Gate.positive_iff (g : Gate) (ds : List ℕ) :
    0 < g.lineDegree ds ↔ ∃ i ∈ g.inputs, 0 < ds.getD i 0 := by
  unfold Gate.lineDegree
  have hs : ∀ ls : List ℕ, 0 < ls.sum ↔ ∃ a ∈ ls, 0 < a := by
    intro ls
    induction ls with
    | nil => simp
    | cons a ls ih => simp [Nat.add_pos_iff_pos_or_pos, ih]
  have hm : ∀ ls : List ℕ, 0 < ls.foldr max 0 ↔ ∃ a ∈ ls, 0 < a := by
    intro ls
    induction ls with
    | nil => simp
    | cons a ls ih => simp [lt_max_iff, ih]
  split
  · rw [hs]; simp only [List.mem_map]; aesop
  · rw [hm]; simp only [List.mem_map]; aesop

lemma Gate.zero_iff (g : Gate) (ds : List ℕ) :
    g.lineDegree ds = 0 ↔ ∀ i ∈ g.inputs, ds.getD i 0 = 0 := by
  have h := Gate.positive_iff g ds
  constructor
  · intro hz i hi
    by_contra hn
    have hp := h.mpr ⟨i,hi,by omega⟩
    omega
  · intro hz
    by_contra hn
    obtain ⟨i,hi,hp⟩ := h.mp (by omega)
    have := hz i hi
    omega

end Transposition738.Reachability

namespace Transposition738
open PEqualNP.CircuitLowerBounds

def Formula.contribution {P L : Type} [Fintype L] [DecidableEq L]
    (f : Formula P L) (x : P → Bool) (y : L → Bool) : Bool :=
  decide (∃ j, y j = true ∧ f.coeff x j = true)

lemma Formula.contribution_zero {P L : Type} [Fintype L] [DecidableEq L]
    (f : Formula P L) (x : P → Bool) (y : L → Bool) (hd : f.degree = 0) :
    f.contribution x y = false := by
  simp [contribution,f.coeff_degree_zero hd x]

lemma Formula.contribution_join {P L : Type} [Fintype L] [DecidableEq L]
    (a b : Formula P L) (x : P → Bool) (y : L → Bool) :
    (a.join b).contribution x y = (a.contribution x y || b.contribution x y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [contribution,coeff,decide_eq_true_eq,Bool.or_eq_true]
  aesop

lemma Formula.contribution_meet_left {P L : Type} [Fintype L] [DecidableEq L]
    (a b : Formula P L) (x : P → Bool) (y : L → Bool) (hb : b.degree = 0) :
    (a.meet b).contribution x y = (a.contribution x y && b.eval x (fun _ => false)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [contribution,coeff,b.coeff_degree_zero hb x,Bool.and_false,Bool.or_false,
    decide_eq_true_eq,Bool.and_eq_true]
  aesop

lemma Formula.contribution_meet_right {P L : Type} [Fintype L] [DecidableEq L]
    (a b : Formula P L) (x : P → Bool) (y : L → Bool) (ha : a.degree = 0) :
    (a.meet b).contribution x y = (a.eval x (fun _ => false) && b.contribution x y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [contribution,coeff,a.coeff_degree_zero ha x,Bool.false_and,Bool.false_or,
    decide_eq_true_eq,Bool.and_eq_true]
  aesop

lemma Formula.contribution_meet (a b : Formula (Fin P) (Fin L))
    (x : Fin P → Bool) (y : Fin L → Bool) (hd : (a.meet b).degree ≤ 1) :
    (a.meet b).contribution x y =
      ((a.contribution x y && b.eval x (fun _ => false)) ||
        (b.contribution x y && a.eval x (fun _ => false))) := by
  have hz : a.degree = 0 ∨ b.degree = 0 := by change a.degree+b.degree ≤ 1 at hd; omega
  rcases hz with ha | hb
  · rw [Formula.contribution_meet_right a b x y ha,Formula.contribution_zero a x y ha]
    simp [Bool.and_comm]
  · rw [Formula.contribution_meet_left a b x y hb,Formula.contribution_zero b x y hb]
    simp

end Transposition738

namespace Transposition738.Builder
open PEqualNP.CircuitLowerBounds
attribute [local instance] lineDegreeGateOpDecEq

def localEdges (g : Gate) (d : ℕ → ℕ) (pt : ℕ → Ref) : List (ℕ × Ref) :=
  if g.op = .and then
    match g.inputs with
    | [i] => if d i = 0 then [] else [(i,.top)]
    | [i,j] => if d i = 0 then
        (if d j = 0 then [] else [(j,pt i)])
      else [(i,pt j)]
    | _ => []
  else g.inputs.filterMap (fun i => if d i = 0 then none else some (i,.top))

lemma localEdges_cost (g : Gate) (d : ℕ → ℕ) (pt : ℕ → Ref)
    (hf : g.inputs.length ≤ 2) :
    (localEdges g d pt).length +
      ((localEdges g d pt).filter (fun e => e.2 ≠ .top)).length ≤ 2 := by
  rcases g with ⟨op,ins⟩
  cases ins with
  | nil => simp [localEdges]
  | cons i ins =>
    cases ins with
    | nil =>
      by_cases ho : op = .and <;> by_cases hi : d i = 0 <;>
        simp [localEdges,ho,hi]
    | cons j ins =>
      cases ins with
      | nil =>
        by_cases ho : op = .and <;> by_cases hi : d i = 0 <;> by_cases hj : d j = 0 <;>
          simp [localEdges,ho,hi,hj]
        all_goals
          simp only [List.filter_cons,List.filter_nil]
          split <;> simp
      | cons k ins => simp at hf

lemma localEdges_cost_zero (g : Gate) (d : ℕ → ℕ) (pt : ℕ → Ref)
    (hz : ∀ i ∈ g.inputs, d i = 0) : localEdges g d pt = [] := by
  unfold localEdges
  split
  · split <;> simp_all
  · apply List.filterMap_eq_nil_iff.mpr
    intro i hi
    simp [hz i hi]


lemma contribution_meet_top (a : Formula (Fin P) (Fin L)) (x : Fin P → Bool) (y : Fin L → Bool) :
    (a.meet .top).contribution x y = a.contribution x y := by
  rw [Formula.contribution_meet_left a .top x y rfl]
  simp [Formula.eval]

lemma contribution_join_bot (a : Formula (Fin P) (Fin L)) (x : Fin P → Bool) (y : Fin L → Bool) :
    (a.join .bot).contribution x y = a.contribution x y := by
  rw [Formula.contribution_join]
  simp [Formula.contribution,Formula.coeff]

lemma localEdges_equation (g : Gate) (fs : List (Formula (Fin P) (Fin L)))
    (pt : ℕ → Ref) (vs : List Bool) (x : Fin P → Bool) (y : Fin L → Bool)
    (hm : g.op = .and ∨ g.op = .or) (hf : g.inputs.length ≤ 2)
    (hd : (expandGate g fs).degree ≤ 1)
    (hp : ∀ i, ((fs[i]?.getD Formula.bot)).degree = 0 →
      (pt i).value vs = ((fs[i]?.getD Formula.bot)).eval x (fun _ => false)) :
    (expandGate g fs).contribution x y =
      ReverseCut.weighted
        ((localEdges g (fun i => ((fs[i]?.getD Formula.bot)).degree) pt).map
          (fun e => (e.1,e.2.value vs)))
        (fun i => ((fs[i]?.getD Formula.bot)).contribution x y) := by
  rcases g with ⟨op,ins⟩
  cases ins with
  | nil =>
    rcases hm with rfl | rfl <;>
      simp [List.getD,expandGate,Formula.all,Formula.any,Formula.contribution,Formula.coeff,localEdges,ReverseCut.weighted]
  | cons i ins =>
    cases ins with
    | nil =>
      rcases hm with rfl | rfl
      · by_cases hi : ((fs[i]?.getD Formula.bot)).degree = 0
        · simp [List.getD,expandGate,Formula.all,contribution_meet_top,Formula.degree,Formula.eval,
            localEdges,hi,ReverseCut.weighted,Formula.contribution_zero _ x y hi]
        · simp [List.getD,expandGate,Formula.all,contribution_meet_top,Formula.degree,Formula.eval,
            localEdges,hi,ReverseCut.weighted,Ref.value]
      · by_cases hi : ((fs[i]?.getD Formula.bot)).degree = 0
        · simp [List.getD,expandGate,Formula.any,Formula.contribution_join,contribution_join_bot,Formula.contribution,Formula.coeff,
            localEdges,hi,ReverseCut.weighted,Formula.coeff_degree_zero _ hi x]
        · simp [List.getD,expandGate,Formula.any,Formula.contribution_join,contribution_join_bot,Formula.contribution,Formula.coeff,
            localEdges,hi,ReverseCut.weighted,Ref.value]
    | cons j ins =>
      cases ins with
      | nil =>
        rcases hm with rfl | rfl
        · have hh : ((fs[i]?.getD Formula.bot)).degree + ((fs[j]?.getD Formula.bot)).degree ≤ 1 := by
            simpa [expandGate,Formula.all,Formula.degree] using hd
          have hz : ((fs[i]?.getD Formula.bot)).degree = 0 ∨ ((fs[j]?.getD Formula.bot)).degree = 0 := by omega
          by_cases hi : ((fs[i]?.getD Formula.bot)).degree = 0
          · by_cases hj : ((fs[j]?.getD Formula.bot)).degree = 0
            · simp [List.getD,expandGate,Formula.all,localEdges,hi,hj,ReverseCut.weighted,
                Formula.contribution_meet_right _ _ x y hi,contribution_meet_top,Formula.degree,Formula.eval,
                Formula.contribution_zero _ x y hi,Formula.contribution_zero _ x y hj]
            · simp [List.getD,expandGate,Formula.all,localEdges,hi,hj,ReverseCut.weighted,
                Formula.contribution_meet_right _ _ x y hi,
                contribution_meet_top,Formula.degree,Formula.eval,hp i hi,Bool.and_comm]
          · have hj := hz.resolve_left hi
            simp [List.getD,expandGate,Formula.all,localEdges,hi,ReverseCut.weighted,
              Formula.contribution_meet_left (fs[j]?.getD Formula.bot) Formula.top x y rfl,
              Formula.contribution_meet_left (fs[i]?.getD Formula.bot)
                ((fs[j]?.getD Formula.bot).meet Formula.top) x y (by simp [Formula.degree,hj]),contribution_meet_top,Formula.degree,Formula.eval,hp j hj,hj]
        · by_cases hi : (fs[i]?.getD Formula.bot).degree = 0 <;>
            by_cases hj : (fs[j]?.getD Formula.bot).degree = 0 <;>
            simp [List.getD,expandGate,Formula.any,localEdges,hi,hj,ReverseCut.weighted,Ref.value,
              Formula.contribution_join,contribution_join_bot,Formula.contribution_zero,
              show Formula.bot.contribution x y = false by simp [Formula.contribution,Formula.coeff]]
      | cons k ins => simp at hf


lemma localEdges_mem (g : Gate) (d : ℕ → ℕ) (pt : ℕ → Ref) (i : ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hf : g.inputs.length ≤ 2)
    (hd : (if g.op = .and then (g.inputs.map d).sum else (g.inputs.map d).foldr max 0) ≤ 1) :
    (∃ r, (i,r) ∈ localEdges g d pt) ↔ i ∈ g.inputs ∧ 0 < d i := by
  rcases g with ⟨op,ins⟩
  cases ins with
  | nil => simp [localEdges]
  | cons a ins =>
    cases ins with
    | nil =>
      rcases hm with rfl | rfl <;> by_cases ha : d a = 0 <;>
        simp_all [localEdges,Nat.pos_iff_ne_zero]
    | cons b ins =>
      cases ins with
      | nil =>
        rcases hm with rfl | rfl
        · have hab : d a + d b ≤ 1 := by simpa using hd
          by_cases ha : d a = 0 <;> by_cases hb : d b = 0 <;>
            simp_all [localEdges,Nat.pos_iff_ne_zero] <;> aesop (add safe forward Nat.eq_zero_of_add_eq_zero)
          omega
        · by_cases ha : d a = 0 <;> by_cases hb : d b = 0 <;>
            simp_all [localEdges,Nat.pos_iff_ne_zero] <;> aesop
      | cons c ins => simp at hf

lemma localEdges_weight_valid (g : Gate) (d : ℕ → ℕ) (pt : ℕ → Ref) (N : ℕ)
    (hp : ∀ i, d i = 0 → (pt i).Valid N)
    (hm : g.op = .and ∨ g.op = .or) (hf : g.inputs.length ≤ 2)
    (hd : (if g.op = .and then (g.inputs.map d).sum else (g.inputs.map d).foldr max 0) ≤ 1) :
    ∀ e ∈ localEdges g d pt, e.2.Valid N := by
  rcases g with ⟨op,ins⟩
  cases ins with
  | nil => simp [localEdges]
  | cons a ins =>
    cases ins with
    | nil =>
      rcases hm with rfl | rfl <;> by_cases ha : d a = 0 <;>
        simp [localEdges,ha,Ref.Valid]
    | cons b ins =>
      cases ins with
      | nil =>
        rcases hm with rfl | rfl
        · have hab : d a+d b ≤ 1 := by simpa using hd
          by_cases ha : d a = 0
          · by_cases hb : d b = 0 <;> simp [localEdges,ha,hb,hp a ha]
          · have hb : d b = 0 := by omega
            simp [localEdges,ha,hp b hb]
        · by_cases ha : d a = 0 <;> by_cases hb : d b = 0 <;>
            simp [localEdges,ha,hb,Ref.Valid]
      | cons c ins => simp at hf

lemma zero_gate_inputs (P L : ℕ) (C : Circuit) (j : Fin C.gates.length)
    (hz : (C.lineDegrees (P+L) (Finset.Ico P (P+L))).getD (P+L+j.val) 0 = 0) :
    ∀ i ∈ (C.gates.get j).inputs, i < P+L+j.val →
      (C.lineDegrees (P+L) (Finset.Ico P (P+L))).getD i 0 = 0 := by
  intro i hi hij
  have hh := Reachability.degree_le_of_edge C (P+L) (Finset.Ico P (P+L)) i (P+L+j.val)
    ⟨hij,j,rfl,hi⟩
  omega

lemma copyPoints_agrees (P L : ℕ) (C : Circuit)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (x : List Bool) (hx : x.length = P) :
    AgreeZero (C.lineDegrees (P+L) (Finset.Ico P (P+L)))
      ((copyPoints P L C).refs.map (Ref.value (run (copyPoints P L C).gates x)))
      (C.wires (x ++ List.replicate L false)) := by
  rw [copyPoints_values P L C hm hf x hx]
  have hh := maskedFold_agrees (C.lineDegrees (P+L) (Finset.Ico P (P+L)))
    (C.gates.zipIdx.map (fun (g,j) => (P+L+j,g)))
    (x ++ List.replicate L false) (x ++ List.replicate L false)
    ⟨rfl,fun _ _ => rfl⟩ ?_ ?_
  · convert hh using 1
    unfold Circuit.wires
    simp only [List.foldl_map]
    have he : ∀ (gs : List Gate) (k : ℕ) (ws : List Bool),
        (gs.zipIdx k).foldl
          (fun ws jg => ws ++ [jg.1.op.eval (jg.1.inputs.map (fun i => ws.getD i false))]) ws =
        gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) ws := by
      intro gs
      induction gs with
      | nil => intros; rfl
      | cons g gs ih => intros; simp only [List.zipIdx_cons, List.foldl_cons]; exact ih _ _
    exact (he _ _ _).symm
  · intro k hk
    simp [hx]
  · intro jg hjg hz i hi hij
    obtain ⟨⟨g,j⟩,hg,rfl⟩ := List.mem_map.mp hjg
    have hj := List.snd_lt_of_mem_zipIdx hg
    have he := List.fst_eq_of_mem_zipIdx hg
    change g = C.gates[j-0] at he
    simp only [Nat.sub_zero] at he
    apply zero_gate_inputs P L C ⟨j,by simpa using hj⟩ hz i
    · simpa only [List.get_eq_getElem, ← he] using hi
    · exact hij



def rootDegrees (P L : ℕ) (C : Circuit) : List ℕ :=
  C.lineDegrees (P+L) (Finset.Ico P (P+L))

def edgeDegree (P L : ℕ) (C : Circuit) (j i : ℕ) : ℕ :=
  if i < P+L+j then (rootDegrees P L C).getD i 0 else 0

def edgePoint (P L : ℕ) (C : Circuit) (j i : ℕ) : Ref :=
  if i < P+L+j then (copyPoints P L C).refs.getD i .bot else .bot

def rootEdges (P L : ℕ) (C : Circuit) (j : ℕ) (g : Gate) : List (ℕ × Ref) :=
  localEdges g (edgeDegree P L C j) (edgePoint P L C j)

def rootGraph (P L : ℕ) (C : Circuit) : List (ℕ × List (ℕ × Ref)) :=
  C.gates.zipIdx.map (fun (g,j) => (P+L+j,rootEdges P L C j g))

lemma prefix_read_degree (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) (i : ℕ) :
    (Reachability.scan (fun g ds => g.lineDegree ds) (C.gates.take j.val)
      ((List.range (P+L)).map (fun k => if k ∈ Finset.Ico P (P+L) then 1 else 0))).getD i 0 =
      edgeDegree P L C j.val i := by
  unfold edgeDegree rootDegrees
  split
  · exact (Reachability.prefix_degrees_agree C (P+L) _ j.val (by omega) i ‹_›).symm
  · apply List.getD_eq_default
    rw [Reachability.scan_length]
    simp only [List.length_map,List.length_range,List.length_take]
    omega

lemma root_gate_degree_eq (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) :
    (rootDegrees P L C).getD (P+L+j.val) 0 =
      if (C.gates.get j).op = .and then
        ((C.gates.get j).inputs.map (edgeDegree P L C j.val)).sum
      else ((C.gates.get j).inputs.map (edgeDegree P L C j.val)).foldr max 0 := by
  unfold rootDegrees
  rw [Reachability.degree_gate_eq]
  unfold Gate.lineDegree
  have he : ∀ i, (Reachability.scan (fun g ds => g.lineDegree ds) (C.gates.take j.val)
      ((List.range (P+L)).map (fun k => if k ∈ Finset.Ico P (P+L) then 1 else 0))).getD i 0 =
      edgeDegree P L C j.val i := prefix_read_degree P L C j
  congr 1 <;> congr 1 <;> apply List.map_congr_left <;> intro i hi <;> exact he i

lemma rootEdges_mem (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) (i : ℕ)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : (rootDegrees P L C).getD (P+L+j.val) 0 ≤ 1) :
    (∃ r, (i,r) ∈ rootEdges P L C j.val (C.gates.get j)) ↔
      i ∈ (C.gates.get j).inputs ∧ i < P+L+j.val ∧
        0 < (rootDegrees P L C).getD i 0 := by
  unfold rootEdges
  rw [localEdges_mem _ _ _ _ (hm _ (List.get_mem _ _)) (hf _ (List.get_mem _ _))
    (by rw [← root_gate_degree_eq P L C j]; exact hd)]
  unfold edgeDegree
  split <;> simp_all

lemma rootEdges_valid (P L : ℕ) (C : Circuit) (j : Fin C.gates.length)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : (rootDegrees P L C).getD (P+L+j.val) 0 ≤ 1) :
    ∀ e ∈ rootEdges P L C j.val (C.gates.get j), e.2.Valid (P+(copyPoints P L C).gates.length) := by
  apply localEdges_weight_valid
  · intro i hi
    unfold edgePoint
    split
    · exact valid_getD _ _ _ (valid_copyPoints P L C)
    · trivial
  · exact hm _ (List.get_mem _ _)
  · exact hf _ (List.get_mem _ _)
  · rw [← root_gate_degree_eq P L C j]
    exact hd


lemma rootEdges_cost (P L : ℕ) (C : Circuit) (j : Fin C.gates.length)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (rootEdges P L C j.val (C.gates.get j)).length +
      ((rootEdges P L C j.val (C.gates.get j)).filter (fun e => e.2 ≠ .top)).length ≤
        if (rootDegrees P L C).getD (P+L+j.val) 0 = 0 then 0 else 2 := by
  by_cases hz : (rootDegrees P L C).getD (P+L+j.val) 0 = 0
  · rw [if_pos hz]
    have hg : (C.gates.get j).lineDegree
        (Reachability.scan (fun g ds => g.lineDegree ds) (C.gates.take j.val)
          ((List.range (P+L)).map (fun k => if k ∈ Finset.Ico P (P+L) then 1 else 0))) = 0 := by
      rw [← Reachability.degree_gate_eq]
      exact hz
    have hi := (Reachability.Gate.zero_iff _ _).mp hg
    have he : rootEdges P L C j.val (C.gates.get j) = [] := by
      apply localEdges_cost_zero
      intro i him
      rw [← prefix_read_degree P L C j i]
      exact hi i him
    rw [he]
    decide
  · rw [if_neg hz]
    exact localEdges_cost _ _ _ (hf _ (List.get_mem _ _))

lemma rootGraph_edges_cost (P L : ℕ) (C : Circuit)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    edgeCost (rootGraph P L C) ≤
      2 * ((C.gates.zipIdx).filter (fun gj =>
        (rootDegrees P L C).getD (P+L+gj.2) 0 ≠ 0)).length := by
  have hh : ∀ ls : List (Gate × ℕ),
      (∀ gj ∈ ls, gj ∈ C.gates.zipIdx) →
      edgeCost (ls.map (fun (g,j) => (P+L+j,rootEdges P L C j g))) ≤
        2 * (ls.filter (fun gj => (rootDegrees P L C).getD (P+L+gj.2) 0 ≠ 0)).length := by
    intro ls
    induction ls with
    | nil => intro _; simp [edgeCost]
    | cons gj ls ih =>
      intro hmem
      have hg := hmem gj (by simp)
      rcases gj with ⟨g,j⟩
      have hj := List.snd_lt_of_mem_zipIdx hg
      have he := List.fst_eq_of_mem_zipIdx hg
      change g = C.gates[j-0] at he
      simp only [Nat.sub_zero] at he
      have hc := rootEdges_cost P L C ⟨j,by simpa using hj⟩ hf
      rw [List.get_eq_getElem,← he] at hc
      have ht := ih (fun a ha => hmem a (by simp [ha]))
      have hec : edgeCost (((g,j)::ls).map (fun (g,j) => (P+L+j,rootEdges P L C j g))) =
          edgeCost (ls.map (fun (g,j) => (P+L+j,rootEdges P L C j g))) +
          (rootEdges P L C j g).length +
          ((rootEdges P L C j g).filter (fun e => e.2 ≠ .top)).length := by
        simp only [edgeCost,List.map_cons,List.sum_cons]
        omega
      rw [hec]
      simp only [ne_eq] at *
      by_cases hz : (rootDegrees P L C).getD (P+L+j) 0 = 0
      · simp only [hz,ite_true] at hc
        simp only [List.filter_cons,hz,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,Prod.fst,Prod.snd]
        omega
      · simp only [hz,ite_false] at hc
        simp only [List.filter_cons,hz,ne_eq,not_false_eq_true,decide_true,ite_true,List.length_cons,Prod.fst,Prod.snd]
        omega
  exact hh _ (fun _ h => h)

end Transposition738.Builder

namespace Transposition738.GraphCount

lemma path_first {α : Type} (E : α → α → Prop) (a b : α)
    (h : Relation.ReflTransGen E a b) : a = b ∨ ∃ c, E a c := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail c d h he ih =>
    rcases ih with rfl | hh
    · exact Or.inr ⟨d,he⟩
    · exact Or.inr hh

lemma reached_in_receivers (E : ℕ → ℕ → Prop) (root : ℕ) (vertices receivers : Finset ℕ)
    (hreach : ∀ v ∈ vertices, Relation.ReflTransGen E v root)
    (hedge : ∀ a b, a ∈ vertices → E a b → a ∈ receivers) :
    vertices ⊆ insert root receivers := by
  intro v hv
  rcases path_first E v root (hreach v hv) with rfl | ⟨c,hc⟩
  · simp
  · exact Finset.mem_insert_of_mem (hedge v c hv hc)

lemma count_reached (E : ℕ → ℕ → Prop) (root : ℕ) (gates lines receivers : Finset ℕ)
    (hdis : Disjoint gates lines)
    (hreach : ∀ v ∈ gates ∪ lines, Relation.ReflTransGen E v root)
    (hedge : ∀ a b, a ∈ gates ∪ lines → E a b → a ∈ receivers) :
    gates.card + lines.card ≤ (insert root receivers).card := by
  have hs := reached_in_receivers E root (gates ∪ lines) receivers hreach hedge
  have hc := Finset.card_le_card hs
  simpa [Finset.card_union_of_disjoint hdis] using hc

lemma zero_positive_partition (ls : List ℕ) :
    (ls.filter (fun d => d = 0)).length + (ls.filter (fun d => 0 < d)).length = ls.length := by
  induction ls with
  | nil => rfl
  | cons a ls ih =>
    by_cases ha : a = 0
    · subst a; simp [ih, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have hp : 0 < a := Nat.pos_of_ne_zero ha
      simp [ha,hp,← ih,Nat.add_assoc]

end Transposition738.GraphCount

namespace Transposition738.Builder
open PEqualNP.CircuitLowerBounds

lemma receiver_of_root_edge (P L : ℕ) (C : Circuit) (a b : ℕ)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hall : ∀ j : Fin C.gates.length,
      (rootDegrees P L C).getD (P+L+j.val) 0 ≤ 1)
    (he : Reachability.Edge C (P+L) a b)
    (ha : 0 < (rootDegrees P L C).getD a 0) : a ∈ receivers (rootGraph P L C) := by
  rcases he with ⟨hab,j,rfl,ha_in⟩
  obtain ⟨r,hr⟩ := (rootEdges_mem P L C j a hm hf (hall j)).mpr ⟨ha_in,hab,ha⟩
  unfold receivers rootGraph
  apply List.mem_toFinset.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(P+L+j.val,rootEdges P L C j.val (C.gates.get j)),?_,?_⟩
  · apply List.mem_map.mpr
    refine ⟨(C.gates.get j,j.val),?_,rfl⟩
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simp
  · exact List.mem_map.mpr ⟨(a,r),hr,rfl⟩

lemma positive_reached_in_receivers (P L : ℕ) (C : Circuit) (a : ℕ)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hall : ∀ j : Fin C.gates.length,
      (rootDegrees P L C).getD (P+L+j.val) 0 ≤ 1)
    (hr : Relation.ReflTransGen (Reachability.Edge C (P+L)) a C.output)
    (ha : 0 < (rootDegrees P L C).getD a 0) :
    a ∈ insert C.output (receivers (rootGraph P L C)) := by
  rcases GraphCount.path_first _ _ _ hr with rfl | ⟨b,hb⟩
  · simp
  · exact Finset.mem_insert_of_mem (receiver_of_root_edge P L C a b hm hf hall hb ha)


def positiveGates (P L : ℕ) (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => 0 < (rootDegrees P L C).getD (P+L+j.val) 0)

lemma positive_vertices_card (P L : ℕ) (C : Circuit) (N : Finset (Fin L))
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : HasLineDegree (P+L) (Finset.Ico P (P+L)) C 1)
    (hg : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Reachability.Edge C (P+L)) (P+L+j.val) C.output)
    (hN : ∀ w : Fin L, w ∈ N ↔ Relation.ReflTransGen (Reachability.Edge C (P+L)) (P+w.val) C.output) :
    (positiveGates P L C).card + N.card ≤ (insert C.output (receivers (rootGraph P L C))).card := by
  let G := (positiveGates P L C).image (fun j => P+L+j.val)
  let Y := N.image (fun w => P+w.val)
  have hG : G.card = (positiveGates P L C).card := Finset.card_image_of_injective _ (by
    intro a b hab; dsimp only at hab; apply Fin.ext; omega)
  have hY : Y.card = N.card := Finset.card_image_of_injective _ (by
    intro a b hab; dsimp only at hab; apply Fin.ext; omega)
  have hdis : Disjoint G Y := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w,_,he⟩ := Finset.mem_image.mp hb
    omega
  have hs : G ∪ Y ⊆ insert C.output (receivers (rootGraph P L C)) := by
    intro a ha
    have hall : ∀ j : Fin C.gates.length, (rootDegrees P L C).getD (P+L+j.val) 0 ≤ 1 :=
      fun j => Reachability.reached_degree_le_one C (P+L) _ hd _ (hg j)
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
      apply positive_reached_in_receivers P L C _ hm hf hall (hg j)
      exact (Finset.mem_filter.mp hj).2
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ha
      apply positive_reached_in_receivers P L C _ hm hf hall ((hN w).mp hw)
      have he := Reachability.marked_input_positive C (P+L) (Finset.Ico P (P+L)) (P+w.val)
        (by omega) (by simp only [Finset.mem_Ico]; constructor <;> omega)
      change 0 < (C.lineDegrees (P+L) (Finset.Ico P (P+L))).getD (P+w.val) 0
      omega
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hdis,hG,hY] at hc
  exact hc


lemma zipIdx_eq_ofFn (gs : List Gate) : gs.zipIdx = List.ofFn (fun j : Fin gs.length => (gs.get j,j.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

lemma filtered_ofFn_card {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((List.ofFn (fun j : Fin n => j)).filter p).length = (Finset.univ.filter p).card := by
  classical
  have hn : (List.ofFn (fun j : Fin n => j)).Nodup := List.nodup_ofFn.mpr Function.injective_id
  have he := List.toFinset_card_of_nodup (hn.filter p)
  have hu : (List.ofFn (fun j : Fin n => j)).toFinset = Finset.univ := by
    ext j; simp
  rw [List.toFinset_filter,hu] at he
  exact he.symm

lemma positiveGates_card (P L : ℕ) (C : Circuit) :
    ((C.gates.zipIdx).filter (fun gj =>
      (rootDegrees P L C).getD (P+L+gj.2) 0 ≠ 0)).length = (positiveGates P L C).card := by
  rw [zipIdx_eq_ofFn]
  have he : List.ofFn (fun j : Fin C.gates.length => (C.gates.get j,j.val)) =
      (List.ofFn (fun j : Fin C.gates.length => j)).map (fun j => (C.gates.get j,j.val)) := by
    rw [List.map_ofFn]
    rfl
  rw [he,List.filter_map,List.length_map]
  change ((List.ofFn (fun j : Fin C.gates.length => j)).filter
    (fun j => (rootDegrees P L C).getD (P+L+j.val) 0 ≠ 0)).length = _
  have hh := filtered_ofFn_card (fun j : Fin C.gates.length => (rootDegrees P L C).getD (P+L+j.val) 0 ≠ 0)
  rw [hh]
  congr 1
  ext j
  simp [positiveGates,Nat.pos_iff_ne_zero]


lemma copyPoints_cost_exact (P L : ℕ) (C : Circuit) :
    (copyPoints P L C).gates.length + (positiveGates P L C).card ≤ C.gates.length := by
  have hh := copyFold_cost P (rootDegrees P L C)
    (C.gates.zipIdx.map (fun (g,j) => (P+L+j,g)))
    ⟨[],(List.range P).map Ref.wire ++ List.replicate L .bot⟩
  change (copyPoints P L C).gates.length ≤ 0 + _ at hh
  have hp := positiveGates_card P L C
  have hz : ((C.gates.zipIdx.map (fun (g,j) => (P+L+j,g))).filter
        (fun jg => (rootDegrees P L C).getD jg.1 0 = 0)).length =
      (C.gates.zipIdx.filter (fun gj => (rootDegrees P L C).getD (P+L+gj.2) 0 = 0)).length := by
    rw [List.filter_map,List.length_map]
    rfl
  rw [hz] at hh
  have hpart : (C.gates.zipIdx.filter (fun gj => (rootDegrees P L C).getD (P+L+gj.2) 0 = 0)).length +
      (C.gates.zipIdx.filter (fun gj => (rootDegrees P L C).getD (P+L+gj.2) 0 ≠ 0)).length = C.gates.length := by
    have hgen : ∀ ls : List (Gate × ℕ),
        (ls.filter (fun gj => (rootDegrees P L C).getD (P+L+gj.2) 0 = 0)).length +
        (ls.filter (fun gj => (rootDegrees P L C).getD (P+L+gj.2) 0 ≠ 0)).length = ls.length := by
      intro ls
      induction ls with
      | nil => rfl
      | cons a ls ih =>
        simp only [ne_eq] at *
        by_cases ha : (rootDegrees P L C).getD (P+L+a.2) 0 = 0 <;>
          simp only [List.filter_cons,ha,ne_eq,not_true_eq_false,not_false_eq_true,
            decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,List.length_cons] <;> omega
    simpa only [List.length_zipIdx] using hgen C.gates.zipIdx
  omega

theorem root_transposition_size (P L : ℕ) (C : Circuit) (N : Finset (Fin L))
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : HasLineDegree (P+L) (Finset.Ico P (P+L)) C 1)
    (hg : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Reachability.Edge C (P+L)) (P+L+j.val) C.output)
    (hN : ∀ w : Fin L, w ∈ N ↔ Relation.ReflTransGen (Reachability.Edge C (P+L)) (P+w.val) C.output) :
    (weightedSweep P (rootGraph P L C)
      (startContexts (copyPoints P L C).gates (P+L+C.gates.length) C.output)).gates.length + N.card ≤ C.size+1 := by
  have hc := copyPoints_cost_exact P L C
  have he := rootGraph_edges_cost P L C hf
  rw [positiveGates_card] at he
  have hv := positive_vertices_card P L C N hm hf hd hg hN
  have hh := weightedSweep_cost P (rootGraph P L C)
    (startContexts (copyPoints P L C).gates (P+L+C.gates.length) C.output) {C.output}
    (startContexts_unseenBot _ _ _)
  change (weightedSweep P (rootGraph P L C)
      (startContexts (copyPoints P L C).gates (P+L+C.gates.length) C.output)).gates.length +
      ({C.output} ∪ receivers (rootGraph P L C)).card ≤
      (copyPoints P L C).gates.length+1+edgeCost (rootGraph P L C) at hh
  have hv' : (positiveGates P L C).card + N.card ≤
      ({C.output} ∪ receivers (rootGraph P L C)).card := by simpa using hv
  unfold Circuit.size
  omega


def rootFormulas (P L : ℕ) (C : Circuit) : List (Formula (Fin P) (Fin L)) :=
  expandList C.gates (splitInitial P L)

def prefixFormulas (P L : ℕ) (C : Circuit) (j : ℕ) : List (Formula (Fin P) (Fin L)) :=
  expandList (C.gates.take j) (splitInitial P L)

lemma rootFormulas_degree (P L : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C) :
    (rootFormulas P L C).map Formula.degree = rootDegrees P L C := by
  rw [rootFormulas,degree_expandList _ _ hm,splitInitial_degree]
  rfl

lemma rootFormulas_eval (P L : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    (rootFormulas P L C).map (Formula.eval x y) = C.wires (List.ofFn x ++ List.ofFn y) := by
  rw [rootFormulas,eval_expandList _ _ hm,splitInitial_eval]
  rfl

lemma formulas_prefix (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) (i : ℕ)
    (hi : i < P+L+j.val) :
    (rootFormulas P L C).getD i .bot = (prefixFormulas P L C j.val).getD i .bot := by
  change (Reachability.scan (fun g fs => expandGate g fs) C.gates (splitInitial P L)).getD i .bot = _
  conv_lhs => rw [← List.take_append_drop j.val C.gates]
  rw [Reachability.scan_append]
  apply Reachability.scan_getD_old
  rw [Reachability.scan_length]
  simp only [splitInitial,List.length_append,List.length_ofFn,List.length_take]
  omega

lemma formulas_prefix_length (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) :
    (prefixFormulas P L C j.val).length = P+L+j.val := by
  change (Reachability.scan (fun g fs => expandGate g fs) (C.gates.take j.val) (splitInitial P L)).length = _
  rw [Reachability.scan_length]
  simp [splitInitial,Nat.min_eq_left (Nat.le_of_lt j.isLt)]

lemma formulas_gate (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) :
    (rootFormulas P L C).getD (P+L+j.val) .bot =
      expandGate (C.gates.get j) (prefixFormulas P L C j.val) := by
  have hh := Reachability.scan_getD_gate (fun g fs => expandGate g fs) C.gates (splitInitial P L) j Formula.bot
  simpa [Reachability.scan,rootFormulas,prefixFormulas,expandList,splitInitial] using hh

lemma formula_degree_at (P L : ℕ) (C : Circuit) (i : ℕ) (hm : IsMonotoneCircuit C) :
    ((rootFormulas P L C).getD i .bot).degree = (rootDegrees P L C).getD i 0 := by
  rw [← rootFormulas_degree P L C hm]
  exact (List.getD_map (l := rootFormulas P L C) (d := Formula.bot) (f := Formula.degree) (n := i)).symm

lemma prefix_formula_degree (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) (i : ℕ)
    (hm : IsMonotoneCircuit C) :
    ((prefixFormulas P L C j.val).getD i .bot).degree = edgeDegree P L C j.val i := by
  unfold edgeDegree
  split
  · rw [← formulas_prefix P L C j i ‹_›,formula_degree_at P L C i hm]
  · rw [List.getD_eq_default _ _ (by rw [formulas_prefix_length]; omega)]
    rfl

lemma edgePoint_value (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) (i : ℕ)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (x : Fin P → Bool) (hz : ((prefixFormulas P L C j.val).getD i .bot).degree = 0) :
    (edgePoint P L C j.val i).value (run (copyPoints P L C).gates (List.ofFn x)) =
      ((prefixFormulas P L C j.val).getD i .bot).eval x (fun _ => false) := by
  unfold edgePoint
  split
  · have hzi : (rootDegrees P L C).getD i 0 = 0 := by
      rw [prefix_formula_degree P L C j i hm] at hz
      simpa only [edgeDegree,if_pos ‹_›] using hz
    have ha := (copyPoints_agrees P L C hm hf (List.ofFn x) (by simp)).2 i hzi
    rw [← getD_map_values] at ha
    have he := List.getD_map (l := rootFormulas P L C) (d := Formula.bot)
      (f := Formula.eval x (fun _ => false)) (n := i)
    rw [rootFormulas_eval P L C hm] at he
    rw [← formulas_prefix P L C j i ‹_›]
    simp only [List.ofFn_const,Formula.eval] at he
    exact ha.trans he
  · rw [List.getD_eq_default _ _ (by rw [formulas_prefix_length]; omega)]
    rfl


def finalState (P L : ℕ) (C : Circuit) : State :=
  weightedSweep P (rootGraph P L C)
    (startContexts (copyPoints P L C).gates (P+L+C.gates.length) C.output)

lemma root_local_equation (P L : ℕ) (C : Circuit) (j : Fin C.gates.length)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : (rootDegrees P L C).getD (P+L+j.val) 0 ≤ 1)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ((rootFormulas P L C).getD (P+L+j.val) .bot).contribution x y =
      ReverseCut.weighted
        ((rootEdges P L C j.val (C.gates.get j)).map
          (fun e => (e.1,e.2.value (run (copyPoints P L C).gates (List.ofFn x)))))
        (fun i => ((rootFormulas P L C).getD i .bot).contribution x y) := by
  have hdeg : (expandGate (C.gates.get j) (prefixFormulas P L C j.val)).degree ≤ 1 := by
    rw [← formulas_gate,formula_degree_at P L C _ hm]
    exact hd
  have hh := localEdges_equation (C.gates.get j) (prefixFormulas P L C j.val)
    (edgePoint P L C j.val) (run (copyPoints P L C).gates (List.ofFn x)) x y
    (hm _ (List.get_mem _ _)) (hf _ (List.get_mem _ _)) hdeg
    (fun i hz => edgePoint_value P L C j i hm hf x hz)
  have he : (fun i => ((prefixFormulas P L C j.val).getD i .bot).degree) =
      edgeDegree P L C j.val := by
    funext i
    exact prefix_formula_degree P L C j i hm
  simp only [List.getD] at he
  rw [he] at hh
  rw [formulas_gate]
  change _ = ReverseCut.weighted _ _ at hh
  rw [hh]
  unfold rootEdges
  have hc : ∀ es : List (ℕ × Ref),
      (∀ e ∈ es, e ∈ localEdges (C.gates.get j) (edgeDegree P L C j.val) (edgePoint P L C j.val)) →
      ReverseCut.weighted (es.map (fun e => (e.1,e.2.value (run (copyPoints P L C).gates (List.ofFn x)))))
        (fun i => ((prefixFormulas P L C j.val).getD i .bot).contribution x y) =
      ReverseCut.weighted (es.map (fun e => (e.1,e.2.value (run (copyPoints P L C).gates (List.ofFn x)))))
        (fun i => ((rootFormulas P L C).getD i .bot).contribution x y) := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons e es ih =>
      intro hmem
      have hm' := (rootEdges_mem P L C j e.1 hm hf hd).mp ⟨e.2,hmem e (by simp)⟩
      simp only [List.map_cons,ReverseCut.weighted,List.foldr_cons]
      rw [← formulas_prefix P L C j e.1 hm'.2.1]
      congr 1
      exact ih (fun a ha => hmem a (by simp [ha]))
  exact hc _ (fun _ h => h)


def rootEdgeList (P L : ℕ) (C : Circuit) : List (List (ℕ × Ref)) :=
  C.gates.zipIdx.map (fun (g,j) => rootEdges P L C j g)

lemma rootGraph_indexed (P L : ℕ) (C : Circuit) :
    rootGraph P L C = ((rootEdgeList P L C).zipIdx (P+L)).map (fun (es,j) => (j,es)) := by
  apply List.ext_getElem
  · simp [rootGraph,rootEdgeList]
  · intro i hi hj
    simp [rootGraph,rootEdgeList]

lemma root_semantic_transposition (P L : ℕ) (C : Circuit)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : HasLineDegree (P+L) (Finset.Ico P (P+L)) C 1)
    (hg : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Reachability.Edge C (P+L)) (P+L+j.val) C.output)
    (ho : C.output < P+L+C.gates.length) (x : Fin P → Bool) (y : Fin L → Bool) :
    (splitUnfold P L C).contribution x y =
      ReverseCut.active (P+L) (ctxValue (finalState P L C) (List.ofFn x))
        (fun i => ((rootFormulas P L C).getD i .bot).contribution x y) := by
  let s := startContexts (copyPoints P L C).gates (P+L+C.gates.length) C.output
  have hall : ∀ j : Fin C.gates.length, (rootDegrees P L C).getD (P+L+j.val) 0 ≤ 1 :=
    fun j => Reachability.reached_degree_le_one C (P+L) _ hd _ (hg j)
  have hh := weighted_transposition P (P+L) (rootEdgeList P L C) s (List.ofFn x)
    (by simp) (startContexts_valid _ _ _ _) ?_ ?_ ?_
    (fun i => ((rootFormulas P L C).getD i .bot).contribution x y) C.output
    (by simpa [rootEdgeList] using ho) (startContexts_ctxValue P _ _ _ _ ho) ?_
  · rw [← rootGraph_indexed] at hh
    exact hh
  · intro es hes e he
    obtain ⟨⟨g,j⟩,hj,rfl⟩ := List.mem_map.mp hes
    have hjl := List.snd_lt_of_mem_zipIdx hj
    have heq := List.fst_eq_of_mem_zipIdx hj
    change g = C.gates[j-0] at heq
    simp only [Nat.sub_zero] at heq
    have hv := rootEdges_valid P L C ⟨j,by simpa using hjl⟩ hm hf (hall ⟨j,by simpa using hjl⟩)
    rw [List.get_eq_getElem,← heq] at hv
    exact hv e he
  · intro k hk e he
    have hkl : k < C.gates.length := by simpa [rootEdgeList] using hk
    have hem : e ∈ rootEdges P L C k (C.gates.get ⟨k,hkl⟩) := by
      simpa [rootEdgeList] using he
    have hev := (rootEdges_mem P L C ⟨k,hkl⟩ e.1 hm hf (hall ⟨k,hkl⟩)).mp ⟨e.2,hem⟩
    exact hev.2.1
  · simp [s,startContexts,rootEdgeList]
  · intro k hk
    have hkl : k < C.gates.length := by simpa [rootEdgeList] using hk
    have hlocal := root_local_equation P L C ⟨k,hkl⟩ hm hf (hall ⟨k,hkl⟩) x y
    simpa [rootEdgeList,realizeEdges,s,startContexts] using hlocal


lemma rootFormula_input (P L : ℕ) (C : Circuit) (i : ℕ) (hi : i < P+L) :
    (rootFormulas P L C).getD i .bot = (splitInitial P L).getD i .bot := by
  apply Reachability.scan_getD_old (fun g fs => expandGate g fs) C.gates (splitInitial P L) i Formula.bot
  simpa [splitInitial] using hi

lemma input_point_contribution (P L : ℕ) (C : Circuit) (i : Fin P)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ((rootFormulas P L C).getD i.val .bot).contribution x y = false := by
  rw [rootFormula_input P L C i.val (by omega)]
  have he : (splitInitial P L).getD i.val .bot = Formula.point i := by
    rw [List.getD_eq_getElem _ _ (by simp only [splitInitial,List.length_append,List.length_ofFn]; omega)]
    simp [splitInitial]
  rw [he]
  simp [Formula.contribution,Formula.coeff]

lemma input_line_contribution (P L : ℕ) (C : Circuit) (i : Fin L)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ((rootFormulas P L C).getD (P+i.val) .bot).contribution x y = y i := by
  rw [rootFormula_input P L C (P+i.val) (by omega)]
  have he : (splitInitial P L).getD (P+i.val) .bot = Formula.line i := by
    rw [List.getD_eq_getElem _ _ (by simp only [splitInitial,List.length_append,List.length_ofFn]; omega)]
    simp [splitInitial]
  rw [he]
  simp [Formula.contribution,Formula.coeff]

lemma active_inputs (P L : ℕ) (C : Circuit) (ctx : ℕ → Bool)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ReverseCut.active (P+L) ctx (fun i => ((rootFormulas P L C).getD i .bot).contribution x y) =
      decide (∃ u : Fin L, y u = true ∧ ctx (P+u.val) = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [ReverseCut.active,decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hc,hv⟩
    by_cases hip : i < P
    · rw [input_point_contribution P L C ⟨i,hip⟩ x y] at hv
      contradiction
    · have hil : i-P < L := by omega
      refine ⟨⟨i-P,hil⟩,?_,?_⟩
      · have he := input_line_contribution P L C ⟨i-P,hil⟩ x y
        have hie : P+(i-P) = i := by omega
        rw [hie] at he
        exact he.symm.trans hv
      · simpa [Nat.add_sub_of_le (Nat.le_of_not_lt hip)] using hc
  · rintro ⟨u,hy,hc⟩
    exact ⟨P+u.val,by omega,hc,by rw [input_line_contribution P L C u x y]; exact hy⟩


def resultCircuit (P L : ℕ) (C : Circuit) : Circuit := ⟨(finalState P L C).gates,0⟩
def resultTrue (P L : ℕ) (C : Circuit) : Finset (Fin L) :=
  Finset.univ.filter (fun i => (finalState P L C).refs.getD (P+i.val) .bot = .top)
def resultOutput (P L : ℕ) (C : Circuit) (i : Fin L) : ℕ :=
  match (finalState P L C).refs.getD (P+i.val) .bot with
  | .wire j => j
  | _ => P+(resultCircuit P L C).size

lemma result_extract (P L : ℕ) (C : Circuit) (i : Fin L) (x : Fin P → Bool) :
    ctxValue (finalState P L C) (List.ofFn x) (P+i.val) = true ↔
      (i ∈ resultTrue P L C ∨
        ((resultCircuit P L C).wires (List.ofFn x)).getD (resultOutput P L C i) false = true) := by
  unfold ctxValue resultTrue resultOutput
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hlen : ((resultCircuit P L C).wires (List.ofFn x)).length = P+(resultCircuit P L C).size := by
    exact (run_length (finalState P L C).gates (List.ofFn x)).trans (by simp [Circuit.size,resultCircuit])
  cases he : (finalState P L C).refs.getD (P+i.val) .bot with
  | bot =>
    simp only [Ref.value,reduceCtorEq,false_or,Bool.false_eq_true]
    rw [List.getD_eq_default _ _ (by omega)]
    simp
  | top => simp [Ref.value]
  | wire j => simp only [Ref.value,reduceCtorEq,false_or]; rfl

lemma final_semantics (P L : ℕ) (C : Circuit)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : HasLineDegree (P+L) (Finset.Ico P (P+L)) C 1)
    (hg : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Reachability.Edge C (P+L)) (P+L+j.val) C.output)
    (ho : C.output < P+L+C.gates.length) (x : Fin P → Bool) (y : Fin L → Bool) :
    C.eval (List.ofFn x ++ List.ofFn y) =
      (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) ||
        decide (∃ u : Fin L, y u = true ∧ (u ∈ resultTrue P L C ∨
          ((resultCircuit P L C).wires (List.ofFn x)).getD (resultOutput P L C u) false = true))) := by
  have hh := root_semantic_transposition P L C hm hf hd hg ho x y
  rw [active_inputs P L C _ x y] at hh
  have he := Formula.linearization (splitUnfold P L C)
    (by rw [splitUnfold_degree P L C hm]; exact hd) x y
  change _ = (_ || (splitUnfold P L C).contribution x y) at he
  rw [hh,splitUnfold_eval P L C hm,splitUnfold_eval P L C hm] at he
  rw [he]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  apply exists_congr
  intro u
  rw [result_extract P L C u x]

end Transposition738.Builder

namespace Transposition738.Partial
open PEqualNP.CircuitLowerBounds

theorem degree_zero_subcase (P L : ℕ) (C : Circuit) (N : Finset (Fin L))
    (hm : IsMonotoneCircuit C)
    (hd : C.lineDeg (P+L) (Finset.Ico P (P+L)) = 0)
    (hN : ∀ w : Fin L, w ∈ N ↔ Relation.ReflTransGen
      (fun r s : ℕ => r < s ∧ ∃ k : Fin C.gates.length,
        s = P+L+k.val ∧ r ∈ (C.gates.get k).inputs) (P+w.val) C.output) :
    ∃ (D : Circuit) (T : Finset (Fin L)) (o : Fin L → ℕ),
      IsMonotoneCircuit D ∧ (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧
      D.size + N.card ≤ C.size + 1 ∧
      ∀ (x : Fin P → Bool) (y : Fin L → Bool),
        C.eval (List.ofFn x ++ List.ofFn y) =
          (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) ||
            decide (∃ u : Fin L, y u = true ∧
              (u ∈ T ∨ (D.wires (List.ofFn x)).getD (o u) false = true))) := by
  have hn : N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    apply Reachability.no_reached_line_if_degree_zero C (P+L) (Finset.Ico P (P+L)) hd
      (P+w.val) (by omega) (by simp only [Finset.mem_Ico]; constructor <;> omega)
    exact (hN w).mp hw
  refine ⟨⟨[],0⟩,∅,fun _ => P,?_,?_,?_,?_⟩
  · simp [IsMonotoneCircuit]
  · simp
  · simp [Circuit.size, hn]
  · intro x y
    have hz : (Transposition738.splitUnfold P L C).degree = 0 := by
      rw [Transposition738.splitUnfold_degree P L C hm,hd]
    have he := Transposition738.Formula.eval_degree_zero _ hz x y (fun _ => false)
    rw [Transposition738.splitUnfold_eval P L C hm,
      Transposition738.splitUnfold_eval P L C hm] at he
    simpa [Circuit.wires, List.getD_eq_default] using he

end Transposition738.Partial

namespace Transposition738.Final
open PEqualNP.CircuitLowerBounds
open Transposition738.Builder

theorem transposition (P L : ℕ) (C : Circuit) (N : Finset (Fin L))
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hd : HasLineDegree (P+L) (Finset.Ico P (P+L)) C 1)
    (hg : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (fun a b : ℕ => a < b ∧ ∃ i : Fin C.gates.length,
        b = P+L+i.val ∧ a ∈ (C.gates.get i).inputs) (P+L+j.val) C.output)
    (hN : ∀ w : Fin L, w ∈ N ↔ Relation.ReflTransGen
      (fun r s : ℕ => r < s ∧ ∃ k : Fin C.gates.length,
        s = P+L+k.val ∧ r ∈ (C.gates.get k).inputs) (P+w.val) C.output) :
    ∃ (D : Circuit) (T : Finset (Fin L)) (o : Fin L → ℕ),
      IsMonotoneCircuit D ∧ (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧
      D.size + N.card ≤ C.size+1 ∧
      ∀ (x : Fin P → Bool) (y : Fin L → Bool),
        C.eval (List.ofFn x ++ List.ofFn y) =
          (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) ||
            decide (∃ u : Fin L, y u = true ∧
              (u ∈ T ∨ (D.wires (List.ofFn x)).getD (o u) false = true))) := by
  by_cases ho : C.output < P+L+C.gates.length
  · refine ⟨resultCircuit P L C,resultTrue P L C,resultOutput P L C,?_,?_,?_,?_⟩
    · exact (weightedSweep_good P (startContexts (copyPoints P L C).gates (P+L+C.gates.length) C.output)
        (rootGraph P L C) (good_copyPoints P L C)).1
    · exact (weightedSweep_good P (startContexts (copyPoints P L C).gates (P+L+C.gates.length) C.output)
        (rootGraph P L C) (good_copyPoints P L C)).2
    · exact root_transposition_size P L C N hm hf hd hg hN
    · exact final_semantics P L C hm hf hd hg ho
  · apply Transposition738.Partial.degree_zero_subcase P L C N hm
    · unfold Circuit.lineDeg
      exact List.getD_eq_default _ _ (by rw [Reachability.lineDegrees_length]; omega)
    · exact hN

end Transposition738.Final

namespace Transposition738.ExactAudit

theorem exact_posted_statement : ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) := Transposition738.Final.transposition

end Transposition738.ExactAudit

