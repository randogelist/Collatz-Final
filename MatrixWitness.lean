import FiniteAlgebra

namespace CollatzFiniteWitness

/-- Explicit propositional interface for Boolean conjunction. -/
theorem bool_and_true_iff (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

/- The parameter d denotes actual matrix dimension d + 1. -/
structure Witness (d : Nat) where
  matrix : Symbol → Mat (d + 1)
  bias : Symbol → Vec (d + 1)

namespace Witness

def affine {d : Nat} (W : Witness d) (s : Symbol) : Affine (d + 1) :=
  ⟨W.matrix s, W.bias s⟩

/-- Exact finite matrix multiplication and vector addition for a word. -/
def compile {d : Nat} (W : Witness d) : Word → Affine (d + 1)
  | [] => Affine.identity (d + 1)
  | s :: w => Affine.compose (W.affine s) (W.compile w)

/-- Functional semantics: the leftmost symbol acts last. -/
def evalWord {d : Nat} (W : Witness d) : Word → Vec (d + 1) → Vec (d + 1)
  | [], x => x
  | s :: w, x => (W.affine s).eval (W.evalWord w x)

theorem eval_compile {d : Nat} (W : Witness d) (w : Word) (x : Vec (d + 1)) :
    (W.compile w).eval x = W.evalWord w x := by
  induction w with
  | nil => exact Affine.eval_identity x
  | cons s w ih =>
    change (Affine.compose (W.affine s) (W.compile w)).eval x =
      (W.affine s).eval (W.evalWord w x)
    rw [Affine.eval_compose, ih]

theorem evalWord_append {d : Nat} (W : Witness d) (p q : Word)
    (x : Vec (d + 1)) :
    W.evalWord (p ++ q) x = W.evalWord p (W.evalWord q x) := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    change (W.affine s).eval (W.evalWord (p ++ q) x) =
      (W.affine s).eval (W.evalWord p (W.evalWord q x))
    rw [ih]

theorem evalWord_mono {d : Nat} (W : Witness d) (p : Word)
    {x y : Vec (d + 1)} (h : ∀ i, x i ≤ y i) :
    ∀ i, W.evalWord p x i ≤ W.evalWord p y i := by
  induction p with
  | nil => exact h
  | cons s p ih =>
    exact Affine.eval_mono (W.affine s) ih

theorem evalWord_strict {d : Nat} (W : Witness d)
    (hpos : ∀ s, 1 ≤ W.matrix s 0 0) (p : Word)
    {x y : Vec (d + 1)} (hxy : ∀ i, x i ≤ y i) (h0 : x 0 < y 0) :
    W.evalWord p x 0 < W.evalWord p y 0 := by
  induction p with
  | nil => exact h0
  | cons s p ih =>
    exact Affine.eval_strict (W.affine s) (hpos s)
      (W.evalWord_mono p hxy) ih

end Witness

/-- Only finitely many natural-number coefficient inequalities occur here. -/
structure Check {d : Nat} (W : Witness d) : Prop where
  positive : ∀ s, 1 ≤ W.matrix s 0 0
  matrix : ∀ (r : RuleId) (i j : Fin (d + 1)),
    (W.compile (rhs r)).matrix i j ≤ (W.compile (lhs r)).matrix i j
  bias : ∀ (r : RuleId) (i : Fin (d + 1)),
    (W.compile (rhs r)).bias i ≤ (W.compile (lhs r)).bias i
  odd_strict : (W.compile (rhs .odd)).bias 0 < (W.compile (lhs .odd)).bias 0

/-- Executable checker. All enumeration bounds come from W's finite dimension. -/
def check {d : Nat} (W : Witness d) : Bool :=
  allList allSymbols (fun s => decide (1 ≤ W.matrix s 0 0)) &&
    (allList allRules (fun r =>
      allFin (fun i => allFin (fun j =>
        decide ((W.compile (rhs r)).matrix i j ≤ (W.compile (lhs r)).matrix i j))) &&
      allFin (fun i =>
        decide ((W.compile (rhs r)).bias i ≤ (W.compile (lhs r)).bias i))) &&
    decide ((W.compile (rhs .odd)).bias 0 < (W.compile (lhs .odd)).bias 0))

theorem check_sound {d : Nat} (W : Witness d) (h : check W = true) : Check W := by
  unfold check at h
  have hs := ((bool_and_true_iff _ _).mp h).1
  have hrest := ((bool_and_true_iff _ _).mp h).2
  have hr := ((bool_and_true_iff _ _).mp hrest).1
  have ho := ((bool_and_true_iff _ _).mp hrest).2
  have hsymbols := (allList_true _ _).mp hs
  have hrules := (allList_true _ _).mp hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact (decide_true_iff _).mp (hsymbols s (mem_allSymbols s))
  · intro r i j
    have hlocal := (bool_and_true_iff _ _).mp (hrules r (mem_allRules r))
    have hrow := (allFin_true _).mp hlocal.1 i
    exact (decide_true_iff _).mp ((allFin_true _).mp hrow j)
  · intro r i
    have hlocal := (bool_and_true_iff _ _).mp (hrules r (mem_allRules r))
    exact (decide_true_iff _).mp ((allFin_true _).mp hlocal.2 i)
  · exact (decide_true_iff _).mp ho

theorem check_complete {d : Nat} (W : Witness d) (h : Check W) : check W = true := by
  unfold check
  apply (bool_and_true_iff _ _).mpr
  constructor
  · apply (allList_true _ _).mpr
    intro s hs
    exact (decide_true_iff _).mpr (h.positive s)
  · apply (bool_and_true_iff _ _).mpr
    constructor
    · apply (allList_true _ _).mpr
      intro r hr
      apply (bool_and_true_iff _ _).mpr
      constructor
      · apply (allFin_true _).mpr
        intro i
        apply (allFin_true _).mpr
        intro j
        exact (decide_true_iff _).mpr (h.matrix r i j)
      · apply (allFin_true _).mpr
        intro i
        exact (decide_true_iff _).mpr (h.bias r i)
    · exact (decide_true_iff _).mpr h.odd_strict

theorem check_iff {d : Nat} (W : Witness d) : check W = true ↔ Check W :=
  ⟨check_sound W, check_complete W⟩

theorem local_rule_weak {d : Nat} (W : Witness d) (h : Check W)
    (r : RuleId) (x : Vec (d + 1)) :
    ∀ i, W.evalWord (rhs r) x i ≤ W.evalWord (lhs r) x i := by
  have hv := Affine.eval_coeff_le (h.matrix r) (h.bias r) x
  simpa only [Witness.eval_compile] using hv

theorem local_odd_strict {d : Nat} (W : Witness d) (h : Check W)
    (x : Vec (d + 1)) :
    W.evalWord (rhs .odd) x 0 < W.evalWord (lhs .odd) x 0 := by
  have hv := Affine.eval_coeff_strict (h.matrix .odd) h.odd_strict x
  simpa only [Witness.eval_compile] using hv

/-- Coefficient comparisons control every suffix and every prefix context. -/
def toRanking {d : Nat} (W : Witness d) (h : Check W) : Ranking where
  rank := fun w => W.evalWord w (fun _ => 0) 0
  weak := by
    intro r p q
    change W.evalWord (p ++ rhs r ++ q) (fun _ => 0) 0 ≤
      W.evalWord (p ++ lhs r ++ q) (fun _ => 0) 0
    simp only [W.evalWord_append]
    exact W.evalWord_mono p
      (local_rule_weak W h r (W.evalWord q (fun _ => 0))) 0
  odd_strict := by
    intro p q
    change W.evalWord (p ++ rhs .odd ++ q) (fun _ => 0) 0 <
      W.evalWord (p ++ lhs .odd ++ q) (fun _ => 0) 0
    simp only [W.evalWord_append]
    exact W.evalWord_strict h.positive p
      (local_rule_weak W h .odd (W.evalWord q (fun _ => 0)))
      (local_odd_strict W h (W.evalWord q (fun _ => 0)))

end CollatzFiniteWitness
