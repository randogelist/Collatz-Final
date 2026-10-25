import MatrixWitness

/-!
A symbolic obstruction to one-dimensional affine certificates.
Only the odd rule and L2 rule are needed. This excludes an entire infinite
family of coefficient assignments, rather than checking a finite sample.
-/

namespace CollatzFiniteWitness

private theorem scalar_odd_L2_obstruction
    (a b f t u bl br bf bt bu : Nat)
    (ha : 0 < a) (hb : 0 < b) (hf : 0 < f)
    (hoddMatrix : u * b ≤ t * b)
    (hL2Matrix : a * (f * t) ≤ a * u)
    (hL2Bias : a * (f * bt + bf) + bl ≤ a * bu + bl)
    (hoddBias : u * br + bu < t * br + bt) : False := by
  have hut : u ≤ t := Nat.le_of_mul_le_mul_right hoddMatrix hb
  have hftu : f * t ≤ u := Nat.le_of_mul_le_mul_left hL2Matrix ha
  have htft : t ≤ f * t := Nat.le_mul_of_pos_left t hf
  have htu : t ≤ u := Nat.le_trans htft hftu
  have heq : u = t := Nat.le_antisymm hut htu
  have hscaled : a * (f * bt + bf) ≤ a * bu := by omega
  have hraw : f * bt + bf ≤ bu := Nat.le_of_mul_le_mul_left hscaled ha
  have hbt : bt ≤ f * bt := Nat.le_mul_of_pos_left bt hf
  rw [heq] at hoddBias
  omega

/-- A symbol whose first output coordinate only depends on the first input. -/
def FirstRowScalar {d : Nat} (W : Witness d) (s : Symbol) : Prop :=
  ∀ j : Fin (d + 1), j ≠ 0 → W.matrix s 0 j = 0

private theorem isolated_row_sum {d : Nat} (a x : Vec (d + 1))
    (h : ∀ j : Fin (d + 1), j ≠ 0 → a j = 0) :
    finSum (fun j => a j * x j) = a 0 * x 0 := by
  calc
    _ = finSum (fun j => if (0 : Fin (d + 1)) = j then a j * x j else 0) := by
      apply finSum_congr
      intro j
      by_cases hj : j = 0
      · subst j
        simp
      · simp [h j hj, Ne.symm hj]
    _ = a 0 * x 0 := finSum_select 0 (fun j => a j * x j)

private theorem scalar_cons_matrix {d : Nat} (W : Witness d)
    (s : Symbol) (hs : FirstRowScalar W s) (w : Word) (j : Fin (d + 1)) :
    (W.compile (s :: w)).matrix 0 j =
      W.matrix s 0 0 * (W.compile w).matrix 0 j := by
  exact isolated_row_sum (W.matrix s 0) (fun i => (W.compile w).matrix i j) hs

private theorem scalar_cons_bias {d : Nat} (W : Witness d)
    (s : Symbol) (hs : FirstRowScalar W s) (w : Word) :
    (W.compile (s :: w)).bias 0 =
      W.matrix s 0 0 * (W.compile w).bias 0 + W.bias s 0 := by
  change finSum (fun i => W.matrix s 0 i * (W.compile w).bias i) + _ = _
  rw [isolated_row_sum (W.matrix s 0) (W.compile w).bias hs]
  rfl

private theorem singleton_matrix {d : Nat} (W : Witness d)
    (s : Symbol) (i j : Fin (d + 1)) :
    (W.compile [s]).matrix i j = W.matrix s i j := by
  change finSum (fun k => W.matrix s i k * (if k = j then 1 else 0)) = _
  calc
    _ = finSum (fun k => if j = k then W.matrix s i k else 0) := by
      apply finSum_congr
      intro k
      by_cases hk : k = j
      · subst k
        simp
      · simp [hk, Ne.symm hk]
    _ = W.matrix s i j := finSum_select j (W.matrix s i)

private theorem singleton_bias {d : Nat} (W : Witness d)
    (s : Symbol) (i : Fin (d + 1)) :
    (W.compile [s]).bias i = W.bias s i := by
  change finSum (fun k => W.matrix s i k * 0) + W.bias s i = _
  simp only [Nat.mul_zero, finSum_zero, Nat.zero_add]

private theorem cons_matrix_head_le {d : Nat} (W : Witness d)
    (s : Symbol) (w : Word) :
    W.matrix s 0 0 * (W.compile w).matrix 0 0 ≤
      (W.compile (s :: w)).matrix 0 0 := by
  change _ ≤ _ + finSum _
  exact Nat.le_add_right _ _

private theorem cons_bias_head_le {d : Nat} (W : Witness d)
    (s : Symbol) (w : Word) :
    W.matrix s 0 0 * (W.compile w).bias 0 + W.bias s 0 ≤
      (W.compile (s :: w)).bias 0 := by
  change _ ≤ (_ + finSum _) + _
  simp only [Witness.affine]
  omega

/-- Three isolated first rows already make the certificate impossible.
The other symbols, and every other matrix row, are unrestricted. -/
theorem THREE_SCALAR_ROWS_IMPOSSIBLE {d : Nat} (W : Witness d)
    (hL : FirstRowScalar W .L)
    (ht : FirstRowScalar W .t) (hu : FirstRowScalar W .two) : ¬ Check W := by
  intro h
  have hoddMatrix := h.matrix .odd 0 0
  have hL2Matrix := h.matrix .L2 0 0
  have hL2Bias := h.bias .L2 0
  have hoddBias := h.odd_strict
  simp only [rhs, lhs] at hoddMatrix hL2Matrix hL2Bias hoddBias
  rw [scalar_cons_matrix W .two hu, scalar_cons_matrix W .t ht,
    singleton_matrix] at hoddMatrix
  rw [scalar_cons_matrix W .L hL, scalar_cons_matrix W .L hL,
    singleton_matrix] at hL2Matrix
  rw [scalar_cons_bias W .L hL, scalar_cons_bias W .L hL,
    singleton_bias] at hL2Bias
  rw [scalar_cons_bias W .two hu, scalar_cons_bias W .t ht,
    singleton_bias] at hoddBias
  have hLpos : 0 < W.matrix .L 0 0 := by have := h.positive .L; omega
  have hM := Nat.le_of_mul_le_mul_left hL2Matrix hLpos
  have hB0 : W.matrix .L 0 0 * (W.compile [.f, .t]).bias 0 ≤
      W.matrix .L 0 0 * W.bias .two 0 := by omega
  have hB := Nat.le_of_mul_le_mul_left hB0 hLpos
  have hfM := cons_matrix_head_le W .f [.t]
  have hfB := cons_bias_head_le W .f [.t]
  rw [singleton_matrix] at hfM
  rw [singleton_bias] at hfB
  have hLM : W.matrix .L 0 0 * (W.matrix .f 0 0 * W.matrix .t 0 0) ≤
      W.matrix .L 0 0 * W.matrix .two 0 0 :=
    Nat.mul_le_mul_left _ (Nat.le_trans hfM hM)
  have hLB : W.matrix .L 0 0 * (W.matrix .f 0 0 * W.bias .t 0 + W.bias .f 0)
      + W.bias .L 0 ≤ W.matrix .L 0 0 * W.bias .two 0 + W.bias .L 0 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_trans hfB hB)) _
  exact scalar_odd_L2_obstruction
    (W.matrix .L 0 0) (W.matrix .R 0 0)
    (W.matrix .f 0 0) (W.matrix .t 0 0) (W.matrix .two 0 0)
    (W.bias .L 0) (W.bias .R 0) (W.bias .f 0)
    (W.bias .t 0) (W.bias .two 0)
    hLpos
    (by have := h.positive .R; omega)
    (by have := h.positive .f; omega)
    hoddMatrix hLM hLB hoddBias

/-- Every accepted witness needs a nonzero coupling into the ranking coordinate
from another coordinate, in at least one of these three specified symbols. -/
theorem ACCEPTED_REQUIRES_FIRST_ROW_COUPLING {d : Nat} (W : Witness d)
    (hW : check W = true) :
    ∃ s : Symbol, (s = .L ∨ s = .t ∨ s = .two) ∧
      ∃ j : Fin (d + 1), j ≠ 0 ∧ 0 < W.matrix s 0 j := by
  classical
  apply Classical.byContradiction
  intro hn
  have hscalar : ∀ s : Symbol,
      (s = .L ∨ s = .t ∨ s = .two) → FirstRowScalar W s := by
    intro s hs j hj
    have hnot : ¬ 0 < W.matrix s 0 j := by
      intro hp
      exact hn ⟨s, hs, j, hj, hp⟩
    omega
  exact THREE_SCALAR_ROWS_IMPOSSIBLE W
    (hscalar .L (Or.inl rfl))
    (hscalar .t (Or.inr (Or.inl rfl)))
    (hscalar .two (Or.inr (Or.inr rfl)))
    (check_sound W hW)

/-- No scalar affine interpretation can pass the matrix certificate rules. -/
theorem SCALAR_CHECK_IMPOSSIBLE (W : Witness 0) : ¬ Check W := by
  intro h
  have hoddMatrix := h.matrix .odd 0 0
  have hL2Matrix := h.matrix .L2 0 0
  have hL2Bias := h.bias .L2 0
  have hoddBias := h.odd_strict
  simp only [rhs, lhs, Witness.compile, Witness.affine,
    Affine.compose, Affine.identity, finSum, Nat.add_zero,
    Nat.mul_one, Nat.mul_zero, Nat.zero_add, ite_true] at hoddMatrix hL2Matrix hL2Bias hoddBias
  exact scalar_odd_L2_obstruction
    (W.matrix .L 0 0) (W.matrix .R 0 0)
    (W.matrix .f 0 0) (W.matrix .t 0 0) (W.matrix .two 0 0)
    (W.bias .L 0) (W.bias .R 0) (W.bias .f 0)
    (W.bias .t 0) (W.bias .two 0)
    (by have := h.positive .L; omega)
    (by have := h.positive .R; omega)
    (by have := h.positive .f; omega)
    hoddMatrix hL2Matrix hL2Bias hoddBias

/-- The executable checker rejects every scalar witness. -/
theorem SCALAR_CHECKER_REJECTS (W : Witness 0) : check W = false := by
  cases heq : check W with
  | false => rfl
  | true => exact False.elim (SCALAR_CHECK_IMPOSSIBLE W (check_sound W heq))

/-- Accepted certificates require actual matrix dimension at least two. -/
theorem ACCEPTED_DIMENSION_POSITIVE {d : Nat} (W : Witness d)
    (hW : check W = true) : 0 < d := by
  cases d with
  | zero => exact False.elim (SCALAR_CHECK_IMPOSSIBLE W (check_sound W hW))
  | succ d => exact Nat.zero_lt_succ d

/-- Removing scalar candidates preserves existence of accepted certificates. -/
theorem ACCEPTED_EXISTS_IFF_POSITIVE_DIMENSION :
    (∃ d : Nat, ∃ W : Witness d, check W = true) ↔
      (∃ d : Nat, ∃ W : Witness (d + 1), check W = true) := by
  constructor
  · rintro ⟨d, W, hW⟩
    cases d with
    | zero => exact False.elim (SCALAR_CHECK_IMPOSSIBLE W (check_sound W hW))
    | succ d => exact ⟨d, W, hW⟩
  · rintro ⟨d, W, hW⟩
    exact ⟨d + 1, W, hW⟩

end CollatzFiniteWitness

#print axioms CollatzFiniteWitness.SCALAR_CHECKER_REJECTS
#print axioms CollatzFiniteWitness.ACCEPTED_DIMENSION_POSITIVE
#print axioms CollatzFiniteWitness.ACCEPTED_EXISTS_IFF_POSITIVE_DIMENSION

#print axioms CollatzFiniteWitness.THREE_SCALAR_ROWS_IMPOSSIBLE
#print axioms CollatzFiniteWitness.ACCEPTED_REQUIRES_FIRST_ROW_COUPLING
