import Definitions

namespace CollatzFiniteWitness

/- Finite natural-number sums, with no algebra or matrix library dependency. -/
def finSum : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + finSum (fun i : Fin n => f i.succ)

theorem finSum_congr : ∀ {n : Nat} (f g : Fin n → Nat),
    (∀ i, f i = g i) → finSum f = finSum g := by
  intro n
  induction n with
  | zero => intro f g h; rfl
  | succ n ih =>
    intro f g h
    change f 0 + finSum (fun i : Fin n => f i.succ) =
      g 0 + finSum (fun i : Fin n => g i.succ)
    rw [h 0, ih _ _ (fun i => h i.succ)]

theorem finSum_zero : ∀ n : Nat, finSum (fun _ : Fin n => 0) = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change 0 + finSum (fun _ : Fin n => 0) = 0
    rw [ih]

theorem finSum_add : ∀ {n : Nat} (f g : Fin n → Nat),
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  intro n
  induction n with
  | zero => intro f g; rfl
  | succ n ih =>
    intro f g
    change (f 0 + g 0) + finSum (fun i : Fin n => f i.succ + g i.succ) =
      (f 0 + finSum (fun i : Fin n => f i.succ)) +
      (g 0 + finSum (fun i : Fin n => g i.succ))
    rw [ih]
    omega

theorem finSum_mul_right : ∀ {n : Nat} (f : Fin n → Nat) (c : Nat),
    finSum (fun i => f i * c) = finSum f * c := by
  intro n
  induction n with
  | zero => intro f c; simp [finSum]
  | succ n ih =>
    intro f c
    change f 0 * c + finSum (fun i : Fin n => f i.succ * c) =
      (f 0 + finSum (fun i : Fin n => f i.succ)) * c
    rw [ih, Nat.add_mul]

theorem finSum_mul_left : ∀ {n : Nat} (c : Nat) (f : Fin n → Nat),
    finSum (fun i => c * f i) = c * finSum f := by
  intro n
  induction n with
  | zero => intro c f; simp [finSum]
  | succ n ih =>
    intro c f
    change c * f 0 + finSum (fun i : Fin n => c * f i.succ) =
      c * (f 0 + finSum (fun i : Fin n => f i.succ))
    rw [ih, Nat.mul_add]

theorem finSum_le : ∀ {n : Nat} (f g : Fin n → Nat),
    (∀ i, f i ≤ g i) → finSum f ≤ finSum g := by
  intro n
  induction n with
  | zero => intro f g h; exact Nat.le_refl 0
  | succ n ih =>
    intro f g h
    exact Nat.add_le_add (h 0) (ih _ _ (fun i => h i.succ))

theorem finSum_swap : ∀ {m : Nat} {n : Nat} (f : Fin m → Fin n → Nat),
    finSum (fun i => finSum (fun j => f i j)) =
      finSum (fun j => finSum (fun i => f i j)) := by
  intro m
  induction m with
  | zero =>
    intro n f
    change 0 = finSum (fun _ : Fin n => 0)
    exact (finSum_zero n).symm
  | succ m ih =>
    intro n f
    change finSum (fun j => f 0 j) +
        finSum (fun i : Fin m => finSum (fun j => f i.succ j)) =
      finSum (fun j => f 0 j + finSum (fun i : Fin m => f i.succ j))
    rw [ih (fun i j => f i.succ j), finSum_add]

theorem fin_succ_ne_zero {n : Nat} (i : Fin n) :
    i.succ ≠ (0 : Fin (n + 1)) := by
  intro h
  have hv := congrArg Fin.val h
  change i.val + 1 = 0 at hv
  omega

theorem fin_succ_injective {n : Nat} {i j : Fin n}
    (h : i.succ = j.succ) : i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change i.val + 1 = j.val + 1 at hv
  omega

theorem finSum_select : ∀ {n : Nat} (i : Fin n) (x : Fin n → Nat),
    finSum (fun j => if i = j then x j else 0) = x i := by
  intro n
  induction n with
  | zero => intro i x; exact Fin.elim0 i
  | succ n ih =>
    intro i x
    refine Fin.cases ?_ (fun k => ?_) i
    · change (if (0 : Fin (n + 1)) = 0 then x 0 else 0) +
        finSum (fun j : Fin n =>
          if (0 : Fin (n + 1)) = j.succ then x j.succ else 0) = x 0
      rw [if_pos rfl]
      have ht : finSum (fun j : Fin n =>
          if (0 : Fin (n + 1)) = j.succ then x j.succ else 0) = 0 := by
        calc
          _ = finSum (fun _ : Fin n => 0) := by
            apply finSum_congr
            intro j
            exact if_neg (Ne.symm (fin_succ_ne_zero j))
          _ = 0 := finSum_zero n
      rw [ht, Nat.add_zero]
    · change (if k.succ = (0 : Fin (n + 1)) then x 0 else 0) +
        finSum (fun j : Fin n => if k.succ = j.succ then x j.succ else 0) =
        x k.succ
      rw [if_neg (fin_succ_ne_zero k), Nat.zero_add]
      calc
        _ = finSum (fun j : Fin n => if k = j then x j.succ else 0) := by
          apply finSum_congr
          intro j
          by_cases h : k = j
          · subst j; simp
          · have hs : k.succ ≠ j.succ := fun he => h (fin_succ_injective he)
            rw [if_neg hs, if_neg h]
        _ = x k.succ := ih k (fun j => x j.succ)

abbrev Vec (n : Nat) := Fin n → Nat
abbrev Mat (n : Nat) := Fin n → Fin n → Nat

structure Affine (n : Nat) where
  matrix : Mat n
  bias : Vec n

namespace Affine

def eval {n : Nat} (A : Affine n) (x : Vec n) : Vec n :=
  fun i => finSum (fun j => A.matrix i j * x j) + A.bias i

def identity (n : Nat) : Affine n where
  matrix := fun i j => if i = j then 1 else 0
  bias := fun _ => 0

def compose {n : Nat} (A B : Affine n) : Affine n where
  matrix := fun i j => finSum (fun k => A.matrix i k * B.matrix k j)
  bias := fun i => finSum (fun k => A.matrix i k * B.bias k) + A.bias i

theorem eval_identity {n : Nat} (x : Vec n) : (identity n).eval x = x := by
  funext i
  change finSum (fun j => (if i = j then 1 else 0) * x j) + 0 = x i
  rw [Nat.add_zero]
  calc
    _ = finSum (fun j => if i = j then x j else 0) := by
      apply finSum_congr
      intro j
      by_cases h : i = j <;> simp [h]
    _ = x i := finSum_select i x

theorem eval_compose {n : Nat} (A B : Affine n) (x : Vec n) :
    (compose A B).eval x = A.eval (B.eval x) := by
  funext i
  have hlin :
      finSum (fun j => finSum (fun k => A.matrix i k * B.matrix k j) * x j) =
      finSum (fun k => A.matrix i k * finSum (fun j => B.matrix k j * x j)) := by
    calc
      _ = finSum (fun j => finSum (fun k => (A.matrix i k * B.matrix k j) * x j)) := by
        apply finSum_congr
        intro j
        exact (finSum_mul_right (fun k => A.matrix i k * B.matrix k j) (x j)).symm
      _ = finSum (fun k => finSum (fun j => (A.matrix i k * B.matrix k j) * x j)) :=
        finSum_swap (fun j k => (A.matrix i k * B.matrix k j) * x j)
      _ = finSum (fun k => A.matrix i k * finSum (fun j => B.matrix k j * x j)) := by
        apply finSum_congr
        intro k
        calc
          _ = finSum (fun j => A.matrix i k * (B.matrix k j * x j)) := by
            apply finSum_congr
            intro j
            exact Nat.mul_assoc _ _ _
          _ = _ := finSum_mul_left _ _
  have hdist :
      finSum (fun k => A.matrix i k *
        (finSum (fun j => B.matrix k j * x j) + B.bias k)) =
      finSum (fun k => A.matrix i k * finSum (fun j => B.matrix k j * x j)) +
      finSum (fun k => A.matrix i k * B.bias k) := by
    calc
      _ = finSum (fun k =>
          A.matrix i k * finSum (fun j => B.matrix k j * x j) +
          A.matrix i k * B.bias k) := by
        apply finSum_congr
        intro k
        exact Nat.mul_add _ _ _
      _ = _ := finSum_add _ _
  change finSum (fun j => finSum (fun k => A.matrix i k * B.matrix k j) * x j) +
      (finSum (fun k => A.matrix i k * B.bias k) + A.bias i) =
    finSum (fun k => A.matrix i k *
      (finSum (fun j => B.matrix k j * x j) + B.bias k)) + A.bias i
  rw [hlin, hdist]
  omega

theorem eval_mono {n : Nat} (A : Affine n) {x y : Vec n}
    (h : ∀ i, x i ≤ y i) : ∀ i, A.eval x i ≤ A.eval y i := by
  intro i
  apply Nat.add_le_add_right
  apply finSum_le
  intro j
  exact Nat.mul_le_mul_left (A.matrix i j) (h j)

theorem eval_coeff_le {n : Nat} {A B : Affine n}
    (hm : ∀ i j, A.matrix i j ≤ B.matrix i j)
    (hb : ∀ i, A.bias i ≤ B.bias i) (x : Vec n) :
    ∀ i, A.eval x i ≤ B.eval x i := by
  intro i
  apply Nat.add_le_add _ (hb i)
  apply finSum_le
  intro j
  exact Nat.mul_le_mul_right (x j) (hm i j)

theorem eval_coeff_strict {d : Nat} {A B : Affine (d + 1)}
    (hm : ∀ i j, A.matrix i j ≤ B.matrix i j)
    (hb : A.bias 0 < B.bias 0) (x : Vec (d + 1)) :
    A.eval x 0 < B.eval x 0 := by
  have hs : finSum (fun j => A.matrix 0 j * x j) ≤
      finSum (fun j => B.matrix 0 j * x j) := by
    apply finSum_le
    intro j
    exact Nat.mul_le_mul_right (x j) (hm 0 j)
  change finSum (fun j => A.matrix 0 j * x j) + A.bias 0 <
    finSum (fun j => B.matrix 0 j * x j) + B.bias 0
  omega

theorem eval_strict {d : Nat} (A : Affine (d + 1))
    (ha : 1 ≤ A.matrix 0 0) {x y : Vec (d + 1)}
    (hxy : ∀ i, x i ≤ y i) (h0 : x 0 < y 0) :
    A.eval x 0 < A.eval y 0 := by
  have ht : finSum (fun j : Fin d => A.matrix 0 j.succ * x j.succ) ≤
      finSum (fun j : Fin d => A.matrix 0 j.succ * y j.succ) := by
    apply finSum_le
    intro j
    exact Nat.mul_le_mul_left (A.matrix 0 j.succ) (hxy j.succ)
  have hs : x 0 + 1 ≤ y 0 := by omega
  have hm := Nat.mul_le_mul_left (A.matrix 0 0) hs
  rw [Nat.mul_add, Nat.mul_one] at hm
  change (A.matrix 0 0 * x 0 +
      finSum (fun j : Fin d => A.matrix 0 j.succ * x j.succ)) + A.bias 0 <
    (A.matrix 0 0 * y 0 +
      finSum (fun j : Fin d => A.matrix 0 j.succ * y j.succ)) + A.bias 0
  omega

end Affine

/- Fully executable finite quantifiers, with soundness proved below. -/
theorem decide_true_iff (P : Prop) [inst : Decidable P] :
    decide P = true ↔ P := by
  cases inst with
  | isTrue hp =>
    constructor
    · intro h; exact hp
    · intro h; rfl
  | isFalse hp =>
    constructor
    · intro h; cases h
    · intro h; exact False.elim (hp h)

def allFin : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f 0 && allFin (fun i : Fin n => f i.succ)

theorem allFin_true : ∀ {n : Nat} (f : Fin n → Bool),
    allFin f = true ↔ ∀ i, f i = true := by
  intro n
  induction n with
  | zero =>
    intro f
    constructor
    · intro h i; exact Fin.elim0 i
    · intro h; rfl
  | succ n ih =>
    intro f
    change (f 0 && allFin (fun i : Fin n => f i.succ)) = true ↔ _
    rw [Bool.and_eq_true]
    constructor
    · intro h i
      exact Fin.cases h.1 (fun j => (ih _).mp h.2 j) i
    · intro h
      exact ⟨h 0, (ih _).mpr (fun j => h j.succ)⟩

def allList {α : Type} : List α → (α → Bool) → Bool
  | [], _ => true
  | a :: l, f => f a && allList l f

theorem allList_true {α : Type} (l : List α) (f : α → Bool) :
    allList l f = true ↔ ∀ a, a ∈ l → f a = true := by
  induction l with
  | nil => simp [allList]
  | cons a l ih =>
    simp only [allList, Bool.and_eq_true, ih, List.mem_cons]
    constructor
    · intro h b hb
      cases hb with
      | inl hb => subst b; exact h.1
      | inr hb => exact h.2 b hb
    · intro h
      exact ⟨h a (Or.inl rfl), fun b hb => h b (Or.inr hb)⟩

end CollatzFiniteWitness
