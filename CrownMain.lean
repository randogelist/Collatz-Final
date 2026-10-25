import MatrixWitness
import Dynamics

namespace CollatzFiniteWitness

/-- The unshortened Collatz map. -/
def C (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Every positive starting value reaches one under the unshortened map. -/
def Collatz : Prop :=
  ∀ n : Nat, 0 < n → ∃ k : Nat, iterate C k n = 1

/-- Every positive starting value reaches one under the shortcut map. -/
def ShortcutCollatz : Prop :=
  ∀ n : Nat, 0 < n → ∃ k : Nat, iterate T k n = 1

theorem full_iterate_add (f : Nat → Nat) (a b n : Nat) :
    iterate f (a + b) n = iterate f b (iterate f a n) := by
  induction a generalizing n with
  | zero => simp only [Nat.zero_add, iterate]
  | succ a ih =>
      simpa only [Nat.succ_add, iterate] using ih (f n)

theorem full_simulates_shortcut (n : Nat) :
    ∃ k : Nat, iterate C k n = T n := by
  by_cases h : n % 2 = 0
  · refine ⟨1, ?_⟩
    simp [iterate, C, T, h]
  · have hm : (3 * n + 1) % 2 = 0 := by omega
    refine ⟨2, ?_⟩
    simp [iterate, C, T, h, hm]

theorem full_simulates_shortcut_iterate (k n : Nat) :
    ∃ j : Nat, iterate C j n = iterate T k n := by
  induction k generalizing n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
      obtain ⟨a, ha⟩ := full_simulates_shortcut n
      obtain ⟨b, hb⟩ := ih (T n)
      refine ⟨a + b, ?_⟩
      calc
        iterate C (a + b) n = iterate C b (iterate C a n) :=
          full_iterate_add C a b n
        _ = iterate T k (T n) := by rw [ha, hb]
        _ = iterate T (Nat.succ k) n := rfl

theorem shortcut_implies_full (h : ShortcutCollatz) : Collatz := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  obtain ⟨j, hj⟩ := full_simulates_shortcut_iterate k n
  exact ⟨j, hj.trans hk⟩

/-- The symbolic finite inequalities imply actual shortcut Collatz. -/
theorem WITNESS_IMPLIES_SHORTCUT_COLLATZ {d : Nat}
    (W : Witness d) (h : Check W) : ShortcutCollatz :=
  ranking_implies_collatz (toRanking W h)

/-- The symbolic finite inequalities imply actual unshortened Collatz. -/
theorem WITNESS_IMPLIES_COLLATZ {d : Nat}
    (W : Witness d) (h : Check W) : Collatz :=
  shortcut_implies_full (WITNESS_IMPLIES_SHORTCUT_COLLATZ W h)

/-- Acceptance by the executable Boolean checker implies Collatz. -/
theorem CHECKER_SOUND {d : Nat}
    (W : Witness d) (h : check W = true) : Collatz :=
  WITNESS_IMPLIES_COLLATZ W (check_sound W h)

/-- A single finite accepted matrix witness suffices. -/
theorem FINITE_WITNESS_IMPLIES_COLLATZ
    (h : ∃ d : Nat, ∃ W : Witness d, check W = true) : Collatz := by
  obtain ⟨d, W, hW⟩ := h
  exact CHECKER_SOUND W hW

end CollatzFiniteWitness

#print CollatzFiniteWitness.C
#print CollatzFiniteWitness.Collatz
#check CollatzFiniteWitness.WITNESS_IMPLIES_SHORTCUT_COLLATZ
#check CollatzFiniteWitness.WITNESS_IMPLIES_COLLATZ
#check CollatzFiniteWitness.CHECKER_SOUND
#check CollatzFiniteWitness.FINITE_WITNESS_IMPLIES_COLLATZ
#print axioms CollatzFiniteWitness.WITNESS_IMPLIES_SHORTCUT_COLLATZ
#print axioms CollatzFiniteWitness.WITNESS_IMPLIES_COLLATZ
#print axioms CollatzFiniteWitness.CHECKER_SOUND
#print axioms CollatzFiniteWitness.FINITE_WITNESS_IMPLIES_COLLATZ
