import Definitions

/-
Arithmetic coverage of the mixed binary-ternary rules.

Every positive natural has a binary numeral. Appending a ternary digit
is normalized by the nine auxiliary rules. The two dynamic rules then
implement the shortcut Collatz map exactly. Weak rank descent handles
even steps; strict descent handles odd steps. No trajectory-coverage or
termination assertion is assumed.
-/

namespace CollatzFiniteWitness

def T (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate f k (f n)

def ReachesOne (n : Nat) : Prop :=
  ∃ k : Nat, iterate T k n = 1

theorem reachesOne_one : ReachesOne 1 :=
  ⟨0, rfl⟩

theorem reachesOne_step {n : Nat} (h : ReachesOne (T n)) : ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, hk⟩

theorem T_even (n : Nat) : T (2 * n) = n := by
  unfold T
  split <;> omega

theorem T_odd (n : Nat) : T (2 * n + 1) = 3 * n + 2 := by
  unfold T
  split <;> omega

inductive Binary where
  | one
  | bit0 (b : Binary)
  | bit1 (b : Binary)
  deriving Repr

def binaryValue : Binary → Nat
  | .one => 1
  | .bit0 b => 2 * binaryValue b
  | .bit1 b => 2 * binaryValue b + 1

/-- The left marker supplies the leading binary one. -/
def binaryWord : Binary → Word
  | .one => [.L]
  | .bit0 b => binaryWord b ++ [.f]
  | .bit1 b => binaryWord b ++ [.t]

def closedWord (b : Binary) : Word := binaryWord b ++ [.R]

inductive TriDigit where
  | zero | one | two
  deriving Repr

def triValue : TriDigit → Nat
  | .zero => 0
  | .one => 1
  | .two => 2

def triSymbol : TriDigit → Symbol
  | .zero => .zero
  | .one => .one
  | .two => .two

/-- Normalize the value `3 * binaryValue b + triValue j`. -/
def normalize : Binary → TriDigit → Binary
  | .one, .zero => .bit1 .one
  | .one, .one => .bit0 (.bit0 .one)
  | .one, .two => .bit1 (.bit0 .one)
  | .bit0 b, .zero => .bit0 (normalize b .zero)
  | .bit0 b, .one => .bit1 (normalize b .zero)
  | .bit0 b, .two => .bit0 (normalize b .one)
  | .bit1 b, .zero => .bit1 (normalize b .one)
  | .bit1 b, .one => .bit0 (normalize b .two)
  | .bit1 b, .two => .bit1 (normalize b .two)

theorem normalize_value (b : Binary) (j : TriDigit) :
    binaryValue (normalize b j) = 3 * binaryValue b + triValue j := by
  induction b generalizing j with
  | one => cases j <;> rfl
  | bit0 b ih =>
      cases j <;>
        simp only [normalize, binaryValue, triValue] <;>
        rw [ih] <;>
        simp only [triValue] <;>
        omega
  | bit1 b ih =>
      cases j <;>
        simp only [normalize, binaryValue, triValue] <;>
        rw [ih] <;>
        simp only [triValue] <;>
        omega

/-- Each normalization is a finite sequence of the nine auxiliary rules. -/
theorem normalize_rank (ranking : Ranking) (b : Binary)
    (j : TriDigit) (q : Word) :
    ranking.rank (binaryWord (normalize b j) ++ q) ≤
      ranking.rank (binaryWord b ++ [triSymbol j] ++ q) := by
  induction b generalizing j q with
  | one =>
      cases j with
      | zero =>
          simpa [normalize, binaryWord, triSymbol, lhs, rhs, List.append_assoc]
            using ranking.weak .L0 [] q
      | one =>
          simpa [normalize, binaryWord, triSymbol, lhs, rhs, List.append_assoc]
            using ranking.weak .L1 [] q
      | two =>
          simpa [normalize, binaryWord, triSymbol, lhs, rhs, List.append_assoc]
            using ranking.weak .L2 [] q
  | bit0 b ih =>
      cases j with
      | zero =>
          have hn :
              ranking.rank (binaryWord (normalize b .zero) ++ (.f :: q)) ≤
                ranking.rank (binaryWord b ++ (.zero :: .f :: q)) := by
            simpa [triSymbol, List.append_assoc] using ih .zero (.f :: q)
          have hs :
              ranking.rank (binaryWord b ++ (.zero :: .f :: q)) ≤
                ranking.rank (binaryWord b ++ (.f :: .zero :: q)) := by
            simpa [lhs, rhs, List.append_assoc]
              using ranking.weak .f0 (binaryWord b) q
          simpa [normalize, binaryWord, triSymbol, List.append_assoc]
            using Nat.le_trans hn hs
      | one =>
          have hn :
              ranking.rank (binaryWord (normalize b .zero) ++ (.t :: q)) ≤
                ranking.rank (binaryWord b ++ (.zero :: .t :: q)) := by
            simpa [triSymbol, List.append_assoc] using ih .zero (.t :: q)
          have hs :
              ranking.rank (binaryWord b ++ (.zero :: .t :: q)) ≤
                ranking.rank (binaryWord b ++ (.f :: .one :: q)) := by
            simpa [lhs, rhs, List.append_assoc]
              using ranking.weak .f1 (binaryWord b) q
          simpa [normalize, binaryWord, triSymbol, List.append_assoc]
            using Nat.le_trans hn hs
      | two =>
          have hn :
              ranking.rank (binaryWord (normalize b .one) ++ (.f :: q)) ≤
                ranking.rank (binaryWord b ++ (.one :: .f :: q)) := by
            simpa [triSymbol, List.append_assoc] using ih .one (.f :: q)
          have hs :
              ranking.rank (binaryWord b ++ (.one :: .f :: q)) ≤
                ranking.rank (binaryWord b ++ (.f :: .two :: q)) := by
            simpa [lhs, rhs, List.append_assoc]
              using ranking.weak .f2 (binaryWord b) q
          simpa [normalize, binaryWord, triSymbol, List.append_assoc]
            using Nat.le_trans hn hs
  | bit1 b ih =>
      cases j with
      | zero =>
          have hn :
              ranking.rank (binaryWord (normalize b .one) ++ (.t :: q)) ≤
                ranking.rank (binaryWord b ++ (.one :: .t :: q)) := by
            simpa [triSymbol, List.append_assoc] using ih .one (.t :: q)
          have hs :
              ranking.rank (binaryWord b ++ (.one :: .t :: q)) ≤
                ranking.rank (binaryWord b ++ (.t :: .zero :: q)) := by
            simpa [lhs, rhs, List.append_assoc]
              using ranking.weak .t0 (binaryWord b) q
          simpa [normalize, binaryWord, triSymbol, List.append_assoc]
            using Nat.le_trans hn hs
      | one =>
          have hn :
              ranking.rank (binaryWord (normalize b .two) ++ (.f :: q)) ≤
                ranking.rank (binaryWord b ++ (.two :: .f :: q)) := by
            simpa [triSymbol, List.append_assoc] using ih .two (.f :: q)
          have hs :
              ranking.rank (binaryWord b ++ (.two :: .f :: q)) ≤
                ranking.rank (binaryWord b ++ (.t :: .one :: q)) := by
            simpa [lhs, rhs, List.append_assoc]
              using ranking.weak .t1 (binaryWord b) q
          simpa [normalize, binaryWord, triSymbol, List.append_assoc]
            using Nat.le_trans hn hs
      | two =>
          have hn :
              ranking.rank (binaryWord (normalize b .two) ++ (.t :: q)) ≤
                ranking.rank (binaryWord b ++ (.two :: .t :: q)) := by
            simpa [triSymbol, List.append_assoc] using ih .two (.t :: q)
          have hs :
              ranking.rank (binaryWord b ++ (.two :: .t :: q)) ≤
                ranking.rank (binaryWord b ++ (.t :: .two :: q)) := by
            simpa [lhs, rhs, List.append_assoc]
              using ranking.weak .t2 (binaryWord b) q
          simpa [normalize, binaryWord, triSymbol, List.append_assoc]
            using Nat.le_trans hn hs

theorem binary_even_rank (ranking : Ranking) (b : Binary) :
    ranking.rank (closedWord b) ≤ ranking.rank (closedWord (.bit0 b)) := by
  simpa [closedWord, binaryWord, lhs, rhs, List.append_assoc]
    using ranking.weak .even (binaryWord b) []

theorem binary_odd_rank (ranking : Ranking) (b : Binary) :
    ranking.rank (closedWord (normalize b .two)) <
      ranking.rank (closedWord (.bit1 b)) := by
  have hn := normalize_rank ranking b .two [.R]
  have hs := ranking.odd_strict (binaryWord b) []
  have hn' :
      ranking.rank (closedWord (normalize b .two)) ≤
        ranking.rank (binaryWord b ++ [.two, .R]) := by
    simpa [closedWord, triSymbol, List.append_assoc] using hn
  have hs' :
      ranking.rank (binaryWord b ++ [.two, .R]) <
        ranking.rank (closedWord (.bit1 b)) := by
    simpa [closedWord, binaryWord, lhs, rhs, List.append_assoc] using hs
  exact Nat.lt_of_le_of_lt hn' hs'

/-- Structural descent handles any finite stretch of even steps. -/
theorem ranking_reaches_binary (ranking : Ranking) :
    ∀ r : Nat, ∀ b : Binary,
      ranking.rank (closedWord b) ≤ r → ReachesOne (binaryValue b) := by
  intro r
  refine Nat.strongRecOn r ?_
  intro r ihr b
  induction b with
  | one =>
      intro _
      exact reachesOne_one
  | bit0 b ih =>
      intro hr
      have hb : ranking.rank (closedWord b) ≤ r :=
        Nat.le_trans (binary_even_rank ranking b) hr
      apply reachesOne_step
      simpa only [binaryValue, T_even] using ih hb
  | bit1 b ih =>
      intro hr
      have hc : ranking.rank (closedWord (normalize b .two)) < r :=
        Nat.lt_of_lt_of_le (binary_odd_rank ranking b) hr
      have hreach : ReachesOne (binaryValue (normalize b .two)) :=
        ihr (ranking.rank (closedWord (normalize b .two))) hc
          (normalize b .two) (Nat.le_refl _)
      apply reachesOne_step
      simpa only [binaryValue, T_odd, normalize_value, triValue] using hreach

/-- Binary numeral coverage, including the positive lower boundary. -/
theorem exists_binary (n : Nat) :
    0 < n → ∃ b : Binary, binaryValue b = n := by
  refine Nat.strongRecOn n ?_
  intro n ih hn
  by_cases h1 : n = 1
  · exact ⟨.one, h1.symm⟩
  · have hhalf : n / 2 < n := by omega
    have hpositive : 0 < n / 2 := by omega
    obtain ⟨b, hb⟩ := ih (n / 2) hhalf hpositive
    by_cases heven : n % 2 = 0
    · refine ⟨.bit0 b, ?_⟩
      simp only [binaryValue, hb]
      omega
    · refine ⟨.bit1 b, ?_⟩
      simp only [binaryValue, hb]
      omega

theorem ranking_implies_collatz (ranking : Ranking) :
    ∀ n : Nat, 0 < n → ∃ k : Nat, iterate T k n = 1 := by
  intro n hn
  obtain ⟨b, hb⟩ := exists_binary n hn
  have h := ranking_reaches_binary ranking
    (ranking.rank (closedWord b)) b (Nat.le_refl _)
  simpa only [ReachesOne, hb] using h

end CollatzFiniteWitness
