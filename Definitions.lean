import Lean.Elab.Tactic.Omega

/-
Exact mixed binary-ternary rewriting data.
Source: E. Yolcu, S. Aaronson, M. J. H. Heule,
An Automated Approach to the Collatz Conjecture, Section 3.2.
https://arxiv.org/pdf/2105.14697
DOI: 10.1007/s10817-022-09658-8

The source supplies the encoding. Its arithmetic simulation and the
certificate implication are proved in this package from natural arithmetic.
-/

namespace CollatzFiniteWitness

inductive Symbol where
  | L | R | f | t | zero | one | two
  deriving DecidableEq, Repr

abbrev Word := List Symbol

inductive RuleId where
  | even | odd | f0 | f1 | f2 | t0 | t1 | t2 | L0 | L1 | L2
  deriving DecidableEq, Repr

def lhs : RuleId → Word
  | .even => [.f, .R]
  | .odd => [.t, .R]
  | .f0 => [.f, .zero]
  | .f1 => [.f, .one]
  | .f2 => [.f, .two]
  | .t0 => [.t, .zero]
  | .t1 => [.t, .one]
  | .t2 => [.t, .two]
  | .L0 => [.L, .zero]
  | .L1 => [.L, .one]
  | .L2 => [.L, .two]

def rhs : RuleId → Word
  | .even => [.R]
  | .odd => [.two, .R]
  | .f0 => [.zero, .f]
  | .f1 => [.zero, .t]
  | .f2 => [.one, .f]
  | .t0 => [.one, .t]
  | .t1 => [.two, .f]
  | .t2 => [.two, .t]
  | .L0 => [.L, .t]
  | .L1 => [.L, .f, .f]
  | .L2 => [.L, .f, .t]

def allSymbols : List Symbol := [.L, .R, .f, .t, .zero, .one, .two]

def allRules : List RuleId :=
  [.even, .odd, .f0, .f1, .f2, .t0, .t1, .t2, .L0, .L1, .L2]

theorem mem_allSymbols (s : Symbol) : s ∈ allSymbols := by
  cases s <;> simp [allSymbols]

theorem mem_allRules (r : RuleId) : r ∈ allRules := by
  cases r <;> simp [allRules]

/-- Semantic ranking interface, constructed from finite matrix checks. -/
structure Ranking where
  rank : Word → Nat
  weak : ∀ (r : RuleId) (p q : Word),
    rank (p ++ rhs r ++ q) ≤ rank (p ++ lhs r ++ q)
  odd_strict : ∀ (p q : Word),
    rank (p ++ rhs .odd ++ q) < rank (p ++ lhs .odd ++ q)

end CollatzFiniteWitness
