import CrownMain
import MatrixObstruction

/-!
A completely executable enumeration of the supplied natural matrix-certificate
language. Candidate witnesses contain only three natural numbers. This module
proves completeness for that certificate language, not a converse from Collatz.
-/

namespace CollatzFiniteWitness.RawSearch

/-- Triangular numbers, used only to prove the natural-number codec. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n + 1

/-- A diagonal enumeration of all ordered pairs of natural numbers. -/
def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | k + 1 =>
      match unpair k with
      | (a, 0) => (0, a + 1)
      | (a, b + 1) => (a + 1, b)

/-- The inverse code on a diagonal. -/
def pair (a b : Nat) : Nat := triangle (a + b) + a

theorem unpair_diagonal : ∀ s a : Nat, a ≤ s →
    unpair (triangle s + a) = (a, s - a) := by
  intro s
  induction s with
  | zero =>
      intro a ha
      have : a = 0 := by omega
      subst a
      rfl
  | succ s ih =>
      intro a ha
      induction a with
      | zero =>
          have hlast := ih s (Nat.le_refl s)
          have heq : triangle (s + 1) = triangle s + s + 1 := rfl
          simp only [Nat.add_zero]
          rw [heq, unpair, hlast]
          simp
      | succ a iha =>
          have ha' : a ≤ s := by omega
          have hprev := iha (by omega)
          have hsub : s + 1 - a = (s - a) + 1 := by omega
          rw [Nat.add_succ, unpair, hprev, hsub]
          simp

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  unfold pair
  have h := unpair_diagonal (a + b) a (by omega)
  simpa using h

/-- Serialize a finite natural table. -/
def encodeFin : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => pair (f 0) (encodeFin (fun i : Fin n => f i.succ))

/-- Decode exactly the requested number of entries; recursion is on its length. -/
def decodeFin : (n : Nat) → Nat → Fin n → Nat
  | 0, _, i => Fin.elim0 i
  | n + 1, code, i =>
      Fin.cases (unpair code).1
        (fun j => decodeFin n (unpair code).2 j) i

theorem decodeFin_encodeFin : ∀ {n : Nat} (f : Fin n → Nat),
    decodeFin n (encodeFin f) = f := by
  intro n
  induction n with
  | zero => intro f; funext i; exact Fin.elim0 i
  | succ n ih =>
      intro f
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [encodeFin, decodeFin, unpair_pair]
      · simp only [encodeFin, decodeFin, unpair_pair, Fin.cases_succ]
        exact congrFun (ih (fun j : Fin n => f j.succ)) j

/-- A fixed seven-symbol table; all entries remain raw natural data. -/
def symbolIndex : Symbol → Fin 7
  | .L => 0 | .R => 1 | .f => 2 | .t => 3
  | .zero => 4 | .one => 5 | .two => 6

def symbolAt (i : Fin 7) : Symbol :=
  match i.val with
  | 0 => .L | 1 => .R | 2 => .f | 3 => .t
  | 4 => .zero | 5 => .one | _ => .two

theorem symbolAt_index (s : Symbol) : symbolAt (symbolIndex s) = s := by
  cases s <;> rfl

/-- No proposition, proof, infinite table, or oracle is stored in a candidate.
The actual matrix dimension is `dimension + 2`; scalar candidates were proved
impossible in MatrixObstruction. -/
structure RawWitness where
  dimension : Nat
  matrixCode : Nat
  biasCode : Nat
  deriving Repr, DecidableEq

/-- Three nested finite decodings reconstruct the seven square matrices. -/
def RawWitness.decode (R : RawWitness) : Witness (R.dimension + 1) where
  matrix := fun s i j =>
    let a := decodeFin (R.dimension + 2)
      (decodeFin (R.dimension + 2)
        (decodeFin 7 R.matrixCode (symbolIndex s)) i) j
    if i = 0 ∧ j = 0 then a + 1 else a
  bias := fun s i =>
    decodeFin (R.dimension + 2)
      (decodeFin 7 R.biasCode (symbolIndex s)) i

/-- Exact serialization of every nonscalar original matrix witness. -/
def pack {d : Nat} (W : Witness (d + 1)) : RawWitness where
  dimension := d
  matrixCode := encodeFin (fun s : Fin 7 =>
    encodeFin (fun i : Fin (d + 2) =>
      encodeFin (fun j : Fin (d + 2) =>
        if i = 0 ∧ j = 0 then W.matrix (symbolAt s) i j - 1
        else W.matrix (symbolAt s) i j)))
  biasCode := encodeFin (fun s : Fin 7 =>
    encodeFin (fun i : Fin (d + 2) => W.bias (symbolAt s) i))

theorem decode_pack {d : Nat} (W : Witness (d + 1)) (h : check W = true) :
    (pack W).decode = W := by
  cases W with
  | mk matrix bias =>
      dsimp only [pack, RawWitness.decode]
      simp only [decodeFin_encodeFin, symbolAt_index]
      congr 1
      funext s i j
      by_cases hij : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hij
        have hp := (check_sound (Witness.mk matrix bias) h).positive s
        change 1 ≤ matrix s 0 0 at hp
        simp [Nat.sub_add_cancel hp]
      · simp [hij]

/-- All seven required positive entries are normalized by construction. -/
theorem DECODE_POSITIVE_ENTRIES (R : RawWitness) (s : Symbol) :
    1 ≤ R.decode.matrix s 0 0 := by
  simp [RawWitness.decode]

/-- One natural number serializes all three raw fields. -/
def RawWitness.code (R : RawWitness) : Nat :=
  pair R.dimension (pair R.matrixCode R.biasCode)

/-- Enumerating n=0,1,2,... exhausts the raw data space. -/
def candidate (n : Nat) : RawWitness :=
  ⟨(unpair n).1, (unpair (unpair n).2).1, (unpair (unpair n).2).2⟩

theorem candidate_code (R : RawWitness) : candidate R.code = R := by
  cases R
  simp [candidate, RawWitness.code, unpair_pair]

/-- Surjectivity is the precise countability/exhaustiveness theorem. -/
theorem COUNTABLE_RAW_SEARCH (R : RawWitness) : ∃ n : Nat, candidate n = R :=
  ⟨R.code, candidate_code R⟩

/-- A necessary off-diagonal coupling in one of the three critical symbols. -/
def FirstRowCoupled {d : Nat} (W : Witness d) : Prop :=
  ∃ j : Fin (d + 1), j ≠ 0 ∧
    (0 < W.matrix .L 0 j ∨ 0 < W.matrix .t 0 j ∨ 0 < W.matrix .two 0 j)

instance firstRowCoupledDecidable {d : Nat} (W : Witness d) :
    Decidable (FirstRowCoupled W) := by
  unfold FirstRowCoupled
  infer_instance

/-- Cheap finite guard; all-scalar first rows have already been ruled out. -/
def couplingGuard {d : Nat} (W : Witness d) : Bool := decide (FirstRowCoupled W)

theorem accepted_coupling_guard {d : Nat} (W : Witness d) (h : check W = true) :
    couplingGuard W = true := by
  obtain ⟨s, hs, j, hj, hp⟩ := ACCEPTED_REQUIRES_FIRST_ROW_COUPLING W h
  have hcoupled : FirstRowCoupled W := by
    refine ⟨j, hj, ?_⟩
    rcases hs with rfl | rfl | rfl
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr hp)
  exact (decide_true_iff _).mpr hcoupled

/-- The coupling guard short-circuits a proved impossible infinite subfamily. -/
def reducedCheck {d : Nat} (W : Witness d) : Bool := couplingGuard W && check W

theorem REDUCED_CHECK_EQ_ORIGINAL {d : Nat} (W : Witness d) :
    reducedCheck W = check W := by
  cases h : check W with
  | false => simp [reducedCheck, h]
  | true => simp [reducedCheck, h, accepted_coupling_guard W h]

/-- Total terminating Boolean test on a single natural-number search index. -/
def checkCode (n : Nat) : Bool := reducedCheck (candidate n).decode

theorem checkCode_eq_original (n : Nat) : checkCode n = check (candidate n).decode :=
  REDUCED_CHECK_EQ_ORIGINAL _

/-- A successful indexed test proves ordinary, unshortened Collatz. -/
theorem CHECK_CODE_SOUND (n : Nat) (h : checkCode n = true) : Collatz :=
  CHECKER_SOUND (candidate n).decode ((checkCode_eq_original n).symm.trans h)

/-- Every accepted original certificate survives the normalization and pruning. -/
theorem ORIGINAL_WITNESS_COVERED {d : Nat} (W : Witness (d + 1))
    (h : check W = true) : checkCode (pack W).code = true := by
  unfold checkCode
  rw [candidate_code]
  rw [decode_pack W h]
  exact (REDUCED_CHECK_EQ_ORIGINAL W).trans h

/-- Completeness is for the specified finite witness language only. -/
theorem INDEXED_SEARCH_IFF_ORIGINAL_ACCEPTANCE :
    (∃ n : Nat, checkCode n = true) ↔
      (∃ d : Nat, ∃ W : Witness d, check W = true) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(candidate n).dimension + 1, (candidate n).decode,
      (checkCode_eq_original n).symm.trans hn⟩
  · intro h
    obtain ⟨d, W, hW⟩ := ACCEPTED_EXISTS_IFF_POSITIVE_DIMENSION.mp h
    exact ⟨(pack W).code, ORIGINAL_WITNESS_COVERED W hW⟩

/-- An accepted search index is sufficient; existence remains open. -/
theorem INDEXED_SEARCH_IMPLIES_COLLATZ
    (h : ∃ n : Nat, checkCode n = true) : Collatz := by
  obtain ⟨n, hn⟩ := h
  exact CHECK_CODE_SOUND n hn

/-- Different raw candidates have different natural codes. -/
theorem raw_code_injective {R S : RawWitness} (h : R.code = S.code) : R = S := by
  have he := congrArg candidate h
  simpa only [candidate_code] using he

/-- The enumerated raw search space has arbitrarily large dimensions. -/
theorem RAW_SEARCH_DIMENSIONS_UNBOUNDED (d : Nat) :
    (candidate (RawWitness.code ⟨d, 0, 0⟩)).dimension = d := by
  rw [candidate_code]

/-- A finite run checks the indices below its bound, stopping at a success. -/
def findAccepted : Nat → Option Nat
  | 0 => none
  | bound + 1 => if checkCode bound then some bound else findAccepted bound

/-- Every reported finite-search success is an actual checked certificate. -/
theorem BOUNDED_SEARCH_SOUND {bound code : Nat}
    (h : findAccepted bound = some code) : code < bound ∧ checkCode code = true := by
  induction bound with
  | zero => simp [findAccepted] at h
  | succ bound ih =>
      cases hc : checkCode bound with
      | false =>
          have hprev : findAccepted bound = some code := by
            simpa [findAccepted, hc] using h
          obtain ⟨hlt, hcheck⟩ := ih hprev
          exact ⟨by omega, hcheck⟩
      | true =>
          have heq : bound = code := by simpa [findAccepted, hc] using h
          subst code
          exact ⟨by omega, hc⟩

/-- Every accepted index is found by a sufficiently long finite run. -/
theorem ACCEPTED_INDEX_EVENTUALLY_FOUND (code : Nat) (h : checkCode code = true) :
    findAccepted (code + 1) = some code := by
  simp [findAccepted, h]

/-- The countable search halts exactly when this certificate language has a witness. -/
theorem SEARCH_SUCCESS_IFF_ORIGINAL_ACCEPTANCE :
    (∃ bound code : Nat, findAccepted bound = some code) ↔
      (∃ d : Nat, ∃ W : Witness d, check W = true) := by
  rw [← INDEXED_SEARCH_IFF_ORIGINAL_ACCEPTANCE]
  constructor
  · rintro ⟨bound, code, h⟩
    exact ⟨code, (BOUNDED_SEARCH_SOUND h).2⟩
  · rintro ⟨code, h⟩
    exact ⟨code + 1, code, ACCEPTED_INDEX_EVENTUALLY_FOUND code h⟩

end CollatzFiniteWitness.RawSearch

#print axioms CollatzFiniteWitness.RawSearch.unpair_pair
#print axioms CollatzFiniteWitness.RawSearch.decode_pack
#print axioms CollatzFiniteWitness.RawSearch.COUNTABLE_RAW_SEARCH
#print axioms CollatzFiniteWitness.RawSearch.INDEXED_SEARCH_IFF_ORIGINAL_ACCEPTANCE
#print axioms CollatzFiniteWitness.RawSearch.CHECK_CODE_SOUND
#print axioms CollatzFiniteWitness.RawSearch.BOUNDED_SEARCH_SOUND
#print axioms CollatzFiniteWitness.RawSearch.SEARCH_SUCCESS_IFF_ORIGINAL_ACCEPTANCE


#print axioms CollatzFiniteWitness.RawSearch.REDUCED_CHECK_EQ_ORIGINAL

#print axioms CollatzFiniteWitness.RawSearch.DECODE_POSITIVE_ENTRIES
