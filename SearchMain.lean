import RawSearch

open CollatzFiniteWitness.RawSearch

private def report (code : Nat) : IO Unit := do
  IO.println s!"ACCEPTED_INDEX={code}"
  IO.println s!"RAW_WITNESS={repr (candidate code)}"
  IO.println "NEXT=Recheck this exact index in a theorem using by decide; audit its dependencies."
  IO.println "NATIVE_SEARCH_OUTPUT_IS_NOT_A_KERNEL_PROOF"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", raw] =>
      match raw.toNat? with
      | none =>
          IO.eprintln "Expected a natural-number search index."
          return 2
      | some code =>
          if checkCode code then
            report code
          else
            IO.println s!"REJECTED_INDEX={code}"
          return 0
  | ["search", raw] =>
      match raw.toNat? with
      | none =>
          IO.eprintln "Expected a natural-number exclusive bound."
          return 2
      | some bound =>
          match findAccepted bound with
          | none => IO.println s!"NO_ACCEPTED_INDEX_BELOW={bound}"
          | some code => report code
          return 0
  | _ =>
      IO.println "Usage: lean --run SearchMain.lean check INDEX"
      IO.println "       lean --run SearchMain.lean search EXCLUSIVE_BOUND"
      IO.println "Reference codec: exhaustive and terminating; not optimized for large codes."
      IO.println "No accepted global certificate is included."
      return if args.isEmpty then 0 else 2
