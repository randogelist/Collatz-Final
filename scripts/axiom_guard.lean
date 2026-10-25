
/- This guard is appended to a freshly generated module that imports every
project module and prints every configured endpoint's axioms. It rejects
unknown constants and every axiom outside Lean's explicit foundational list. -/
open Lean Elab Command in
run_cmd do
  let contents ← liftIO <| IO.FS.readFile "scripts/audit_endpoints.txt"
  let mut checked : Nat := 0
  let mut seen : Array Name := #[]
  for raw in contents.splitOn "\n" do
    let line := raw.trimAscii.toString
    unless line.isEmpty || line.startsWith "#" do
      let endpoint := line.toName
      unless (← getEnv).contains endpoint do
        throwError "AXIOM_AUDIT_UNKNOWN_ENDPOINT: {endpoint}"
      if seen.contains endpoint then
        throwError "AXIOM_AUDIT_DUPLICATE_ENDPOINT: {endpoint}"
      seen := seen.push endpoint
      let axioms ← Lean.collectAxioms endpoint
      for axiomName in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "AXIOM_AUDIT_REJECTED: {endpoint} depends on {axiomName}"
      checked := checked + 1
  if checked == 0 then
    throwError "AXIOM_AUDIT_EMPTY_ENDPOINT_LIST"
  logInfo m!"AXIOM_WHITELIST_PASS: {checked} endpoints; allowed propext Classical.choice Quot.sound"
