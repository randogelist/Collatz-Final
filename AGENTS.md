# Execution policy

The user requires all Lean compilation and validation to run exclusively on
the GitHub Actions CI runner. Do not install or invoke Lean, Lake, elan,
`scripts/build.py`, `scripts/test_axiom_guard.py`, `run.cmd`, or Lean-backed
search/tests in the assistant's local environment. Local source inspection,
editing, static checks, and Git operations are allowed.

Push changes to GitHub and inspect the workflow result and logs for the exact
commit. Report compilation and axiom-audit success only when the runner's
evidence supports it. If CI is unavailable, report the blocker instead of
falling back to local compilation.

Keep the distinction between a sound conditional certificate theorem and an
accepted concrete witness. No accepted witness or Collatz-to-certificate
converse is currently proved.
