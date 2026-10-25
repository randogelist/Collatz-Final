#!/usr/bin/env python3
"""Exercise the audit guard's accept/reject paths; performs no witness search."""
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TEMP = ROOT / ".build/guard-selftest"
(TEMP / "scripts").mkdir(parents=True, exist_ok=True)
GUARD = (ROOT / "scripts/axiom_guard.lean").read_text()
LEAN = shutil.which(os.environ.get("LEAN", "lean"))
if not LEAN:
    raise SystemExit("Lean compiler not found")
env = os.environ.copy()
env["LEAN_PATH"] = str(ROOT / ".build/linux")
results = {}
for case, preamble, endpoint, expect_pass in [
    ("clean", "import Lean\nimport CrownMain\n", "CollatzFiniteWitness.CHECKER_SOUND", True),
    ("custom", "import Lean\naxiom rogue : False\ntheorem rejected : False := rogue\n", "rejected", False),
    ("sorry", "import Lean\ntheorem rejected : False := by sorry\n", "rejected", False),
    ("unknown", "import Lean\n", "NoSuchEndpoint", False),
]:
    (TEMP / "scripts/audit_endpoints.txt").write_text(endpoint + "\n")
    source = TEMP / (case + ".lean")
    source.write_text(preamble + GUARD)
    p = subprocess.run([LEAN, "-j", "2", str(source)], cwd=TEMP, env=env,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (TEMP / (case + ".log")).write_text(p.stdout)
    passed = p.returncode == 0
    message = ("AXIOM_WHITELIST_PASS" if expect_pass else
               "AXIOM_AUDIT_UNKNOWN_ENDPOINT" if case == "unknown" else "AXIOM_AUDIT_REJECTED")
    ok = passed == expect_pass and message in p.stdout
    results[case] = {"exit": p.returncode, "expected_pass": expect_pass,
                     "result": "PASS" if ok else "FAIL"}
    print(f"AXIOM_GUARD_TEST_{case.upper()}={'PASS' if ok else 'FAIL'}", flush=True)
    if not ok:
        print(p.stdout)
        raise SystemExit(1)
(TEMP / "receipt.json").write_text(json.dumps(results, indent=2) + "\n")
print("AXIOM_GUARD_SELFTEST=PASS", flush=True)
