#!/usr/bin/env python3
"""Compile the explicit project graph and freshly audit all public endpoints.

Cached .olean files are reused only with a matching module source hash,
transitive dependency fingerprint, compiler/core-library identity, flags,
build-script hash, and output-byte hash. A successful receipt is written only
after the fresh axiom guard passes. This script performs no witness search.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
VERSION = "v0_1_0_construction"
PREFIX = f"GOODWORKFLOWFRONTIER::{VERSION}::"
EXPECTED_VERSION = "4.33.0"
EXPECTED_COMMIT = "d8b18978322de05a8f3dba51ef03cf5461676c17"
FLAGS: list[str] = ["-j", "2"]
NAME = re.compile(r"^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*$")


def emit(key: str, value: object) -> None:
    print(f"{PREFIX}{key}={value}", flush=True)


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def digest(obj: object) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def read_list(path: Path) -> list[str]:
    values = [line.strip() for line in path.read_text().splitlines()
              if line.strip() and not line.lstrip().startswith("#")]
    if not values or len(values) != len(set(values)) or not all(NAME.fullmatch(v) for v in values):
        raise RuntimeError(f"empty, duplicate, or malformed names in {path}")
    return values


def code_only(text: str) -> str:
    """Remove nested block comments, line comments and string literals."""
    out: list[str] = []
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i): depth += 1; i += 2
            elif text.startswith("-/", i): depth -= 1; i += 2
            else:
                if text[i] == "\n": out.append("\n")
                i += 1
        elif string:
            if text[i] == "\\": i += 2
            elif text[i] == '"': string = False; i += 1; out.append(" ")
            else:
                if text[i] == "\n": out.append("\n")
                i += 1
        elif text.startswith("/-", i): depth = 1; i += 2; out.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"': string = True; i += 1; out.append(" ")
        else: out.append(text[i]); i += 1
    return "".join(out)


def run(command: list[str], *, env: dict[str, str] | None = None) -> str:
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {' '.join(command)}\n{result.stdout}")
    return result.stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--no-incremental", action="store_true")
    args = parser.parse_args()
    build = ROOT / ".build" / "linux"
    logs = ROOT / ".build" / "logs"
    build.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    receipt_path = ROOT / ".build" / "receipt.json"
    receipt_path.unlink(missing_ok=True)
    modules = read_list(ROOT / "scripts/modules.txt")
    endpoints = read_list(ROOT / "scripts/audit_endpoints.txt")
    architecture_endpoints = {
        "CollatzFiniteWitness.FINITE_WITNESS_IMPLIES_COLLATZ",
        "CollatzFiniteWitness.RawSearch.INDEXED_SEARCH_IMPLIES_COLLATZ",
        "CollatzFiniteWitness.RawSearch.INDEXED_SEARCH_IFF_ORIGINAL_ACCEPTANCE",
    }
    if not architecture_endpoints.issubset(endpoints):
        raise RuntimeError("architecture report requires all three audited transfer/coverage endpoints")
    files = {m: ROOT.joinpath(*m.split(".")).with_suffix(".lean") for m in modules}
    actual = {p.stem for p in ROOT.glob("*.lean")}
    if actual != set(modules):
        raise RuntimeError(f"module inventory mismatch: unlisted={sorted(actual-set(modules))}, missing={sorted(set(modules)-actual)}")
    deps: dict[str, list[str]] = {}
    ordered: list[str] = []
    for module in modules:
        code = code_only(files[module].read_text())
        forbidden = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code)
        if forbidden:
            raise RuntimeError(f"forbidden source token {forbidden.group()} in {files[module].name}")
        imports: list[str] = []
        for line in code.splitlines():
            match = re.match(r"\s*(?:public\s+|private\s+)?import\s+(.+)$", line)
            if match: imports.extend(match.group(1).split())
        deps[module] = [name for name in imports if name in files]
        for name in imports:
            if name not in files and not (name == "Lean" or name.startswith("Lean.") or name.startswith("Init.") or name == "Init" or name.startswith("Std.") or name == "Std"):
                raise RuntimeError(f"unconfigured external import: {module}: {name}")
        if any(name not in ordered for name in deps[module]):
            raise RuntimeError(f"scripts/modules.txt is not topologically ordered at {module}")
        ordered.append(module)
    lean = shutil.which(args.lean)
    if not lean:
        raise RuntimeError(f"Lean is not installed or executable: {args.lean}")
    version = run([lean, "--version"])
    if not re.search(r"\bversion 4\.33\.0(?:,|\s|\))", version) or EXPECTED_COMMIT not in version:
        raise RuntimeError(f"wrong toolchain: expected Lean {EXPECTED_VERSION} commit {EXPECTED_COMMIT}; found {version}")
    lean_prefix = Path(run([lean, "--print-prefix"]))
    core_dir = lean_prefix / "lib" / "lean"
    core_files = sorted(p for p in core_dir.rglob("*.olean*") if p.is_file())
    if not core_files:
        raise RuntimeError("toolchain has no core .olean files")
    core_manifest = {str(p.relative_to(core_dir)): sha(p) for p in core_files}
    compiler = lean_prefix / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    shared_files = sorted(p for p in lean_prefix.rglob("*.so*") if p.is_file())
    shared_manifest = {str(p.relative_to(lean_prefix)): sha(p) for p in shared_files}
    relevant_env = {key: os.environ.get(key, "") for key in
                    ["LD_PRELOAD", "LD_LIBRARY_PATH", "LEAN_SYSROOT", "LEAN_NUM_THREADS"]}
    environment_files: dict[str, str] = {}
    # Include explicit loader libraries and library directories. Never read
    # unrelated environment variables (credentials, tokens, or connector data).
    for name in re.split(r"[:\s]+", relevant_env["LD_PRELOAD"]):
        p = Path(name)
        if name and p.is_absolute() and p.is_file(): environment_files[str(p)] = sha(p)
    for name in relevant_env["LD_LIBRARY_PATH"].split(":"):
        p = Path(name)
        if name and p.is_dir():
            for library in sorted(p.glob("*.so*")):
                if library.is_file(): environment_files[str(library)] = sha(library)
    # A platform compatibility launcher may add an explicit loader library.
    # Its bytes are hashed below; also fingerprint its literal .so references.
    launcher_bytes = Path(lean).read_bytes()
    if launcher_bytes.startswith(b"#!"):
        for name in re.findall(r"/[A-Za-z0-9_./+-]+\.so(?:\.[0-9]+)*", launcher_bytes.decode(errors="replace")):
            p = Path(name)
            if p.is_file(): environment_files[str(p)] = sha(p)
    identity = {
        "version": version, "core_olean_sha256": digest(core_manifest),
        "compiler_sha256": sha(compiler), "launcher_sha256": sha(Path(lean)),
        "shared_library_sha256": digest(shared_manifest),
        "explicit_environment": relevant_env, "environment_file_sha256": environment_files,
        "platform": sys.platform, "machine": os.uname().machine,
        "flags": FLAGS, "build_script_sha256": sha(Path(__file__)),
        "lean_path_policy": "project build output only; implicit compiler core path",
    }
    (ROOT / ".build/toolchain-provenance.json").write_text(json.dumps(identity, indent=2) + "\n")
    emit("TOOLCHAIN", "PASS")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(build)
    env.pop("LEAN_SRC_PATH", None)
    compiled, reused = [], []
    fingerprints: dict[str, str] = {}
    module_results: dict[str, object] = {}
    for module in ordered:
        output = build.joinpath(*module.split(".")).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        metadata = output.with_suffix(".json")
        fingerprint = digest({"source_sha256": sha(files[module]), "toolchain": identity,
                              "imports": {dep: fingerprints[dep] for dep in deps[module]}})
        previous = {}
        try: previous = json.loads(metadata.read_text())
        except (OSError, ValueError): pass
        can_reuse = (not args.no_incremental and previous.get("fingerprint") == fingerprint
                     and output.is_file() and previous.get("output_sha256") == sha(output))
        if can_reuse:
            reused.append(module)
            emit(f"MODULE_{module}", "FROZEN_REUSED")
        else:
            metadata.unlink(missing_ok=True)
            output.unlink(missing_ok=True)
            result = subprocess.run([lean, *FLAGS, "-o", str(output), str(files[module])],
                                    cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            (logs / f"{module}.log").write_text(result.stdout)
            if result.returncode or not output.exists():
                print(result.stdout, end="", flush=True)
                raise RuntimeError(f"module compilation failed: {module} (exit {result.returncode})")
            record = {"fingerprint": fingerprint, "output_sha256": sha(output),
                      "source_sha256": sha(files[module]), "imports": deps[module]}
            metadata.write_text(json.dumps(record, indent=2) + "\n")
            compiled.append(module)
            emit(f"MODULE_{module}", "COMPILED_PASS")
        fingerprints[module] = digest({"input": fingerprint, "output": sha(output)})
        module_results[module] = {"state": "frozen_reused" if can_reuse else "compiled",
                                  "source_sha256": sha(files[module]),
                                  "output_sha256": sha(output), "fingerprint": fingerprint}
    audit = ROOT / ".build" / "AxiomAudit.lean"
    audit.write_text("import Lean\n" + "".join(f"import {m}\n" for m in ordered)
                     + "\n"
                     + "".join(f"#print axioms {name}\n" for name in endpoints)
                     + (ROOT / "scripts/axiom_guard.lean").read_text())
    result = subprocess.run([lean, str(audit)], cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / "axiom-audit.log").write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    if result.returncode or f"AXIOM_WHITELIST_PASS: {len(endpoints)} endpoints;" not in result.stdout:
        raise RuntimeError(f"fresh endpoint axiom audit failed (exit {result.returncode})")
    source_paths = [*files.values(), ROOT/"lean-toolchain", ROOT/"lakefile.toml",
                    *sorted((ROOT/"scripts").glob("*")), ROOT/"run.cmd"]
    provenance = {str(p.relative_to(ROOT)): sha(p) for p in source_paths if p.is_file()}
    (ROOT/".build/source-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    # Report only the audited forward implication. The converse and witness
    # existence remain open; these labels do not assert their negations.
    architecture = {
        "ACCEPTED_WITNESS_EXISTS_IMPLIES_COLLATZ": "PROVED",
        "COLLATZ_IMPLIES_ACCEPTED_WITNESS_EXISTS": "NOT_PROVED",
        "ACCEPTED_WITNESS_EXISTS_IFF_COLLATZ": "NOT_ESTABLISHED",
        "ACCEPTED_CONCRETE_WITNESS": "NOT_SUPPLIED",
    }
    receipt = {"workflow": "YOU_ARE_GOODWORKFLOWFRONTIER", "version": VERSION,
               "build": "PASS", "axiom_audit": "PASS", "compiler": identity,
               "compiled": compiled, "frozen_reused": reused, "modules": module_results,
               "endpoints": endpoints, "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
               "accepted_concrete_witness": "NOT_SUPPLIED", "collatz_proved": False,
               "search_executed": False, "architecture": architecture,
               "utc_timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    for key, value in architecture.items():
        emit(key, value)
    emit("SUMMARY", f"BUILD=PASS;AXIOM_AUDIT=PASS;NEW={len(compiled)};REUSED={len(reused)};ACCEPTED_WITNESS=NOT_SUPPLIED;COLLATZ_PROVED=NO")
    return 0


if __name__ == "__main__":
    try: raise SystemExit(main())
    except (OSError, RuntimeError) as error:
        emit("SUMMARY", "BUILD=FAIL;COLLATZ_PROVED=NO")
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
