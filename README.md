# Collatz finite-witness countable search

`YOU_ARE_GOODWORKFLOWFRONTIER` · `v0_1_0_construction` · Lean 4.33.0

This project formalizes a sufficient finite-certificate route to the ordinary
Collatz conjecture, an exhaustive countable search of that certificate language,
and symbolic reductions of its search space. It does not prove Collatz and does
not supply an accepted global certificate.

The exact main implication is:

```lean
CollatzFiniteWitness.RawSearch.INDEXED_SEARCH_IMPLIES_COLLATZ
  (h : ∃ n : Nat, CollatzFiniteWitness.RawSearch.checkCode n = true) :
  CollatzFiniteWitness.Collatz
```

Here `Collatz` is literally every positive natural number reaching 1 under
`C n = if n % 2 = 0 then n / 2 else 3 * n + 1`.

## Finite data and exhaustive enumeration

The source certificate is seven natural matrices and seven natural bias vectors
of a common finite dimension. The checker verifies eleven rewrite-rule
comparisons, with strict descent for the odd rule. All infinite-context descent,
binary representation coverage, and transfer to ordinary Collatz are proved.

`RawSearch.RawWitness` contains exactly three natural numbers: `dimension`,
`matrixCode`, and `biasCode`. It contains no proposition, proof field, oracle,
or infinite function. Finite tables are decoded from these integers. A fourth
encoding combines the three integers into a single natural index.

The following are separate proved statements:

| Declaration | Exact purpose |
|---|---|
| `COUNTABLE_RAW_SEARCH` | Every raw witness is reached by `candidate : Nat → RawWitness`. |
| `ORIGINAL_WITNESS_COVERED` | Every accepted nonscalar original matrix witness has an accepted code. |
| `INDEXED_SEARCH_IFF_ORIGINAL_ACCEPTANCE` | An accepted index exists iff an accepted witness exists in the original matrix language. |
| `CHECK_CODE_SOUND` | Acceptance of one index implies ordinary Collatz. |
| `BOUNDED_SEARCH_SOUND` | A finite search result really passed the checker and lies below the requested bound. |
| `ACCEPTED_INDEX_EVENTUALLY_FOUND` | Every accepted index is found by a sufficiently large finite search, possibly via another accepted index. |
| `SEARCH_SUCCESS_IFF_ORIGINAL_ACCEPTANCE` | Some finite search succeeds iff the original matrix language has an accepted witness. |

No theorem asserts the converse `Collatz → ∃ n, checkCode n = true`. The search
is complete for this particular certificate language; its completeness for
Collatz remains open. Countable enumeration does not imply eventual success.

## Proved search reductions

1. Every scalar certificate is rejected, for all coefficient values. The raw
   decoder therefore starts at actual dimension `dimension + 2`.
2. The seven mandatory positive entries `M_s[0,0]` are encoded as `raw + 1`.
   Their positivity is guaranteed by construction, and exact coverage of all
   accepted original certificates is proved.
3. Every accepted certificate has a positive off-diagonal first-row coefficient
   in at least one of `L`, `t`, or `two`. An exact finite guard rejects candidates
   lacking this coupling before the main checker. `REDUCED_CHECK_EQ_ORIGINAL`
   proves that the guard loses no accepted original certificate.

These are symbolic impossibility proofs, not outcomes of a bounded numerical
experiment. In particular, every diagonal matrix interpretation is excluded.
No universal minimality or optimality of the remaining search language is claimed.

## Build and audit

The project needs only the pinned Lean distribution, including core/Omega.
Mathlib is not required for this certificate chain.

On Linux, with Lean 4.33.0 on PATH:

```sh
python3 scripts/build.py
```

Alternatively set `LEAN` or pass `--lean /absolute/path/to/lean`. This compiles
the explicit module graph and freshly checks all listed endpoint axioms against
`propext`, `Classical.choice`, and `Quot.sound`. Any other axiom, including
`sorryAx`, fails the build. The source gate also rejects proof holes and unsafe
proof shortcuts. Successful logs and source/toolchain fingerprints are under
`.build/`. Unchanged modules are reused only after fingerprint validation.

On native Windows, use the sole `run.cmd`. It uses the existing Lean 4.33.0
installation and rebuilds into a fresh output directory. Set `COLLATZ_LEAN_EXE`
if Lean is outside the usual elan toolchain directory. It runs the same Lean
axiom guard without Python, PowerShell, WSL, or Lake setup. Native Windows
execution is not claimed by a Linux receipt.

`.github/workflows/lean.yml` installs the official Lean 4.33.0 release on an
Ubuntu runner, verifies the pinned archive checksum, caches compatible build
artifacts, runs the build/audit, and uploads receipts. A checked-in workflow is
not evidence of a successful GitHub Actions run; remote status must be observed
separately.

`lake build` is available for ordinary development, but is not a replacement
for the explicit axiom audit.

## Optional finite search

After the audited Linux build, use its output path:

```sh
LEAN_PATH=.build/linux lean --run SearchMain.lean check INDEX
LEAN_PATH=.build/linux lean --run SearchMain.lean search EXCLUSIVE_BOUND
```

The commands require natural numbers in place of the uppercase arguments.
There is no automatic unbounded search, scheduled job, or background search.
The reference diagonal decoder has cost linear in the numeric code and can be
impractical for large codes. Its purpose is a transparent, proved enumeration.
Efficient SAT/SMT search can target the original finite coefficient constraints
and use the same checker without traversing the reference enumeration.

A native executable printing acceptance is candidate discovery only. Recheck
the exact candidate in a theorem with kernel-reduced `decide`, compile it, and
audit its transferred conclusion before claiming a proof of Collatz. Finite
search failure never establishes that the infinite search space is empty.

## Sources and status

The five core files are copied byte-for-byte from the attached
`COLLATZ_CROWN_QM28_FRONTIER_ALGEBRA_LEAN_v0_10_0_HEAVY242_MERGE8192` package.
New files formalize search and pruning. Input and core hashes are recorded in
[`docs/source-provenance.json`](docs/source-provenance.json).

[`docs/branch-audit.md`](docs/branch-audit.md) records why the other supplied
branches do not provide a stronger standalone terminating checker: several
retain analytic, universal-adapter, or rooted-carrier assumptions. The sharper
HeavyMerge242 carrier is not silently substituted for matrix-checker completeness.

The mixed binary/ternary rewrite encoding is attributed in the original source
to Yolcu, Aaronson, and Heule,
[An Automated Approach to the Collatz Conjecture](https://arxiv.org/abs/2105.14697).
The local arithmetic transfer is proved here, rather than imported as an axiom.

`ACCEPTED_CONCRETE_WITNESS=NOT_SUPPLIED` · `COLLATZ_PROVED=NO`.
