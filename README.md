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

## Accomplishments

| Accomplishment | Result and verification scope |
|---|---|
| Ordinary Collatz transfer | An accepted finite matrix certificate implies that every positive integer reaches 1 under the ordinary map. CI-verified: `CHECKER_SOUND`. |
| Finite raw witness format | Three natural numbers encode dimension, matrix entries, and bias entries; the witness has no proof fields or assumed propositions. |
| Exhaustive countable certificate search | Every accepted certificate in the matrix language occurs at a natural-number index. CI-verified: `INDEXED_SEARCH_IFF_ORIGINAL_ACCEPTANCE`. |
| Sound bounded search | Every returned index is accepted and below the bound; an accepted index guarantees success at some finite bound. CI-verified: `BOUNDED_SEARCH_SOUND`, `ACCEPTED_INDEX_EVENTUALLY_FOUND`. |
| Symbolic search-space reductions | Scalar interpretations are impossible; positive leading entries are encoded by construction; a necessary first-row coupling guard preserves every accepted certificate. CI-verified. |
| Reproducible Lean verification | Lean 4.33.0 on GitHub Actions; eight modules, 24 audited endpoints, and four audit-guard tests passed. |
| Frontier A: conditional limit-exchange closure | The supporting interchange branch identifies both iterated limits and proves that their equality for every positive target is equivalent to Collatz. The interchange premise remains open; this branch is outside the current eight-module CI target. |

The certificate search is exhaustive for its specified language. Neither an
accepted global witness nor the converse “Collatz implies a matrix certificate
exists” has been proved.

## Frontier A — conditional limit-exchange closure

The recovered branch `COLLATZ_FRONTIER_A_INTERCHANGE_LEAN_v0_1_0` gives the
**dyadic predecessor tower formulation** of Frontier A, using the actual
ordinary Collatz dynamics.

Let $J$ be the first square-root restart: for $n>1$, take the first ordinary
orbit value $x$ with $x^2\le n$, or return the failure marker $0$ if no such
value exists; $J(0)=0$ and $J(1)=1$. Define

$$
B=\{c\ge1:\text{the ordinary Collatz orbit of }c\text{ never reaches }1\},
\qquad A_k=\{n\ge1:J^k(n)=0\},
\qquad U_c(j,k)=\mathbf 1_{A_k}(2^j c).
$$

For every positive target $c$, the branch proves both limit values:

$$
\lim_{j\to\infty}\lim_{k\to\infty}U_c(j,k)=\mathbf 1_B(c),
\qquad
\lim_{k\to\infty}\lim_{j\to\infty}U_c(j,k)=0.
$$

At fixed restart depth $k$, the support bound
$U_c(j,k)=1\Rightarrow 2^j c<(2c)^{2^k}$ makes the tower sequence eventually
zero. At fixed tower height $j$, absorption eventually stabilizes at
$\mathbf 1_B(c)$. Lean expresses these limits by exact eventual equality
of sequences taking values in $\{0,1\}$.

The remaining condition is the **limit-exchange postulate**:

$$
\left[
\forall c\ge1,\quad
\lim_{j\to\infty}\lim_{k\to\infty}U_c(j,k)
=
\lim_{k\to\infty}\lim_{j\to\infty}U_c(j,k)
\right]
\quad\Longleftrightarrow\quad
\mathrm{Collatz}.
$$

The precise declarations in `NativeIteratedLimits.lean`, namespace
`CollatzNativeLimits`, are `DEPTH_THEN_TOWER_LIMIT`,
`TOWER_THEN_DEPTH_LIMIT`, `INTERCHANGE_POSTULATE_IMPLIES_COLLATZ`, and
`INTERCHANGE_POSTULATE_IFF_COLLATZ`.

**Status: conditional closure.** Both iterated limits are identified; their
interchange is an explicit, unproved theorem premise. Existence of both limits
does not establish their equality. The actual restart predicate is
noncomputable, so this is a separate analytic reduction, not an accepted finite
matrix witness.

The original **harmonic Frontier A** retains the explicit
`ActualPredecessorDensity` premise:

$$
\mathrm{ActualPredecessorDensity}
\quad\land\quad
\liminf_{N\to\infty}
\max_{0\le k<K(N)}\mu_N(F_k)=0
\quad\Longrightarrow\quad
\mathrm{Collatz},
$$

where $F_k$ is the layer of starts with $k$ successful restarts followed by
failure, $\mu_N(S)=H_N^{-1}\sum_{1\le n\le N,\ n\in S}1/n$,
$H_N=\sum_{n=1}^{N}1/n$, and $K(N)=\min\{k:N<2^{2^k}\}$.
The tower formulation above needs no predecessor-density assumption.

These Frontier A statements document the supporting branch sources. They are
not included in this repository's current eight-module CI certification.

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

**Assistant execution policy: GitHub Actions CI only.** All Lean compilation,
axiom audits, and Lean-backed tests must run on the CI runner, as recorded in
[`AGENTS.md`](AGENTS.md). The commands below document the runner and manual
tooling; they do not authorize assistant-local compilation.

The [first CI run](https://github.com/randogelist/Collatz-Final/actions/runs/40174097923)
passed for commit `6ca031982422214ff33f2ec651b9c0da2f7551e6`: eight modules
compiled, 24 endpoints passed the axiom whitelist, and all four guard tests
passed. Its compiler and audit receipts are retained as workflow artifacts.

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
