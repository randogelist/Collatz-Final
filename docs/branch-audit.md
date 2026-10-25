# Attached branch audit

This is a source audit, not a fresh compilation claim for every supplied archive.
The default Lean target contains only the five unchanged arithmetic/matrix core
modules from archive 10 and the new search/pruning modules. No Mazur axiom is imported.

| Supplied branch | Relevant result | Qualification |
|---|---|---|
| 01 Dagger Mazur regularity | Dagger regularity equivalence | Assumes predecessor density and existence of actual fibre densities. |
| 02 Heavy prefix count | Necessary heaviness and exact counting bound | Restricts hypothetical bad minima; does not prove their absence. |
| 03 Dagger partition | Partition-vanishing equivalence | Assumes `MazurHarmonicInput`; actual masses are noncomputable. |
| 04 Dagger QM28 | Actual Collatz/QM28 equivalences | Any stated arithmetic anchors must be discharged before using the conclusion. |
| 05 CBC packet | Packet/Collatz equivalences | Retains harmonic input and universal bad-basin packet soundness. |
| 06 Dagger partition Mazur | Moving-layer equivalence | Assumes `MazurInput`; countable quantifiers do not make predicates executable. |
| 07 Weighted closure | Aggregate cofinal smallness equivalence | Retains predecessor density and an infinite-depth condition. |
| 08 Monks carrier | Terminal-carrier reduction | Requires two `ExternalAnchors`. |
| 09 Affine return orientation | Mixed binary/ternary matrix certificate core | Finite raw coefficient data; acceptance implies actual Collatz. |
| 10 Heavy242 frontier | Same standalone matrix core; HeavyMerge242 carrier | Matrix core has no external arithmetic adapter. Carrier restrictions are a separate search problem. |
| 11 Crown row mechanics | Row and component minimum restrictions | Contains a transitive `MazurAxiom` import; not used in the default target. |
| 12 Direct basin pathway | `HARD_FRONTIER_IFF_COLLATZ` | Requires `ActualPredecessorDensity`; noncomputable frontier, not a finite checker. |
| 13 Compact Poincare scout | C++ candidate/pruning search | No accompanying fully proved finite-witness-to-Collatz transfer. |
| 14 R34 adaptive checker | Finite arithmetic cell checker | Global conclusion still requires `Rooted384Anchor`. |
| 15 Two-map scout | C++ rational-height search | No supplied Lean soundness chain for the global conclusion. |
| 16 Mazur zero density | Conditional analytic closure | Explicit research axiom `MAZUR_2026_PREDECESSOR_DENSITY`; excluded. |

## Carrier search versus certificate search

Archive 10 proves `nativeBadMinimum_heavyMerge242`: each minimum representative
of a hypothetical bad coalescence component lies in 242 residue classes modulo
8192. Its `ACTUAL_COLLATZ_IFF_ROOT_CARRIER242_QM28` retains a universal condition
on those hypothetical minima. It does not turn the matrix parameter space into
242 candidates or imply a finite accepted certificate exists.

The matrix certificate language has seven natural matrices and seven natural
vectors, with eleven finite rewrite-rule comparisons. Its soundness chain is:

`check_sound -> toRanking -> ranking_implies_collatz -> CHECKER_SOUND`.

The proof constructs arithmetic simulation and binary coverage. It does not
assume termination, trajectory coverage, the Collatz conjecture, or an analytic
density theorem. The new search layer enumerates this sufficient certificate
language. Completeness for that language is distinct from completeness for
Collatz itself.

## Explicitly open

1. Exhibit a global accepted certificate.
2. Prove, if possible, that Collatz implies existence of a certificate in this
   matrix language. None of the audited sources establishes this converse.
3. Establish the analytic branch's predecessor-density/frontier inputs without
   a research axiom if that separate route is pursued.

No assertion that the witness search will eventually succeed is made.
