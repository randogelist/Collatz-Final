# Mazur companion: source provenance

[mazur-source-archives.zip](mazur-source-archives.zip) preserves four supplied
source archives byte-for-byte. Only their outer entry filenames have been
normalized; the nested archive contents are unchanged. The bundle contains
`SHA256SUMS.txt` for the four original ZIP byte streams.

These are the source and evidence inputs for reconstructing the Mazur companion,
not a recovered original manuscript. The statuses below report the evidence
contained in each supplied package. They do not constitute a fresh compilation
or a result of this repository's current GitHub CI. No Lean execution was
performed while preparing this provenance bundle.

| Source archive | Role | Evidence and remaining obligations |
| --- | --- | --- |
| `COLLATZ_DAGGER_MAZUR_REGULARITY_LEAN_v0_1_6_FIX6.zip` | Fixed-fibre harmonic regularity, restart gaps, density transfer, and conditional closure. | `PREPARATION_STATUS.txt` marks FIX6 compiler validation pending. Earlier theorem-module passes are recorded in `CHANGES.txt`; the final FIX6 probe and runner audit remain unverified in the supplied record. Mazur predecessor density and fibre regularity are explicit unproved premises. |
| `COLLATZ_DAGGER_PARTITION_MAZUR_LEAN_v0_1_5_FIX5.zip` | Failure-root partition, finite predecessor localization, moving-layer counts, and conditional partition closure. | `README.txt` and `PROVENANCE.txt` record eight FIX4 theorem modules passing and 16 dependency reports containing only standard foundational axioms; the FIX4 probe failed on `pp.width`. FIX5 removes that option and preserves the theorem sources, but its complete runner audit is pending. Mazur density and the simultaneous small moving-layer condition remain explicit hypotheses. |
| `COLLATZ_DAGGER_WEIGHTED_CLOSURE_LEAN_v0_2_1_FIX1.zip` | Parity density, weighted inverse first-crossing masses, contraction, and synchronized aggregate closure. | `README.txt`, `SOURCE_LINEAGE.txt`, and `PATCH_NOTES.txt` distinguish passed predecessor modules from the new work. The supplied run stopped at `ParityDensity`; FIX1 changes that proof line, and subsequent modules were not reached. Complete FIX1 verification remains pending. Mazur density, weighted contraction, and the aggregate frontier are not discharged. |
| `COLLATZ_MAZUR_FRONTIER_ZERO_DENSITY_ATIER_LEAN_v0_2_0_REBUILT.zip` | Actual-frontier zero lower harmonic/log density, positive-density contradiction, and Mazur-relative closure. | `NATIVE_PASS_LOG.txt` is a supplied native Windows Lean 4.33.0 PASS record for the package lineage, as identified by its README. The explicit-premise core closure and basin estimate have standard-only dependencies in that log. Public wrappers additionally depend on the research axiom `CollatzMazurLiterature.MAZUR_2026_PREDECESSOR_DENSITY`. This is not a fresh certification of the rebuilt archive or a current CI pass; `ActualFrontier` remains open. |

The sources support conditional reductions. They supply neither an unconditional
Collatz proof nor an accepted finite global witness. The explicit Mazur axiom in
the zero-density lineage must not be identified with the theorem-parameter
formulations in the other three packages, or silently admitted by the current
matrix-certificate axiom gate.

## Exact source SHA-256 hashes

```text
d4a2f60f789f83e57b017cf5d7d278d253bc0aa2828d79c011c840237e0ae150  COLLATZ_DAGGER_MAZUR_REGULARITY_LEAN_v0_1_6_FIX6.zip
833306e636f00802db438dc84a15356206022136b9a041b1086207e34a41062a  COLLATZ_DAGGER_PARTITION_MAZUR_LEAN_v0_1_5_FIX5.zip
340340211ffe0317388456a3a6733a80d7199993997de7d82e91461134aa7358  COLLATZ_DAGGER_WEIGHTED_CLOSURE_LEAN_v0_2_1_FIX1.zip
81ba476aac0c85952ecf3f7e4e1cb2c6138614810bd62784689929aec65a0b68  COLLATZ_MAZUR_FRONTIER_ZERO_DENSITY_ATIER_LEAN_v0_2_0_REBUILT.zip
```

After extracting the outer bundle, `sha256sum -c SHA256SUMS.txt` verifies the
nested archives without invoking Lean. Preserve the bundled status and lineage
files when reconstructing or extending the companion.

The external input is Lech Mazur, [*Positive Lower Density of Collatz Predecessors*, Theorem 1.1](https://www.proofatlas.ai/papers/positive-lower-density-collatz-predecessors/paper-v1.pdf), version 1.0, 6 September 2026. Its statement matches the explicit predecessor-density premise. The local source bundle does not import its proof.
