# Collatz-Final

Formal reductions of ordinary Collatz in Lean 4.33.0.

[Finite-witness PDF](docs/preprint/collatz-preprint.pdf) ·
[Mazur PDF](docs/preprint/mazur-preprint.pdf) ·
[Sources](docs/preprint/)

**Finite-witness CI:** 8 modules · 24 axiom-audited endpoints.

## Accomplishments

- Finite matrix checker with proved transfer to ordinary Collatz.
- Exhaustive natural-number enumeration of its certificate language.
- Sound bounded search and eventual discovery of any accepted index.
- Scalar certificates excluded; a necessary coupling guard proved.

$$
(\exists n\in\mathbb N,\ \mathrm{checkCode}(n)=\mathrm{true})
\Longrightarrow \mathrm{Collatz}.
$$

**Remaining goal:** produce one accepted finite witness. The forward implication
is sufficient; enumeration alone does not guarantee success.

## Sample runner output

After a successful build and axiom audit (version prefix omitted):

```text
ACCEPTED_WITNESS_EXISTS_IMPLIES_COLLATZ=PROVED
COLLATZ_IMPLIES_ACCEPTED_WITNESS_EXISTS=NOT_PROVED
ACCEPTED_WITNESS_EXISTS_IFF_COLLATZ=NOT_ESTABLISHED
ACCEPTED_CONCRETE_WITNESS=NOT_SUPPLIED
```

The proved biconditional equates indexed search with matrix-certificate
acceptance; the transfer to Collatz is presently one-way.

## Frontier A · conditional limit-exchange closure

Let $U_c(j,k)$ indicate actual restart absorption by depth $k$ on the dyadic
predecessor $2^j c$, and let $B$ be the set of bad positive integers.

$$
\lim_j\lim_k U_c(j,k)=\mathbf1_B(c),
\qquad
\lim_k\lim_j U_c(j,k)=0.
$$

Equality of the two limit orders for every $c\ge1$ is equivalent to Collatz.
**The interchange premise remains unproved.** This supporting branch is
outside the current CI target.

[Full statements](docs/overview.md) ·
[Branch audit](docs/branch-audit.md) ·
[GitHub Actions](https://github.com/randogelist/Collatz-Final/actions)

All assistant-run Lean compilation and audits use GitHub CI.
