# Claim — No Level-3 modular obstruction at n = 4, 5, 6 (and, structurally, at any prime)

- **Vector attempted**: modular-obstruction
- **Date**: 2026-06-17
- **Author**: Loom builder (issue #22636)
- **Status**: failed (no obstruction found) — negative result, fully decisive

## What was tried

For each $(n, \epsilon, p)$ with

- $n \in \{4, 5, 6\}$,
- $\epsilon \in \{-1, +1\}$ (negative defect $a^n + b^n + 1 \equiv c^n$, positive
  defect $a^n + b^n \equiv c^n + 1$),
- $p \in \{3, 5, 7, 11, 13\}$,

an exhaustive search over all residue triples $(a, b, c) \in (\mathbb{Z}/p)^3$
was run, excluding only the all-zero triple $(0,0,0) \equiv 0$ as non-primitive.
A prime $p$ is a *Level-3 modular obstruction* at $(n, \epsilon)$ iff **no**
primitive residue triple satisfies the corresponding congruence. The search
script (`claims/scripts/modular_obstruction_search.py`) is a trivial triple loop
over residues mod $p$ (30 cells, each $p^3 \le 2197$ triples); it ran in well
under a second.

## What happened

**Every** $(n, \epsilon, p)$ in scope admits a primitive residue solution, so
**no obstruction exists** anywhere in the searched range. Full table (all 30
cells found a solution; representative witnesses shown):

| $n$ | sign | $p=3$ | $p=5$ | $p=7$ | $p=11$ | $p=13$ |
|----|------|-------|-------|-------|--------|--------|
| 4 | neg ($+1$) | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ |
| 4 | pos ($-1$) | $(0,1,0)$ | $(0,1,0)$ | $(0,1,0)$ | $(0,1,0)$ | $(0,1,0)$ |
| 5 | neg ($+1$) | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ |
| 5 | pos ($-1$) | $(0,0,2)$ | $(0,0,4)$ | $(0,0,6)$ | $(0,0,2)$ | $(0,0,12)$ |
| 6 | neg ($+1$) | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ | $(0,0,1)$ |
| 6 | pos ($-1$) | $(0,1,0)$ | $(0,0,2)$ | $(0,1,0)$ | $(0,1,0)$ | $(0,0,2)$ |

The non-obstruction is **structural and rules out every prime**, not just the
searched range. There are universal "unit" residue witnesses valid in any
$\mathbb{Z}/p$ for all $n \ge 1$:

- Negative sign: $(a, b, c) = (0, 0, 1)$ gives $0^n + 0^n + 1 = 1 = 1^n$. This is
  primitive ($c = 1 \ne 0$).
- Positive sign: $(a, b, c) = (1, 0, 0)$ gives $1^n + 0^n = 1 = 0^n + 1$. This is
  primitive ($a = 1 \ne 0$).

Intuitively, a unit-offset Fermat congruence is *trivially* satisfiable mod any
$p$ precisely because the "$\pm 1$" can be absorbed by the residue $1 = 1^n =
\dots$. So single-prime congruence obstructions cannot exist for the defect-one
problem in either sign at any exponent — this attack vector is a dead end for
*all* $n$, not merely $n \in \{4,5,6\}$.

### Lean formalization

The structural result is machine-checked in `proofs/Proofs/FermatDefectOne.lean`
(built clean under the Docker wrapper, 0 sorry / 0 axiom / no `native_decide` in
the new declarations — the existing $n=3$ benchmarks' `native_decide` is
untouched):

- `fermat_defect_no_obstruction_neg (n p : Nat) (hn : 1 ≤ n) [NeZero p]
  [Fact (1 < p)] : ModSolvableNeg n p` — general negative-sign witness $(0,0,1)$.
- `fermat_defect_no_obstruction_pos (n p : Nat) (hn : 1 ≤ n) [NeZero p]
  [Fact (1 < p)] : ModSolvablePos n p` — general positive-sign witness $(1,0,0)$.
- 30 explicit `decide`-checked instances
  `fermat_defect_obstruction_n_<k>_<sign>_mod_<p>` for the searched
  $(n, \epsilon, p)$, each stating `Mod{Neg,Pos}Solvable <k> <p>` (the congruence
  is solvable, hence *no* obstruction).

`ModSolvableNeg`/`ModSolvablePos` package "the defect congruence has a primitive
residue solution over $\mathbb{Z}/p$".

## What this suggests for next iteration

- **Abandon the single-prime `modular-obstruction` vector for all $n$.** The
  unit witnesses $(0,0,1)$ / $(1,0,0)$ make it provably impossible. Record this
  in `notes/dead-ends.md`.
- A *composite* / CRT modulus inherits the same unit witnesses, so it cannot
  obstruct either — combining primes does not help.
- More promising remaining vectors for refuting Level 3 (if it is false at some
  $(n, \epsilon)$) are non-congruence: the `reduction` vector (Fermat–Catalan /
  Mason–Stothers finiteness; see the parameterization claim #22637 which already
  closed the $\mathbb{Z}[t]$ polynomial-family route) and direct
  `witness-search` (issue #22635) to find or bound integer witnesses.
- The genuine arithmetic obstruction, if any exists, is global (archimedean /
  size-based), not local at a prime.
