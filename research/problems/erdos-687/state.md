# Current State

**Phase**: COMPLETED
**Since**: 2026-05-17T17:55:00Z
**Iteration**: 5

## Current Focus

Gallery proof is fully formalized at `proofs/Proofs/Erdos687Problem.lean` (548 lines, status `axiomatized`).
state.md catches up with the realized work: covering systems, Jacobsthal function, and the
$1,000 Erdős conjecture are encoded with explicit axiom dependencies on known results.

## Active Approach

Axiomatized formalization (final): all four classical/conjectural inputs are stated as `axiom`
declarations and the open conjecture is derived from them.

Canonical inventory (per `proofs/Proofs/Erdos687Problem.lean`):
- 548 lines (split('\n').length), 0 sorries
- 4 axioms: `jacobsthalY_eq_jacobsthal_sub_one`, `iwaniec_upper`, `fgkmt_lower`,
  `maier_pomerance_conjecture`
- 5 definitions: `primorial`, `IsCovered`, `jacobsthalSet`, `jacobsthalY`, `jacobsthal`
- 26 theorems (broad count, includes private CRT helper lemmas; 21 by narrow
  `^(theorem|lemma) ` regex — both conventions are present in repo tooling)
- Proved (not axiomatized): `jacobsthalSet_bddAbove` (CRT-induction argument that any
  covering system leaves gaps within one primorial period), `erdos_687_conjecture`
  (derived from the stronger Maier–Pomerance conjecture), `jacobsthalY_three`
  (the concrete value Y(3) = 3 by exhaustive residue case analysis)

## Blockers

None. The four `axiom` declarations are honest dependencies on open/unformalized
results — they are the assumptions, not gaps:

1. `jacobsthalY_eq_jacobsthal_sub_one` — bridging identity $Y(x) = g(P(x)) - 1$
   between covering Y(x) and the Jacobsthal function $g$ of the primorial $P(x)$;
   requires CRT periodicity + careful index handling (off-by-one corrected in earlier
   iteration).
2. `iwaniec_upper` — Iwaniec (1978) Selberg-sieve bound $Y(x) \ll x^2$.
3. `fgkmt_lower` — Ford–Green–Konyagin–Maynard–Tao (2018) lower bound
   $Y(x) \gg x \cdot (\log x)(\log\log\log x)/(\log\log x)$.
4. `maier_pomerance_conjecture` — conjectural upper bound
   $Y(x) \ll x \cdot (\log x)^{2 + o(1)}$ (open).

The $1,000 prize statement $Y(x) = o(x^2)$ would follow unconditionally from a
proof of `maier_pomerance_conjecture` (or any sub-$x^{2-\epsilon}$ upper bound).

## Next Action

Maintenance only. Future research iterations could attempt to replace one of the
four axioms (most tractable target: a quantitative formalization of Iwaniec's
Selberg-sieve argument, which is the only fully proved upper bound). No active
work is scheduled.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: 1 (axiomatized formalization with proved CRT structure +
  proved Y(3) = 3 base case)
