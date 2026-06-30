# Knowledge: erdos-978-oq-01 (n⁴ + 2 squarefree infinitely often)

## Established this session (S1 ORIENT, build-free, sympy-verified)

`verify_squarefree_density.py` certifies by exact integer/rational computation:

- **No local square obstruction.** For every prime `p < 200`,
  `ρ(p²) = #{n mod p² : p² | n⁴+2} ≤ 4` (the degree bound), so `ρ(p²) < p²` always.
  Hence there is **no fixed square dividing `n⁴+2` for all `n`** — the trivial "NO"
  route (a covering square) is ruled out. A degree-4 congruence mod `p²` has at most
  4 roots, so `ρ(p²) = p²` is impossible for `p² > 4`; the data confirms the bound is
  attained (`ρ = 4`) only at `p ∈ {73, 89, 113, …}`.

- **Contributing primes.** `ρ(p²) > 0` (i.e. `x⁴ ≡ −2 mod p²` solvable) for
  `p ∈ {3, 11, 19, 43, 59, 67, 73, 83, 89, 107, 113, 131, 139, 163, 179, …}`. Each has
  `x⁴ ≡ −2 mod p` solvable and Hensel-lifts (cross-checked). `ρ(p²) = 4` exactly when
  `−2` is a fourth power with 4 distinct fourth roots mod `p` (e.g. `p = 73, 89, 113`).

- **Positive conjectural density.** `C = ∏_p (1 − ρ(p²)/p²)`:
  - over `p < 200`:  `C ≈ 0.757273`
  - over `p < 2000`: `C ≈ 0.756728`  (tail shift `5.4×10⁻⁴` ⇒ converged, `C > 0`).
  So the standard squarefree-sieve heuristic predicts a **positive density** of
  squarefree values of `n⁴+2`, hence **infinitely many** — consistent with the
  (open) conjecture.

- **Empirical match.** Actual squarefree fraction of `{n⁴+2 : n ≤ N}`:
  `N=2000 → 0.7570`, `N=10⁴ → 0.7564`, `N=5·10⁴ → 0.75668`, vs heuristic `0.756728`
  (`|diff| ≈ 5×10⁻⁵` at `N=5·10⁴`). The sieve model matches the true behaviour.

## Literature anchors

- Hooley 1967: `(k−1)`-power-free values have positive density (⇒ `n⁴+2` cubefree
  infinitely often — already an axiom `n4_plus_2_cubefree` in the gallery file).
- Heath-Brown 2006 / Browning 2011: `(k−2)`-power-free infinitely often for `k ≥ 9`
  (with asymptotic). The `k = 4` squarefree case is **not** reached by these methods.

## Open / blocked

- **The conjecture itself is open** — not a Lean proof target. The analytic gap is the
  large-prime square-sieve (`p` up to `~N²`), beyond Mathlib and beyond current
  number theory for `k = 4`.
- **Formalizable residue (future ACT, Docker-gated):** Lean defs/lemmas for `ρ(p²)`
  (decidable, `Finset.filter` over `ZMod (p²)`), the no-obstruction statement
  `∀ p prime, ρ(p²) < p²` (follows from `Polynomial.card_roots`/degree ≤ 4), and the
  positivity of the local-factor product. These are genuine, self-contained, and do
  not require resolving the open analytic problem.
