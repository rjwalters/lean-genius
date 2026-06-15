# Knowledge Base: four-square-distribution-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

We count **representation types** of `n` as four squares. The hyperoctahedral
group `B₄ = (ℤ/2)⁴ ⋊ S₄` (order `2⁴·4! = 384`) acts on the solution set

```
Sol(n) = { (x₁,x₂,x₃,x₄) ∈ ℤ⁴ : x₁²+x₂²+x₃²+x₄² = n }
```

by permuting coordinates (the `S₄` factor) and flipping signs independently (the
`(ℤ/2)⁴` factor). A **type** is a `B₄`-orbit; `numTypes(n) := #(B₄-orbits on Sol(n))`.
Jacobi pins the total `|Sol(n)| = r₄(n)`. The OQ asks for a bound on `numTypes(n)`
in terms of `r₄(n)` / divisor data of `n`.

---

## Insights

### ORIENT (S1, 2026-06-14, researcher-3) — verified orbit-size law + clean type bound

All three results below are checked by brute force for `n = 1..50` in the
reproducible script `scripts/verify_orbit_bound.py` (host `python3`, no Docker).
`ALL CHECKS PASSED`.

**Action convention.** An element `g = (s, σ) ∈ (ℤ/2)⁴ ⋊ S₄` (with `s ∈ {±1}⁴`,
`σ ∈ S₄`) acts by `(g·v)_i = s_i · v_{σ⁻¹(i)}`. The 384 elements were enumerated
explicitly and orbits computed directly.

**(A) Jacobi total (input, classical).**
`r₄(n) = 8·σ*(n)` where `σ*(n) = Σ_{d∣n, 4∤d} d`. Confirmed `r₄ = 8σ*` for all
`n ≤ 50` against brute-force ordered-signed counts. This is the *weighted total*
the OQ takes as given (existence is Mathlib `Nat.sum_four_squares`; the exact
count is the assumed/parent input — see Gaps).

**(B) Orbit-size law (the core lemma).** For a solution `v` with
- `z` = number of zero coordinates, and
- nonzero absolute values occurring with multiplicities `m₁,…,m_k`
  (`z + Σ mⱼ = 4`),

the stabilizer is exactly

```
|Stab_{B₄}(v)| = 2^z · z! · ∏ⱼ (mⱼ!)
|orbit(v)|     = 384 / |Stab_{B₄}(v)|.
```

Reason: a stabilizing `(s,σ)` needs `σ` to preserve both the zero-set and each
equal-|value| class (`z!·∏mⱼ!` choices); given `σ`, signs are *forced* on the
nonzero coordinates and *free* on the `z` zero coordinates (`2^z` choices). The
formula matched the brute-force orbit cardinality for every orbit, every `n ≤ 50`.

Degeneracy table (illustrative, n>0):

| type | `\|Stab\|` | `\|orbit\|` |
|------|-----:|------:|
| `(a,b,c,d)` distinct nonzero | 1 | 384 |
| `(a,a,a,a)` | 24 | 16 |
| `(a,a,0,0)` | 16 | 24 |
| `(a,0,0,0)` | 48 | **8** |

**(C) Clean type bound (the deliverable).** For every `n > 0`,

```
numTypes(n) ≤ r₄(n) / 8 = σ*(n) = Σ_{d∣n, 4∤d} d.
```

Proof skeleton: by orbit–stabilizer `Σ_{orbits} |orbit| = r₄(n)`. By (B), for
`n > 0` at least one coordinate is nonzero, so `z ≤ 3` and the stabilizer is
maximised at the `(a,0,0,0)` type, `|Stab| = 2³·3!·1! = 48`; hence **every orbit
has size ≥ 384/48 = 8**. Therefore `numTypes(n) = Σ_{orbits} 1 ≤ Σ |orbit|/8 =
r₄(n)/8`. Substituting Jacobi gives `numTypes(n) ≤ σ*(n)`. Verified: bound holds
and `minorb ≥ 8` for all `n ≤ 50`.

This is a self-contained, finite, fully-formalizable bound with **no open
analytic dependencies** (matching the OQ's stated character). Equality
`numTypes = σ*` requires every orbit to have size exactly 8 — i.e. all reps of
the `(a,0,0,0)` type — which forces `n` a perfect square `a²` with `r₄ = 8`
(`σ*(a²) = 1`, e.g. `n = 1`). So the bound is tight only at `n = 1` among `n ≤ 50`
(`numTypes(1) = 1 = σ*(1)`); for larger `n` it is a genuine (often loose) upper bound.

---

## Lean Formalization Plan (ORIENT decomposition)

Target Lean statement (clean form, Jacobi taken as a hypothesis):

```lean
-- numTypes n := Nat.card (orbits of B₄ on Sol n)
theorem numTypes_le_sigmaStar (n : ℕ) (hn : 0 < n) :
    numTypes n ≤ sigmaStar n := ...
```

**Buildable now (no analytic input):**
1. `B₄` as `SemidirectProduct (Fin 4 → ZMod 2) (Equiv.Perm (Fin 4)) φ`, or
   pragmatically as the signed-permutation subgroup of `Equiv.Perm (Fin 4 → ...)`.
   Order `384` via `Fintype.card` of the semidirect product
   (`card = 2⁴ · 4!`). **M1.**
2. The `MulAction` of `B₄` on `Sol n ⊆ (Fin 4 → ℤ)`. **M2.**
3. Orbit–stabilizer: `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
   (orbit size = `|G| / |Stab|`), giving `Σ |orbit| = r₄(n)` over orbit reps. **M3.**
4. The orbit-size law (B): stabilizer computation by zero-count + abs-value
   multiplicities. This is the **main labor** — case analysis on degeneracy. **M4.**
5. The bound (C): `|orbit| ≥ 8` for `n > 0` ⟹ `numTypes ≤ r₄/8`. **M5.**

**Gated / assumed (Jacobi exact count):**
- `r₄(n) = 8·σ*(n)` — Mathlib has Lagrange existence (`Nat.sum_four_squares`) but
  (as of pin `2df2f01…`) **not** the exact Jacobi count. Take `r₄ = 8σ*` as a
  hypothesis / parent input, OR prove only the orbit-side `numTypes ≤ r₄(n)/8`
  (which needs NO Jacobi) and state the `σ*` corollary conditionally.
  → **The orbit-side bound `numTypes(n) ≤ r₄(n)/8` is fully self-contained and
     does not depend on Jacobi at all.** Recommend shipping that as the verified
     core, with `≤ σ*(n)` as a Jacobi-conditional corollary.

**Mathlib anchors (modules; exact lemma names to confirm at build time):**
- `Mathlib.GroupTheory.GroupAction.Basic` / `…/Quotient` — `orbit`, `stabilizer`,
  `orbitEquivQuotientStabilizer`, orbit–stabilizer cardinality.
- `Mathlib.GroupTheory.SemidirectProduct` — `B₄` construction.
- `Mathlib.GroupTheory.Perm.*`, `Fintype.card_perm` (`= 4! = 24`).
- `Mathlib.NumberTheory.SumFourSquares` — Lagrange baseline.

---

## Dead Ends

- **Direct divisor bound alone** (approach 2 in problem.md): bounding
  `numTypes ≤ r₄ / (min orbit)` is exactly the route taken, but the value of
  `min orbit` must come from the stabilizer law (B) — without (B) one cannot
  justify `min orbit = 8`. So (B) is not optional; it is the crux. Not a dead end,
  but the "crude" framing in problem.md understates that (B) is required.
