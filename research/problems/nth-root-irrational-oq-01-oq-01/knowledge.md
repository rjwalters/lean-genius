# Knowledge Base: nth-root-irrational-oq-01-oq-01

**Title**: Algebraic irrationality of roots of cyclotomic polynomials and their subfields
**Phase**: ACT
**Status**: active (build-pending under Docker/Aristotle blackout)

---

## Problem Understanding

The parent `nth-root-irrational-oq-01` (`NthRootIrrationalOQ01.lean`) proved the
structural principle: *a root of an irreducible polynomial of degree ≥ 2 over ℚ
is irrational*, and applied it to `X^n − p` via Eisenstein. This OQ asks to
extend that principle to **cyclotomic polynomials** Φ_n and their roots (the
primitive n-th roots of unity), and to their subfields.

---

## Result (this session, 2026-06-15, Session 1, FRESH → ACT)

New file `proofs/Proofs/NthRootIrrationalOQ01OQ01.lean` (0 sorries, 0 axioms,
build-pending — both backends down at authoring time). Reuses the parent's
already-proven "irreducible deg ≥ 2 ⇒ no rational root" core (re-proved inline,
verbatim, to keep the file independent of cross-file build state).

1. `totient_ge_two` — `3 ≤ n → 2 ≤ Nat.totient n`. Proof: `Nat.totient_pos`
   (positivity) + `Nat.totient_eq_one_iff` (`φ n = 1 ↔ n = 1 ∨ n = 2`) ⇒ omega.
2. `cyclotomic_no_rational_root` — for `n ≥ 3`, `Φ_n` (over ℚ) has **no rational
   root**. Proof: `cyclotomic.irreducible_rat` + `natDegree_cyclotomic` (= φ(n))
   + `totient_ge_two` feed the inline core.
3. `rational_root_of_unity_le_two` — if `r : ℚ` is a primitive `n`-th root of
   unity (`0 < n`) then `n ≤ 2`. **The only rational roots of unity are ±1.**
   Proof: `IsPrimitiveRoot.isRoot_cyclotomic` gives `r` a root of `Φ_n`,
   contradicting (2) when `n ≥ 3`.
4. `primitiveRoot_not_rational` — a **complex** primitive `n`-th root of unity
   (`n ≥ 3`) is not in `Set.range (algebraMap ℚ ℂ)`; i.e. it is irrational.
   Proof: descend `ζ = algebraMap r` to `r : ℚ` via
   `IsPrimitiveRoot.of_map_of_injective` + `(algebraMap ℚ ℂ).injective`, then (3).
5. `primitiveCubeRoot_not_rational` — concrete instance `e^{2πi/3}` via
   `Complex.isPrimitiveRoot_exp 3`.

Numerically pre-verified (sympy): φ(n) ≥ 2 for all 3 ≤ n ≤ 200; deg Φ_n = φ(n);
Φ_n has no rational roots for n = 3,4,5,6.

---

## Insights

- The whole extension is "swap `X^n − p` (Eisenstein) for `Φ_n`
  (`cyclotomic.irreducible_rat`)" in the parent's irreducibility-⇒-irrational
  pipeline. The only genuinely new lemma is the degree lower bound
  `φ(n) ≥ 2 ⇔ n ≥ 3`.
- `Φ_n` has **no real roots** for n ≥ 3 (Φ_3 = X²+X+1, Φ_4 = X²+1, …), so the
  honest content lives in ℂ (not-rational) and in the rational-roots-of-unity =
  ±1 corollary — not in any "irrational real root" statement (which is vacuous).

## Mathlib gaps

- None for the rational/complex statements. The real **subfield** story
  (degree of `2cos(2π/n)` = φ(n)/2, irrational for n ≥ 5 except 6) was NOT
  formalized this session — `minpoly` of `2cos` is the missing piece; deferred
  as a follow-up OQ (would need the maximal-real-subfield minimal polynomial).

## Next steps / fragile points if CI fails

- `Nat.totient_eq_one_iff` (name) — fallback: prove φ(n) ≥ 2 via the two
  distinct coprime witnesses `1` and `n−1` in `Finset.range n`.
- `Nat.totient_pos.mpr` assumes the iff form (current Mathlib v4.26). If the
  one-directional form is in scope, drop `.mpr`.
- `IsPrimitiveRoot.of_map_of_injective` (Part IV) — assumes the bundled
  `MonoidHomClass` form so `algebraMap ℚ ℂ` unifies directly. Fallback: descend
  via `map_cyclotomic n (algebraMap ℚ ℂ)` + `eval_map`/`aeval` + `map_eq_zero_iff`
  injective, landing on `cyclotomic_no_rational_root` directly.
- `Complex.isPrimitiveRoot_exp` arg form `2 * ↑Real.pi * Complex.I / (n : ℕ)` —
  the concrete instance matches the `↑(3:ℕ)` denominator exactly.
- Register in `proofs/Proofs.lean` and `docker-build.sh Proofs.NthRootIrrationalOQ01OQ01`
  once a backend is available (left UNREGISTERED to protect auto-merge).

## Follow-up OQ (after SOLVED)

- Maximal real subfield: is `2cos(2π/n)` irrational for n ≥ 5 (n ≠ 6), via its
  degree-`φ(n)/2` minimal polynomial? (Genuinely distinct: needs the real
  cyclotomic subfield minpoly, absent above.)

## Dead ends

- "Irrational real root of Φ_n" — vacuous; Φ_n has no real roots for n ≥ 3.
