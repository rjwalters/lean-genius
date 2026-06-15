# Knowledge Base: inclusion-exclusion-oq-01-oq-03

Open question of `inclusion-exclusion-oq-01`:

> Formalize Möbius inversion: `f(n) = Σ_{d|n} g(d)  ⟺  g(n) = Σ_{d|n} μ(d)·f(n/d)`.

This is the number-theoretic form of inclusion–exclusion (μ = IE sign on the
divisor lattice). The parent already proves the special case `Σ_{d|n} φ(d) = n`.

---

## Insights

### Session 2026-06-15 (ORIENT, researcher-9) — Mathlib has it in antidiagonal form; bridge to textbook form

**Mode**: FRESH. **Outcome**: ORIENT + build-pending Lean bridge; all-pass verifier.
Honest framing: the mathematical depth is already in Mathlib; this session's
contribution is exposing the **textbook divisor-sum** shape the gallery wants.

**Mathlib already proves Möbius inversion** (v4.26.0, pin `2df2f0150c27`), but in
**antidiagonal** form — `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`
(`Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:240`, `[NonAssocRing R]`):

    (∀ n>0, Σ_{i ∈ n.divisors} f i = g n) ↔
      (∀ n>0, Σ_{x ∈ n.divisorsAntidiagonal} μ x.1 · g x.2 = f n).

Companions: `sum_eq_iff_sum_smul_moebius_eq` (AddCommGroup, `•`),
`prod_eq_iff_prod_pow_moebius_eq` (multiplicative), and `_on`/`_on'` variants
restricted to a divisor-closed set.

**The textbook form** `g(n) = Σ_{d|n} μ(d)·f(n/d)` differs only by replacing the
antidiagonal sum with a divisor sum. The bridge is `Nat.sum_divisorsAntidiagonal`
(`Mathlib/NumberTheory/Divisors.lean`, the `@[to_additive]` partner of
`prod_divisorsAntidiagonal`):

    Σ_{x ∈ n.divisorsAntidiagonal} F x.1 x.2 = Σ_{d ∈ n.divisors} F d (n/d).

So the textbook theorem is `sum_eq_iff_sum_mul_moebius_eq` rewritten by
`Nat.sum_divisorsAntidiagonal (fun a b => μ a · f b)` (plus `eq_comm` to match the
gallery orientation `f(n) = Σ g(d)`).

**Durable verification** `verify_moebius_inversion.py` (stdlib, exhaustive
n ≤ 400, random ℤ data) — ALL PASS:
- (A) forward→inverse `g(n) = Σ_{d|n} μ(d) f(n/d)`;
- (B) inverse→forward `f(n) = Σ_{d|n} g(d)`;
- (C) μ sanity + the convolution `Σ_{d|n} μ(d) = [n=1]`;
- (D) Euler-φ anchor: `Σ_{d|n} φ(d) = n` and `φ(n) = Σ_{d|n} μ(d)·(n/d)`.

**Lean artifact** (build-pending, UNREGISTERED)
`proofs/Proofs/InclusionExclusionOQ01OQ03.lean`:
`moebius_inversion_divisors {f g : ℕ → R} [CommRing R]` — the textbook iff,
proved by the two-lemma bridge above.

---

## Next steps

1. **ACT (live build).** Compile `InclusionExclusionOQ01OQ03.lean`; if a name
   needs adjustment (`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`,
   `Nat.sum_divisorsAntidiagonal`, `μ` scoped notation), repair and register.
2. **φ corollary.** Add `(φ n : ℤ) = Σ_{d|n} μ(d)·((n/d : ℕ) : ℤ)` as a one-line
   consequence (`f = Nat.cast`, `g = φ`, using `Nat.sum_totient`), tying back to
   the parent's `Σ_{d|n} φ(d) = n`.
3. **General poset IE (optional, harder).** Möbius inversion over an arbitrary
   locally-finite poset (Rota); Mathlib's `Mathlib/Order/...` incidence-algebra
   coverage would need checking — out of scope for this divisor-lattice OQ.

## Dead Ends / Non-starters

- Re-deriving Möbius inversion from scratch: unnecessary — Mathlib has it
  (`sum_eq_iff_sum_mul_moebius_eq`); only the antidiagonal→divisor presentation
  was missing.

### Session 2026-06-15 (ACT, researcher-2) — added the Euler-φ Möbius corollary

Built on S1's `moebius_inversion_divisors` bridge by adding the documented next-step
corollary in the same UNREGISTERED `InclusionExclusionOQ01OQ03.lean`:

    totient_eq_sum_moebius_mul (n) (hn : 0 < n) :
      (Nat.totient n : ℤ) = ∑ d ∈ n.divisors, (μ d : ℤ) * ((n / d : ℕ) : ℤ)

Proof = one application of `moebius_inversion_divisors (R := ℤ)` with `f = (·:ℤ)`,
`g = (Nat.totient ·:ℤ)`; the forward input `(m:ℤ) = Σ_{d|m} φ(d)` is `exact_mod_cast
(Nat.sum_totient m).symm` (`Nat.sum_totient : n.divisors.sum φ = n`, Data/Nat/Totient.lean:160).
`exact_mod_cast` used deliberately to dodge `Nat.cast_sum` name drift (no bare `Nat.cast_sum`
in this layout; `cast_sum` only exists for ℚ/ℚ≥0). This is the inclusion–exclusion "inverse"
of the parent entry's `Σ_{d|n} φ(d) = n`.

Name-checks vs pinned mathlib4 v4.26.0 (sibling): `sum_eq_iff_sum_mul_moebius_eq`
(Moebius.lean:240, `[NonAssocRing R]`), `Nat.sum_totient` (Totient.lean:160),
`Nat.sum_divisorsAntidiagonal` (to_additive partner of `prod_divisorsAntidiagonal`,
Divisors.lean:543) — all present. File still 0 axioms / 0 sorries; build-pending UNREGISTERED
(dual blackout: docker ps exit 124, Aristotle 404).

### Session 2026-06-15 (ACT, researcher-3) — register the completed file for machine-checking

**Mode**: build-free ACT under Docker+Aristotle blackout. **Outcome**: registration only.

`InclusionExclusionOQ01OQ03.lean` was on `main` and complete (both
`moebius_inversion_divisors` and `totient_eq_sum_moebius_mul`, 0 axioms / 0 sorries)
but **absent from `proofs/Proofs.lean`** — i.e. never compiled by the gallery build,
so "verified" was inspection-only. Added the single manifest line
`import Proofs.InclusionExclusionOQ01OQ03` (between `…OQ01` and `…OQ03`) and updated
the file's status note. Re-verified the proof logic by hand: the `(f := g)(g := f)`
instantiation of `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` composed with the
`Nat.sum_divisorsAntidiagonal` divisor↔antidiagonal bridge (plus `.symm`/`eq_comm`)
is sound. Registration is deployer-build-gated: a compile failure blocks this PR's
merge, not `main`, so it is blackout-safe.

**Next**: if a later live session sees the build pass, mark the OQ `completed`.
General poset (Rota) Möbius inversion remains out of scope for this divisor-lattice OQ.
