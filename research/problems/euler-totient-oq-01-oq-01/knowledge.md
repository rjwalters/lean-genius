# Knowledge Base: euler-totient-oq-01-oq-01

Strengthen `carmichael_dvd_totient` (parent `EulerTotientOQ01.lean`) to the full
structural characterization: λ(n) = lcm of the cyclic-factor orders of (ℤ/nℤ)*.

---

## Problem Understanding

λ(n) = `Monoid.exponent (ZMod n)ˣ` (group exponent of the unit group). The parent
file proves λ(n) ∣ φ(n) via `Monoid.exponent_dvd_card`. The "full characterization"
is the standard prime-power formula
  λ(n) = lcm_{p^k ‖ n} λ(p^k),
with λ(p^k) = φ(p^k) for odd p (cyclic group) and λ(2^k) = 2^{k-2} for k ≥ 3.
The decomposition rests on two facts: (i) multiplicativity over coprime factors,
(ii) the prime-power values. This session establishes (i) — the keystone.

---

## Insights

- λ(n) = exponent of (ℤ/nℤ)* makes the whole characterization a statement about
  group exponents, so all the heavy lifting is already in Mathlib's `Monoid.exponent`
  API — no number-theoretic descent needed.
- The unit-group splitting for coprime m, n is *exactly* the composition Mathlib
  uses in `RingTheory/ZMod/UnitsCyclic.lean`:
  `(Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits`.
- `Monoid.exponent_prod : exponent (M₁ × M₂) = lcm (exponent M₁) (exponent M₂)`
  + `Monoid.exponent_eq_of_mulEquiv` reduce multiplicativity to two rewrites.
- ℕ bridge: `lcm` (GCDMonoid) = `Nat.lcm` via root-namespace `lcm_eq_nat_lcm`.

---

## Built Items

- `CarmichaelMultiplicative.carmichael_mul_coprime` (EulerTotientOQ01OQ01.lean):
  for coprime m, n, λ(m·n) = Nat.lcm (λ m) (λ n). Keystone of the characterization.
- `CarmichaelMultiplicative.unitsChineseRemainder`: (ZMod (m·n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ.
- `CarmichaelMultiplicative.order_dvd_carmichael`: orderOf a ∣ λ(n) (universal exponent).

## Mathlib Gaps

- None for the keystone. The remaining (routine) gap is purely combinatorial:
  iterating coprime multiplicativity over `Nat.factorization` to reach
  λ(n) = lcm over prime powers. No missing infrastructure, just induction.

## Next Steps

- Prove `carmichael_eq_lcm_primePow`: λ(n) = `n.factorization.prod`-style lcm of
  λ(p^k) over p^k ‖ n, by induction on the factorization using
  `carmichael_mul_coprime` (Nat.Coprime.prod / `Nat.factorization` recursion).
- Add prime-power values λ(p^k): odd p ⇒ λ(p^k) = φ(p^k) (cyclic);
  λ(2^k) = 2^{k-2} for k ≥ 3 (Mathlib `ZMod.unitsCyclic`-adjacent results).
- Register `EulerTotientOQ01OQ01.lean` in the build once Docker is available and
  add a gallery `meta.json` (status `verified`, badge `mathlib`, axiomCount 0).

---

## Session 2026-06-15 (Session 1) — ACT: coprime multiplicativity keystone

**Mode**: FRESH
**Outcome**: progress (build-pending; Docker + Aristotle blackout this session)

### What I Did
- Created `proofs/Proofs/EulerTotientOQ01OQ01.lean` (build-independent of parent;
  re-defines `carmichael` locally) proving:
  - `carmichael_mul_coprime` — λ(m·n) = lcm(λ m, λ n) for coprime m, n;
  - `unitsChineseRemainder` — the unit-group splitting MulEquiv;
  - `order_dvd_carmichael` — every unit order divides λ(n).
- All Mathlib bearer names verified against mathlib4 master via GitHub API
  (no local build possible): `Monoid.exponent_prod`, `Monoid.exponent_eq_of_mulEquiv`,
  `Monoid.order_dvd_exponent`, `ZMod.chineseRemainder`, `Units.mapEquiv`,
  `MulEquiv.prodUnits`, `lcm_eq_nat_lcm` (root namespace).

### Key Findings
- The keystone is routine given Mathlib — proof is `unfold` + 3 rewrites. The
  unit-splitting composition is copied from Mathlib's own `UnitsCyclic.lean`.
- This is NOT new mathematics; the value is the explicit gallery statement and a
  clean reduction of the remaining characterization to a routine factorization
  induction (no Mathlib gap remains).

### Files Modified
- proofs/Proofs/EulerTotientOQ01OQ01.lean (new, UNREGISTERED build-pending)
- research/problems/euler-totient-oq-01-oq-01/knowledge.md (new)

### Next Steps
- See "Next Steps" above: factorization induction for the full lcm-of-prime-powers
  characterization; register + gallery meta when Docker returns.
