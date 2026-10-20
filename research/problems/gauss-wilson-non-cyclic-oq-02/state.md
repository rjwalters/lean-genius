# Research State: gauss-wilson-non-cyclic-oq-02

## Current State
**Phase**: ACT (S3 — UNBLOCKED; cyclic half PROVED in new `GaussWilsonNonCyclicOQ02.lean`; next S4 = elementary-abelian half)
**Path**: full
**Since**: 2026-07-24 (S3 ACT, researcher-2)
**Iteration**: 3

## S3 ACT (researcher-2, 2026-07-24) — UNBLOCKED; cyclic half proved

The S2 block was 6 weeks stale (Docker up, multiple green builds today).
Created `proofs/Proofs/GaussWilsonNonCyclicOQ02.lean` (0 sorries, 0 axioms,
kernel `decide` only):

- `two_torsion_pm_one_iff_isCyclic` (n ≥ 3): 2-torsion ⊆ {±1} ↔
  `IsCyclic (ZMod n)ˣ` — the survey's "S₂ cyclic ⟺ global cyclic" in
  Sylow-free form. Forward = contrapositive of parent
  `exists_third_sqrt_of_not_cyclic` (+ public `unitOfSqEqOne*` lifts);
  reverse = `IsCyclic.card_pow_eq_one_le` vs `{1, -1, x}`.
- `neg_one_ne_one_units` (public re-derivation; parent's is `private`).
- Exponent anchors by kernel `decide`: `(ZMod 8)ˣ` exponent 2,
  `(ZMod 16)ˣ` has an order-4 element (rank-blind invariant).

**S4 (next)**: elementary-abelian half, Sylow-free form
`(∀ x, x⁴ = 1 → x² = 1) ↔ (all odd p ∣ n have p % 4 = 3) ∧ v₂(n) ≤ 3`.
CRT + odd-cyclic order-gcd + 2-adic cap; the `(ZMod 2^a)ˣ ≅ C₂ × C_{2^{a-2}}`
structure lemma is the likely Mathlib gap (~80–150 LOC). 1–2 sessions.
See `sessions/2026-07-24-s3-act-cyclic-half.md`.

## S2 STATUS-SYNC (superseded 2026-07-24; blockers were stale) — flag BLOCKED
researcher-1, 2026-06-13. No Lean written. The S1 ORIENT survey already
resolved the core mathematics on paper (both boundary characterizations,
cross-checked vs OQ-03). The sole remaining work — creating
`GaussWilsonNonCyclicOQ02.lean` with `s2_cyclic_iff` and
`s2_elementaryAbelian_iff` — is build-dependent, and the verification
blackout (Docker daemon HUNG, Aristotle 404, CI does not build Lean)
leaves no route to compile/verify a new file. There is also a likely
Mathlib gap (explicit `(ZMod 2^a)ˣ ≅ C₂ × C_{2^{a-2}}` iso, ~80-150 LOC
if absent). Flipping `surveyed → blocked` stops the depth-first claim
picker from repeatedly re-selecting a slug whose only next step is
build-gated; reverse to `surveyed` when Docker returns. Unblock recipe
unchanged (see Next Action below).

## Current Focus
Core mathematics resolved on paper (see knowledge.md): the Sylow 2-subgroup
structure of `(ZMod n)ˣ` and both boundary characterizations (cyclic;
elementary abelian). Next is formalization, currently build-gated.

## Active Approach
CRT decomposition `(ZMod n)ˣ ≅ (ZMod 2^a)ˣ × ∏ (ZMod pᵢ^{eᵢ})ˣ`, then read off
`S₂ ≅ D(a) × ∏ C_{2^{v₂(pᵢ-1)}}`. Reuse parent file's CRT machinery and
`ZMod.isCyclic_units_iff`.

## Attempt Count
- Total attempts: 0 (no Lean written — verification infra down)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Docker build daemon down and Aristotle backend returning 404 (2026-06-13
  verification blackout) — no route to compile/verify Lean this session.
- Likely Mathlib gap: explicit `(ZMod 2^a)ˣ ≅ C₂ × C_{2^{a-2}}` iso (to confirm).

## Next Action
When build infra returns: create `GaussWilsonNonCyclicOQ02.lean` stating
`s2_cyclic_iff` and `s2_elementaryAbelian_iff`, reusing the parent CRT lemmas;
locate or build the `(ZMod 2^a)ˣ` structure lemma.

## Status (S4, researcher-3, 2026-09-29) — ACT: elementary-abelian half PROVED; OQ-02 fully formal

`GaussWilsonNonCyclicOQ02.lean` extended 131 → 379 lines (0 sorries, 0 axioms,
kernel `decide` only; `#print axioms` = foundational trio on all headline
theorems; host-verified `lake env lean` exit 0):

- **`units_pow_four_imp_sq_iff`** (n ≠ 0): `(∀ x : (ZMod n)ˣ, x⁴ = 1 → x² = 1)
  ↔ (∀ odd prime p ∣ n, p % 4 = 3) ∧ n.factorization 2 ≤ 3` — the Sylow
  2-subgroup of `(ZMod n)ˣ` is elementary abelian iff every odd prime factor
  is ≡ 3 (mod 4) and 2⁴ ∤ n. Together with S3's
  `two_torsion_pm_one_iff_isCyclic`, BOTH halves of OQ-02 are now formal.
- Proof: multiplicative induction `Nat.recOnPosPrimePosCoprime`; CRT splitting
  `(ZMod ab)ˣ ≃* (ZMod a)ˣ × (ZMod b)ˣ` via `ZMod.chineseRemainder` +
  `Units.mapEquiv` + `MulEquiv.prodUnits`; odd prime powers via
  `ZMod.isCyclic_units_of_prime_pow` + generator order = φ(p^a) with
  `4 ∣ p−1 ⟺ p % 4 = 1`; 2-adic cap via **`ZMod.orderOf_five`** (5 has order
  `2^(a−2)`), which landed in `Mathlib.RingTheory.ZMod.UnitsCyclic` — the
  structure lemma S3 predicted would be an 80–150-line gap required ZERO gap
  lines.
- Reusable helper `exists_pow_four_ne_sq`: `orderOf g = 4m, m ≠ 0` ⟹ `g^m`
  is the order-4 violation — avoids `orderOf_pow`/gcd bookkeeping.
- v4.31 drift notes: `orderOf_eq_card_of_forall_mem_zpowers` now lands in
  `Nat.card` (bridge with `Nat.card_eq_fintype_card`; use
  `orderOf_dvd_natCard`); `Nat.recOnPosPrimePosCoprime` hands the case
  `Nat.Prime p` directly (no `Nat.prime_iff` conversion);
  `Nat.Prime.factorization_pow` takes `Nat.Prime`; `Nat.Coprime.pow` has
  explicit exponent arguments.

## Next Action
OQ-02 is answered in full (both halves formal). Candidate follow-ups: none
strong — the natural next invariant (full 2-adic valuation of the exponent of
`(ZMod n)ˣ`, i.e. `v₂(λ(n))`) is a routine generalization of the same
induction, and the rank/exponent contrast is already pinned by the S3 anchors.
Prefer marking completed.
