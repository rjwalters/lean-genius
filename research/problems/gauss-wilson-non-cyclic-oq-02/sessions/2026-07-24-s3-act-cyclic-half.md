# S3 ACT — cyclic half proved; slug UNBLOCKED (new file created)

**Date**: 2026-07-24
**Agent**: researcher-2
**Mode**: REVISIT (MODERATE, score 8)
**Outcome**: `GaussWilsonNonCyclicOQ02.lean` created (0 sorries, 0 axioms);
the cyclic boundary characterization is fully proved. Stale S2 block
cleared (Docker has been up for weeks; three green builds today).

## What was proved

1. `two_torsion_pm_one_iff_isCyclic` (n ≥ 3):
   `(∀ x : (ZMod n)ˣ, x² = 1 → x = 1 ∨ x = -1) ↔ IsCyclic (ZMod n)ˣ`.
   - Forward = contrapositive of the parent's
     `exists_third_sqrt_of_not_cyclic`, lifted to units via the parent's
     public `unitOfSqEqOne*` API.
   - Reverse = `IsCyclic.card_pow_eq_one_le` (≤ 2 square roots of 1 in a
     cyclic group) vs the 3-element set `{1, -1, x}` (parent's own
     counting pattern, reused).
   This IS the survey's "S₂ cyclic ⟺ global cyclic" statement in the
   Sylow-free formulation: 2-torsion ⊆ {±1} ⟺ rank₂ ≤ 1 ⟺ S₂ cyclic.
2. `neg_one_ne_one_units` — public re-derivation of the parent's private
   lemma via `CharP.cast_eq_zero_iff` (n ∣ 2 contradiction).
3. Kernel-`decide` exponent anchors: `zmod8_units_sq_eq_one`
   ((ZMod 8)ˣ elementary abelian) and `zmod16_units_exists_order_four`
   ((ZMod 16)ˣ has an order-4 element) — the rank-blind exponent
   phenomenon the elementary-abelian half is about. No `native_decide`.

## S4 target (the remaining half)

Sylow-free formulation:
`(∀ x : (ZMod n)ˣ, x⁴ = 1 → x² = 1) ↔`
`(∀ p, p.Prime → Odd p → p ∣ n → p % 4 = 3) ∧ n.factorization 2 ≤ 3`.

Route: CRT (`ZMod.chineseRemainder`, parent machinery), odd prime-power
unit groups cyclic with `v₂(p−1) = 1 ⟺ p ≡ 3 (mod 4)` (order-gcd
argument: x⁴ = 1 and x^|G| = 1 with v₂|G| = 1 gives x² = 1), and the
2-adic cap `a ≤ 3` — small cases by `decide`, `a ≥ 4` needs an order-4
element in `(ZMod 2^a)ˣ` (e.g. the class of 3 mod 16 pushed up, or the
`(ZMod 2^a)ˣ ≅ C₂ × C_{2^{a-2}}` structure lemma, likely a Mathlib gap,
~80–150 LOC). Estimate: 1–2 sessions.

## Ops note

The S2 BLOCKED flags (Docker blackout 2026-06-13, Aristotle 404) were 6
weeks stale — same vein as the bpg-oq-03-oq-02 stale-blocker narrative:
RICH/MODERATE slugs with old build-blocker stories must be re-verified
against live infra before honoring the block.
