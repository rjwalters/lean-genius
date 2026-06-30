# burnside-counting-oq-04-oq-02-oq-02 — Reflection half of the dihedral bracelet count

## Goal
Evaluate Σᵢ |Fix(sr i)| (reflection contribution to the dihedral Burnside sum) by parity of n,
completing the closed form b(n) = (rotationSum + reflectionSum)/(2n) built in parent OQ-04-OQ-02-OQ-01.

## Worked-out mathematics (complete)
Reflection `sr i` acts on positions by the involution σ_i(p) = -i - p (from posPerm_sr = subLeft(-i)).
A colouring is fixed by sr i ⟺ constant on σ_i-orbits.
#σ_i-orbits = (n + f_i)/2 where f_i = #{p : 2p = -i} (fixed points of σ_i).
So |Fix(sr i)| = 2^((n+f_i)/2).

f_i by parity of n:
- n odd: 2 is a unit ⟹ f_i = 1 for all i ⟹ |Fix| = 2^((n+1)/2).
  Σ = n·2^((n+1)/2).
- n even: f_i = 2 if i has even val (i in image of doubling), else 0; n/2 of each.
  even-val i: 2^(n/2+1); odd-val i: 2^(n/2).
  Σ = (n/2)·2^(n/2+1) + (n/2)·2^(n/2) = (3n/2)·2^(n/2).

## Linchpin lemma (proved, elementary)
`card_invariant_colorings_involutive`: for an involution σ on a Fintype α,
|{c : α → Fin 2 // ∀a, c(σ a)=c a}| = 2^((|α| + |Fix σ|)/2).
Proof avoids group actions / Burnside / orbit-quotient Fintype instances entirely:
- index α by ℕ via Fintype.equivFin (f a = (equivFin a).val), injective;
- representative rep a = the smaller-f element of {a, σ a}; reps = R = filter (f a ≤ f(σ a));
- invariant colourings ≃ (R → Fin 2)  [explicit Equiv: restrict to reps / pull back via rep];
- |R| = (|α|+|Fix|)/2 from: R = L ∪ Fix (L = filter f a<f(σa)); R.card+G.card=|α|
  (G = filter f(σa)<fa = complement of R); |L|=|G| via the σ-bijection (Finset.card_nbij'); omega.
Key API: Fintype.card_fun, Fintype.card_coe, filter_card_add_filter_neg_card_eq_card,
Finset.card_nbij', Finset.filter_or, Finset.card_union_of_disjoint, lt_trichotomy.

## Session 1 (FRESH) — 2026-06-25
- Read parent (rotation half = Σ 2^gcd(n,i)) and grandparent (dihedral action; bracelet_burnside).
- Wrote proofs/Proofs/BurnsideCountingOQ04OQ02OQ02.lean: structural lemmas
  (reflection_smul_apply, fixed_iff_symm, refl, refl_involutive), the linchpin
  card_invariant_colorings_involutive, the per-reflection count card_fixedBy_reflection
  (= 2^((n+reflFix i)/2)), reflFix_odd (= 1 via (2:ZMod n) unit / Units.mulLeft_bijective /
  Bijective.existsUnique), and reflection_sum_odd (= n·2^((n+1)/2)).
- reflFix_odd API: ZMod.isUnit_iff_coprime, Nat.coprime_two_left.mpr, Units.mulLeft_bijective,
  Bijective.existsUnique, Finset.card_eq_one, linear_combination for refl i p = p ↔ 2p = -i.

## Session 2 — 2026-06-25 — COMPLETE & VERIFIED (both parities)
- Odd case built clean as written (no errors). Added the EVEN-n case:
  - two_mul_eq_zero_iff: doubling kernel on ZMod (2m) is exactly {0, m}.
  - reflFix_even: reflFix i ∈ {0, 2} (solution set of 2p=-i is empty or a {0,n/2}-coset).
  - reflFix_sum: Σ_i reflFix i = n for every n, by a fiberwise Finset.sum_comm count
    (each bead is the unique fixed point of one axis i=-2p).
  - card_even_reflections: #{i : reflFix i = 2} = n/2 (omega from 2·#=n and each term∈{0,2}).
  - reflection_sum_even: Σ_i |Fix(sr i)| = 3·(n/2)·2^(n/2), via an ADDITIVE split of the term
    (2^(n/2) + if reflFix i=2 then 2^(n/2) else 0) that uses only the positive filter and
    dodges the un-beta-reduced negated filter from Finset.sum_ite.
- n=6 sanity: 3·3·8 = 72 (parent `decide`: Dihedral 6 total = 156).

## VERIFICATION (Docker down → single-file lake env)
Docker Desktop VM was hung host-wide again (`docker info` HANGS; whole fleet piled up zombie
docker info; `open -a Docker` did not revive in time). Verified anyway WITHOUT docker-build:
  cd /Users/rwalters/GitHub/lean-genius/proofs && lake env lean <worktree-abs-path>
`lake env` is an explicit SAFE pass-through in proofs/bin/lake (only `lake build` is blocked);
it elaborates ONE file against main's prebuilt .lake oleans (parent + Mathlib), bounded memory,
and runs the `#print axioms` lines. RESULT: all four headlines
(card_invariant_colorings_involutive, card_fixedBy_reflection, reflection_sum_odd,
reflection_sum_even) depend only on [propext, Classical.choice, Quot.sound] — no sorryAx, no
Lean.ofReduceBool. 0 axioms, 0 sorries, 12 thm / 2 def / 436 lines.

Lean fixes: `rw [hn2] at hp` (hp:n∣2*p.val) fails motive (p.val type depends on n) → obtain
the witness and finish with omega; `congr 1; omega` → "No goals" (congr already closed defeq)
→ `simp`; deprecations natCast_zmod_eq_zero_iff_dvd→natCast_eq_zero_iff,
card_insert_of_not_mem→card_insert_of_notMem.

## Status: registered in Proofs.lean; gallery entry
src/data/proofs/burnside-counting-oq-04-oq-02-oq-02/ (meta.json + annotations.json) created;
status verified / badge original / axiomCount 0. PR opened.

## Branch
`research/burnside-reflection-half-oq04020202`.
