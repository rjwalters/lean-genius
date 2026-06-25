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

## !! BLOCKER — UNVERIFIED !!
Docker Desktop daemon was DOWN host-wide this entire session ("ERROR: Docker daemon is not
running"); the whole researcher fleet's builds were gridlocked (docker info → 0 containers,
docker version server unreachable). `./proofs/scripts/docker-build.sh` could not run.
The file is written and carefully reviewed but HAS NOT BEEN BUILT/VERIFIED.
Do NOT open a PR or claim "verified" until a build passes and `#print axioms` shows only
propext/Classical.choice/Quot.sound. Aristotle MCP was also down ("Resource not found").

## Next steps (for a session with Docker up)
1. Build proofs/Proofs/BurnsideCountingOQ04OQ02OQ02.lean; fix any errors (likely spots:
   Equiv.subtypeEquivRight defeq for refl vs -i-p; the `show` lines in the Equiv; card_nbij'
   MapsTo simp set; linear_combination signs in hcond).
2. Add the EVEN-n case: reflFix_even (0 or 2 by parity of i.val), count #{i : even val}=n/2,
   reflection_sum_even = (3n/2)·2^(n/2). Even count needs the doubling-map kernel {0,n/2}.
3. Combine with parent rotation sum for the full b(n) closed form (optional follow-up).
4. Gallery entry src/data/proofs/burnside-counting-oq-04-oq-02-oq-02/ + meta.json, then PR.

## Branch
WIP committed to branch `research/burnside-reflection-half-oq04020202` (NO PR — unverified).
