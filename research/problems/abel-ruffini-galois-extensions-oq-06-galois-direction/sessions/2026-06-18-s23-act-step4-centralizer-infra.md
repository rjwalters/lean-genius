# S23 ACT — Step 4 infrastructure: centralizer of a p-cycle (`|C(σ)| = p`, `C(σ) = ⟨σ⟩`) (researcher-3, 2026-06-18)

## Mode
ACT — claimed `abel-ruffini-galois-extensions-oq-06-galois-direction` (RICH, knowledge
score 24) via `claim-random`. Docker up (load ~19, 13 peer containers); Aristotle MCP
returns 404 ("Resource not found") — backend still down, so a manual discharge.

## Prior state (post-S22)
The registered file `Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean` carries a
**single** remaining `sorry`: Step 4, `normalizer_iso_AGL1Z` (line ~429). Steps 1, 2, 3, 5
and the main assembly are all proved (PRs #25684 Step 3, #25698 main, #24917 Step 5,
#25875 Step 1). So the entire classification
`primitive_solvable_subgroup_embeds_AGL1Z` is conditional ONLY on Step 4.

## Step 4, restated
`normalizer_iso_AGL1Z (σ) (σ.IsCycle) (σ.support.card = p) :`
`∃ φ : (zpowers σ).normalizer →* AGL1Z p, Injective φ ∧ Surjective φ`.

Mathematically: `N := N_{S_p}(⟨σ⟩)` has order `p·(p−1) = |AGL1Z p|`, and the conjugation
action of `N` on the cyclic `⟨σ⟩ ≅ ℤ/p` realises the iso `N ≅ ℤ/p ⋊ (ℤ/p)ˣ = AGL(1,p)`.
The **crux cardinality input** is `|C_{S_p}(σ)| = p`, i.e. the centralizer of a `p`-cycle
is exactly `⟨σ⟩` (so it is the kernel of `N → Aut(⟨σ⟩)`, giving
`|N| = |C|·|image| ≤ p·(p−1)`).

## What S23 did — proved the centralizer infrastructure (build-verified)
Two new theorems, inserted before `normalizer_iso_AGL1Z`:

1. `centralizer_pcycle_card : Nat.card (Subgroup.centralizer {σ}) = p`.
   Route: `Equiv.Perm.nat_card_centralizer` (Mathlib
   `GroupTheory/Perm/Centralizer.lean:632`) expresses `|C(g)|` as a product over the
   cycle type. A `p`-cycle on the `p`-point set `ZMod p` has
   `cycleType σ = {p}` (`IsCycle.cycleType : σ.cycleType = {#σ.support}` + `σ.support.card = p`),
   so the formula `(card α − sum)! · prod · ∏(count)!` collapses to
   `(p−p)! · p · 1! = 1·p·1 = p`. Closed by `Multiset.{sum,prod,toFinset,count_singleton}` +
   `Finset.prod_singleton` + `Nat.sub_self` + `simp`.

2. `centralizer_pcycle_eq_zpowers : Subgroup.centralizer {σ} = Subgroup.zpowers σ`.
   `⟨σ⟩ ≤ C(σ)` (powers commute with `σ`, `Commute.zpow_self`); both have order `p`
   (lemma 1; `Nat.card_zpowers` + `IsCycle.orderOf` for `⟨σ⟩`); equal finite cardinality +
   inclusion ⟹ equality (`Subgroup.eq_of_le_of_card_ge`).

Both are `sorry`-free, axiom-free, and reusable. They are the genuinely reusable kernel of
the still-hard Step-4 cardinality bound (`|N| ≤ p(p−1)`). The remaining Step-4 work — the
concrete injective+surjective hom into the AGL1Z *structure* — still requires a
σ-coordinate identification of the `p` points with `ℤ/p` (unavoidable for a hom into the
concrete affine structure), and is left `sorry`.

## Build
- `docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`: see
  `/tmp/r3-step4-build.log` (result recorded in PR).
- Sorry frontier unchanged at **1** (Step 4 `normalizer_iso_AGL1Z`), but Step 4 now rests on
  two machine-checked centralizer lemmas instead of a hand-waved `|C(σ)| = p`.

## Next steps
- **Finish Step 4**: build the conjugation hom `N → (ZMod p)ˣ` (scale, via
  `centralizer_pcycle_eq_zpowers` as kernel) and the σ-coordinate `trans` map; or
  transport `N(⟨σ⟩) ≅ N(⟨c⟩) = range(AGL1Z.toPerm)` via a conjugator `τστ⁻¹ = c`
  (`isConj_iff_cycleType_eq`), then pull back along the parent's injective `AGL1Z.toPerm`.
  The `range(toPerm) = N(⟨c⟩)` identification reduces (via these new lemmas) to the easy
  inclusion `range ⊆ N` plus the now-established `|N| ≤ p(p−1) = |range|`.
- Aristotle retry once the 404 backend recovers (the Step-4 statement is self-contained).
