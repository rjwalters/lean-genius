/-
# Cardinality preservation under the k-fold CRT (bezout-identity-oq-03-oq-01-oq-01-oq-02)

## Open Question
Following the k-fold Chinese Remainder Theorem
  ℤ/(n₁···nₖ)ℤ ≅ ∏ᵢ ℤ/nᵢℤ   (for pairwise coprime nᵢ),
prove the cardinality preservation statement
  |ℤ/(∏nᵢ)ℤ| = ∏ᵢ |ℤ/nᵢℤ| = ∏ᵢ nᵢ.

## Answer: YES

We work with `Nat.card`, which assigns `0` to infinite types. This gives a
uniform statement valid for *every* list of moduli — including the degenerate
case `0 ∈ ns`, where `ℤ/0ℤ = ℤ` is infinite (`Nat.card ℤ = 0`) and both sides
collapse to `0` consistently. No positivity hypothesis is required.

The substantive content is the **left** equality `|ℤ/(∏nᵢ)ℤ| = ∏ᵢ |ℤ/nᵢℤ|`:
it is obtained by transporting the count along the parent's ring isomorphism
`crtKFold`, then factoring `Nat.card` over the nested product type `CRTProd`
factor by factor (`Nat.card_prod`). The **right** equality
`∏ᵢ |ℤ/nᵢℤ| = ∏ᵢ nᵢ` is `Nat.card_zmod` applied termwise.

Note that `|ℤ/(∏nᵢ)ℤ| = ∏nᵢ` is *also* immediate from `Nat.card_zmod` alone;
the value of the CRT route is that it exhibits the count as factoring through
the isomorphism, i.e. it is genuine *preservation* rather than a coincidence of
two independent evaluations.

## Status
- All theorems proved (0 sorries, 0 axioms)
- Reuses `crtKFold` / `CRTProd` from `Proofs.BezoutIdentityOQ03OQ01OQ01`
-/

import Mathlib
import Proofs.BezoutIdentityOQ03OQ01OQ01

namespace BezoutCRTCard

open BezoutCRTKFold

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: CARDINALITY OF THE NESTED PRODUCT TYPE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The count of the nested product type `CRTProd ns` factors as the product of
    the counts of its `ZMod` factors. Proved by induction on `ns`, splitting the
    product with `Nat.card_prod` at each cons. -/
theorem card_CRTProd (ns : List ℕ) :
    Nat.card (CRTProd ns) = (ns.map (fun n => Nat.card (ZMod n))).prod := by
  induction ns with
  | nil =>
      simp only [CRTProd, List.map_nil, List.prod_nil]
      exact Nat.card_unique
  | cons n ns ih =>
      simp only [CRTProd, List.map_cons, List.prod_cons]
      rw [Nat.card_prod, ih]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: TRANSPORT OF THE COUNT ALONG THE CRT ISOMORPHISM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The k-fold CRT ring isomorphism preserves cardinality: the source and target
    are equinumerous because they are isomorphic. -/
theorem card_zmod_prod_eq_card_CRTProd (ns : List ℕ)
    (h : List.Pairwise Nat.Coprime ns) :
    Nat.card (ZMod ns.prod) = Nat.card (CRTProd ns) :=
  Nat.card_congr (crtKFold ns h).toEquiv

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: CARDINALITY PRESERVATION  |ℤ/(∏nᵢ)ℤ| = ∏ᵢ |ℤ/nᵢℤ|
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Cardinality preservation (left equality).**
    `|ℤ/(∏nᵢ)ℤ| = ∏ᵢ |ℤ/nᵢℤ|` for pairwise coprime moduli, witnessed by the
    k-fold CRT isomorphism. This is the substantive half of the open question. -/
theorem card_preservation (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns) :
    Nat.card (ZMod ns.prod) = (ns.map (fun n => Nat.card (ZMod n))).prod :=
  (card_zmod_prod_eq_card_CRTProd ns h).trans (card_CRTProd ns)

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: EVALUATION  ∏ᵢ |ℤ/nᵢℤ| = ∏ᵢ nᵢ
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Termwise evaluation (right equality).**
    `∏ᵢ |ℤ/nᵢℤ| = ∏ᵢ nᵢ`, since `|ℤ/nᵢℤ| = nᵢ` for every modulus
    (`Nat.card_zmod`, which is `nᵢ` even when `nᵢ = 0`, as `Nat.card ℤ = 0`). -/
theorem map_card_zmod_prod (ns : List ℕ) :
    (ns.map (fun n => Nat.card (ZMod n))).prod = ns.prod := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [Nat.card_zmod, ih]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: THE FULL CHAIN  |ℤ/(∏nᵢ)ℤ| = ∏ᵢ |ℤ/nᵢℤ| = ∏ᵢ nᵢ
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Headline.** The full cardinality-preservation chain
    `|ℤ/(∏nᵢ)ℤ| = ∏ᵢ |ℤ/nᵢℤ| = ∏ᵢ nᵢ`, packaged as the conjunction of the two
    equalities so both halves are visible at the use site. -/
theorem card_chain (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns) :
    Nat.card (ZMod ns.prod) = (ns.map (fun n => Nat.card (ZMod n))).prod ∧
      (ns.map (fun n => Nat.card (ZMod n))).prod = ns.prod :=
  ⟨card_preservation ns h, map_card_zmod_prod ns⟩

/-- Direct corollary: `|ℤ/(∏nᵢ)ℤ| = ∏ᵢ nᵢ` for pairwise coprime moduli. -/
theorem card_zmod_prod_eq_prod (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns) :
    Nat.card (ZMod ns.prod) = ns.prod :=
  (card_preservation ns h).trans (map_card_zmod_prod ns)

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: CONCRETE EXAMPLES
═══════════════════════════════════════════════════════════════════════════════ -/

private theorem coprime_2_3_5 : List.Pairwise Nat.Coprime [2, 3, 5] := by decide

/-- `|ℤ/30ℤ| = |ℤ/2ℤ| · |ℤ/3ℤ| · |ℤ/5ℤ| = 2 · 3 · 5 = 30`. -/
theorem card_30 : Nat.card (ZMod 30) = 30 := by
  have h : Nat.card (ZMod (List.prod [2, 3, 5])) = List.prod [2, 3, 5] :=
    card_zmod_prod_eq_prod [2, 3, 5] coprime_2_3_5
  simpa using h

/-- The preservation equality, instantiated at `[2, 3, 5]`. -/
theorem card_preservation_2_3_5 :
    Nat.card (ZMod (List.prod [2, 3, 5]))
      = ([2, 3, 5].map (fun n => Nat.card (ZMod n))).prod :=
  card_preservation [2, 3, 5] coprime_2_3_5

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @card_CRTProd
#check @card_zmod_prod_eq_card_CRTProd
#check @card_preservation
#check @map_card_zmod_prod
#check @card_chain
#check @card_zmod_prod_eq_prod
#check @card_30
#check @card_preservation_2_3_5

end BezoutCRTCard
