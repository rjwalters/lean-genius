/-
# Unit-group cardinality under the k-fold CRT
# (bezout-identity-oq-03-oq-01-oq-01-oq-02-oq-02)

## Open Question
The parent (oq-03-oq-01-oq-01-oq-02) proved the *element*-count is preserved by
the k-fold Chinese Remainder isomorphism:
  |ℤ/(∏nᵢ)ℤ| = ∏ᵢ |ℤ/nᵢℤ| = ∏ᵢ nᵢ.
Carry the same transport one functor up, to the **unit groups**:
  |(ℤ/(∏nᵢ)ℤ)ˣ| = ∏ᵢ |(ℤ/nᵢℤ)ˣ|,
and express the right-hand side in terms of Euler's totient.

## Answer: YES

The new content is the **unit-group cardinality preservation**
(`card_units_preservation`). It is obtained by applying the *units functor* to
the parent's ring isomorphism `crtKFold ns h : ℤ/(∏nᵢ)ℤ ≃+* CRTProd ns`. A ring
isomorphism is in particular a multiplicative isomorphism, so `Units.mapEquiv`
lifts it to a group isomorphism on units; transporting `Nat.card` along it
reduces the count to the nested product type `CRTProd`. There the units of a
product factor by `MulEquiv.prodUnits : (α × β)ˣ ≃* αˣ × βˣ`, and an induction
peels off one factor at a time (`Nat.card_prod`).

This mirrors the parent's element-count proof exactly one functor up: where the
parent factored `Nat.card (CRTProd ns)` through `Nat.card_prod`, we factor
`Nat.card (CRTProd ns)ˣ` through `MulEquiv.prodUnits` and then `Nat.card_prod`.
Unlike the element count, the *unit* count does **not** read off from `Nat.card`
alone — the order of `(ℤ/nℤ)ˣ` is Euler's `φ n`, which is genuinely sensitive to
the factorization of `n` — so the CRT route is the substance, not a coincidence.

The totient bridge `Nat.card (ℤ/nℤ)ˣ = φ n` (`natCard_units_zmod`, valid for
`n > 0` via `ZMod.card_units_eq_totient`) then lets us read the right-hand side
as `∏ᵢ φ(nᵢ)`, giving the headline payoff
  |(ℤ/(∏nᵢ)ℤ)ˣ| = ∏ᵢ φ(nᵢ)            (`card_units_eq_totient_prod`).

Multiplicativity of `φ` *itself* — `φ(∏nᵢ) = ∏φ(nᵢ)` — is **not** new: it is in
Mathlib (`Nat.totient_mul`) and is already proved unconditionally in the parent
file as `totient_prod_pairwise_coprime` (by `Nat.totient_mul` induction). We do
not re-derive it; instead `card_units_eq_totient_prod` exhibits the *same product*
`∏φ(nᵢ)` as the order of the unit group of `ℤ/(∏nᵢ)ℤ`, i.e. as the unit-count
shadow of the explicit k-fold CRT isomorphism.

We use `Nat.card` throughout, so the pure unit-count statement
(`card_units_CRTProd`, `card_units_preservation`) needs no positivity hypothesis.
Only the totient reading requires `0 < nᵢ`, because `ℤ/0ℤ = ℤ` has the two units
`±1` whereas `φ 0 = 0`.

## Status
- All theorems proved (0 sorries, 0 axioms)
- Reuses `crtKFold` / `CRTProd` from `Proofs.BezoutIdentityOQ03OQ01OQ01`
-/

import Mathlib
import Proofs.BezoutIdentityOQ03OQ01OQ01

namespace BezoutCRTUnits

open BezoutCRTKFold

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: UNIT-GROUP CARDINALITY OF THE NESTED PRODUCT TYPE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The unit count of the nested product type `CRTProd ns` factors as the
    product of the unit counts of its `ZMod` factors. Proved by induction on
    `ns`: at each `cons`, `MulEquiv.prodUnits` splits the units of a product
    into a product of unit groups, and `Nat.card_prod` splits the count. -/
theorem card_units_CRTProd (ns : List ℕ) :
    Nat.card (CRTProd ns)ˣ = (ns.map (fun n => Nat.card (ZMod n)ˣ)).prod := by
  induction ns with
  | nil =>
      -- `CRTProd [] = PUnit`; its unit group is a subsingleton with one element.
      simp only [CRTProd, List.map_nil, List.prod_nil]
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  | cons n ns ih =>
      -- `CRTProd (n :: ns) = ZMod n × CRTProd ns`.
      simp only [CRTProd, List.map_cons, List.prod_cons]
      -- Units of a product ≃* product of unit groups.
      rw [Nat.card_congr (MulEquiv.prodUnits (M := ZMod n) (N := CRTProd ns)).toEquiv,
          Nat.card_prod, ih]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: TRANSPORT OF THE UNIT COUNT ALONG THE CRT ISOMORPHISM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Unit-group cardinality preservation.** For pairwise-coprime moduli, the
    unit count of `ℤ/(∏nᵢ)ℤ` equals the product of the unit counts of the
    factors `ℤ/nᵢℤ`. Obtained by transporting `Nat.card` along the units of the
    k-fold CRT ring isomorphism. No positivity hypothesis is needed. -/
theorem card_units_preservation (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns) :
    Nat.card (ZMod ns.prod)ˣ = (ns.map (fun n => Nat.card (ZMod n)ˣ)).prod := by
  -- The ring iso `crtKFold` is in particular a multiplicative iso, so its
  -- units functor gives `(ℤ/(∏nᵢ)ℤ)ˣ ≃* (CRTProd ns)ˣ`.
  rw [Nat.card_congr (Units.mapEquiv (crtKFold ns h).toMulEquiv).toEquiv,
      card_units_CRTProd]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE UNIT COUNT AS A PRODUCT OF TOTIENTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- For a positive modulus, `Nat.card (ℤ/nℤ)ˣ` is Euler's totient `φ n`.
    Bridges the `Nat.card`-based unit count to Mathlib's `Nat.totient`. -/
theorem natCard_units_zmod (n : ℕ) (hn : 0 < n) :
    Nat.card (ZMod n)ˣ = n.totient := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- **Headline payoff.** The order of the unit group of `ℤ/(∏nᵢ)ℤ` equals the
    product of the totients `∏ᵢ φ(nᵢ)` (pairwise-coprime, positive moduli).
    Combines the unit-count preservation with the termwise totient bridge.

    Together with the standard `φ N = |(ℤ/Nℤ)ˣ|` this *re-expresses* the parent's
    `totient_prod_pairwise_coprime` (`φ(∏nᵢ)=∏φ(nᵢ)`) as the unit-count shadow of
    the CRT isomorphism; we do not re-prove the totient identity itself. -/
theorem card_units_eq_totient_prod (ns : List ℕ)
    (h : List.Pairwise Nat.Coprime ns) (hpos : ∀ n ∈ ns, 0 < n) :
    Nat.card (ZMod ns.prod)ˣ = (ns.map Nat.totient).prod := by
  rw [card_units_preservation ns h]
  -- Termwise replace `Nat.card (ℤ/nᵢℤ)ˣ` by `φ nᵢ` (each nᵢ is positive).
  exact congrArg List.prod (List.map_congr_left (fun n hn => natCard_units_zmod n (hpos n hn)))

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: WORKED EXAMPLE  (30 = 2 · 3 · 5)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- `[2, 3, 5]` is pairwise coprime. -/
theorem coprime_2_3_5' : List.Pairwise Nat.Coprime [2, 3, 5] := by decide

/-- Unit-count preservation for `30 = 2 · 3 · 5`:
    `|(ℤ/30ℤ)ˣ| = |(ℤ/2ℤ)ˣ| · |(ℤ/3ℤ)ˣ| · |(ℤ/5ℤ)ˣ|`. -/
theorem card_units_2_3_5 :
    Nat.card (ZMod ([2, 3, 5].prod))ˣ
      = ([2, 3, 5].map (fun n => Nat.card (ZMod n)ˣ)).prod :=
  card_units_preservation [2, 3, 5] coprime_2_3_5'

/-- The headline payoff at `[2, 3, 5]`:
    `|(ℤ/30ℤ)ˣ| = φ(2)·φ(3)·φ(5)`. -/
theorem card_units_30_eq_totient_prod :
    Nat.card (ZMod ([2, 3, 5].prod))ˣ = ([2, 3, 5].map Nat.totient).prod :=
  card_units_eq_totient_prod [2, 3, 5] coprime_2_3_5' (by decide)

/-- Numeric check: `|(ℤ/30ℤ)ˣ| = φ(2)·φ(3)·φ(5) = 1·2·4 = 8`. -/
theorem card_units_30_eq_8 : Nat.card (ZMod 30)ˣ = 8 := by
  have h : Nat.card (ZMod ([2, 3, 5].prod))ˣ = 8 := by
    rw [card_units_30_eq_totient_prod]; decide
  simpa using h

end BezoutCRTUnits
