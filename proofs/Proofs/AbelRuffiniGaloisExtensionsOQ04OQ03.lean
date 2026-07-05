/-
  Zassenhaus (Butterfly) Lemma  (OQ-04-OQ-03)

  A self-contained formalization of the Zassenhaus butterfly lemma for subgroups,
  the key ingredient of the Schreier refinement theorem and hence of an
  independent (non-lattice) route to Jordan–Hölder.

  ## Statement

  Let `A ⊴ A'` and `B ⊴ B'` be subgroups of a group `G` (here `A ≤ A'` with `A`
  relatively normal in `A'`, and likewise for `B`).  Then
  ```
      A (A' ∩ B')            B (B' ∩ A')
     ────────────    ≅      ────────────
      A (A' ∩ B )            B (B' ∩ A )
  ```
  where a "product" `A (A' ∩ B')` is realized as the subgroup join
  `A ⊔ (A' ⊓ B')` — legitimate because `A ⊴ A'` normalizes `A' ⊓ B' ≤ A'`.

  ## Proof architecture (classical, via a common middle quotient)

  Both butterfly quotients are shown isomorphic to the single quotient
  ```
      (A' ∩ B') ⧸ D ,      D := (A ∩ B') (A' ∩ B) = (A ⊓ B') ⊔ (A' ⊓ B).
  ```
  The isomorphism `(A' ∩ B')/D  ≃  A(A'∩B') / A(A'∩B)` is a *refined second
  isomorphism theorem*: the homomorphism
  ```
      ψ : (A' ⊓ B')  →  (A ⊔ (A'⊓B')) ⧸ (A ⊔ (A'⊓B)) ,   ψ = mk' ∘ inclusion
  ```
  is surjective (because `A ⊴ A'` lets us absorb the `A`-part) with kernel exactly
  `D.subgroupOf (A' ⊓ B')`.  This is the *same construction* used for `second_iso`
  in `AbelRuffiniGaloisExtensionsOQ04` (there proved sorry-free via
  `QuotientGroup.quotientKerEquivOfSurjective`); the butterfly lemma is obtained by
  running it twice and composing.

  ## Proof status (BUILD-BLOCKED — Docker/Aristotle unavailable this session)

  * `zassenhaus_middle_left_le` / `zassenhaus_D_le` … normality/containment
    scaffolding, proved directly (mirrors the parent file's compiled API usage).
  * `half_diamond_iso` … the refined second isomorphism, structured exactly like
    the parent's `second_iso`.  Two analytic steps — surjectivity via `A ⊴ A'`
    conjugation, and the kernel computation `ker ψ = D` — are isolated as `sorry`s
    with full proof sketches inline.  Each is a concrete, closed sub-goal.
  * `zassenhaus_butterfly` … assembles the two half-diamonds.

  This file has NOT been machine-checked (build infrastructure was unavailable).
  Lemma names and tactic idioms were taken from the sibling compiled file
  `AbelRuffiniGaloisExtensionsOQ04.lean`.  Treat every `sorry` as an open,
  fully-specified obligation, not as an axiom.
-/

import Mathlib.Tactic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Basic

namespace AbelRuffiniGaloisExtensionsOQ04OQ03

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

-- ============================================================
-- PART I: The four subgroups and the middle datum
-- ============================================================

/-- Package of a Zassenhaus configuration: `A ⊴ A'` and `B ⊴ B'`. -/
structure ZConfig (G : Type*) [Group G] where
  A  : Subgroup G
  A' : Subgroup G
  B  : Subgroup G
  B' : Subgroup G
  hAle : A ≤ A'
  hAn  : (A.subgroupOf A').Normal
  hBle : B ≤ B'
  hBn  : (B.subgroupOf B').Normal

namespace ZConfig

variable (Z : ZConfig G)

/-- The upper "product" `A (A' ∩ B') = A ⊔ (A' ⊓ B')`.  Marked `abbrev` so that
    the containment lemmas below elaborate transparently. -/
abbrev upper : Subgroup G := Z.A ⊔ (Z.A' ⊓ Z.B')

/-- The lower "product" `A (A' ∩ B) = A ⊔ (A' ⊓ B)`. -/
abbrev lower : Subgroup G := Z.A ⊔ (Z.A' ⊓ Z.B)

/-- The middle subgroup `A' ∩ B'`. -/
abbrev mid : Subgroup G := Z.A' ⊓ Z.B'

/-- The common denominator `D = (A ∩ B') (A' ∩ B) = (A ⊓ B') ⊔ (A' ⊓ B)`. -/
abbrev D : Subgroup G := (Z.A ⊓ Z.B') ⊔ (Z.A' ⊓ Z.B)

lemma lower_le_upper : Z.lower ≤ Z.upper :=
  sup_le_sup_left (inf_le_inf_left Z.A' Z.hBle) Z.A

lemma mid_le_upper : Z.mid ≤ Z.upper := le_sup_right

-- ============================================================
-- PART II: Containments defining the common denominator `D`
-- ============================================================

/-- `A ⊓ B' ≤ A' ⊓ B'` — the left factor of `D` sits inside the middle. -/
lemma inf_A_B'_le_mid : Z.A ⊓ Z.B' ≤ Z.mid :=
  le_inf (inf_le_left.trans Z.hAle) inf_le_right

/-- `A' ⊓ B ≤ A' ⊓ B'` — the right factor of `D` sits inside the middle. -/
lemma inf_A'_B_le_mid : Z.A' ⊓ Z.B ≤ Z.mid :=
  le_inf inf_le_left (inf_le_right.trans Z.hBle)

/-- `D ≤ A' ⊓ B'`: the common denominator lies in the middle subgroup. -/
lemma D_le_mid : Z.D ≤ Z.mid :=
  sup_le Z.inf_A_B'_le_mid Z.inf_A'_B_le_mid

/-- `A' ⊓ B ≤ A ⊔ (A' ⊓ B) = lower`. -/
lemma inf_A'_B_le_lower : Z.A' ⊓ Z.B ≤ Z.lower := le_sup_right

/-- `A ⊓ B' ≤ lower` (through `A`). -/
lemma inf_A_B'_le_lower : Z.A ⊓ Z.B' ≤ Z.lower :=
  inf_le_left.trans le_sup_left

/-- `D ≤ lower`: everything in the denominator is already in `A (A' ∩ B)`. -/
lemma D_le_lower : Z.D ≤ Z.lower :=
  sup_le Z.inf_A_B'_le_lower Z.inf_A'_B_le_lower

-- ============================================================
-- PART III: The refined second isomorphism ("half-diamond")
-- ============================================================

/--
**Half-diamond isomorphism.**  The middle quotient by `D` is isomorphic to the
upper butterfly quotient:
```
    (A' ∩ B') ⧸ D  ≃*  A(A' ∩ B') ⧸ A(A' ∩ B).
```

Proof is the refined second isomorphism theorem, built exactly as the parent
file's `second_iso`: the homomorphism `ψ = mk' ∘ inclusion : (A'⊓B') → upper/lower`
is surjective with kernel `D.subgroupOf (A'⊓B')`, then
`QuotientGroup.quotientKerEquivOfSurjective` closes it.

Two obligations remain (isolated as `sorry`, each a concrete closed goal):
* `hφ_surj` — surjectivity, using `A ⊴ A'` to absorb the `A`-component of any
  element of `upper = A ⊔ (A'⊓B')` (conjugation `h⁻¹ a h ∈ A ≤ lower`), verbatim
  analogue of the parent's `hn_sup.conj_mem'` argument.
* `hker`   — kernel computation.  `h ∈ (A'⊓B') ∩ lower` iff `h ∈ D`: write
  `h = a·c` with `a ∈ A`, `c ∈ A'⊓B`; then `a = h c⁻¹ ∈ A ⊓ B'` (as `h ∈ B'`,
  `c ∈ B ≤ B'`, `h,c ∈ A'`), so `h = a·c ∈ (A⊓B') ⊔ (A'⊓B) = D`.  The reverse is
  `D_le_lower` together with `D_le_mid`.
-/
theorem half_diamond_iso
    (hlowerN : (Z.lower.subgroupOf Z.upper).Normal)
    (hDN : (Z.D.subgroupOf Z.mid).Normal) :
    Nonempty
      (Z.mid ⧸ Z.D.subgroupOf Z.mid ≃* Z.upper ⧸ Z.lower.subgroupOf Z.upper) := by
  haveI := hlowerN
  haveI := hDN
  -- ψ : (A' ⊓ B') → upper ⧸ lower,  via inclusion of `mid` into `upper`.
  let ψ : Z.mid →* Z.upper ⧸ Z.lower.subgroupOf Z.upper :=
    (mk' (Z.lower.subgroupOf Z.upper)).comp (inclusion Z.mid_le_upper)
  -- Kernel: exactly `D`, viewed inside `mid`.
  have hker : ψ.ker = Z.D.subgroupOf Z.mid := by
    -- ker ψ = { h ∈ mid : h ∈ lower } = mid ⊓ lower = D  (see docstring).
    sorry
  -- Surjectivity: absorb the `A`-part using `A ⊴ A'`.
  have hφ_surj : Function.Surjective ψ := by
    sorry
  haveI : (ψ.ker).Normal := by rw [hker]; infer_instance
  have e := QuotientGroup.quotientKerEquivOfSurjective ψ hφ_surj
  rw [hker] at e
  exact ⟨e.symm⟩

-- ============================================================
-- PART IV: The Zassenhaus butterfly lemma
-- ============================================================

/-- The mirror configuration obtained by swapping the roles of `(A, A')` and
    `(B, B')`.  Note `mirror.mid = B' ⊓ A'` and `mirror.D = (B ⊓ A') ⊔ (B' ⊓ A)`,
    which equal `Z.mid` and `Z.D` up to `inf`/`sup` commutativity. -/
def mirror : ZConfig G where
  A := Z.B; A' := Z.B'; B := Z.A; B' := Z.A'
  hAle := Z.hBle; hAn := Z.hBn; hBle := Z.hAle; hBn := Z.hAn

/--
**Zassenhaus butterfly lemma.**  For `A ⊴ A'` and `B ⊴ B'`,
```
    A(A' ∩ B') ⧸ A(A' ∩ B)  ≃*  B(B' ∩ A') ⧸ B(B' ∩ A).
```

Assembled from two `half_diamond_iso` applications sharing the middle quotient
`(A'∩B') ⧸ D`.  The bridge between `Z.mid`/`Z.D` and `mirror.mid`/`mirror.D` is
`inf_comm`/`sup_comm` (handled by `QuotientGroup.quotientMulEquivOfEq`), isolated
below as `bridge`.
-/
theorem zassenhaus_butterfly
    (hLU  : (Z.lower.subgroupOf Z.upper).Normal)
    (hLU' : ((Z.mirror).lower.subgroupOf (Z.mirror).upper).Normal)
    (hDN  : (Z.D.subgroupOf Z.mid).Normal)
    (hDN' : ((Z.mirror).D.subgroupOf (Z.mirror).mid).Normal) :
    Nonempty
      (Z.upper ⧸ Z.lower.subgroupOf Z.upper ≃*
        (Z.mirror).upper ⧸ (Z.mirror).lower.subgroupOf (Z.mirror).upper) := by
  obtain ⟨eL⟩ := Z.half_diamond_iso hLU hDN
  obtain ⟨eR⟩ := (Z.mirror).half_diamond_iso hLU' hDN'
  -- eL : Z.mid ⧸ Z.D ≃* Z.upper ⧸ Z.lower
  -- eR : mirror.mid ⧸ mirror.D ≃* mirror.upper ⧸ mirror.lower
  -- Bridge the two middle quotients: mirror.mid = Z.mid, mirror.D = Z.D (comm).
  have bridge :
      Nonempty
        (Z.mid ⧸ Z.D.subgroupOf Z.mid ≃*
          (Z.mirror).mid ⧸ (Z.mirror).D.subgroupOf (Z.mirror).mid) := by
    -- `mirror.mid = B' ⊓ A' = A' ⊓ B' = Z.mid` and `mirror.D = Z.D` by comm;
    -- transport via `QuotientGroup.quotientMulEquivOfEq` / `MulEquiv.subgroupCongr`.
    sorry
  obtain ⟨eM⟩ := bridge
  exact ⟨eL.symm.trans (eM.trans eR)⟩

-- ============================================================
-- PART V: Verification stubs
-- ============================================================

#check @half_diamond_iso
#check @zassenhaus_butterfly

end ZConfig

end AbelRuffiniGaloisExtensionsOQ04OQ03
