/-
  Erdős Problem #70 — the FAITHFUL order-type arrow at β = ω.

  The WIP file `Erdos70WIP01.lean` proves the *formalized* conjecture
  `erdos_70_conjecture` unconditionally, but under the gallery's cardinality
  surrogate for order type (`HasOrderTypeAtLeast S H α ↔ α.card ≤ #H`).  Its
  standing next-step notes that the β = ω instance of the arrow is provable
  with the GENUINE order type, because any infinite subset of a well-ordered
  set has order type at least ω.  This file delivers that instance:

  * `omega0_le_type_subrel_of_infinite` — the key order-theoretic fact: an
    infinite subset of a well-ordered type has suborder type `≥ ω` (were the
    type a natural number `n`, `card_type` would force `#H = n < ℵ₀`).
  * `FaithfulArrowOmega κ m` — the arrow `κ → (ω, m)₂³` with the TRUE
    order-type clause: for every well-ordering `r` of a κ-sized `S` and every
    2-colouring of 3-subsets, either a colour-0 homogeneous `H` with
    `ω ≤ type (Subrel r H)`, or a colour-1 homogeneous `m`-set.
  * `infiniteRamsey3_imp_faithful_omega` / `faithful_omega_arrow_holds` —
    the faithful ω arrow follows from `InfiniteRamsey3`, hence holds
    UNCONDITIONALLY at the continuum via `infiniteRamsey3_holds`.
  * `faithfulArrowOmega_iff_partitionArrow_omega` — at β = ω (and only there)
    the faithful arrow and the surrogate arrow are EQUIVALENT: the surrogate
    side well-orders `S` by `WellOrderingRel`, the faithful side upgrades an
    infinite homogeneous set to suborder type `≥ ω` by the key fact.

  Faithfulness caveat, restated honestly: this settles β = ω only.  From
  β = ω² onward the genuine order-type arrow needs Erdős–Rado order-type
  machinery absent from Mathlib, and Erdős #70 itself remains open.

  0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.Erdos70WIP01

open Set Cardinal Ordinal

namespace Erdos70

/- ## The key order-theoretic fact -/

/-- **An infinite subset of a well-ordered type has suborder type at least
`ω`.**  If the type of `Subrel r (· ∈ H)` were below `ω` it would be some
natural `n` (`lt_omega0`), and taking cardinalities (`card_type`, `card_nat`)
would force `#H = n < ℵ₀`, contradicting the infinitude of `H`. -/
theorem omega0_le_type_subrel_of_infinite {S : Type*} (r : S → S → Prop)
    [IsWellOrder S r] {H : Set S} (hH : H.Infinite) :
    Ordinal.omega0 ≤ Ordinal.type (Subrel r (· ∈ H)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hlt
  have hcard := congrArg Ordinal.card hn
  rw [Ordinal.card_type, Ordinal.card_nat] at hcard
  have hfin : Cardinal.mk ↥H < Cardinal.aleph0 := by
    have h' : Cardinal.mk ↥H = (n : Cardinal) := hcard
    rw [h']
    exact Cardinal.natCast_lt_aleph0
  have hinf : Cardinal.aleph0 ≤ Cardinal.mk ↥H :=
    Cardinal.aleph0_le_mk_iff.mpr (Set.infinite_coe_iff.mpr hH)
  exact (not_le.mpr hfin) hinf

/- ## The faithful arrow at β = ω -/

/-- **The faithful partition arrow `κ → (ω, m)₂³`** — genuine order type, not
the cardinality surrogate: for every well-ordering `r` of a `κ`-sized set `S`
and every 2-colouring of its 3-subsets, either some colour-0 homogeneous set
has suborder type `≥ ω` under `r`, or some colour-1 homogeneous set has size
`≥ m`. -/
def FaithfulArrowOmega (κ : Cardinal) (m : ℕ) : Prop :=
  ∀ (S : Type) [DecidableEq S] (r : S → S → Prop) [IsWellOrder S r]
    (_ : Cardinal.mk S = κ) (c : Coloring S 3 2),
    (∃ H : Set S, Ordinal.omega0 ≤ Ordinal.type (Subrel r (· ∈ H)) ∧
      IsHomogeneous H 3 c 0) ∨
    (∃ H : Finset S, H.card ≥ m ∧ FinsetIsHomogeneous H 3 2 c 1)

/-- **`InfiniteRamsey3` yields the faithful ω arrow.**  The infinite
homogeneous set the Ramsey theorem supplies has suborder type `≥ ω` under any
well-ordering of the ambient set (`omega0_le_type_subrel_of_infinite`); the
colour-1 branch is the same finite extraction as in the surrogate reduction. -/
theorem infiniteRamsey3_imp_faithful_omega (h : InfiniteRamsey3) (m : ℕ) :
    FaithfulArrowOmega continuum_card m := by
  intro S _ r _ hS c
  obtain ⟨H, i, hHinf, hHom⟩ := h S hS c
  fin_cases i
  · exact Or.inl ⟨H, omega0_le_type_subrel_of_infinite r hHinf, hHom⟩
  · obtain ⟨t, hts, htc⟩ := hHinf.exists_subset_card_eq m
    refine Or.inr ⟨t, htc.ge, ?_⟩
    intro s hs hsub
    exact hHom s hs (subset_trans (Finset.coe_subset.mpr hsub) hts)

/-- **Unconditional faithful ω arrow at the continuum** — the first genuine
order-type instance of the Erdős #70 arrow in this development, via the
ultrafilter proof of `InfiniteRamsey3` in `Erdos70WIP01.lean`.  β ≥ ω²
onward still needs Erdős–Rado order-type machinery and remains open. -/
theorem faithful_omega_arrow_holds (m : ℕ) :
    FaithfulArrowOmega continuum_card m :=
  infiniteRamsey3_imp_faithful_omega infiniteRamsey3_holds m

/- ## Equivalence with the surrogate at β = ω -/

/-- **The faithful arrow implies the surrogate arrow at `ω`.**  Well-order the
surrogate's bare set by `WellOrderingRel`; the faithful colour-0 set has
suborder type `≥ ω`, so its cardinality is at least `card ω = ℵ₀`, which is
exactly the surrogate clause `HasOrderTypeAtLeast S H ω`. -/
theorem faithfulArrowOmega_imp_partitionArrow_omega {κ : Cardinal} {m : ℕ}
    (h : FaithfulArrowOmega κ m) :
    PartitionArrow κ Ordinal.omega0 m := by
  intro S _ hS c
  rcases h S WellOrderingRel hS c with ⟨H, htype, hHom⟩ | hr
  · refine Or.inl ⟨H, ?_, hHom⟩
    unfold HasOrderTypeAtLeast
    calc Ordinal.omega0.card = Cardinal.aleph0 := Ordinal.card_omega0
    _ ≤ Cardinal.mk ↥H := by
        have h' := Ordinal.card_le_card htype
        rwa [Ordinal.card_omega0, Ordinal.card_type] at h'
  · exact Or.inr hr

/-- **The surrogate arrow implies the faithful arrow at `ω`.**  A surrogate
colour-0 set has cardinality `≥ card ω = ℵ₀`, hence is infinite, hence has
suborder type `≥ ω` under ANY well-ordering (the key fact).  So at β = ω —
and only there — the gallery's cardinality surrogate loses nothing. -/
theorem partitionArrow_omega_imp_faithfulArrowOmega {κ : Cardinal} {m : ℕ}
    (h : PartitionArrow κ Ordinal.omega0 m) :
    FaithfulArrowOmega κ m := by
  intro S _ r _ hS c
  rcases h S hS c with ⟨H, htype, hHom⟩ | hr
  · refine Or.inl ⟨H, ?_, hHom⟩
    have hcard : Cardinal.aleph0 ≤ Cardinal.mk ↥H := by
      have h' : Ordinal.omega0.card ≤ Cardinal.mk ↥H := htype
      rwa [Ordinal.card_omega0] at h'
    exact omega0_le_type_subrel_of_infinite r
      (Set.infinite_coe_iff.mp (Cardinal.aleph0_le_mk_iff.mp hcard))
  · exact Or.inr hr

/-- **At β = ω the faithful and surrogate arrows are equivalent.**  This
certifies that the WIP file's unconditional `erdos_70_formalized_conjecture_holds`
is FAITHFUL at its ω instance; the surrogate only diverges from the genuine
partition relation at β ≥ ω², where suborder type can no longer be recovered
from cardinality alone (e.g. an ω-type subset of ω² is infinite but has
suborder type ω < ω²). -/
theorem faithfulArrowOmega_iff_partitionArrow_omega {κ : Cardinal} {m : ℕ} :
    FaithfulArrowOmega κ m ↔ PartitionArrow κ Ordinal.omega0 m :=
  ⟨faithfulArrowOmega_imp_partitionArrow_omega,
    partitionArrow_omega_imp_faithfulArrowOmega⟩

end Erdos70
