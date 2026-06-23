/-
# Szemerédi Density: k-AP-Free Sets Are o(N)

Szemerédi's theorem in density form: k-AP-free sets A ⊆ {0, ..., N-1}
have vanishing density |A| / N → 0 as N → ∞.

**Main results:**
- `szemeredi_vanishing_density` — sequences of AP-free sets have density → 0 (all k ≥ 1)
- `roth_density_isLittleO` — k=3 case as IsLittleO, directly from Mathlib
- `ap_free_density_isLittleO_k3` — density o(N) for sequences of 3-AP-free sets
- `szemeredi_density_full` — main theorem alias

**Status:**
- k=1,2: Proved (trivial)
- k=3: Proved via Mathlib's `rothNumberNat_isLittleO_id`
- k≥4: Axiomatized (hypergraph regularity not in Mathlib)

**New vs `SzemerediTheorem.lean`:**
- `Filter.Tendsto` / `IsLittleO` formulation of the density bound
- Sequence-of-sets formulation: if each A_N is k-AP-free, then |A_N|/N → 0
- Explicit Mathlib `rothNumberNat_isLittleO_id` reference for k=3

**References:**
- Szemerédi (1975), Gowers (2001)
- Mathlib `Mathlib.Combinatorics.Additive.Corner.Roth`
-/

import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic
import Proofs.SzemerediTheorem

namespace SzemerediDensity

open Szemeredi Asymptotics Filter

/-!
## Density Tends to Zero: Sequence Formulation

For any sequence of k-AP-free sets A_N ⊆ {0,...,N-1}, |A_N|/N → 0.
-/

/-- **Szemerédi Vanishing Density**: Any sequence of k-AP-free sets has density → 0.

For all k ≥ 1: if each A_N ⊆ {0,...,N-1} is k-AP-free, then |A_N|/N → 0. -/
theorem szemeredi_vanishing_density (k : ℕ) (hk : k ≥ 1)
    (A : ℕ → Finset ℕ)
    (hA_sub : ∀ N, A N ⊆ Finset.range N)
    (hA_free : ∀ N, IsAPFree (↑(A N)) k) :
    Filter.Tendsto (fun N => (A N).card / (N : ℝ)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := ap_free_density_bound k hk (ε / 2) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have h1 : 1 ≤ N := (le_max_right N₀ 1).trans hN
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_succ_le h1
  have hN_ge_N₀ : N₀ ≤ N := (le_max_left N₀ 1).trans hN
  have hcard := hN₀ N hN_ge_N₀ (A N) (hA_sub N) (hA_free N)
  rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hN_pos)),
      div_lt_iff₀ hN_pos]
  nlinarith

/-!
## k=3: Roth's Theorem via Mathlib IsLittleO
-/

/-- **Roth's Theorem** in IsLittleO form (directly from Mathlib).

The maximum size of a 3-AP-free subset of {0,...,N-1} is o(N). -/
theorem roth_density_isLittleO :
    IsLittleO atTop (fun N => (rothNumberNat N : ℝ)) (fun N => (N : ℝ)) :=
  rothNumberNat_isLittleO_id

/-- For k=3: any sequence of 3-AP-free sets has density o(N). -/
theorem ap_free_density_isLittleO_k3 (A : ℕ → Finset ℕ)
    (hA_sub : ∀ N, A N ⊆ Finset.range N)
    (hA_free : ∀ N, IsAPFree (↑(A N)) 3) :
    IsLittleO atTop (fun N => ((A N).card : ℝ)) (fun N => (N : ℝ)) := by
  -- Derive from the Tendsto statement via isLittleO_iff_tendsto
  rw [isLittleO_iff_tendsto (fun N hN => by
    have hN0 : N = 0 := by exact_mod_cast hN
    subst hN0
    have hA0 : A 0 = ∅ := Finset.subset_empty.mp (Finset.range_zero ▸ hA_sub 0)
    simp [hA0])]
  exact szemeredi_vanishing_density 3 (by omega) A hA_sub hA_free

/-!
## Main Density Theorem

The full Szemerédi density theorem assembling all cases.
k≥4 relies on the `szemeredi_k_ge_4` axiom from SzemerediTheorem.lean.
-/

/-- **Szemerédi Density Theorem**: k-AP-free sets have vanishing density, all k ≥ 1.

k=1,2: trivial; k=3: Roth via Mathlib; k≥4: axiomatized (hypergraph regularity needed). -/
theorem szemeredi_density_full (k : ℕ) (hk : k ≥ 1)
    (A : ℕ → Finset ℕ)
    (hA_sub : ∀ N, A N ⊆ Finset.range N)
    (hA_free : ∀ N, IsAPFree (↑(A N)) k) :
    Filter.Tendsto (fun N => (A N).card / (N : ℝ)) Filter.atTop (nhds 0) :=
  szemeredi_vanishing_density k hk A hA_sub hA_free

/-!
## Note on Gowers Uniformity

Gowers (2001) proved: k-AP-free A ⊆ [N] implies ‖𝟏_A‖_{U^{k-1}} → 0.
Gowers norms are NOT in Mathlib 4.26. A full Gowers-norm formalization would need:
- U^k norm definition on ZMod N (~200 lines)
- Cauchy-Schwarz for Gowers inner product (~100 lines)
- AP counting lemma via Gowers norms (~300 lines)
- U^2 inverse theorem (Fourier, k=3 case) (~500 lines)

This is a future milestone; the density-zero statement above covers all k.
-/

end SzemerediDensity
