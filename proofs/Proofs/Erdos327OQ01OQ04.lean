/-
# Erdős #327 OQ-01 OQ-04: Linear Lower Bound on Sum-Divides-Product Pair Count

**Context**: OQ-01 established that all sum-divides-product pairs (a,b) with
a+b | ab arise from the parametrization (m·s·a', m·s·b') where gcd(a',b')=1
and s = a'+b'. The count D(N) = #{(a,b) : 1 ≤ a < b ≤ N, (a+b)|ab} is
conjectured to satisfy D(N) ~ C·N·log N.

**This file** establishes the lower bound D(N) ≥ ⌊N/6⌋ using the explicit
witness family {(3k, 6k) : 1 ≤ k ≤ ⌊N/6⌋}.

**Key computation**: 3k + 6k = 9k divides 3k·6k = 18k² = 9k·2k. ✓
-/

import Proofs.Erdos327OQ01
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos327OQ01OQ04

open Finset Nat

/-! ## The witness family -/

/-- The pair (3k, 6k) satisfies sum-divides-product for any k ≥ 1.
    Proof: 3k + 6k = 9k and 3k·6k = 18k² = 9k·(2k). -/
theorem threeK_sixK_dvd (k : ℕ) (hk : 0 < k) :
    (3 * k + 6 * k) ∣ (3 * k * (6 * k)) :=
  ⟨2 * k, by ring⟩

/-- The witness family: pairs (3k, 6k) for k ∈ [1, ⌊N/6⌋]. -/
def witnessFamily (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (N / 6)).image (fun k => (3 * k, 6 * k))

/-- The witness map k ↦ (3k, 6k) is injective. -/
theorem witnessInj : Function.Injective (fun k : ℕ => (3 * k, 6 * k)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  omega

/-- Each witness pair lies in the set sumDvdProdPairs N. -/
theorem witnessFamily_subset (N : ℕ) :
    witnessFamily N ⊆ sumDvdProdPairs N := by
  intro ⟨a, b⟩ h
  simp only [witnessFamily, mem_image, mem_Icc] at h
  obtain ⟨k, ⟨hk1, hkN⟩, rfl⟩ := h
  have hkpos : 0 < k := by omega
  -- 6k ≤ N: since k ≤ N/6, we have 6k ≤ 6·(N/6) ≤ N
  have h6kN : 6 * k ≤ N := by
    have hq : 6 * k ≤ 6 * (N / 6) := by omega
    have hle : N / 6 * 6 ≤ N := Nat.div_mul_le_self N 6
    linarith [show 6 * (N / 6) = N / 6 * 6 from by ring]
  simp only [sumDvdProdPairs, mem_filter, mem_product, mem_Icc]
  refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, h6kN⟩⟩, by omega, threeK_sixK_dvd k hkpos⟩

/-- The witness family has exactly ⌊N/6⌋ elements. -/
theorem witnessFamily_card (N : ℕ) : (witnessFamily N).card = N / 6 := by
  unfold witnessFamily
  rw [Finset.card_image_of_injective _ witnessInj]
  simp [Finset.Nat.card_Icc]
  omega

/-! ## Main lower bound -/

/-- **Lower bound**: The count of sum-divides-product pairs in [1,N] is at least ⌊N/6⌋.

    This proves D(N) → ∞ and grows at least linearly in N.
    The witness family {(3k,6k) : 1 ≤ k ≤ ⌊N/6⌋} has exactly ⌊N/6⌋ pairs,
    all contained in sumDvdProdPairs N. -/
theorem sumDvdProdPairs_lowerBound (N : ℕ) :
    N / 6 ≤ numSumDvdProdPairs N := by
  unfold numSumDvdProdPairs
  calc N / 6
      = (witnessFamily N).card := (witnessFamily_card N).symm
    _ ≤ (sumDvdProdPairs N).card :=
        Finset.card_le_card (witnessFamily_subset N)

/-- Corollary: D(N) → ∞. -/
theorem sumDvdProdPairs_unbounded :
    ∀ M : ℕ, ∃ N : ℕ, M ≤ numSumDvdProdPairs N := by
  intro M
  use 6 * M
  calc M = 6 * M / 6 := by omega
    _ ≤ numSumDvdProdPairs (6 * M) := sumDvdProdPairs_lowerBound _

end Erdos327OQ01OQ04
