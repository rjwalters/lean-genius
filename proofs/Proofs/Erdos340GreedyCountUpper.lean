/-
# Erdős Problem #340: the growth bracket for the greedy Sidon sequence

The greedy (Mian–Chowla) Sidon sequence `a₀ < a₁ < ⋯` is constructed, fully and
axiom-free, in `Proofs.Erdos340GreedySidon`.  Its counting function

  `greedyCount N = #{ k : aₖ ≤ N }`

(`Proofs.Erdos340GreedyRpowBound`) already has a verified **lower** bound

  `greedyCount_rpow_lower : ∃ C > 0, ∀ N > 0,  C · N^{1/3} ≤ greedyCount N`,

coming from the cubic growth bound `aₙ ≤ 2(n+1)³`.

This file supplies the matching **upper** bound.  The values counted by
`greedyCount N` form a Sidon set contained in `{0,…,N}`, so the Erdős–Turán /
Lindström bound `Erdos340.sidon_card_le_sqrt` (proved in
`Proofs.Erdos340SidonErdosTuran` by optimising the window inequality of
`Proofs.Erdos340GreedySidonOQ02`) applies verbatim:

  `greedyCount_le_sqrt :  greedyCount N ≤ ⌊√N⌋ + ⌊⁴√N⌋ + 2.`

Together these give the **growth bracket**

  `C · N^{1/3} ≤ greedyCount N ≤ √N + ⁴√N + 2`,

which is the precise quantitative location of the open problem: the lower bound
has exponent `1/3`, the upper bound exponent `1/2`, and Erdős #340 asks whether
the greedy sequence actually attains the upper exponent `N^{1/2−ε}`.  The
`1/3`-vs-`1/2` gap is the open problem; both bookends are here verified and
axiom-free.
-/
import Mathlib
import Proofs.Erdos340GreedySidon
import Proofs.Erdos340GreedyRpowBound
import Proofs.Erdos340SidonErdosTuran

namespace Erdos340

open Finset

/-- **Upper bound on the greedy Sidon counting function.**

`greedyCount N ≤ ⌊√N⌋ + ⌊√⌊√N⌋⌋ + 2`.

The greedy terms `≤ N` are the image, under the (injective) greedy sequence, of
the index set counted by `greedyCount`; this image is a Sidon set contained in
`{0,…,N}`, so the verified Erdős–Turán bound `sidon_card_le_sqrt` applies. -/
theorem greedyCount_le_sqrt (N : ℕ) :
    greedyCount N ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 2 := by
  -- The index set counted by `greedyCount`, and its value image.
  set F : Finset ℕ := (Finset.range (N + 1)).filter (fun k => greedySidonSeq k ≤ N) with hF
  set B : Finset ℕ := F.image greedySidonSeq with hB
  have hinj : Function.Injective greedySidonSeq := greedySidonSeq_strictMono.injective
  -- `|B| = greedyCount N` because the greedy sequence is injective.
  have hcardB : B.card = greedyCount N := by
    rw [hB, Finset.card_image_of_injective _ hinj, greedyCount, hF]
  -- `B` is Sidon: it is a subset of the (Sidon) image of `range (N+1)`.
  have hsub : B ⊆ Finset.image greedySidonSeq (Finset.range (N + 1)) := by
    rw [hB]
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have hBsidon : IsSidon B := (greedySidonSeq_isSidon N).subset hsub
  -- Every counted value is `≤ N`.
  have hBmem : ∀ b ∈ B, b ≤ N := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    rw [hF, Finset.mem_filter] at hk
    exact hk.2
  -- Apply the Erdős–Turán upper bound.
  have h := sidon_card_le_sqrt B hBsidon N hBmem
  rwa [hcardB] at h

/-- **The Erdős #340 growth bracket (real form).**

For the greedy/Mian–Chowla Sidon sequence the counting function satisfies

  `C · N^{1/3} ≤ greedyCount N ≤ √N + ⁴√N + 2`

for a fixed `C > 0` and all `N > 0`.  Both bookends are verified and axiom-free;
the gap between the `1/3` and `1/2` exponents is exactly the content of the open
problem Erdős #340. -/
theorem greedyCount_bracket :
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → C * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (greedyCount N : ℝ)) ∧
      (∀ N : ℕ, (greedyCount N : ℝ) ≤ Real.sqrt N + Real.sqrt (Real.sqrt N) + 2) := by
  refine ⟨greedyCount_rpow_lower, fun N => ?_⟩
  -- Lift the integer bound `⌊√N⌋ + ⌊⁴√N⌋ + 2` to the real bound `√N + ⁴√N + 2`.
  have hnat := greedyCount_le_sqrt N
  have h1 : (Nat.sqrt N : ℝ) ≤ Real.sqrt N :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast Nat.sqrt_le' N)
  have h2 : (Nat.sqrt (Nat.sqrt N) : ℝ) ≤ Real.sqrt (Real.sqrt N) :=
    (Real.le_sqrt (by positivity) (Real.sqrt_nonneg _)).mpr (by
      have h := (by exact_mod_cast Nat.sqrt_le' (Nat.sqrt N) :
        (Nat.sqrt (Nat.sqrt N) : ℝ) ^ 2 ≤ (Nat.sqrt N : ℝ))
      linarith [h1])
  have hcast : (greedyCount N : ℝ) ≤ (Nat.sqrt N : ℝ) + (Nat.sqrt (Nat.sqrt N) : ℝ) + 2 := by
    exact_mod_cast hnat
  linarith

end Erdos340
