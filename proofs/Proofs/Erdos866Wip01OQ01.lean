import Proofs.Erdos866Wip01

/-
# Erdős Problem #866 — the exact threshold `g_3(N) = 1` under the repeated-index definition

## The problem

For `k ≥ 3`, Erdős #866 asks for the minimal threshold `g_k(N)` such that **every**
`A ⊆ {1,…,2N}` with `|A| ≥ N + g_k(N)` contains all pairwise sums `b_i + b_j` of some
`k`-element family `b_1,…,b_k`.  The base file `Erdos866Problem.lean` formalizes a
configuration as a map `b : Fin k → ℤ` (with `HasAllPairwiseSums A b` meaning every
pairwise sum lands in `A`) and the file `Erdos866Wip01.lean` proves the lower bound
`g_k(N) ≥ 1` uniformly in `k` via the parity construction (the `N` odd numbers force no
configuration).

## What this file proves

This file establishes the **matching upper bound `g_3(N) ≤ 1`**, hence pins down the
exact value

  `g_3(N) = 1`

*for the definition used in these files*, where the configuration map `b : Fin 3 → ℤ` is
**not required to be injective**.  The mechanism is a single-element degeneracy:

* `config_of_even_mem` — if `A` contains any **even** number `e`, then the constant family
  `b ≡ e/2` has all three pairwise sums equal to `e ∈ A`, so `A` already admits a
  3-configuration.
* `exists_even_of_large` — any `A ⊆ {1,…,2N}` with `|A| ≥ N + 1` must contain an even
  number (the `N` odd numbers cannot fit `N + 1` elements).
* `config_of_large` / `guarantees_one` — combining the two, every `A ⊆ {1,…,2N}` of size
  `≥ N + 1` admits a 3-configuration, i.e. `Guarantees N 3 1`.
* `g_3_least_threshold` — with `Erdos866Wip01.g_k_ge_one`, the least guaranteeing
  threshold is exactly `1`.

## Honesty / scope

The classical value of Erdős #866 for `k = 3` is `g_3(N) = 2`, established with a family
of **three distinct** integers.  The value proved here is `1`, and the gap is *entirely*
due to the relaxation in the base definition: a configuration `b : Fin 3 → ℤ` is allowed
to be constant, so a lone even element `e` (via `b ≡ e/2`, whose three pairwise sums all
equal `e`) is a valid — but degenerate — 3-configuration.  This file therefore does two
honest things at once: it computes the *exact* threshold for the formalization actually in
the gallery (`g_3 = 1`, upgrading the file's `≥ 1` to an equality), and it makes explicit,
via `config_of_even_mem`, precisely why that formalization collapses the classical `2` to
`1`.  Recovering the classical `g_3 = 2` requires strengthening `HasAllPairwiseSums` to
demand an injective family; that is a genuinely harder statement and is not attempted here.

Theorems: 6, Axioms: 0, Sorries: 0
-/

open Finset

namespace Erdos866Wip01OQ01

open Erdos866 Erdos866Wip01

/-! ## The single-element degeneracy -/

/-- **A lone even element already forms a 3-configuration.**  If `e ∈ A` is even, the
constant family `b ≡ e/2 : Fin 3 → ℤ` has every pairwise sum equal to `e ∈ A`.  This is
the mechanism collapsing the threshold to `1`: injectivity of `b` is *not* required, so no
three *distinct* integers are needed. -/
theorem config_of_even_mem {A : Finset ℕ} {e : ℕ} (he : e ∈ A) (heven : Even e) :
    ∃ b : Fin 3 → ℤ, HasAllPairwiseSums A b := by
  obtain ⟨m, hm⟩ := heven
  refine ⟨fun _ => (m : ℤ), ?_⟩
  intro i j _
  have hval : ((m : ℤ) + (m : ℤ)).toNat = e := by omega
  rw [hval]
  exact he

/-! ## Large sets contain an even number -/

/-- Any `A ⊆ {1,…,2N}` with `|A| ≥ N + 1` contains an even number: otherwise `A` would be
a subset of the `N` odd numbers and could not have `N + 1` elements. -/
theorem exists_even_of_large {N : ℕ} {A : Finset ℕ} (hAsub : A ⊆ Erdos866.Interval N)
    (hcard : N + 1 ≤ A.card) : ∃ e ∈ A, Even e := by
  by_contra h
  push_neg at h
  have hsub : A ⊆ oddNumbers N := by
    intro a ha
    have haI := hAsub ha
    have hodd : a % 2 = 1 := Nat.not_even_iff.mp (h a ha)
    simp only [oddNumbers, Finset.mem_filter]
    exact ⟨haI, hodd⟩
  have hle := Finset.card_le_card hsub
  rw [oddNumbers_card] at hle
  omega

/-! ## The upper bound `g_3(N) ≤ 1` -/

/-- **Every `A ⊆ {1,…,2N}` of size `≥ N + 1` admits a 3-configuration.**  Such an `A`
contains an even element `e` (`exists_even_of_large`), and `e` alone yields a configuration
(`config_of_even_mem`). -/
theorem config_of_large {N : ℕ} {A : Finset ℕ} (hAsub : A ⊆ Erdos866.Interval N)
    (hcard : N + 1 ≤ A.card) : ∃ b : Fin 3 → ℤ, HasAllPairwiseSums A b := by
  obtain ⟨e, he, heven⟩ := exists_even_of_large hAsub hcard
  exact config_of_even_mem he heven

/-- **`g_3(N) ≤ 1`.**  A threshold of `1` already guarantees a 3-configuration. -/
theorem guarantees_one (N : ℕ) : Guarantees N 3 1 := by
  intro A hAsub hcard
  exact config_of_large hAsub (by omega)

/-! ## The exact threshold `g_3(N) = 1` -/

/-- **The least guaranteeing threshold for `k = 3` is exactly `1`.**  Combining the upper
bound `guarantees_one` with the lower bound `Erdos866Wip01.g_k_ge_one`: `1` guarantees a
configuration, and no smaller threshold does.  So `g_3(N) = 1` for the (non-injective)
configuration definition used in these files. -/
theorem g_3_least_threshold (N : ℕ) :
    Guarantees N 3 1 ∧ ∀ g, Guarantees N 3 g → 1 ≤ g :=
  ⟨guarantees_one N, fun _ hG => g_k_ge_one N (by norm_num) hG⟩

/-- **`g_3(N) = 1` as a two-sided statement:** `1` guarantees a 3-configuration but `0`
does not.  Compare the classical `g_3(N) = 2`, which requires an *injective* family; the
drop to `1` is exactly the degeneracy exhibited by `config_of_even_mem`. -/
theorem g_3_eq_one (N : ℕ) : Guarantees N 3 1 ∧ ¬ Guarantees N 3 0 :=
  ⟨guarantees_one N, not_guarantees_zero N (by norm_num)⟩

end Erdos866Wip01OQ01
