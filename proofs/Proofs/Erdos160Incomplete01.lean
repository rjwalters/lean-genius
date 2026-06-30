/-
  Erdős Problem #160 — incomplete-01
  The exact small-N floor of the 4-AP 3-diverse colouring number.

  `h(N)` is the least number of colours needed to colour `{1,…,N}` so that every
  four-term arithmetic progression receives at least three distinct colours.
  Erdős #160 (OPEN) asks for the growth of `h(N)`; the known bounds are deep
  (`h(N) ≪ N^{2/3}`, sharpened by Hunter, and `h(N) ≫ exp(c(log N)^{1/9})`) and
  appear in the parent file `Erdos160Problem.lean` only as *axioms*.

  This file proves, with no axioms and no `sorry`, the elementary but exact base of
  the function — the part the asymptotics build on but never state:

    * `not_achievable_le_two` : two colours can never be 3-diverse once a 4-AP
      exists (a 4-term progression has only 4 elements, so ≤ 2 colours give ≤ 2
      distinct values < 3);
    * `h_ge_three` : hence `h(N) ≥ 3` for every `N ≥ 4` — a certain lower bound,
      sitting below all the axiomatised asymptotics;
    * `h_four` : `h(4) = 3` exactly — the first nontrivial value, attained by the
      colouring `1,2,3,1`.

  Together with the parent file's `h(N) ≤ 1` for `N ≤ 3`, this pins the function
  completely up to the first 4-AP: `h = 0,1,1,1` on `N = 0,1,2,3` and `h(4) = 3`.

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib
import Proofs.Erdos160Problem

namespace Erdos160.Incomplete01

open Erdos160

/-- **Two colours are never enough once a 4-AP exists.**  A four-term arithmetic
    progression has four elements; a colouring with at most two colours assigns them
    at most two distinct values, so the 3-diversity requirement (`≥ 3` colours on the
    progression `1,2,3,4`) cannot hold for `N ≥ 4`. -/
theorem not_achievable_le_two {n k : ℕ} (hn : 4 ≤ n) (hk : k ≤ 2) :
    ¬ Achievable n k := by
  rintro ⟨c, hc⟩
  -- the progression a = 1, d = 1 occupies positions 0,1,2,3, valid since n ≥ 4
  have hap : Is4AP n 1 1 := ⟨le_refl 1, le_refl 1, by omega⟩
  have h0 : (1 : ℕ) - 1 < n := by omega
  have h1 : (1 : ℕ) + 1 - 1 < n := by omega
  have h2 : (1 : ℕ) + 2 * 1 - 1 < n := by omega
  have h3 : (1 : ℕ) + 3 * 1 - 1 < n := by omega
  have hcard := hc 1 1 hap h0 h1 h2 h3
  -- but the number of distinct colours on any four points is at most k ≤ 2
  have hle : colorCount4 c ⟨1 - 1, h0⟩ ⟨1 + 1 - 1, h1⟩
      ⟨1 + 2 * 1 - 1, h2⟩ ⟨1 + 3 * 1 - 1, h3⟩ ≤ k := by
    unfold colorCount4
    have hcl := Finset.card_le_univ
      ({c ⟨1 - 1, h0⟩, c ⟨1 + 1 - 1, h1⟩, c ⟨1 + 2 * 1 - 1, h2⟩,
        c ⟨1 + 3 * 1 - 1, h3⟩} : Finset (Fin k))
    simpa using hcl
  omega

/-- **Certain lower bound `h(N) ≥ 3` for `N ≥ 4`.**  Every colouring with `< 3`
    colours fails on the progression `1,2,3,4`, so the minimum `h(N)` is at least 3.
    This is the unconditional floor underneath the (axiomatised) asymptotic bounds. -/
theorem h_ge_three {n : ℕ} (hn : 4 ≤ n) : 3 ≤ h n := by
  by_contra hlt
  push_neg at hlt
  exact not_achievable_le_two hn (by omega) (h_achievable n)

/-- **Exact first value `h(4) = 3`.**  The colouring `1,2,3,1` (i.e. `![0,1,2,0]`)
    gives the single 4-AP `1,2,3,4` the three colours `{0,1,2}`, so three colours
    suffice; and `h_ge_three` shows two never do. -/
theorem h_four : h 4 = 3 := by
  refine le_antisymm ?_ (h_ge_three (by norm_num))
  apply Nat.sInf_le
  refine ⟨(![0, 1, 2, 0] : Fin 4 → Fin 3), ?_⟩
  intro a d hap ha ha1 ha2 ha3
  obtain ⟨hd, ha', hle⟩ := hap
  -- for N = 4 the only valid 4-AP is a = 1, d = 1
  obtain ⟨rfl, rfl⟩ : a = 1 ∧ d = 1 := by omega
  -- the four positions are 0,1,2,3 (proofs irrelevant); colours are 0,1,2,0
  show colorCount4 (![0, 1, 2, 0] : Fin 4 → Fin 3) 0 1 2 3 ≥ 3
  decide

end Erdos160.Incomplete01
