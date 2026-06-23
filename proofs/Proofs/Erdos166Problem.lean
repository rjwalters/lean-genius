/-
Erdős Problem #166: Ramsey Number R(4,k) Lower Bound

Source: https://erdosproblems.com/166
Status: SOLVED (Mattheus-Verstraete 2023)
Prize: $250

Statement:
Prove that R(4,k) >> k³/(log k)^O(1).

Resolution:
Mattheus and Verstraete [MaVe23] proved R(4,k) >> k³/(log k)⁴,
resolving the conjecture and earning the $250 Erdős prize.

Historical Timeline:
- Spencer (1977): R(4,k) >> (k log k)^{5/2}
- Ajtai-Komlós-Szemerédi (1980): R(4,k) << k³/(log k)²
- Mattheus-Verstraete (2023): R(4,k) >> k³/(log k)⁴ [SOLVED]

References:
- Erdős [Er90b], [Er91], [Er93 p.339], [Er97c]: Original problem
- Spencer [Sp77]: Early lower bound
- Ajtai-Komlós-Szemerédi [AKS80]: Upper bound
- Mattheus-Verstraete [MaVe23]: Solution
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2

open Finset

namespace Erdos166

/- ## Part I: Ramsey Number Definitions -/

/--
**Ramsey Number R(s,t):**
The minimum N such that any 2-coloring of edges of the complete graph K_N
contains either a monochromatic red K_s or a monochromatic blue K_t.

This is the fundamental object in Ramsey theory.
-/
noncomputable def RamseyNumber (s t : ℕ) : ℕ :=
  sInf { N : ℕ | ∀ (c : Sym2 (Fin N) → Bool),
    (∃ S : Finset (Fin N), S.card = s ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = true) ∨
    (∃ T : Finset (Fin N), T.card = t ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c s(x, y) = false) }

/-- Notation: R(s,t) for Ramsey numbers. -/
notation "R(" s "," t ")" => RamseyNumber s t

/- ## Part II: Basic Properties -/

/--
**Symmetry of Ramsey Numbers:**
R(s, t) = R(t, s) for all s, t.

This follows from swapping the colors red ↔ blue in any coloring.
-/
theorem ramsey_symmetric (s t : ℕ) : R(s, t) = R(t, s) := by
  simp [RamseyNumber]
  congr! 3
  constructor <;> intro h c <;> specialize h (fun x => !c x) <;> aesop

/--
**Ramsey Number R(1, t):**
R(1, t) = 1 for all t ≥ 1.

Any single vertex forms a monochromatic K_1 trivially.
-/
theorem ramsey_one_left (t : ℕ) (ht : t ≥ 1) : R(1, t) = 1 := by
  have h1 : ∀ c : (Sym2 (Fin 1) → Bool), (∃ S : Finset (Fin 1), S.card = 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c (Sym2.mk (x, y)) = true) ∨
      (∃ T : Finset (Fin 1), T.card = t ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
        c (Sym2.mk (x, y)) = false) := by
    exact fun c => Or.inl ⟨{0}, by simp +decide⟩
  refine' le_antisymm (Nat.sInf_le h1) _
  refine' le_csInf _ _
  · exact ⟨1, h1⟩
  · rintro (_ | _ | N) <;> simp +arith +decide
    exact fun x => ne_of_lt (lt_of_le_of_lt (Finset.card_le_univ _) (by simpa))

/--
**Ramsey Number R(2, t):**
R(2, t) = t for all t ≥ 2.

Either two vertices share a red edge, or all edges are blue forming K_t.
-/
theorem ramsey_two_left (t : ℕ) (ht : t ≥ 2) : R(2, t) = t := by
  refine' le_antisymm _ _
  · refine' Nat.sInf_le _
    by_contra! h
    norm_num +zetaDelta at *
    obtain ⟨c, hc⟩ := h
    obtain ⟨x, hx⟩ := hc.2 Finset.univ (by simpa)
    obtain ⟨y, hy, hxy, hyx⟩ := hx.2
    specialize hc
    have := hc.1 {x, y}
    simp_all +decide
    simp_all +decide [Sym2.eq_swap]
  · refine' le_csInf _ _
    · refine' ⟨t + 1, fun c => _⟩
      by_contra! h
      have h_blue : ∀ x y : Fin (t + 1), x ≠ y → c s(x, y) = false := by
        intros x y hxy
        have := h.1 {x, y}
        simp_all +decide [Finset.card_insert_of_notMem]
        cases this <;> simp_all +decide [Sym2.eq_swap]
      obtain ⟨x, hx, y, hy, hxy, h⟩ := h.2 (Finset.univ.erase 0)
          (by simp +decide [Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (t + 1)))])
      aesop
    · simp +zetaDelta at *
      intro b hb
      contrapose! hb
      use fun _ => Bool.false
      norm_num +zetaDelta at *
      exact ⟨fun x hx => by
        obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 (by linarith)
        exact ⟨y, hy, z, hz, hyz⟩,
        fun x hx => by linarith [show x.card ≤ b by
          exact le_trans (Finset.card_le_univ _) (by simpa)]⟩

/- ## Part III: Known Exact Values -/

/--
**R(3,3) = 6:**
The most famous small Ramsey number. Any 2-coloring of K_6 contains
a monochromatic triangle. K_5 can be 2-colored without a monochromatic triangle.
-/
/--
**R(4,4) = 18:**
Any 2-coloring of K_18 contains a monochromatic K_4.
Finding the exact value required extensive computation.
-/
/--
**R(4,5) = 25:**
The largest exactly known off-diagonal Ramsey number with s = 4.
-/
/--
**R(3,k) Bounds:**
The best known bounds for R(3,k) are
c₁ · k²/log k ≤ R(3,k) ≤ c₂ · k²/log k.
-/
/- ## Part IV: Historical Lower Bounds for R(4,k) -/

/--
**Spencer (1977):**
R(4,k) ≥ c · (k log k)^{5/2} for some constant c > 0.

This was the best lower bound for over 40 years, using
probabilistic constructions with dependent random choices.
-/
/- ## Part V: Upper Bound (Ajtai-Komlós-Szemerédi) -/

/--
**Ajtai-Komlós-Szemerédi (1980):**
R(4,k) ≤ C · k³/(log k)² for some constant C > 0.

This established that R(4,k) grows like k³ up to polylogarithmic factors.
The proof uses a clever greedy coloring algorithm.
-/
axiom aks_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≤ C * k^3 / (Real.log k)^2


/- ## Part VI: The Solution (Mattheus-Verstraete 2023) -/

/--
**Mattheus-Verstraete (2023):**
R(4,k) ≥ c · k³/(log k)⁴ for some constant c > 0.

This SOLVED Erdős Problem #166, earning the $250 prize.
The proof uses algebraic constructions from finite geometry.
-/
axiom mattheus_verstraete :
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≥ c * k^3 / (Real.log k)^4


/- ## Part VII: Erdős's Conjecture (SOLVED) -/

/--
**Erdős Problem #166 Statement:**
There exist constants c > 0 and A > 0 such that for all sufficiently large k,
R(4,k) ≥ c · k³/(log k)^A.

This asks for the lower bound to match the upper bound up to
polylogarithmic factors.
-/
def Erdos166Statement : Prop :=
  ∃ c : ℝ, ∃ A : ℝ, c > 0 ∧ A > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    (R(4, k) : ℝ) ≥ c * k^3 / (Real.log k)^A

/--
**Erdős Problem #166 is SOLVED:**
Mattheus-Verstraete proves the statement with A = 4.
-/
theorem erdos_166_solved : Erdos166Statement := by
  obtain ⟨c, hc, hbound⟩ := mattheus_verstraete
  exact ⟨c, 4, hc, by norm_num, hbound⟩

/--
**Current Best Bounds for R(4,k):**
c · k³/(log k)⁴ ≤ R(4,k) ≤ C · k³/(log k)²

The gap is only in the exponent of log k (4 vs 2).
-/
theorem current_bounds :
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ k : ℕ, k ≥ 3 →
    c * k^3 / (Real.log k)^4 ≤ R(4, k) ∧
    (R(4, k) : ℝ) ≤ C * k^3 / (Real.log k)^2 := by
  obtain ⟨c, hc, hc_bound⟩ := mattheus_verstraete
  obtain ⟨C, hC, hC_bound⟩ := aks_upper_bound
  exact ⟨c, C, hc, hC, fun k hk => ⟨hc_bound k hk, hC_bound k hk⟩⟩

/- ## Part VIII: Summary -/

/--
**Summary of Erdős Problem #166:**

PROBLEM: Prove R(4,k) >> k³/(log k)^{O(1)}.

STATUS: SOLVED (Mattheus-Verstraete 2023)

PRIZE: $250 (collected)

ANSWER: YES. R(4,k) ≥ c · k³/(log k)⁴ for some c > 0.

KEY INSIGHT: Algebraic graph constructions from finite geometry
achieve bounds that probabilistic methods could not reach.

CURRENT BOUNDS:
- Lower: c · k³/(log k)⁴ ≤ R(4,k) [Mattheus-Verstraete 2023]
- Upper: R(4,k) ≤ C · k³/(log k)² [Ajtai-Komlós-Szemerédi 1980]
- Remaining gap: only the exponent of log k

HISTORICAL TIMELINE:
- 1977: Spencer proves R(4,k) >> (k log k)^{5/2}
- 1980: AKS proves R(4,k) << k³/(log k)²
- 2023: Mattheus-Verstraete proves R(4,k) >> k³/(log k)⁴ [SOLVED]

A breakthrough result bridging 43 years of effort in Ramsey theory.
-/
theorem erdos_166_status :
    -- Erdős Problem #166 is solved
    Erdos166Statement := erdos_166_solved

/--
**The bounds match up to logarithmic factors:**
Both lower and upper bounds are Θ(k³/(log k)^α) for some α.
-/
theorem logarithmic_gap :
    ∃ α β : ℝ, 2 ≤ α ∧ β ≤ 4 ∧
    ∀ k : ℕ, k ≥ 3 → ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      c * k^3 / (Real.log k)^β ≤ R(4, k) ∧
      (R(4, k) : ℝ) ≤ C * k^3 / (Real.log k)^α := by
  use 2, 4
  constructor
  · norm_num
  constructor
  · norm_num
  intro k hk
  obtain ⟨c, hc, hc_bound⟩ := mattheus_verstraete
  obtain ⟨C, hC, hC_bound⟩ := aks_upper_bound
  exact ⟨c, C, hc, hC, hc_bound k hk, hC_bound k hk⟩

end Erdos166
