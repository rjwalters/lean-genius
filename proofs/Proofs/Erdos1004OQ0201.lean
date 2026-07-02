/-
Erdős Problem #1004 — the optimal exponent `c₀` for totient run lengths

Source: https://erdosproblems.com/1004
Parent formalization: Proofs/Erdos1004Problem.lean

Erdős #1004 asks: for every `c > 0`, if `x` is large, does there exist `n ≤ x`
such that `φ(n+1), …, φ(n+⌊(log x)^c⌋)` are all distinct?  The parent entry names
the "optimal exponent" `c₀` only informally (a bound variable inside
`SmallCaseConjecture`).  This file turns `c₀` into a genuine, well-defined
invariant of the problem and reframes the two conjecture shapes as single
quantitative statements about it:

  * `Erdos1004Conjecture` (holds for every `c > 0`)  ↔  `c₀ = ⊤`
  * `SmallCaseConjecture`  (holds on a band `0 < c < c₀`) ↔  `0 < c₀`

The engine is a single elementary fact — the set of *achievable exponents* is
an interval (downward closed): a long distinct run restricts to every shorter
run at the same witness `n`.  Everything here is verified with **0 axioms** and
no analytic number theory; the *value* of `c₀` (whether `> 0`, whether `= ⊤`)
is the open analytic core of Erdős #1004 and is deliberately left out.
-/
import Mathlib
import Proofs.Erdos1004Problem

open Real Filter Topology

namespace Erdos1004

/-! ## The achievable-exponent set -/

/-- `c` is an **achievable exponent** if, for all large `x`, some `n ≤ x` starts a
distinct totient run of length `⌊(log x)^c⌋`.  This is exactly the body of
`Erdos1004Conjecture` at a fixed `c`, and of the band in `SmallCaseConjecture`. -/
def AchievableExponent (c : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ n ≤ x, IsDistinctTotientRun n ⌊(Real.log x) ^ c⌋₊

/-- A distinct totient run restricts to any shorter prefix at the same start. -/
theorem run_prefix (n K K' : ℕ) (h : IsDistinctTotientRun n K) (hle : K' ≤ K) :
    IsDistinctTotientRun n K' := by
  intro i j hi hiK hj hjK hij
  exact h i j hi (hiK.trans hle) hj (hjK.trans hle) hij

/-- **Downward closure.**  If a large exponent is achievable, so is every smaller
nonnegative one — at the *same* witness `n`, by `run_prefix`. -/
theorem achievable_downward_closed {c c' : ℝ} (_hc' : 0 ≤ c') (hcc : c' ≤ c)
    (h : AchievableExponent c) : AchievableExponent c' := by
  have hlog : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ Real.log x :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [h, hlog] with x hx hlogx
  obtain ⟨n, hnx, hrun⟩ := hx
  refine ⟨n, hnx, ?_⟩
  refine run_prefix n _ _ hrun ?_
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hlogx hcc)

/-- The exponent `0` is achievable: `⌊(log x)^0⌋ = ⌊1⌋ = 1`, and every `n` starts
a distinct run of length `1`. -/
theorem zero_achievable : AchievableExponent 0 := by
  refine Filter.Eventually.of_forall (fun x => ⟨0, Nat.zero_le x, ?_⟩)
  rw [Real.rpow_zero, Nat.floor_one]
  exact distinctRun_one 0

/-! ## The optimal exponent as a supremum in `EReal` -/

/-- The set of achievable exponents, coerced into `EReal`. -/
def achievableSet : Set EReal :=
  (fun r : ℝ => (r : EReal)) '' {r : ℝ | 0 ≤ r ∧ AchievableExponent r}

/-- **The optimal exponent** `c₀ ∈ [0, ∞]`: the supremum of all achievable
exponents.  Taken in the complete lattice `EReal` so the value is total even in
the conjectured unbounded case (`c₀ = ⊤`), avoiding the junk value of a real
`sSup` on an unbounded set. -/
noncomputable def c₀ : EReal := sSup achievableSet

theorem coe_mem_achievableSet {r : ℝ} (hr0 : 0 ≤ r) (hr : AchievableExponent r) :
    ((r : ℝ) : EReal) ∈ achievableSet :=
  Set.mem_image_of_mem _ ⟨hr0, hr⟩

/-- `c₀ ≥ 0`, since `0` is achievable. -/
theorem zero_le_c₀ : (0 : EReal) ≤ c₀ := by
  have hmem : ((0 : ℝ) : EReal) ∈ achievableSet :=
    coe_mem_achievableSet le_rfl zero_achievable
  calc (0 : EReal) = ((0 : ℝ) : EReal) := (EReal.coe_zero).symm
    _ ≤ c₀ := le_sSup hmem

theorem c₀_ne_bot : c₀ ≠ ⊥ := fun hb => by
  have := zero_le_c₀
  rw [hb, le_bot_iff] at this
  exact (EReal.zero_ne_bot) this

/-! ## The two conjectures reframed as statements about `c₀` -/

/-- **The full conjecture is exactly `c₀ = ⊤`.**  If every positive exponent is
achievable the supremum is unbounded (`⊤`); conversely if `c₀ = ⊤`, every `c > 0`
lies below some achievable `r`, so is itself achievable by downward closure. -/
theorem conjecture_iff_c₀_top : Erdos1004Conjecture ↔ c₀ = ⊤ := by
  constructor
  · intro hconj
    by_contra htop
    -- `c₀` is a genuine real; pick an achievable exponent one larger, contradiction.
    have hcoe : ((c₀.toReal : ℝ) : EReal) = c₀ := EReal.coe_toReal htop c₀_ne_bot
    have hy0 : (0 : ℝ) ≤ c₀.toReal := by
      have h := zero_le_c₀
      rw [← hcoe] at h
      exact_mod_cast h
    have hach : AchievableExponent (c₀.toReal + 1) := hconj _ (by linarith)
    have hle : ((c₀.toReal + 1 : ℝ) : EReal) ≤ c₀ :=
      le_sSup (coe_mem_achievableSet (by linarith) hach)
    rw [← hcoe] at hle
    have : c₀.toReal + 1 ≤ c₀.toReal := by exact_mod_cast hle
    linarith
  · intro htop c hc
    have hlt : ((c : ℝ) : EReal) < c₀ := by rw [htop]; exact EReal.coe_lt_top c
    unfold c₀ achievableSet at hlt
    rw [lt_sSup_iff] at hlt
    obtain ⟨b, hbS, hcb⟩ := hlt
    obtain ⟨r, ⟨hr0, hrach⟩, rfl⟩ := hbS
    simp only at hcb
    have hcr : c < r := by exact_mod_cast hcb
    exact achievable_downward_closed hc.le hcr.le hrach

/-- **The weak (band) conjecture is exactly `0 < c₀`.** -/
theorem smallCase_iff_c₀_pos : SmallCaseConjecture ↔ 0 < c₀ := by
  constructor
  · rintro ⟨c₀', hc₀'pos, hband⟩
    have hach : AchievableExponent (c₀' / 2) := hband (c₀' / 2) (by linarith) (by linarith)
    have hle : ((c₀' / 2 : ℝ) : EReal) ≤ c₀ :=
      le_sSup (coe_mem_achievableSet (by linarith) hach)
    have hpos : (0 : EReal) < ((c₀' / 2 : ℝ) : EReal) := by
      rw [← EReal.coe_zero]
      exact_mod_cast (by linarith : (0 : ℝ) < c₀' / 2)
    exact lt_of_lt_of_le hpos hle
  · intro hpos
    unfold c₀ achievableSet at hpos
    rw [lt_sSup_iff] at hpos
    obtain ⟨b, hbS, hb0⟩ := hpos
    obtain ⟨r, ⟨hr0, hrach⟩, rfl⟩ := hbS
    simp only at hb0
    have hrpos : 0 < r := by
      rw [← EReal.coe_zero] at hb0
      exact_mod_cast hb0
    refine ⟨r, hrpos, fun c hc0 hcr => ?_⟩
    exact achievable_downward_closed hc0.le hcr.le hrach

end Erdos1004
