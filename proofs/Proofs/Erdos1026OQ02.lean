import Mathlib

/-
# erdos-1026-oq-02: Does the monotonic-subsequence bound extend to *approximate* monotonicity?

Erdős Problem #1026 concerns monotonic subsequences: by Erdős–Szekeres, every sequence of
`k² + 1` distinct reals contains a monotonic subsequence of length `k + 1`, and the
optimization variant studies the maximum *sum* carried by such a subsequence.

**OQ-02** asks whether these guarantees survive when the rigid notion of monotonicity is
relaxed to *ε-approximate* monotonicity: a subsequence whose later values may dip below
earlier ones by at most a fixed tolerance `ε ≥ 0` (and dually for decreasing). This is the
natural robust variant — exact monotonicity is brittle under measurement noise, and the
question is whether the same length guarantees hold, or whether the slack `ε` permits
provably longer subsequences (a better bound).

This file pins the question down and proves, axiom-free, the **easy half** of the answer:
approximate monotonicity is a genuine *relaxation* of exact monotonicity, so every length
guarantee for monotonic subsequences transfers verbatim to approximate ones (the classical
`k + 1` lower bound persists). Concretely:

* at `ε = 0` the approximate notion coincides exactly with strict monotonicity
  (`isApproxIncreasing_zero_iff`);
* the tolerance is monotone — a larger `ε` is a weaker constraint
  (`isApproxIncreasing_mono`);
* every exactly monotonic subsequence is `ε`-approximately monotonic for `ε ≥ 0`
  (`IsIncreasing.isApproxIncreasing`, `IsMonotonic.isApproxMonotonic`);
* hence existence transfers: a guaranteed monotonic subsequence of length `m` yields an
  `ε`-approximately monotonic one of the same length
  (`exists_approxMonotonic_of_exists_monotonic`). Every classical lower bound is inherited.

What is **left open** (the hard, interesting direction) is whether the slack is ever
*strictly* helpful — whether some sequences admit `ε`-approximately monotonic subsequences
strictly longer than any exactly monotonic one. The notions genuinely differ
(`approxIncreasing_not_increasing` exhibits an `ε`-approximately increasing subsequence that
is not increasing), so the question is nonvacuous; quantifying the gain is the open content.

The framework is self-contained (it re-states the minimal `Subsequence` interface of
`Erdos1026Problem.lean` rather than importing it, since that file depends on
`Archive.Wiedijk100Theorems`). No axioms, no sorries.
-/

open Finset

namespace Erdos1026OQ02

/-- A sequence of `n` real numbers (mirrors `Erdos1026.RealSeq`). -/
def RealSeq (n : ℕ) := Fin n → ℝ

/-- A subsequence, given by a strictly increasing index map (mirrors
`Erdos1026.Subsequence`). -/
structure Subsequence (n m : ℕ) where
  indices : Fin m → Fin n
  strictMono : StrictMono indices

variable {n m : ℕ}

/-- A subsequence is (exactly) increasing: its values strictly increase. -/
def IsIncreasing (seq : RealSeq n) (sub : Subsequence n m) : Prop :=
  StrictMono (seq ∘ sub.indices)

/-- A subsequence is (exactly) decreasing: its values strictly decrease. -/
def IsDecreasing (seq : RealSeq n) (sub : Subsequence n m) : Prop :=
  ∀ i j : Fin m, i < j → seq (sub.indices j) < seq (sub.indices i)

/-- A subsequence is monotonic if it is increasing or decreasing. -/
def IsMonotonic (seq : RealSeq n) (sub : Subsequence n m) : Prop :=
  IsIncreasing seq sub ∨ IsDecreasing seq sub

/-- **ε-approximately increasing.** Later values may fall below earlier ones by at most the
tolerance `ε`: for `i < j`, `seq (idxᵢ) - ε < seq (idxⱼ)`. At `ε = 0` this is strict
increase; for `ε > 0` a bounded amount of backtracking is permitted. -/
def IsApproxIncreasing (ε : ℝ) (seq : RealSeq n) (sub : Subsequence n m) : Prop :=
  ∀ i j : Fin m, i < j → seq (sub.indices i) - ε < seq (sub.indices j)

/-- **ε-approximately decreasing** (the dual): for `i < j`,
`seq (idxⱼ) < seq (idxᵢ) + ε`. -/
def IsApproxDecreasing (ε : ℝ) (seq : RealSeq n) (sub : Subsequence n m) : Prop :=
  ∀ i j : Fin m, i < j → seq (sub.indices j) < seq (sub.indices i) + ε

/-- ε-approximately monotonic: approximately increasing or approximately decreasing. -/
def IsApproxMonotonic (ε : ℝ) (seq : RealSeq n) (sub : Subsequence n m) : Prop :=
  IsApproxIncreasing ε seq sub ∨ IsApproxDecreasing ε seq sub

/-- **At zero tolerance the approximate notion is exactly strict monotonicity.** This pins
the relaxation: `IsApproxIncreasing 0` and `IsIncreasing` are the same predicate, so the
approximate framework is a genuine one-parameter family through the classical notion. -/
theorem isApproxIncreasing_zero_iff (seq : RealSeq n) (sub : Subsequence n m) :
    IsApproxIncreasing 0 seq sub ↔ IsIncreasing seq sub := by
  constructor
  · intro h i j hij
    have := h i j hij
    simpa using this
  · intro h i j hij
    have := h hij
    simpa using this

/-- **The tolerance is monotone: a larger `ε` is a weaker constraint.** Anything
`ε₁`-approximately increasing is `ε₂`-approximately increasing whenever `ε₁ ≤ ε₂`. -/
theorem isApproxIncreasing_mono {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsApproxIncreasing ε₁ seq sub) : IsApproxIncreasing ε₂ seq sub := by
  intro i j hij
  have := h i j hij
  linarith

/-- Dual monotonicity in the tolerance for the decreasing notion. -/
theorem isApproxDecreasing_mono {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsApproxDecreasing ε₁ seq sub) : IsApproxDecreasing ε₂ seq sub := by
  intro i j hij
  have := h i j hij
  linarith

/-- **Every exactly increasing subsequence is `ε`-approximately increasing** (`ε ≥ 0`).
The strict inequality `seq (idxᵢ) < seq (idxⱼ)` only improves when `ε` is subtracted from
the smaller side. -/
theorem IsIncreasing.isApproxIncreasing {ε : ℝ} (hε : 0 ≤ ε)
    {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsIncreasing seq sub) : IsApproxIncreasing ε seq sub := by
  intro i j hij
  have := h hij
  simp only [Function.comp_apply] at this
  linarith

/-- Dual: every exactly decreasing subsequence is `ε`-approximately decreasing (`ε ≥ 0`). -/
theorem IsDecreasing.isApproxDecreasing {ε : ℝ} (hε : 0 ≤ ε)
    {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsDecreasing seq sub) : IsApproxDecreasing ε seq sub := by
  intro i j hij
  have := h i j hij
  linarith

/-- **Every monotonic subsequence is `ε`-approximately monotonic** (`ε ≥ 0`). The relaxation
contains the classical notion. -/
theorem IsMonotonic.isApproxMonotonic {ε : ℝ} (hε : 0 ≤ ε)
    {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsMonotonic seq sub) : IsApproxMonotonic ε seq sub := by
  rcases h with hinc | hdec
  · exact Or.inl (hinc.isApproxIncreasing hε)
  · exact Or.inr (hdec.isApproxDecreasing hε)

/-- **Existence transfer — the easy half of OQ-02.** A guaranteed monotonic subsequence of
length `m` yields an `ε`-approximately monotonic one of the *same* length, for every
`ε ≥ 0`. Consequently every classical length lower bound (e.g. the Erdős–Szekeres `k + 1`
from `k² + 1` distinct terms) holds verbatim for approximate monotonicity: relaxing the
constraint can only make long subsequences easier to find. -/
theorem exists_approxMonotonic_of_exists_monotonic {ε : ℝ} (hε : 0 ≤ ε)
    {seq : RealSeq n}
    (h : ∃ sub : Subsequence n m, IsMonotonic seq sub) :
    ∃ sub : Subsequence n m, IsApproxMonotonic ε seq sub := by
  obtain ⟨sub, hsub⟩ := h
  exact ⟨sub, hsub.isApproxMonotonic hε⟩

/-- **The relaxation is genuine (the open direction is nonvacuous).** For `ε = 2` there is a
subsequence that is `ε`-approximately increasing but not exactly increasing: the two-term
sequence `(0, -1)` backtracks by `1 < 2`, so it is `2`-approximately increasing, yet
`0 < -1` fails. This is exactly the slack in which a strictly longer approximate subsequence
could live — quantifying that gain is the open content of OQ-02. -/
theorem approxIncreasing_not_increasing :
    ∃ (seq : RealSeq 2) (sub : Subsequence 2 2),
      IsApproxIncreasing 2 seq sub ∧ ¬ IsIncreasing seq sub := by
  refine ⟨![0, -1], ⟨id, strictMono_id⟩, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h
    have hlt := h (show (0 : Fin 2) < 1 from by decide)
    norm_num [Function.comp_apply] at hlt

end Erdos1026OQ02
