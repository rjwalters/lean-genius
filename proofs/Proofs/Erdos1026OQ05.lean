import Mathlib

/-
# erdos-1026-oq-05: Lower bound on monotonic decompositions of a sequence

Erdős Problem #1026 concerns monotonic subsequences: by Erdős–Szekeres, every sequence of
`k² + 1` distinct reals contains a monotonic subsequence of length `k + 1`, and the
optimization variant studies the maximum *sum* carried by such a subsequence.

**OQ-05** asks to extend the picture from single monotonic subsequences to *decompositions*
of the whole sequence into monotonic pieces (the object underlying Hanani's 1957 theorem,
`MonotonicDecomposition` in `Erdos1026Problem.lean`). The parent file states the
`MonotonicDecomposition` structure but proves *nothing* about how many parts such a
decomposition must use — Hanani's `(√2 + o(1))√n` bound lives only in a comment.

This file proves, axiom-free, the elementary but genuine **lower bound** direction
(the Mirsky/Dilworth half): *every* monotonic decomposition of a sequence into pieces that
are each increasing or decreasing must use enough parts to cover the sequence, namely

    n ≤ numParts · max (LIS seq) (LDS seq)         (`monotonicDecomposition_numParts_lower_bound`)

where `LIS`/`LDS` are the longest increasing / decreasing subsequence lengths. The proof is
a clean counting argument: the parts' index maps assemble into a surjection from their
disjoint union onto `Fin n`, so `n` is at most the sum of the part lengths; and each part,
being monotonic, has length at most `LIS seq` (if increasing) or `LDS seq` (if decreasing),
hence at most `max (LIS seq) (LDS seq)`.

Two consequences are recorded:
* the contrapositive `monotonicDecomposition_numParts_ge` — you cannot cover a length-`n`
  sequence with `numParts` monotonic pieces once `numParts · max(LIS, LDS) < n`; and
* the fact that a decomposition always exists (`singletonDecomposition`), so the bound is
  about a nonempty class of objects and brackets `numParts` from below (the trivial
  singleton decomposition gives the matching crude upper bound `numParts ≤ n`).

For the extremal Erdős–Szekeres sequences, where the longest monotone run has length only
`≈ √n`, the bound forces `numParts ≳ √n` monotone pieces — the lower-bound side of Hanani's
theorem. The matching **upper** bound (that `O(√n)` pieces always *suffice*) is the hard
constructive direction and is left open, stated but not axiomatized.

The framework is self-contained: it re-states the minimal `Subsequence` / `LIS` / `LDS` /
`MonotonicDecomposition` interface of `Erdos1026Problem.lean` rather than importing it, since
that file depends on `Archive.Wiedijk100Theorems`. No axioms, no sorries.
-/

open Finset

namespace Erdos1026OQ05

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

/-- A subsequence has length at most that of its parent sequence. -/
lemma subsequence_length_le (sub : Subsequence n m) : m ≤ n := by
  have := Fintype.card_le_of_injective sub.indices sub.strictMono.injective
  simpa using this

/-- The longest increasing subsequence length. -/
noncomputable def LIS (seq : RealSeq n) : ℕ :=
  sSup {m | ∃ sub : Subsequence n m, IsIncreasing seq sub}

/-- The longest decreasing subsequence length. -/
noncomputable def LDS (seq : RealSeq n) : ℕ :=
  sSup {m | ∃ sub : Subsequence n m, IsDecreasing seq sub}

/-- The set of achievable increasing subsequence lengths is bounded above by `n`. -/
lemma lis_bddAbove (seq : RealSeq n) :
    BddAbove {m | ∃ sub : Subsequence n m, IsIncreasing seq sub} :=
  ⟨n, fun _ ⟨sub, _⟩ => subsequence_length_le sub⟩

/-- The set of achievable decreasing subsequence lengths is bounded above by `n`. -/
lemma lds_bddAbove (seq : RealSeq n) :
    BddAbove {m | ∃ sub : Subsequence n m, IsDecreasing seq sub} :=
  ⟨n, fun _ ⟨sub, _⟩ => subsequence_length_le sub⟩

/-- An increasing subsequence has length at most `LIS`. -/
lemma len_le_LIS_of_increasing {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsIncreasing seq sub) : m ≤ LIS seq :=
  le_csSup (lis_bddAbove seq) ⟨sub, h⟩

/-- A decreasing subsequence has length at most `LDS`. -/
lemma len_le_LDS_of_decreasing {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsDecreasing seq sub) : m ≤ LDS seq :=
  le_csSup (lds_bddAbove seq) ⟨sub, h⟩

/-- A monotonic subsequence has length at most `max (LIS seq) (LDS seq)`. -/
lemma len_le_max_of_monotonic {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsMonotonic seq sub) : m ≤ max (LIS seq) (LDS seq) := by
  rcases h with hInc | hDec
  · exact (len_le_LIS_of_increasing hInc).trans (le_max_left _ _)
  · exact (len_le_LDS_of_decreasing hDec).trans (le_max_right _ _)

/-- A decomposition of a sequence into monotonic subsequences whose images cover every
index (mirrors `Erdos1026.MonotonicDecomposition`). -/
structure MonotonicDecomposition (n : ℕ) (seq : RealSeq n) where
  numParts : ℕ
  parts : Fin numParts → Σ m, Subsequence n m
  monotonic : ∀ i, IsMonotonic seq (parts i).2
  disjoint : ∀ i j k₁ k₂, i ≠ j →
    (parts i).2.indices k₁ ≠ (parts j).2.indices k₂
  covering : ∀ k : Fin n, ∃ i m hm, (parts i).2.indices ⟨m, hm⟩ = k

/-- **OQ-05 lower bound.** Every monotonic decomposition of a length-`n` sequence uses
enough parts that `numParts · max(LIS, LDS) ≥ n`. Equivalently, you cannot cover the
sequence with fewer than `n / max(LIS, LDS)` monotone pieces.

Proof: the parts' index maps assemble into a surjection `g` from the disjoint union
`Σ i, Fin (length of part i)` onto `Fin n` (this is exactly the covering condition), so
`n = |Fin n| ≤ Σ i, (length of part i)`. Each part is monotonic, hence has length at most
`max (LIS seq) (LDS seq)`, and summing the constant bound over the `numParts` parts gives the
claim. -/
theorem monotonicDecomposition_numParts_lower_bound
    (seq : RealSeq n) (D : MonotonicDecomposition n seq) :
    n ≤ D.numParts * max (LIS seq) (LDS seq) := by
  classical
  -- The parts' index maps, packaged as one map out of the disjoint union of the parts.
  let g : (Σ i : Fin D.numParts, Fin (D.parts i).1) → Fin n :=
    fun p => (D.parts p.1).2.indices p.2
  -- Covering says this map is surjective.
  have hsurj : Function.Surjective g := by
    intro k
    obtain ⟨i, m, hm, hk⟩ := D.covering k
    exact ⟨⟨i, ⟨m, hm⟩⟩, hk⟩
  -- Hence `n = |Fin n| ≤ |Σ i, Fin (part i length)| = Σ i, (part i length)`.
  have hcard : Fintype.card (Fin n)
      ≤ Fintype.card (Σ i : Fin D.numParts, Fin (D.parts i).1) :=
    Fintype.card_le_of_surjective g hsurj
  rw [Fintype.card_fin, Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  refine hcard.trans ?_
  -- Each part is monotonic, so its length is at most `max (LIS seq) (LDS seq)`.
  calc ∑ i, (D.parts i).1
      ≤ ∑ _i : Fin D.numParts, max (LIS seq) (LDS seq) :=
        Finset.sum_le_sum (fun i _ => len_le_max_of_monotonic (D.monotonic i))
    _ = D.numParts * max (LIS seq) (LDS seq) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Division form: any monotonic decomposition uses at least `n / max(LIS, LDS)` parts.
(For `max = 0` the sequence is empty and the bound `0 ≤ numParts` is trivial.) -/
theorem monotonicDecomposition_numParts_ge
    (seq : RealSeq n) (D : MonotonicDecomposition n seq) :
    n / max (LIS seq) (LDS seq) ≤ D.numParts := by
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm]
  exact monotonicDecomposition_numParts_lower_bound seq D

/-- Any function out of `Fin 1` is (vacuously) strictly monotone: there are no `a < b`. -/
lemma fin_one_strictMono {α : Type*} [Preorder α] (f : Fin 1 → α) : StrictMono f := by
  intro a b hab
  exact absurd hab (by simp [Fin.lt_def])

/-- Every sequence admits a monotonic decomposition: split it into `n` singleton parts.
A single element is (vacuously) increasing, so each part is monotonic; the parts obviously
cover and are pairwise disjoint. This shows `MonotonicDecomposition` is a nonempty class and
gives the crude upper bound `numParts = n`, which together with
`monotonicDecomposition_numParts_lower_bound` brackets the optimal number of parts in
`[n / max(LIS, LDS), n]`. -/
def singletonDecomposition (seq : RealSeq n) : MonotonicDecomposition n seq where
  numParts := n
  parts := fun i => ⟨1, ⟨fun _ => i, fin_one_strictMono _⟩⟩
  monotonic := fun _ => Or.inl (fin_one_strictMono _)
  disjoint := fun _ _ _ _ hij => hij
  covering := fun k => ⟨k, 0, Nat.one_pos, rfl⟩

end Erdos1026OQ05
