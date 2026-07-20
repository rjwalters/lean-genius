/-
# erdos-1026-oq-05 (Mirsky companion): the matching UPPER bound on monotonic decompositions

`Erdos1026OQ05.lean` proves the elementary Mirsky/Dilworth **lower** bound

    n ≤ numParts · max (LIS seq) (LDS seq)

and brackets the optimal part count `minMonotonicParts seq ∈ [n / max(LIS,LDS), n]`, leaving the
matching upper bound open (only the crude `≤ n` from the singleton decomposition was available).

This file supplies the matching **upper** bound — the constructive (Mirsky) half — for sequences
of *distinct* reals:

    minMonotonicParts seq ≤ LDS seq                (`minMonotonicParts_le_LDS`)
    minMonotonicParts seq ≤ LIS seq                (`minMonotonicParts_le_LIS`)
    minMonotonicParts seq ≤ min (LIS seq) (LDS seq) (`minMonotonicParts_le_min`)

so together with the lower bound the optimal part count is now bracketed in

    [ n / max(LIS,LDS) , min(LIS,LDS) ]            (`minMonotonicParts_sharp_bracket`).

For the Erdős–Szekeres extremal sequences (where `LIS ≈ LDS ≈ √n`) this pins
`minMonotonicParts ≈ √n`, matching the lower bound.

**Construction (Mirsky, avoiding general Dilworth — which Mathlib lacks).**  Colour each index `i`
by `rank i = ` the length of the longest strictly-*decreasing* subsequence ending at `i`.  Two facts
drive everything:

* `rank i ∈ [1, LDS seq]` — a decreasing run ending at `i` is a decreasing subsequence.
* **equal colour ⇒ increasing**: if `seq` is injective, `i < j` and `rank i = rank j`, then
  `seq i < seq j`.  (If instead `seq j < seq i`, appending `j` to a maximal decreasing run ending at
  `i` yields a strictly longer one ending at `j`, forcing `rank j > rank i`.)

Hence each colour class is a strictly-increasing subsequence, and there are at most `LDS seq`
non-empty classes, giving a monotonic decomposition into `≤ LDS` parts.  The `LIS` bound follows by
negating the sequence (which swaps increasing/decreasing and hence `LIS ↔ LDS`).

No axioms, no sorries.
-/

import Mathlib
import Proofs.Erdos1026OQ05

open Finset

namespace Erdos1026OQ05

variable {n : ℕ}

/-! ## The rank colouring: longest strictly-decreasing run ending at `i` -/

/-- The set of achievable lengths of strictly-decreasing runs ending at index `i`: a run is a
finite set `T` of indices with maximum `i` on which `seq` is strictly antitone (i.e. `seq`
strictly decreases along increasing indices). -/
def decRunsEndingAt (seq : RealSeq n) (i : Fin n) : Set ℕ :=
  {c | ∃ T : Finset (Fin n), c = T.card ∧ i ∈ T ∧ (∀ a ∈ T, a ≤ i) ∧
        StrictAntiOn seq (T : Set (Fin n))}

/-- The colour of index `i`: the length of the longest strictly-decreasing run ending at `i`. -/
noncomputable def rank (seq : RealSeq n) (i : Fin n) : ℕ := sSup (decRunsEndingAt seq i)

/-- The singleton run `{i}` shows `decRunsEndingAt` is nonempty (and `rank ≥ 1`). -/
lemma one_mem_decRunsEndingAt (seq : RealSeq n) (i : Fin n) : 1 ∈ decRunsEndingAt seq i := by
  refine ⟨{i}, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro a ha; simp only [Finset.mem_singleton] at ha; exact le_of_eq ha
  · intro a ha b hb hab
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) (ne_of_lt hab)

lemma decRunsEndingAt_nonempty (seq : RealSeq n) (i : Fin n) :
    (decRunsEndingAt seq i).Nonempty :=
  ⟨1, one_mem_decRunsEndingAt seq i⟩

/-- Every decreasing run has length at most `n`, so the length set is bounded above. -/
lemma decRunsEndingAt_bddAbove (seq : RealSeq n) (i : Fin n) :
    BddAbove (decRunsEndingAt seq i) := by
  refine ⟨n, ?_⟩
  rintro c ⟨T, rfl, -, -, -⟩
  calc T.card ≤ Fintype.card (Fin n) := Finset.card_le_univ T
    _ = n := Fintype.card_fin n

/-- The maximal decreasing run length is realised by an actual run `T`. -/
lemma rank_mem (seq : RealSeq n) (i : Fin n) : rank seq i ∈ decRunsEndingAt seq i :=
  Nat.sSup_mem (decRunsEndingAt_nonempty seq i) (decRunsEndingAt_bddAbove seq i)

/-- `1 ≤ rank i`. -/
lemma one_le_rank (seq : RealSeq n) (i : Fin n) : 1 ≤ rank seq i :=
  le_csSup (decRunsEndingAt_bddAbove seq i) (one_mem_decRunsEndingAt seq i)

/-- A strictly-antitone finite index set is (the index range of) a decreasing subsequence, hence
has length at most `LDS seq`. -/
lemma card_le_LDS_of_strictAntiOn (seq : RealSeq n) {T : Finset (Fin n)}
    (hT : StrictAntiOn seq (T : Set (Fin n))) : T.card ≤ LDS seq := by
  -- Enumerate `T` in increasing index order; the resulting subsequence is decreasing.
  let idx : Fin T.card → Fin n := T.orderEmbOfFin rfl
  have hmono : StrictMono idx := (T.orderEmbOfFin rfl).strictMono
  refine len_le_LDS_of_decreasing (sub := ⟨idx, hmono⟩) ?_
  intro a b hab
  have hmemA : idx a ∈ T := T.orderEmbOfFin_mem rfl a
  have hmemB : idx b ∈ T := T.orderEmbOfFin_mem rfl b
  exact hT hmemA hmemB (hmono hab)

/-- **Colour bound.** `rank i ≤ LDS seq`. -/
lemma rank_le_LDS (seq : RealSeq n) (i : Fin n) : rank seq i ≤ LDS seq := by
  refine csSup_le (decRunsEndingAt_nonempty seq i) ?_
  rintro c ⟨T, rfl, -, -, hanti⟩
  exact card_le_LDS_of_strictAntiOn seq hanti

/-! ## Equal colour ⇒ strictly increasing (the heart of the argument) -/

/-- **Key lemma.** For a sequence of distinct reals, two indices with the same colour appear in
increasing value order: `i < j` and `rank i = rank j` force `seq i < seq j`.

If instead `seq j < seq i`, append `j` to a maximal decreasing run ending at `i`: since every index
of that run is `≤ i < j` and its values all dominate `seq i > seq j`, the extended set is a longer
decreasing run ending at `j`, so `rank j ≥ rank i + 1`, contradicting `rank i = rank j`. -/
theorem seq_lt_of_rank_eq (seq : RealSeq n) (hinj : Function.Injective seq)
    {i j : Fin n} (hij : i < j) (hrank : rank seq i = rank seq j) : seq i < seq j := by
  rcases lt_trichotomy (seq i) (seq j) with hlt | heq | hgt
  · exact hlt
  · exact absurd (hinj heq) (ne_of_lt hij)
  · -- The impossible case `seq j < seq i`.
    exfalso
    obtain ⟨T, hcard, hiT, hmax, hanti⟩ := rank_mem seq i
    -- Every value in the run dominates `seq i`.
    have hdom : ∀ a ∈ T, seq i ≤ seq a := by
      intro a ha
      rcases eq_or_lt_of_le (hmax a ha) with h | h
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (hanti ha hiT h)
    -- `j` is above the whole run in index.
    have hjT : j ∉ T := fun hj => absurd (hmax j hj) (not_le.mpr hij)
    set T' := insert j T with hT'
    -- `T'` is a decreasing run ending at `j` of length `rank i + 1`.
    have hcard' : T'.card = rank seq i + 1 := by
      rw [hT', Finset.card_insert_of_not_mem hjT, hcard]
    have hmax' : ∀ a ∈ T', a ≤ j := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact le_refl a
      · exact le_of_lt (lt_of_le_of_lt (hmax a ha) hij)
    have hanti' : StrictAntiOn seq (T' : Set (Fin n)) := by
      intro a ha b hb hab
      simp only [hT', Finset.coe_insert, Set.mem_insert_iff] at ha hb
      rcases hb with rfl | hbT
      · -- `b = j` is the top; `a < j` forces `a ∈ T`, and every run value dominates `seq i > seq j`.
        rcases ha with rfl | haT
        · exact absurd hab (lt_irrefl _)
        · exact lt_of_lt_of_le hgt (hdom a haT)
      · rcases ha with rfl | haT
        · -- `a = j` with `j < b ≤ i < j` is impossible.
          exact absurd (lt_of_le_of_lt (hmax b hbT) hij) (lt_asymm hab)
        · exact hanti haT hbT hab
    have hmemj : rank seq i + 1 ∈ decRunsEndingAt seq j :=
      ⟨T', hcard'.symm, Finset.mem_insert_self j T, hmax', hanti'⟩
    have : rank seq i + 1 ≤ rank seq j :=
      le_csSup (decRunsEndingAt_bddAbove seq j) hmemj
    omega

/-! ## Assembling the colour classes into a monotonic decomposition -/

section Construction

variable (seq : RealSeq n) (hinj : Function.Injective seq)

/-- Colour class `k`: the indices whose rank is `k + 1`.  Ranks run over `1 … LDS seq`, so classes
are indexed by `Fin (LDS seq)`. -/
def colourClass (k : Fin (LDS seq)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => rank seq i = k.val + 1)

lemma mem_colourClass {k : Fin (LDS seq)} {i : Fin n} :
    i ∈ colourClass seq k ↔ rank seq i = k.val + 1 := by
  simp [colourClass]

/-- **The Mirsky decomposition.**  One strictly-increasing part per colour class; there are
`LDS seq` classes.  Increasing-ness of a class is exactly `seq_lt_of_rank_eq`. -/
noncomputable def mirskyDecomposition : MonotonicDecomposition n seq where
  numParts := LDS seq
  parts := fun k => ⟨(colourClass seq k).card,
    ⟨(colourClass seq k).orderEmbOfFin rfl, ((colourClass seq k).orderEmbOfFin rfl).strictMono⟩⟩
  monotonic := by
    intro k
    left
    intro p q hpq
    have hlt : (colourClass seq k).orderEmbOfFin rfl p < (colourClass seq k).orderEmbOfFin rfl q :=
      ((colourClass seq k).orderEmbOfFin rfl).strictMono hpq
    have hmp := (colourClass seq k).orderEmbOfFin_mem rfl p
    have hmq := (colourClass seq k).orderEmbOfFin_mem rfl q
    rw [mem_colourClass] at hmp hmq
    exact seq_lt_of_rank_eq seq hinj hlt (hmp.trans hmq.symm)
  disjoint := by
    intro a b p q hab hEq
    have hm1 := (colourClass seq a).orderEmbOfFin_mem rfl p
    have hm2 := (colourClass seq b).orderEmbOfFin_mem rfl q
    rw [mem_colourClass] at hm1 hm2
    rw [hEq] at hm1
    rw [hm1] at hm2
    exact hab (Fin.ext (by omega))
  covering := by
    intro i
    have hge := one_le_rank seq i
    have hle := rank_le_LDS seq i
    refine ⟨⟨rank seq i - 1, by omega⟩, ?_⟩
    have hmem : i ∈ colourClass seq ⟨rank seq i - 1, by omega⟩ := by
      rw [mem_colourClass]; omega
    have hi : i ∈ Set.range ⇑((colourClass seq ⟨rank seq i - 1, by omega⟩).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hmem
    obtain ⟨pos, hpos⟩ := hi
    exact ⟨pos.val, pos.isLt, by simpa using hpos⟩

/-- **Mirsky upper bound.**  For a sequence of distinct reals, the minimum number of monotone parts
is at most the longest strictly-decreasing subsequence length. -/
theorem minMonotonicParts_le_LDS : minMonotonicParts seq ≤ LDS seq := by
  apply Nat.sInf_le
  exact ⟨mirskyDecomposition seq hinj, rfl⟩

end Construction

/-! ## The `LIS` bound by negation symmetry, and the sharp bracket -/

/-- The negated sequence, whose increasing/decreasing runs are swapped. -/
def negSeq (seq : RealSeq n) : RealSeq n := fun i => - seq i

lemma isDecreasing_negSeq (seq : RealSeq n) {m : ℕ} (sub : Subsequence n m) :
    IsDecreasing (negSeq seq) sub ↔ IsIncreasing seq sub := by
  constructor
  · intro h a b hab
    have := h a b hab
    simpa [negSeq, neg_lt_neg_iff] using this
  · intro h a b hab
    have := h hab
    simpa [negSeq, neg_lt_neg_iff] using this

lemma isIncreasing_negSeq (seq : RealSeq n) {m : ℕ} (sub : Subsequence n m) :
    IsIncreasing (negSeq seq) sub ↔ IsDecreasing seq sub := by
  constructor
  · intro h a b hab
    have := h hab
    simpa [negSeq, neg_lt_neg_iff] using this
  · intro h a b hab
    have := h a b hab
    simpa [negSeq, neg_lt_neg_iff] using this

lemma isMonotonic_negSeq (seq : RealSeq n) {m : ℕ} (sub : Subsequence n m) :
    IsMonotonic (negSeq seq) sub ↔ IsMonotonic seq sub := by
  unfold IsMonotonic
  rw [isIncreasing_negSeq, isDecreasing_negSeq, or_comm]

/-- A monotonic decomposition of `seq` is one of `negSeq seq` (same parts). -/
def negSeqDecomposition (seq : RealSeq n) (D : MonotonicDecomposition n seq) :
    MonotonicDecomposition n (negSeq seq) where
  numParts := D.numParts
  parts := D.parts
  monotonic := fun i => (isMonotonic_negSeq seq (D.parts i).2).mpr (D.monotonic i)
  disjoint := D.disjoint
  covering := D.covering

/-- …and conversely. -/
def negSeqDecomposition' (seq : RealSeq n) (D : MonotonicDecomposition n (negSeq seq)) :
    MonotonicDecomposition n seq where
  numParts := D.numParts
  parts := D.parts
  monotonic := fun i => (isMonotonic_negSeq seq (D.parts i).2).mp (D.monotonic i)
  disjoint := D.disjoint
  covering := D.covering

lemma minMonotonicParts_negSeq (seq : RealSeq n) :
    minMonotonicParts (negSeq seq) = minMonotonicParts seq := by
  unfold minMonotonicParts
  congr 1
  ext p
  constructor
  · rintro ⟨D, rfl⟩; exact ⟨negSeqDecomposition' seq D, rfl⟩
  · rintro ⟨D, rfl⟩; exact ⟨negSeqDecomposition seq D, rfl⟩

lemma LDS_negSeq (seq : RealSeq n) : LDS (negSeq seq) = LIS seq := by
  unfold LDS LIS
  congr 1
  ext m
  constructor
  · rintro ⟨sub, h⟩; exact ⟨sub, (isDecreasing_negSeq seq sub).mp h⟩
  · rintro ⟨sub, h⟩; exact ⟨sub, (isDecreasing_negSeq seq sub).mpr h⟩

/-- **Mirsky upper bound, `LIS` form.**  By negation symmetry, `≤ LIS seq` too. -/
theorem minMonotonicParts_le_LIS (seq : RealSeq n) (hinj : Function.Injective seq) :
    minMonotonicParts seq ≤ LIS seq := by
  have hinj' : Function.Injective (negSeq seq) := fun a b h => hinj (neg_injective h)
  calc minMonotonicParts seq = minMonotonicParts (negSeq seq) := (minMonotonicParts_negSeq seq).symm
    _ ≤ LDS (negSeq seq) := minMonotonicParts_le_LDS (negSeq seq) hinj'
    _ = LIS seq := LDS_negSeq seq

/-- **Matching upper bound.**  `minMonotonicParts seq ≤ min (LIS seq) (LDS seq)`. -/
theorem minMonotonicParts_le_min (seq : RealSeq n) (hinj : Function.Injective seq) :
    minMonotonicParts seq ≤ min (LIS seq) (LDS seq) :=
  le_min (minMonotonicParts_le_LIS seq hinj) (minMonotonicParts_le_LDS seq hinj)

/-- **The sharp bracket.**  Combining the elementary Mirsky/Dilworth lower bound
(`minMonotonicParts_ge`) with the constructive upper bound proved here, the optimal number of
monotone parts of a sequence of distinct reals lies in

    [ n / max(LIS, LDS) , min(LIS, LDS) ].

For the Erdős–Szekeres extremal sequences (`LIS ≈ LDS ≈ √n`) both ends are `≈ √n`. -/
theorem minMonotonicParts_sharp_bracket (seq : RealSeq n) (hinj : Function.Injective seq) :
    n / max (LIS seq) (LDS seq) ≤ minMonotonicParts seq ∧
      minMonotonicParts seq ≤ min (LIS seq) (LDS seq) :=
  ⟨minMonotonicParts_ge seq, minMonotonicParts_le_min seq hinj⟩

end Erdos1026OQ05
