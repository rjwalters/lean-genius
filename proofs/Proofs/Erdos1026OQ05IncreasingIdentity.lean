/-
# erdos-1026-oq-05 (increasing-decomposition companion): the exact Mirsky/Dilworth min–max IDENTITY

`Erdos1026OQ05.lean` studies decompositions of a length-`n` real sequence into *monotonic*
(increasing OR decreasing) subsequences, and brackets the optimal part count
`minMonotonicParts seq ∈ [n / max(LIS, LDS), n]` — a bracket, not an identity, because a monotone
part can be either type.

This file resolves the **exact** min–max identity for the *increasing-only* covering number.
Define `minIncreasingParts seq` = the least number of strictly-*increasing* subsequences needed to
cover every index. Then, for a sequence of distinct reals,

    minIncreasingParts seq = LDS seq                    (`minIncreasingParts_eq_LDS`)

the length of the longest strictly-*decreasing* subsequence. This is the sequence form of the
dual-Dilworth / Mirsky theorem (equivalently, the correctness of patience sorting): an *identity*,
strictly sharper than the monotone bracket.

Both halves are elementary and self-contained (they import only the committed base file):

* **Lower bound** `LDS seq ≤ numParts` (`LDS_le_numParts`, needs no distinctness): a longest
  strictly-decreasing subsequence meets each strictly-increasing part in at most one index
  (two indices of a decreasing pair have their values in the wrong order for one increasing part),
  so its `LDS` indices land in `LDS` distinct parts — a clean pigeonhole.

* **Upper bound** `minIncreasingParts seq ≤ LDS seq` (`minIncreasingParts_le_LDS`, distinct reals):
  the Mirsky rank colouring. Colour index `i` by `rank i` = length of the longest strictly-decreasing
  run ending at `i`; ranks live in `[1, LDS]`, and two equal-coloured indices are forced into
  increasing value order, so each colour class is a strictly-increasing subsequence. That yields a
  covering by `≤ LDS` increasing parts.

As a corollary the increasing covering number dominates the monotone one
(`minMonotonicParts_le_minIncreasingParts`), so the identity also re-derives the committed monotone
upper bound `minMonotonicParts seq ≤ LDS seq`.

The file also proves the exact **dual** identity `minDecreasingParts seq = LIS seq`
(`minDecreasingParts_eq_LIS`) by transporting the increasing identity through the order-reversing map
`x ↦ -x`, and combines the two to **close the monotone bracket to its sharp form**
`minMonotonicParts seq ∈ [n / max(LIS, LDS), min(LIS, LDS)]` for distinct reals
(`minMonotonicParts_le_min_LIS_LDS`).

No axioms, no sorries.
-/

import Mathlib
import Proofs.Erdos1026OQ05

open Finset

namespace Erdos1026OQ05IncreasingIdentity

open Erdos1026OQ05

variable {n : ℕ}

/-! ## Increasing decompositions and their covering number -/

/-- A decomposition of a sequence into strictly-*increasing* subsequences whose images cover every
index. Identical to `MonotonicDecomposition` but with each part required to be *increasing* (not
merely monotone). -/
structure IncreasingDecomposition (n : ℕ) (seq : RealSeq n) where
  numParts : ℕ
  parts : Fin numParts → Σ m, Subsequence n m
  increasing : ∀ i, IsIncreasing seq (parts i).2
  disjoint : ∀ i j k₁ k₂, i ≠ j →
    (parts i).2.indices k₁ ≠ (parts j).2.indices k₂
  covering : ∀ k : Fin n, ∃ i m hm, (parts i).2.indices ⟨m, hm⟩ = k

/-- Every sequence admits an increasing decomposition: split it into `n` singleton parts (a single
element is vacuously strictly increasing). This makes the class nonempty. -/
def singletonIncreasingDecomposition (seq : RealSeq n) : IncreasingDecomposition n seq where
  numParts := n
  parts := fun i => ⟨1, ⟨fun _ => i, fin_one_strictMono _⟩⟩
  increasing := fun _ => fin_one_strictMono _
  disjoint := fun _ _ _ _ hij => hij
  covering := fun k => ⟨k, 0, Nat.one_pos, rfl⟩

/-- The **minimum number of strictly-increasing parts** needed to cover `seq`. Well-defined because
`singletonIncreasingDecomposition` always supplies a decomposition. -/
noncomputable def minIncreasingParts (seq : RealSeq n) : ℕ :=
  sInf {p | ∃ D : IncreasingDecomposition n seq, D.numParts = p}

/-- Every increasing decomposition is in particular a monotonic one (same parts). -/
def toMonotonic (seq : RealSeq n) (D : IncreasingDecomposition n seq) :
    MonotonicDecomposition n seq where
  numParts := D.numParts
  parts := D.parts
  monotonic := fun i => Or.inl (D.increasing i)
  disjoint := D.disjoint
  covering := D.covering

/-- Refinement: covering by *increasing* parts is at least as costly as by *monotone* parts. -/
theorem minMonotonicParts_le_minIncreasingParts (seq : RealSeq n) :
    minMonotonicParts seq ≤ minIncreasingParts seq := by
  apply le_csInf
  · exact ⟨n, singletonIncreasingDecomposition seq, rfl⟩
  · rintro p ⟨D, rfl⟩
    exact Nat.sInf_le ⟨toMonotonic seq D, rfl⟩

/-! ## Lower bound: `LDS ≤ numParts` (pigeonhole, no distinctness needed) -/

/-- The empty subsequence witnesses `0` as an achievable decreasing length, so the length set is
nonempty and `LDS` is realised by an actual decreasing subsequence. -/
lemma exists_decreasing_of_LDS (seq : RealSeq n) :
    ∃ sub : Subsequence n (LDS seq), IsDecreasing seq sub := by
  have hmem : LDS seq ∈ {m | ∃ sub : Subsequence n m, IsDecreasing seq sub} := by
    apply Nat.sSup_mem
    · exact ⟨0, ⟨Fin.elim0, by intro a b h; exact a.elim0⟩, by intro i j h; exact i.elim0⟩
    · exact lds_bddAbove seq
  exact hmem

/-- Within a single strictly-increasing part, two indices in the part with `x < y` have their values
in the same order: `seq x < seq y`. -/
lemma incr_part_range_mono {seq : RealSeq n} {m : ℕ} {sub : Subsequence n m}
    (h : IsIncreasing seq sub) {x y : Fin n}
    (hx : x ∈ Set.range sub.indices) (hy : y ∈ Set.range sub.indices)
    (hxy : x < y) : seq x < seq y := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  have hpq : p < q := sub.strictMono.lt_iff_lt.mp hxy
  exact h hpq

/-- **Lower bound.** Any covering of the sequence by strictly-increasing parts needs at least
`LDS seq` of them: the indices of a longest strictly-decreasing subsequence land in pairwise
distinct parts (an increasing part cannot contain two indices of a decreasing pair). -/
theorem LDS_le_numParts (seq : RealSeq n) (D : IncreasingDecomposition n seq) :
    LDS seq ≤ D.numParts := by
  classical
  obtain ⟨sub, hsub⟩ := exists_decreasing_of_LDS seq
  -- Assign each position of the decreasing subsequence to a part containing it.
  have hcov : ∀ k : Fin (LDS seq), ∃ i : Fin D.numParts, ∃ p : Fin (D.parts i).1,
      (D.parts i).2.indices p = sub.indices k := by
    intro k
    obtain ⟨i, m, hm, hk⟩ := D.covering (sub.indices k)
    exact ⟨i, ⟨m, hm⟩, hk⟩
  choose partOf posOf hpos using hcov
  -- Two earlier/later positions cannot share a part.
  have key : ∀ a b : Fin (LDS seq), a < b → partOf a ≠ partOf b := by
    intro a b hlt hpart
    have hxa : sub.indices a ∈ Set.range ((D.parts (partOf b)).2.indices) := by
      rw [← hpart]; exact ⟨posOf a, hpos a⟩
    have hxb : sub.indices b ∈ Set.range ((D.parts (partOf b)).2.indices) :=
      ⟨posOf b, hpos b⟩
    have hidx : sub.indices a < sub.indices b := sub.strictMono hlt
    have hval : seq (sub.indices a) < seq (sub.indices b) :=
      incr_part_range_mono (D.increasing (partOf b)) hxa hxb hidx
    have hdec : seq (sub.indices b) < seq (sub.indices a) := hsub a b hlt
    exact absurd hval (not_lt.mpr (le_of_lt hdec))
  -- Hence the part-assignment is injective, so there are at least `LDS` parts.
  have hinj : Function.Injective partOf := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a b h hab
    · exact key b a h hab.symm
  have hcard := Fintype.card_le_of_injective partOf hinj
  simpa using hcard

/-! ## Upper bound: the Mirsky rank colouring (distinct reals) -/

/-- The lengths of strictly-decreasing runs ending at index `i`. -/
def decRunsEndingAt (seq : RealSeq n) (i : Fin n) : Set ℕ :=
  {c | ∃ T : Finset (Fin n), c = T.card ∧ i ∈ T ∧ (∀ a ∈ T, a ≤ i) ∧
        StrictAntiOn seq (T : Set (Fin n))}

/-- The colour of index `i`: the length of the longest strictly-decreasing run ending at `i`. -/
noncomputable def rank (seq : RealSeq n) (i : Fin n) : ℕ := sSup (decRunsEndingAt seq i)

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

lemma decRunsEndingAt_bddAbove (seq : RealSeq n) (i : Fin n) :
    BddAbove (decRunsEndingAt seq i) := by
  refine ⟨n, ?_⟩
  rintro c ⟨T, rfl, -, -, -⟩
  calc T.card ≤ Fintype.card (Fin n) := Finset.card_le_univ T
    _ = n := Fintype.card_fin n

lemma rank_mem (seq : RealSeq n) (i : Fin n) : rank seq i ∈ decRunsEndingAt seq i :=
  Nat.sSup_mem (decRunsEndingAt_nonempty seq i) (decRunsEndingAt_bddAbove seq i)

lemma one_le_rank (seq : RealSeq n) (i : Fin n) : 1 ≤ rank seq i :=
  le_csSup (decRunsEndingAt_bddAbove seq i) (one_mem_decRunsEndingAt seq i)

/-- A strictly-antitone finite index set is a decreasing subsequence, hence has length `≤ LDS`. -/
lemma card_le_LDS_of_strictAntiOn (seq : RealSeq n) {T : Finset (Fin n)}
    (hT : StrictAntiOn seq (T : Set (Fin n))) : T.card ≤ LDS seq := by
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

/-- **Key lemma.** For distinct reals, two equal-coloured indices are in increasing value order. -/
theorem seq_lt_of_rank_eq (seq : RealSeq n) (hinj : Function.Injective seq)
    {i j : Fin n} (hij : i < j) (hrank : rank seq i = rank seq j) : seq i < seq j := by
  rcases lt_trichotomy (seq i) (seq j) with hlt | heq | hgt
  · exact hlt
  · exact absurd (hinj heq) (ne_of_lt hij)
  · exfalso
    obtain ⟨T, hcard, hiT, hmax, hanti⟩ := rank_mem seq i
    have hdom : ∀ a ∈ T, seq i ≤ seq a := by
      intro a ha
      rcases eq_or_lt_of_le (hmax a ha) with h | h
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (hanti ha hiT h)
    have hjT : j ∉ T := fun hj => absurd (hmax j hj) (not_le.mpr hij)
    set T' := insert j T with hT'
    have hcard' : T'.card = rank seq i + 1 := by
      rw [hT', Finset.card_insert_of_notMem hjT, hcard]
    have hmax' : ∀ a ∈ T', a ≤ j := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact le_refl a
      · exact le_of_lt (lt_of_le_of_lt (hmax a ha) hij)
    have hanti' : StrictAntiOn seq (T' : Set (Fin n)) := by
      intro a ha b hb hab
      simp only [hT', Finset.coe_insert, Set.mem_insert_iff] at ha hb
      rcases hb with rfl | hbT
      · rcases ha with rfl | haT
        · exact absurd hab (lt_irrefl _)
        · exact lt_of_lt_of_le hgt (hdom a haT)
      · rcases ha with rfl | haT
        · exact absurd (lt_of_le_of_lt (hmax b hbT) hij) (lt_asymm hab)
        · exact hanti haT hbT hab
    have hmemj : rank seq i + 1 ∈ decRunsEndingAt seq j :=
      ⟨T', hcard'.symm, Finset.mem_insert_self j T, hmax', hanti'⟩
    have : rank seq i + 1 ≤ rank seq j :=
      le_csSup (decRunsEndingAt_bddAbove seq j) hmemj
    omega

section Construction

variable (seq : RealSeq n) (hinj : Function.Injective seq)

/-- Colour class `k`: the indices whose rank is `k + 1` (ranks run over `1 … LDS seq`). -/
noncomputable def colourClass (k : Fin (LDS seq)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => rank seq i = k.val + 1)

lemma mem_colourClass {k : Fin (LDS seq)} {i : Fin n} :
    i ∈ colourClass seq k ↔ rank seq i = k.val + 1 := by
  simp [colourClass]

include hinj in
/-- **The Mirsky increasing decomposition.** One strictly-increasing part per colour class, with
`LDS seq` classes. Increasing-ness of a class is exactly `seq_lt_of_rank_eq`. -/
noncomputable def mirskyIncreasingDecomposition : IncreasingDecomposition n seq where
  numParts := LDS seq
  parts := fun k => ⟨(colourClass seq k).card,
    ⟨(colourClass seq k).orderEmbOfFin rfl, ((colourClass seq k).orderEmbOfFin rfl).strictMono⟩⟩
  increasing := by
    intro k p q hpq
    have hlt : (colourClass seq k).orderEmbOfFin rfl p < (colourClass seq k).orderEmbOfFin rfl q :=
      ((colourClass seq k).orderEmbOfFin rfl).strictMono hpq
    have hmp := (colourClass seq k).orderEmbOfFin_mem rfl p
    have hmq := (colourClass seq k).orderEmbOfFin_mem rfl q
    rw [mem_colourClass] at hmp hmq
    exact seq_lt_of_rank_eq seq hinj hlt (hmp.trans hmq.symm)
  disjoint := by
    intro a b p q hab hEq
    apply hab
    have hm1 := (colourClass seq a).orderEmbOfFin_mem rfl p
    have hm2 := (colourClass seq b).orderEmbOfFin_mem rfl q
    rw [mem_colourClass] at hm1 hm2
    -- reduce the sigma-projection form of `hEq` to the bare `orderEmbOfFin` index equality
    have hEq' : (colourClass seq a).orderEmbOfFin rfl p
              = (colourClass seq b).orderEmbOfFin rfl q := hEq
    have hrank : rank seq ((colourClass seq a).orderEmbOfFin rfl p)
               = rank seq ((colourClass seq b).orderEmbOfFin rfl q) := by rw [hEq']
    rw [hm1, hm2] at hrank
    exact Fin.ext (by omega)
  covering := by
    intro i
    have hge := one_le_rank seq i
    have hle := rank_le_LDS seq i
    have hlt : rank seq i - 1 < LDS seq := by omega
    refine ⟨⟨rank seq i - 1, hlt⟩, ?_⟩
    have hmem : i ∈ colourClass seq ⟨rank seq i - 1, hlt⟩ := by
      rw [mem_colourClass]
      show rank seq i = (rank seq i - 1) + 1
      omega
    have hi : i ∈ Set.range ⇑((colourClass seq ⟨rank seq i - 1, hlt⟩).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hmem
    obtain ⟨pos, hpos⟩ := hi
    exact ⟨pos.val, pos.isLt, by simpa using hpos⟩

include hinj in
/-- **Upper bound.** For distinct reals the increasing covering number is at most `LDS seq`. -/
theorem minIncreasingParts_le_LDS : minIncreasingParts seq ≤ LDS seq := by
  apply Nat.sInf_le
  exact ⟨mirskyIncreasingDecomposition seq hinj, rfl⟩

end Construction

/-! ## The exact identity -/

/-- `LDS seq ≤ minIncreasingParts seq` — the lower bound applied to the optimal decomposition. -/
theorem LDS_le_minIncreasingParts (seq : RealSeq n) :
    LDS seq ≤ minIncreasingParts seq := by
  apply le_csInf
  · exact ⟨n, singletonIncreasingDecomposition seq, rfl⟩
  · rintro p ⟨D, rfl⟩
    exact LDS_le_numParts seq D

/-- **The Mirsky/Dilworth min–max identity for sequences.** For a sequence of distinct reals, the
minimum number of strictly-increasing subsequences needed to cover it equals the length of the
longest strictly-decreasing subsequence. -/
theorem minIncreasingParts_eq_LDS (seq : RealSeq n) (hinj : Function.Injective seq) :
    minIncreasingParts seq = LDS seq :=
  le_antisymm (minIncreasingParts_le_LDS seq hinj) (LDS_le_minIncreasingParts seq)

/-- The identity re-derives the committed monotone upper bound `minMonotonicParts seq ≤ LDS seq`. -/
theorem minMonotonicParts_le_LDS (seq : RealSeq n) (hinj : Function.Injective seq) :
    minMonotonicParts seq ≤ LDS seq :=
  (minMonotonicParts_le_minIncreasingParts seq).trans
    (minIncreasingParts_eq_LDS seq hinj).le

/-! ## The dual identity: `minDecreasingParts = LIS` by order-negation transport

The increasing identity `minIncreasingParts = LDS` has an exact **dual**: the least number of
strictly-*decreasing* subsequences covering a sequence of distinct reals equals `LIS`, the length of
its longest strictly-*increasing* subsequence. Rather than re-run the whole Mirsky argument with the
order reversed, we transport the increasing identity through the order-reversing map `x ↦ -x`:
negating the sequence swaps increasing ↔ decreasing subsequences (and hence `LIS ↔ LDS`) and turns an
increasing decomposition of `-seq` into a decreasing decomposition of `seq` with the same part count.
So `minDecreasingParts seq = minIncreasingParts (negSeq seq) = LDS (negSeq seq) = LIS seq`.

As a payoff the two identities together **close the monotone bracket to its sharp form**
`minMonotonicParts seq ∈ [n / max(LIS, LDS), min(LIS, LDS)]` for distinct reals: covering by monotone
parts is no more costly than covering by increasing parts *or* by decreasing parts. -/

/-- The negated sequence `i ↦ -seq i`. Order reversal on the value axis. -/
def negSeq (seq : RealSeq n) : RealSeq n := fun i => -seq i

/-- Negating the sequence swaps *increasing* into *decreasing*: an increasing subsequence of `-seq`
is exactly a decreasing subsequence of `seq`. -/
lemma isIncreasing_negSeq_iff {seq : RealSeq n} {m : ℕ} {sub : Subsequence n m} :
    IsIncreasing (negSeq seq) sub ↔ IsDecreasing seq sub := by
  constructor
  · intro h i j hij
    have h2 : negSeq seq (sub.indices i) < negSeq seq (sub.indices j) := h hij
    simpa [negSeq] using h2
  · intro h i j hij
    show negSeq seq (sub.indices i) < negSeq seq (sub.indices j)
    simpa [negSeq] using h i j hij

/-- Dually, a *decreasing* subsequence of `-seq` is exactly an *increasing* subsequence of `seq`. -/
lemma isDecreasing_negSeq_iff {seq : RealSeq n} {m : ℕ} {sub : Subsequence n m} :
    IsDecreasing (negSeq seq) sub ↔ IsIncreasing seq sub := by
  constructor
  · intro h i j hij
    show seq (sub.indices i) < seq (sub.indices j)
    simpa [negSeq] using h i j hij
  · intro h i j hij
    show negSeq seq (sub.indices j) < negSeq seq (sub.indices i)
    simpa [negSeq] using h hij

/-- Consequently `LDS (negSeq seq) = LIS seq`: the achievable decreasing lengths of `-seq` are
exactly the achievable increasing lengths of `seq`. -/
theorem LDS_negSeq (seq : RealSeq n) : LDS (negSeq seq) = LIS seq := by
  have hset : {m | ∃ sub : Subsequence n m, IsDecreasing (negSeq seq) sub}
            = {m | ∃ sub : Subsequence n m, IsIncreasing seq sub} := by
    ext m
    simp only [Set.mem_setOf_eq]
    exact ⟨fun ⟨sub, h⟩ => ⟨sub, isDecreasing_negSeq_iff.mp h⟩,
           fun ⟨sub, h⟩ => ⟨sub, isDecreasing_negSeq_iff.mpr h⟩⟩
  unfold LDS LIS
  rw [hset]

/-- Negation is injective, so `negSeq seq` has distinct entries iff `seq` does. -/
lemma negSeq_injective_iff {seq : RealSeq n} :
    Function.Injective (negSeq seq) ↔ Function.Injective seq := by
  constructor
  · intro h a b hab
    exact h (by simp only [negSeq, hab])
  · intro h a b hab
    simp only [negSeq, neg_inj] at hab
    exact h hab

/-- A decomposition of `seq` into strictly-*decreasing* covering subsequences (dual of
`IncreasingDecomposition`). -/
structure DecreasingDecomposition (n : ℕ) (seq : RealSeq n) where
  numParts : ℕ
  parts : Fin numParts → Σ m, Subsequence n m
  decreasing : ∀ i, IsDecreasing seq (parts i).2
  disjoint : ∀ i j k₁ k₂, i ≠ j →
    (parts i).2.indices k₁ ≠ (parts j).2.indices k₂
  covering : ∀ k : Fin n, ∃ i m hm, (parts i).2.indices ⟨m, hm⟩ = k

/-- A decreasing decomposition of `seq` is an increasing decomposition of `-seq` (same parts). -/
def DecreasingDecomposition.toIncreasingNeg {seq : RealSeq n}
    (D : DecreasingDecomposition n seq) : IncreasingDecomposition n (negSeq seq) where
  numParts := D.numParts
  parts := D.parts
  increasing := fun i => isIncreasing_negSeq_iff.mpr (D.decreasing i)
  disjoint := D.disjoint
  covering := D.covering

/-- Conversely an increasing decomposition of `-seq` is a decreasing decomposition of `seq`. -/
def IncreasingDecomposition.toDecreasingOfNeg {seq : RealSeq n}
    (D : IncreasingDecomposition n (negSeq seq)) : DecreasingDecomposition n seq where
  numParts := D.numParts
  parts := D.parts
  decreasing := fun i => isIncreasing_negSeq_iff.mp (D.increasing i)
  disjoint := D.disjoint
  covering := D.covering

/-- Split into `n` singleton parts; obtained by transporting the singleton *increasing*
decomposition of `-seq` (a single element is both increasing and decreasing). Makes the class
nonempty with `numParts = n`. -/
def singletonDecreasingDecomposition (seq : RealSeq n) : DecreasingDecomposition n seq :=
  (singletonIncreasingDecomposition (negSeq seq)).toDecreasingOfNeg

/-- The minimum number of strictly-decreasing parts needed to cover `seq`. -/
noncomputable def minDecreasingParts (seq : RealSeq n) : ℕ :=
  sInf {p | ∃ D : DecreasingDecomposition n seq, D.numParts = p}

/-- Every decreasing decomposition is in particular a monotonic one. -/
def DecreasingDecomposition.toMonotonic {seq : RealSeq n} (D : DecreasingDecomposition n seq) :
    MonotonicDecomposition n seq where
  numParts := D.numParts
  parts := D.parts
  monotonic := fun i => Or.inr (D.decreasing i)
  disjoint := D.disjoint
  covering := D.covering

/-- The part-count-preserving bijection makes the two covering numbers agree. -/
theorem minDecreasingParts_eq_minIncreasingParts_negSeq (seq : RealSeq n) :
    minDecreasingParts seq = minIncreasingParts (negSeq seq) := by
  have hset : {p | ∃ D : DecreasingDecomposition n seq, D.numParts = p}
            = {p | ∃ D : IncreasingDecomposition n (negSeq seq), D.numParts = p} := by
    ext p
    simp only [Set.mem_setOf_eq]
    exact ⟨fun ⟨D, hD⟩ => ⟨D.toIncreasingNeg, hD⟩,
           fun ⟨D, hD⟩ => ⟨D.toDecreasingOfNeg, hD⟩⟩
  unfold minDecreasingParts minIncreasingParts
  rw [hset]

/-- **The dual Mirsky/Dilworth min–max identity for sequences.** For a sequence of distinct reals,
the minimum number of strictly-decreasing subsequences needed to cover it equals the length of the
longest strictly-increasing subsequence. -/
theorem minDecreasingParts_eq_LIS (seq : RealSeq n) (hinj : Function.Injective seq) :
    minDecreasingParts seq = LIS seq := by
  rw [minDecreasingParts_eq_minIncreasingParts_negSeq,
      minIncreasingParts_eq_LDS (negSeq seq) (negSeq_injective_iff.mpr hinj),
      LDS_negSeq]

/-- Covering by *decreasing* parts is at least as costly as covering by *monotone* parts. -/
theorem minMonotonicParts_le_minDecreasingParts (seq : RealSeq n) :
    minMonotonicParts seq ≤ minDecreasingParts seq := by
  apply le_csInf
  · exact ⟨n, singletonDecreasingDecomposition seq, rfl⟩
  · rintro p ⟨D, rfl⟩
    exact Nat.sInf_le ⟨D.toMonotonic, rfl⟩

/-- The dual identity gives the second half of the sharp monotone upper bound. -/
theorem minMonotonicParts_le_LIS (seq : RealSeq n) (hinj : Function.Injective seq) :
    minMonotonicParts seq ≤ LIS seq :=
  (minMonotonicParts_le_minDecreasingParts seq).trans (minDecreasingParts_eq_LIS seq hinj).le

/-- **Sharp monotone upper bound.** For distinct reals, covering by monotone parts costs at most
`min (LIS, LDS)` — the two identities together close the monotone bracket to
`minMonotonicParts seq ∈ [n / max (LIS, LDS), min (LIS, LDS)]`. -/
theorem minMonotonicParts_le_min_LIS_LDS (seq : RealSeq n) (hinj : Function.Injective seq) :
    minMonotonicParts seq ≤ min (LIS seq) (LDS seq) :=
  le_min (minMonotonicParts_le_LIS seq hinj) (minMonotonicParts_le_LDS seq hinj)

end Erdos1026OQ05IncreasingIdentity

