/-
# erdos-1026-oq-05 (k-monotonic companion): decompositions into k-monotone parts

`Erdos1026OQ05.lean` studies decompositions of a length-`n` real sequence into *monotonic*
(increasing OR decreasing) subsequences and brackets the optimal part count
`minMonotonicParts seq ∈ [n / max(LIS, LDS), n]`.

This file carries out the natural **k-monotonic** generalization requested by OQ-05: instead of
requiring each part to be a *single* monotone run, allow each part to be a union of up to `k`
monotone runs (a "k-monotone" piece — a sequence that changes direction at most `k - 1` times).
The relevant covering number `minKMonotonicParts k seq` interpolates between the singleton
decomposition (`k = n`, one part) and the monotone decomposition (`k = 1`).

The key structural facts, all elementary and self-contained (importing only the committed base
file):

* **Length bound** `len_le_kmono`: a k-monotone subsequence has length `≤ k · max(LIS, LDS)`.
  Its index image is covered by `k` monotone runs, each of length `≤ max(LIS, LDS)`
  (`len_le_max_of_monotonic`), so a `Finset.card_biUnion_le` counting argument bounds the total.

* **Counting lower bound** `kMonotonicDecomposition_numParts_lower_bound`:
  `n ≤ numParts · (k · max(LIS, LDS))` — the same covering surjection as the monotone case, now
  charging each part the k-monotone length budget.

* **Sandwich** `minKMonotonicParts_bracket` (for `k ≥ 1`):
      n / (k · max(LIS, LDS))  ≤  minKMonotonicParts k seq  ≤  minMonotonicParts seq.
  The upper half `minKMonotonicParts_le_minMonotonicParts` embeds every monotone decomposition into
  a k-monotone one (a monotone part is trivially a k-monotone part with constant runs), so allowing
  more runs never *increases* the covering number. The lower half weakens as `k` grows — allowing
  more runs per part lets you use fewer parts, exactly as expected.

No axioms, no sorries.
-/

import Mathlib
import Proofs.Erdos1026OQ05

open Finset

namespace Erdos1026OQ05KMonotonic

open Erdos1026OQ05

variable {n m : ℕ}

/-! ## k-monotone subsequences -/

/-- A subsequence is **k-monotonic** if its index image is covered by `k` monotonic subsequences
("runs"). Concretely: there are `k` monotone subsequences `runs j` such that every index of `sub`
is an index of some run. For `k = 1` this is (a covering form of) monotonicity; larger `k` permits
a piece that changes direction up to `k - 1` times. -/
def IsKMonotonic (k : ℕ) (seq : RealSeq n) (sub : Subsequence n m) : Prop :=
  ∃ runs : Fin k → Σ p, Subsequence n p,
    (∀ j, IsMonotonic seq (runs j).2) ∧
    (∀ a : Fin m, ∃ j b, (runs j).2.indices b = sub.indices a)

/-- A monotone subsequence is `k`-monotone for any `k ≥ 1`: take all `k` runs to be the subsequence
itself. (The covering condition only needs a single run, so we may repeat it.) -/
theorem IsMonotonic.isKMonotonic {k : ℕ} (hk : 0 < k) {seq : RealSeq n}
    {sub : Subsequence n m} (h : IsMonotonic seq sub) : IsKMonotonic k seq sub :=
  ⟨fun _ => ⟨m, sub⟩, fun _ => h, fun a => ⟨⟨0, hk⟩, a, rfl⟩⟩

/-- **Core length bound.** A k-monotone subsequence has length at most `k · max(LIS, LDS)`.

Its index image sits inside the union of the `k` runs' images; each run is monotone, so its image
has at most `max(LIS, LDS)` elements, and `Finset.card_biUnion_le` sums the budgets. This is the
exact k-monotone analogue of `len_le_max_of_monotonic` (the `k = 1` case, up to the trivial
`m ≤ 1 · max = max`). -/
theorem len_le_kmono {k : ℕ} {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsKMonotonic k seq sub) : m ≤ k * max (LIS seq) (LDS seq) := by
  classical
  obtain ⟨runs, hmono, hcov⟩ := h
  -- The image of `sub` (which has exactly `m` elements) is covered by the runs' images.
  set S : Finset (Fin n) := Finset.image sub.indices Finset.univ with hS
  have hScard : S.card = m := by
    rw [hS, Finset.card_image_of_injective _ sub.strictMono.injective,
      Finset.card_univ, Fintype.card_fin]
  have hsub : S ⊆ Finset.univ.biUnion
      (fun j : Fin k => Finset.image (runs j).2.indices Finset.univ) := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨j, b, hjb⟩ := hcov a
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ _, Finset.mem_image.2 ⟨b, Finset.mem_univ _, hjb⟩⟩
  calc m = S.card := hScard.symm
    _ ≤ (Finset.univ.biUnion
          (fun j : Fin k => Finset.image (runs j).2.indices Finset.univ)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j : Fin k, (Finset.image (runs j).2.indices Finset.univ).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin k, max (LIS seq) (LDS seq) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ, Fintype.card_fin]
        exact len_le_max_of_monotonic (hmono j)
    _ = k * max (LIS seq) (LDS seq) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## k-monotone decompositions and their covering number -/

/-- A decomposition of a sequence into **k-monotonic** parts whose images cover every index.
Identical to `MonotonicDecomposition` but with each part only required to be `k`-monotone (a union
of up to `k` monotone runs) rather than a single monotone run. -/
structure KMonotonicDecomposition (k n : ℕ) (seq : RealSeq n) where
  numParts : ℕ
  parts : Fin numParts → Σ m, Subsequence n m
  kmonotonic : ∀ i, IsKMonotonic k seq (parts i).2
  disjoint : ∀ i j k₁ k₂, i ≠ j →
    (parts i).2.indices k₁ ≠ (parts j).2.indices k₂
  covering : ∀ x : Fin n, ∃ i m hm, (parts i).2.indices ⟨m, hm⟩ = x

/-- **k-monotone counting lower bound.** Every k-monotone decomposition uses enough parts that
`numParts · (k · max(LIS, LDS)) ≥ n`. The covering condition assembles the parts' index maps into a
surjection from `Σ i, Fin (length of part i)` onto `Fin n`, and each part now has length at most
`k · max(LIS, LDS)` (`len_le_kmono`). For `k = 1` this is
`monotonicDecomposition_numParts_lower_bound`. -/
theorem kMonotonicDecomposition_numParts_lower_bound {k : ℕ} (seq : RealSeq n)
    (D : KMonotonicDecomposition k n seq) :
    n ≤ D.numParts * (k * max (LIS seq) (LDS seq)) := by
  classical
  let g : (Σ i : Fin D.numParts, Fin (D.parts i).1) → Fin n :=
    fun p => (D.parts p.1).2.indices p.2
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨i, mm, hm, hx⟩ := D.covering x
    exact ⟨⟨i, ⟨mm, hm⟩⟩, hx⟩
  have hcard : Fintype.card (Fin n)
      ≤ Fintype.card (Σ i : Fin D.numParts, Fin (D.parts i).1) :=
    Fintype.card_le_of_surjective g hsurj
  rw [Fintype.card_fin, Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  refine hcard.trans ?_
  calc ∑ i, (D.parts i).1
      ≤ ∑ _i : Fin D.numParts, k * max (LIS seq) (LDS seq) :=
        Finset.sum_le_sum (fun i _ => len_le_kmono (D.kmonotonic i))
    _ = D.numParts * (k * max (LIS seq) (LDS seq)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Division form of the lower bound: any k-monotone decomposition uses at least
`n / (k · max(LIS, LDS))` parts. -/
theorem kMonotonicDecomposition_numParts_ge {k : ℕ} (seq : RealSeq n)
    (D : KMonotonicDecomposition k n seq) :
    n / (k * max (LIS seq) (LDS seq)) ≤ D.numParts := by
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm]
  exact kMonotonicDecomposition_numParts_lower_bound seq D

/-- Every monotone decomposition is a `k`-monotone decomposition for `k ≥ 1`: each monotone part is
trivially a k-monotone part (via `IsMonotonic.isKMonotonic`), and the disjointness and covering data
carry over unchanged. -/
def monotonicToKMonotonic {k : ℕ} (hk : 0 < k) {seq : RealSeq n}
    (D : MonotonicDecomposition n seq) : KMonotonicDecomposition k n seq where
  numParts := D.numParts
  parts := D.parts
  kmonotonic := fun i => IsMonotonic.isKMonotonic hk (D.monotonic i)
  disjoint := D.disjoint
  covering := D.covering

/-- The **minimum number of k-monotone parts** needed to cover `seq`: the k-monotone covering number.
Well-defined for `k ≥ 1` because `singletonDecomposition` (embedded via `monotonicToKMonotonic`) always
supplies a k-monotone decomposition, so the achievable part-counts form a nonempty set. -/
noncomputable def minKMonotonicParts (k : ℕ) (seq : RealSeq n) : ℕ :=
  sInf {p | ∃ D : KMonotonicDecomposition k n seq, D.numParts = p}

/-- The k-monotone covering number never exceeds the ordinary monotone covering number (`k ≥ 1`):
the optimal monotone decomposition is, in particular, a k-monotone decomposition, so its part count
is an upper bound for the k-monotone infimum. Allowing more runs per part cannot force *more* parts. -/
theorem minKMonotonicParts_le_minMonotonicParts {k : ℕ} (hk : 0 < k) (seq : RealSeq n) :
    minKMonotonicParts k seq ≤ minMonotonicParts seq := by
  classical
  have hne : {p | ∃ D : MonotonicDecomposition n seq, D.numParts = p}.Nonempty :=
    ⟨n, singletonDecomposition seq, rfl⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hEq : minMonotonicParts seq = D.numParts := hD.symm
  rw [hEq]
  unfold minKMonotonicParts
  apply Nat.sInf_le
  exact ⟨monotonicToKMonotonic hk D, rfl⟩

/-- The k-monotone covering number is at least `n / (k · max(LIS, LDS))` (`k ≥ 1`): the elementary
counting lower bound holds for *every* k-monotone decomposition, hence for the optimal one. -/
theorem minKMonotonicParts_ge {k : ℕ} (hk : 0 < k) (seq : RealSeq n) :
    n / (k * max (LIS seq) (LDS seq)) ≤ minKMonotonicParts k seq := by
  unfold minKMonotonicParts
  apply le_csInf
  · exact ⟨n, monotonicToKMonotonic hk (singletonDecomposition seq), rfl⟩
  · rintro p ⟨D, rfl⟩
    exact kMonotonicDecomposition_numParts_ge seq D

/-- **The k-monotone covering number is sandwiched** (`k ≥ 1`):

    n / (k · max(LIS, LDS))  ≤  minKMonotonicParts k seq  ≤  minMonotonicParts seq.

The lower bound is the k-monotone Mirsky/Dilworth counting half; it weakens as `k` grows, reflecting
that a part allowed more direction-changes can absorb more of the sequence. The upper bound says the
covering number is monotone (non-increasing) in the allowed run-count `k`, pinned at `k = 1` by the
ordinary monotone covering number. -/
theorem minKMonotonicParts_bracket {k : ℕ} (hk : 0 < k) (seq : RealSeq n) :
    n / (k * max (LIS seq) (LDS seq)) ≤ minKMonotonicParts k seq ∧
      minKMonotonicParts k seq ≤ minMonotonicParts seq :=
  ⟨minKMonotonicParts_ge hk seq, minKMonotonicParts_le_minMonotonicParts hk seq⟩

/-! ## The exact `k = 1` identity: `minKMonotonicParts 1 = minMonotonicParts`

The bracket above only pins `minKMonotonicParts k ≤ minMonotonicParts` from one side. At
`k = 1` this is an **equality**: a `1`-monotone piece — a subsequence covered by a *single*
monotone run — is itself monotone, so `1`-monotone decompositions and ordinary monotone
decompositions coincide. -/

/-- **A `1`-monotone subsequence is monotone.**  If `sub` is `k`-monotone with `k = 1`, its
single covering run `runs 0` is monotone and every index of `sub` is an index of that run.
Since the run's index map is strictly monotone, the inclusion `sub ↪ run` is order-preserving,
so the monotonicity (increasing or decreasing) of the run transfers verbatim to `sub`. This is
the reverse of `IsMonotonic.isKMonotonic` at `k = 1`. -/
theorem IsKMonotonic.isMonotonic_of_one {seq : RealSeq n} {sub : Subsequence n m}
    (h : IsKMonotonic 1 seq sub) : IsMonotonic seq sub := by
  obtain ⟨runs, hmono, hcov⟩ := h
  set R := (runs 0).2 with hR
  -- The covering index `j : Fin 1` is forced to be `0`, so every index of `sub` is an index of `R`.
  have hcov0 : ∀ a : Fin m, ∃ b, R.indices b = sub.indices a := by
    intro a
    obtain ⟨j, b, hjb⟩ := hcov a
    have hj0 : j = 0 := Subsingleton.elim _ _
    subst hj0
    exact ⟨b, hjb⟩
  choose b hb using hcov0
  -- The induced inclusion `b : Fin m → Fin p` is strictly monotone (order-reflecting run indices).
  have hbmono : StrictMono b := by
    intro a a' haa'
    have h1 : R.indices (b a) < R.indices (b a') := by
      rw [hb a, hb a']; exact sub.strictMono haa'
    exact R.strictMono.lt_iff_lt.mp h1
  rcases hmono 0 with hInc | hDec
  · -- Increasing run ⇒ increasing subsequence.
    left
    intro a a' haa'
    show seq (sub.indices a) < seq (sub.indices a')
    rw [← hb a, ← hb a']
    exact hInc (hbmono haa')
  · -- Decreasing run ⇒ decreasing subsequence.
    right
    intro a a' haa'
    rw [← hb a, ← hb a']
    exact hDec (b a) (b a') (hbmono haa')

/-- A `1`-monotone decomposition is exactly an ordinary monotone decomposition: each part,
being `1`-monotone, is monotone (`IsKMonotonic.isMonotonic_of_one`); disjointness and covering
carry over unchanged. Inverse of `monotonicToKMonotonic` at `k = 1`. -/
def kMonotonicToMonotonic_one {seq : RealSeq n}
    (D : KMonotonicDecomposition 1 n seq) : MonotonicDecomposition n seq where
  numParts := D.numParts
  parts := D.parts
  monotonic := fun i => (D.kmonotonic i).isMonotonic_of_one
  disjoint := D.disjoint
  covering := D.covering

/-- The reverse inequality to `minKMonotonicParts_le_minMonotonicParts` at `k = 1`: the optimal
`1`-monotone decomposition is an ordinary monotone decomposition of the same size, so the monotone
covering number does not exceed the `1`-monotone one. -/
theorem minMonotonicParts_le_minKMonotonicParts_one (seq : RealSeq n) :
    minMonotonicParts seq ≤ minKMonotonicParts 1 seq := by
  classical
  have hne : {p | ∃ D : KMonotonicDecomposition 1 n seq, D.numParts = p}.Nonempty :=
    ⟨n, monotonicToKMonotonic Nat.one_pos (singletonDecomposition seq), rfl⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hEq : minKMonotonicParts 1 seq = D.numParts := hD.symm
  rw [hEq]
  unfold minMonotonicParts
  apply Nat.sInf_le
  exact ⟨kMonotonicToMonotonic_one D, rfl⟩

/-- **Exact `k = 1` identity.**  `minKMonotonicParts 1 seq = minMonotonicParts seq`: allowing a
single run per part is no different from requiring each part to be monotone. This pins the
`k = 1` endpoint of the covering-number bracket `minKMonotonicParts_bracket` to an equality,
completing the "non-increasing in `k`, pinned at the monotone covering number" picture. -/
theorem minKMonotonicParts_one_eq_minMonotonicParts (seq : RealSeq n) :
    minKMonotonicParts 1 seq = minMonotonicParts seq :=
  le_antisymm (minKMonotonicParts_le_minMonotonicParts Nat.one_pos seq)
    (minMonotonicParts_le_minKMonotonicParts_one seq)

end Erdos1026OQ05KMonotonic
