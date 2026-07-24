/-
  The complexity of finding the actual monotonic subsequence — the computable layer
  (Open Question OQ-02 of erdos-szekeres:
   "What is the complexity of finding the actual monotonic subsequence?")

  ## What this file establishes (0 sorry, 0 axiom)

  The parent file `ErdosSzekeres.lean` measures longest increasing subsequences
  through `maxIncLen f i = Nat.findGreatest (HasIncreasingEndingAt f i) (i.val + 1)`,
  which is `noncomputable` (a Classical search over a `Prop` existential): the parent
  can say a monotone subsequence *exists* but cannot produce one. OQ-02 asks how
  expensive it is to actually *find* the subsequence. This file formalizes the
  classical answer's elementary layer:

    * `incDP` — a COMPUTABLE (no `noncomputable` marker) dynamic program computing
      the longest-increasing-subsequence length ending at each position, by
      well-founded recursion over the position:
      `incDP f i = 1 + max { incDP f j : j < i, f j < f i }` (`incDP_eq`).
    * `exactIncEnd_incDP` — the DP value is realized: for every `i` there is a
      strictly increasing position map of length `incDP f i` with strictly
      increasing values, bounded by `i` and ending exactly at `i`. Consequently
      `HasIncreasingEndingAt f i (incDP f i)` — the parent's own ending-at
      predicate — holds (`hasIncreasingEndingAt_incDP`), and an
      `IncreasingSubseq f (incDP f i)` exists (`exists_increasingSubseq_incDP`).
    * `incDP_le_maxIncLen` — the DP is sound against the parent's noncomputable
      spec: `incDP f i ≤ maxIncLen f i`. (The converse inequality — optimal
      substructure — is the remaining half of full correctness; see below.)
    * `incDPcost_closed` / `incDPcost_two_mul` — the exact comparison count. The
      DP at position `i` scans every candidate `j < i` (`scanned`/`card_scanned`,
      and the actual predecessor set satisfies `preds_subset_scanned`), so the
      total number of scanned pairs is `incDPcost n = ∑ i, |Iio i|`, with the
      proved closed forms `incDPcost n = n * (n - 1) / 2` and
      `incDPcost n * 2 = n * (n - 1)` — the Θ(n²) bound as an exact equation.

  ## The cost-model judgement

  Mathlib has no cost monad, RAM model, or comparison-decision-tree machinery, so
  asymptotic statements ("Θ(n log n)") have no formal home. Following the Garner
  precedent (chinese-remainder-non-coprime-oq-01-oq-02), complexity is formalized
  as an explicit `Nat`-valued operation counter with a proved closed form. The
  literature answer to OQ-02 beyond this file — patience sorting computes the LIS
  in Θ(n log n) comparisons (Mallows 1963, Schensted 1961) and Fredman (1975)
  proved a matching Ω(n log n) comparison lower bound, so Θ(n log n) is optimal —
  is documented here but is out of Lean scope without a comparison-cost model.

  ## Remaining milestones (tracked in research/problems/erdos-szekeres-oq-02/)

  * Full correctness `incDP f i = maxIncLen f i`: needs the optimal-substructure
    (stripping) argument for `maxIncLen f i ≤ incDP f i`; sequenced after sibling
    oq-01's extension lemma to avoid duplicating shared infrastructure.
  * Executable witness data `incWitness f i : IncreasingSubseq f (incDP f i)` via
    computable argmax selection (`List.argmax`), turning the `Nonempty` here into
    a program that returns the actual index map.

  Depends on: `Proofs/ErdosSzekeres.lean` (definitions only — no axiom of the
  parent is used; every result here is axiom-free, `#print axioms` shows only
  propext/Classical.choice/Quot.sound).
-/

import Mathlib
import Proofs.ErdosSzekeres

namespace ErdosSzekeresOQ02

open Finset ErdosSzekeres

variable {α : Type*} [LinearOrder α] {n : ℕ}

/- ## The dynamic program

`incDP f i` is the classical quadratic-time recurrence for the length of the
longest strictly increasing subsequence ending at position `i`: one more than
the best value over admissible predecessors (earlier positions with smaller
values). Unlike the parent's `maxIncLen`, this is a computable function — the
recursion is well-founded on `i.val`, and the predecessor set is a decidable
`Finset` filter.
-/

/-- The predecessor set scanned by the DP at position `i`: earlier positions
    with strictly smaller values. -/
def preds (f : Sequence α n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j < i ∧ f j < f i)

lemma mem_preds {f : Sequence α n} {i j : Fin n} :
    j ∈ preds f i ↔ j < i ∧ f j < f i := by
  simp [preds]

/-- Computable longest-increasing-subsequence-ending-at-`i` length, by the
    classical quadratic dynamic program. Compare the parent's `noncomputable
    maxIncLen`. -/
def incDP (f : Sequence α n) (i : Fin n) : ℕ :=
  1 + (preds f i).attach.sup (fun j => incDP f j.1)
termination_by i.val
decreasing_by
  exact (mem_preds.mp j.2).1

/-- The DP recurrence in `attach`-free form:
    `incDP f i = 1 + sup { incDP f j : j < i, f j < f i }`. -/
theorem incDP_eq (f : Sequence α n) (i : Fin n) :
    incDP f i = 1 + (preds f i).sup (fun j => incDP f j) := by
  rw [incDP, Finset.sup_attach]

/-- Every position carries at least the singleton subsequence. -/
theorem one_le_incDP (f : Sequence α n) (i : Fin n) : 1 ≤ incDP f i := by
  rw [incDP_eq]
  exact Nat.le_add_right 1 _

/-- A subsequence ending at position `i` uses positions `≤ i`, so its length is
    at most `i.val + 1`. This is the bound that lets the DP value enter the
    parent's `Nat.findGreatest (· ) (i.val + 1)` search window. -/
theorem incDP_le_index_succ (f : Sequence α n) (i : Fin n) :
    incDP f i ≤ i.val + 1 := by
  rw [incDP_eq]
  have h : (preds f i).sup (fun j => incDP f j) ≤ i.val := by
    refine Finset.sup_le fun j hj => ?_
    have hji : j.val < i.val := (mem_preds.mp hj).1
    have hrec : incDP f j ≤ j.val + 1 := incDP_le_index_succ f j
    omega
  omega
termination_by i.val
decreasing_by exact hji

/- ## Realizing the DP value

The parent's `HasIncreasingEndingAt` allows the final position to fall short of
`i` in degenerate branches, which is too weak to extend chains: knowing only
`f j < f i` says nothing about the values at positions strictly before `j`.
`ExactIncEnd` strengthens the invariant to "ends exactly at `i`", which makes
the one-step extension by a new maximum position go through, and afterwards
downgrades to the parent's predicate.
-/

/-- An increasing subsequence of length `len` ending *exactly* at `i`: strictly
    increasing positions with strictly increasing values, all positions `≤ i`,
    and the last position equal to `i`. -/
def ExactIncEnd (f : Sequence α n) (i : Fin n) (len : ℕ) : Prop :=
  ∃ k : Fin len → Fin n,
    StrictMono k ∧ StrictMono (f ∘ k) ∧ (∀ a, k a ≤ i) ∧
    (∀ a : Fin len, a.val = len - 1 → k a = i)

/-- The singleton chain at `i`. -/
theorem exactIncEnd_one (f : Sequence α n) (i : Fin n) : ExactIncEnd f i 1 := by
  refine ⟨fun _ => i, ?_, ?_, fun _ => le_refl i, fun _ _ => rfl⟩
  · intro a b hab
    exact absurd hab (Subsingleton.elim a b ▸ lt_irrefl _)
  · intro a b hab
    exact absurd hab (Subsingleton.elim a b ▸ lt_irrefl _)

/-- Exact chains satisfy the parent's ending-at predicate. -/
theorem ExactIncEnd.hasIncreasingEndingAt {f : Sequence α n} {i : Fin n} {len : ℕ}
    (h : ExactIncEnd f i len) : HasIncreasingEndingAt f i len := by
  obtain ⟨k, hmono, hvals, hle, hlast⟩ := h
  refine ⟨k, hmono, fun a => ?_, hvals⟩
  by_cases ha : a.val = len - 1
  · exact Or.inr ⟨ha, hlast a ha⟩
  · left
    have hpos : 0 < len := a.pos
    have h1 : len - 1 < len := by omega
    have hlt : a < (⟨len - 1, h1⟩ : Fin len) := by
      rw [Fin.lt_def]
      have := a.isLt
      simp only []
      omega
    have hmlt := hmono hlt
    rw [hlast ⟨len - 1, h1⟩ rfl] at hmlt
    exact hmlt

/-- One-step extension: an exact chain to `j` extends by any later, larger
    position `i` to an exact chain of length `len + 1`, via `Fin.snoc`. The
    `ends exactly at j` invariant is what makes the value comparison at the
    junction available (`f (k a) < f j < f i` for interior positions). -/
theorem ExactIncEnd.extend {f : Sequence α n} {j i : Fin n} {len : ℕ}
    (hlen : 1 ≤ len) (h : ExactIncEnd f j len) (hji : j < i) (hfji : f j < f i) :
    ExactIncEnd f i (len + 1) := by
  obtain ⟨k, hmono, hvals, hle, hlast⟩ := h
  have hki : ∀ a : Fin len, k a < i := fun a => lt_of_le_of_lt (hle a) hji
  have hfki : ∀ a : Fin len, f (k a) < f i := by
    intro a
    by_cases ha : a.val = len - 1
    · rw [hlast a ha]
      exact hfji
    · have h1 : len - 1 < len := by omega
      have hlt : a < (⟨len - 1, h1⟩ : Fin len) := by
        rw [Fin.lt_def]
        have := a.isLt
        simp only []
        omega
      have h2 := hvals hlt
      simp only [Function.comp_apply] at h2
      rw [hlast ⟨len - 1, h1⟩ rfl] at h2
      exact lt_trans h2 hfji
  refine ⟨Fin.snoc k i, ?_, ?_, ?_, ?_⟩
  · -- positions strictly increase
    intro a b hab
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hmono (Fin.castSucc_lt_castSucc_iff.mp hab)
      · exact absurd hab (not_lt.mpr (Fin.castSucc_lt_last b').le)
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hki a'
      · exact absurd hab (lt_irrefl _)
  · -- values strictly increase
    rw [Fin.comp_snoc]
    intro a b hab
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvals (Fin.castSucc_lt_castSucc_iff.mp hab)
      · exact absurd hab (not_lt.mpr (Fin.castSucc_lt_last b').le)
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hfki a'
      · exact absurd hab (lt_irrefl _)
  · -- bounded by i
    intro a
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact (hki a').le
    · rw [Fin.snoc_last]
  · -- ends at i
    intro a ha
    have haeq : a = Fin.last len := by
      apply Fin.ext
      simpa using ha
    rw [haeq, Fin.snoc_last]

/-- **The DP value is realized**: for every position there is an exact chain of
    length `incDP f i` ending at `i`. Well-founded recursion mirroring the DP:
    an empty predecessor set gives the singleton; otherwise extend an exact
    chain of a predecessor attaining the `Finset.sup`. -/
theorem exactIncEnd_incDP (f : Sequence α n) (i : Fin n) :
    ExactIncEnd f i (incDP f i) := by
  rcases (preds f i).eq_empty_or_nonempty with he | hne
  · rw [incDP_eq, he]
    simpa using exactIncEnd_one f i
  · obtain ⟨j₀, hj₀mem, hsup⟩ := Finset.exists_mem_eq_sup (preds f i) hne (fun j => incDP f j)
    have hj₀ := mem_preds.mp hj₀mem
    have hrec : ExactIncEnd f j₀ (incDP f j₀) := exactIncEnd_incDP f j₀
    have hext := hrec.extend (one_le_incDP f j₀) hj₀.1 hj₀.2
    rw [incDP_eq, hsup, Nat.add_comm]
    exact hext
termination_by i.val
decreasing_by exact hj₀.1

/-- The parent's ending-at predicate holds at the DP value. -/
theorem hasIncreasingEndingAt_incDP (f : Sequence α n) (i : Fin n) :
    HasIncreasingEndingAt f i (incDP f i) :=
  (exactIncEnd_incDP f i).hasIncreasingEndingAt

/-- **Soundness against the noncomputable spec**: the computable DP never
    exceeds the parent's `maxIncLen`. (The converse — optimal substructure —
    is the remaining half of full correctness.) -/
theorem incDP_le_maxIncLen (f : Sequence α n) (i : Fin n) :
    incDP f i ≤ maxIncLen f i := by
  classical
  show incDP f i ≤ Nat.findGreatest (HasIncreasingEndingAt f i) (i.val + 1)
  exact Nat.le_findGreatest (incDP_le_index_succ f i) (hasIncreasingEndingAt_incDP f i)

/-- An actual `IncreasingSubseq` (the parent's subsequence structure) of the DP
    length exists at every position. -/
theorem exists_increasingSubseq_incDP (f : Sequence α n) (i : Fin n) :
    Nonempty (IncreasingSubseq f (incDP f i)) := by
  obtain ⟨k, hmono, hvals, -, -⟩ := exactIncEnd_incDP f i
  exact ⟨⟨k, hmono, hvals⟩⟩

/- ## The exact comparison count

The DP at position `i` tests every candidate `j < i` once (the `preds` filter
evaluates `j < i ∧ f j < f i` over all of `Fin n`, and the order-comparison
work is the `i.val` candidates below `i`). `incDPcost` counts exactly these
scanned pairs `(j, i)` with `j < i` — that is, `∑ i |Iio i| = C(n, 2)` — the
Θ(n²) comparison bound as an exact closed form, division-free variant included.
-/

/-- Candidate positions scanned by the DP at position `i`: every `j < i`. -/
def scanned (i : Fin n) : Finset (Fin n) := Finset.Iio i

/-- The admissible predecessors are among the scanned candidates. -/
theorem preds_subset_scanned (f : Sequence α n) (i : Fin n) :
    preds f i ⊆ scanned i := by
  intro j hj
  rw [scanned, Finset.mem_Iio]
  exact (mem_preds.mp hj).1

/-- Position `i` scans exactly `i.val` candidates. -/
theorem card_scanned (i : Fin n) : (scanned i).card = i.val := by
  rw [scanned]
  exact Fin.card_Iio i

/-- Total number of candidate pairs scanned by the DP on a length-`n` input. -/
def incDPcost (n : ℕ) : ℕ := ∑ i : Fin n, (Finset.Iio i).card

theorem incDPcost_eq_sum (n : ℕ) : incDPcost n = ∑ i : Fin n, i.val := by
  unfold incDPcost
  exact Finset.sum_congr rfl fun i _ => Fin.card_Iio i

/-- **The exact quadratic comparison count**: `incDPcost n = n(n-1)/2`. -/
theorem incDPcost_closed (n : ℕ) : incDPcost n = n * (n - 1) / 2 := by
  rw [incDPcost_eq_sum, Fin.sum_univ_eq_sum_range (fun i => i)]
  exact Finset.sum_range_id n

/-- Division-free form: `2 · incDPcost n = n(n-1)`. -/
theorem incDPcost_two_mul (n : ℕ) : incDPcost n * 2 = n * (n - 1) := by
  rw [incDPcost_eq_sum, Fin.sum_univ_eq_sum_range (fun i => i)]
  exact Finset.sum_range_id_mul_two n

/- ## Executable smoke tests

`incDP` is computable, so `#eval` runs it directly — this is the point of the
OQ: the parent's `maxIncLen` admits no such evaluation. On [3,1,4,1,5,9,2,6]
the DP table is [1,1,2,1,3,4,2,4] (e.g. 3,4,5,9 ends at position 5; 3,4,5,6
ends at position 7), and `incDPcost 8 = 28 = 8·7/2`.
-/

#eval incDP (![3, 1, 4, 1, 5, 9, 2, 6] : Fin 8 → ℕ) 7
#eval (List.ofFn fun i : Fin 8 => incDP (![3, 1, 4, 1, 5, 9, 2, 6] : Fin 8 → ℕ) i)
#eval incDPcost 8

end ErdosSzekeresOQ02
