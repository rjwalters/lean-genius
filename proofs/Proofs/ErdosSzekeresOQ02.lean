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
      spec: `incDP f i ≤ maxIncLen f i`.
    * `ExactIncEnd.le_incDP` / `exactIncEnd_iff_le_incDP` — **optimal
      substructure (stripping)**: `incDP f i` is *exactly* the maximum length of
      an increasing subsequence ending exactly at `i` (a chain of length `len`
      ending at `i` exists iff `len ≤ incDP f i`).
    * `maxIncLen_eq_sup_Iic` — **the corrected full-correctness bridge**:
      `maxIncLen f i = (Iic i).sup (incDP f)`. The naive pointwise equality
      `incDP f i = maxIncLen f i` is **false** — the parent's
      `HasIncreasingEndingAt` disjunction `k j < i ∨ (last ∧ k j = i)` never
      *forces* the chain to touch `i`, so `maxIncLen` actually measures the
      longest chain among positions `≤ i` (a running maximum), not the longest
      chain ending at `i` that its docstring describes. The refutation is
      formalized (`incDP_lt_maxIncLen_counterexample`: on `[1,2,0]` at `i = 2`,
      `maxIncLen = 2` but `incDP = 1`), and the bridge is the honest correct
      statement, proved in both directions.
    * `lisLength` / `lisLength_eq_sup_maxIncLen` — the computable global LIS
      length, agreeing with the supremum of the parent's measure.
    * `incChain` / `incWitness` / `lisWitness` — **the executable witness**
      (milestone 3): computable `List.argmax` predecessor selection plus
      `Fin.snoc` backtracking produces an actual `IncreasingSubseq f (incDP f i)`
      (and a global one of length `lisLength f`) with no `Classical.choice` in
      the data — `#eval` prints the actual indices. `incWitness_positions_last`
      certifies the computed subsequence genuinely ends at `i`.
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

  ## Milestone status (tracked in research/problems/erdos-szekeres-oq-02/)

  All three milestones are now complete: (1) computable DP + exact cost,
  (2) full correctness — in the corrected prefix-supremum form
  `maxIncLen_eq_sup_Iic`, with the naive pointwise form refuted, plus the exact
  characterization `exactIncEnd_iff_le_incDP` — and (3) the executable witness
  `incWitness`/`lisWitness`. Out of Lean scope by design: Θ(n log n) patience
  sorting and Fredman's Ω(n log n) lower bound (no comparison-cost model in
  Mathlib; documented above as the literature answer).

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

/- ## Optimal substructure: the DP value is the exact maximum

The stripping argument: any exact chain ending at `i` of length `m + 1` hands
its first `m` entries to the second-to-last position `j₀` (which is an
admissible predecessor of `i`), so by induction `m ≤ incDP f j₀ ≤ sup`, hence
`m + 1 ≤ incDP f i`. Together with `exactIncEnd_incDP` (the DP value is
realized) this characterizes `incDP f i` exactly: `ExactIncEnd f i len` holds
iff `len ≤ incDP f i` (`exactIncEnd_iff_le_incDP`).
-/

/-- **Stripping / optimal substructure**: every exact chain ending at `i` has
    length at most `incDP f i`. Induction on the length; the inductive step
    strips the last element and recurses at the second-to-last position. -/
theorem ExactIncEnd.le_incDP {f : Sequence α n} {i : Fin n} {len : ℕ}
    (h : ExactIncEnd f i len) : len ≤ incDP f i := by
  induction len generalizing i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    obtain ⟨k, hmono, hvals, hle, hlast⟩ := h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact one_le_incDP f i
    · have hmlt : m < m + 1 := Nat.lt_succ_self m
      have hprevlt : m - 1 < m + 1 := by omega
      have hklast : k ⟨m, hmlt⟩ = i := hlast ⟨m, hmlt⟩ rfl
      have hprev : (⟨m - 1, hprevlt⟩ : Fin (m + 1)) < ⟨m, hmlt⟩ := by
        rw [Fin.lt_def]
        show m - 1 < m
        omega
      have hj₀i : k ⟨m - 1, hprevlt⟩ < i := by
        have := hmono hprev
        rwa [hklast] at this
      have hfj₀ : f (k ⟨m - 1, hprevlt⟩) < f i := by
        have h2 := hvals hprev
        simp only [Function.comp_apply] at h2
        rwa [hklast] at h2
      have hchain : ExactIncEnd f (k ⟨m - 1, hprevlt⟩) m := by
        refine ⟨fun a => k a.castSucc, ?_, ?_, ?_, ?_⟩
        · intro a b hab
          exact hmono (Fin.castSucc_lt_castSucc_iff.mpr hab)
        · intro a b hab
          exact hvals (Fin.castSucc_lt_castSucc_iff.mpr hab)
        · intro a
          apply hmono.monotone
          rw [Fin.le_def]
          show a.val ≤ m - 1
          have := a.isLt
          omega
        · intro a ha
          show k a.castSucc = k ⟨m - 1, hprevlt⟩
          exact congrArg k (Fin.ext ha)
      have hrec : m ≤ incDP f (k ⟨m - 1, hprevlt⟩) := ih hchain
      have hmem : k ⟨m - 1, hprevlt⟩ ∈ preds f i := mem_preds.mpr ⟨hj₀i, hfj₀⟩
      have hsup : incDP f (k ⟨m - 1, hprevlt⟩) ≤ (preds f i).sup (fun j => incDP f j) :=
        Finset.le_sup hmem
      rw [incDP_eq]
      omega

/-- Exact chains truncate: a length-`L` exact chain restricts to its last `len`
    entries, for any `len ≤ L` (the empty chain covers `len = 0`). -/
theorem ExactIncEnd.of_le {f : Sequence α n} {i : Fin n} {L len : ℕ}
    (h : ExactIncEnd f i L) (hlen : len ≤ L) : ExactIncEnd f i len := by
  rcases Nat.eq_zero_or_pos len with rfl | hpos
  · exact ⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  · obtain ⟨k, hmono, hvals, hle, hlast⟩ := h
    refine ⟨fun a => k ⟨L - len + a.val, by omega⟩, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have hidx : (⟨L - len + a.val, by omega⟩ : Fin L) < ⟨L - len + b.val, by omega⟩ := by
        rw [Fin.mk_lt_mk]
        have := Fin.lt_def.mp hab
        omega
      exact hmono hidx
    · intro a b hab
      have hidx : (⟨L - len + a.val, by omega⟩ : Fin L) < ⟨L - len + b.val, by omega⟩ := by
        rw [Fin.mk_lt_mk]
        have := Fin.lt_def.mp hab
        omega
      exact hvals hidx
    · intro a
      exact hle _
    · intro a ha
      exact hlast ⟨L - len + a.val, by omega⟩ (show L - len + a.val = L - 1 by omega)

/-- **Exact characterization of the DP value**: a chain ending exactly at `i`
    of length `len` exists iff `len ≤ incDP f i`. So `incDP f i` is precisely
    the maximum length of an increasing subsequence ending exactly at `i` —
    full correctness of the DP against the exact-ending specification. -/
theorem exactIncEnd_iff_le_incDP {f : Sequence α n} {i : Fin n} {len : ℕ} :
    ExactIncEnd f i len ↔ len ≤ incDP f i :=
  ⟨ExactIncEnd.le_incDP, fun h => (exactIncEnd_incDP f i).of_le h⟩

/- ## The bridge to the parent's noncomputable spec

The naive completion of correctness would be `incDP f i = maxIncLen f i`. **That
statement is false**, and the discrepancy is a genuine finding about the parent
file: `HasIncreasingEndingAt f i len` requires each chain position to satisfy
`k j < i ∨ (j.val = len - 1 ∧ k j = i)` — the second disjunct is *available* to
the last element but not *forced*, so chains lying entirely strictly below `i`
qualify. `maxIncLen f i` therefore measures the longest increasing chain among
positions `≤ i` where only the last element may touch `i` — NOT the longest
chain genuinely ending at `i` that its docstring describes and that `incDP`
computes. Witness `f = [1, 2, 0]` at `i = 2`: the chain at positions `(0, 1)`
(values `1 < 2`) makes `maxIncLen f 2 = 2`, while `incDP f 2 = 1` (no value
below `f 2 = 0` exists). Formalized in `incDP_lt_maxIncLen_counterexample`.

The honest correct statement is the prefix-supremum bridge
`maxIncLen f i = (Iic i).sup (incDP f)` (`maxIncLen_eq_sup_Iic`): the parent's
measure is the running maximum of the DP table. Both directions are proved, so
this — together with `exactIncEnd_iff_le_incDP` — is the full correctness of
the DP against the parent's actual (weak) specification.
-/

/-- Each DP value at a position `j ≤ i` is a valid length for the parent's
    (weak) ending-at predicate at `i`, hence bounded by `maxIncLen f i`. -/
theorem incDP_le_maxIncLen_of_le {f : Sequence α n} {j i : Fin n} (hji : j ≤ i) :
    incDP f j ≤ maxIncLen f i := by
  classical
  obtain ⟨k, hmono, hvals, hle, hlast⟩ := exactIncEnd_incDP f j
  have hP : HasIncreasingEndingAt f i (incDP f j) := by
    refine ⟨k, hmono, ?_, hvals⟩
    intro a
    rcases lt_or_eq_of_le hji with hlt | rfl
    · exact Or.inl (lt_of_le_of_lt (hle a) hlt)
    · by_cases ha : a.val = incDP f j - 1
      · exact Or.inr ⟨ha, hlast a ha⟩
      · have hpos : 1 ≤ incDP f j := one_le_incDP f j
        have h1 : incDP f j - 1 < incDP f j := by omega
        have hlt2 : a < (⟨incDP f j - 1, h1⟩ : Fin (incDP f j)) := by
          rw [Fin.lt_def]
          show a.val < incDP f j - 1
          have := a.isLt
          omega
        have hka := hmono hlt2
        rw [hlast ⟨incDP f j - 1, h1⟩ rfl] at hka
        exact Or.inl hka
  have hwin : incDP f j ≤ i.val + 1 := by
    have h1 := incDP_le_index_succ f j
    have h2 : j.val ≤ i.val := hji
    omega
  show incDP f j ≤ Nat.findGreatest (HasIncreasingEndingAt f i) (i.val + 1)
  exact Nat.le_findGreatest hwin hP

/-- Conversely, any length admitted by the parent's predicate is realized as an
    exact chain ending at *some* position `≤ i`, hence bounded by the prefix
    supremum of the DP table. -/
theorem maxIncLen_le_sup_Iic (f : Sequence α n) (i : Fin n) :
    maxIncLen f i ≤ (Finset.Iic i).sup (fun j => incDP f j) := by
  classical
  have hP : HasIncreasingEndingAt f i (maxIncLen f i) := by
    show HasIncreasingEndingAt f i (Nat.findGreatest (HasIncreasingEndingAt f i) (i.val + 1))
    exact Nat.findGreatest_spec (by omega) (hasIncreasingEndingAt_one f i)
  have hL1 : 1 ≤ maxIncLen f i := one_le_maxIncLen f i
  obtain ⟨k, hmono, hdisj, hvals⟩ := hP
  have h1 : maxIncLen f i - 1 < maxIncLen f i := by omega
  have hjle : k ⟨maxIncLen f i - 1, h1⟩ ≤ i := by
    rcases hdisj ⟨maxIncLen f i - 1, h1⟩ with h | h
    · exact h.le
    · exact h.2.le
  have hexact : ExactIncEnd f (k ⟨maxIncLen f i - 1, h1⟩) (maxIncLen f i) := by
    refine ⟨k, hmono, hvals, ?_, ?_⟩
    · intro a
      apply hmono.monotone
      rw [Fin.le_def]
      show a.val ≤ maxIncLen f i - 1
      have := a.isLt
      omega
    · intro a ha
      exact congrArg k (Fin.ext ha)
  calc maxIncLen f i ≤ incDP f (k ⟨maxIncLen f i - 1, h1⟩) := hexact.le_incDP
    _ ≤ (Finset.Iic i).sup (fun j => incDP f j) := Finset.le_sup (Finset.mem_Iic.mpr hjle)

/-- **The corrected full-correctness statement**: the parent's noncomputable
    `maxIncLen` is exactly the running (prefix) maximum of the computable DP
    table. This is the true relationship — pointwise equality
    `incDP f i = maxIncLen f i` is refuted by
    `incDP_lt_maxIncLen_counterexample` below. -/
theorem maxIncLen_eq_sup_Iic (f : Sequence α n) (i : Fin n) :
    maxIncLen f i = (Finset.Iic i).sup (fun j => incDP f j) :=
  le_antisymm (maxIncLen_le_sup_Iic f i)
    (Finset.sup_le fun _j hj => incDP_le_maxIncLen_of_le (Finset.mem_Iic.mp hj))

/-- The DP table of `[1, 2, 0]` is `[1, 2, 1]`. -/
theorem incDP_counterexample_table :
    incDP (![1, 2, 0] : Sequence ℕ 3) 0 = 1 ∧
    incDP (![1, 2, 0] : Sequence ℕ 3) 1 = 2 ∧
    incDP (![1, 2, 0] : Sequence ℕ 3) 2 = 1 := by
  have h0 : incDP (![1, 2, 0] : Sequence ℕ 3) 0 = 1 := by
    rw [incDP_eq, show preds (![1, 2, 0] : Sequence ℕ 3) 0 = ∅ from by decide]
    simp
  have h1 : incDP (![1, 2, 0] : Sequence ℕ 3) 1 = 2 := by
    rw [incDP_eq, show preds (![1, 2, 0] : Sequence ℕ 3) 1 = {0} from by decide]
    simp [h0]
  have h2 : incDP (![1, 2, 0] : Sequence ℕ 3) 2 = 1 := by
    rw [incDP_eq, show preds (![1, 2, 0] : Sequence ℕ 3) 2 = ∅ from by decide]
    simp
  exact ⟨h0, h1, h2⟩

/-- **The naive correctness statement `incDP = maxIncLen` is FALSE.** On
    `f = [1, 2, 0]` at `i = 2`, the parent's weak ending-at disjunction admits
    the chain `1 < 2` at positions `(0, 1)` lying entirely below `i`, so
    `maxIncLen f 2 = 2` while no increasing chain genuinely ends at `i = 2`
    beyond the singleton: `incDP f 2 = 1`. -/
theorem incDP_lt_maxIncLen_counterexample :
    incDP (![1, 2, 0] : Sequence ℕ 3) 2 < maxIncLen (![1, 2, 0] : Sequence ℕ 3) 2 := by
  obtain ⟨h0, h1, h2⟩ := incDP_counterexample_table
  have hsup : maxIncLen (![1, 2, 0] : Sequence ℕ 3) 2 = 2 := by
    rw [maxIncLen_eq_sup_Iic, show Finset.Iic (2 : Fin 3) = {0, 1, 2} from by decide]
    simp only [Finset.sup_insert, Finset.sup_singleton, h0, h1, h2]
    decide
  rw [h2, hsup]
  omega

/- ## The global LIS length

`lisLength f = sup_i (incDP f i)` is the computable global
longest-increasing-subsequence length; by the bridge it agrees with the
supremum of the parent's noncomputable per-position measure.
-/

/-- The computable global longest-increasing-subsequence length. -/
def lisLength (f : Sequence α n) : ℕ := Finset.univ.sup (fun i => incDP f i)

/-- The computable global length agrees with the supremum of the parent's
    noncomputable per-position measure. -/
theorem lisLength_eq_sup_maxIncLen (f : Sequence α n) :
    lisLength f = Finset.univ.sup (fun i => maxIncLen f i) := by
  unfold lisLength
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    exact le_trans (incDP_le_maxIncLen f i) (Finset.le_sup (Finset.mem_univ i))
  · refine Finset.sup_le fun i _ => ?_
    rw [maxIncLen_eq_sup_Iic]
    exact Finset.sup_le fun j _ => Finset.le_sup (Finset.mem_univ j)

/- ## The executable witness (milestone 3)

`incChain` backtracks computable `List.argmax` predecessor pointers to build
the actual index map — the literal content of "finding the actual monotonic
subsequence". No `Classical.choice` enters the data: the only choices made are
`List.argmax` over decidable comparisons, so `#eval` runs the whole pipeline
and prints the indices (see the smoke tests at the end of the file).
-/

/-- Executable chain data: the `Type`-level (data-carrying) counterpart of
    `ExactIncEnd` — positions of a strictly increasing subsequence with
    strictly increasing values, bounded by `i` and ending exactly at `i`. -/
structure IncChain (f : Sequence α n) (i : Fin n) (len : ℕ) where
  /-- The positions forming the chain. -/
  positions : Fin len → Fin n
  /-- Positions strictly increase. -/
  strictMono_positions : StrictMono positions
  /-- Values strictly increase. -/
  strictMono_values : StrictMono (f ∘ positions)
  /-- All positions are bounded by the endpoint. -/
  le_endpoint : ∀ a, positions a ≤ i
  /-- The last position is exactly the endpoint. -/
  last_eq : ∀ a : Fin len, a.val = len - 1 → positions a = i

/-- Chain data yields the `Prop`-level invariant. -/
theorem IncChain.exactIncEnd {f : Sequence α n} {i : Fin n} {len : ℕ}
    (c : IncChain f i len) : ExactIncEnd f i len :=
  ⟨c.positions, c.strictMono_positions, c.strictMono_values, c.le_endpoint, c.last_eq⟩

/-- The singleton chain at `i`. -/
def IncChain.single (f : Sequence α n) (i : Fin n) : IncChain f i 1 where
  positions := fun _ => i
  strictMono_positions := by
    intro a b hab
    exact absurd hab (Subsingleton.elim a b ▸ lt_irrefl _)
  strictMono_values := by
    intro a b hab
    exact absurd hab (Subsingleton.elim a b ▸ lt_irrefl _)
  le_endpoint := fun _ => le_refl i
  last_eq := fun _ _ => rfl

/-- Transport chain data along a length equality. -/
def IncChain.cast {f : Sequence α n} {i : Fin n} {len len' : ℕ} (h : len = len')
    (c : IncChain f i len) : IncChain f i len' := h ▸ c

/-- One-step extension of chain data by a later, larger position (the
    data-level twin of `ExactIncEnd.extend`, same `Fin.snoc` mechanism). -/
def IncChain.extend {f : Sequence α n} {j i : Fin n} {len : ℕ}
    (c : IncChain f j len) (hlen : 1 ≤ len) (hji : j < i) (hfji : f j < f i) :
    IncChain f i (len + 1) :=
  have hki : ∀ a : Fin len, c.positions a < i := fun a =>
    lt_of_le_of_lt (c.le_endpoint a) hji
  have hfki : ∀ a : Fin len, f (c.positions a) < f i := by
    intro a
    by_cases ha : a.val = len - 1
    · rw [c.last_eq a ha]
      exact hfji
    · have h1 : len - 1 < len := by omega
      have hlt : a < (⟨len - 1, h1⟩ : Fin len) := by
        rw [Fin.lt_def]
        show a.val < len - 1
        have := a.isLt
        omega
      have h2 := c.strictMono_values hlt
      simp only [Function.comp_apply] at h2
      rw [c.last_eq ⟨len - 1, h1⟩ rfl] at h2
      exact lt_trans h2 hfji
  { positions := Fin.snoc c.positions i
    strictMono_positions := by
      intro a b hab
      rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]
          exact c.strictMono_positions (Fin.castSucc_lt_castSucc_iff.mp hab)
        · exact absurd hab (not_lt.mpr (Fin.castSucc_lt_last b').le)
      · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc, Fin.snoc_last]
          exact hki a'
        · exact absurd hab (lt_irrefl _)
    strictMono_values := by
      rw [Fin.comp_snoc]
      intro a b hab
      rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]
          exact c.strictMono_values (Fin.castSucc_lt_castSucc_iff.mp hab)
        · exact absurd hab (not_lt.mpr (Fin.castSucc_lt_last b').le)
      · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc, Fin.snoc_last]
          exact hfki a'
        · exact absurd hab (lt_irrefl _)
    le_endpoint := by
      intro a
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact (hki a').le
      · rw [Fin.snoc_last]
    last_eq := by
      intro a ha
      have haeq : a = Fin.last len := by
        apply Fin.ext
        simpa using ha
      rw [haeq, Fin.snoc_last] }

/-- Computable predecessor selection: an admissible predecessor maximizing the
    DP value, chosen via `List.argmax` over the (computably) sorted predecessor
    list (`Finset.toList` is noncomputable, `Finset.sort` is not; no
    `Classical.choice`). -/
def incArgmax (f : Sequence α n) (i : Fin n) : Option (Fin n) :=
  ((preds f i).sort (· ≤ ·)).argmax (fun j => incDP f j)

theorem incArgmax_eq_none {f : Sequence α n} {i : Fin n}
    (h : incArgmax f i = none) : preds f i = ∅ := by
  have hnil : (preds f i).sort (· ≤ ·) = [] := List.argmax_eq_none.mp h
  have hlen := Finset.length_sort (s := preds f i) (r := (· ≤ ·))
  rw [hnil] at hlen
  exact Finset.card_eq_zero.mp hlen.symm

theorem incArgmax_mem {f : Sequence α n} {i : Fin n} {j₀ : Fin n}
    (h : incArgmax f i = some j₀) : j₀ ∈ preds f i :=
  ((preds f i).mem_sort (· ≤ ·)).mp (List.argmax_mem (Option.mem_def.mpr h))

/-- With no admissible predecessor the DP value is `1`. -/
theorem incDP_eq_one_of_incArgmax_none {f : Sequence α n} {i : Fin n}
    (h : incArgmax f i = none) : incDP f i = 1 := by
  rw [incDP_eq, incArgmax_eq_none h]
  simp

/-- The argmax predecessor attains the DP recurrence:
    `incDP f i = incDP f j₀ + 1`. -/
theorem incDP_eq_of_incArgmax_some {f : Sequence α n} {i : Fin n} {j₀ : Fin n}
    (h : incArgmax f i = some j₀) : incDP f i = incDP f j₀ + 1 := by
  have hmem : j₀ ∈ preds f i := incArgmax_mem h
  have hmax : ∀ j ∈ preds f i, incDP f j ≤ incDP f j₀ := fun j hj =>
    List.le_of_mem_argmax (((preds f i).mem_sort (· ≤ ·)).mpr hj) (Option.mem_def.mpr h)
  have hsup : (preds f i).sup (fun j => incDP f j) = incDP f j₀ :=
    le_antisymm (Finset.sup_le hmax) (Finset.le_sup hmem)
  rw [incDP_eq, hsup, Nat.add_comm]

/-- **The executable witness chain**: backtracks `incArgmax` predecessor
    pointers, building the position map by `Fin.snoc`. Computable — this is
    the O(n) reconstruction on top of the DP table. -/
def incChain (f : Sequence α n) (i : Fin n) : IncChain f i (incDP f i) :=
  match h : incArgmax f i with
  | none => (IncChain.single f i).cast (incDP_eq_one_of_incArgmax_none h).symm
  | some j₀ =>
    have hj := mem_preds.mp (incArgmax_mem h)
    ((incChain f j₀).extend (one_le_incDP f j₀) hj.1 hj.2).cast
      (incDP_eq_of_incArgmax_some h).symm
termination_by i.val
decreasing_by exact hj.1

/-- **Milestone 3 — the actual subsequence as a program**: an executable
    `IncreasingSubseq` of the DP length at every position. Where
    `exists_increasingSubseq_incDP` asserts existence, this *returns the
    indices* (see the `#eval` smoke tests). -/
def incWitness (f : Sequence α n) (i : Fin n) : IncreasingSubseq f (incDP f i) :=
  ⟨(incChain f i).positions, (incChain f i).strictMono_positions,
    (incChain f i).strictMono_values⟩

/-- The computed witness genuinely ends at `i`. -/
theorem incWitness_positions_last (f : Sequence α n) (i : Fin n)
    (a : Fin (incDP f i)) (ha : a.val = incDP f i - 1) :
    (incWitness f i).positions a = i :=
  (incChain f i).last_eq a ha

/-- Computable global argmax position of the DP table (`List.finRange` is the
    computable enumeration of `Fin n`). -/
def lisArgmax (f : Sequence α n) : Option (Fin n) :=
  (List.finRange n).argmax (fun i => incDP f i)

/-- **The global executable witness**: an actual longest increasing
    subsequence of the whole sequence, of the computable global length
    `lisLength f`. -/
def lisWitness (f : Sequence α n) : IncreasingSubseq f (lisLength f) :=
  match h : lisArgmax f with
  | none =>
    have hempty : IsEmpty (Fin n) := ⟨fun a => by
      have ha : a ∈ List.finRange n := List.mem_finRange a
      rw [List.argmax_eq_none.mp h] at ha
      simp at ha⟩
    have hlen : lisLength f = 0 := by
      haveI := hempty
      rw [lisLength, Finset.univ_eq_empty, Finset.sup_empty]
      rfl
    hlen.symm ▸
      (⟨Fin.elim0, fun a => a.elim0, fun a => a.elim0⟩ : IncreasingSubseq f 0)
  | some i₀ =>
    have hmax : ∀ j ∈ Finset.univ, incDP f j ≤ incDP f i₀ := fun j _ =>
      List.le_of_mem_argmax (List.mem_finRange j) (Option.mem_def.mpr h)
    have hlen : lisLength f = incDP f i₀ :=
      le_antisymm (Finset.sup_le hmax) (Finset.le_sup (Finset.mem_univ i₀))
    hlen.symm ▸ incWitness f i₀

/-- An `IncreasingSubseq` of the global LIS length always exists (now a
    one-liner: the executable witness inhabits it). -/
theorem exists_increasingSubseq_lisLength (f : Sequence α n) :
    Nonempty (IncreasingSubseq f (lisLength f)) :=
  ⟨lisWitness f⟩

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
ends at position 7), and `incDPcost 8 = 28 = 8·7/2`. The witness pipeline
`incWitness`/`lisWitness` prints the *actual indices* of a longest increasing
subsequence — the literal answer to "finding the actual monotonic
subsequence".
-/

#eval incDP (![3, 1, 4, 1, 5, 9, 2, 6] : Fin 8 → ℕ) 7
#eval (List.ofFn fun i : Fin 8 => incDP (![3, 1, 4, 1, 5, 9, 2, 6] : Fin 8 → ℕ) i)
#eval incDPcost 8
#eval List.ofFn (incWitness (![3, 1, 4, 1, 5, 9, 2, 6] : Fin 8 → ℕ) 7).positions
#eval lisLength (![3, 1, 4, 1, 5, 9, 2, 6] : Fin 8 → ℕ)
#eval List.ofFn (lisWitness (![3, 1, 4, 1, 5, 9, 2, 6] : Fin 8 → ℕ)).positions

end ErdosSzekeresOQ02
