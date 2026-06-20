/-
# Erdős Problem #340 (oq-01): The cubic growth bound for the greedy Sidon sequence

The parent file `Erdos340GreedySidon.lean` **constructs** the greedy (Mian–Chowla)
Sidon sequence `aₙ` as an explicit `Nat.find` recursion and discharges the three former
existence axioms.  What remained only as a *comment-level proof sketch* there was the
**N^(1/3) lower bound** — the quantitative heart of Erdős #340's known direction.

This file formalizes the crux of that sketch: the **global covering argument** giving the
cubic upper bound on the sequence values,

  `aₙ ≤ (n+1) + (n+1)³`            (`greedySidonSeq_le_cubic`)

which is exactly the bound whose cube-root inversion yields `|A ∩ [1,N]| = Ω(N^(1/3))`.

## The argument

For a Sidon set `A` and a value `m` strictly above every element of `A`, inserting `m`
breaks the Sidon property **iff** `m = c + d - a` for some `a, c, d ∈ A` (the only
surviving collision once `m` exceeds `max A`).  Collect these *forbidden* values into
`forbidden A`; there are at most `|A|³` of them.

The greedy step picks the **least** valid `m`, so every integer `p` skipped between two
consecutive greedy terms is forbidden against the prefix placed so far — and `forbidden`
is monotone, so `p` is forbidden against the full set `Aₙ`.  Hence every `p ∈ [1, aₙ]` is
either an element of `Aₙ` or forbidden against `Aₙ`:

  `aₙ = |[1, aₙ]| ≤ |Aₙ| + |forbidden Aₙ| ≤ (n+1) + (n+1)³`.

The crux necessary lemma (`not_sidon_insert_forbidden`) is the contrapositive of the
parent's `sidon_insert_of_large`, which already carries the hard 6-way collision case
analysis — so here it is a one-line `by_contra`.

NOTE on the `1/3`-vs-`1/2` gap: the cubic bound is the *known* result.  Improving the
exponent past `1/3` for the greedy sequence is the OPEN part of Erdős #340 and is **not**
attempted here.
-/
import Proofs.Erdos340GreedySidon

namespace Erdos340

open Finset

/- ## Forbidden values -/

/-- The **forbidden set** of `A`: all values `c + d - a` with `a, c, d ∈ A`.  When `m`
exceeds every element of `A`, `insert m A` stays Sidon unless `m` lands in `forbidden A`
(see `not_sidon_insert_forbidden`). -/
def forbidden (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A ×ˢ A).image (fun p => p.2.1 + p.2.2 - p.1)

/-- There are at most `|A|³` forbidden values: each is the image of a triple `(a, c, d)`. -/
theorem forbidden_card_le (A : Finset ℕ) : (forbidden A).card ≤ A.card ^ 3 := by
  calc (forbidden A).card ≤ (A ×ˢ A ×ˢ A).card := Finset.card_image_le
    _ = A.card ^ 3 := by rw [Finset.card_product, Finset.card_product]; ring

/-- `forbidden` is monotone: a larger ground set forbids at least as much. -/
theorem forbidden_mono {A B : Finset ℕ} (h : A ⊆ B) : forbidden A ⊆ forbidden B := by
  apply Finset.image_subset_image
  exact Finset.product_subset_product h (Finset.product_subset_product h h)

/-- **Necessary direction** (crux).  If `m` is above every element of the Sidon set `A`
and `insert m A` is *not* Sidon, then `m` is a forbidden value `c + d - a`.

This is the contrapositive of `sidon_insert_of_large`, which already contains the hard
case analysis. -/
theorem not_sidon_insert_forbidden {A : Finset ℕ} (hA : IsSidon A) {m : ℕ}
    (hm : ∀ a ∈ A, a < m) (hbad : ¬ IsSidon (insert m A)) :
    m ∈ forbidden A := by
  by_contra hmem
  apply hbad
  apply sidon_insert_of_large hA hm
  intro a ha c hc d hd heq
  -- heq : m + a = c + d ;  goal : False  (m + a ≠ c + d)
  apply hmem
  rw [forbidden, Finset.mem_image]
  refine ⟨(a, c, d), ?_, ?_⟩
  · simp only [Finset.mem_product]
    exact ⟨ha, hc, hd⟩
  · show c + d - a = m
    omega

/- ## Greedy-sequence bookkeeping -/

/-- Every greedy term lies in its own prefix set. -/
theorem greedySidonSeq_mem (n : ℕ) : greedySidonSeq n ∈ greedySeqSet n := by
  rw [greedySeqSet_eq_image]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- `aₙ` is the largest element of the prefix `Aₙ` (the sequence is strictly increasing). -/
theorem greedySeqSet_le {n x : ℕ} (hx : x ∈ greedySeqSet n) : x ≤ greedySidonSeq n := by
  rw [greedySeqSet_eq_image, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_range] at hk
  exact greedySidonSeq_strictMono.monotone (by omega)

/-- The prefix set has exactly `n + 1` elements (strict monotonicity ⇒ injectivity). -/
theorem greedySeqSet_card (n : ℕ) : (greedySeqSet n).card = n + 1 := by
  rw [greedySeqSet_eq_image,
      Finset.card_image_of_injective _ greedySidonSeq_strictMono.injective,
      Finset.card_range]

/-- Prefixes grow by insertion. -/
theorem greedySeqSet_subset_succ (n : ℕ) : greedySeqSet n ⊆ greedySeqSet (n + 1) := by
  have h : greedySeqSet (n + 1)
      = insert (greedySidonSeq (n + 1)) (greedySeqSet n) := rfl
  rw [h]
  exact Finset.subset_insert _ _

/-- **Greedy minimality.**  Any value strictly between consecutive greedy terms was
*skipped*: inserting it into the prefix would have broken the Sidon property. -/
theorem greedy_skip_not_sidon {n p : ℕ}
    (h1 : greedySidonSeq n < p) (h2 : p < greedySidonSeq (n + 1)) :
    ¬ IsSidon (insert p (greedySeqSet n)) := by
  classical
  have hSidon : IsSidon (greedySeqSet n) := greedySeqSet_isSidon n
  have hex : ∃ m, greedySidonSeq n < m ∧ IsSidon (insert m (greedySeqSet n)) := by
    obtain ⟨m, hbm, _, hm⟩ := sidon_exists_extension (greedySeqSet n) hSidon (greedySidonSeq n)
    exact ⟨m, hbm, hm⟩
  have hnext : greedySidonSeq (n + 1) = nextSidon (greedySeqSet n) (greedySidonSeq n) := rfl
  have hval : nextSidon (greedySeqSet n) (greedySidonSeq n) = Nat.find hex := by
    unfold nextSidon; exact dif_pos hex
  rw [hnext, hval] at h2
  have hmin := Nat.find_min hex h2
  push_neg at hmin
  exact hmin h1

/- ## The covering bound -/

/-- **Global covering.**  Every integer `p ∈ [1, aₙ]` is either a greedy element or a
forbidden value against the *full* prefix `Aₙ`. -/
theorem greedy_covering (n : ℕ) :
    ∀ p, 1 ≤ p → p ≤ greedySidonSeq n →
      p ∈ greedySeqSet n ∨ p ∈ forbidden (greedySeqSet n) := by
  induction n with
  | zero =>
    intro p hp1 hp2
    have h0 : greedySidonSeq 0 = 1 := rfl
    rw [h0] at hp2
    have hp : p = 1 := by omega
    left
    have hset : greedySeqSet 0 = {1} := rfl
    rw [hp, hset]
    exact Finset.mem_singleton_self 1
  | succ n ih =>
    intro p hp1 hp2
    by_cases hle : p ≤ greedySidonSeq n
    · rcases ih p hp1 hle with hin | hforb
      · exact Or.inl (greedySeqSet_subset_succ n hin)
      · exact Or.inr (forbidden_mono (greedySeqSet_subset_succ n) hforb)
    · push_neg at hle
      by_cases hpeq : p = greedySidonSeq (n + 1)
      · left
        rw [hpeq]
        exact greedySidonSeq_mem (n + 1)
      · have hlt : p < greedySidonSeq (n + 1) := lt_of_le_of_ne hp2 hpeq
        have hnotsidon := greedy_skip_not_sidon hle hlt
        right
        have hmem : p ∈ forbidden (greedySeqSet n) := by
          apply not_sidon_insert_forbidden (greedySeqSet_isSidon n) ?_ hnotsidon
          intro a ha
          exact lt_of_le_of_lt (greedySeqSet_le ha) hle
        exact forbidden_mono (greedySeqSet_subset_succ n) hmem

/-- **Cubic growth bound.**  The `n`-th greedy Sidon term satisfies `aₙ ≤ (n+1) + (n+1)³`.

This is the quantitative crux of the known `N^(1/3)` lower bound for Erdős #340: the
greedy sequence cannot grow faster than cubically, because every value it skips is one of
at most `|Aₙ|³ = (n+1)³` forbidden differences against the placed prefix. -/
theorem greedySidonSeq_le_cubic (n : ℕ) :
    greedySidonSeq n ≤ (n + 1) + (n + 1) ^ 3 := by
  have hcover : Finset.Icc 1 (greedySidonSeq n)
      ⊆ greedySeqSet n ∪ forbidden (greedySeqSet n) := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    rw [Finset.mem_union]
    exact greedy_covering n p hp.1 hp.2
  have hcard := Finset.card_le_card hcover
  rw [Nat.card_Icc] at hcard
  have hunion : (greedySeqSet n ∪ forbidden (greedySeqSet n)).card
      ≤ (greedySeqSet n).card + (forbidden (greedySeqSet n)).card :=
    Finset.card_union_le _ _
  have hsetcard : (greedySeqSet n).card = n + 1 := greedySeqSet_card n
  have hforbcard : (forbidden (greedySeqSet n)).card ≤ (n + 1) ^ 3 := by
    calc (forbidden (greedySeqSet n)).card ≤ (greedySeqSet n).card ^ 3 := forbidden_card_le _
      _ = (n + 1) ^ 3 := by rw [hsetcard]
  omega

/- ## Cube-root inversion: the discrete `Ω(N^(1/3))` count -/

/-- Every greedy term is positive (`a₀ = 1` is the minimum). -/
theorem one_le_greedySidonSeq (k : ℕ) : 1 ≤ greedySidonSeq k := by
  have hmono : greedySidonSeq 0 ≤ greedySidonSeq k :=
    greedySidonSeq_strictMono.monotone (Nat.zero_le k)
  have h0 : greedySidonSeq 0 = 1 := rfl
  omega

/-- Cleaner cubic bound: `aₙ ≤ 2(n+1)³`, absorbing the linear term. -/
theorem greedySidonSeq_le_two_mul_cubic (n : ℕ) :
    greedySidonSeq n ≤ 2 * (n + 1) ^ 3 := by
  have h := greedySidonSeq_le_cubic n
  have hle : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) (n + 1)
  omega

/-- The first `n+1` greedy terms all lie inside the window `[1, 2(n+1)³]`. -/
theorem greedySeqSet_subset_Icc (n : ℕ) :
    greedySeqSet n ⊆ Finset.Icc 1 (2 * (n + 1) ^ 3) := by
  intro x hx
  rw [Finset.mem_Icc]
  refine ⟨?_, le_trans (greedySeqSet_le hx) (greedySidonSeq_le_two_mul_cubic n)⟩
  rw [greedySeqSet_eq_image, Finset.mem_image] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact one_le_greedySidonSeq k

/-- **Discrete `Ω(N^(1/3))` lower bound for the greedy Sidon counting function.**

Whenever `N ≥ 2(n+1)³`, at least `n+1` of the integers in `[1, N]` are greedy Sidon
terms.  Reading it the other way: the count `A(N)` of greedy terms `≤ N` satisfies
`A(N) ≥ k` as soon as `N ≥ 2k³`, i.e. `A(N) ≥ ⌊(N/2)^{1/3}⌋ = Ω(N^{1/3})`.

This is the known lower-bound direction of Erdős #340, now an elementary, fully verified
counting statement (no `rpow`, no axiom).  The `1/3`→`1/2` exponent improvement remains
the OPEN conjecture and is not addressed here. -/
theorem greedy_count_ge {n N : ℕ} (hN : 2 * (n + 1) ^ 3 ≤ N) :
    n + 1 ≤ ((Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet n)).card := by
  have hsub : greedySeqSet n
      ⊆ (Finset.Icc 1 N).filter (fun x => x ∈ greedySeqSet n) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨?_, hx⟩
    have hwin := greedySeqSet_subset_Icc n hx
    rw [Finset.mem_Icc] at hwin ⊢
    omega
  calc n + 1 = (greedySeqSet n).card := (greedySeqSet_card n).symm
    _ ≤ _ := Finset.card_le_card hsub

end Erdos340
