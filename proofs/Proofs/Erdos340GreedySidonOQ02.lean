/-
  Erdős #340 — OQ-02: the Erdős–Turán upper bound for Sidon sets.

  Parent file `Proofs.Erdos340GreedySidon` proves the *weak* difference-counting
  bound `sidon_upper_bound_weak : |A| ≤ √(2N) + 1` for a Sidon set
  `A ⊆ {1,…,N}`, and then *postulates the sharp bound as an axiom*:

      axiom sidon_upper_bound (A) (hA : IsSidon A) (N) (hAN : ∀ a ∈ A, a ≤ N) :
        A.card ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 1

  flagged "HARD (known result, needs formalization)". This file works toward
  *removing that axiom* by formalizing the classical sliding-window / Cauchy–
  Schwarz argument of Erdős and Turán (in the form sharpened by Lindström).

  ## The argument

  Translate `A` to `B = A + ℓ` (Sidon-ness and cardinality are preserved) so that
  every element lies in `[ℓ, N+ℓ]`. For each window start `x` put

      wc x = #{ b ∈ B : x < b ≤ x + ℓ }      (count of B in the length-ℓ window).

  Two counting facts drive everything:

  * **(A) window-sum identity** `∑_{x<M} wc x = ℓ · |B|` — each element sits in
    exactly `ℓ` of the windows `x ∈ range M` (here `M = N+ℓ`).
  * **(B) window pair bound** `∑_{x<M} wc x · (wc x − 1) ≤ ℓ · (ℓ−1)` — the inner
    sum counts ordered pairs sharing a window, weighted by `ℓ − |b−b'|`; because a
    Sidon set has *distinct differences* each difference `d < ℓ` is hit at most
    once, so the total is `≤ 2·∑_{d<ℓ}(ℓ−d) = ℓ(ℓ−1)`.

  Cauchy–Schwarz (`Finset.sq_sum_le_card_mul_sum_sq`) on `wc` over `range M` then
  gives, after dividing by `ℓ`, the **key inequality**

      ℓ · |A|² ≤ (N + ℓ) · (ℓ − 1 + |A|)          (`sidon_window_key`)

  valid for every window length `ℓ ≥ 1`. Optimising `ℓ ≈ √N` yields the sharp
  `√N + √√N + 1` bound.

  ## Status of this file

  The Cauchy–Schwarz **assembly** (`sidon_window_key` from (A),(B)) and the
  translation-invariance infrastructure are proved here unconditionally. The two
  window-counting lemmas (A) and (B) are concrete finite double-counting
  identities — *known* combinatorics, not the open problem — and are isolated as
  `window_sum_identity` / `window_pair_bound` for completion (delegated to the
  Aristotle proof-search backend). Until both are closed this file is `wip`; once
  closed, `axiom sidon_upper_bound` in the parent can be discharged.
-/
import Mathlib
import Proofs.Erdos340GreedySidon

namespace Erdos340.OQ02

open Finset

/-! ## Translation invariance of Sidon sets

Shifting every element by a constant preserves the Sidon property and the
cardinality. This is exactly what lets us assume the set lives in `[ℓ, N+ℓ]`
so that every element is covered by precisely `ℓ` windows. -/

/-- The Sidon property is invariant under translation `a ↦ a + c`. -/
theorem isSidon_image_add (A : Finset ℕ) (hA : IsSidon A) (c : ℕ) :
    IsSidon (A.image (· + c)) := by
  intro a b d e ha hb hd he hab hde hsum
  simp only [Finset.mem_image] at ha hb hd he
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨d', hd', rfl⟩ := hd
  obtain ⟨e', he', rfl⟩ := he
  have hab' : a' ≤ b' := by omega
  have hde' : d' ≤ e' := by omega
  have hsum' : a' + b' = d' + e' := by omega
  obtain ⟨h1, h2⟩ := hA a' b' d' e' ha' hb' hd' he' hab' hde' hsum'
  constructor <;> omega

/-- Translation by `c` does not change the cardinality (it is injective). -/
theorem card_image_add (A : Finset ℕ) (c : ℕ) :
    (A.image (· + c)).card = A.card :=
  Finset.card_image_of_injective A (add_left_injective c)

/-! ## Window counts -/

/-- `windowCount B ℓ x` is the number of elements of `B` in the half-open length-`ℓ`
window `(x, x+ℓ]`. -/
def windowCount (B : Finset ℕ) (ℓ x : ℕ) : ℕ :=
  (B.filter (fun b => x < b ∧ b ≤ x + ℓ)).card

/-! ## The two counting lemmas (concrete finite combinatorics → Aristotle)

These are the only gaps. Both are standard double-counting identities for a fixed
finite set; neither involves the open problem. -/

/-- **(A) Window-sum identity.** If every element of `B` lies in `[ℓ, M]` then,
summing the window counts over all starts `x ∈ range M`, each element is counted
exactly `ℓ` times. -/
theorem window_sum_identity (B : Finset ℕ) (ℓ M : ℕ) (hℓ : 1 ≤ ℓ)
    (hB : ∀ b ∈ B, ℓ ≤ b ∧ b ≤ M) :
    ∑ x ∈ range M, windowCount B ℓ x = ℓ * B.card := by
  -- Expand each window count as a sum of indicators over `B`, then swap the order.
  simp only [windowCount, Finset.card_filter]
  rw [Finset.sum_comm]
  -- For each `b ∈ B`, the window starts `x` covering `b` are exactly `Ico (b-ℓ) b`,
  -- an interval of length `ℓ`.
  have hb : ∀ b ∈ B, (∑ x ∈ range M, if x < b ∧ b ≤ x + ℓ then 1 else 0) = ℓ := by
    intro b hbB
    obtain ⟨hbℓ, hbM⟩ := hB b hbB
    rw [← Finset.card_filter]
    have hset : ((range M).filter (fun x => x < b ∧ b ≤ x + ℓ)) = Finset.Ico (b - ℓ) b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hset, Nat.card_Ico]
    omega
  rw [Finset.sum_congr rfl hb, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- `card · (card − 1)` counts the ordered pairs of distinct elements, i.e. the
off-diagonal. (`Finset.offDiag_card` states this as `card·card − card`.) -/
private theorem card_offDiag_mul (s : Finset ℕ) :
    s.card * (s.card - 1) = s.offDiag.card := by
  rw [Finset.offDiag_card]
  rcases Nat.eq_zero_or_pos s.card with h | h
  · simp [h]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    rw [hk, Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]

/-- **(B) Window pair bound.** For a Sidon set `B` with elements in `[ℓ, M]`, the
total number of ordered pairs sharing a window is at most `ℓ·(ℓ−1)`, because the
pairwise differences of a Sidon set are distinct. -/
theorem window_pair_bound (B : Finset ℕ) (ℓ M : ℕ) (hℓ : 1 ≤ ℓ)
    (hBsid : IsSidon B) (hB : ∀ b ∈ B, ℓ ≤ b ∧ b ≤ M) :
    ∑ x ∈ range M, windowCount B ℓ x * (windowCount B ℓ x - 1) ≤ ℓ * (ℓ - 1) := by
  classical
  -- `cover x p` : both coordinates of the pair `p` lie in the window `(x, x+ℓ]`.
  set cover : ℕ → ℕ × ℕ → Prop :=
    fun x p => (x < p.1 ∧ p.1 ≤ x + ℓ) ∧ (x < p.2 ∧ p.2 ≤ x + ℓ) with hcover
  -- `cnt p` : number of windows covering both coordinates of `p`.
  set cnt : ℕ × ℕ → ℕ := fun p => ((range M).filter (fun x => cover x p)).card with hcnt
  -- The off-diagonal of a window equals the off-diagonal pairs of `B` covered by it.
  have hoff : ∀ x, (B.filter (fun b => x < b ∧ b ≤ x + ℓ)).offDiag
      = B.offDiag.filter (fun p => cover x p) := by
    intro x
    ext ⟨b, b'⟩
    simp only [Finset.mem_offDiag, Finset.mem_filter, hcover]
    tauto
  -- Double counting: the LHS counts triples `(x, b, b')` with `b ≠ b'` both in window `x`.
  have hmain : ∑ x ∈ range M, windowCount B ℓ x * (windowCount B ℓ x - 1)
      = ∑ p ∈ B.offDiag, cnt p := by
    have e1 : ∀ x ∈ range M, windowCount B ℓ x * (windowCount B ℓ x - 1)
        = ∑ p ∈ B.offDiag, (if cover x p then (1 : ℕ) else 0) := by
      intro x _
      simp only [windowCount]
      rw [card_offDiag_mul, hoff x, Finset.card_filter]
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [hcnt, Finset.card_filter]
  rw [hmain]
  -- A reusable "Gauss" bound: an injective positive gap with `cnt p ≤ ℓ − gap p`
  -- sums to at most `∑_{i<ℓ} i`.
  have gauss : ∀ (S : Finset (ℕ × ℕ)) (d : ℕ × ℕ → ℕ),
      (∀ p ∈ S, cnt p ≤ ℓ - d p) → (∀ p ∈ S, 1 ≤ d p) →
      Set.InjOn d (S : Set (ℕ × ℕ)) → ∑ p ∈ S, cnt p ≤ ∑ i ∈ range ℓ, i := by
    intro S d hle hd1 hinj
    calc ∑ p ∈ S, cnt p
        ≤ ∑ p ∈ S, (ℓ - d p) := Finset.sum_le_sum hle
      _ = ∑ e ∈ S.image d, (ℓ - e) := (Finset.sum_image hinj).symm
      _ ≤ ∑ i ∈ range ℓ, i := ?_
    rw [← Finset.sum_filter_add_sum_filter_not (S.image d) (fun e => e < ℓ) (fun e => ℓ - e)]
    have hzero : ∑ e ∈ (S.image d).filter (fun e => ¬ e < ℓ), (ℓ - e) = 0 := by
      refine Finset.sum_eq_zero (fun e he => ?_)
      simp only [Finset.mem_filter, not_lt] at he
      omega
    rw [hzero, add_zero]
    have hinj2 : Set.InjOn (fun e => ℓ - e)
        (((S.image d).filter (fun e => e < ℓ)) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      obtain ⟨_, halt⟩ := ha
      obtain ⟨_, hblt⟩ := hb
      simp only at hab
      omega
    have hsub : ((S.image d).filter (fun e => e < ℓ)).image (fun e => ℓ - e) ⊆ range ℓ := by
      intro j hj
      simp only [Finset.mem_image, Finset.mem_filter] at hj
      obtain ⟨e, ⟨he_img, helt⟩, rfl⟩ := hj
      obtain ⟨p, hp, rfl⟩ := he_img
      have := hd1 p hp
      simp only [Finset.mem_range]
      omega
    calc ∑ e ∈ (S.image d).filter (fun e => e < ℓ), (ℓ - e)
        = ∑ j ∈ ((S.image d).filter (fun e => e < ℓ)).image (fun e => ℓ - e), j :=
          (Finset.sum_image (f := fun j => j) hinj2).symm
      _ ≤ ∑ i ∈ range ℓ, i := Finset.sum_le_sum_of_subset hsub
  -- Split off-diagonal into the two orientations and bound each by the Gauss sum.
  rw [← Finset.sum_filter_add_sum_filter_not B.offDiag (fun p => p.1 < p.2) cnt]
  have hgauss_val : ∑ i ∈ range ℓ, i + ∑ i ∈ range ℓ, i = ℓ * (ℓ - 1) := by
    have := Finset.sum_range_id_mul_two ℓ; omega
  -- Orientation `p.1 < p.2`: gap `p.2 − p.1` is `pairDiff`, injective by the Sidon property.
  have hG : ∑ p ∈ B.offDiag.filter (fun p => p.1 < p.2), cnt p ≤ ∑ i ∈ range ℓ, i := by
    apply gauss _ (fun p => p.2 - p.1)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hp
      obtain ⟨⟨hp1, hp2, _⟩, hlt⟩ := hp
      have hℓ1 := (hB p.1 hp1).1
      have hℓ2 := (hB p.2 hp2).1
      have hsubInt : (range M).filter (fun x => cover x p) ⊆ Finset.Ico (p.2 - ℓ) p.1 := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range, hcover] at hx
        simp only [Finset.mem_Ico]; omega
      calc cnt p ≤ (Finset.Ico (p.2 - ℓ) p.1).card := by
            rw [hcnt]; exact Finset.card_le_card hsubInt
        _ = p.1 - (p.2 - ℓ) := Nat.card_Ico _ _
        _ ≤ ℓ - (p.2 - p.1) := by omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hp; omega
    · simpa only [orderedPairsLt, pairDiff] using sidon_pairDiff_injective hBsid
  -- Orientation `p.2 < p.1`: gap `p.1 − p.2`, injective by `IsSidon.diff_injective`.
  have hH : ∑ p ∈ B.offDiag.filter (fun p => ¬ p.1 < p.2), cnt p ≤ ∑ i ∈ range ℓ, i := by
    apply gauss _ (fun p => p.1 - p.2)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, not_lt] at hp
      obtain ⟨⟨hp1, hp2, hne⟩, hle⟩ := hp
      have hℓ1 := (hB p.1 hp1).1
      have hℓ2 := (hB p.2 hp2).1
      have hsubInt : (range M).filter (fun x => cover x p) ⊆ Finset.Ico (p.1 - ℓ) p.2 := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range, hcover] at hx
        simp only [Finset.mem_Ico]; omega
      calc cnt p ≤ (Finset.Ico (p.1 - ℓ) p.2).card := by
            rw [hcnt]; exact Finset.card_le_card hsubInt
        _ = p.2 - (p.1 - ℓ) := Nat.card_Ico _ _
        _ ≤ ℓ - (p.1 - p.2) := by omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, not_lt] at hp; omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_offDiag, Set.mem_setOf_eq,
        not_lt] at ha hb
      simp only at hab
      obtain ⟨⟨ha1, ha2, hane⟩, hale⟩ := ha
      obtain ⟨⟨hb1, hb2, hbne⟩, hble⟩ := hb
      have key := hBsid.diff_injective ha1 ha2 hb1 hb2 (by omega) (by omega) hab
      exact Prod.ext key.1 key.2
  calc ∑ p ∈ B.offDiag.filter (fun p => p.1 < p.2), cnt p
        + ∑ p ∈ B.offDiag.filter (fun p => ¬ p.1 < p.2), cnt p
      ≤ ∑ i ∈ range ℓ, i + ∑ i ∈ range ℓ, i := Nat.add_le_add hG hH
    _ = ℓ * (ℓ - 1) := hgauss_val

/-! ## Cauchy–Schwarz assembly (unconditional given (A),(B))

From the two counting lemmas we obtain the Erdős–Turán key inequality. This part
is fully proved. -/

/-- Elementary identity used in the assembly: `n² = n·(n−1) + n` over `ℕ`. -/
private theorem sq_eq_mul_pred_add (n : ℕ) : n ^ 2 = n * (n - 1) + n := by
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.succ_sub_one]; ring

/-- **Erdős–Turán key inequality.** For a Sidon set `A ⊆ {0,…,N}` and any window
length `ℓ ≥ 1`,
`ℓ · |A|² ≤ (N + ℓ) · (ℓ − 1 + |A|)`. Optimising `ℓ ≈ √N` gives the sharp
`√N + √√N + 1` bound (see the file header). -/
theorem sidon_window_key (A : Finset ℕ) (hA : IsSidon A) (N ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hAN : ∀ a ∈ A, a ≤ N) :
    ℓ * A.card ^ 2 ≤ (N + ℓ) * (ℓ - 1 + A.card) := by
  -- Translate `A` upward by `ℓ` so that every element lands in `[ℓ, N+ℓ]`.
  set B := A.image (· + ℓ) with hBdef
  have hBcard : B.card = A.card := card_image_add A ℓ
  have hBsid : IsSidon B := isSidon_image_add A hA ℓ
  have hBmem : ∀ b ∈ B, ℓ ≤ b ∧ b ≤ N + ℓ := by
    intro b hb
    rw [hBdef, Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨Nat.le_add_left ℓ a, by have := hAN a ha; omega⟩
  set M := N + ℓ with hM
  -- The two counting facts.
  have hsum : ∑ x ∈ range M, windowCount B ℓ x = ℓ * B.card :=
    window_sum_identity B ℓ M hℓ hBmem
  have hpair : ∑ x ∈ range M, windowCount B ℓ x * (windowCount B ℓ x - 1) ≤ ℓ * (ℓ - 1) :=
    window_pair_bound B ℓ M hℓ hBsid hBmem
  -- `∑ wc² = ∑ wc(wc-1) + ∑ wc`.
  have hsq_eq : ∑ x ∈ range M, windowCount B ℓ x ^ 2
      = (∑ x ∈ range M, windowCount B ℓ x * (windowCount B ℓ x - 1))
        + ∑ x ∈ range M, windowCount B ℓ x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => sq_eq_mul_pred_add _)
  -- Hence `∑ wc² ≤ ℓ(ℓ-1) + ℓ·k`.
  have hsq_le : ∑ x ∈ range M, windowCount B ℓ x ^ 2 ≤ ℓ * (ℓ - 1) + ℓ * B.card := by
    rw [hsq_eq, hsum]; exact Nat.add_le_add_right hpair _
  -- Cauchy–Schwarz on `wc` over `range M` (card `M`).
  have hCS : (∑ x ∈ range M, windowCount B ℓ x) ^ 2
      ≤ M * ∑ x ∈ range M, windowCount B ℓ x ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range M) (f := fun x => windowCount B ℓ x)
    rwa [Finset.card_range] at this
  -- Combine: `(ℓk)² ≤ M·(ℓ(ℓ-1)+ℓk)`.
  have hcombine : (ℓ * B.card) ^ 2 ≤ M * (ℓ * (ℓ - 1) + ℓ * B.card) := by
    calc (ℓ * B.card) ^ 2 = (∑ x ∈ range M, windowCount B ℓ x) ^ 2 := by rw [hsum]
      _ ≤ M * ∑ x ∈ range M, windowCount B ℓ x ^ 2 := hCS
      _ ≤ M * (ℓ * (ℓ - 1) + ℓ * B.card) := Nat.mul_le_mul_left M hsq_le
  -- Eliminate the `ℓ-1` truncation by writing `ℓ = m+1`, then divide by `ℓ`.
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hcombine ⊢
  -- `hcombine : (m+1)²·k² ≤ M·((m+1)·m + (m+1)·k)`; goal after ÷(m+1):
  -- `(m+1)·k² ≤ M·(m + k)`.
  rw [hBcard] at hcombine
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos m)
  nlinarith [hcombine]

end Erdos340.OQ02
