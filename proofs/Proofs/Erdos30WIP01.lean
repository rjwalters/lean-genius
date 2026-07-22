/-
  Erdős Problem #30: Sidon Sets — the Erdős–Turán counting upper bound (0-axiom).

  Companion to `Erdos30Problem.lean`. That file defines `IsSidonSet`,
  `HasDistinctSums`, and the Sidon number `sidonNumber N = h(N)` (the maximum
  size of a Sidon set inside {0,1,…,N}), but leaves the actual bounds on `h(N)`
  in comments or as axioms. This file closes the elementary half of that gap:
  the classical Erdős–Turán (1941) *upper* bound, in the clean counting form.

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/Quot.sound):

  * `diffMap_injOn`         : on a Sidon set the difference map (a,b) ↦ a − b is
                              injective over the off-diagonal.
  * `sidon_offDiag_card_le` : a Sidon set A ⊆ {0,…,N} has |A|(|A|−1) ≤ 2N
                              (stated via `offDiag`, whose card is |A|² − |A|).
  * `sidon_card_sq_le`      : |A|² ≤ 2N + |A|.
  * `sidon_card_le_sqrt`    : |A| ≤ ⌊√(2N)⌋ + 1.
  * `sidonNumber_le_sqrt`   : h(N) = sidonNumber N ≤ ⌊√(2N)⌋ + 1.
  * `sidonNumber_le_real`   : (h(N) : ℝ) ≤ √(2N) + 1  — the √N shape of Erdős–Turán.

  Structural theory of the Sidon predicate (no Mathlib Sidon API; all axiom-free):

  * `isSidonSet_subset`     : Sidon-ness is hereditary (subsets of Sidon are Sidon).
  * `isSidonSet_image_add`  : Sidon-ness is translation-invariant (`A ↦ A + t`).
  * `one_le_sidonNumber`    : `1 ≤ h(N)` (the singleton `{0}` is Sidon), bracketing
                              `1 ≤ h(N) ≤ √(2N) + 1` with the bound above.
  * `sidonNumber_mono`      : `N ≤ M ⟹ h(N) ≤ h(M)` — `h` is monotone in the range.

  The mechanism: for a Sidon set the differences a − b (a ≠ b) are all distinct
  (a − b = c − d rewrites to a + d = c + b, and the Sidon property forces the
  pair to match), and they are nonzero integers in [−N, N], of which there are
  exactly 2N. So the number |A|(|A|−1) of ordered off-diagonal pairs is ≤ 2N.

  The open Erdős–Turán conjecture — that the N^{1/4} error term can be reduced to
  N^ε for every ε > 0 ($1000 prize) — is untouched, and stays a `Prop` in the
  parent file. This file only supplies the provable √(2N) upper envelope.
-/

import Mathlib
import Proofs.Erdos30Problem

open Finset

namespace Erdos30

/-- The signed difference map underlying the Erdős–Turán counting argument. -/
private def diffMap (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- **Injectivity of the difference map on a Sidon set.**
    If `a − b = c − d` with `a,b,c,d` in a Sidon set `A` and `a ≠ b`, `c ≠ d`,
    then `(a,b) = (c,d)`. The equation `a − b = c − d` is `a + d = c + b`, and the
    Sidon property (`HasDistinctSums`) forces `{a,d} = {c,b}`; the diagonal branch
    `a = b` is excluded on the off-diagonal. -/
theorem diffMap_injOn {A : Finset ℕ} (hA : IsSidonSet A) :
    Set.InjOn diffMap ↑A.offDiag := by
  intro p hp q hq hpq
  rw [Finset.mem_coe, Finset.mem_offDiag] at hp hq
  obtain ⟨hp1, hp2, hpne⟩ := hp
  obtain ⟨hq1, hq2, hqne⟩ := hq
  -- Turn `a − b = c − d` into the sum equation `p.1 + q.2 = q.1 + p.2`.
  have hsum : p.1 + q.2 = q.1 + p.2 := by
    have : (p.1 : ℤ) + q.2 = q.1 + p.2 := by
      simp only [diffMap] at hpq; omega
    exact_mod_cast this
  have hds := (sidon_iff_distinct_sums A).mp hA
  rcases hds p.1 q.2 q.1 p.2 hp1 hq2 hq1 hp2 hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2.symm
  · exact absurd h1 hpne

/-- **Erdős–Turán counting bound (off-diagonal form).**
    A Sidon set `A ⊆ {0,…,N}` has `|A|² − |A| = |A.offDiag| ≤ 2N`. -/
theorem sidon_offDiag_card_le {A : Finset ℕ} (N : ℕ)
    (hsub : A ⊆ Finset.range (N + 1)) (hA : IsSidonSet A) :
    A.offDiag.card ≤ 2 * N := by
  -- The difference map sends the off-diagonal into the 2N nonzero integers in [−N, N].
  have hmaps : ∀ p ∈ A.offDiag, diffMap p ∈ (Finset.Icc (-(N : ℤ)) N).erase 0 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hpne⟩ := hp
    have hb1 : p.1 ≤ N := by
      have := hsub hp1; rwa [Finset.mem_range, Nat.lt_succ_iff] at this
    have hb2 : p.2 ≤ N := by
      have := hsub hp2; rwa [Finset.mem_range, Nat.lt_succ_iff] at this
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨?_, ?_, ?_⟩
    · simp only [diffMap]; intro h; exact hpne (by omega)
    · simp only [diffMap]; omega
    · simp only [diffMap]; omega
  have hinj : Set.InjOn diffMap ↑A.offDiag := diffMap_injOn hA
  have hcard := Finset.card_le_card_of_injOn diffMap hmaps hinj
  have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by rw [Finset.mem_Icc]; omega
  have hScard : ((Finset.Icc (-(N : ℤ)) N).erase 0).card = 2 * N := by
    rw [Finset.card_erase_of_mem h0mem, Int.card_Icc]; omega
  omega

/-- **Erdős–Turán counting bound (square form).**
    A Sidon set `A ⊆ {0,…,N}` satisfies `|A|² ≤ 2N + |A|`. -/
theorem sidon_card_sq_le {A : Finset ℕ} (N : ℕ)
    (hsub : A ⊆ Finset.range (N + 1)) (hA : IsSidonSet A) :
    A.card * A.card ≤ 2 * N + A.card := by
  have h := sidon_offDiag_card_le N hsub hA
  rw [Finset.offDiag_card] at h
  omega

/-- **Erdős–Turán upper bound (√ form).**
    A Sidon set `A ⊆ {0,…,N}` has size at most `⌊√(2N)⌋ + 1`. -/
theorem sidon_card_le_sqrt {A : Finset ℕ} (N : ℕ)
    (hsub : A ⊆ Finset.range (N + 1)) (hA : IsSidonSet A) :
    A.card ≤ Nat.sqrt (2 * N) + 1 := by
  have hcard := sidon_card_sq_le N hsub hA
  -- (|A| − 1)² ≤ |A|(|A| − 1) = |A|² − |A| ≤ 2N.
  have key : (A.card - 1) * (A.card - 1) ≤ 2 * N := by
    rcases Nat.eq_zero_or_pos A.card with h0 | h0
    · simp [h0]
    · obtain ⟨m, hm⟩ : ∃ m, A.card = m + 1 := ⟨A.card - 1, by omega⟩
      rw [hm] at hcard ⊢
      have e : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      rw [e] at hcard
      simp only [Nat.add_sub_cancel]
      omega
  have hsqrt : A.card - 1 ≤ Nat.sqrt (2 * N) := Nat.le_sqrt.mpr key
  omega

/-- **Erdős–Turán bound on the Sidon number** `h(N) = sidonNumber N ≤ ⌊√(2N)⌋ + 1`.
    Every Sidon set in `{0,…,N}` obeys `sidon_card_le_sqrt`, and `h(N)` is the
    supremum of their sizes, so the bound passes to the supremum. -/
theorem sidonNumber_le_sqrt (N : ℕ) : sidonNumber N ≤ Nat.sqrt (2 * N) + 1 := by
  unfold sidonNumber
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  exact sidon_card_le_sqrt N hA.1 hA.2

/-- **Erdős–Turán bound in real form**: `h(N) ≤ √(2N) + 1`, the `√N` envelope. -/
theorem sidonNumber_le_real (N : ℕ) :
    (sidonNumber N : ℝ) ≤ Real.sqrt (2 * N) + 1 := by
  have h := sidonNumber_le_sqrt N
  have hnr : (Nat.sqrt (2 * N) : ℝ) ≤ Real.sqrt (2 * N) := by
    rw [show (Nat.sqrt (2 * N) : ℝ) = Real.sqrt ((Nat.sqrt (2 * N) : ℝ) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have hle : (Nat.sqrt (2 * N)) ^ 2 ≤ 2 * N := Nat.sqrt_le' (2 * N)
    calc (Nat.sqrt (2 * N) : ℝ) ^ 2 = ((Nat.sqrt (2 * N) ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hle
      _ = 2 * (N : ℝ) := by push_cast; ring
  calc (sidonNumber N : ℝ) ≤ ((Nat.sqrt (2 * N) + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ = (Nat.sqrt (2 * N) : ℝ) + 1 := by push_cast; ring
    _ ≤ Real.sqrt (2 * N) + 1 := by linarith [hnr]

/- ## Structural theory of Sidon sets

The counting bound above pins the *size* of a Sidon set; these are the elementary
closure/structure facts of the Sidon predicate itself (absent from Mathlib, which
has no `B₂`/Sidon API).  They are the natural companions of the Erdős–Turán bound:
Sidon-ness is hereditary and translation-invariant, and the Sidon number `h(N)` is
monotone in `N` and bounded *below* by `1` — so together with `sidonNumber_le_real`
the Sidon number is bracketed `1 ≤ h(N) ≤ √(2N) + 1`. -/

/-- **Sidon-ness is hereditary.**  Every subset of a Sidon set is Sidon: the
    distinct-sums condition on `A` restricts verbatim to any `B ⊆ A`, since all four
    witnesses `a,b,c,d ∈ B` are then in `A`. -/
theorem isSidonSet_subset {A B : Finset ℕ} (hBA : B ⊆ A) (hA : IsSidonSet A) :
    IsSidonSet B :=
  fun a b c d ha hb hc hd => hA a b c d (hBA ha) (hBA hb) (hBA hc) (hBA hd)

/-- **Sidon-ness is translation-invariant.**  Translating a Sidon set by a constant
    `t` (`A ↦ {a + t : a ∈ A}`) keeps it Sidon: a sum collision
    `(a+t)+(b+t) = (c+t)+(d+t)` cancels the `4t` to `a+b = c+d`, which the Sidon
    property of `A` resolves.  So the Sidon condition depends only on the *difference
    structure* of `A`, not its position. -/
theorem isSidonSet_image_add {A : Finset ℕ} (hA : IsSidonSet A) (t : ℕ) :
    IsSidonSet (A.image (· + t)) := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_image] at ha hb hc hd
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨d', hd', rfl⟩ := hd
  obtain ⟨h1, h2⟩ := hA a' b' c' d' ha' hb' hc' hd' (by omega) (by omega) (by omega)
  exact ⟨by omega, by omega⟩

/-- **The Sidon number is at least `1`.**  The singleton `{0}` is a Sidon subset of
    `{0,…,N}`, so `h(N) = sidonNumber N ≥ 1`.  Combined with `sidonNumber_le_real`
    this brackets `1 ≤ h(N) ≤ √(2N) + 1`. -/
theorem one_le_sidonNumber (N : ℕ) : 1 ≤ sidonNumber N := by
  unfold sidonNumber
  have h1 : (1 : ℕ) ≤ ({0} : Finset ℕ).card := by simp
  refine h1.trans (Finset.le_sup ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun x hx => ?_, fun a b c d ha hb hc hd _ _ _ => ?_⟩
  · simp only [Finset.mem_singleton] at hx
    subst hx; simp
  · simp only [Finset.mem_singleton] at ha hb hc hd
    subst ha; subst hb; subst hc; subst hd
    exact ⟨rfl, rfl⟩

/-- **The Sidon number is monotone in the range.**  `N ≤ M ⟹ h(N) ≤ h(M)`: every
    Sidon subset of `{0,…,N}` is a Sidon subset of the larger `{0,…,M}`, so the
    supremum of Sidon-set sizes can only grow. -/
theorem sidonNumber_mono {N M : ℕ} (h : N ≤ M) : sidonNumber N ≤ sidonNumber M := by
  unfold sidonNumber
  apply Finset.sup_mono
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
  refine ⟨fun x hx => ?_, hA.2⟩
  have hxN := hA.1 hx
  rw [Finset.mem_range] at hxN ⊢
  omega

end Erdos30
