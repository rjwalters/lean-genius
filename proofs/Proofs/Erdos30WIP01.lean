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

/- ## A growing Sidon family: powers of two (a lower bound on `h(N)`)

The results above bound `h(N)` from *above* by `√(2N) + 1`, but the only lower
bound so far is the trivial `1 ≤ h(N)` (the singleton). Here we supply a genuine
*growing* lower bound: the `k + 1` powers `{2^0, 2^1, …, 2^k}` form a Sidon set
inside `{0, …, 2^k}`, so `h(2^k) ≥ k + 1`. In particular `h(N)` is unbounded
(`sidonNumber_unbounded`). This is only a logarithmic bound — far from the sharp
`√N` growth (which needs Singer/perfect-difference-set constructions, absent from
Mathlib) — but it is the first proof in this file that `h(N) → ∞`. -/

/-- **Powers of two have distinct pairwise sums.** If `2^i + 2^j = 2^p + 2^q` with
`i ≤ j` and `p ≤ q` and `i ≤ p`, then `(i, j) = (p, q)`. The 2-adic valuation of the
smaller exponent must match (else one side is odd and the other even, or one side is
`2` while the other is `≥ 4`), forcing `i = p`; cancelling then gives `j = q`. -/
private theorem two_pow_add_inj {i j p q : ℕ} (hij : i ≤ j) (hpq : p ≤ q)
    (hip : i ≤ p) (h : 2 ^ i + 2 ^ j = 2 ^ p + 2 ^ q) : i = p ∧ j = q := by
  have hiq : i ≤ q := hip.trans hpq
  have hi_p : i = p := by
    by_contra hne
    have hlt : i < p := lt_of_le_of_ne hip hne
    have e1 : 2 ^ i + 2 ^ j = 2 ^ i * (1 + 2 ^ (j - i)) := by
      rw [Nat.mul_add, Nat.mul_one, ← pow_add, Nat.add_sub_cancel' hij]
    have e2 : 2 ^ p + 2 ^ q = 2 ^ i * (2 ^ (p - i) + 2 ^ (q - i)) := by
      rw [Nat.mul_add, ← pow_add, ← pow_add, Nat.add_sub_cancel' hip,
        Nat.add_sub_cancel' hiq]
    rw [e1, e2] at h
    have hcancel : 1 + 2 ^ (j - i) = 2 ^ (p - i) + 2 ^ (q - i) :=
      Nat.eq_of_mul_eq_mul_left (by positivity) h
    have hPpos : 0 < p - i := by omega
    have hQpos : 0 < q - i := by omega
    have hReven : Even (2 ^ (p - i) + 2 ^ (q - i)) :=
      (Nat.even_pow.mpr ⟨even_two, by omega⟩).add (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rcases Nat.eq_zero_or_pos (j - i) with hj0 | hjpos
    · rw [hj0] at hcancel
      have h2p : 2 ≤ 2 ^ (p - i) := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (p - i) := Nat.pow_le_pow_right (by norm_num) hPpos
      have h2q : 2 ≤ 2 ^ (q - i) := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (q - i) := Nat.pow_le_pow_right (by norm_num) hQpos
      simp only [pow_zero] at hcancel
      omega
    · have hLodd : Odd (1 + 2 ^ (j - i)) := by
        rw [Nat.add_comm]
        exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      rw [hcancel] at hLodd
      rw [Nat.even_iff] at hReven
      rw [Nat.odd_iff] at hLodd
      omega
  refine ⟨hi_p, ?_⟩
  subst hi_p
  have hjq : 2 ^ j = 2 ^ q := by omega
  exact Nat.pow_right_injective (by norm_num) hjq

/-- **The powers `{2^0, …, 2^k}` form a Sidon set.** -/
theorem isSidonSet_two_pow_range (k : ℕ) :
    IsSidonSet ((Finset.range (k + 1)).image (2 ^ ·)) := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_image, Finset.mem_range] at ha hb hc hd
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, rfl⟩ := hb
  obtain ⟨p, _, rfl⟩ := hc
  obtain ⟨q, _, rfl⟩ := hd
  have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hab
  have hpq : p ≤ q := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcd
  rcases le_total i p with hip | hpi
  · obtain ⟨hi, hj⟩ := two_pow_add_inj hij hpq hip heq
    exact ⟨by rw [hi], by rw [hj]⟩
  · obtain ⟨hp, hq⟩ := two_pow_add_inj hpq hij hpi heq.symm
    exact ⟨by rw [hp], by rw [hq]⟩

/-- **`{2^0, …, 2^k}` sits inside `{0, …, 2^k}`.** -/
theorem two_pow_range_subset (k : ℕ) :
    (Finset.range (k + 1)).image (2 ^ ·) ⊆ Finset.range (2 ^ k + 1) := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range]
  have : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Lower bound `h(2^k) ≥ k + 1`.** The `k + 1` distinct powers `{2^0, …, 2^k}` are a
Sidon subset of `{0, …, 2^k}`, so the Sidon number of `2^k` is at least their count. -/
theorem sidonNumber_two_pow_ge (k : ℕ) : k + 1 ≤ sidonNumber (2 ^ k) := by
  have hcard : ((Finset.range (k + 1)).image (2 ^ ·)).card = k + 1 := by
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num)),
      Finset.card_range]
  unfold sidonNumber
  rw [← hcard]
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨two_pow_range_subset k, isSidonSet_two_pow_range k⟩

/-- **The Sidon number is unbounded.** For every `M` there is an `N` with
`h(N) ≥ M` (take `N = 2^M`, giving `h(2^M) ≥ M + 1`). So `h(N) → ∞`, a qualitative
lower complement to the `√(2N) + 1` upper bound. -/
theorem sidonNumber_unbounded : ∀ M : ℕ, ∃ N : ℕ, M ≤ sidonNumber N :=
  fun M => ⟨2 ^ M, (Nat.le_succ M).trans (sidonNumber_two_pow_ge M)⟩

/- ## Exact initial values of the Sidon number

The counting upper bound `|A|² ≤ 2N + |A|` (`sidon_card_sq_le`) is *sharp* for small
`N`: matched against explicit optimal Sidon sets it pins the exact value of
`h(N) = sidonNumber N` for `N ≤ 6`, giving the initial segment

  `h(0), …, h(6) = 1, 2, 2, 3, 3, 3, 4`.

This exhibits `h` as a (non-strict) step function — the counting bound alone already
determines `h` exactly in the small range, before the `√N` asymptotics take over. The
optimal witnesses are `{0}`, `{0,1}`, `{0,1,3}` (a perfect ruler on 4 points) and
`{0,1,4,6}` (whose six differences `1,2,3,4,5,6` are all distinct — a perfect
difference set on 7 points). -/

/-- **Lower bound from an explicit Sidon set.**  Any Sidon set `A ⊆ {0,…,N}` witnesses
`|A| ≤ h(N)`, since `h(N)` is the supremum of the sizes of such sets.  This is the
lower-bound companion of `sidon_card_le_sqrt` (the per-set upper bound). -/
theorem sidonNumber_ge_card {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Finset.range (N + 1)) (hA : IsSidonSet A) : A.card ≤ sidonNumber N := by
  unfold sidonNumber
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hA⟩

/-- **Sharp counting upper bound on `h(N)`.**  If every `m` with `m² ≤ 2N + m` satisfies
`m ≤ B`, then `h(N) ≤ B`.  Each Sidon set in `{0,…,N}` has `|A|² ≤ 2N + |A|`
(`sidon_card_sq_le`), so its size — and hence the supremum `h(N)` — is `≤ B`.  For small
`N` this is *sharp* (unlike the looser `⌊√(2N)⌋ + 1`), because it uses the exact
quadratic rather than a square-root relaxation. -/
theorem sidonNumber_le_of_sq {N B : ℕ}
    (h : ∀ m : ℕ, m * m ≤ 2 * N + m → m ≤ B) : sidonNumber N ≤ B := by
  unfold sidonNumber
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  exact h A.card (sidon_card_sq_le N hA.1 hA.2)

-- Explicit optimal Sidon sets (verified by exhaustive case analysis on membership).
private theorem isSidonSet_0_1 : IsSidonSet {0, 1} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> omega

private theorem isSidonSet_0_1_3 : IsSidonSet {0, 1, 3} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> omega

private theorem isSidonSet_0_1_4_6 : IsSidonSet {0, 1, 4, 6} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> omega

/-- `h(0) = 1`: the only nonempty Sidon set in `{0}` is `{0}` itself. -/
theorem sidonNumber_zero : sidonNumber 0 = 1 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) (one_le_sidonNumber 0)
  by_contra hc; rw [not_le] at hc; nlinarith [hm, hc]

/-- `h(1) = 2`, with optimal witness `{0,1}`. -/
theorem sidonNumber_one : sidonNumber 1 = 2 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc; nlinarith [hm, hc]
  · calc 2 = ({0, 1} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 1 := sidonNumber_ge_card (by decide) isSidonSet_0_1

/-- `h(2) = 2`: `{0,1,2}` fails (`0+2 = 1+1`), so `{0,1}` is still optimal. -/
theorem sidonNumber_two : sidonNumber 2 = 2 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc; nlinarith [hm, hc]
  · calc 2 = ({0, 1} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 2 := sidonNumber_ge_card (by decide) isSidonSet_0_1

/-- `h(3) = 3`, with optimal witness `{0,1,3}`. -/
theorem sidonNumber_three : sidonNumber 3 = 3 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc; nlinarith [hm, hc]
  · calc 3 = ({0, 1, 3} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 3 := sidonNumber_ge_card (by decide) isSidonSet_0_1_3

/-- `h(4) = 3`: six distinct differences cannot fit in `{1,…,4}`, so `{0,1,3}` stays optimal. -/
theorem sidonNumber_four : sidonNumber 4 = 3 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc; nlinarith [hm, hc]
  · calc 3 = ({0, 1, 3} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 4 := sidonNumber_ge_card (by decide) isSidonSet_0_1_3

/-- `h(5) = 3`: still no room for a 4-element Sidon set (`4·3 = 12 > 10 = 2·5`). -/
theorem sidonNumber_five : sidonNumber 5 = 3 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc; nlinarith [hm, hc]
  · calc 3 = ({0, 1, 3} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 5 := sidonNumber_ge_card (by decide) isSidonSet_0_1_3

/-- `h(6) = 4`, with optimal witness `{0,1,4,6}` — a perfect difference set whose six
differences `1,2,3,4,5,6` exhaust `{1,…,6}`. -/
theorem sidonNumber_six : sidonNumber 6 = 4 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc; nlinarith [hm, hc]
  · calc 4 = ({0, 1, 4, 6} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 6 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_6

/-- `h(7) = 4`: the counting bound rules out a 5-element Sidon set
(`5·4 = 20 > 14 = 2·7`), and `{0,1,4,6} ⊆ {0,…,7}` still attains `4`.

Unlike `h(6)`, the quadratic `m² ≤ 2·7 + m` has its real root at `(1+√57)/2 ≈ 4.27`,
so `nlinarith` needs the integrality step `5 ≤ m` (from `4 < m` over `ℕ`) to exclude
the real gap `(4, 4.27]`. -/
theorem sidonNumber_seven : sidonNumber 7 = 4 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h5 : 5 ≤ m := hc
    nlinarith [hm, h5]
  · calc 4 = ({0, 1, 4, 6} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 7 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_6

/-- `h(8) = 4`: `5·4 = 20 > 16 = 2·8` still blocks a 5-element Sidon set, and
`{0,1,4,6} ⊆ {0,…,8}` attains `4`. -/
theorem sidonNumber_eight : sidonNumber 8 = 4 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h5 : 5 ≤ m := hc
    nlinarith [hm, h5]
  · calc 4 = ({0, 1, 4, 6} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 8 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_6

/-- `h(9) = 4`: `5·4 = 20 > 18 = 2·9` blocks a 5-element Sidon set, and
`{0,1,4,6} ⊆ {0,…,9}` attains `4`.  `h(10)` is the first value where the counting
bound goes slack (`5·4 = 20 = 2·10` admits `m = 5`), so the table's easy stretch
ends here — a 5-element Sidon set first fits at `N = 11` (`{0,1,4,9,11}`). -/
theorem sidonNumber_nine : sidonNumber 9 = 4 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h5 : 5 ≤ m := hc
    nlinarith [hm, h5]
  · calc 4 = ({0, 1, 4, 6} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 9 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_6

/-! ### `h(10) = 4` — breaking the counting wall with a parity argument

For `N ≤ 9` the counting bound `|A|² ≤ 2N + |A|` alone forces `|A| ≤ 4`.  At `N = 10`
it goes slack: `5·4 = 20 = 2·10` admits a 5-element set.  A genuinely new obstruction
is needed, and it is a clean parity fact.

A 5-element Sidon set `A ⊆ {0,…,10}` has `C(5,2) = 10` *distinct* ordered positive
differences `a − b` (`a > b`), all lying in `{1,…,10}`; being 10 distinct values in a
10-element set they are **exactly** `{1,…,10}` — a *perfect difference set* / perfect
ruler.  Their sum is therefore `1 + 2 + ⋯ + 10 = 55`, which is **odd**.

But the sum of the ordered positive differences is always **even**: writing
`S₁ = ∑_{a>b} a` and `S₂ = ∑_{a>b} b`, the sum is `S₁ − S₂`, while `S₁ + S₂` equals
`∑_{(a,b) ∈ offDiag} a = (|A| − 1)·∑A = 4·∑A` (each element is a first coordinate of
`|A| − 1` ordered pairs).  Hence `S₁ − S₂ = 4·∑A − 2·S₂` is even.  Even ≠ 55, so no
such set exists and `h(10) = 4`.  A perfect ruler with 5 marks does not exist. -/

/-- **General size bound helper.** If every Sidon subset of `{0,…,N}` has size at most
`B`, then `h(N) = sidonNumber N ≤ B`.  (The counting-based `sidonNumber_le_of_sq` is the
special case `B = ⌊…⌋`; this form accepts any pointwise size argument.) -/
theorem sidonNumber_le_of_card {N B : ℕ}
    (h : ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → IsSidonSet A → A.card ≤ B) :
    sidonNumber N ≤ B := by
  unfold sidonNumber
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  exact h A hA.1 hA.2

/-- **Off-diagonal first-coordinate sum.** `∑_{(a,b) ∈ A.offDiag} a = (|A| − 1)·∑A`:
each `a ∈ A` is the first coordinate of exactly `|A| − 1` ordered off-diagonal pairs.
(Computed as `∑_{A×A} a − ∑_{diag} a = |A|·∑A − ∑A`.) -/
theorem sum_offDiag_fst (A : Finset ℕ) :
    ∑ p ∈ A.offDiag, (p.1 : ℤ) = ((A.card : ℤ) - 1) * ∑ a ∈ A, (a : ℤ) := by
  have hsplit : ∑ p ∈ A ×ˢ A, (p.1 : ℤ)
      = ∑ p ∈ A.diag, (p.1 : ℤ) + ∑ p ∈ A.offDiag, (p.1 : ℤ) := by
    rw [← Finset.diag_union_offDiag A, Finset.sum_union (Finset.disjoint_diag_offDiag A)]
  have hprod : ∑ p ∈ A ×ˢ A, (p.1 : ℤ) = (A.card : ℤ) * ∑ a ∈ A, (a : ℤ) := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hc : ∀ b, ((a, b).1 : ℤ) = (a : ℤ) := fun _ => rfl
    simp_rw [hc, Finset.sum_const, nsmul_eq_mul]
  have hdiag : ∑ p ∈ A.diag, (p.1 : ℤ) = ∑ a ∈ A, (a : ℤ) := by
    simp [Finset.sum_diag]
  rw [hprod, hdiag] at hsplit
  have hoff : ∑ p ∈ A.offDiag, (p.1 : ℤ)
      = (A.card : ℤ) * ∑ a ∈ A, (a : ℤ) - ∑ a ∈ A, (a : ℤ) := by linarith
  rw [hoff]; ring

/-- **No 5-element Sidon set fits in `{0,…,10}`** — the perfect-ruler parity obstruction.
Such a set would have `10` distinct positive differences exhausting `{1,…,10}` (sum `55`,
odd), yet the sum of ordered positive differences is always even. -/
theorem no_sidon_card_five_range_eleven (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 11) (hA : IsSidonSet A) : A.card ≤ 4 := by
  by_contra hcard
  rw [not_le] at hcard
  -- Counting caps the size at 5, so a violating set has exactly 5 elements.
  have hup : A.card * A.card ≤ 20 + A.card := by
    have := sidon_card_sq_le 10 hsub hA; omega
  have hc5 : A.card = 5 := by
    have h5 : 5 ≤ A.card := hcard
    by_contra hne
    have h6 : 6 ≤ A.card := by omega
    have hmul : 6 * A.card ≤ A.card * A.card := Nat.mul_le_mul h6 (le_refl A.card)
    omega
  -- `P` = ordered pairs `(a,b)` with `a > b`: the positive-difference pairs.
  set P := A.offDiag.filter (fun p => p.2 < p.1) with hP
  have hPsub : P ⊆ A.offDiag := Finset.filter_subset _ _
  have hinjP : Set.InjOn diffMap ↑P :=
    (diffMap_injOn hA).mono (Finset.coe_subset.mpr hPsub)
  -- Both coordinates of any off-diagonal pair are `≤ 10`.
  have hle10 : ∀ p ∈ A.offDiag, p.1 ≤ 10 ∧ p.2 ≤ 10 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    have h1 := hsub hp.1
    have h2 := hsub hp.2.1
    rw [Finset.mem_range] at h1 h2
    omega
  -- Positive differences land in `[1,10]`.
  have hmaps : ∀ p ∈ P, diffMap p ∈ Finset.Icc (1 : ℤ) 10 := by
    intro p hp
    rw [hP, Finset.mem_filter] at hp
    obtain ⟨hpoff, hlt⟩ := hp
    have hb := hle10 p hpoff
    rw [Finset.mem_Icc]
    simp only [diffMap]
    constructor <;> omega
  -- `|P| = 10`: `P` and its swap are the two equal halves of the 20-element off-diagonal.
  have hoffcard : A.offDiag.card = 20 := by
    rw [Finset.offDiag_card, hc5]
  have hpart := Finset.card_filter_add_card_filter_not A.offDiag (fun p => p.2 < p.1)
  have hfeq : A.offDiag.filter (fun p => ¬ p.2 < p.1)
            = A.offDiag.filter (fun p => p.1 < p.2) := by
    apply Finset.filter_congr
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨_, _, hne⟩ := hp
    constructor <;> intro <;> omega
  have hswapcard : (A.offDiag.filter (fun p => p.1 < p.2)).card
                 = (A.offDiag.filter (fun p => p.2 < p.1)).card := by
    apply Finset.card_nbij' Prod.swap Prod.swap
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
      obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := hp
      exact ⟨⟨h2, h1, fun h => hne h.symm⟩, by simp only [Prod.swap]; omega⟩
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
      obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := hp
      exact ⟨⟨h2, h1, fun h => hne h.symm⟩, by simp only [Prod.swap]; omega⟩
    · intro p _; simp [Prod.swap]
    · intro p _; simp [Prod.swap]
  have hcardP : P.card = 10 := by
    rw [hP] at hoffcard hpart ⊢
    rw [hfeq, hswapcard] at hpart
    omega
  -- The image of `P` under `diffMap` is exactly `{1,…,10}`.
  have hDsub : P.image diffMap ⊆ Finset.Icc (1 : ℤ) 10 := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    exact hmaps p hp
  have hcardimg : (P.image diffMap).card = 10 := by
    rw [Finset.card_image_of_injOn hinjP, hcardP]
  have hIcc : (Finset.Icc (1 : ℤ) 10).card = 10 := by decide
  have hDeq : P.image diffMap = Finset.Icc (1 : ℤ) 10 :=
    Finset.eq_of_subset_of_card_le hDsub (by rw [hcardimg, hIcc])
  -- Sum of the positive differences is `1 + ⋯ + 10 = 55`.
  have himg_sum : ∑ d ∈ P.image diffMap, d = ∑ p ∈ P, diffMap p :=
    Finset.sum_image hinjP
  have hsum55 : ∑ p ∈ P, diffMap p = 55 := by
    rw [← himg_sum, hDeq]; decide
  -- Structural parity: `∑ p₁ + ∑ p₂ = ∑_{offDiag} p₁ = 4·∑A` is even.
  have hS1S2 : ∑ p ∈ P, (p.1 : ℤ) + ∑ p ∈ P, (p.2 : ℤ)
             = ∑ p ∈ A.offDiag, (p.1 : ℤ) := by
    have hfa := Finset.sum_filter_add_sum_filter_not A.offDiag
      (fun p => p.2 < p.1) (fun p => (p.1 : ℤ))
    have hswap : ∑ p ∈ A.offDiag.filter (fun p => ¬ p.2 < p.1), (p.1 : ℤ)
               = ∑ p ∈ P, (p.2 : ℤ) := by
      rw [hP]
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
      · intro q hq
        rw [Finset.mem_filter, Finset.mem_offDiag] at hq ⊢
        obtain ⟨⟨h1, h2, hne⟩, hnlt⟩ := hq
        exact ⟨⟨h2, h1, fun h => hne h.symm⟩, by simp only [Prod.swap]; omega⟩
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
        obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := hp
        exact ⟨⟨h2, h1, fun h => hne h.symm⟩, by simp only [Prod.swap]; omega⟩
      · intro q _; simp [Prod.swap]
      · intro p _; simp [Prod.swap]
      · intro q _; simp only [Prod.swap]
    rw [hswap] at hfa
    rw [← hP] at hfa
    linarith [hfa]
  have heven : Even (∑ p ∈ P, diffMap p) := by
    have hval : ∑ p ∈ P, diffMap p = ∑ p ∈ P, (p.1 : ℤ) - ∑ p ∈ P, (p.2 : ℤ) := by
      simp only [diffMap]; rw [Finset.sum_sub_distrib]
    have hoff := sum_offDiag_fst A
    rw [hc5] at hoff
    have h4 : ∑ p ∈ P, (p.1 : ℤ) + ∑ p ∈ P, (p.2 : ℤ) = 4 * ∑ a ∈ A, (a : ℤ) := by
      rw [hS1S2, hoff]; norm_num
    rw [hval]
    refine ⟨2 * ∑ a ∈ A, (a : ℤ) - ∑ p ∈ P, (p.2 : ℤ), ?_⟩
    linarith [h4]
  rw [hsum55] at heven
  exact absurd heven (by norm_num)

/-- `h(10) = 4` — the first value past the counting wall.  A perfect ruler with 5 marks
would be required for `h(10) = 5` and none exists (`no_sidon_card_five_range_eleven`);
`{0,1,4,6} ⊆ {0,…,10}` still attains `4`. -/
theorem sidonNumber_ten : sidonNumber 10 = 4 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_five_range_eleven A hsub hA)
  · calc 4 = ({0, 1, 4, 6} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 10 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_6

end Erdos30
