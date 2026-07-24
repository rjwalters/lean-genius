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
    rw [show (∑ y ∈ A, ((a, y).1 : ℤ)) = ∑ _y ∈ A, (a : ℤ) from rfl,
      Finset.sum_const, nsmul_eq_mul]
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
  -- `P` = the positive-difference ordered pairs `(a, b)` with `a > b` (i.e. `diffMap > 0`).
  set P := A.offDiag.filter (fun p => 0 < diffMap p) with hP
  have hPsub : P ⊆ A.offDiag := Finset.filter_subset _ _
  have hfull : Set.InjOn diffMap ↑A.offDiag := diffMap_injOn hA
  have hinjP : Set.InjOn diffMap ↑P := hfull.mono (Finset.coe_subset.mpr hPsub)
  have hoffcard : A.offDiag.card = 20 := by rw [Finset.offDiag_card, hc5]
  -- `diffMap` sends the off-diagonal onto the 20 nonzero integers of `[-10, 10]`.
  have hmapsFull : ∀ p ∈ A.offDiag, diffMap p ∈ (Finset.Icc (-10 : ℤ) 10).erase 0 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hpne⟩ := hp
    have hb1 := hsub hp1; have hb2 := hsub hp2
    rw [Finset.mem_range] at hb1 hb2
    rw [Finset.mem_erase, Finset.mem_Icc]
    simp only [diffMap]
    exact ⟨fun h => hpne (by omega), by omega, by omega⟩
  have hcardErase : ((Finset.Icc (-10 : ℤ) 10).erase 0).card = 20 := by
    rw [Finset.card_erase_of_mem (by decide), Int.card_Icc]; decide
  have himageFull : A.offDiag.image diffMap = (Finset.Icc (-10 : ℤ) 10).erase 0 := by
    refine Finset.eq_of_subset_of_card_le (fun d hd => ?_) ?_
    · rw [Finset.mem_image] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      exact hmapsFull p hp
    · rw [Finset.card_image_of_injOn hfull, hoffcard]
      exact le_of_eq hcardErase
  -- The positive differences are exactly `{1, …, 10}` (a perfect difference set).
  have hPimg : P.image diffMap = Finset.Icc (1 : ℤ) 10 := by
    rw [hP, ← Finset.filter_image, himageFull]; decide
  -- Hence the sum of positive differences is `1 + 2 + ⋯ + 10 = 55`.
  have hsum55 : ∑ p ∈ P, diffMap p = 55 := by
    have hsi := Finset.sum_image (f := fun d : ℤ => d) hinjP
    rw [hPimg] at hsi
    rw [← hsi]; decide
  -- Structural parity: `∑ p₁ + ∑ p₂ = ∑_{offDiag} p₁ = 4·∑A`, hence even.
  have hS1S2 : ∑ p ∈ P, (p.1 : ℤ) + ∑ p ∈ P, (p.2 : ℤ)
             = ∑ p ∈ A.offDiag, (p.1 : ℤ) := by
    have key : ∑ p ∈ A.offDiag, (p.1 : ℤ)
        = ∑ p ∈ P, (p.1 : ℤ)
          + ∑ p ∈ A.offDiag.filter (fun p => ¬ 0 < diffMap p), (p.1 : ℤ) := by
      rw [hP]
      exact (Finset.sum_filter_add_sum_filter_not A.offDiag
        (fun p => 0 < diffMap p) (fun p => (p.1 : ℤ))).symm
    have hswap : ∑ p ∈ A.offDiag.filter (fun p => ¬ 0 < diffMap p), (p.1 : ℤ)
               = ∑ p ∈ P, (p.2 : ℤ) := by
      rw [hP]
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_
        (fun a _ => Prod.swap_swap a) (fun a _ => Prod.swap_swap a) (fun a _ => rfl)
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := ha
        simp only [diffMap, not_lt] at hlt
        refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
        show 0 < (a.2 : ℤ) - (a.1 : ℤ); omega
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := ha
        simp only [diffMap] at hlt
        refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
        show ¬ 0 < (a.2 : ℤ) - (a.1 : ℤ); omega
    rw [key, hswap]
  have heven : Even (∑ p ∈ P, diffMap p) := by
    have hval : ∑ p ∈ P, diffMap p = ∑ p ∈ P, (p.1 : ℤ) - ∑ p ∈ P, (p.2 : ℤ) := by
      simp only [diffMap]; rw [Finset.sum_sub_distrib]
    have hoff := sum_offDiag_fst A
    rw [hc5] at hoff
    have h4 : ∑ p ∈ P, (p.1 : ℤ) + ∑ p ∈ P, (p.2 : ℤ) = 4 * ∑ a ∈ A, (a : ℤ) := by
      rw [hS1S2, hoff]; norm_num
    rw [hval]
    exact ⟨2 * ∑ a ∈ A, (a : ℤ) - ∑ p ∈ P, (p.2 : ℤ), by linarith [h4]⟩
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

/-! ### `h(11) = h(12) = h(13) = h(14) = 5` — the counting bound resumes

At `N = 11` a 5-element Sidon set first fits: `{0,1,4,9,11}` (pairwise sums
`1,4,5,9,10,11,12,13,15,20` and doubles `0,2,8,18,22` — all distinct).  On the
upper side the counting bound `|A|² ≤ 2N + |A|` is active again against a
6-element set: `6·5 = 30 > 2N` for every `N ≤ 14`, i.e. the `C(6,2) = 15`
distinct positive differences of a 6-element Sidon set cannot fit in `{1,…,N}`.
So the exact table extends through `h(14) = 5` with a single witness and the
existing counting machinery.

The wall returns at `N = 15`: `6·5 = 30 = 2·15` goes slack, and the `h(10)`
parity obstruction does NOT transfer — a 6-mark perfect ruler of length 15
would have difference sum `1 + ⋯ + 15 = 120`, which is *even*, so parity is
silent.  Ruling out `h(15) = 6` requires the (true, but finer) nonexistence of
a perfect 6-mark ruler — the natural next-session target. -/

private theorem isSidonSet_0_1_4_9_11 : IsSidonSet {0, 1, 4, 9, 11} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> omega

/-- `h(11) = 5`, with optimal witness `{0,1,4,9,11}` — a 5-element Sidon set first
fits at `N = 11`, and the counting bound (`6·5 = 30 > 22 = 2·11`) rules out `6`. -/
theorem sidonNumber_eleven : sidonNumber 11 = 5 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h6 : 6 ≤ m := hc
    nlinarith [hm, h6]
  · calc 5 = ({0, 1, 4, 9, 11} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 11 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_9_11

/-- `h(12) = 5`: `6·5 = 30 > 24 = 2·12` still blocks a 6-element Sidon set, and
`{0,1,4,9,11} ⊆ {0,…,12}` attains `5`. -/
theorem sidonNumber_twelve : sidonNumber 12 = 5 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h6 : 6 ≤ m := hc
    nlinarith [hm, h6]
  · calc 5 = ({0, 1, 4, 9, 11} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 12 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_9_11

/-- `h(13) = 5`: `6·5 = 30 > 26 = 2·13` blocks a 6-element Sidon set, and
`{0,1,4,9,11} ⊆ {0,…,13}` attains `5`. -/
theorem sidonNumber_thirteen : sidonNumber 13 = 5 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h6 : 6 ≤ m := hc
    nlinarith [hm, h6]
  · calc 5 = ({0, 1, 4, 9, 11} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 13 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_9_11

/-- `h(14) = 5`: `6·5 = 30 > 28 = 2·14` blocks a 6-element Sidon set, and
`{0,1,4,9,11} ⊆ {0,…,14}` attains `5`.  This closes the easy stretch: at `N = 15`
the counting bound goes slack (`30 = 2·15`) and the parity argument is silent
(`1+⋯+15 = 120` is even), so `h(15)` needs the nonexistence of a perfect 6-mark
ruler. -/
theorem sidonNumber_fourteen : sidonNumber 14 = 5 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h6 : 6 ≤ m := hc
    nlinarith [hm, h6]
  · calc 5 = ({0, 1, 4, 9, 11} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 14 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_9_11

/-! ### `h(15) = 5` — breaking the second wall with a mod-3 class count

At `N = 15` the counting bound goes slack again (`6·5 = 30 = 2·15` admits a 6-element
set) and the `h(10)` parity trick is silent: a 6-element Sidon set in `{0,…,15}` would
have `C(6,2) = 15` distinct positive differences exhausting `{1,…,15}` — a perfect
6-mark ruler — whose sum `1 + ⋯ + 15 = 120` is *even*, so no parity contradiction.

A **mod-3 class count** kills it instead.  Among `{1,…,15}` exactly `5` values are
divisible by `3`.  On the other hand, a pair `(a, b)` has `3 ∣ a − b` iff `a` and `b`
lie in the same residue class mod `3`; writing `c₀, c₁, c₂` for the sizes of the three
residue classes of `A`, the number of *ordered* off-diagonal pairs with `3 ∣ a − b` is
`∑ cᵣ(cᵣ − 1)`, which must equal `2·5 = 10`.  But with `c₀ + c₁ + c₂ = 6` the quantity
`∑ cᵣ(cᵣ − 1)` only takes the values

  `(6,0,0) ↦ 30, (5,1,0) ↦ 20, (4,2,0) ↦ 14, (4,1,1) ↦ 12, (3,3,0) ↦ 12,
   (3,2,1) ↦ 8, (2,2,2) ↦ 6`

— never `10`.  So no perfect 6-mark ruler exists and `h(15) = 5`. -/

/-- **No 6-element Sidon set fits in `{0,…,15}`** — the perfect-ruler mod-3 obstruction.
Such a set would have `15` distinct positive differences exhausting `{1,…,15}`, hence
exactly `10` ordered off-diagonal pairs with difference divisible by `3`; but the
same-residue-class pair count `∑ cᵣ(cᵣ − 1)` with `c₀ + c₁ + c₂ = 6` never equals `10`. -/
theorem no_sidon_card_six_range_sixteen (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 16) (hA : IsSidonSet A) : A.card ≤ 5 := by
  by_contra hcard
  rw [not_le] at hcard
  -- Counting caps the size at 6, so a violating set has exactly 6 elements.
  have hup : A.card * A.card ≤ 30 + A.card := by
    have := sidon_card_sq_le 15 hsub hA; omega
  have hc6 : A.card = 6 := by
    have h6 : 6 ≤ A.card := hcard
    by_contra hne
    have h7 : 7 ≤ A.card := by omega
    have hmul : 7 * A.card ≤ A.card * A.card := Nat.mul_le_mul h7 (le_refl A.card)
    omega
  have hfull : Set.InjOn diffMap ↑A.offDiag := diffMap_injOn hA
  have hoffcard : A.offDiag.card = 30 := by rw [Finset.offDiag_card, hc6]
  -- `diffMap` sends the off-diagonal onto the 30 nonzero integers of `[-15, 15]`.
  have hmapsFull : ∀ p ∈ A.offDiag, diffMap p ∈ (Finset.Icc (-15 : ℤ) 15).erase 0 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hpne⟩ := hp
    have hb1 := hsub hp1; have hb2 := hsub hp2
    rw [Finset.mem_range] at hb1 hb2
    rw [Finset.mem_erase, Finset.mem_Icc]
    simp only [diffMap]
    exact ⟨fun h => hpne (by omega), by omega, by omega⟩
  have hcardErase : ((Finset.Icc (-15 : ℤ) 15).erase 0).card = 30 := by
    rw [Finset.card_erase_of_mem (by decide), Int.card_Icc]; decide
  have himageFull : A.offDiag.image diffMap = (Finset.Icc (-15 : ℤ) 15).erase 0 := by
    refine Finset.eq_of_subset_of_card_le (fun d hd => ?_) ?_
    · rw [Finset.mem_image] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      exact hmapsFull p hp
    · rw [Finset.card_image_of_injOn hfull, hoffcard]
      exact le_of_eq hcardErase
  -- `T` = the off-diagonal pairs whose difference is divisible by `3`.
  set T := A.offDiag.filter (fun p => diffMap p % 3 = 0) with hT
  have hTsub : T ⊆ A.offDiag := Finset.filter_subset _ _
  have hinjT : Set.InjOn diffMap ↑T := hfull.mono (Finset.coe_subset.mpr hTsub)
  -- Its image is the 10 nonzero multiples of 3 in `[-15, 15]`, so `|T| = 10`.
  have hTimg : T.image diffMap
      = ((Finset.Icc (-15 : ℤ) 15).erase 0).filter (fun d => d % 3 = 0) := by
    rw [hT, ← Finset.filter_image (p := fun d : ℤ => d % 3 = 0), himageFull]
  have hTcard : T.card = 10 := by
    rw [← Finset.card_image_of_injOn hinjT, hTimg]
    decide
  -- Structurally, `T` is the set of same-residue pairs, fibered by the residue class.
  have hTeq : T = A.offDiag.filter (fun p => p.1 % 3 = p.2 % 3) := by
    rw [hT]
    refine Finset.filter_congr (fun p hp => ?_)
    simp only [diffMap]
    omega
  have hfiber : ∀ r : ℕ, T.filter (fun p => p.1 % 3 = r)
      = (A.filter (fun a => a % 3 = r)).offDiag := by
    intro r
    ext p
    rw [hTeq]
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨h1, h2, hne⟩, heqr⟩, h1r⟩
      exact ⟨⟨h1, h1r⟩, ⟨h2, by omega⟩, hne⟩
    · rintro ⟨⟨h1, h1r⟩, ⟨h2, h2r⟩, hne⟩
      exact ⟨⟨⟨h1, h2, hne⟩, by omega⟩, h1r⟩
  -- Fiberwise counts: `|A| = c₀ + c₁ + c₂` and `|T| = ∑ cᵣ(cᵣ − 1)`.
  have hfib : A.card = ∑ r ∈ Finset.range 3, (A.filter (fun a => a % 3 = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
  have hTfib : T.card = ∑ r ∈ Finset.range 3, (T.filter (fun p => p.1 % 3 = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
  have hcount : (10 : ℕ) = ∑ r ∈ Finset.range 3,
      ((A.filter (fun a => a % 3 = r)).card * (A.filter (fun a => a % 3 = r)).card
        - (A.filter (fun a => a % 3 = r)).card) := by
    rw [← hTcard, hTfib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hfiber r, Finset.offDiag_card]
  -- Extract the two Diophantine constraints and refute them by finite case analysis.
  have hsum6 : (A.filter (fun a => a % 3 = 0)).card + (A.filter (fun a => a % 3 = 1)).card
      + (A.filter (fun a => a % 3 = 2)).card = 6 := by
    have h := hfib
    rw [hc6] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
    omega
  have hsum10 : ((A.filter (fun a => a % 3 = 0)).card * (A.filter (fun a => a % 3 = 0)).card
        - (A.filter (fun a => a % 3 = 0)).card)
      + ((A.filter (fun a => a % 3 = 1)).card * (A.filter (fun a => a % 3 = 1)).card
        - (A.filter (fun a => a % 3 = 1)).card)
      + ((A.filter (fun a => a % 3 = 2)).card * (A.filter (fun a => a % 3 = 2)).card
        - (A.filter (fun a => a % 3 = 2)).card) = 10 := by
    have h := hcount
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
    exact h.symm
  generalize hg0 : (A.filter (fun a => a % 3 = 0)).card = c0 at hsum6 hsum10
  generalize hg1 : (A.filter (fun a => a % 3 = 1)).card = c1 at hsum6 hsum10
  generalize hg2 : (A.filter (fun a => a % 3 = 2)).card = c2 at hsum6 hsum10
  have hb0 : c0 ≤ 6 := by omega
  have hb1 : c1 ≤ 6 := by omega
  have hb2 : c2 ≤ 6 := by omega
  interval_cases c0 <;> interval_cases c1 <;> interval_cases c2 <;> omega

/-- `h(15) = 5` — the second wall.  Counting is slack (`30 = 2·15`) and parity is
silent (`1 + ⋯ + 15 = 120` even); the mod-3 class count
(`no_sidon_card_six_range_sixteen`) rules out the perfect 6-mark ruler, and
`{0,1,4,9,11} ⊆ {0,…,15}` still attains `5`. -/
theorem sidonNumber_fifteen : sidonNumber 15 = 5 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_six_range_sixteen A hsub hA)
  · calc 5 = ({0, 1, 4, 9, 11} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 15 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_9_11

/-! ### `h(17) = ⋯ = h(20) = 6` — the six-element plateau, and `h(21) = 6` by parity

The first 6-element Sidon set to fit in an initial segment is the classical
**optimal 6-mark Golomb ruler** `{0, 1, 4, 10, 12, 17}` of span `17`, with the 15
distinct positive differences `{1,…,13} ∪ {16, 17}`.  On the upper side the counting
bound blocks a 7-element set throughout `17 ≤ N ≤ 20` (`7·6 = 42 > 2N`), so
`h(17) = ⋯ = h(20) = 6`.

At `N = 21` counting goes slack (`42 = 2·21`) — and the `h(10)` **parity argument
revives**: a 7-element Sidon set in `{0,…,21}` would have `C(7,2) = 21` distinct
positive differences exhausting `{1,…,21}` (a perfect 7-mark ruler), of sum
`1 + ⋯ + 21 = 231`, *odd*; but the sum of ordered positive differences is always even
(`S₁ − S₂ = 6·∑A − 2·S₂`).  So `h(21) = 6` as well.

**The one remaining gap below this point is `h(16)`** (truth: `5`): a 6-element Sidon
set in `{0,…,16}` has 15 distinct differences among `{1,…,16}`, *missing exactly one
value* `d` — a near-perfect ruler, where the exhaustion arguments above lose traction.
Parity forces `d` even; the mod-3 count forces `3 ∣ d` (with residue profile
`(3,2,1)`); so `d ∈ {6, 12}`, but finishing requires a finer invariant or a structured
search — supplied at the end of this file (`sidonNumber_sixteen`) by a span dichotomy
plus a kernel-checked search over the four interior elements. -/

private theorem isSidonSet_0_1_4_10_12_17 : IsSidonSet {0, 1, 4, 10, 12, 17} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- `h(17) = 6`: the optimal 6-mark Golomb ruler `{0,1,4,10,12,17}` fits exactly,
and `7·6 = 42 > 34 = 2·17` blocks a 7-element Sidon set. -/
theorem sidonNumber_seventeen : sidonNumber 17 = 6 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h7 : 7 ≤ m := hc
    nlinarith [hm, h7]
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 17 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

/-- `h(18) = 6`: `42 > 36 = 2·18` blocks seven, and the span-17 ruler still fits. -/
theorem sidonNumber_eighteen : sidonNumber 18 = 6 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h7 : 7 ≤ m := hc
    nlinarith [hm, h7]
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 18 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

/-- `h(19) = 6`: `42 > 38 = 2·19` blocks seven, and the span-17 ruler still fits. -/
theorem sidonNumber_nineteen : sidonNumber 19 = 6 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h7 : 7 ≤ m := hc
    nlinarith [hm, h7]
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 19 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

/-- `h(20) = 6`: `42 > 40 = 2·20` blocks seven, and the span-17 ruler still fits.
This closes the counting stretch: at `N = 21` the bound goes slack (`42 = 2·21`). -/
theorem sidonNumber_twenty : sidonNumber 20 = 6 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h7 : 7 ≤ m := hc
    nlinarith [hm, h7]
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 20 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

/-- **No 7-element Sidon set fits in `{0,…,21}`** — the perfect-ruler parity
obstruction, at the next slack point of the counting bound.  Such a set would have
`C(7,2) = 21` distinct positive differences exhausting `{1,…,21}`, of sum `231`
(odd), yet the sum of ordered positive differences is always even
(`S₁ − S₂ = 6·∑A − 2·S₂`).  The direct analogue of
`no_sidon_card_five_range_eleven` (`h(10)`), which works at `N = 10` and `N = 21`
because the triangular sums `55` and `231` are odd, but not at `N = 15` (`120`,
even) where the mod-3 count was needed instead. -/
theorem no_sidon_card_seven_range_twentytwo (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 22) (hA : IsSidonSet A) : A.card ≤ 6 := by
  by_contra hcard
  rw [not_le] at hcard
  have hup : A.card * A.card ≤ 42 + A.card := by
    have := sidon_card_sq_le 21 hsub hA; omega
  have hc7 : A.card = 7 := by
    have h7 : 7 ≤ A.card := hcard
    by_contra hne
    have h8 : 8 ≤ A.card := by omega
    have hmul : 8 * A.card ≤ A.card * A.card := Nat.mul_le_mul h8 (le_refl A.card)
    omega
  set P := A.offDiag.filter (fun p => 0 < diffMap p) with hP
  have hPsub : P ⊆ A.offDiag := Finset.filter_subset _ _
  have hfull : Set.InjOn diffMap ↑A.offDiag := diffMap_injOn hA
  have hinjP : Set.InjOn diffMap ↑P := hfull.mono (Finset.coe_subset.mpr hPsub)
  have hoffcard : A.offDiag.card = 42 := by rw [Finset.offDiag_card, hc7]
  have hmapsFull : ∀ p ∈ A.offDiag, diffMap p ∈ (Finset.Icc (-21 : ℤ) 21).erase 0 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hpne⟩ := hp
    have hb1 := hsub hp1; have hb2 := hsub hp2
    rw [Finset.mem_range] at hb1 hb2
    rw [Finset.mem_erase, Finset.mem_Icc]
    simp only [diffMap]
    exact ⟨fun h => hpne (by omega), by omega, by omega⟩
  have hcardErase : ((Finset.Icc (-21 : ℤ) 21).erase 0).card = 42 := by
    rw [Finset.card_erase_of_mem (by decide), Int.card_Icc]; decide
  have himageFull : A.offDiag.image diffMap = (Finset.Icc (-21 : ℤ) 21).erase 0 := by
    refine Finset.eq_of_subset_of_card_le (fun d hd => ?_) ?_
    · rw [Finset.mem_image] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      exact hmapsFull p hp
    · rw [Finset.card_image_of_injOn hfull, hoffcard]
      exact le_of_eq hcardErase
  have hPimg : P.image diffMap = Finset.Icc (1 : ℤ) 21 := by
    rw [hP, ← Finset.filter_image, himageFull]; decide
  have hsum231 : ∑ p ∈ P, diffMap p = 231 := by
    have hsi := Finset.sum_image (f := fun d : ℤ => d) hinjP
    rw [hPimg] at hsi
    rw [← hsi]; decide
  have hS1S2 : ∑ p ∈ P, (p.1 : ℤ) + ∑ p ∈ P, (p.2 : ℤ)
             = ∑ p ∈ A.offDiag, (p.1 : ℤ) := by
    have key : ∑ p ∈ A.offDiag, (p.1 : ℤ)
        = ∑ p ∈ P, (p.1 : ℤ)
          + ∑ p ∈ A.offDiag.filter (fun p => ¬ 0 < diffMap p), (p.1 : ℤ) := by
      rw [hP]
      exact (Finset.sum_filter_add_sum_filter_not A.offDiag
        (fun p => 0 < diffMap p) (fun p => (p.1 : ℤ))).symm
    have hswap : ∑ p ∈ A.offDiag.filter (fun p => ¬ 0 < diffMap p), (p.1 : ℤ)
               = ∑ p ∈ P, (p.2 : ℤ) := by
      rw [hP]
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_
        (fun a _ => Prod.swap_swap a) (fun a _ => Prod.swap_swap a) (fun a _ => rfl)
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := ha
        simp only [diffMap, not_lt] at hlt
        refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
        show 0 < (a.2 : ℤ) - (a.1 : ℤ); omega
      · intro a ha
        rw [Finset.mem_filter, Finset.mem_offDiag] at ha ⊢
        obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := ha
        simp only [diffMap] at hlt
        refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
        show ¬ 0 < (a.2 : ℤ) - (a.1 : ℤ); omega
    rw [key, hswap]
  have heven : Even (∑ p ∈ P, diffMap p) := by
    have hval : ∑ p ∈ P, diffMap p = ∑ p ∈ P, (p.1 : ℤ) - ∑ p ∈ P, (p.2 : ℤ) := by
      simp only [diffMap]; rw [Finset.sum_sub_distrib]
    have hoff := sum_offDiag_fst A
    rw [hc7] at hoff
    have h6 : ∑ p ∈ P, (p.1 : ℤ) + ∑ p ∈ P, (p.2 : ℤ) = 6 * ∑ a ∈ A, (a : ℤ) := by
      rw [hS1S2, hoff]; norm_num
    rw [hval]
    exact ⟨3 * ∑ a ∈ A, (a : ℤ) - ∑ p ∈ P, (p.2 : ℤ), by linarith [h6]⟩
  rw [hsum231] at heven
  exact absurd heven (by norm_num)

/-- `h(21) = 6` — the third wall, felled by the revived parity argument.  Counting
is slack (`42 = 2·21`) but a perfect 7-mark ruler would need difference-sum `231`,
odd (`no_sidon_card_seven_range_twentytwo`); the span-17 ruler still attains `6`. -/
theorem sidonNumber_twentyone : sidonNumber 21 = 6 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_seven_range_twentytwo A hsub hA)
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 21 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

/-! ### `h(16) = 5` — the near-perfect ruler, felled by a span dichotomy

A 6-element Sidon set in `{0,…,16}` would be a 6-mark Golomb ruler of length at most
`16` — but the optimal 6-mark ruler (`{0,1,4,10,12,17}`) has length `17`, so none
exists and `h(16) = 5`.  The counting, parity, and mod-3 invariants all go slack here
(the near-perfect ruler misses one difference `d ∈ {6,12}` and every residue count
stays feasible), so this is the first entry of the table that genuinely needs a
*search*.  We keep it small with a span dichotomy:

* **Span ≤ 15.**  Sliding the set down by its minimum (`IsSidonSet` is
  translation-invariant, and sliding preserves cardinality) lands it inside
  `{0,…,15}` — impossible by the mod-3 obstruction `no_sidon_card_six_range_sixteen`
  already proved for `h(15)`.
* **Span = 16.**  The minimum slides to `0` and the maximum to `16`, so after the
  slide the set is `{0, 16} ∪ B` with `B` one of the `C(15,4) = 1365` four-element
  subsets of `{1,…,15}`.  A kernel-checked `decide` (`no_sidon_extension_zero_sixteen`)
  rules out every one of them.  This stays well inside kernel range: `1365` subsets
  with `6⁴ = 1296` quadruple checks each.

The lower bound is the familiar 5-element witness `{0,1,4,9,11}`.  This closes the
last missing value below `22`: the table `h(0),…,h(21)` is now complete. -/

/-- Membership-bounded (hence decidable) form of the Sidon predicate, used for the
finite search below.  `IsSidonSet` itself quantifies over all of `ℕ` and so has no
`Decidable` instance; this form is equivalent (`sidonCheck_of_isSidonSet`). -/
private def SidonCheck (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

private instance (A : Finset ℕ) : Decidable (SidonCheck A) :=
  inferInstanceAs (Decidable (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d))

private theorem sidonCheck_of_isSidonSet {A : Finset ℕ} (hA : IsSidonSet A) :
    SidonCheck A :=
  fun a ha b hb c hc d hd hab hcd heq => hA a b c d ha hb hc hd hab hcd heq

set_option maxRecDepth 10000 in
/-- **The exhaustive kernel search**: no four interior elements `B ⊆ {1,…,15}` extend
the pinned endpoints `{0, 16}` to a 6-element Sidon set.  `1365` candidate subsets,
each checked against the bounded Sidon predicate; `decide +kernel` hands the whole
evaluation to the kernel's fast numeral arithmetic. -/
private theorem no_sidon_extension_zero_sixteen :
    ∀ B ∈ (Finset.Icc 1 15).powersetCard 4,
      ¬ SidonCheck (insert 0 (insert 16 B)) := by
  decide +kernel

/-- **No 6-element Sidon set fits in `{0,…,16}`** — equivalently, every 6-mark Golomb
ruler has length `≥ 17`.  Span dichotomy: after sliding the minimum to `0`, either the
set lies in `{0,…,15}` (killed by the `h(15)` mod-3 obstruction) or its maximum is
`16` and the four interior elements fall to the kernel search. -/
theorem no_sidon_card_six_range_seventeen (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 17) (hA : IsSidonSet A) : A.card ≤ 5 := by
  by_contra hcard
  rw [not_le] at hcard
  -- Counting caps the size at 6, so a violating set has exactly 6 elements.
  have hup : A.card * A.card ≤ 32 + A.card := by
    have := sidon_card_sq_le 16 hsub hA; omega
  have hc6 : A.card = 6 := by
    by_contra hne
    have h7 : 7 ≤ A.card := by omega
    have hmul : 7 * A.card ≤ A.card * A.card := Nat.mul_le_mul h7 (le_refl A.card)
    omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set m := A.min' hne with hm
  have hmle : ∀ x ∈ A, m ≤ x := fun x hx => A.min'_le x hx
  have hbound : ∀ x ∈ A, x ≤ 16 := fun x hx => by
    have := hsub hx; rw [Finset.mem_range] at this; omega
  -- Slide the set down by its minimum.
  set A' := A.image (fun x => x - m) with hA'
  have hinj : Set.InjOn (fun x => x - m) ↑A := by
    intro x hx y hy hxy
    have hx' := hmle x (Finset.mem_coe.mp hx)
    have hy' := hmle y (Finset.mem_coe.mp hy)
    have hxy' : x - m = y - m := hxy
    omega
  have hA'card : A'.card = 6 := by
    rw [hA', Finset.card_image_of_injOn hinj, hc6]
  have hA'sidon : IsSidonSet A' := by
    intro a b c d ha hb hc hd hab hcd heq
    rw [hA'] at ha hb hc hd
    simp only [Finset.mem_image] at ha hb hc hd
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hma := hmle a₀ ha₀; have hmb := hmle b₀ hb₀
    have hmc := hmle c₀ hc₀; have hmd := hmle d₀ hd₀
    obtain ⟨h1, h2⟩ := hA a₀ b₀ c₀ d₀ ha₀ hb₀ hc₀ hd₀ (by omega) (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  have hzero : (0 : ℕ) ∈ A' := by
    rw [hA']
    exact Finset.mem_image.mpr ⟨m, A.min'_mem hne, Nat.sub_self m⟩
  have hA'ne : A'.Nonempty := ⟨0, hzero⟩
  have hA'bound : ∀ x ∈ A', x ≤ 16 := by
    intro x hx
    rw [hA'] at hx
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Finset.mem_image.mp hx
    have hb := hbound x₀ hx₀
    have hx₀eq' : x₀ - m = x := hx₀eq
    omega
  rcases Nat.lt_or_ge (A'.max' hA'ne) 16 with hM | hM
  · -- Span ≤ 15: the slid set lives in {0,…,15}; the h(15) obstruction applies.
    have hsub' : A' ⊆ Finset.range 16 := fun x hx => by
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (A'.le_max' x hx) hM
    have := no_sidon_card_six_range_sixteen A' hsub' hA'sidon
    omega
  · -- Span = 16: both endpoints pinned; the four interior elements fall to `decide`.
    have h16 : (16 : ℕ) ∈ A' := by
      have hMle : A'.max' hA'ne ≤ 16 := hA'bound _ (A'.max'_mem hA'ne)
      have hMeq : A'.max' hA'ne = 16 := le_antisymm hMle hM
      rw [← hMeq]
      exact A'.max'_mem hA'ne
    set B := (A'.erase 0).erase 16 with hB
    have h16' : (16 : ℕ) ∈ A'.erase 0 := Finset.mem_erase.mpr ⟨by omega, h16⟩
    have hrecon : insert 0 (insert 16 B) = A' := by
      rw [hB, Finset.insert_erase h16', Finset.insert_erase hzero]
    have hBcard : B.card = 4 := by
      rw [hB, Finset.card_erase_of_mem h16', Finset.card_erase_of_mem hzero, hA'card]
    have hBsub : B ⊆ Finset.Icc 1 15 := by
      intro x hx
      rw [hB] at hx
      have hx16 := (Finset.mem_erase.mp hx).1
      have hx' := Finset.mem_of_mem_erase hx
      have hx0 := (Finset.mem_erase.mp hx').1
      have hxA := Finset.mem_of_mem_erase hx'
      have := hA'bound x hxA
      rw [Finset.mem_Icc]
      omega
    exact no_sidon_extension_zero_sixteen B
      (Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩)
      (by rw [hrecon]; exact sidonCheck_of_isSidonSet hA'sidon)

/-- `h(16) = 5` — the last missing value below `22`, completing the exact table
`h(0),…,h(21)`.  No 6-mark Golomb ruler has length `≤ 16`
(`no_sidon_card_six_range_seventeen`); the 5-element witness `{0,1,4,9,11}` persists. -/
theorem sidonNumber_sixteen : sidonNumber 16 = 5 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_six_range_seventeen A hsub hA)
  · calc 5 = ({0, 1, 4, 9, 11} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 16 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_9_11

/-! ### `h(22) = h(23) = h(24) = 6` and `h(25) = h(26) = h(27) = 7` — the table to 27

Past `h(21)` the parity wall is again silent (a 7-element Sidon set in `{0,…,N}` for
`N ∈ {22, 23, 24}` misses `N − 21` differences, and no small congruence pins them
down), but the span dichotomy of `h(16)` *scales*: sliding a hypothetical 7-element
Sidon set down by its minimum either reduces the span below the previous obstruction
or pins both endpoints `{0, N}`, leaving a kernel search over the
`C(N−1, 5)` five-element interior subsets — `20349`, `26334`, `33649` candidates for
`N = 22, 23, 24`.  The three searches chain: each span-reduction case appeals to the
obstruction proved just before it, with the merged `h(21)` parity theorem
(`no_sidon_card_seven_range_twentytwo`) anchoring the chain.

At `N = 25` the **optimal 7-mark Golomb ruler** `{0, 1, 4, 10, 18, 23, 25}` (span 25,
differences `{1,…,25} \ {11, 12, 16, 20}`) finally fits, and the counting bound blocks
an 8-element set throughout `25 ≤ N ≤ 27` (`8² = 64 > 2N + 8`), so
`h(25) = h(26) = h(27) = 7`.  The table `h(0), …, h(27)` is now complete; the next
wall is `N = 28`, where counting goes slack for eight (`64 = 2·28 + 8`) and the
8-mark ruler `{0, 1, 4, 9, 15, 22, 32, 34}` is still far away (span 34). -/

/-- Converse bridge to `sidonCheck_of_isSidonSet`: the bounded predicate implies the
unbounded one (any violating quadruple lies in `A` anyway), so explicit witnesses can
be certified by `decide` instead of an `|A|⁴`-case `rcases`/`omega` sweep. -/
private theorem isSidonSet_of_sidonCheck {A : Finset ℕ} (hA : SidonCheck A) :
    IsSidonSet A :=
  fun a b c d ha hb hc hd hab hcd heq => hA a ha b hb c hc d hd hab hcd heq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Kernel search for `h(22)`: no five interior elements `B ⊆ {1,…,21}` extend the
pinned endpoints `{0, 22}` to a 7-element Sidon set (`C(21,5) = 20349` candidates). -/
private theorem no_sidon_extension_zero_twentytwo :
    ∀ B ∈ (Finset.Icc 1 21).powersetCard 5,
      ¬ SidonCheck (insert 0 (insert 22 B)) := by
  decide +kernel

/-- **No 7-element Sidon set fits in `{0,…,22}`.**  Span dichotomy: after sliding the
minimum to `0`, either the set lies in `{0,…,21}` (killed by the `h(21)` parity
obstruction) or its span is exactly `22` and the five interior elements fall to the
kernel search. -/
theorem no_sidon_card_seven_range_twentythree (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 23) (hA : IsSidonSet A) : A.card ≤ 6 := by
  by_contra hcard
  rw [not_le] at hcard
  -- Counting caps the size at 7, so a violating set has exactly 7 elements.
  have hup : A.card * A.card ≤ 44 + A.card := by
    have := sidon_card_sq_le 22 hsub hA; omega
  have hc7 : A.card = 7 := by
    by_contra hne
    have h8 : 8 ≤ A.card := by omega
    have hmul : 8 * A.card ≤ A.card * A.card := Nat.mul_le_mul h8 (le_refl A.card)
    omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set m := A.min' hne with hm
  have hmle : ∀ x ∈ A, m ≤ x := fun x hx => A.min'_le x hx
  have hbound : ∀ x ∈ A, x ≤ 22 := fun x hx => by
    have := hsub hx; rw [Finset.mem_range] at this; omega
  -- Slide the set down by its minimum.
  set A' := A.image (fun x => x - m) with hA'
  have hinj : Set.InjOn (fun x => x - m) ↑A := by
    intro x hx y hy hxy
    have hx' := hmle x (Finset.mem_coe.mp hx)
    have hy' := hmle y (Finset.mem_coe.mp hy)
    have hxy' : x - m = y - m := hxy
    omega
  have hA'card : A'.card = 7 := by
    rw [hA', Finset.card_image_of_injOn hinj, hc7]
  have hA'sidon : IsSidonSet A' := by
    intro a b c d ha hb hc hd hab hcd heq
    rw [hA'] at ha hb hc hd
    simp only [Finset.mem_image] at ha hb hc hd
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hma := hmle a₀ ha₀; have hmb := hmle b₀ hb₀
    have hmc := hmle c₀ hc₀; have hmd := hmle d₀ hd₀
    obtain ⟨h1, h2⟩ := hA a₀ b₀ c₀ d₀ ha₀ hb₀ hc₀ hd₀ (by omega) (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  have hzero : (0 : ℕ) ∈ A' := by
    rw [hA']
    exact Finset.mem_image.mpr ⟨m, A.min'_mem hne, Nat.sub_self m⟩
  have hA'ne : A'.Nonempty := ⟨0, hzero⟩
  have hA'bound : ∀ x ∈ A', x ≤ 22 := by
    intro x hx
    rw [hA'] at hx
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Finset.mem_image.mp hx
    have hb := hbound x₀ hx₀
    have hx₀eq' : x₀ - m = x := hx₀eq
    omega
  rcases Nat.lt_or_ge (A'.max' hA'ne) 22 with hM | hM
  · -- Span ≤ 21: the slid set lives in {0,…,21}; the h(21) parity obstruction applies.
    have hsub' : A' ⊆ Finset.range 22 := fun x hx => by
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (A'.le_max' x hx) hM
    have := no_sidon_card_seven_range_twentytwo A' hsub' hA'sidon
    omega
  · -- Span = 22: both endpoints pinned; the five interior elements fall to `decide`.
    have h22 : (22 : ℕ) ∈ A' := by
      have hMle : A'.max' hA'ne ≤ 22 := hA'bound _ (A'.max'_mem hA'ne)
      have hMeq : A'.max' hA'ne = 22 := le_antisymm hMle hM
      rw [← hMeq]
      exact A'.max'_mem hA'ne
    set B := (A'.erase 0).erase 22 with hB
    have h22' : (22 : ℕ) ∈ A'.erase 0 := Finset.mem_erase.mpr ⟨by omega, h22⟩
    have hrecon : insert 0 (insert 22 B) = A' := by
      rw [hB, Finset.insert_erase h22', Finset.insert_erase hzero]
    have hBcard : B.card = 5 := by
      rw [hB, Finset.card_erase_of_mem h22', Finset.card_erase_of_mem hzero, hA'card]
    have hBsub : B ⊆ Finset.Icc 1 21 := by
      intro x hx
      rw [hB] at hx
      have hx22 := (Finset.mem_erase.mp hx).1
      have hx' := Finset.mem_of_mem_erase hx
      have hx0 := (Finset.mem_erase.mp hx').1
      have hxA := Finset.mem_of_mem_erase hx'
      have := hA'bound x hxA
      rw [Finset.mem_Icc]
      omega
    exact no_sidon_extension_zero_twentytwo B
      (Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩)
      (by rw [hrecon]; exact sidonCheck_of_isSidonSet hA'sidon)

/-- `h(22) = 6`: the span dichotomy scales past the parity wall, and the span-17
ruler `{0,1,4,10,12,17}` still gives the lower bound. -/
theorem sidonNumber_twentytwo : sidonNumber 22 = 6 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_seven_range_twentythree A hsub hA)
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 22 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Kernel search for `h(23)`: no five interior elements `B ⊆ {1,…,22}` extend the
pinned endpoints `{0, 23}` to a 7-element Sidon set (`C(22,5) = 26334` candidates). -/
private theorem no_sidon_extension_zero_twentythree :
    ∀ B ∈ (Finset.Icc 1 22).powersetCard 5,
      ¬ SidonCheck (insert 0 (insert 23 B)) := by
  decide +kernel

/-- **No 7-element Sidon set fits in `{0,…,23}`.**  Same dichotomy, chained onto the
`h(22)` obstruction. -/
theorem no_sidon_card_seven_range_twentyfour (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 24) (hA : IsSidonSet A) : A.card ≤ 6 := by
  by_contra hcard
  rw [not_le] at hcard
  have hup : A.card * A.card ≤ 46 + A.card := by
    have := sidon_card_sq_le 23 hsub hA; omega
  have hc7 : A.card = 7 := by
    by_contra hne
    have h8 : 8 ≤ A.card := by omega
    have hmul : 8 * A.card ≤ A.card * A.card := Nat.mul_le_mul h8 (le_refl A.card)
    omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set m := A.min' hne with hm
  have hmle : ∀ x ∈ A, m ≤ x := fun x hx => A.min'_le x hx
  have hbound : ∀ x ∈ A, x ≤ 23 := fun x hx => by
    have := hsub hx; rw [Finset.mem_range] at this; omega
  set A' := A.image (fun x => x - m) with hA'
  have hinj : Set.InjOn (fun x => x - m) ↑A := by
    intro x hx y hy hxy
    have hx' := hmle x (Finset.mem_coe.mp hx)
    have hy' := hmle y (Finset.mem_coe.mp hy)
    have hxy' : x - m = y - m := hxy
    omega
  have hA'card : A'.card = 7 := by
    rw [hA', Finset.card_image_of_injOn hinj, hc7]
  have hA'sidon : IsSidonSet A' := by
    intro a b c d ha hb hc hd hab hcd heq
    rw [hA'] at ha hb hc hd
    simp only [Finset.mem_image] at ha hb hc hd
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hma := hmle a₀ ha₀; have hmb := hmle b₀ hb₀
    have hmc := hmle c₀ hc₀; have hmd := hmle d₀ hd₀
    obtain ⟨h1, h2⟩ := hA a₀ b₀ c₀ d₀ ha₀ hb₀ hc₀ hd₀ (by omega) (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  have hzero : (0 : ℕ) ∈ A' := by
    rw [hA']
    exact Finset.mem_image.mpr ⟨m, A.min'_mem hne, Nat.sub_self m⟩
  have hA'ne : A'.Nonempty := ⟨0, hzero⟩
  have hA'bound : ∀ x ∈ A', x ≤ 23 := by
    intro x hx
    rw [hA'] at hx
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Finset.mem_image.mp hx
    have hb := hbound x₀ hx₀
    have hx₀eq' : x₀ - m = x := hx₀eq
    omega
  rcases Nat.lt_or_ge (A'.max' hA'ne) 23 with hM | hM
  · -- Span ≤ 22: the slid set lives in {0,…,22}; the h(22) obstruction applies.
    have hsub' : A' ⊆ Finset.range 23 := fun x hx => by
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (A'.le_max' x hx) hM
    have := no_sidon_card_seven_range_twentythree A' hsub' hA'sidon
    omega
  · -- Span = 23: both endpoints pinned; the five interior elements fall to `decide`.
    have h23 : (23 : ℕ) ∈ A' := by
      have hMle : A'.max' hA'ne ≤ 23 := hA'bound _ (A'.max'_mem hA'ne)
      have hMeq : A'.max' hA'ne = 23 := le_antisymm hMle hM
      rw [← hMeq]
      exact A'.max'_mem hA'ne
    set B := (A'.erase 0).erase 23 with hB
    have h23' : (23 : ℕ) ∈ A'.erase 0 := Finset.mem_erase.mpr ⟨by omega, h23⟩
    have hrecon : insert 0 (insert 23 B) = A' := by
      rw [hB, Finset.insert_erase h23', Finset.insert_erase hzero]
    have hBcard : B.card = 5 := by
      rw [hB, Finset.card_erase_of_mem h23', Finset.card_erase_of_mem hzero, hA'card]
    have hBsub : B ⊆ Finset.Icc 1 22 := by
      intro x hx
      rw [hB] at hx
      have hx23 := (Finset.mem_erase.mp hx).1
      have hx' := Finset.mem_of_mem_erase hx
      have hx0 := (Finset.mem_erase.mp hx').1
      have hxA := Finset.mem_of_mem_erase hx'
      have := hA'bound x hxA
      rw [Finset.mem_Icc]
      omega
    exact no_sidon_extension_zero_twentythree B
      (Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩)
      (by rw [hrecon]; exact sidonCheck_of_isSidonSet hA'sidon)

/-- `h(23) = 6`. -/
theorem sidonNumber_twentythree : sidonNumber 23 = 6 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_seven_range_twentyfour A hsub hA)
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 23 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Kernel search for `h(24)`: no five interior elements `B ⊆ {1,…,23}` extend the
pinned endpoints `{0, 24}` to a 7-element Sidon set (`C(23,5) = 33649` candidates). -/
private theorem no_sidon_extension_zero_twentyfour :
    ∀ B ∈ (Finset.Icc 1 23).powersetCard 5,
      ¬ SidonCheck (insert 0 (insert 24 B)) := by
  decide +kernel

/-- **No 7-element Sidon set fits in `{0,…,24}`.**  Same dichotomy, chained onto the
`h(23)` obstruction.  This is sharp: the 7-mark ruler `{0,1,4,10,18,23,25}` fits at
`N = 25`. -/
theorem no_sidon_card_seven_range_twentyfive (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 25) (hA : IsSidonSet A) : A.card ≤ 6 := by
  by_contra hcard
  rw [not_le] at hcard
  have hup : A.card * A.card ≤ 48 + A.card := by
    have := sidon_card_sq_le 24 hsub hA; omega
  have hc7 : A.card = 7 := by
    by_contra hne
    have h8 : 8 ≤ A.card := by omega
    have hmul : 8 * A.card ≤ A.card * A.card := Nat.mul_le_mul h8 (le_refl A.card)
    omega
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set m := A.min' hne with hm
  have hmle : ∀ x ∈ A, m ≤ x := fun x hx => A.min'_le x hx
  have hbound : ∀ x ∈ A, x ≤ 24 := fun x hx => by
    have := hsub hx; rw [Finset.mem_range] at this; omega
  set A' := A.image (fun x => x - m) with hA'
  have hinj : Set.InjOn (fun x => x - m) ↑A := by
    intro x hx y hy hxy
    have hx' := hmle x (Finset.mem_coe.mp hx)
    have hy' := hmle y (Finset.mem_coe.mp hy)
    have hxy' : x - m = y - m := hxy
    omega
  have hA'card : A'.card = 7 := by
    rw [hA', Finset.card_image_of_injOn hinj, hc7]
  have hA'sidon : IsSidonSet A' := by
    intro a b c d ha hb hc hd hab hcd heq
    rw [hA'] at ha hb hc hd
    simp only [Finset.mem_image] at ha hb hc hd
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    have hma := hmle a₀ ha₀; have hmb := hmle b₀ hb₀
    have hmc := hmle c₀ hc₀; have hmd := hmle d₀ hd₀
    obtain ⟨h1, h2⟩ := hA a₀ b₀ c₀ d₀ ha₀ hb₀ hc₀ hd₀ (by omega) (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  have hzero : (0 : ℕ) ∈ A' := by
    rw [hA']
    exact Finset.mem_image.mpr ⟨m, A.min'_mem hne, Nat.sub_self m⟩
  have hA'ne : A'.Nonempty := ⟨0, hzero⟩
  have hA'bound : ∀ x ∈ A', x ≤ 24 := by
    intro x hx
    rw [hA'] at hx
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Finset.mem_image.mp hx
    have hb := hbound x₀ hx₀
    have hx₀eq' : x₀ - m = x := hx₀eq
    omega
  rcases Nat.lt_or_ge (A'.max' hA'ne) 24 with hM | hM
  · -- Span ≤ 23: the slid set lives in {0,…,23}; the h(23) obstruction applies.
    have hsub' : A' ⊆ Finset.range 24 := fun x hx => by
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (A'.le_max' x hx) hM
    have := no_sidon_card_seven_range_twentyfour A' hsub' hA'sidon
    omega
  · -- Span = 24: both endpoints pinned; the five interior elements fall to `decide`.
    have h24 : (24 : ℕ) ∈ A' := by
      have hMle : A'.max' hA'ne ≤ 24 := hA'bound _ (A'.max'_mem hA'ne)
      have hMeq : A'.max' hA'ne = 24 := le_antisymm hMle hM
      rw [← hMeq]
      exact A'.max'_mem hA'ne
    set B := (A'.erase 0).erase 24 with hB
    have h24' : (24 : ℕ) ∈ A'.erase 0 := Finset.mem_erase.mpr ⟨by omega, h24⟩
    have hrecon : insert 0 (insert 24 B) = A' := by
      rw [hB, Finset.insert_erase h24', Finset.insert_erase hzero]
    have hBcard : B.card = 5 := by
      rw [hB, Finset.card_erase_of_mem h24', Finset.card_erase_of_mem hzero, hA'card]
    have hBsub : B ⊆ Finset.Icc 1 23 := by
      intro x hx
      rw [hB] at hx
      have hx24 := (Finset.mem_erase.mp hx).1
      have hx' := Finset.mem_of_mem_erase hx
      have hx0 := (Finset.mem_erase.mp hx').1
      have hxA := Finset.mem_of_mem_erase hx'
      have := hA'bound x hxA
      rw [Finset.mem_Icc]
      omega
    exact no_sidon_extension_zero_twentyfour B
      (Finset.mem_powersetCard.mpr ⟨hBsub, hBcard⟩)
      (by rw [hrecon]; exact sidonCheck_of_isSidonSet hA'sidon)

/-- `h(24) = 6`. -/
theorem sidonNumber_twentyfour : sidonNumber 24 = 6 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_seven_range_twentyfive A hsub hA)
  · calc 6 = ({0, 1, 4, 10, 12, 17} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 24 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_12_17

/-- The **optimal 7-mark Golomb ruler** `{0,1,4,10,18,23,25}` is a Sidon set — the
first 7-element Sidon set to fit in an initial segment (span `25`, sharp by
`no_sidon_card_seven_range_twentyfive`).  Certified through the `SidonCheck` bridge:
one `decide` replaces the `7⁴ = 2401`-case `rcases`/`omega` sweep the 6-element
witnesses needed. -/
private theorem isSidonSet_0_1_4_10_18_23_25 :
    IsSidonSet {0, 1, 4, 10, 18, 23, 25} :=
  isSidonSet_of_sidonCheck (by decide)

/-- `h(25) = 7`: the optimal 7-mark Golomb ruler fits exactly, and
`8² = 64 > 58 = 2·25 + 8` blocks an 8-element Sidon set. -/
theorem sidonNumber_twentyfive : sidonNumber 25 = 7 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h8 : 8 ≤ m := hc
    nlinarith [hm, h8]
  · calc 7 = ({0, 1, 4, 10, 18, 23, 25} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 25 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_18_23_25

/-- `h(26) = 7`: `64 > 60 = 2·26 + 8` blocks eight, and the span-25 ruler still fits. -/
theorem sidonNumber_twentysix : sidonNumber 26 = 7 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h8 : 8 ≤ m := hc
    nlinarith [hm, h8]
  · calc 7 = ({0, 1, 4, 10, 18, 23, 25} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 26 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_18_23_25

/-- `h(27) = 7`: `64 > 62 = 2·27 + 8` blocks eight, and the span-25 ruler still fits.
This closes the counting stretch: at `N = 28` the bound goes slack (`64 = 2·28 + 8`),
opening the next wall. -/
theorem sidonNumber_twentyseven : sidonNumber 27 = 7 := by
  refine le_antisymm (sidonNumber_le_of_sq fun m hm => ?_) ?_
  · by_contra hc; rw [not_le] at hc
    have h8 : 8 ≤ m := hc
    nlinarith [hm, h8]
  · calc 7 = ({0, 1, 4, 10, 18, 23, 25} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 27 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_18_23_25

/-! ### `h(28) = 7` — the third wall falls to a mod-4 class double count

At `N = 28` the counting bound goes slack against an 8-element set for the first
time (`8·7 = 56 = 2·28`), the `h(10)`/`h(21)` parity trick is silent (a perfect
8-mark ruler of span `28` has difference sum `1 + ⋯ + 28 = 406`, *even*), and the
`h(15)` mod-3 count is inconclusive (class sizes `{4,3,1}` satisfy it).  The
`h(16)`/`h(22..24)` span dichotomy would need a `C(27,6) ≈ 296k`-candidate kernel
search.  None of that is necessary: counting differences **mod 4** kills the
configuration outright, with no search at all.

An 8-element Sidon set in `{0,…,28}` has `C(8,2) = 28` distinct positive
differences inside `{1,…,28}`, hence *exhausting* it — a perfect 8-mark ruler is
forced automatically (no span dichotomy needed).  Among the `56` signed nonzero
differences `{±1,…,±28}` exactly `14` are `≡ 0 (mod 4)` and exactly `14` are
`≡ 2 (mod 4)`.  Writing `c₀,c₁,c₂,c₃` for the sizes of the residue classes of `A`
mod `4`:

* ordered pairs with `a − b ≡ 0 (mod 4)` are the same-class pairs:
  `∑ᵣ cᵣ(cᵣ − 1) = 14`, i.e. `∑ᵣ cᵣ² = 22`;
* ordered pairs with `a − b ≡ 2 (mod 4)` pair class `r` with class `r + 2`:
  `∑ᵣ cᵣ·c_{r+2 mod 4} = 2(c₀c₂ + c₁c₃) = 14`.

With `c₀ + c₁ + c₂ + c₃ = 8` the first constraint forces the multiset of class
sizes to be `{4,2,1,1}` or `{3,3,2,0}`, and for every arrangement of either,
`c₀c₂ + c₁c₃ ∈ {6, 9}` — never `7`.  Contradiction, so `h(28) = 7`. -/

/-- **No 8-element Sidon set fits in `{0,…,28}`** — the perfect-ruler mod-4 double
count.  Such a set would have `56` signed differences exhausting `{±1,…,±28}`,
hence exactly `14` ordered pairs with `a − b ≡ 0 (mod 4)` and exactly `14` with
`a − b ≡ 2 (mod 4)`; but with `c₀ + c₁ + c₂ + c₃ = 8` the class-size counts
`∑ cᵣ(cᵣ − 1) = 14` and `∑ cᵣ·c_{r+2 mod 4} = 14` are jointly unsatisfiable. -/
set_option maxHeartbeats 4000000 in
theorem no_sidon_card_eight_range_twentynine (A : Finset ℕ)
    (hsub : A ⊆ Finset.range 29) (hA : IsSidonSet A) : A.card ≤ 7 := by
  by_contra hcard
  rw [not_le] at hcard
  -- Counting caps the size at 8, so a violating set has exactly 8 elements.
  have hup : A.card * A.card ≤ 56 + A.card := by
    have := sidon_card_sq_le 28 hsub hA; omega
  have hc8 : A.card = 8 := by
    have h8 : 8 ≤ A.card := hcard
    by_contra hne
    have h9 : 9 ≤ A.card := by omega
    have hmul : 9 * A.card ≤ A.card * A.card := Nat.mul_le_mul h9 (le_refl A.card)
    omega
  have hfull : Set.InjOn diffMap ↑A.offDiag := diffMap_injOn hA
  have hoffcard : A.offDiag.card = 56 := by rw [Finset.offDiag_card, hc8]
  -- `diffMap` sends the off-diagonal onto the 56 nonzero integers of `[-28, 28]`.
  have hmapsFull : ∀ p ∈ A.offDiag, diffMap p ∈ (Finset.Icc (-28 : ℤ) 28).erase 0 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hpne⟩ := hp
    have hb1 := hsub hp1; have hb2 := hsub hp2
    rw [Finset.mem_range] at hb1 hb2
    rw [Finset.mem_erase, Finset.mem_Icc]
    simp only [diffMap]
    exact ⟨fun h => hpne (by omega), by omega, by omega⟩
  have hcardErase : ((Finset.Icc (-28 : ℤ) 28).erase 0).card = 56 := by
    rw [Finset.card_erase_of_mem (by decide), Int.card_Icc]; decide
  have himageFull : A.offDiag.image diffMap = (Finset.Icc (-28 : ℤ) 28).erase 0 := by
    refine Finset.eq_of_subset_of_card_le (fun d hd => ?_) ?_
    · rw [Finset.mem_image] at hd
      obtain ⟨p, hp, rfl⟩ := hd
      exact hmapsFull p hp
    · rw [Finset.card_image_of_injOn hfull, hoffcard]
      exact le_of_eq hcardErase
  -- `T0` = the off-diagonal pairs whose difference is divisible by `4`.
  set T0 := A.offDiag.filter (fun p => diffMap p % 4 = 0) with hT0
  have hT0sub : T0 ⊆ A.offDiag := Finset.filter_subset _ _
  have hinjT0 : Set.InjOn diffMap ↑T0 := hfull.mono (Finset.coe_subset.mpr hT0sub)
  -- Its image is the 14 nonzero multiples of 4 in `[-28, 28]`, so `|T0| = 14`.
  have hT0img : T0.image diffMap
      = ((Finset.Icc (-28 : ℤ) 28).erase 0).filter (fun d => d % 4 = 0) := by
    rw [hT0, ← Finset.filter_image (p := fun d : ℤ => d % 4 = 0), himageFull]
  have hT0card : T0.card = 14 := by
    rw [← Finset.card_image_of_injOn hinjT0, hT0img]
    decide
  -- `T2` = the off-diagonal pairs whose difference is `≡ 2 (mod 4)`.
  set T2 := A.offDiag.filter (fun p => diffMap p % 4 = 2) with hT2
  have hT2sub : T2 ⊆ A.offDiag := Finset.filter_subset _ _
  have hinjT2 : Set.InjOn diffMap ↑T2 := hfull.mono (Finset.coe_subset.mpr hT2sub)
  -- Its image is the 14 values `≡ 2 (mod 4)` in `[-28, 28]`, so `|T2| = 14`.
  have hT2img : T2.image diffMap
      = ((Finset.Icc (-28 : ℤ) 28).erase 0).filter (fun d => d % 4 = 2) := by
    rw [hT2, ← Finset.filter_image (p := fun d : ℤ => d % 4 = 2), himageFull]
  have hT2card : T2.card = 14 := by
    rw [← Finset.card_image_of_injOn hinjT2, hT2img]
    decide
  -- Structurally, `T0` is the set of same-residue pairs, fibered by the class.
  have hT0eq : T0 = A.offDiag.filter (fun p => p.1 % 4 = p.2 % 4) := by
    rw [hT0]
    refine Finset.filter_congr (fun p hp => ?_)
    simp only [diffMap]
    omega
  have hfiber0 : ∀ r : ℕ, T0.filter (fun p => p.1 % 4 = r)
      = (A.filter (fun a => a % 4 = r)).offDiag := by
    intro r
    ext p
    rw [hT0eq]
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨⟨h1, h2, hne⟩, heqr⟩, h1r⟩
      exact ⟨⟨h1, h1r⟩, ⟨h2, by omega⟩, hne⟩
    · rintro ⟨⟨h1, h1r⟩, ⟨h2, h2r⟩, hne⟩
      exact ⟨⟨⟨h1, h2, hne⟩, by omega⟩, h1r⟩
  -- `T2` fibers into full class products: first coordinate in class `r`, second
  -- in class `(r + 2) % 4` (distinct classes, so off-diagonality is automatic).
  have hfiber2 : ∀ r s : ℕ, s = (r + 2) % 4 → T2.filter (fun p => p.1 % 4 = r)
      = (A.filter (fun a => a % 4 = r)) ×ˢ (A.filter (fun a => a % 4 = s)) := by
    intro r s hs
    ext p
    rw [hT2]
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2, hne⟩, hd2⟩, h1r⟩
      refine ⟨⟨h1, h1r⟩, h2, ?_⟩
      simp only [diffMap] at hd2
      omega
    · rintro ⟨⟨h1, h1r⟩, h2, h2s⟩
      refine ⟨⟨⟨h1, h2, ?_⟩, ?_⟩, h1r⟩
      · omega
      · simp only [diffMap]
        omega
  -- Fiberwise counts: `|A| = ∑ cᵣ`, `|T0| = ∑ cᵣ(cᵣ − 1)`, `|T2| = ∑ cᵣ·c_{r+2 mod 4}`.
  have hfib : A.card = ∑ r ∈ Finset.range 4, (A.filter (fun a => a % 4 = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
  have hT0fib : T0.card = ∑ r ∈ Finset.range 4, (T0.filter (fun p => p.1 % 4 = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
  have hT2fib : T2.card = ∑ r ∈ Finset.range 4, (T2.filter (fun p => p.1 % 4 = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
  have hcount0 : (14 : ℕ) = ∑ r ∈ Finset.range 4,
      ((A.filter (fun a => a % 4 = r)).card * (A.filter (fun a => a % 4 = r)).card
        - (A.filter (fun a => a % 4 = r)).card) := by
    rw [← hT0card, hT0fib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hfiber0 r, Finset.offDiag_card]
  have hcount2 : (14 : ℕ) = ∑ r ∈ Finset.range 4,
      ((A.filter (fun a => a % 4 = r)).card
        * (A.filter (fun a => a % 4 = (r + 2) % 4)).card) := by
    rw [← hT2card, hT2fib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hfiber2 r ((r + 2) % 4) rfl, Finset.card_product]
  -- Extract the three Diophantine constraints and refute them by finite case analysis.
  have hsum8 : (A.filter (fun a => a % 4 = 0)).card + (A.filter (fun a => a % 4 = 1)).card
      + (A.filter (fun a => a % 4 = 2)).card + (A.filter (fun a => a % 4 = 3)).card = 8 := by
    have h := hfib
    rw [hc8] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
    omega
  have hsame : ((A.filter (fun a => a % 4 = 0)).card * (A.filter (fun a => a % 4 = 0)).card
        - (A.filter (fun a => a % 4 = 0)).card)
      + ((A.filter (fun a => a % 4 = 1)).card * (A.filter (fun a => a % 4 = 1)).card
        - (A.filter (fun a => a % 4 = 1)).card)
      + ((A.filter (fun a => a % 4 = 2)).card * (A.filter (fun a => a % 4 = 2)).card
        - (A.filter (fun a => a % 4 = 2)).card)
      + ((A.filter (fun a => a % 4 = 3)).card * (A.filter (fun a => a % 4 = 3)).card
        - (A.filter (fun a => a % 4 = 3)).card) = 14 := by
    have h := hcount0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
    exact h.symm
  have hcross : (A.filter (fun a => a % 4 = 0)).card * (A.filter (fun a => a % 4 = 2)).card
      + (A.filter (fun a => a % 4 = 1)).card * (A.filter (fun a => a % 4 = 3)).card
      + (A.filter (fun a => a % 4 = 2)).card * (A.filter (fun a => a % 4 = 0)).card
      + (A.filter (fun a => a % 4 = 3)).card * (A.filter (fun a => a % 4 = 1)).card = 14 := by
    have h := hcount2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.reduceAdd, Nat.reduceMod] at h
    exact h.symm
  generalize hg0 : (A.filter (fun a => a % 4 = 0)).card = c0 at hsum8 hsame hcross
  generalize hg1 : (A.filter (fun a => a % 4 = 1)).card = c1 at hsum8 hsame hcross
  generalize hg2 : (A.filter (fun a => a % 4 = 2)).card = c2 at hsum8 hsame hcross
  generalize hg3 : (A.filter (fun a => a % 4 = 3)).card = c3 at hsum8 hsame hcross
  have hb0 : c0 ≤ 8 := by omega
  have hb1 : c1 ≤ 8 := by omega
  have hb2 : c2 ≤ 8 := by omega
  have hb3 : c3 ≤ 8 := by omega
  interval_cases c0 <;> interval_cases c1 <;> interval_cases c2 <;>
    interval_cases c3 <;> omega

/-- `h(28) = 7` — the third wall.  Counting is slack (`56 = 2·28`), parity is silent
(`1 + ⋯ + 28 = 406` even), and mod-3 is inconclusive; the mod-4 class double count
(`no_sidon_card_eight_range_twentynine`) rules out the forced perfect 8-mark ruler,
and the span-25 optimal 7-mark Golomb ruler still attains `7`. -/
theorem sidonNumber_twentyeight : sidonNumber 28 = 7 := by
  refine le_antisymm ?_ ?_
  · exact sidonNumber_le_of_card
      (fun A hsub hA => no_sidon_card_eight_range_twentynine A hsub hA)
  · calc 7 = ({0, 1, 4, 10, 18, 23, 25} : Finset ℕ).card := by decide
      _ ≤ sidonNumber 28 := sidonNumber_ge_card (by decide) isSidonSet_0_1_4_10_18_23_25

/- ## The Erdős–Turán construction: a √N-order LOWER bound

Powers of two gave only `h(N) ≳ log₂ N`.  This section closes the polynomial
gap with the Erdős–Turán (1941) modular construction: for a prime `p`, the
`p` numbers

    `aᵢ = 2p·i + (i² mod p)`,   `i = 0, 1, …, p − 1`

form a Sidon set inside `{0, …, 2p² − 1}`, so `h(2p² − 1) ≥ p`.  Feeding in a
Bertrand prime `q ∈ (s, 2s]` for `s = ⌊√(N/8)⌋` yields `h(N) > ⌊√(N/8)⌋` for
all `N ≥ 32` — in real form `√N/4 ≤ h(N)`.  Together with the counting upper
bound `sidonNumber_le_real` this pins the Sidon number at the `√N` order:

    `√N/4  ≤  h(N)  ≤  √(2N) + 1`      (N ≥ 32),

a constant-factor bracket (ratio ≤ 4√2 + o(1)) on a $1000-problem quantity.

Why `aᵢ` is Sidon: in `aᵢ + aⱼ = aₖ + aₗ` the base-`2p` digits separate
(each remainder `i² mod p` is `< p`, so a sum of two is `< 2p`), giving
`i + j = k + l` in `ℕ` and `i² + j² ≡ k² + l² (mod p)`.  Hence in the field
`𝔽_p` the pairs `{i,j}` and `{k,l}` have the same sum and — since `2` is
invertible for odd `p` — the same product `ij = ((i+j)² − (i²+j²))/2`.  Two
pairs with equal sum and product are the root multisets of the same monic
quadratic, so `(k−i)(k−j) = k² − (i+j)k + ij = 0` in `𝔽_p`; a field has no
zero divisors, and `0 ≤ i,j,k,l < p` lifts the conclusion back to `ℕ`. -/

/-- The Erdős–Turán map `i ↦ 2p·i + (i² mod p)` behind the √N-order Sidon set. -/
private def etMap (p i : ℕ) : ℕ := 2 * p * i + i ^ 2 % p

/-- Dividing out the leading base-`2p` digit recovers the index: `etMap p i / 2p = i`. -/
private theorem etMap_div {p : ℕ} (hp : 0 < p) (i : ℕ) : etMap p i / (2 * p) = i := by
  unfold etMap
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by have := Nat.mod_lt (i ^ 2) hp; omega)]

/-- `etMap p` is injective (the quotient by `2p` recovers the index). -/
private theorem etMap_injOn {p : ℕ} (hp : 0 < p) :
    Set.InjOn (etMap p) ↑(Finset.range p) := by
  intro i _ j _ hij
  have h := congrArg (· / (2 * p)) hij
  simp only [etMap_div hp] at h
  exact h

/-- **Digit separation.**  If `etMap p i + etMap p j = etMap p k + etMap p l` then the
base-`2p` digits match separately: the index sums agree in `ℕ` and the residue sums
agree on the nose (each side is a sum of two remainders `< p`, hence `< 2p`). -/
private theorem etMap_add_eq {p : ℕ} (hp : 0 < p) {i j k l : ℕ}
    (heq : etMap p i + etMap p j = etMap p k + etMap p l) :
    i + j = k + l ∧ i ^ 2 % p + j ^ 2 % p = k ^ 2 % p + l ^ 2 % p := by
  have hri : i ^ 2 % p < p := Nat.mod_lt _ hp
  have hrj : j ^ 2 % p < p := Nat.mod_lt _ hp
  have hrk : k ^ 2 % p < p := Nat.mod_lt _ hp
  have hrl : l ^ 2 % p < p := Nat.mod_lt _ hp
  have h2p : 0 < 2 * p := by omega
  have h1 : 2 * p * (i + j) + (i ^ 2 % p + j ^ 2 % p)
      = 2 * p * (k + l) + (k ^ 2 % p + l ^ 2 % p) := by
    unfold etMap at heq
    rw [Nat.mul_add, Nat.mul_add]
    linarith [heq]
  have hsum : i + j = k + l := by
    have hd := congrArg (· / (2 * p)) h1
    simpa [Nat.mul_add_div h2p,
      Nat.div_eq_of_lt (show i ^ 2 % p + j ^ 2 % p < 2 * p by omega),
      Nat.div_eq_of_lt (show k ^ 2 % p + l ^ 2 % p < 2 * p by omega)] using hd
  refine ⟨hsum, ?_⟩
  rw [hsum] at h1
  exact Nat.add_left_cancel h1

/-- **Quadratic uniqueness over `𝔽_p`.**  For an odd prime `p` and `i,j,k,l < p`, if the
pairs `{i,j}` and `{k,l}` have the same sum (in `ℕ`) and the same sum of squares mod `p`,
they coincide as unordered pairs: sum and sum-of-squares determine the product (2 is
invertible), and sum and product determine a monic quadratic whose roots over a field
are unique. -/
private theorem pair_eq_of_sum_sq {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) {i j k l : ℕ}
    (hi : i < p) (hj : j < p) (hk : k < p) (hl : l < p)
    (hsum : i + j = k + l)
    (hsq : i ^ 2 % p + j ^ 2 % p = k ^ 2 % p + l ^ 2 % p) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZsum : (i : ZMod p) + (j : ZMod p) = (k : ZMod p) + (l : ZMod p) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hsum
  have hZsq : (i : ZMod p) ^ 2 + (j : ZMod p) ^ 2
      = (k : ZMod p) ^ 2 + (l : ZMod p) ^ 2 := by
    have h := congrArg (Nat.cast : ℕ → ZMod p) hsq
    push_cast [ZMod.natCast_mod] at h
    exact h
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hv := congrArg ZMod.val h2
    rw [ZMod.val_natCast_of_lt hp2, ZMod.val_zero] at hv
    exact two_ne_zero hv
  have hZprod : (i : ZMod p) * (j : ZMod p) = (k : ZMod p) * (l : ZMod p) := by
    have h2 : (2 : ZMod p) * ((i : ZMod p) * (j : ZMod p))
        = 2 * ((k : ZMod p) * (l : ZMod p)) := by
      linear_combination ((i : ZMod p) + (j : ZMod p) + (k : ZMod p) + (l : ZMod p)) * hZsum
        - hZsq
    exact mul_left_cancel₀ h2ne h2
  have hfact : ((k : ZMod p) - (i : ZMod p)) * ((k : ZMod p) - (j : ZMod p)) = 0 := by
    linear_combination (-(k : ZMod p)) * hZsum + hZprod
  have hlift : ∀ a b : ℕ, a < p → b < p → (a : ZMod p) = (b : ZMod p) → a = b := by
    intro a b ha hb hab
    have hv := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
  rcases mul_eq_zero.mp hfact with h | h
  · left
    have hki : k = i := hlift k i hk hi (sub_eq_zero.mp h)
    exact ⟨hki.symm, by omega⟩
  · right
    have hkj : k = j := hlift k j hk hj (sub_eq_zero.mp h)
    exact ⟨by omega, hkj.symm⟩

/-- **The Erdős–Turán set is a Sidon set** for every odd prime `p`. -/
theorem isSidonSet_erdosTuran {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    IsSidonSet ((Finset.range p).image (etMap p)) := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_image, Finset.mem_range] at ha hb hc hd
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨l, hl, rfl⟩ := hd
  obtain ⟨hsum, hsq⟩ := etMap_add_eq hp.pos heq
  rcases pair_eq_of_sum_sq hp hp2 hi hj hk hl hsum hsq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨le_antisymm hab hcd, le_antisymm hcd hab⟩

/-- The Erdős–Turán set has exactly `p` elements. -/
theorem erdosTuran_card {p : ℕ} (hp : 0 < p) :
    ((Finset.range p).image (etMap p)).card = p := by
  rw [Finset.card_image_of_injOn (etMap_injOn hp), Finset.card_range]

/-- The Erdős–Turán set lives inside `{0, …, 2p² − 1}`. -/
theorem erdosTuran_subset {p : ℕ} (hp : 0 < p) :
    (Finset.range p).image (etMap p) ⊆ Finset.range (2 * p ^ 2 - 1 + 1) := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  have hr : i ^ 2 % p < p := Nat.mod_lt _ hp
  have hstep : p * (2 * i + 1) ≤ p * (2 * p) := Nat.mul_le_mul (le_refl p) (by omega)
  have hpos : 0 < 2 * p ^ 2 := by positivity
  have h3 : 2 * p ^ 2 - 1 + 1 = 2 * p ^ 2 := Nat.succ_pred_eq_of_pos hpos
  rw [h3]
  have h1 : 2 * p * i + p = p * (2 * i + 1) := by ring
  have h2 : p * (2 * p) = 2 * p ^ 2 := by ring
  unfold etMap
  linarith [hr, hstep]

/-- **Prime lower bound**: `h(2p² − 1) ≥ p` for every odd prime `p` — the Erdős–Turán
Sidon set of size `p` fits in `{0, …, 2p² − 1}`. -/
theorem prime_le_sidonNumber {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    p ≤ sidonNumber (2 * p ^ 2 - 1) := by
  have h := sidonNumber_ge_card (erdosTuran_subset hp.pos) (isSidonSet_erdosTuran hp hp2)
  rwa [erdosTuran_card hp.pos] at h

/-- **The √N-order lower bound**: `h(N) > ⌊√(N/8)⌋` for `N ≥ 32`.  A Bertrand prime
`q ∈ (s, 2s]` for `s = ⌊√(N/8)⌋` satisfies `2q² − 1 ≤ 8s² − 1 ≤ N`, so the Erdős–Turán
set for `q` already fits in `{0, …, N}` and `h(N) ≥ q > s`.  This replaces the previous
logarithmic lower bound (`sidonNumber_two_pow_ge`) by one of the same √N order as the
counting upper bound. -/
theorem sidonNumber_gt_sqrt {N : ℕ} (hN : 32 ≤ N) :
    Nat.sqrt (N / 8) < sidonNumber N := by
  set s := Nat.sqrt (N / 8) with hs
  have hs2 : 2 ≤ s := by
    rw [hs]
    exact Nat.le_sqrt.mpr (by omega : 2 * 2 ≤ N / 8)
  obtain ⟨q, hq, hsq, hq2s⟩ := Nat.bertrand s (by omega)
  have hq2 : 2 < q := by omega
  have hssq : s * s ≤ N / 8 := by rw [hs]; exact Nat.sqrt_le (N / 8)
  have h8 : 8 * (N / 8) ≤ N := by omega
  have hsqle : q * q ≤ (2 * s) * (2 * s) := Nat.mul_le_mul hq2s hq2s
  have hqN : 2 * q ^ 2 ≤ N := by nlinarith [hsqle, hssq, h8]
  calc s < q := hsq
    _ ≤ sidonNumber (2 * q ^ 2 - 1) := prime_le_sidonNumber hq hq2
    _ ≤ sidonNumber N := sidonNumber_mono (le_trans (Nat.sub_le _ _) hqN)

/-- **Real form of the lower bound**: `√N / 4 ≤ h(N)` for `N ≥ 32`.  Together with
`sidonNumber_le_real` this brackets the Sidon number at the √N order:
`√N/4 ≤ h(N) ≤ √(2N) + 1`. -/
theorem sidonNumber_ge_real {N : ℕ} (hN : 32 ≤ N) :
    Real.sqrt N / 4 ≤ (sidonNumber N : ℝ) := by
  have hmain := sidonNumber_gt_sqrt hN
  set s := Nat.sqrt (N / 8) with hs
  have hlt : N / 8 < (s + 1) * (s + 1) := by
    rw [hs]
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (N / 8)
  have hdm : N < 8 * (N / 8) + 8 := by omega
  have h16 : (N : ℝ) ≤ (4 * ((s : ℝ) + 1)) ^ 2 := by
    have h1 : N ≤ 16 * ((s + 1) * (s + 1)) := by nlinarith [hlt, hdm]
    calc (N : ℝ) ≤ 16 * (((s : ℝ) + 1) * ((s : ℝ) + 1)) := by exact_mod_cast h1
      _ = (4 * ((s : ℝ) + 1)) ^ 2 := by ring
  have hsqrt : Real.sqrt N ≤ 4 * ((s : ℝ) + 1) := by
    rw [show 4 * ((s : ℝ) + 1) = Real.sqrt ((4 * ((s : ℝ) + 1)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt h16
  have hcard : (s : ℝ) + 1 ≤ (sidonNumber N : ℝ) := by exact_mod_cast hmain
  linarith

/-- **Two-sided √N bracket** on the Sidon number: for `N ≥ 32`,
`√N/4 ≤ h(N) ≤ √(2N) + 1`.  The upper and lower bounds differ by a factor
`≤ 4√2 + o(1)`; sharpening the constants (Lindström/BFR upper `√N + N^{1/4} + 1`,
Singer lower `(1−o(1))√N`) and the $1000 `N^ε`-error conjecture remain open. -/
theorem sidonNumber_sqrt_bracket {N : ℕ} (hN : 32 ≤ N) :
    Real.sqrt N / 4 ≤ (sidonNumber N : ℝ) ∧ (sidonNumber N : ℝ) ≤ Real.sqrt (2 * N) + 1 :=
  ⟨sidonNumber_ge_real hN, sidonNumber_le_real N⟩

/- ### The reduction layer: ε-monotone bounds and the shape of the conjecture

`Erdos30Problem.lean` defines the upper-bound family `RequiredUpperBound ε`
(`h(N) ≤ √N + C·N^ε` for all `N ≥ 1`) and states the $1000 conjecture
`Erdos30Conjecture` (`|h(N) − √N| ≤ C·N^ε` eventually, for every `ε > 0`),
but leaves the reduction argument as a comment sketch.  This section
formalizes that layer:

* `requiredUpperBound_mono` / `requiredLowerBound_mono` — a bound with error
  exponent `ε₀` propagates to every exponent `ε ≥ ε₀` (for `N ≥ 1` we have
  `N^{ε₀} ≤ N^ε`), so a single sub-`1/4` improvement upgrades all larger
  exponents at once.
* `RequiredLowerBound ε` — the matching lower-bound family
  (`√N − C·N^ε ≤ h(N)`), the Singer side of the conjecture.
* `erdos30ConjectureAt_of_bounds` — at any single `ε`, the upper and lower
  families combine into the conjecture's two-sided eventual bound
  `Erdos30ConjectureAt ε`; `erdos30Conjecture_of_bounds` assembles the full
  conjecture from the two families over all `ε > 0`.
* `erdos30Conjecture_of_stronger` — the `O(1)` conjecture implies the `N^ε`
  conjecture.
* `requiredUpperBound_half` / `erdos30ConjectureAt_half` — the proved bracket
  `√N/4 ≤ h(N) ≤ √(2N) + 1` settles the `ε = 1/2` instance unconditionally
  (`C = √2` on the upper side; the lower side is trivial at `ε = 1/2` since
  `√N − N^{1/2} = 0`).  The open content of the conjecture thus lives
  strictly below `ε = 1/2` — and below `1/4` after Erdős–Turán (1941). -/

/-- The conjecture's two-sided eventual bound at a single exponent `ε`:
there are `C > 0` and `N₀` with `|h(N) − √N| ≤ C·N^ε` for all `N ≥ N₀`.
`Erdos30Conjecture` is definitionally `∀ ε > 0, Erdos30ConjectureAt ε`
(see `erdos30Conjecture_iff_forall`). -/
def Erdos30ConjectureAt (ε : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |(sidonNumber N : ℝ) - Real.sqrt N| ≤ C * N ^ ε

/-- The `N^ε` conjecture is exactly the family of single-exponent bounds. -/
theorem erdos30Conjecture_iff_forall :
    Erdos30Conjecture ↔ ∀ ε : ℝ, ε > 0 → Erdos30ConjectureAt ε :=
  Iff.rfl

/-- The matching lower-bound family: `√N − C·N^ε ≤ h(N)` for all `N ≥ 1`.
This is the (Singer) lower side of the conjecture, mirroring
`RequiredUpperBound`; Singer's projective-plane construction is expected to
realize it for every `ε > 0`, but only `ε = 1/2` is formalized here
(trivially — see `erdos30ConjectureAt_half`). -/
def RequiredLowerBound (ε : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
    Real.sqrt N - C * (N : ℝ) ^ ε ≤ (sidonNumber N : ℝ)

/-- Error-exponent monotonicity for the upper family: since `N^{ε₀} ≤ N^ε`
for `N ≥ 1` and `ε₀ ≤ ε`, a `√N + C·N^{ε₀}` upper bound propagates verbatim
to every larger exponent.  A single sub-`1/4` improvement therefore settles
the whole range above its exponent. -/
theorem requiredUpperBound_mono {ε₀ ε : ℝ} (hε : ε₀ ≤ ε)
    (h : RequiredUpperBound ε₀) : RequiredUpperBound ε := by
  obtain ⟨C, hC, hbd⟩ := h
  refine ⟨C, hC, fun N hN => ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ ε₀ ≤ (N : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le h1 hε
  have h2 : C * (N : ℝ) ^ ε₀ ≤ C * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_left hpow hC.le
  have h3 := hbd N hN
  linarith

/-- Error-exponent monotonicity for the lower family. -/
theorem requiredLowerBound_mono {ε₀ ε : ℝ} (hε : ε₀ ≤ ε)
    (h : RequiredLowerBound ε₀) : RequiredLowerBound ε := by
  obtain ⟨C, hC, hbd⟩ := h
  refine ⟨C, hC, fun N hN => ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ ε₀ ≤ (N : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le h1 hε
  have h2 : C * (N : ℝ) ^ ε₀ ≤ C * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_left hpow hC.le
  have h3 := hbd N hN
  linarith

/-- Assembly at a single exponent: an upper bound `h(N) ≤ √N + C₁·N^ε` and a
lower bound `√N − C₂·N^ε ≤ h(N)` combine into the two-sided bound
`|h(N) − √N| ≤ max C₁ C₂ · N^ε`. -/
theorem erdos30ConjectureAt_of_bounds {ε : ℝ}
    (hub : RequiredUpperBound ε) (hlb : RequiredLowerBound ε) :
    Erdos30ConjectureAt ε := by
  obtain ⟨C₁, hC₁, h₁⟩ := hub
  obtain ⟨C₂, hC₂, h₂⟩ := hlb
  refine ⟨max C₁ C₂, lt_max_iff.mpr (Or.inl hC₁), 1, fun N hN => ?_⟩
  have hpow : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
  have hm1 : C₁ * (N : ℝ) ^ ε ≤ max C₁ C₂ * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  have hm2 : C₂ * (N : ℝ) ^ ε ≤ max C₁ C₂ * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hpow
  rw [abs_sub_le_iff]
  exact ⟨by linarith [h₁ N hN], by linarith [h₂ N hN]⟩

/-- **The reduction theorem**: the full `N^ε` conjecture follows from the two
`ε`-families of one-sided bounds.  Combined with the monotonicity lemmas this
is the precise sense in which the conjecture reduces to small-`ε` one-sided
improvements — the upper family below `1/4` (open since Erdős–Turán 1941) and
the lower family below the Singer error exponent. -/
theorem erdos30Conjecture_of_bounds
    (hub : ∀ ε : ℝ, ε > 0 → RequiredUpperBound ε)
    (hlb : ∀ ε : ℝ, ε > 0 → RequiredLowerBound ε) :
    Erdos30Conjecture :=
  fun ε hε => erdos30ConjectureAt_of_bounds (hub ε hε) (hlb ε hε)

/-- The stronger `h(N) = √N + O(1)` conjecture implies the `N^ε` conjecture:
a constant error is dominated by `C·N^ε` as soon as `N ≥ 1` (where
`N^ε ≥ 1`). -/
theorem erdos30Conjecture_of_stronger (h : StrongerConjecture) :
    Erdos30Conjecture := by
  obtain ⟨C, hC, hbd⟩ := h
  intro ε hε
  refine ⟨C, hC, 1, fun N hN => ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ ε := by
    calc (1 : ℝ) = (N : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le h1 hε.le
  have h2 : C ≤ C * (N : ℝ) ^ ε := le_mul_of_one_le_right hC.le hpow
  have h3 := hbd N
  linarith

/-- The `ε = 1/2` instance of the upper family holds unconditionally, with
`C = √2`: from the counting bound `h(N) ≤ √(2N) + 1 = √2·√N + 1` and
`1 ≤ √N` (for `N ≥ 1`) we get `h(N) ≤ √N + √2·N^{1/2}`. -/
theorem requiredUpperBound_half : RequiredUpperBound (1 / 2) := by
  refine ⟨Real.sqrt 2, Real.sqrt_pos.mpr (by norm_num), fun N hN => ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt h1
  have hrp : (N : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt N := (Real.sqrt_eq_rpow _).symm
  have hub := sidonNumber_le_real N
  have h2N : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N :=
    Real.sqrt_mul (by norm_num) _
  rw [hrp]
  rw [h2N] at hub
  linarith

/-- The `ε = 1/2` instance of the conjecture's two-sided bound is settled
unconditionally by the proved bracket: `|h(N) − √N| ≤ √2·N^{1/2}` for
`N ≥ 1`.  The lower side is trivial at this exponent (`√N − N^{1/2} = 0`),
so the genuinely open content of `Erdos30Conjecture` lives strictly below
`ε = 1/2`. -/
theorem erdos30ConjectureAt_half : Erdos30ConjectureAt (1 / 2) := by
  refine erdos30ConjectureAt_of_bounds requiredUpperBound_half
    ⟨1, one_pos, fun N hN => ?_⟩
  have hrp : (N : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt N := (Real.sqrt_eq_rpow _).symm
  rw [hrp, one_mul, sub_self]
  exact Nat.cast_nonneg _

end Erdos30
