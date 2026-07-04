/-
  Schnirelmann's covering lemma (toward the additive-basis theorem).

  This file develops the first missing piece flagged in Mathlib's
  `Mathlib/Combinatorics/Schnirelmann.lean` TODO list:

    * "Show that if the sum of two densities is at least one, the sumset
       covers the positive naturals."

  formalized here as `sumset_covers_of_density_add_ge_one`.

  This is the *covering* step of Schnirelmann's theorem. Fully discharging the
  `schnirelmann_basis_theorem` axiom in `WeakGoldbach.lean` additionally
  requires Schnirelmann's *inequality* (`σ(A ⊕ B) ≥ σA + σB − σA·σB`) to boost
  the density of iterated sumsets above `1/2`; that step is the remaining gap
  (see the note at the bottom of this file).

  The proof of the covering lemma is the classical pigeonhole argument: for a
  target `n`, the `A`-elements of `[0,n]` and the reflected `B`-elements
  `{x : n - x ∈ B}` of `[0,n]` each have cardinality `≥ σ·n + 1`; if they were
  disjoint their union would exceed `[0,n]`, contradicting `σA + σB ≥ 1`. Hence
  they meet, yielding `a ∈ A`, `b ∈ B` with `a + b = n`.
-/
import Mathlib

open Finset

namespace SchnirelmannBasis

variable {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

/-- The number of `A`-elements in `{0, 1, …, n}` is at least `σ(A)·n + 1`
    when `0 ∈ A`: the `+1` accounts for `0`, which the density infimum (taken
    over `Ioc 0 n`) does not see. -/
lemma card_Icc_filter_ge (hA0 : 0 ∈ A) (n : ℕ) :
    schnirelmannDensity A * n + 1 ≤ (#{a ∈ Icc 0 n | a ∈ A} : ℝ) := by
  have h0not : (0 : ℕ) ∉ {a ∈ Ioc 0 n | a ∈ A} := by simp
  have hsub : insert 0 {a ∈ Ioc 0 n | a ∈ A} ⊆ {a ∈ Icc 0 n | a ∈ A} := by
    intro x hx
    simp only [mem_insert, mem_filter, mem_Ioc, mem_Icc] at hx ⊢
    rcases hx with rfl | ⟨⟨_, h2⟩, h3⟩
    · exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, hA0⟩
    · exact ⟨⟨Nat.zero_le _, h2⟩, h3⟩
  have hcard : #{a ∈ Ioc 0 n | a ∈ A} + 1 ≤ #{a ∈ Icc 0 n | a ∈ A} := by
    have := card_le_card hsub
    rwa [card_insert_of_notMem h0not] at this
  have hdens : schnirelmannDensity A * n ≤ (#{a ∈ Ioc 0 n | a ∈ A} : ℝ) :=
    schnirelmannDensity_mul_le_card_filter
  have hcast : (#{a ∈ Ioc 0 n | a ∈ A} : ℝ) + 1 ≤ (#{a ∈ Icc 0 n | a ∈ A} : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The reflected count: the number of `x ∈ {0, …, n}` with `n - x ∈ B` is at
    least `σ(B)·n + 1` when `0 ∈ B`. The reflection `x ↦ n - x` sends the
    `B`-elements of `[1,n]` injectively into this set, and `x = n` (giving
    `n - n = 0 ∈ B`) supplies the extra `+1`. -/
lemma card_reflect_filter (hB0 : 0 ∈ B) (n : ℕ) :
    schnirelmannDensity B * n + 1 ≤ (#{x ∈ Icc 0 n | (n - x) ∈ B} : ℝ) := by
  set s : Finset ℕ := {b ∈ Ioc 0 n | b ∈ B} with hs
  set t : Finset ℕ := {x ∈ Icc 0 n | (n - x) ∈ B} with ht
  have hn_t : n ∈ t := by
    simp only [ht, mem_filter, mem_Icc, Nat.sub_self]
    exact ⟨⟨Nat.zero_le _, le_refl _⟩, hB0⟩
  have himg : s.image (fun b => n - b) ⊆ t := by
    intro y hy
    simp only [mem_image, hs, mem_filter, mem_Ioc] at hy
    obtain ⟨b, ⟨⟨_, hbn⟩, hbB⟩, rfl⟩ := hy
    simp only [ht, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, Nat.sub_le _ _⟩, by rwa [Nat.sub_sub_self hbn]⟩
  have hninimg : n ∉ s.image (fun b => n - b) := by
    simp only [mem_image, hs, mem_filter, mem_Ioc, not_exists]
    rintro b ⟨⟨hb0, hbn⟩, _⟩
    omega
  have hinj : Set.InjOn (fun b => n - b) s := by
    intro a ha b hb hab
    simp only [hs, coe_filter, Set.mem_setOf_eq, mem_Ioc] at ha hb
    simp only at hab
    omega
  have hcardimg : (s.image (fun b => n - b)).card = s.card := card_image_of_injOn hinj
  have hins : insert n (s.image (fun b => n - b)) ⊆ t := by
    rw [insert_subset_iff]; exact ⟨hn_t, himg⟩
  have hcard : s.card + 1 ≤ t.card := by
    have := card_le_card hins
    rwa [card_insert_of_notMem hninimg, hcardimg] at this
  have hdens : schnirelmannDensity B * n ≤ (s.card : ℝ) :=
    schnirelmannDensity_mul_le_card_filter
  have hcast : (s.card : ℝ) + 1 ≤ (t.card : ℝ) := by exact_mod_cast hcard
  linarith

/-- **Schnirelmann's covering lemma.** If `0 ∈ A`, `0 ∈ B`, and the Schnirelmann
    densities satisfy `σ(A) + σ(B) ≥ 1`, then every natural number `n` is a sum
    `a + b` with `a ∈ A` and `b ∈ B`.

    This is the item "if the sum of two densities is at least one, the sumset
    covers the positive naturals" from the Mathlib `Schnirelmann.lean` TODO. -/
theorem sumset_covers_of_density_add_ge_one
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (h : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) (n : ℕ) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = n := by
  set SA : Finset ℕ := {a ∈ Icc 0 n | a ∈ A} with hSA_def
  set TB : Finset ℕ := {x ∈ Icc 0 n | (n - x) ∈ B} with hTB_def
  by_cases hdisj : Disjoint SA TB
  · exfalso
    have hunion : SA ∪ TB ⊆ Icc 0 n :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    have hcardun : SA.card + TB.card ≤ (Icc 0 n).card := by
      rw [← card_union_of_disjoint hdisj]
      exact card_le_card hunion
    have hIcc : (Icc 0 n).card = n + 1 := by rw [Nat.card_Icc]; omega
    have hSA : schnirelmannDensity A * n + 1 ≤ (SA.card : ℝ) := card_Icc_filter_ge hA0 n
    have hTB : schnirelmannDensity B * n + 1 ≤ (TB.card : ℝ) := card_reflect_filter hB0 n
    have hcast : (SA.card : ℝ) + (TB.card : ℝ) ≤ (n : ℝ) + 1 := by
      have hnat : SA.card + TB.card ≤ n + 1 := by rw [hIcc] at hcardun; exact hcardun
      have : ((SA.card + TB.card : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this; linarith
    have hge1 : (n : ℝ) ≤ schnirelmannDensity A * n + schnirelmannDensity B * n := by
      have h2 := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ (n : ℝ))
      rw [one_mul, add_mul] at h2
      exact h2
    linarith
  · rw [Finset.not_disjoint_iff] at hdisj
    obtain ⟨x, hxSA, hxTB⟩ := hdisj
    simp only [hSA_def, mem_filter, mem_Icc] at hxSA
    simp only [hTB_def, mem_filter, mem_Icc] at hxTB
    obtain ⟨⟨_, hxn⟩, hxA⟩ := hxSA
    obtain ⟨_, hnxB⟩ := hxTB
    exact ⟨x, hxA, n - x, hnxB, by omega⟩

/-- If `0 ∈ A` and the Schnirelmann density of `A` is at least `1/2`, then `A`
    is an additive basis of order `2`: every natural number is a sum of two
    elements of `A`. Immediate from the covering lemma with `B := A`. -/
theorem basis_order_two_of_density_ge_half
    (hA0 : 0 ∈ A) (h : 1 / 2 ≤ schnirelmannDensity A) (n : ℕ) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = n :=
  sumset_covers_of_density_add_ge_one hA0 hA0 (by linarith) n

/-- **Terminal step of Schnirelmann's theorem, in additive-basis form.** If
    `0 ∈ A` and `σ(A) ≥ 1/2`, then `A` is an additive basis of order `2` in the
    exact `Multiset` shape used by `WeakGoldbach.IsAdditiveBasis`: every `n` is
    the sum of a multiset of `≤ 2` elements of `A`.

    Where `basis_order_two_of_density_ge_half` produces a bare pair `a + b = n`,
    this repackages it as the multiset witness `{a, b}` that
    `schnirelmann_basis_theorem` requires as its conclusion. It is the *final*
    link of the density-boosting chain: once an iterated sumset `h·A` has been
    shown to have density `> 1/2` (via Schnirelmann's inequality — the one
    remaining gap), this lemma discharges the basis property for `h·A`, hence
    for `A` at order `2h`. -/
theorem isAdditiveBasis_two_of_density_ge_half
    (hA0 : 0 ∈ A) (h : 1 / 2 ≤ schnirelmannDensity A) (n : ℕ) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ 2 ∧ S.sum = n := by
  obtain ⟨a, ha, b, hb, hab⟩ := basis_order_two_of_density_ge_half hA0 h n
  refine ⟨{a, b}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]
    omega
  · simpa [Multiset.insert_eq_cons, Multiset.sum_cons] using hab

/-- **Convergence input for the density-boosting iteration.** If `σ(A) > 0`
    then the "deficiency" `1 − σ(A)` is `< 1`, so it decays geometrically and
    some finite power drops below `1/2`: `∃ h, (1 − σ(A))^h < 1/2`.

    This is the analytic half of the iteration. Schnirelmann's inequality gives
    `1 − σ(h·A) ≤ (1 − σ(A))^h` (the outstanding combinatorial gap); picking the
    `h` supplied here then yields `σ(h·A) > 1/2`, at which point
    `isAdditiveBasis_two_of_density_ge_half` closes the argument. Together these
    two lemmas reduce `schnirelmann_basis_theorem` to exactly the sumset
    inequality plus the bookkeeping "an element of `h·A` is a sum of `≤ h`
    elements of `A`". -/
theorem exists_pow_deficiency_lt_half
    (hpos : 0 < schnirelmannDensity A) :
    ∃ h : ℕ, (1 - schnirelmannDensity A) ^ h < 1 / 2 :=
  exists_pow_lt_of_lt_one (by norm_num) (by linarith)

/-
  ── Iteration bookkeeping: `h`-fold sum-sets and basis composition ────────────

  The density-boosting iteration of Schnirelmann's theorem produces the `h`-fold
  sum-set `h · A` and needs the bookkeeping that an element of `h · A` is a sum
  of at most `h` elements of `A`, and that composing two such representations
  gives a sum of at most `2h` elements. The lemmas below discharge that
  bookkeeping *completely* (0 sorry / 0 axiom), leaving Schnirelmann's inequality
  as the *sole* remaining gap toward `schnirelmann_basis_theorem`.
-/

/-- `IsSumOfAtMost A h n`: `n` is a sum of at most `h` elements of `A` (with
    repetition). This is `WeakGoldbach.IsAdditiveBasis A h` unfolded at a single
    point `n`, using the identical `Multiset` shape. -/
def IsSumOfAtMost (A : Set ℕ) (h n : ℕ) : Prop :=
  ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = n

/-- `0` is a sum of at most `h` elements of `A` for every `h`: the empty
    multiset works (`0` summands, empty sum). No hypothesis `0 ∈ A` is needed. -/
theorem zero_isSumOfAtMost (A : Set ℕ) (h : ℕ) : IsSumOfAtMost A h 0 :=
  ⟨0, by simp, by simp, by simp⟩

/-- Relax the summand budget: a sum of at most `h` elements is also a sum of at
    most `h'` elements when `h ≤ h'`. -/
theorem IsSumOfAtMost.mono {A : Set ℕ} {h h' n : ℕ}
    (hn : IsSumOfAtMost A h n) (hh : h ≤ h') : IsSumOfAtMost A h' n := by
  obtain ⟨S, hS, hSc, hSs⟩ := hn
  exact ⟨S, hS, le_trans hSc hh, hSs⟩

/-- **Composition.** If `m` is a sum of at most `h₁` elements of `A` and `p` is a
    sum of at most `h₂` elements of `A`, then `m + p` is a sum of at most
    `h₁ + h₂` elements of `A`: concatenate the two witnessing multisets. -/
theorem IsSumOfAtMost.add {A : Set ℕ} {h₁ h₂ m p : ℕ}
    (hm : IsSumOfAtMost A h₁ m) (hp : IsSumOfAtMost A h₂ p) :
    IsSumOfAtMost A (h₁ + h₂) (m + p) := by
  obtain ⟨S, hS, hSc, hSs⟩ := hm
  obtain ⟨T, hT, hTc, hTs⟩ := hp
  refine ⟨S + T, ?_, ?_, ?_⟩
  · intro x hx
    rw [Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact hS x hx
    · exact hT x hx
  · rw [Multiset.card_add]; omega
  · rw [Multiset.sum_add, hSs, hTs]

/-- The `h`-fold sum-set of `A`: the set of naturals expressible as a sum of at
    most `h` elements of `A`. Always contains `0` (see `zero_mem_sumsetPow`),
    which is exactly the `0 ∈ ·` hypothesis the covering lemma needs. -/
def sumsetPow (A : Set ℕ) (h : ℕ) : Set ℕ := {n | IsSumOfAtMost A h n}

@[simp] theorem mem_sumsetPow {A : Set ℕ} {h n : ℕ} :
    n ∈ sumsetPow A h ↔ IsSumOfAtMost A h n := Iff.rfl

/-- `0` lies in every `h`-fold sum-set of `A`. -/
theorem zero_mem_sumsetPow (A : Set ℕ) (h : ℕ) : 0 ∈ sumsetPow A h :=
  zero_isSumOfAtMost A h

/-- The sum of a multiset all of whose entries lie in the `h`-fold sum-set
    `sumsetPow A h` is itself a sum of at most `S.card · h` elements of `A`.
    Proof by multiset induction, using `IsSumOfAtMost.add` at each `cons`. -/
theorem isSumOfAtMost_multiset_sum {A : Set ℕ} {h : ℕ} :
    ∀ S : Multiset ℕ, (∀ x ∈ S, x ∈ sumsetPow A h) →
      IsSumOfAtMost A (S.card * h) S.sum := by
  intro S
  induction S using Multiset.induction with
  | empty =>
      intro _
      simp only [Multiset.card_zero, Nat.zero_mul, Multiset.sum_zero]
      exact zero_isSumOfAtMost A 0
  | cons a s ih =>
      intro hmem
      have ha : IsSumOfAtMost A h a := hmem a (Multiset.mem_cons_self a s)
      have hs : IsSumOfAtMost A (s.card * h) s.sum :=
        ih (fun x hx => hmem x (Multiset.mem_cons_of_mem hx))
      have hidx : (s.card + 1) * h = h + s.card * h := by ring
      rw [Multiset.card_cons, Multiset.sum_cons, hidx]
      exact ha.add hs

/-- **Basis composition (bookkeeping step of Schnirelmann's theorem).** If the
    `h`-fold sum-set `sumsetPow A h` has Schnirelmann density `≥ 1/2`, then `A`
    itself is an additive basis of order `2h`: every `n` is a sum of at most `2h`
    elements of `A`.

    This composes two verified pieces — `isAdditiveBasis_two_of_density_ge_half`
    (density `≥ 1/2` ⇒ the sum-set is a basis of order `2`) with
    `isSumOfAtMost_multiset_sum` (each sum-set element unpacks into `≤ h`
    elements of `A`) — closing the entire iteration bookkeeping. The result is in
    the exact `Multiset` shape of `WeakGoldbach.IsAdditiveBasis A (2h)`.

    Combined with `exists_pow_deficiency_lt_half`, this reduces
    `schnirelmann_basis_theorem` to the *single* outstanding lemma: Schnirelmann's
    inequality `σ(A ⊕ B) ≥ σA + σB − σA·σB` (needed to push some `σ(sumsetPow A h)`
    above `1/2`). -/
theorem isAdditiveBasis_of_sumsetPow_density_ge_half {A : Set ℕ} {h : ℕ}
    [DecidablePred (· ∈ sumsetPow A h)]
    (hdens : 1 / 2 ≤ schnirelmannDensity (sumsetPow A h)) (n : ℕ) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ 2 * h ∧ S.sum = n := by
  obtain ⟨S, hS, hSc, hSs⟩ :=
    isAdditiveBasis_two_of_density_ge_half (zero_mem_sumsetPow A h) hdens n
  have hsum : IsSumOfAtMost A (S.card * h) n := by
    have := isSumOfAtMost_multiset_sum S hS
    rwa [hSs] at this
  obtain ⟨T, hT, hTc, hTs⟩ := hsum.mono (by gcongr)
  exact ⟨T, hT, hTc, hTs⟩

/-
  ── Remaining gap toward `schnirelmann_basis_theorem` ─────────────────────────

  The `schnirelmann_basis_theorem` axiom in `WeakGoldbach.lean` states
    σ(A) > 0 → ∃ h, IsAdditiveBasis A h.
  Discharging it from the covering lemma above requires two further ingredients:

    1. Schnirelmann's inequality (subadditivity of the "deficiency" 1 − σ):
         σ(A ⊕ B) ≥ σ(A) + σ(B) − σ(A)·σ(B),   equivalently
         1 − σ(A ⊕ B) ≤ (1 − σ(A))·(1 − σ(B)).
       This is the delicate gap-counting step (Ruzsa, *Sumsets and structure*).

    2. Iteration: from (1), 1 − σ(h·A) ≤ (1 − σ(A))^h, so for h large enough
       that (1 − σ(A))^h < 1/2 we get σ(h·A) > 1/2; two copies of h·A then have
       density sum > 1, and `sumset_covers_of_density_add_ge_one` finishes:
       every n is a sum of ≤ 2h elements of A, i.e. A is a basis of order 2h.

  Step (2) is now fully verified above:
    * its analytic input — `∃ h, (1 − σ(A))^h < 1/2` — is
      `exists_pow_deficiency_lt_half`;
    * its terminal step — `σ ≥ 1/2 ⇒ additive basis of order 2`, in the
      `Multiset` shape of `IsAdditiveBasis` — is
      `isAdditiveBasis_two_of_density_ge_half`;
    * its bookkeeping — an element of the `h`-fold sum-set is a sum of `≤ h`
      elements of `A`, and this composes to order `2h` — is
      `isSumOfAtMost_multiset_sum` / `IsSumOfAtMost.add`, packaged as the
      reduction `isAdditiveBasis_of_sumsetPow_density_ge_half`:
        `σ(sumsetPow A h) ≥ 1/2 ⇒ IsAdditiveBasis A (2h)`.

  The **sole** remaining gap is therefore step (1), Schnirelmann's inequality
  `σ(A ⊕ B) ≥ σA + σB − σA·σB` (the delicate gap-counting step). Once it lands,
  iterating it drives `σ(sumsetPow A h)` above `1/2` for some `h`, and
  `isAdditiveBasis_of_sumsetPow_density_ge_half` discharges the axiom outright.
-/

end SchnirelmannBasis
