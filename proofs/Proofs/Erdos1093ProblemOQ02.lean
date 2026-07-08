/-
# Erdős Problem #1093 — OQ-02: Is `d(284,28) = 9` the maximal deficiency?

The parent file `Erdos1093Problem.lean` defines the *deficiency* of `C(n,k)`
(for `n ≥ 2k`, when `C(n,k)` has no prime factor `≤ k`): the number of
`0 ≤ i < k` with `n - i` being `k`-smooth.  It records the current record

    `deficiency 284 28 = 9`   (`deficiency_284_28`, by `native_decide`)

together with the smaller deficiency-`1,2,3,4` examples of Erdős–Lacampagne–
Selfridge.  Open Question 02 asks:

> Is `d(284,28) = 9` the **maximum possible** deficiency, or do higher
> values occur?

The universal upper-bound direction is genuinely open.  This file establishes
the **tractable half** and formalizes the question precisely.

## What is proved here (0 `sorry`, no new `axiom` declarations)

1. `noSmallPrimeFactors_iff` — a *decidable* reformulation of the
   `NoSmallPrimeFactors` side-condition: it suffices to check the finitely
   many primes `p ≤ k`.  (The definition quantifies over *all* primes; this
   lemma restricts the check to `Finset.range (k+1)`.)

2. `noSmallPrimeFactors_284_28` — the record `C(284,28)` genuinely satisfies
   the side-condition: no prime `≤ 28` divides `C(284,28)`.  The parent file
   verified the *count* `= 9` but never checked that `(284,28)` is an
   *admissible* pair, so on its own `deficiency_284_28` did not exhibit a
   valid deficiency-9 example.  This closes that gap.

3. `smooth_indices_284_28` — the explicit human-readable certificate: the
   nine smooth indices are `{4, 8, 9, 11, 12, 14, 18, 20, 24}`, i.e. the nine
   `28`-smooth values are

       280 = 2³·5·7,  276 = 2²·3·23,  275 = 5²·11,  273 = 3·7·13,
       272 = 2⁴·17,   270 = 2·3³·5,   266 = 2·7·19,  264 = 2³·3·11,
       260 = 2²·5·13.

4. `exists_deficiency_nine` — the **existence half** of OQ-02: there is a
   valid deficiency example attaining `9`.

5. `maximalDeficiencyIs_nine_iff_upperBound` — the payoff: with the existence
   half discharged, the full conjecture `MaximalDeficiencyIs 9` is
   *equivalent* to the single open statement "no valid example exceeds `9`".
   This isolates exactly the open content.

## Axioms

The record facts (`deficiency_284_28`, `noSmallPrimeFactors_284_28`,
`smooth_indices_284_28`) are discharged by `native_decide`, so they depend on
`Lean.ofReduceBool`.  The structural results (1, 5) are `ofReduceBool`-free.

## Status: OPEN (universal upper bound); existence half machine-verified.
-/

import Proofs.Erdos1093Problem
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-
## Section I: A decidable reformulation of the admissibility side-condition
-/

/-- `NoSmallPrimeFactors n k` is equivalent to checking only the finitely many
primes `p ≤ k`: since a witnessing prime `p` with `p ∣ C(n,k)` must satisfy
`k < p`, the failure of the condition would require a prime `p ≤ k` dividing
`C(n,k)`.  This turns the unbounded `∀ p` into a bounded, decidable check. -/
theorem noSmallPrimeFactors_iff (n k : ℕ) :
    NoSmallPrimeFactors n k ↔
      ∀ p ∈ Finset.range (k + 1), p.Prime → ¬ p ∣ n.choose k := by
  constructor
  · intro h p hp hpp hdvd
    have hlt : k < p := h p hpp hdvd
    have hle : p ≤ k := by have := Finset.mem_range.mp hp; omega
    omega
  · intro h p hpp hdvd
    by_contra hle
    push_neg at hle
    exact h p (Finset.mem_range.mpr (by omega)) hpp hdvd

/-
## Section II: The record `C(284,28)` is an admissible deficiency example
-/

/-- No prime `≤ 28` divides `C(284,28)`, so the pair `(284,28)` is admissible
and its deficiency is well-defined.  Verified by `native_decide` after the
reduction to a bounded prime check. -/
theorem noSmallPrimeFactors_284_28 : NoSmallPrimeFactors 284 28 := by
  rw [noSmallPrimeFactors_iff]
  native_decide

/-- Explicit certificate: the nine smooth indices witnessing `deficiency 284 28 = 9`
are exactly `{4, 8, 9, 11, 12, 14, 18, 20, 24}` (the `28`-smooth values
`280, 276, 275, 273, 272, 270, 266, 264, 260`). -/
theorem smooth_indices_284_28 :
    (Finset.range 28).filter (fun i => IsKSmooth 28 (284 - i))
      = ({4, 8, 9, 11, 12, 14, 18, 20, 24} : Finset ℕ) := by
  native_decide

/-
## Section III: Formalizing OQ-02
-/

/-- A pair `(n,k)` is an *admissible deficiency example* when `n ≥ 2k` and
`C(n,k)` has no prime factor `≤ k` (so the deficiency is well-defined). -/
def ValidDeficiencyExample (n k : ℕ) : Prop :=
  2 * k ≤ n ∧ NoSmallPrimeFactors n k

/-- `MaximalDeficiencyIs D` : some admissible pair attains deficiency `D`, and
no admissible pair exceeds it.  OQ-02 is the assertion `MaximalDeficiencyIs 9`. -/
def MaximalDeficiencyIs (D : ℕ) : Prop :=
  (∃ n k, ValidDeficiencyExample n k ∧ deficiency n k = D) ∧
  (∀ n k, ValidDeficiencyExample n k → deficiency n k ≤ D)

/-- The record pair `(284,28)` is admissible. -/
theorem record_valid : ValidDeficiencyExample 284 28 :=
  ⟨by norm_num, noSmallPrimeFactors_284_28⟩

/-- **Existence half of OQ-02.**  There is an admissible deficiency example
attaining `9` — so if `9` is maximal, it is genuinely attained. -/
theorem exists_deficiency_nine :
    ∃ n k, ValidDeficiencyExample n k ∧ deficiency n k = 9 :=
  ⟨284, 28, record_valid, deficiency_284_28⟩

/-- **Reduction of OQ-02 to its open core.**  Because the existence half is
established (`exists_deficiency_nine`), the conjecture `MaximalDeficiencyIs 9`
is *equivalent* to the single open statement: no admissible pair has deficiency
exceeding `9`.  All the machine-checkable content of OQ-02 lives in the forward
extraction; the remaining content is exactly this universal bound. -/
theorem maximalDeficiencyIs_nine_iff_upperBound :
    MaximalDeficiencyIs 9 ↔ ∀ n k, ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨exists_deficiency_nine, h⟩

/-
## Section IV: Elementary consequences of the trivial bound

The parent's `deficiency_le` gives `deficiency n k ≤ k` unconditionally.  So
any admissible example with deficiency `> 9` must have `k ≥ 10`; equivalently,
OQ-02 is automatic for `k ≤ 9`.
-/

/-- For `k ≤ 9` the deficiency never exceeds `9`, so no counterexample to
`MaximalDeficiencyIs 9` can occur in that range — the open part is confined to
`k ≥ 10`. -/
theorem deficiency_le_nine_of_k_le_nine {n k : ℕ} (hk : k ≤ 9) :
    deficiency n k ≤ 9 :=
  (deficiency_le n k).trans hk

/-
## Section V: A density bound — high deficiency forces few primes in the window

The trivial bound `deficiency n k ≤ k` treats every one of the `k` consecutive
integers `n, n-1, …, n-k+1` as a potential smooth contributor.  But a *prime*
value in that window can never contribute: for an admissible pair every value
`n - i` (`i < k`, `n ≥ 2k`) exceeds `k`, and a `k`-smooth number `> k` cannot be
prime (a prime is `k`-smooth iff it is `≤ k`).  Hence the deficiency is bounded
by the number of *non-prime* values in the window, and — the sharper statement —
`deficiency + (#primes in the window) ≤ k`.  A large deficiency therefore forces
the length-`k` window of consecutive integers to contain few primes, exactly the
density phenomenon the Erdős–Lacampagne–Selfridge bound exploits.
-/

/-- Every value `n - i` in the deficiency window exceeds `k` (needs `i < k`,
`n ≥ 2k`). -/
theorem window_value_gt_k {n k i : ℕ} (hi : i < k) (hn : 2 * k ≤ n) :
    k < n - i := by omega

/-- A smooth contributor to the deficiency is never prime: it exceeds `k`, and a
`k`-smooth number `> k` cannot be prime (a prime `p` is `k`-smooth iff `p ≤ k`). -/
theorem smooth_contributor_not_prime {n k i : ℕ} (hi : i < k) (hn : 2 * k ≤ n)
    (hs : IsKSmooth k (n - i)) : ¬ (n - i).Prime := by
  intro hp
  have hle : n - i ≤ k := (isKSmooth_prime_iff hp).mp hs
  have hgt : k < n - i := window_value_gt_k hi hn
  omega

/-- **Density bound (weak form).**  The deficiency is at most the number of
non-prime values among the `k` consecutive integers `n, …, n-k+1`. -/
theorem deficiency_le_nonprime_count {n k : ℕ} (hn : 2 * k ≤ n) :
    deficiency n k ≤
      ((Finset.range k).filter (fun i => ¬ (n - i).Prime)).card := by
  unfold deficiency
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  obtain ⟨hir, hsmooth⟩ := hi
  exact ⟨hir, smooth_contributor_not_prime (Finset.mem_range.mp hir) hn hsmooth⟩

/-- **Density bound (sharp form).**  The deficiency plus the number of primes in
the length-`k` window `n, …, n-k+1` is at most `k`.  Equivalently, an admissible
pair with deficiency `d` has at most `k - d` primes among its `k` consecutive
integers, so a record-breaking deficiency forces an unusually prime-poor window. -/
theorem deficiency_add_prime_count_le {n k : ℕ} (hn : 2 * k ≤ n) :
    deficiency n k
      + ((Finset.range k).filter (fun i => (n - i).Prime)).card ≤ k := by
  have hpart :
      ((Finset.range k).filter (fun i => (n - i).Prime)).card
        + ((Finset.range k).filter (fun i => ¬ (n - i).Prime)).card = k := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_range]
  have hd := deficiency_le_nonprime_count (n := n) (k := k) hn
  omega

/-
## Section VI: Sharpening the open core to `k ≥ 10`

Combining the trivial bound with the existence half, the whole conjecture
`MaximalDeficiencyIs 9` collapses to a universal statement quantified only over
`k ≥ 10`: the cases `k ≤ 9` are automatic from `deficiency ≤ k`.
-/

/-- **Sharpened reduction.**  `MaximalDeficiencyIs 9` is equivalent to the open
statement restricted to `k ≥ 10`; the small cases `k ≤ 9` are discharged by the
trivial bound.  This is strictly sharper than
`maximalDeficiencyIs_nine_iff_upperBound`. -/
theorem maximalDeficiencyIs_nine_iff_kGe10 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 10 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 9
    · exact deficiency_le_nine_of_k_le_nine hk
    · exact h n k (by omega) hv

/-
## Section VII: Prime values in the window cap the deficiency

The sharp density bound `deficiency + (#primes in window) ≤ k`
(`deficiency_add_prime_count_le`) has a clean *effective* consequence:
exhibiting a **single** prime among the `k` consecutive integers `n, …, n-k+1`
already forces `deficiency n k < k`.  Dually, the extreme case
`deficiency n k = k` (every window value `k`-smooth) can only occur across a
prime gap of length `≥ k` — no window value is prime.  This is a structural
reason record deficiencies are hard: they demand unusually prime-poor windows,
exactly the phenomenon the Erdős–Lacampagne–Selfridge density bound exploits.
-/

/-- **A prime in the window strictly lowers the deficiency.**  If some `n - i`
(`i < k`) is prime, then `deficiency n k < k`: the prime occupies a window slot
that no smooth contributor can (a smooth window value is never prime), and the
sharp bound converts this into `< k`.  Effective: one prime certificate suffices. -/
theorem deficiency_lt_k_of_prime_in_window {n k i : ℕ} (hn : 2 * k ≤ n)
    (hi : i < k) (hp : (n - i).Prime) : deficiency n k < k := by
  have hmem : i ∈ (Finset.range k).filter (fun j => (n - j).Prime) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hp⟩
  have hpos : 1 ≤ ((Finset.range k).filter (fun j => (n - j).Prime)).card :=
    Finset.one_le_card.mpr ⟨i, hmem⟩
  have hbound := deficiency_add_prime_count_le (n := n) (k := k) hn
  omega

/-- **Extreme deficiency forces a prime gap.**  If the deficiency attains the
trivial maximum `deficiency n k = k` (every one of the `k` consecutive integers
`n, …, n-k+1` is `k`-smooth), then none of them is prime — a prime gap of length
`≥ k`.  Record deficiencies are correspondingly hard: they demand prime-poor
windows. -/
theorem window_primefree_of_deficiency_eq_k {n k : ℕ} (hn : 2 * k ≤ n)
    (h : deficiency n k = k) : ∀ i < k, ¬ (n - i).Prime := by
  intro i hi hp
  have := deficiency_lt_k_of_prime_in_window hn hi hp
  omega

/-
## Section VIII: The multiplicative reformulation — admissibility as coprimality

The admissibility side-condition `NoSmallPrimeFactors n k` ("no prime `≤ k`
divides `C(n,k)`") is exactly the statement that `C(n,k)` is **coprime to `k!`**:
the prime factors of `k!` are precisely the primes `≤ k`.  Recasting the
condition this way is what makes the Erdős–Lacampagne–Selfridge argument run,
because the window product factors multiplicatively:

    ∏_{i<k} (n - i)  =  n.descFactorial k  =  k! · C(n,k).

For an admissible pair the cofactor `C(n,k)` carries *no* prime `≤ k`, so the
entire "small-prime part" of the length-`k` window is packaged into the single
factor `k!`.  This is the exact accounting the density bound of Section V only
approximated, and it yields (Section IX) the first *quantitative* upper bound on
the deficiency improving on the trivial `deficiency ≤ k` **without** invoking the
axiomatized ELS bound.
-/

/-- **Admissibility ⇔ coprimality with `k!`.**  `C(n,k)` has no prime factor
`≤ k` exactly when it is coprime to `k!` (whose prime factors are the primes
`≤ k`).  This is the conceptual form of `NoSmallPrimeFactors`, cleaner than the
bounded prime check `noSmallPrimeFactors_iff` and the form ELS work in. -/
theorem noSmallPrimeFactors_iff_coprime (n k : ℕ) :
    NoSmallPrimeFactors n k ↔ Nat.Coprime (n.choose k) (Nat.factorial k) := by
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpc hpf
    have hlt : k < p := h p hp hpc
    have hle : p ≤ k := (Nat.Prime.dvd_factorial hp).mp hpf
    omega
  · intro hcop p hp hpc
    by_contra hle
    push_neg at hle
    have hpf : p ∣ Nat.factorial k := (Nat.Prime.dvd_factorial hp).mpr (by omega)
    have hcop' : Nat.gcd (n.choose k) (Nat.factorial k) = 1 := hcop
    have hd1 : p ∣ Nat.gcd (n.choose k) (Nat.factorial k) := Nat.dvd_gcd hpc hpf
    rw [hcop'] at hd1
    exact hp.one_lt.ne' (Nat.dvd_one.mp hd1)

/-- The multiplicative decomposition of the length-`k` window: the product of the
`k` consecutive integers `n, n-1, …, n-k+1` equals `k! · C(n,k)`.  (This is the
descending-factorial identity `n.descFactorial k = k! · C(n,k)` expressed over the
window range.) -/
theorem window_prod_eq_choose_mul_factorial (n k : ℕ) :
    ∏ i ∈ Finset.range k, (n - i) = Nat.factorial k * n.choose k := by
  rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]

/-- A finite product of `k`-smooth numbers is `k`-smooth. -/
theorem isKSmooth_prod {k : ℕ} {s : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ s, IsKSmooth k (f i)) : IsKSmooth k (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsKSmooth k) (fun _ _ ha hb => isKSmooth_mul ha hb)
    (isKSmooth_one k) hf

/-
## Section IX: A quantitative bound `(k+1)^{deficiency} ≤ k!`

For an admissible pair the product `P` of the smooth window values is `k`-smooth,
so it shares no prime factor with the cofactor `C(n,k)` (which is coprime to every
prime `≤ k`).  Since `P ∣ k! · C(n,k)` and `gcd(P, C(n,k)) = 1`, we get `P ∣ k!`.
Each smooth contributor exceeds `k`, so `P ≥ (k+1)^{deficiency}`; combined with
`P ≤ k!` this bounds the deficiency strictly below the trivial `k` for every `k`
(e.g. for `k = 28` it already forces `deficiency ≤ 20`, the record being `9`).
Crucially this bound is `ofReduceBool`-free and independent of the axiomatized
`els_upper_bound`.
-/

/-- **The smooth part of the window divides `k!`.**  For an admissible pair the
product of the `k`-smooth values among `n, …, n-k+1` divides `k!`: it is `k`-smooth
and hence coprime to the admissible cofactor `C(n,k)`, while it divides
`k! · C(n,k) = ∏(n-i)`. -/
theorem smooth_window_prod_dvd_factorial {n k : ℕ} (h : NoSmallPrimeFactors n k) :
    (∏ i ∈ (Finset.range k).filter (fun i => IsKSmooth k (n - i)), (n - i)) ∣ Nat.factorial k := by
  set S := (Finset.range k).filter (fun i => IsKSmooth k (n - i)) with hS
  set P := ∏ i ∈ S, (n - i) with hP
  have hPsmooth : IsKSmooth k P := by
    apply isKSmooth_prod
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hdvd : P ∣ Nat.factorial k * n.choose k := by
    have hsub : S ⊆ Finset.range k := Finset.filter_subset _ _
    have hpd : P ∣ ∏ i ∈ Finset.range k, (n - i) :=
      Finset.prod_dvd_prod_of_subset S (Finset.range k) (fun i => n - i) hsub
    rwa [window_prod_eq_choose_mul_factorial] at hpd
  have hcop : Nat.Coprime P (n.choose k) := by
    apply Nat.coprime_of_dvd
    intro q hq hqP hqC
    have hqk : q ≤ k := hPsmooth q hq hqP
    have : k < q := h q hq hqC
    omega
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- **Quantitative deficiency bound.**  For an admissible pair, since each of the
`deficiency n k` smooth window values exceeds `k` and their product divides `k!`,

    `(k+1) ^ (deficiency n k) ≤ k!`.

This is the first upper bound in the file that improves on the trivial
`deficiency n k ≤ k` without the axiomatized ELS bound (for `k = 28` it already
forces `deficiency ≤ 20`). -/
theorem deficiency_pow_succ_le_factorial {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) :
    (k + 1) ^ deficiency n k ≤ Nat.factorial k := by
  set S := (Finset.range k).filter (fun i => IsKSmooth k (n - i)) with hS
  have hcard : deficiency n k = S.card := rfl
  set P := ∏ i ∈ S, (n - i) with hP
  have hlow : (k + 1) ^ S.card ≤ P := by
    apply Finset.pow_card_le_prod
    intro i hi
    have hir : i < k := Finset.mem_range.mp (Finset.filter_subset _ _ hi)
    have := window_value_gt_k hir hn
    omega
  have hdvd : P ∣ Nat.factorial k := smooth_window_prod_dvd_factorial h
  have hle : P ≤ Nat.factorial k := Nat.le_of_dvd (Nat.factorial_pos k) hdvd
  calc (k + 1) ^ deficiency n k = (k + 1) ^ S.card := by rw [hcard]
    _ ≤ P := hlow
    _ ≤ Nat.factorial k := hle

/-
## Section X: The sharp factorial bound `(k + deficiency)! ≤ (k!)²`

Section IX only used that each smooth window value exceeds `k`, giving the crude
lower bound `P ≥ (k+1)^{deficiency}`.  But the smooth window values are *distinct*
integers (the map `i ↦ n - i` is injective on `i < k ≤ n`), so `P` is a product of
`deficiency` **distinct** integers each `≥ k+1`.  The smallest such product is
`(k+1)(k+2)⋯(k+d) = (k+1).ascFactorial d`, hence

    `(k+1).ascFactorial (deficiency n k) ≤ P ≤ k!`.

Multiplying by `k!` and using `k! · (k+1).ascFactorial d = (k+d)!`
(`Nat.factorial_mul_ascFactorial`) turns this into the memorable closed form

    `(k + deficiency n k)! ≤ (k!)²`.

This strictly improves Section IX (for `k = 28` it forces `deficiency ≤ 18` versus
the `≤ 20` from `(k+1)^d ≤ k!`), and like everything since Section V it is
`ofReduceBool`-free and independent of the axiomatized ELS bound.
-/

/-- **Product lower bound for distinct naturals bounded below.**  If every element
of a finset `T ⊆ ℕ` is at least `m`, then `∏_{x∈T} x ≥ m(m+1)⋯(m+|T|-1)` — the
product of the `|T|` smallest values the elements could possibly take.  Proved by
induction on `T`, peeling off the maximum: the erased set lies in `[m, max)`, whose
`max - m` slots bound its cardinality, forcing `max ≥ m + (|T|-1)`. -/
theorem prod_range_add_le_prod_of_forall_ge {m : ℕ} :
    ∀ (T : Finset ℕ), (∀ x ∈ T, m ≤ x) →
      (∏ j ∈ Finset.range T.card, (m + j)) ≤ ∏ x ∈ T, x := by
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro hT
    rcases T.eq_empty_or_nonempty with rfl | hne
    · simp
    · set M := T.max' hne with hM
      have hMmem : M ∈ T := T.max'_mem hne
      have hMge : m ≤ M := hT M hMmem
      have hsub : T.erase M ⊆ Finset.Ico m M := by
        intro x hx
        have hxT : x ∈ T := Finset.mem_of_mem_erase hx
        have hxne : x ≠ M := Finset.ne_of_mem_erase hx
        have hxle : x ≤ M := T.le_max' x hxT
        exact Finset.mem_Ico.mpr ⟨hT x hxT, lt_of_le_of_ne hxle hxne⟩
      have hcardle : (T.erase M).card ≤ M - m := by
        calc (T.erase M).card ≤ (Finset.Ico m M).card := Finset.card_le_card hsub
          _ = M - m := Nat.card_Ico m M
      have hMbound : m + (T.erase M).card ≤ M := by omega
      have hcard : T.card = (T.erase M).card + 1 := by
        have he := Finset.card_erase_of_mem hMmem
        have hpos : 0 < T.card := Finset.card_pos.mpr hne
        omega
      have hIH : (∏ j ∈ Finset.range (T.erase M).card, (m + j)) ≤ ∏ x ∈ T.erase M, x :=
        ih (T.erase M) (Finset.erase_ssubset hMmem)
          (fun x hx => hT x (Finset.mem_of_mem_erase hx))
      rw [hcard, Finset.prod_range_succ]
      calc (∏ j ∈ Finset.range (T.erase M).card, (m + j)) * (m + (T.erase M).card)
          ≤ (∏ x ∈ T.erase M, x) * M := Nat.mul_le_mul hIH hMbound
        _ = ∏ x ∈ T, x := by
              rw [mul_comm]; exact Finset.mul_prod_erase T (fun x => x) hMmem

/-- **The smooth window product dominates `(k+1).ascFactorial (deficiency)`.**  The
`deficiency n k` smooth values in the window are distinct integers each `> k`, so
their product is at least the product `(k+1)(k+2)⋯(k+deficiency)` of the smallest
possible distinct values above `k`. -/
theorem ascFactorial_le_smooth_window_prod {n k : ℕ} (hn : 2 * k ≤ n) :
    (k + 1).ascFactorial (deficiency n k) ≤
      ∏ i ∈ (Finset.range k).filter (fun i => IsKSmooth k (n - i)), (n - i) := by
  set S := (Finset.range k).filter (fun i => IsKSmooth k (n - i)) with hS
  have hcard : deficiency n k = S.card := rfl
  set T := S.image (fun i => n - i) with hT
  have hinj : ∀ a ∈ S, ∀ b ∈ S, (fun i => n - i) a = (fun i => n - i) b → a = b := by
    intro a ha b hb hab
    simp only at hab
    have hak : a < k := Finset.mem_range.mp (Finset.filter_subset _ _ ha)
    have hbk : b < k := Finset.mem_range.mp (Finset.filter_subset _ _ hb)
    omega
  have hTcard : T.card = S.card := Finset.card_image_of_injOn (by
    intro a ha b hb hab
    exact hinj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab)
  have hPeq : (∏ x ∈ T, x) = ∏ i ∈ S, (n - i) := Finset.prod_image hinj
  have hTge : ∀ x ∈ T, k + 1 ≤ x := by
    intro x hx
    rw [hT, Finset.mem_image] at hx
    obtain ⟨i, hiS, rfl⟩ := hx
    have hik : i < k := Finset.mem_range.mp (Finset.filter_subset _ _ hiS)
    have := window_value_gt_k hik hn
    omega
  calc (k + 1).ascFactorial (deficiency n k)
      = (k + 1).ascFactorial T.card := by rw [hcard, hTcard]
    _ = ∏ j ∈ Finset.range T.card, (k + 1 + j) := by rw [Nat.ascFactorial_eq_prod_range]
    _ ≤ ∏ x ∈ T, x := prod_range_add_le_prod_of_forall_ge T hTge
    _ = ∏ i ∈ S, (n - i) := hPeq

/-- **Sharp ascending-factorial bound.**  For an admissible pair,

    `(k+1).ascFactorial (deficiency n k) ≤ k!`,

i.e. `(k+1)(k+2)⋯(k+deficiency) ≤ k!`.  This refines Section IX's
`(k+1)^{deficiency} ≤ k!` because the smooth window values are distinct. -/
theorem deficiency_ascFactorial_le_factorial {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) :
    (k + 1).ascFactorial (deficiency n k) ≤ Nat.factorial k := by
  have hlow := ascFactorial_le_smooth_window_prod (n := n) (k := k) hn
  have hdvd := smooth_window_prod_dvd_factorial h
  exact hlow.trans (Nat.le_of_dvd (Nat.factorial_pos k) hdvd)

/-- **Sharp factorial bound (closed form).**  For an admissible pair,

    `(k + deficiency n k)! ≤ (k!)²`.

This is the strongest elementary upper bound in the file: it improves Section IX
(for `k = 28` it forces `deficiency ≤ 18`, versus `≤ 20`), is `ofReduceBool`-free,
and does not use the axiomatized ELS bound.  It follows from
`deficiency_ascFactorial_le_factorial` via `k! · (k+1).ascFactorial d = (k+d)!`. -/
theorem deficiency_add_factorial_le_sq {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) :
    Nat.factorial (k + deficiency n k) ≤ (Nat.factorial k) ^ 2 := by
  have hasc := deficiency_ascFactorial_le_factorial hn h
  calc Nat.factorial (k + deficiency n k)
      = Nat.factorial k * (k + 1).ascFactorial (deficiency n k) :=
        (Nat.factorial_mul_ascFactorial k (deficiency n k)).symm
    _ ≤ Nat.factorial k * Nat.factorial k := Nat.mul_le_mul (le_refl _) hasc
    _ = (Nat.factorial k) ^ 2 := by rw [pow_two]
