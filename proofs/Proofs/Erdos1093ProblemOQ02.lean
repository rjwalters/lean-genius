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

Two record facts remain discharged by `native_decide`, so they depend on
`Lean.ofReduceBool`: the parent's `deficiency_284_28` computes the bignum
binomial `C(284,28)` (Pascal recursion, infeasible for the kernel), and
`smooth_indices_284_28` factors values via `Nat.primeFactors` (well-founded
recursion, which does not reduce under kernel `decide`).  Two facts that
previously used `native_decide` are now `ofReduceBool`-free:
- the numeric certificate `(28!)² < 47!` inside `deficiency_record_le_18`
  (Section XII), via kernel `decide` (`Nat.factorial` is structural recursion, so
  the kernel reduces it);
- `noSmallPrimeFactors_284_28`, via **Kummer's theorem** — instead of the bignum
  divisibility test it reduces each prime `p ≤ 28` to a bounded base-`p` carry
  count (`Nat.factorization_choose`) that the kernel discharges.

The structural results (1, 5) and all of Sections IV–XI are `ofReduceBool`-free.

## Status: OPEN (universal upper bound); existence half machine-verified.
-/

import Proofs.Erdos1093Problem
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Choose.Factorization
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
and its deficiency is well-defined.

**`ofReduceBool`-free (kernel `decide` only).**  Rather than compute the
~50-digit bignum `C(284,28)` and test divisibility — which would force
`native_decide`, since kernel `decide` cannot evaluate the exponential Pascal
recursion for `Nat.choose 284 28` — we invoke **Kummer's theorem**
(`Nat.factorization_choose`): the `p`-adic valuation of `C(n,k)` equals the
number of carries when `k` and `n - k` are added in base `p`.  For each prime
`p ≤ 28`, `p ∣ C(284,28)` would force a positive carry count over the finite
window `Ico 1 9` (valid because `log p 284 ≤ log 2 284 = 8 < 9`), a purely
bounded `%`/`≤` computation the kernel discharges.  Adding `28` and `256` has no
carry in any base `p ≤ 28`, so the carry count is `0` and no such prime divides
`C(284,28)`. -/
theorem noSmallPrimeFactors_284_28 : NoSmallPrimeFactors 284 28 := by
  rw [noSmallPrimeFactors_iff]
  intro p hp hpp hdvd
  have hp2 : 2 ≤ p := hpp.two_le
  have hchoose_ne : Nat.choose 284 28 ≠ 0 := (Nat.choose_pos (by norm_num)).ne'
  have hpos : 0 < (Nat.choose 284 28).factorization p :=
    hpp.factorization_pos_of_dvd hchoose_ne hdvd
  -- Kummer's carry bound needs any `b > log p 284`; `log p 284 ≤ log 2 284 = 8`.
  have hb : Nat.log p 284 < 9 := by
    apply Nat.log_lt_of_lt_pow (by norm_num)
    calc (284 : ℕ) < 2 ^ 9 := by norm_num
      _ ≤ p ^ 9 := Nat.pow_le_pow_left hp2 9
  rw [Nat.factorization_choose hpp (by norm_num) hb] at hpos
  -- `hpos : 0 < #{i ∈ Ico 1 9 | p ^ i ≤ 28 % p ^ i + (284 - 28) % p ^ i}`.
  -- Case on the finitely many `p ≤ 28`: non-primes contradict `hpp`; for each
  -- prime the carry set is empty, contradicting `hpos`.
  have hp28 : p ≤ 28 := by have := Finset.mem_range.mp hp; omega
  -- For each prime `p` the carry set is empty (`decide` closes `0 < card → False`);
  -- composite `p` are ruled out by `hpp` (`norm_num` only ever sees non-primes here,
  -- where `¬ p.Prime` holds — proving it against a *prime* would instead reduce the
  -- side goal to `⊢ False` and stall, so `decide` must be tried first).
  interval_cases p <;>
    first
      | (revert hpos; decide)
      | exact absurd hpp (by norm_num)

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

/-
## Section XI: The trivial bound is never attained — windows are never fully smooth

The quantitative bound `(k+1)^{deficiency} ≤ k!` of Section IX has a clean
*qualitative* consequence that the earlier bounds could not reach: the trivial
maximum `deficiency n k = k` is **impossible** for every admissible pair with
`k ≥ 1`.  Indeed if the deficiency were `k` then `(k+1)^k ≤ k!`, but
`k! ≤ k^k < (k+1)^k`, a contradiction.  So the deficiency is *strictly* below the
trivial bound — `deficiency n k ≤ k - 1` — with no appeal to prime distribution
or the axiomatized ELS bound.

This makes the hypothesis of `window_primefree_of_deficiency_eq_k` (Section VII)
vacuous: no admissible length-`k` window is entirely `k`-smooth, so at least one
of the `k` consecutive integers `n, …, n-k+1` always carries a prime factor `> k`.
-/

/-- **The trivial bound is strict.**  For an admissible pair with `k ≥ 1`, the
deficiency is *strictly* less than `k`: `deficiency n k < k`.  This improves the
trivial `deficiency n k ≤ k` of `deficiency_le` unconditionally — no prime-gap or
density input is needed — via the multiplicative bound `(k+1)^{deficiency} ≤ k!`
together with `k! ≤ k^k < (k+1)^k`. -/
theorem deficiency_lt_k {n k : ℕ} (hn : 2 * k ≤ n) (hk : 1 ≤ k)
    (h : NoSmallPrimeFactors n k) : deficiency n k < k := by
  by_contra hge
  push_neg at hge
  have hbound := deficiency_pow_succ_le_factorial hn h
  have hmono : (k + 1) ^ k ≤ (k + 1) ^ deficiency n k :=
    Nat.pow_le_pow_right (by omega) hge
  have hfk : Nat.factorial k < (k + 1) ^ k :=
    calc Nat.factorial k ≤ k ^ k := Nat.factorial_le_pow k
      _ < (k + 1) ^ k := Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by omega)
  omega

/-- **No admissible window is entirely smooth.**  For an admissible pair with
`k ≥ 1`, at least one of the `k` consecutive integers `n, n-1, …, n-k+1` fails to
be `k`-smooth, i.e. carries a prime factor `> k`.  (Immediate from
`deficiency_lt_k`: if every window value were `k`-smooth the deficiency would be
`k`.) -/
theorem exists_nonsmooth_window_value {n k : ℕ} (hn : 2 * k ≤ n) (hk : 1 ≤ k)
    (h : NoSmallPrimeFactors n k) :
    ∃ i, i < k ∧ ¬ IsKSmooth k (n - i) := by
  by_contra hcon
  push_neg at hcon
  have hfull : deficiency n k = k := by
    unfold deficiency
    rw [Finset.filter_true_of_mem
      (fun i hi => hcon i (Finset.mem_range.mp hi)), Finset.card_range]
  have := deficiency_lt_k hn hk h
  omega

/-
## Section XII: The sharp bound already resolves `k ≤ 14` — open frontier is `k ≥ 15`

The sharp factorial bound `(k + deficiency n k)! ≤ (k!)²`
(`deficiency_add_factorial_le_sq`) is not merely a per-`k` numerical ceiling: for
small `k` that ceiling already drops below `9`.  A deficiency `≥ 9` would force
`(k + 9)! ≤ (k!)²`, but a direct finite check shows `(k!)² < (k + 9)!` for every
`k ≤ 14` (the inequality first fails at `k = 15`, where `(15!)² ` first exceeds
`24!`).  Hence *no* admissible pair with `k ≤ 14` can have deficiency exceeding
`8`, and the open universal bound `MaximalDeficiencyIs 9` is confined to `k ≥ 15`
— a strict sharpening of the `k ≥ 10` reduction of Section VI, obtained with no
appeal to prime distribution or the axiomatized ELS bound, and `ofReduceBool`-free
(the finite check is discharged by kernel `decide`, not `native_decide`).
-/

/-- **The sharp bound closes `k ≤ 14`.**  For an admissible pair with `k ≤ 14`
the deficiency never exceeds `8`.  Indeed a deficiency `≥ 9` would give
`(k + 9)! ≤ (k + deficiency n k)! ≤ (k!)²` via `deficiency_add_factorial_le_sq`,
contradicting the finite fact `(k!)² < (k + 9)!` valid for all `k ≤ 14`.  This is
the first place the elementary sharp bound *beats* the target `9`, and it does so
uniformly in `n`. -/
theorem deficiency_le_eight_of_k_le_14 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 14) : deficiency n k ≤ 8 := by
  by_contra hcon
  push_neg at hcon
  have hsharp := deficiency_add_factorial_le_sq hn h
  have hle : Nat.factorial (k + 9) ≤ (Nat.factorial k) ^ 2 :=
    (Nat.factorial_le (by omega)).trans hsharp
  interval_cases k <;> exact absurd hle (by decide)

/-- **Sharpened reduction to `k ≥ 15`.**  `MaximalDeficiencyIs 9` is equivalent to
the open universal bound restricted to `k ≥ 15`: the cases `k ≤ 9` are automatic
from the trivial bound and the cases `10 ≤ k ≤ 14` are now discharged by the sharp
factorial bound (`deficiency_le_eight_of_k_le_14`).  Strictly sharper than
`maximalDeficiencyIs_nine_iff_kGe10`; the entire remaining open content of OQ-02
lives at `k ≥ 15`. -/
theorem maximalDeficiencyIs_nine_iff_kGe15 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 15 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 14
    · have := deficiency_le_eight_of_k_le_14 hv.1 hv.2 hk; omega
    · exact h n k (by omega) hv

/-
## Section XIII: The sharp factorial bound is *exactly* tight — it provably cannot
exclude deficiency `9` for any `k ≥ 15`

Section XII showed the sharp bound `(k + deficiency)! ≤ (k!)²` closes every case
`k ≤ 14`.  The natural question is whether pushing the *same* elementary bound
further could close `k = 15, 16, …` too.  It cannot: the frontier `k ≤ 14` is
*exactly* the reach of the `(k!)²` method.  Concretely, for every `k ≥ 15`,

    `(k + 9)! ≤ (k!)²`,

so the sharp bound is *consistent with* deficiency `9` at every `k ≥ 15` and can
never, by itself, rule out a deficiency of `9` there.  Equivalently, the finite
fact `(k!)² < (k + 9)!` powering `deficiency_le_eight_of_k_le_14` holds for
`k ≤ 14` and *reverses* exactly at `k = 15`.

This is a limitative result: it does not advance the universal bound, but it proves
rigorously that the remaining open content of OQ-02 at `k ≥ 15` lies genuinely
beyond the elementary `(k!)²` method — no amount of pushing this bound closes it,
so the tail truly requires the axiomatized Erdős–Lacampagne–Selfridge density
input.  Like everything since Section V it is `ofReduceBool`-free.
-/

/-- **The sharp bound permits deficiency `9` for every `k ≥ 15`.**  For all
`k ≥ 15` one has `(k + 9)! ≤ (k!)²`.  Hence the sharp factorial bound
`deficiency_add_factorial_le_sq` is *consistent with* `deficiency = 9` at every
`k ≥ 15`: it cannot exclude a deficiency of `9` there.  Paired with
`deficiency_le_eight_of_k_le_14` — whose finite check `(k!)² < (k + 9)!` reverses
exactly at `k = 15` — this shows the elementary sharp bound closes *precisely* the
cases `k ≤ 14`, confirming the open frontier `k ≥ 15` is beyond its reach.

Proof by induction from the base `24! ≤ (15!)²`; the inductive step multiplies the
hypothesis `(k + 9)! ≤ (k!)²` by the factor `k + 10 ≤ (k + 1)²`. -/
theorem sharp_bound_permits_deficiency_nine :
    ∀ k, 15 ≤ k → Nat.factorial (k + 9) ≤ (Nat.factorial k) ^ 2 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      have e1 : k + 1 + 9 = (k + 9) + 1 := by omega
      have hstep :
          (k + 10) * Nat.factorial (k + 9) ≤ (k + 1) ^ 2 * (Nat.factorial k) ^ 2 := by
        have h1 : (k + 10) * Nat.factorial (k + 9) ≤ (k + 10) * (Nat.factorial k) ^ 2 :=
          Nat.mul_le_mul le_rfl ih
        have h2 :
            (k + 10) * (Nat.factorial k) ^ 2 ≤ (k + 1) ^ 2 * (Nat.factorial k) ^ 2 :=
          Nat.mul_le_mul (by nlinarith [hk]) le_rfl
        exact h1.trans h2
      calc Nat.factorial (k + 1 + 9)
          = (k + 10) * Nat.factorial (k + 9) := by
              rw [e1, Nat.factorial_succ]
        _ ≤ (k + 1) ^ 2 * (Nat.factorial k) ^ 2 := hstep
        _ = (Nat.factorial (k + 1)) ^ 2 := by rw [Nat.factorial_succ, mul_pow]

/-- **The elementary sharp bound resolves *exactly* `k ≤ 14`.**  Combining
`deficiency_le_eight_of_k_le_14` (the sharp bound forces `deficiency ≤ 8` when
`k ≤ 14`) with `sharp_bound_permits_deficiency_nine` (the bound is consistent with
`deficiency = 9` once `k ≥ 15`): the `(k!)²` method closes the deficiency question
for `k ≤ 14` and is provably powerless for `k ≥ 15`.  Stated as the sharp split of
the finite comparison at the frontier `k = 15`. -/
theorem sharp_bound_frontier_exact (k : ℕ) :
    (k ≤ 14 → (Nat.factorial k) ^ 2 < Nat.factorial (k + 9)) ∧
    (15 ≤ k → Nat.factorial (k + 9) ≤ (Nat.factorial k) ^ 2) := by
  refine ⟨fun hk => ?_, fun hk => sharp_bound_permits_deficiency_nine k hk⟩
  interval_cases k <;> decide

/-
## Section XIV: The explicit elementary bound at the record modulus `k = 28`

Section X's sharp closed form `(k + deficiency n k)! ≤ (k!)²`
(`deficiency_add_factorial_le_sq`) is an abstract inequality; specialising it to
the record modulus `k = 28` turns it into a concrete numeric ceiling on the
deficiency.  Since `(28!)² < 47!` (a single bignum comparison, kernel `decide`)
while `(28!)² ≥ 46! = (28 + 18)!`, the bound `(28 + d)! ≤ (28!)²` forces
`d ≤ 18`.  So *every* admissible pair with `k = 28` — including the record
`(284, 28)` itself — has deficiency at most `18`.

This is the best ceiling the purely elementary (ELS-axiom-free) theory of this
file delivers at `k = 28`, and it quantifies precisely the gap it leaves open:
the actual record there is `deficiency 284 28 = 9`, so closing OQ-02 at this
modulus still needs to rule out the range `10 ≤ d ≤ 18` — exactly the analytic
short-interval prime-density input the elementary product argument cannot supply.
-/

/-- **Explicit deficiency ceiling at the record modulus `k = 28`.**  Every
admissible pair `(n, 28)` has `deficiency n 28 ≤ 18`.  This specialises the sharp
factorial bound `(28 + d)! ≤ (28!)²` (`deficiency_add_factorial_le_sq`) using the
numeric certificate `(28!)² < 47!`: a deficiency `≥ 19` would give
`47! ≤ (28 + d)! ≤ (28!)² < 47!`, a contradiction.  The record `(284, 28)` attains
`9`, so the elementary theory still leaves the window `10 ≤ d ≤ 18` open. -/
theorem deficiency_record_le_18 {n : ℕ} (hn : 56 ≤ n)
    (h : NoSmallPrimeFactors n 28) : deficiency n 28 ≤ 18 := by
  by_contra hgt
  push_neg at hgt
  have hsq := deficiency_add_factorial_le_sq (n := n) (k := 28) (by omega) h
  have hmono : Nat.factorial 47 ≤ Nat.factorial (28 + deficiency n 28) :=
    Nat.factorial_le (by omega)
  -- `Nat.factorial` is structural recursion, so the kernel reduces it: this
  -- bignum comparison is checked by `decide` (⇒ no `Lean.ofReduceBool`), matching
  -- the `interval_cases k <;> decide` pattern used for the abstract bound above.
  have hnum : (Nat.factorial 28) ^ 2 < Nat.factorial 47 := by decide
  exact absurd (hmono.trans hsq) (not_le.mpr hnum)

/-
## Section XV: The correct OQ-02 frontier — the sharp bound closes `k ≤ 15`, open frontier is `k ≥ 16`

Sections XII–XIII analysed the finite comparison `(k!)² < (k + 9)!`, whose reversal
at `k = 15` confines the reach of the sharp bound *for detecting deficiency `9`* to
`k ≤ 14`.  But OQ-02 (`MaximalDeficiencyIs 9`) is the statement that no admissible
pair has deficiency **exceeding** `9`, i.e. it must rule out deficiency `≥ 10`.  The
threshold `9` was therefore one too small: the exclusion of deficiency `≥ 10` is
governed by the comparison `(k!)² < (k + 10)!`, whose reversal sits at `k = 16`, not
`k = 15`.

Concretely `(k!)² < (k + 10)!` holds for every `k ≤ 15` (at the frontier
`25!/(15!)² ≈ 9.07 > 1`) and *reverses* at `k = 16` (`26!/(16!)² ≈ 0.92 < 1`).  Via
the sharp factorial bound `(k + deficiency n k)! ≤ (k!)²`
(`deficiency_add_factorial_le_sq`), the case `deficiency ≥ 10` forces
`(k + 10)! ≤ (k!)²`, impossible for `k ≤ 15`.  Hence *every* admissible pair with
`k ≤ 15` already has `deficiency ≤ 9`, and the open universal bound of OQ-02 is
confined to `k ≥ 16` — a strict sharpening of `maximalDeficiencyIs_nine_iff_kGe15`
(which left `k = 15` nominally open).  Like everything since Section V it is
`ofReduceBool`-free (the finite comparisons are discharged by kernel `decide`).
-/

/-- **The deficiency-`10` frontier comparison.**  For every `k ≤ 15` one has
`(k!)² < (k + 10)!`.  This is the analogue for the exclusion of deficiency `≥ 10`
of the `(k!)² < (k + 9)!` comparison of Section XII, and it reverses one step
later — at `k = 16` (see `sharp_bound_permits_deficiency_ten`). -/
theorem factorial_sq_lt_add_ten_of_k_le_15 {k : ℕ} (hk : k ≤ 15) :
    (Nat.factorial k) ^ 2 < Nat.factorial (k + 10) := by
  interval_cases k <;> decide

/-- **The sharp bound closes `k ≤ 15` for OQ-02.**  For an admissible pair with
`k ≤ 15` the deficiency never exceeds `9`.  Indeed a deficiency `≥ 10` would give
`(k + 10)! ≤ (k + deficiency n k)! ≤ (k!)²` via `deficiency_add_factorial_le_sq`,
contradicting `(k!)² < (k + 10)!` (`factorial_sq_lt_add_ten_of_k_le_15`).  This is
the sharp elementary resolution of OQ-02 in the range `k ≤ 15`: it rules out the
record-breaking deficiency `≥ 10` uniformly in `n`, extending the
`deficiency ≤ 8`-for-`k ≤ 14` bound of Section XII to cover `k = 15` as well
(where the bound permits deficiency `9` but not `10`). -/
theorem deficiency_le_nine_of_k_le_15 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 15) : deficiency n k ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hsharp := deficiency_add_factorial_le_sq hn h
  have hle : Nat.factorial (k + 10) ≤ (Nat.factorial k) ^ 2 :=
    (Nat.factorial_le (by omega)).trans hsharp
  exact absurd hle (not_le.mpr (factorial_sq_lt_add_ten_of_k_le_15 hk))

/-- **Sharpened reduction to `k ≥ 16`.**  `MaximalDeficiencyIs 9` is equivalent to
the open universal bound restricted to `k ≥ 16`: the cases `k ≤ 14` are discharged
by `deficiency_le_eight_of_k_le_14` and the case `k = 15` by the new
`deficiency_le_nine_of_k_le_15`.  Strictly sharper than
`maximalDeficiencyIs_nine_iff_kGe15`; the entire remaining open content of OQ-02
lives at `k ≥ 16`.  (The earlier `k ≥ 15` reduction was not tight because it tracked
the deficiency-`9` frontier `(k!)² < (k + 9)!` rather than the deficiency-`10`
frontier `(k!)² < (k + 10)!` that actually governs the conjecture.) -/
theorem maximalDeficiencyIs_nine_iff_kGe16 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 16 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 15
    · exact deficiency_le_nine_of_k_le_15 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-- **The sharp bound permits deficiency `10` for every `k ≥ 16`.**  For all
`k ≥ 16` one has `(k + 10)! ≤ (k!)²`.  Hence the sharp factorial bound
`deficiency_add_factorial_le_sq` is *consistent with* `deficiency = 10` at every
`k ≥ 16`: it cannot exclude a record-breaking deficiency `≥ 10` there.  Paired with
`factorial_sq_lt_add_ten_of_k_le_15` — whose comparison reverses exactly at
`k = 16` — this shows the elementary sharp bound resolves OQ-02 for *precisely* the
cases `k ≤ 15`, confirming the open frontier `k ≥ 16` is beyond its reach.

Proof by induction from the base `26! ≤ (16!)²`; the inductive step multiplies the
hypothesis `(k + 10)! ≤ (k!)²` by the factor `k + 11 ≤ (k + 1)²`. -/
theorem sharp_bound_permits_deficiency_ten :
    ∀ k, 16 ≤ k → Nat.factorial (k + 10) ≤ (Nat.factorial k) ^ 2 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      have e1 : k + 1 + 10 = (k + 10) + 1 := by omega
      have hstep :
          (k + 11) * Nat.factorial (k + 10) ≤ (k + 1) ^ 2 * (Nat.factorial k) ^ 2 := by
        have h1 : (k + 11) * Nat.factorial (k + 10) ≤ (k + 11) * (Nat.factorial k) ^ 2 :=
          Nat.mul_le_mul le_rfl ih
        have h2 :
            (k + 11) * (Nat.factorial k) ^ 2 ≤ (k + 1) ^ 2 * (Nat.factorial k) ^ 2 :=
          Nat.mul_le_mul (by nlinarith [hk]) le_rfl
        exact h1.trans h2
      calc Nat.factorial (k + 1 + 10)
          = (k + 11) * Nat.factorial (k + 10) := by
              rw [e1, Nat.factorial_succ]
        _ ≤ (k + 1) ^ 2 * (Nat.factorial k) ^ 2 := hstep
        _ = (Nat.factorial (k + 1)) ^ 2 := by rw [Nat.factorial_succ, mul_pow]

/-- **The elementary sharp bound resolves OQ-02 for *exactly* `k ≤ 15`.**  Combining
`deficiency_le_nine_of_k_le_15` (the sharp bound forces `deficiency ≤ 9` when
`k ≤ 15`) with `sharp_bound_permits_deficiency_ten` (the bound is consistent with
`deficiency = 10` once `k ≥ 16`): the `(k!)²` method closes the OQ-02 question for
`k ≤ 15` and is provably powerless for `k ≥ 16`.  Stated as the sharp split of the
finite comparison `(k!)² < (k + 10)!` at the frontier `k = 16`. -/
theorem oq02_frontier_exact (k : ℕ) :
    (k ≤ 15 → (Nat.factorial k) ^ 2 < Nat.factorial (k + 10)) ∧
    (16 ≤ k → Nat.factorial (k + 10) ≤ (Nat.factorial k) ^ 2) :=
  ⟨fun hk => factorial_sq_lt_add_ten_of_k_le_15 hk,
   fun hk => sharp_bound_permits_deficiency_ten k hk⟩

/-
## Section XVI: The window-floor bound and an unconditional (ELS-free) location bound on `n`

Sections IX–X bounded the smooth window product from below using only that every
smooth value **exceeds `k`** (floor `k + 1`).  But the smooth values live in the
length-`k` window `n, n-1, …, n-k+1`, so the *true* floor is the window minimum
`n - k + 1` — attained at the extreme index `i = k - 1` — which is `≥ k + 1` and
grows with `n`.  Feeding this sharper floor into the same distinctness argument
(`prod_range_add_le_prod_of_forall_ge`, already stated for an arbitrary floor `m`)
gives a strictly stronger, **`n`-dependent** bound

    `(n - k + 1).ascFactorial (deficiency n k) ≤ k!`,

which at the boundary `n = 2k` reduces *exactly* to the Section X bound
`(k+1).ascFactorial (deficiency n k) ≤ k!` and is strictly stronger for every
`n > 2k`.

Its qualitative payoff is new to this file: dropping to the crude power form
`(n - k + 1)^{deficiency} ≤ k!` and reading it as a constraint on `n` yields an
**unconditional location bound** — for any target deficiency `d`,

    `d ≤ deficiency n k  ⟹  (n - k + 1)^d ≤ k!`,   i.e.   `n ≤ k - 1 + (k!)^{1/d}`.

This is elementary and `ofReduceBool`-free; it does **not** use the axiomatized ELS
bound `els_upper_bound` (`n ≪ 2^k √k`).  The two are complementary: ELS is uniform
in `d` (it already bounds `n` from `d ≥ 1`, far more tightly for small `d`), whereas
this bound is weak for small `d` but *sharpens as the demanded deficiency grows* —
a record-breaking deficiency `d ≥ 10` forces `(n - k + 1)^{10} ≤ k!`.  Earlier
sessions noted that the only location bound available was the axiomatized ELS
estimate; this shows an unconditional, deficiency-graded location bound exists by
purely elementary means.
-/

/-- **The smooth window product dominates `(n-k+1).ascFactorial (deficiency)`.**
Sharper companion of `ascFactorial_le_smooth_window_prod`: the `deficiency n k`
smooth values are distinct integers each `≥ n - k + 1` (the window minimum, hit at
index `i = k - 1`), so their product is at least the product of the `deficiency`
smallest possible distinct values above the floor `n - k + 1`. -/
theorem windowFloor_ascFactorial_le_smooth_window_prod {n k : ℕ} (hn : 2 * k ≤ n) :
    (n - k + 1).ascFactorial (deficiency n k) ≤
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
  have hTge : ∀ x ∈ T, n - k + 1 ≤ x := by
    intro x hx
    rw [hT, Finset.mem_image] at hx
    obtain ⟨i, hiS, rfl⟩ := hx
    have hik : i < k := Finset.mem_range.mp (Finset.filter_subset _ _ hiS)
    omega
  calc (n - k + 1).ascFactorial (deficiency n k)
      = (n - k + 1).ascFactorial T.card := by rw [hcard, hTcard]
    _ = ∏ j ∈ Finset.range T.card, (n - k + 1 + j) := by rw [Nat.ascFactorial_eq_prod_range]
    _ ≤ ∏ x ∈ T, x := prod_range_add_le_prod_of_forall_ge T hTge
    _ = ∏ i ∈ S, (n - i) := hPeq

/-- **Window-floor ascending-factorial bound.**  For an admissible pair,

    `(n - k + 1).ascFactorial (deficiency n k) ≤ k!`.

This strictly improves the Section X bound `(k+1).ascFactorial (deficiency) ≤ k!`
whenever `n > 2k` (the floor `n - k + 1` exceeds `k + 1`), and coincides with it at
the boundary `n = 2k`.  It follows from `windowFloor_ascFactorial_le_smooth_window_prod`
and `smooth_window_prod_dvd_factorial`. -/
theorem windowFloor_ascFactorial_le_factorial {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) :
    (n - k + 1).ascFactorial (deficiency n k) ≤ Nat.factorial k := by
  have hlow := windowFloor_ascFactorial_le_smooth_window_prod (n := n) (k := k) hn
  have hdvd := smooth_window_prod_dvd_factorial h
  exact hlow.trans (Nat.le_of_dvd (Nat.factorial_pos k) hdvd)

/-- **Window-floor power bound.**  For an admissible pair,

    `(n - k + 1) ^ (deficiency n k) ≤ k!`.

The crude power form of `windowFloor_ascFactorial_le_factorial`, obtained directly
from `Finset.pow_card_le_prod` at the window floor.  Unlike the closed form it reads
cleanly as a constraint on `n`. -/
theorem windowFloor_pow_le_factorial {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) :
    (n - k + 1) ^ deficiency n k ≤ Nat.factorial k := by
  set S := (Finset.range k).filter (fun i => IsKSmooth k (n - i)) with hS
  have hcard : deficiency n k = S.card := rfl
  set P := ∏ i ∈ S, (n - i) with hP
  have hlow : (n - k + 1) ^ S.card ≤ P := by
    apply Finset.pow_card_le_prod
    intro i hi
    have hir : i < k := Finset.mem_range.mp (Finset.filter_subset _ _ hi)
    omega
  have hdvd : P ∣ Nat.factorial k := smooth_window_prod_dvd_factorial h
  have hle : P ≤ Nat.factorial k := Nat.le_of_dvd (Nat.factorial_pos k) hdvd
  calc (n - k + 1) ^ deficiency n k = (n - k + 1) ^ S.card := by rw [hcard]
    _ ≤ P := hlow
    _ ≤ Nat.factorial k := hle

/-- **Unconditional (ELS-free) location bound.**  For an admissible pair and *any*
target deficiency `d ≤ deficiency n k`,

    `(n - k + 1) ^ d ≤ k!`,

so `n ≤ k - 1 + (k!)^{1/d}`: demanding a deficiency of at least `d` caps how large
`n` can be, purely elementarily.  The bound sharpens as the target `d` grows; for a
record-breaking `d ≥ 10` it forces `(n - k + 1)^{10} ≤ k!`.  Independent of the
axiomatized ELS bound `els_upper_bound`. -/
theorem windowFloor_pow_le_factorial_of_le {n k d : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hd : d ≤ deficiency n k) :
    (n - k + 1) ^ d ≤ Nat.factorial k :=
  (Nat.pow_le_pow_right (by omega) hd).trans (windowFloor_pow_le_factorial hn h)

/-- **Boundary consistency.**  At `n = 2k` the window-floor bound
`windowFloor_ascFactorial_le_factorial` is *definitionally* the Section X sharp bound
`deficiency_ascFactorial_le_factorial`, confirming Section XVI strictly generalizes
Section X (equal at the boundary, sharper above it). -/
theorem windowFloor_eq_sharp_bound_at_boundary {k : ℕ} (hk : 1 ≤ k)
    (h : NoSmallPrimeFactors (2 * k) k) :
    (k + 1).ascFactorial (deficiency (2 * k) k) ≤ Nat.factorial k := by
  have hbound := windowFloor_ascFactorial_le_factorial (n := 2 * k) (k := k) (by omega) h
  have hfloor : 2 * k - k + 1 = k + 1 := by omega
  rwa [hfloor] at hbound

/-
## Section XVII: The effective location bound makes each fixed `k` a finite check — closing `k = 16`

The window-floor location bound of Section XVI, `(n - k + 1)^d ≤ k!` for any
`d ≤ deficiency n k`, is **effective**: it bounds `n` above by an *explicit*
computable quantity, `n ≤ k - 1 + (k!)^{1/d}`.  Combined with the admissibility
floor `n ≥ 2k`, this confines every admissible pair with `deficiency ≥ 1` to a
**finite, explicit** window `2k ≤ n < k + k!` (`deficiency_ge_forces_bounded_n`).

This corrects a pessimistic assessment recorded in earlier sessions — that "even
fixed-`k` slices of OQ-02 are not decidable, because the ELS location axiom
`els_upper_bound` has a non-effective constant."  The *elementary* window-floor
bound supplies an effective constant with no analytic input, so each fixed-`k`
slice **is** a finite (in principle decidable) check.  The demand sharpens with the
target deficiency: ruling out a record-breaking `deficiency ≥ 10` at modulus `k`
only requires inspecting the `n` with `(n - k + 1)^{10} ≤ k!` and `2k ≤ n`.

We cash this out concretely at the current open frontier `k = 16`.  A deficiency
`≥ 10` there forces `(n - 15)^{10} ≤ 16! < 22^{10}`, hence `n ≤ 36`; together with
`n ≥ 32` this leaves only `n ∈ {32, 33, 34, 35, 36}`.  Every one of those five
binomials `C(n,16)` is even, so none of the pairs is admissible.  Therefore no
admissible pair at `k = 16` has deficiency exceeding `9`: the sharp factorial
method left `k = 16` open (Section XV), but the *location* bound closes it.  The
elementary resolution of OQ-02 now covers **all `k ≤ 16`**, moving the open
frontier to `k ≥ 17` — one step past the `(k!)²`-method frontier of Section XV.
Like everything since Section V the structural results are `ofReduceBool`-free;
only the five concrete "`2 ∣ C(n,16)`" admissibility facts use `native_decide`
(the naive `Nat.choose` recursion does not reduce under kernel `decide`),
consistent with the file's existing record certificates. -/

/-- **Effective, ELS-free finiteness of each fixed-`k` slice.**  An admissible pair
with a positive deficiency has `n` in the finite, explicit range `2k ≤ n < k + k!`.
The upper bound is purely elementary (the window-floor power bound with `d = 1`),
so — unlike the axiomatized ELS estimate `els_upper_bound` — it gives an *effective*
enclosure: for each fixed `k` only finitely many `n` can host any admissible
deficiency example, making every fixed-`k` slice of OQ-02 a finite check.  (The
enclosure sharpens as the demanded deficiency grows: `d ≤ deficiency n k` forces
`(n - k + 1)^d ≤ k!`.) -/
theorem deficiency_ge_forces_bounded_n {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hpos : 1 ≤ deficiency n k) :
    2 * k ≤ n ∧ n < k + Nat.factorial k := by
  refine ⟨hn, ?_⟩
  have hpow : (n - k + 1) ^ 1 ≤ Nat.factorial k :=
    windowFloor_pow_le_factorial_of_le hn h hpos
  have hself : n - k + 1 ≤ Nat.factorial k := by simpa using hpow
  omega

/-- `16! < 22^10`, the numeric input that pins the `k = 16` window: `(n-15)^{10} ≤ 16!`
forces `n - 15 < 22`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`). -/
theorem factorial_16_lt_22_pow_ten : Nat.factorial 16 < 22 ^ 10 := by decide

/-- For `32 ≤ n ≤ 36` the binomial `C(n,16)` is even, so `2` (a prime `≤ 16`) divides
it — hence such a pair is *not* admissible.  Uses `native_decide` (⇒ `Lean.ofReduceBool`)
because the naive `Nat.choose` recursion is infeasible for kernel `decide`. -/
theorem two_dvd_choose_16_of_range {n : ℕ} (hlo : 32 ≤ n) (hhi : n ≤ 36) :
    2 ∣ Nat.choose n 16 := by
  interval_cases n <;> native_decide

/-- The five small pairs left by the `k = 16` location window are all inadmissible:
`2 ∣ C(n,16)` and `2 ≤ 16`, contradicting `NoSmallPrimeFactors n 16`. -/
theorem not_admissible_k16_of_range {n : ℕ} (hlo : 32 ≤ n) (hhi : n ≤ 36) :
    ¬ NoSmallPrimeFactors n 16 := by
  intro h
  have hdvd : 2 ∣ Nat.choose n 16 := two_dvd_choose_16_of_range hlo hhi
  have := h 2 Nat.prime_two hdvd
  omega

/-- **The location bound closes `k = 16`.**  For an admissible pair with `k = 16`
the deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the
window-floor bound, `(n - 15)^{10} ≤ 16! < 22^{10}`, hence `n ≤ 36`; with the
admissibility floor `n ≥ 32` this leaves only `n ∈ {32,…,36}`, none of which is
admissible (`C(n,16)` is even).  This is exactly the case the `(k!)²` method of
Section XV could not reach — the sharp factorial bound permits deficiency `10` at
`k = 16` (`sharp_bound_permits_deficiency_ten`), but the *location* bound rules it
out. -/
theorem deficiency_le_nine_of_k_eq_16 {n : ℕ} (hn : 32 ≤ n)
    (h : NoSmallPrimeFactors n 16) : deficiency n 16 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 16 + 1) ^ 10 ≤ Nat.factorial 16 :=
    windowFloor_pow_le_factorial_of_le (k := 16) (d := 10) (by omega) h (by omega)
  have hlt : (n - 16 + 1) ^ 10 < 22 ^ 10 := lt_of_le_of_lt hpow factorial_16_lt_22_pow_ten
  have hfloor : n - 16 + 1 < 22 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k16_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 16`.**  Combines the sharp
factorial bound for `k ≤ 15` (`deficiency_le_nine_of_k_le_15`) with the location
bound at `k = 16` (`deficiency_le_nine_of_k_eq_16`).  Strictly extends the
`k ≤ 15` reach of Section XV. -/
theorem deficiency_le_nine_of_k_le_16 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 16) : deficiency n k ≤ 9 := by
  by_cases hk15 : k ≤ 15
  · exact deficiency_le_nine_of_k_le_15 hn h hk15
  · have hk16 : k = 16 := by omega
    subst hk16
    exact deficiency_le_nine_of_k_eq_16 (by omega) h

/-- **Sharpened reduction to `k ≥ 17`.**  `MaximalDeficiencyIs 9` is equivalent to
the open universal bound restricted to `k ≥ 17`: the cases `k ≤ 15` are discharged
by the sharp factorial bound and `k = 16` by the location bound
(`deficiency_le_nine_of_k_le_16`).  Strictly sharper than
`maximalDeficiencyIs_nine_iff_kGe16`; the entire remaining open content of OQ-02
now lives at `k ≥ 17`. -/
theorem maximalDeficiencyIs_nine_iff_kGe17 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 17 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 16
    · exact deficiency_le_nine_of_k_le_16 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-
## Section XVIII: The location bound closes `k = 17` — frontier `k ≥ 17` → `k ≥ 18`

Section XVII cashed out the effective, ELS-free location bound of Section XVI at the
open frontier `k = 16`.  The same mechanism applies verbatim one step further, at
`k = 17`: the demand `deficiency ≥ 10` forces the window-floor power bound
`(n - 16)^{10} ≤ 17!`, and `17! < 29^{10}` (`factorial_17_lt_29_pow_ten`), so
`n - 16 < 29`, i.e. `n ≤ 44`.  With the admissibility floor `n ≥ 34` (`= 2·17`) this
leaves the finite window `n ∈ {34, 35, …, 44}` (eleven values).  Every one of those
eleven binomials `C(n,17)` is even, so `2` — a prime `≤ 17` — divides it and none of
the pairs is admissible.  Hence no admissible pair at `k = 17` has deficiency exceeding
`9`.

Nothing in the `(k!)²` factorial method reaches this: `sharp_bound_permits_deficiency_ten`
already shows that bound permits deficiency `10` for every `k ≥ 16`, so it is powerless at
`k = 17`.  Only the *location* bound closes the slice, exactly as at `k = 16`.  The
elementary resolution of OQ-02 now covers **all `k ≤ 17`**, moving the open frontier to
`k ≥ 18`.  As in Section XVII the structural results are `ofReduceBool`-free; only the
concrete "`2 ∣ C(n,17)`" admissibility facts use `native_decide` (the naive `Nat.choose`
recursion does not reduce under kernel `decide`), consistent with the file's existing
record certificates. -/

/-- `17! < 29^10`, the numeric input that pins the `k = 17` window: `(n-16)^{10} ≤ 17!`
forces `n - 16 < 29`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `17! = 355687428096000 < 420707233300201 = 29^{10}`). -/
theorem factorial_17_lt_29_pow_ten : Nat.factorial 17 < 29 ^ 10 := by decide

/-- For `34 ≤ n ≤ 44` the binomial `C(n,17)` is even, so `2` (a prime `≤ 17`) divides
it — hence such a pair is *not* admissible.  Uses `native_decide` (⇒ `Lean.ofReduceBool`)
because the naive `Nat.choose` recursion is infeasible for kernel `decide`. -/
theorem two_dvd_choose_17_of_range {n : ℕ} (hlo : 34 ≤ n) (hhi : n ≤ 44) :
    2 ∣ Nat.choose n 17 := by
  interval_cases n <;> native_decide

/-- The eleven small pairs left by the `k = 17` location window are all inadmissible:
`2 ∣ C(n,17)` and `2 ≤ 17`, contradicting `NoSmallPrimeFactors n 17`. -/
theorem not_admissible_k17_of_range {n : ℕ} (hlo : 34 ≤ n) (hhi : n ≤ 44) :
    ¬ NoSmallPrimeFactors n 17 := by
  intro h
  have hdvd : 2 ∣ Nat.choose n 17 := two_dvd_choose_17_of_range hlo hhi
  have := h 2 Nat.prime_two hdvd
  omega

/-- **The location bound closes `k = 17`.**  For an admissible pair with `k = 17`
the deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the
window-floor bound, `(n - 16)^{10} ≤ 17! < 29^{10}`, hence `n ≤ 44`; with the
admissibility floor `n ≥ 34` this leaves only `n ∈ {34,…,44}`, none of which is
admissible (`C(n,17)` is even).  As at `k = 16`, the sharp factorial bound permits
deficiency `10` here (`sharp_bound_permits_deficiency_ten`), but the *location* bound
rules it out. -/
theorem deficiency_le_nine_of_k_eq_17 {n : ℕ} (hn : 34 ≤ n)
    (h : NoSmallPrimeFactors n 17) : deficiency n 17 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 17 + 1) ^ 10 ≤ Nat.factorial 17 :=
    windowFloor_pow_le_factorial_of_le (k := 17) (d := 10) (by omega) h (by omega)
  have hlt : (n - 17 + 1) ^ 10 < 29 ^ 10 := lt_of_le_of_lt hpow factorial_17_lt_29_pow_ten
  have hfloor : n - 17 + 1 < 29 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k17_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 17`.**  Combines the location
bound at `k ≤ 16` (`deficiency_le_nine_of_k_le_16`) with the location bound at
`k = 17` (`deficiency_le_nine_of_k_eq_17`).  Strictly extends the `k ≤ 16` reach of
Section XVII. -/
theorem deficiency_le_nine_of_k_le_17 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 17) : deficiency n k ≤ 9 := by
  by_cases hk16 : k ≤ 16
  · exact deficiency_le_nine_of_k_le_16 hn h hk16
  · have hk17 : k = 17 := by omega
    subst hk17
    exact deficiency_le_nine_of_k_eq_17 (by omega) h

/-- **Sharpened reduction to `k ≥ 18`.**  `MaximalDeficiencyIs 9` is equivalent to
the open universal bound restricted to `k ≥ 18`: the cases `k ≤ 16` are discharged
by the sharp/location bounds and `k = 17` by the location bound
(`deficiency_le_nine_of_k_le_17`).  Strictly sharper than
`maximalDeficiencyIs_nine_iff_kGe17`; the entire remaining open content of OQ-02
now lives at `k ≥ 18`. -/
theorem maximalDeficiencyIs_nine_iff_kGe18 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 18 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 17
    · exact deficiency_le_nine_of_k_le_17 hv.1 hv.2 hk
    · exact h n k (by omega) hv
