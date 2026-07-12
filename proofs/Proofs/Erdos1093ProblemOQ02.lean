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

/-- **Well-definedness of the maximal deficiency.**  The value `D` in
`MaximalDeficiencyIs D` is unique: if two constants `D₁, D₂` are both maximal
deficiencies, then `D₁ = D₂`.  Each maximal value is *attained* by some admissible
pair and *dominates* every admissible pair, so `D₁`'s attaining example is bounded by
`D₂` (giving `D₁ ≤ D₂`) and symmetrically `D₂ ≤ D₁`.  In particular the target value
`9` of OQ-02 is the *only* possible answer — `MaximalDeficiencyIs` picks out a single
number — so no rival constant can also satisfy the conjecture's shape.  Pure
consequence of the definition (no Ramsey/prime input), the exact analogue of the
"unique extremal constant" packaging. -/
theorem maximalDeficiencyIs_unique {D₁ D₂ : ℕ}
    (h₁ : MaximalDeficiencyIs D₁) (h₂ : MaximalDeficiencyIs D₂) : D₁ = D₂ := by
  obtain ⟨⟨n₁, k₁, hv₁, he₁⟩, hub₁⟩ := h₁
  obtain ⟨⟨n₂, k₂, hv₂, he₂⟩, hub₂⟩ := h₂
  have hb1 := hub₂ n₁ k₁ hv₁
  have hb2 := hub₁ n₂ k₂ hv₂
  omega

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

/-- **Uniform elementary deficiency ceiling — the transfer principle behind Section XIV.**
For *every* modulus `k` a single factorial comparison `(k!)² < (k + D + 1)!` promotes to a
deficiency ceiling `deficiency n k ≤ D` on every admissible pair `(n, k)` with `n ≥ 2k`.
This is the general form that the record-modulus bound `deficiency_record_le_18` below
instantiates at `k = 28, D = 18` (certificate `(28!)² < 47!`).  It follows in one step from
the sharp closed form `(k + deficiency n k)! ≤ (k!)²` (`deficiency_add_factorial_le_sq`):
if the deficiency exceeded `D` then `D + 1 ≤ deficiency n k`, so by `Nat.factorial_le`
`(k + D + 1)! ≤ (k + deficiency n k)! ≤ (k!)² < (k + D + 1)!`, a contradiction.

The certificate `(k!)² < (k + D + 1)!` is a comparison of two *literal* factorials, which
the kernel reduces (`Nat.factorial` is structural recursion), so every instance is
`Lean.ofReduceBool`-free.  This lemma turns the abstract sharp bound into a reusable,
per-`k`, `decide`-checkable ceiling without re-running the product argument each time; it is
the elementary theory's uniform upper-bound tool.  (It cannot reach the conjectural bound
`9`: for each fixed `D` the certificate eventually *fails* as `k` grows, since `(k!)²` then
overtakes `(k + D + 1)!` — the sharp bound is provably consistent with unboundedly large
deficiency, cf. `sharp_bound_permits_deficiency_ten`.) -/
theorem deficiency_le_of_sq_factorial_lt {n k D : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k)
    (hnum : (Nat.factorial k) ^ 2 < Nat.factorial (k + D + 1)) :
    deficiency n k ≤ D := by
  by_contra hgt
  push_neg at hgt
  have hsq := deficiency_add_factorial_le_sq hn h
  have hmono : Nat.factorial (k + D + 1) ≤ Nat.factorial (k + deficiency n k) :=
    Nat.factorial_le (by omega)
  exact absurd (hmono.trans hsq) (not_le.mpr hnum)

/-- **Explicit deficiency ceiling at the record modulus `k = 28`.**  Every
admissible pair `(n, 28)` has `deficiency n 28 ≤ 18`.  Now a one-line instance of the
uniform transfer principle `deficiency_le_of_sq_factorial_lt` at `k = 28, D = 18`, whose
certificate is the bignum comparison `(28!)² < 47!` (kernel `decide`, so
`Lean.ofReduceBool`-free): a deficiency `≥ 19` would give
`47! ≤ (28 + d)! ≤ (28!)² < 47!`, a contradiction.  The record `(284, 28)` attains `9`, so
the elementary theory still leaves the window `10 ≤ d ≤ 18` open. -/
theorem deficiency_record_le_18 {n : ℕ} (hn : 56 ≤ n)
    (h : NoSmallPrimeFactors n 28) : deficiency n 28 ≤ 18 :=
  deficiency_le_of_sq_factorial_lt (k := 28) (D := 18) (by omega) h (by decide)

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
## Section XVIIB: The uniform location-bound transfer principle behind Sections XVII+

Section XVII closes `k = 16` by a five-step argument, and every later section
(`XVIII, XIX, …`) closing `k = 17, 18, …` repeats it *verbatim* with only three
inputs changed: the modulus `k`, a numeric certificate `k! < M^(d₀+1)`, and the
inadmissibility of the resulting finite window `2k ≤ n ≤ k + M - 2`.  This section
factors that shared skeleton into a single reusable lemma, exactly as
`deficiency_le_of_sq_factorial_lt` (Section XIV) did for the *factorial-ceiling*
method.  The file now carries both uniform elementary tools symmetrically:

  * the **factorial-ceiling** transfer principle (`deficiency_le_of_sq_factorial_lt`),
    from a certificate `(k!)² < (k + D + 1)!`, and
  * the **location-bound** transfer principle (`deficiency_le_of_windowFloor_pow_lt`,
    below), from a certificate `k! < M^(d₀+1)` plus window inadmissibility.

The engine turns each `deficiency_le_nine_of_k_eq_*` proof into a one-line
instantiation; the numeric certificate `k! < M^(d₀+1)` is a literal-factorial /
literal-power comparison the kernel reduces, so the location step itself is always
`Lean.ofReduceBool`-free (only the window's `Nat.choose` admissibility facts use
`native_decide`, as before).
-/

/-- **Uniform location-bound transfer principle.**  Fix a modulus `k` and suppose
the window-floor certificate `k! < M^(d₀+1)` holds *and* every `n` in the finite
window `2k ≤ n ≤ k + M - 2` fails admissibility.  Then every admissible pair `(n, k)`
with `n ≥ 2k` has `deficiency n k ≤ d₀`.

Proof (the shared skeleton of Sections XVII+): a deficiency `≥ d₀ + 1` would force,
via the window-floor power bound `windowFloor_pow_le_factorial_of_le`,
`(n - k + 1)^(d₀+1) ≤ k! < M^(d₀+1)`, hence `n - k + 1 < M`, i.e. `n ≤ k + M - 2`;
with the admissibility floor `2k ≤ n` this lands `n` in the window, contradicting its
inadmissibility.  Independent of the axiomatized ELS bound `els_upper_bound`. -/
theorem deficiency_le_of_windowFloor_pow_lt {n k M d₀ : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k)
    (hnum : Nat.factorial k < M ^ (d₀ + 1))
    (hwin : ∀ m : ℕ, 2 * k ≤ m → m ≤ k + M - 2 → ¬ NoSmallPrimeFactors m k) :
    deficiency n k ≤ d₀ := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - k + 1) ^ (d₀ + 1) ≤ Nat.factorial k :=
    windowFloor_pow_le_factorial_of_le hn h (by omega)
  have hlt : (n - k + 1) ^ (d₀ + 1) < M ^ (d₀ + 1) := lt_of_le_of_lt hpow hnum
  have hfloor : n - k + 1 < M := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge (d₀ + 1)) (not_le.mpr hlt)
  exact hwin n hn (by omega) h

/-- **The record-target specialization.**  The exact shape every `k`-section needs:
from a certificate `k! < M^10` and inadmissibility of the location window
`2k ≤ n ≤ k + M - 2`, no admissible pair at modulus `k` exceeds the record
deficiency `9`.  A one-line corollary of `deficiency_le_of_windowFloor_pow_lt` at
`d₀ = 9`. -/
theorem deficiency_le_nine_of_location {n k M : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k)
    (hnum : Nat.factorial k < M ^ 10)
    (hwin : ∀ m : ℕ, 2 * k ≤ m → m ≤ k + M - 2 → ¬ NoSmallPrimeFactors m k) :
    deficiency n k ≤ 9 :=
  deficiency_le_of_windowFloor_pow_lt hn h hnum hwin

/-- **Certification that the engine reproduces Section XVII.**  An independent
one-line re-derivation of `deficiency_le_nine_of_k_eq_16` through the uniform
`deficiency_le_nine_of_location`, instantiated at `k = 16, M = 22` with the very
same certificate `16! < 22^10` and window facts.  It confirms the transfer principle
subsumes the hand-written per-`k` skeleton (window here: `32 ≤ n ≤ 16 + 22 - 2 = 36`). -/
theorem deficiency_le_nine_of_k_eq_16_via_location {n : ℕ} (hn : 32 ≤ n)
    (h : NoSmallPrimeFactors n 16) : deficiency n 16 ≤ 9 :=
  deficiency_le_nine_of_location (k := 16) (M := 22) (by omega) h
    factorial_16_lt_22_pow_ten
    (fun m hlo hhi => not_admissible_k16_of_range (by omega) (by omega))

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

/-
## Section XIX: The location bound closes `k = 18` — frontier `k ≥ 18` → `k ≥ 19`

Section XVIII cashed out the effective, ELS-free location bound at the open frontier
`k = 17`.  The same mechanism advances one further step, to `k = 18`, but with a new
arithmetic wrinkle that makes the slice *not* a mechanical copy of `k = 17`.  A
deficiency `≥ 10` forces the window-floor power bound `(n - 17)^{10} ≤ 18!`, and
`18! < 39^{10}` (`factorial_18_lt_39_pow_ten`), so `n - 17 < 39`, i.e. `n ≤ 55`.  With
the admissibility floor `n ≥ 36` (`= 2·18`) this leaves the finite window
`n ∈ {36, 37, …, 55}` (twenty values).

Unlike every earlier slice, `C(n,18)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,18)` is odd exactly when the binary digits of `18 = 10010₂` sit
inside those of `n`, which occurs at `n = 50, 51, 54, 55` inside the window, so the
single prime `2` no longer certifies inadmissibility.  It remains true — and this is
what closes the slice — that *some* prime `≤ 18` divides `C(n,18)` for every one of the
twenty values: `2` for the sixteen even ones, and `5` (`n = 50, 51`) or `3`
(`n = 54, 55`) for the four odd ones.  Concretely `2 ∣ C(n,18) ∨ 3 ∣ C(n,18) ∨
5 ∣ C(n,18)` holds throughout the window, so no pair is admissible and no admissible
pair at `k = 18` has deficiency exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice.  The elementary resolution of OQ-02 now covers
**all `k ≤ 18`**, moving the open frontier to `k ≥ 19`.  The structural results remain
`ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `18! < 39^10`, the numeric input that pins the `k = 18` window: `(n-17)^{10} ≤ 18!`
forces `n - 17 < 39`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `18! = 6402373705728000 < 8140406085191601 = 39^{10}`). -/
theorem factorial_18_lt_39_pow_ten : Nat.factorial 18 < 39 ^ 10 := by decide

/-- For `36 ≤ n ≤ 55` some prime `≤ 18` divides `C(n,18)`: `2` for the even values and,
for the four odd binomials `n ∈ {50, 51, 54, 55}`, the prime `5` (`n = 50, 51`) or `3`
(`n = 54, 55`).  Stated as the disjunction `2 ∣ · ∨ 3 ∣ · ∨ 5 ∣ ·`, which holds across
the whole window.  Uses `native_decide` (⇒ `Lean.ofReduceBool`) because the naive
`Nat.choose` recursion is infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_18_of_range {n : ℕ} (hlo : 36 ≤ n) (hhi : n ≤ 55) :
    2 ∣ Nat.choose n 18 ∨ 3 ∣ Nat.choose n 18 ∨ 5 ∣ Nat.choose n 18 := by
  interval_cases n <;> native_decide

/-- The twenty small pairs left by the `k = 18` location window are all inadmissible:
some prime `p ∈ {2, 3, 5}` (each `≤ 18`) divides `C(n,18)`, contradicting
`NoSmallPrimeFactors n 18` (which would force `18 < p`). -/
theorem not_admissible_k18_of_range {n : ℕ} (hlo : 36 ≤ n) (hhi : n ≤ 55) :
    ¬ NoSmallPrimeFactors n 18 := by
  intro h
  rcases smallPrime_dvd_choose_18_of_range hlo hhi with hd | hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 3 Nat.prime_three hd; omega
  · have := h 5 (by norm_num) hd; omega

/-- **The location bound closes `k = 18`.**  For an admissible pair with `k = 18` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 17)^{10} ≤ 18! < 39^{10}`, hence `n ≤ 55`; with the admissibility floor
`n ≥ 36` this leaves only `n ∈ {36,…,55}`, none admissible (some prime `≤ 18` divides
`C(n,18)`, even where `C(n,18)` is odd).  The sharp factorial bound permits deficiency
`10` here (`sharp_bound_permits_deficiency_ten`), but the *location* bound rules it out. -/
theorem deficiency_le_nine_of_k_eq_18 {n : ℕ} (hn : 36 ≤ n)
    (h : NoSmallPrimeFactors n 18) : deficiency n 18 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 18 + 1) ^ 10 ≤ Nat.factorial 18 :=
    windowFloor_pow_le_factorial_of_le (k := 18) (d := 10) (by omega) h (by omega)
  have hlt : (n - 18 + 1) ^ 10 < 39 ^ 10 := lt_of_le_of_lt hpow factorial_18_lt_39_pow_ten
  have hfloor : n - 18 + 1 < 39 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k18_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 18`.**  Combines the location bound at
`k ≤ 17` (`deficiency_le_nine_of_k_le_17`) with the location bound at `k = 18`
(`deficiency_le_nine_of_k_eq_18`).  Strictly extends the `k ≤ 17` reach of Section XVIII. -/
theorem deficiency_le_nine_of_k_le_18 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 18) : deficiency n k ≤ 9 := by
  by_cases hk17 : k ≤ 17
  · exact deficiency_le_nine_of_k_le_17 hn h hk17
  · have hk18 : k = 18 := by omega
    subst hk18
    exact deficiency_le_nine_of_k_eq_18 (by omega) h

/-- **Sharpened reduction to `k ≥ 19`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 19`: the cases `k ≤ 17` are discharged by the
sharp/location bounds and `k = 18` by the location bound (`deficiency_le_nine_of_k_le_18`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe18`; the entire remaining open
content of OQ-02 now lives at `k ≥ 19`. -/
theorem maximalDeficiencyIs_nine_iff_kGe19 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 19 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 18
    · exact deficiency_le_nine_of_k_le_18 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-!
## Section XX: The location bound closes `k = 19` — frontier `k ≥ 19` → `k ≥ 20`

Section XIX cashed out the effective, ELS-free location bound at the open frontier
`k = 18`.  The same mechanism advances one further step, to `k = 19`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 18)^{10} ≤ 19!`, and `19! < 52^{10}`
(`factorial_19_lt_52_pow_ten`), so `n - 18 < 52`, i.e. `n ≤ 69`.  With the admissibility
floor `n ≥ 38` (`= 2·19`) this leaves the finite window `n ∈ {38, 39, …, 69}` (thirty-two
values).

As at `k = 18`, `C(n,19)` is **not** uniformly even on this window: by Kummer/Lucas
`C(n,19)` is odd exactly when the binary digits of `19 = 10011₂` sit inside those of `n`,
which occurs at `n = 51, 55, 59, 63` inside the window, so the single prime `2` no longer
certifies inadmissibility.  It remains true — and this is what closes the slice — that
*some* prime `≤ 19` divides `C(n,19)` for every one of the thirty-two values: `2` for the
twenty-eight even ones, and `3` for all four odd ones (`n = 51, 55, 59, 63` are each
divisible by `3`).  So already the two-prime disjunction `2 ∣ C(n,19) ∨ 3 ∣ C(n,19)`
holds throughout the window — a step *simpler* than `k = 18`, which needed `5` as well —
so no pair is admissible and no admissible pair at `k = 19` has deficiency exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice.  The elementary resolution of OQ-02 now covers
**all `k ≤ 19`**, moving the open frontier to `k ≥ 20`.  The structural results remain
`ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `19! < 52^10`, the numeric input that pins the `k = 19` window: `(n-18)^{10} ≤ 19!`
forces `n - 18 < 52`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `19! = 121645100408832000 < 144555105949057024 = 52^{10}`). -/
theorem factorial_19_lt_52_pow_ten : Nat.factorial 19 < 52 ^ 10 := by decide

/-- For `38 ≤ n ≤ 69` some prime `≤ 19` divides `C(n,19)`: `2` for the even values and,
for the four odd binomials `n ∈ {51, 55, 59, 63}`, the prime `3`.  Stated as the
disjunction `2 ∣ · ∨ 3 ∣ ·`, which holds across the whole window.  Uses `native_decide`
(⇒ `Lean.ofReduceBool`) because the naive `Nat.choose` recursion is infeasible for kernel
`decide`. -/
theorem smallPrime_dvd_choose_19_of_range {n : ℕ} (hlo : 38 ≤ n) (hhi : n ≤ 69) :
    2 ∣ Nat.choose n 19 ∨ 3 ∣ Nat.choose n 19 := by
  interval_cases n <;> native_decide

/-- The thirty-two small pairs left by the `k = 19` location window are all inadmissible:
some prime `p ∈ {2, 3}` (each `≤ 19`) divides `C(n,19)`, contradicting
`NoSmallPrimeFactors n 19` (which would force `19 < p`). -/
theorem not_admissible_k19_of_range {n : ℕ} (hlo : 38 ≤ n) (hhi : n ≤ 69) :
    ¬ NoSmallPrimeFactors n 19 := by
  intro h
  rcases smallPrime_dvd_choose_19_of_range hlo hhi with hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 3 Nat.prime_three hd; omega

/-- **The location bound closes `k = 19`.**  For an admissible pair with `k = 19` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 18)^{10} ≤ 19! < 52^{10}`, hence `n ≤ 69`; with the admissibility floor
`n ≥ 38` this leaves only `n ∈ {38,…,69}`, none admissible (some prime `≤ 19` divides
`C(n,19)`, even where `C(n,19)` is odd).  The sharp factorial bound permits deficiency
`10` here (`sharp_bound_permits_deficiency_ten`), but the *location* bound rules it out. -/
theorem deficiency_le_nine_of_k_eq_19 {n : ℕ} (hn : 38 ≤ n)
    (h : NoSmallPrimeFactors n 19) : deficiency n 19 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 19 + 1) ^ 10 ≤ Nat.factorial 19 :=
    windowFloor_pow_le_factorial_of_le (k := 19) (d := 10) (by omega) h (by omega)
  have hlt : (n - 19 + 1) ^ 10 < 52 ^ 10 := lt_of_le_of_lt hpow factorial_19_lt_52_pow_ten
  have hfloor : n - 19 + 1 < 52 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k19_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 19`.**  Combines the location bound at
`k ≤ 18` (`deficiency_le_nine_of_k_le_18`) with the location bound at `k = 19`
(`deficiency_le_nine_of_k_eq_19`).  Strictly extends the `k ≤ 18` reach of Section XIX. -/
theorem deficiency_le_nine_of_k_le_19 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 19) : deficiency n k ≤ 9 := by
  by_cases hk18 : k ≤ 18
  · exact deficiency_le_nine_of_k_le_18 hn h hk18
  · have hk19 : k = 19 := by omega
    subst hk19
    exact deficiency_le_nine_of_k_eq_19 (by omega) h

/-- **Sharpened reduction to `k ≥ 20`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 20`: the cases `k ≤ 18` are discharged by the
sharp/location bounds and `k = 19` by the location bound (`deficiency_le_nine_of_k_le_19`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe19`; the entire remaining open
content of OQ-02 now lives at `k ≥ 20`. -/
theorem maximalDeficiencyIs_nine_iff_kGe20 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 20 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 19
    · exact deficiency_le_nine_of_k_le_19 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-!
## Section XXI: The location bound closes `k = 20` — frontier `k ≥ 20` → `k ≥ 21`

Section XX cashed out the effective, ELS-free location bound at the open frontier
`k = 19`.  The same mechanism advances one further step, to `k = 20`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 19)^{10} ≤ 20!`, and `20! < 69^{10}`
(`factorial_20_lt_69_pow_ten`), so `n - 19 < 69`, i.e. `n ≤ 87`.  With the admissibility
floor `n ≥ 40` (`= 2·20`) this leaves the finite window `n ∈ {40, 41, …, 87}` (forty-eight
values).

As at `k = 18, 19`, `C(n,20)` is **not** uniformly even on this window: by Kummer/Lucas
`C(n,20)` is odd exactly when the binary digits of `20 = 10100₂` sit inside those of `n`,
which occurs at `n = 52, 53, 54, 55, 60, 61, 62, 63, 84, 85, 86, 87` inside the window, so
the single prime `2` no longer certifies inadmissibility.  It remains true — and this is
what closes the slice — that *some* prime `≤ 20` divides `C(n,20)` for every one of the
forty-eight values: `2` for the thirty-six even ones, and `5` for all twelve odd ones (each
of the odd binomials has `5 ∣ C(n,20)`).  So already the two-prime disjunction
`2 ∣ C(n,20) ∨ 5 ∣ C(n,20)` holds throughout the window — matching the two-prime economy of
`k = 19` (and simpler than `k = 18`, which needed `3` as well) — so no pair is admissible
and no admissible pair at `k = 20` has deficiency exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice.  The elementary resolution of OQ-02 now covers
**all `k ≤ 20`**, moving the open frontier to `k ≥ 21`.  The structural results remain
`ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `20! < 69^10`, the numeric input that pins the `k = 20` window: `(n-19)^{10} ≤ 20!`
forces `n - 19 < 69`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `20! = 2432902008176640000 < 2446194060654759801 = 69^{10}`). -/
theorem factorial_20_lt_69_pow_ten : Nat.factorial 20 < 69 ^ 10 := by decide

/-- For `40 ≤ n ≤ 87` some prime `≤ 20` divides `C(n,20)`: `2` for the even values and,
for the twelve odd binomials `n ∈ {52,53,54,55,60,61,62,63,84,85,86,87}`, the prime `5`.
Stated as the disjunction `2 ∣ · ∨ 5 ∣ ·`, which holds across the whole window.  Uses
`native_decide` (⇒ `Lean.ofReduceBool`) because the naive `Nat.choose` recursion is
infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_20_of_range {n : ℕ} (hlo : 40 ≤ n) (hhi : n ≤ 87) :
    2 ∣ Nat.choose n 20 ∨ 5 ∣ Nat.choose n 20 := by
  interval_cases n <;> native_decide

/-- The forty-eight small pairs left by the `k = 20` location window are all inadmissible:
some prime `p ∈ {2, 5}` (each `≤ 20`) divides `C(n,20)`, contradicting
`NoSmallPrimeFactors n 20` (which would force `20 < p`). -/
theorem not_admissible_k20_of_range {n : ℕ} (hlo : 40 ≤ n) (hhi : n ≤ 87) :
    ¬ NoSmallPrimeFactors n 20 := by
  intro h
  rcases smallPrime_dvd_choose_20_of_range hlo hhi with hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 5 Nat.prime_five hd; omega

/-- **The location bound closes `k = 20`.**  For an admissible pair with `k = 20` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 19)^{10} ≤ 20! < 69^{10}`, hence `n ≤ 87`; with the admissibility floor
`n ≥ 40` this leaves only `n ∈ {40,…,87}`, none admissible (some prime `≤ 20` divides
`C(n,20)`, even where `C(n,20)` is odd).  The sharp factorial bound permits deficiency
`10` here (`sharp_bound_permits_deficiency_ten`), but the *location* bound rules it out. -/
theorem deficiency_le_nine_of_k_eq_20 {n : ℕ} (hn : 40 ≤ n)
    (h : NoSmallPrimeFactors n 20) : deficiency n 20 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 20 + 1) ^ 10 ≤ Nat.factorial 20 :=
    windowFloor_pow_le_factorial_of_le (k := 20) (d := 10) (by omega) h (by omega)
  have hlt : (n - 20 + 1) ^ 10 < 69 ^ 10 := lt_of_le_of_lt hpow factorial_20_lt_69_pow_ten
  have hfloor : n - 20 + 1 < 69 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k20_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 20`.**  Combines the location bound at
`k ≤ 19` (`deficiency_le_nine_of_k_le_19`) with the location bound at `k = 20`
(`deficiency_le_nine_of_k_eq_20`).  Strictly extends the `k ≤ 19` reach of Section XX. -/
theorem deficiency_le_nine_of_k_le_20 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 20) : deficiency n k ≤ 9 := by
  by_cases hk19 : k ≤ 19
  · exact deficiency_le_nine_of_k_le_19 hn h hk19
  · have hk20 : k = 20 := by omega
    subst hk20
    exact deficiency_le_nine_of_k_eq_20 (by omega) h

/-- **Sharpened reduction to `k ≥ 21`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 21`: the cases `k ≤ 19` are discharged by the
sharp/location bounds and `k = 20` by the location bound (`deficiency_le_nine_of_k_le_20`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe20`; the entire remaining open
content of OQ-02 now lives at `k ≥ 21`. -/
theorem maximalDeficiencyIs_nine_iff_kGe21 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 21 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 20
    · exact deficiency_le_nine_of_k_le_20 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-!
## Section XXII: The location bound closes `k = 21` — frontier `k ≥ 21` → `k ≥ 22`

Section XXI cashed out the effective, ELS-free location bound at the open frontier
`k = 20`.  The same mechanism advances one further step, to `k = 21`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 20)^{10} ≤ 21!`, and `21! < 94^{10}`
(`factorial_21_lt_94_pow_ten`), so `n - 20 < 94`, i.e. `n ≤ 113`.  With the admissibility
floor `n ≥ 42` (`= 2·21`) this leaves the finite window `n ∈ {42, 43, …, 113}` (seventy-two
values).

As at `k = 18, 19, 20`, `C(n,21)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,21)` is odd exactly when the binary digits of `21 = 10101₂` sit inside
those of `n`, which occurs at `n = 53, 55, 61, 63, 85, 87, 93, 95` inside the window, so the
single prime `2` no longer certifies inadmissibility.  It remains true — and this is what
closes the slice — that *some* prime `≤ 21` divides `C(n,21)` for every one of the
seventy-two values: `2` for the sixty-four even ones, and `5` for all eight odd ones (each
of the odd binomials has `5 ∣ C(n,21)`).  So already the two-prime disjunction
`2 ∣ C(n,21) ∨ 5 ∣ C(n,21)` holds throughout the window — matching the two-prime economy of
`k = 19` and `k = 20` (and simpler than `k = 18`, which needed `3` as well) — so no pair is
admissible and no admissible pair at `k = 21` has deficiency exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice.  The elementary resolution of OQ-02 now covers
**all `k ≤ 21`**, moving the open frontier to `k ≥ 22`.  The structural results remain
`ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `21! < 94^10`, the numeric input that pins the `k = 21` window: `(n-20)^{10} ≤ 21!`
forces `n - 20 < 94`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `21! = 51090942171709440000 < 53861511409489970176 = 94^{10}`). -/
theorem factorial_21_lt_94_pow_ten : Nat.factorial 21 < 94 ^ 10 := by decide

/-- For `42 ≤ n ≤ 113` some prime `≤ 21` divides `C(n,21)`: `2` for the even values and,
for the eight odd binomials `n ∈ {53,55,61,63,85,87,93,95}`, the prime `5`.  Stated as the
disjunction `2 ∣ · ∨ 5 ∣ ·`, which holds across the whole window.  Uses `native_decide`
(⇒ `Lean.ofReduceBool`) because the naive `Nat.choose` recursion is infeasible for kernel
`decide`. -/
theorem smallPrime_dvd_choose_21_of_range {n : ℕ} (hlo : 42 ≤ n) (hhi : n ≤ 113) :
    2 ∣ Nat.choose n 21 ∨ 5 ∣ Nat.choose n 21 := by
  interval_cases n <;> native_decide

/-- The seventy-two small pairs left by the `k = 21` location window are all inadmissible:
some prime `p ∈ {2, 5}` (each `≤ 21`) divides `C(n,21)`, contradicting
`NoSmallPrimeFactors n 21` (which would force `21 < p`). -/
theorem not_admissible_k21_of_range {n : ℕ} (hlo : 42 ≤ n) (hhi : n ≤ 113) :
    ¬ NoSmallPrimeFactors n 21 := by
  intro h
  rcases smallPrime_dvd_choose_21_of_range hlo hhi with hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 5 Nat.prime_five hd; omega

/-- **The location bound closes `k = 21`.**  For an admissible pair with `k = 21` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 20)^{10} ≤ 21! < 94^{10}`, hence `n ≤ 113`; with the admissibility floor
`n ≥ 42` this leaves only `n ∈ {42,…,113}`, none admissible (some prime `≤ 21` divides
`C(n,21)`, even where `C(n,21)` is odd).  The sharp factorial bound permits deficiency
`10` here (`sharp_bound_permits_deficiency_ten`), but the *location* bound rules it out. -/
theorem deficiency_le_nine_of_k_eq_21 {n : ℕ} (hn : 42 ≤ n)
    (h : NoSmallPrimeFactors n 21) : deficiency n 21 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 21 + 1) ^ 10 ≤ Nat.factorial 21 :=
    windowFloor_pow_le_factorial_of_le (k := 21) (d := 10) (by omega) h (by omega)
  have hlt : (n - 21 + 1) ^ 10 < 94 ^ 10 := lt_of_le_of_lt hpow factorial_21_lt_94_pow_ten
  have hfloor : n - 21 + 1 < 94 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k21_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 21`.**  Combines the location bound at
`k ≤ 20` (`deficiency_le_nine_of_k_le_20`) with the location bound at `k = 21`
(`deficiency_le_nine_of_k_eq_21`).  Strictly extends the `k ≤ 20` reach of Section XXI. -/
theorem deficiency_le_nine_of_k_le_21 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 21) : deficiency n k ≤ 9 := by
  by_cases hk20 : k ≤ 20
  · exact deficiency_le_nine_of_k_le_20 hn h hk20
  · have hk21 : k = 21 := by omega
    subst hk21
    exact deficiency_le_nine_of_k_eq_21 (by omega) h

/-- **Sharpened reduction to `k ≥ 22`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 22`: the cases `k ≤ 20` are discharged by the
sharp/location bounds and `k = 21` by the location bound (`deficiency_le_nine_of_k_le_21`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe21`; the entire remaining open
content of OQ-02 now lives at `k ≥ 22`. -/
theorem maximalDeficiencyIs_nine_iff_kGe22 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 22 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 21
    · exact deficiency_le_nine_of_k_le_21 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-!
## Section XXIII: The location bound closes `k = 22` — frontier `k ≥ 22` → `k ≥ 23`

Section XXII cashed out the effective, ELS-free location bound at the open frontier
`k = 21`.  The same mechanism advances one further step, to `k = 22`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 21)^{10} ≤ 22!`, and `22! < 128^{10}`
(`factorial_22_lt_128_pow_ten`), so `n - 21 < 128`, i.e. `n ≤ 148`.  With the admissibility
floor `n ≥ 44` (`= 2·22`) this leaves the finite window `n ∈ {44, 45, …, 148}` (one hundred
and five values).

As at `k = 18, …, 21`, `C(n,22)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,22)` is odd exactly when the binary digits of `22 = 10110₂` sit inside
those of `n`, which occurs at `n = 54, 55, 62, 63, 86, 87, 94, 95, 118, 119, 126, 127`
inside the window, so the single prime `2` no longer certifies inadmissibility.  It remains
true — and this is what closes the slice — that *some* prime `≤ 22` divides `C(n,22)` for
every one of the one hundred and five values: `2` for the ninety-three even ones, and `3`
for all twelve odd ones (each of the odd binomials has `3 ∣ C(n,22)`).  So already the
two-prime disjunction `2 ∣ C(n,22) ∨ 3 ∣ C(n,22)` holds throughout the window — matching
the two-prime economy of `k = 19, 20, 21` (and simpler than `k = 18`, which needed `5` as
well) — so no pair is admissible and no admissible pair at `k = 22` has deficiency exceeding
`9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice.  The elementary resolution of OQ-02 now covers
**all `k ≤ 22`**, moving the open frontier to `k ≥ 23`.  The structural results remain
`ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `22! < 128^10`, the numeric input that pins the `k = 22` window: `(n-21)^{10} ≤ 22!`
forces `n - 21 < 128`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `22! = 1124000727777607680000 < 1180591620717411303424 = 128^{10}`). -/
theorem factorial_22_lt_128_pow_ten : Nat.factorial 22 < 128 ^ 10 := by decide

/-- For `44 ≤ n ≤ 148` some prime `≤ 22` divides `C(n,22)`: `2` for the even values and,
for the twelve odd binomials `n ∈ {54,55,62,63,86,87,94,95,118,119,126,127}`, the prime `3`.
Stated as the disjunction `2 ∣ · ∨ 3 ∣ ·`, which holds across the whole window.  Uses
`native_decide` (⇒ `Lean.ofReduceBool`) because the naive `Nat.choose` recursion is
infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_22_of_range {n : ℕ} (hlo : 44 ≤ n) (hhi : n ≤ 148) :
    2 ∣ Nat.choose n 22 ∨ 3 ∣ Nat.choose n 22 := by
  interval_cases n <;> native_decide

/-- The one hundred and five small pairs left by the `k = 22` location window are all
inadmissible: some prime `p ∈ {2, 3}` (each `≤ 22`) divides `C(n,22)`, contradicting
`NoSmallPrimeFactors n 22` (which would force `22 < p`). -/
theorem not_admissible_k22_of_range {n : ℕ} (hlo : 44 ≤ n) (hhi : n ≤ 148) :
    ¬ NoSmallPrimeFactors n 22 := by
  intro h
  rcases smallPrime_dvd_choose_22_of_range hlo hhi with hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 3 Nat.prime_three hd; omega

/-- **The location bound closes `k = 22`.**  For an admissible pair with `k = 22` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 21)^{10} ≤ 22! < 128^{10}`, hence `n ≤ 148`; with the admissibility floor
`n ≥ 44` this leaves only `n ∈ {44,…,148}`, none admissible (some prime `≤ 22` divides
`C(n,22)`, even where `C(n,22)` is odd).  The sharp factorial bound permits deficiency
`10` here (`sharp_bound_permits_deficiency_ten`), but the *location* bound rules it out. -/
theorem deficiency_le_nine_of_k_eq_22 {n : ℕ} (hn : 44 ≤ n)
    (h : NoSmallPrimeFactors n 22) : deficiency n 22 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 22 + 1) ^ 10 ≤ Nat.factorial 22 :=
    windowFloor_pow_le_factorial_of_le (k := 22) (d := 10) (by omega) h (by omega)
  have hlt : (n - 22 + 1) ^ 10 < 128 ^ 10 := lt_of_le_of_lt hpow factorial_22_lt_128_pow_ten
  have hfloor : n - 22 + 1 < 128 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k22_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 22`.**  Combines the location bound at
`k ≤ 21` (`deficiency_le_nine_of_k_le_21`) with the location bound at `k = 22`
(`deficiency_le_nine_of_k_eq_22`).  Strictly extends the `k ≤ 21` reach of Section XXII. -/
theorem deficiency_le_nine_of_k_le_22 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 22) : deficiency n k ≤ 9 := by
  by_cases hk21 : k ≤ 21
  · exact deficiency_le_nine_of_k_le_21 hn h hk21
  · have hk22 : k = 22 := by omega
    subst hk22
    exact deficiency_le_nine_of_k_eq_22 (by omega) h

/-- **Sharpened reduction to `k ≥ 23`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 23`: the cases `k ≤ 21` are discharged by the
sharp/location bounds and `k = 22` by the location bound (`deficiency_le_nine_of_k_le_22`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe22`; the entire remaining open
content of OQ-02 now lives at `k ≥ 23`. -/
theorem maximalDeficiencyIs_nine_iff_kGe23 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 23 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 22
    · exact deficiency_le_nine_of_k_le_22 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-!
## Section XXIV: The location bound closes `k = 23` — frontier `k ≥ 23` → `k ≥ 24`

Section XXIII cashed out the effective, ELS-free location bound at the open frontier
`k = 22`.  The same mechanism advances one further step, to `k = 23`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 22)^{10} ≤ 23!`, and `23! < 175^{10}`
(`factorial_23_lt_175_pow_ten`), so `n - 22 < 175`, i.e. `n ≤ 196`.  With the admissibility
floor `n ≥ 46` (`= 2·23`) this leaves the finite window `n ∈ {46, 47, …, 196}` (one hundred
and fifty-one values).

As at `k = 18, …, 22`, `C(n,23)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,23)` is odd exactly when the binary digits of `23 = 10111₂` sit inside
those of `n`, which occurs at `n = 55, 63, 87, 95, 119, 127, 151, 159, 183, 191` inside the
window, so the single prime `2` no longer certifies inadmissibility.  It remains true — and
this is what closes the slice — that *some* prime `≤ 23` divides `C(n,23)` for every one of
the one hundred and fifty-one values: `2` for the one hundred and forty-one even ones, and
`5` for all ten odd ones (each of the odd binomials has `5 ∣ C(n,23)`).  So already the
two-prime disjunction `2 ∣ C(n,23) ∨ 5 ∣ C(n,23)` holds throughout the window — matching
the two-prime economy of `k = 19, 20, 21` (`5` here as at `k = 20, 21`, versus `3` at
`k = 22`) — so no pair is admissible and no admissible pair at `k = 23` has deficiency
exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice.  The elementary resolution of OQ-02 now covers
**all `k ≤ 23`**, moving the open frontier to `k ≥ 24`.  The structural results remain
`ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `23! < 175^10`, the numeric input that pins the `k = 23` window: `(n-22)^{10} ≤ 23!`
forces `n - 22 < 175`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `23! = 25852016738884976640000 < 26938938999176025390625 = 175^{10}`). -/
theorem factorial_23_lt_175_pow_ten : Nat.factorial 23 < 175 ^ 10 := by decide

/-- For `46 ≤ n ≤ 196` some prime `≤ 23` divides `C(n,23)`: `2` for the even values and,
for the ten odd binomials `n ∈ {55,63,87,95,119,127,151,159,183,191}`, the prime `5`.
Stated as the disjunction `2 ∣ · ∨ 5 ∣ ·`, which holds across the whole window.  Uses
`native_decide` (⇒ `Lean.ofReduceBool`) because the naive `Nat.choose` recursion is
infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_23_of_range {n : ℕ} (hlo : 46 ≤ n) (hhi : n ≤ 196) :
    2 ∣ Nat.choose n 23 ∨ 5 ∣ Nat.choose n 23 := by
  interval_cases n <;> native_decide

/-- The one hundred and fifty-one small pairs left by the `k = 23` location window are all
inadmissible: some prime `p ∈ {2, 5}` (each `≤ 23`) divides `C(n,23)`, contradicting
`NoSmallPrimeFactors n 23` (which would force `23 < p`). -/
theorem not_admissible_k23_of_range {n : ℕ} (hlo : 46 ≤ n) (hhi : n ≤ 196) :
    ¬ NoSmallPrimeFactors n 23 := by
  intro h
  rcases smallPrime_dvd_choose_23_of_range hlo hhi with hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 5 Nat.prime_five hd; omega

/-- **The location bound closes `k = 23`.**  For an admissible pair with `k = 23` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 22)^{10} ≤ 23! < 175^{10}`, hence `n ≤ 196`; with the admissibility floor
`n ≥ 46` this leaves only `n ∈ {46,…,196}`, none admissible (some prime `≤ 23` divides
`C(n,23)`, even where `C(n,23)` is odd).  The sharp factorial bound permits deficiency
`10` here (`sharp_bound_permits_deficiency_ten`), but the *location* bound rules it out. -/
theorem deficiency_le_nine_of_k_eq_23 {n : ℕ} (hn : 46 ≤ n)
    (h : NoSmallPrimeFactors n 23) : deficiency n 23 ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - 23 + 1) ^ 10 ≤ Nat.factorial 23 :=
    windowFloor_pow_le_factorial_of_le (k := 23) (d := 10) (by omega) h (by omega)
  have hlt : (n - 23 + 1) ^ 10 < 175 ^ 10 := lt_of_le_of_lt hpow factorial_23_lt_175_pow_ten
  have hfloor : n - 23 + 1 < 175 := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  exact not_admissible_k23_of_range (n := n) (by omega) (by omega) h

/-- **Elementary resolution of OQ-02 for all `k ≤ 23`.**  Combines the location bound at
`k ≤ 22` (`deficiency_le_nine_of_k_le_22`) with the location bound at `k = 23`
(`deficiency_le_nine_of_k_eq_23`).  Strictly extends the `k ≤ 22` reach of Section XXIII. -/
theorem deficiency_le_nine_of_k_le_23 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 23) : deficiency n k ≤ 9 := by
  by_cases hk22 : k ≤ 22
  · exact deficiency_le_nine_of_k_le_22 hn h hk22
  · have hk23 : k = 23 := by omega
    subst hk23
    exact deficiency_le_nine_of_k_eq_23 (by omega) h

/-- **Sharpened reduction to `k ≥ 24`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 24`: the cases `k ≤ 22` are discharged by the
sharp/location bounds and `k = 23` by the location bound (`deficiency_le_nine_of_k_le_23`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe23`; the entire remaining open
content of OQ-02 now lives at `k ≥ 24`. -/
theorem maximalDeficiencyIs_nine_iff_kGe24 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 24 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 23
    · exact deficiency_le_nine_of_k_le_23 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-
## Section XXV: The location bound closes `k = 24` — frontier `k ≥ 24` → `k ≥ 25`

Section XXIV cashed out the effective, ELS-free location bound at the open frontier
`k = 23`.  The same mechanism advances one further step, to `k = 24`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 23)^{10} ≤ 24!`, and `24! < 240^{10}`
(`factorial_24_lt_240_pow_ten`), so `n - 23 < 240`, i.e. `n ≤ 262`.  With the admissibility
floor `n ≥ 48` (`= 2·24`) this leaves the finite window `n ∈ {48, 49, …, 262}` (two hundred
and fifteen values).

As at `k = 18, …, 23`, `C(n,24)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,24)` is odd exactly when the binary digits of `24 = 11000₂` sit inside
those of `n`, which happens for fifty-six values of `n` in the window, so the single prime
`2` no longer certifies inadmissibility.  It remains true — and this is what closes the
slice — that *some* prime `≤ 24` divides `C(n,24)` for every one of the two hundred and
fifteen values: `2` for the one hundred and fifty-nine even ones, `3` for all but two of
the fifty-six odd ones, and `5` for the two remaining odd exceptions `n = 159, 186`.  So
already the three-prime disjunction `2 ∣ C(n,24) ∨ 3 ∣ C(n,24) ∨ 5 ∣ C(n,24)` holds
throughout the window — one prime richer than the two-prime economy of `k = 19, …, 23`,
reflecting that no two primes `≤ 24` suffice here — so no pair is admissible and no
admissible pair at `k = 24` has deficiency exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice, through the uniform engine
`deficiency_le_nine_of_location` (Section XVIIB).  The elementary resolution of OQ-02 now
covers **all `k ≤ 24`**, moving the open frontier to `k ≥ 25`.  The structural results
remain `ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `24! < 240^10`, the numeric input that pins the `k = 24` window: `(n-23)^{10} ≤ 24!`
forces `n - 23 < 240`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `24! = 620448401733239439360000 < 634033809653760000000000 = 240^{10}`). -/
theorem factorial_24_lt_240_pow_ten : Nat.factorial 24 < 240 ^ 10 := by decide

/-- For `48 ≤ n ≤ 262` some prime `≤ 24` divides `C(n,24)`: `2` for the even values, `3`
for all but two of the odd binomials, and `5` for the two remaining odd exceptions
`n ∈ {159, 186}`.  Stated as the disjunction `2 ∣ · ∨ 3 ∣ · ∨ 5 ∣ ·`, which holds across
the whole window.  Uses `native_decide` (⇒ `Lean.ofReduceBool`) because the naive
`Nat.choose` recursion is infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_24_of_range {n : ℕ} (hlo : 48 ≤ n) (hhi : n ≤ 262) :
    2 ∣ Nat.choose n 24 ∨ 3 ∣ Nat.choose n 24 ∨ 5 ∣ Nat.choose n 24 := by
  interval_cases n <;> native_decide

/-- The two hundred and fifteen small pairs left by the `k = 24` location window are all
inadmissible: some prime `p ∈ {2, 3, 5}` (each `≤ 24`) divides `C(n,24)`, contradicting
`NoSmallPrimeFactors n 24` (which would force `24 < p`). -/
theorem not_admissible_k24_of_range {n : ℕ} (hlo : 48 ≤ n) (hhi : n ≤ 262) :
    ¬ NoSmallPrimeFactors n 24 := by
  intro h
  rcases smallPrime_dvd_choose_24_of_range hlo hhi with hd | hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 3 Nat.prime_three hd; omega
  · have := h 5 Nat.prime_five hd; omega

/-- **The location bound closes `k = 24`.**  For an admissible pair with `k = 24` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 23)^{10} ≤ 24! < 240^{10}`, hence `n ≤ 262`; with the admissibility floor
`n ≥ 48` this leaves only `n ∈ {48,…,262}`, none admissible (some prime `≤ 24` divides
`C(n,24)`, even where `C(n,24)` is odd).  A one-line instantiation of the uniform engine
`deficiency_le_nine_of_location` at `k = 24, M = 240`. -/
theorem deficiency_le_nine_of_k_eq_24 {n : ℕ} (hn : 48 ≤ n)
    (h : NoSmallPrimeFactors n 24) : deficiency n 24 ≤ 9 :=
  deficiency_le_nine_of_location (k := 24) (M := 240) (by omega) h
    factorial_24_lt_240_pow_ten
    (fun m hlo hhi => not_admissible_k24_of_range (by omega) (by omega))

/-- **Elementary resolution of OQ-02 for all `k ≤ 24`.**  Combines the location bound at
`k ≤ 23` (`deficiency_le_nine_of_k_le_23`) with the location bound at `k = 24`
(`deficiency_le_nine_of_k_eq_24`).  Strictly extends the `k ≤ 23` reach of Section XXIV. -/
theorem deficiency_le_nine_of_k_le_24 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 24) : deficiency n k ≤ 9 := by
  by_cases hk23 : k ≤ 23
  · exact deficiency_le_nine_of_k_le_23 hn h hk23
  · have hk24 : k = 24 := by omega
    subst hk24
    exact deficiency_le_nine_of_k_eq_24 (by omega) h

/-- **Sharpened reduction to `k ≥ 25`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 25`: the cases `k ≤ 23` are discharged by the
sharp/location bounds and `k = 24` by the location bound (`deficiency_le_nine_of_k_le_24`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe24`; the entire remaining open
content of OQ-02 now lives at `k ≥ 25`. -/
theorem maximalDeficiencyIs_nine_iff_kGe25 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 25 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 24
    · exact deficiency_le_nine_of_k_le_24 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-
## Section XXVI: The location bound closes `k = 25` — frontier `k ≥ 25` → `k ≥ 26`

Section XXV cashed out the effective, ELS-free location bound at the open frontier
`k = 24`.  The same mechanism advances one further step, to `k = 25`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 24)^{10} ≤ 25!`, and `25! < 331^{10}`
(`factorial_25_lt_331_pow_ten`), so `n - 24 < 331`, i.e. `n ≤ 354`.  With the admissibility
floor `n ≥ 50` (`= 2·25`) this leaves the finite window `n ∈ {50, 51, …, 354}` (three
hundred and five values).

As at `k = 18, …, 24`, `C(n,25)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,25)` is odd exactly when the binary digits of `25 = 11001₂` sit inside
those of `n`, which happens for forty values of `n` in the window, so the single prime `2`
no longer certifies inadmissibility.  It remains true — and this is what closes the slice —
that *some* prime `≤ 25` divides `C(n,25)` for every one of the three hundred and five
values: `2` for the two hundred and sixty-five even ones, `3` for all but two of the forty
odd ones, `7` for the odd exception `n = 349`, and `11` for the last odd exception
`n = 187` (which no prime `≤ 7` reaches).  So already the four-prime disjunction
`2 ∣ C(n,25) ∨ 3 ∣ C(n,25) ∨ 7 ∣ C(n,25) ∨ 11 ∣ C(n,25)` holds throughout the window —
one convenient certificate (`5` is now dispensable, while a prime as large as `11` is needed
to catch `n = 187`), reflecting that the two-prime economy of the earlier slices no longer
suffices — so no pair is admissible and no admissible pair at `k = 25` has deficiency
exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice, through the uniform engine
`deficiency_le_nine_of_location` (Section XVIIB).  The elementary resolution of OQ-02 now
covers **all `k ≤ 25`**, moving the open frontier to `k ≥ 26`.  The structural results
remain `ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `25! < 331^10`, the numeric input that pins the `k = 25` window: `(n-24)^{10} ≤ 25!`
forces `n - 24 < 331`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `25! = 15511210043330985984000000 <
15786284949774657045043801 = 331^{10}`). -/
theorem factorial_25_lt_331_pow_ten : Nat.factorial 25 < 331 ^ 10 := by decide

/-- For `50 ≤ n ≤ 354` some prime `≤ 25` divides `C(n,25)`: `2` for the even values, `3`
for all but two of the odd binomials, `7` for the odd exception `n = 349`, and `11` for the
last odd exception `n = 187`.  Stated as the disjunction `2 ∣ · ∨ 3 ∣ · ∨ 7 ∣ · ∨ 11 ∣ ·`,
which holds across the whole window.  Uses `native_decide` (⇒ `Lean.ofReduceBool`) because
the naive `Nat.choose` recursion is infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_25_of_range {n : ℕ} (hlo : 50 ≤ n) (hhi : n ≤ 354) :
    2 ∣ Nat.choose n 25 ∨ 3 ∣ Nat.choose n 25 ∨ 7 ∣ Nat.choose n 25 ∨
      11 ∣ Nat.choose n 25 := by
  interval_cases n <;> native_decide

/-- The three hundred and five small pairs left by the `k = 25` location window are all
inadmissible: some prime `p ∈ {2, 3, 7, 11}` (each `≤ 25`) divides `C(n,25)`, contradicting
`NoSmallPrimeFactors n 25` (which would force `25 < p`). -/
theorem not_admissible_k25_of_range {n : ℕ} (hlo : 50 ≤ n) (hhi : n ≤ 354) :
    ¬ NoSmallPrimeFactors n 25 := by
  intro h
  rcases smallPrime_dvd_choose_25_of_range hlo hhi with hd | hd | hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 3 Nat.prime_three hd; omega
  · have := h 7 (by norm_num) hd; omega
  · have := h 11 (by norm_num) hd; omega

/-- **The location bound closes `k = 25`.**  For an admissible pair with `k = 25` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 24)^{10} ≤ 25! < 331^{10}`, hence `n ≤ 354`; with the admissibility floor
`n ≥ 50` this leaves only `n ∈ {50,…,354}`, none admissible (some prime `≤ 25` divides
`C(n,25)`, even where `C(n,25)` is odd).  A one-line instantiation of the uniform engine
`deficiency_le_nine_of_location` at `k = 25, M = 331`. -/
theorem deficiency_le_nine_of_k_eq_25 {n : ℕ} (hn : 50 ≤ n)
    (h : NoSmallPrimeFactors n 25) : deficiency n 25 ≤ 9 :=
  deficiency_le_nine_of_location (k := 25) (M := 331) (by omega) h
    factorial_25_lt_331_pow_ten
    (fun m hlo hhi => not_admissible_k25_of_range (by omega) (by omega))

/-- **Elementary resolution of OQ-02 for all `k ≤ 25`.**  Combines the location bound at
`k ≤ 24` (`deficiency_le_nine_of_k_le_24`) with the location bound at `k = 25`
(`deficiency_le_nine_of_k_eq_25`).  Strictly extends the `k ≤ 24` reach of Section XXV. -/
theorem deficiency_le_nine_of_k_le_25 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 25) : deficiency n k ≤ 9 := by
  by_cases hk24 : k ≤ 24
  · exact deficiency_le_nine_of_k_le_24 hn h hk24
  · have hk25 : k = 25 := by omega
    subst hk25
    exact deficiency_le_nine_of_k_eq_25 (by omega) h

/-- **Sharpened reduction to `k ≥ 26`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 26`: the cases `k ≤ 24` are discharged by the
sharp/location bounds and `k = 25` by the location bound (`deficiency_le_nine_of_k_le_25`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe25`; the entire remaining open
content of OQ-02 now lives at `k ≥ 26`. -/
theorem maximalDeficiencyIs_nine_iff_kGe26 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 26 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 25
    · exact deficiency_le_nine_of_k_le_25 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-
## Section XXVII: The location bound closes `k = 26` — frontier `k ≥ 26` → `k ≥ 27`

Section XXVI cashed out the effective, ELS-free location bound at the open frontier
`k = 25`.  The same mechanism advances one further step, to `k = 26`.  A deficiency
`≥ 10` forces the window-floor power bound `(n - 25)^{10} ≤ 26!`, and `26! < 458^{10}`
(`factorial_26_lt_458_pow_ten`), so `n - 25 < 458`, i.e. `n ≤ 482`.  With the admissibility
floor `n ≥ 52` (`= 2·26`) this leaves the finite window `n ∈ {52, 53, …, 482}` (four
hundred and thirty-one values).

As at `k = 18, …, 25`, `C(n,26)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,26)` is odd exactly when the binary digits of `26 = 11010₂` sit inside
those of `n`, which happens for fifty-six values of `n` in the window, so the single prime
`2` no longer certifies inadmissibility.  It remains true — and this is what closes the
slice — that *some* prime `≤ 26` divides `C(n,26)` for every one of the four hundred and
thirty-one values: `2` for the three hundred and seventy-five even ones, `3` for all but one
of the fifty-six odd ones, and `5` for the single odd exception `n = 350` (which no prime
`≤ 3` reaches).  So already the three-prime disjunction
`2 ∣ C(n,26) ∨ 3 ∣ C(n,26) ∨ 5 ∣ C(n,26)` holds throughout the window — a tighter
certificate than the `k = 25` slice needed (there a prime as large as `11` was required),
the wider window at `k = 26` nonetheless yielding the fewest exceptional residues yet — so no
pair is admissible and no admissible pair at `k = 26` has deficiency exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice, through the uniform engine
`deficiency_le_nine_of_location` (Section XVIIB).  The elementary resolution of OQ-02 now
covers **all `k ≤ 26`**, moving the open frontier to `k ≥ 27`.  The structural results
remain `ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `26! < 458^10`, the numeric input that pins the `k = 26` window: `(n-25)^{10} ≤ 26!`
forces `n - 25 < 458`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `26! = 403291461126605635584000000 <
406120376413199518554317824 = 458^{10}`; and `458` is sharp: `457^{10} =
397339737654378065640319249 ≤ 26!`). -/
theorem factorial_26_lt_458_pow_ten : Nat.factorial 26 < 458 ^ 10 := by decide

/-- For `52 ≤ n ≤ 482` some prime `≤ 26` divides `C(n,26)`: `2` for the even values, `3`
for all but one of the odd binomials, and `5` for the odd exception `n = 350`.  Stated as
the disjunction `2 ∣ · ∨ 3 ∣ · ∨ 5 ∣ ·`, which holds across the whole window.  Uses
`native_decide` (⇒ `Lean.ofReduceBool`) because the naive `Nat.choose` recursion is
infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_26_of_range {n : ℕ} (hlo : 52 ≤ n) (hhi : n ≤ 482) :
    2 ∣ Nat.choose n 26 ∨ 3 ∣ Nat.choose n 26 ∨ 5 ∣ Nat.choose n 26 := by
  interval_cases n <;> native_decide

/-- The four hundred and thirty-one small pairs left by the `k = 26` location window are all
inadmissible: some prime `p ∈ {2, 3, 5}` (each `≤ 26`) divides `C(n,26)`, contradicting
`NoSmallPrimeFactors n 26` (which would force `26 < p`). -/
theorem not_admissible_k26_of_range {n : ℕ} (hlo : 52 ≤ n) (hhi : n ≤ 482) :
    ¬ NoSmallPrimeFactors n 26 := by
  intro h
  rcases smallPrime_dvd_choose_26_of_range hlo hhi with hd | hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 3 Nat.prime_three hd; omega
  · have := h 5 (by norm_num) hd; omega

/-- **The location bound closes `k = 26`.**  For an admissible pair with `k = 26` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 25)^{10} ≤ 26! < 458^{10}`, hence `n ≤ 482`; with the admissibility floor
`n ≥ 52` this leaves only `n ∈ {52,…,482}`, none admissible (some prime `≤ 26` divides
`C(n,26)`, even where `C(n,26)` is odd).  A one-line instantiation of the uniform engine
`deficiency_le_nine_of_location` at `k = 26, M = 458`. -/
theorem deficiency_le_nine_of_k_eq_26 {n : ℕ} (hn : 52 ≤ n)
    (h : NoSmallPrimeFactors n 26) : deficiency n 26 ≤ 9 :=
  deficiency_le_nine_of_location (k := 26) (M := 458) (by omega) h
    factorial_26_lt_458_pow_ten
    (fun m hlo hhi => not_admissible_k26_of_range (by omega) (by omega))

/-- **Elementary resolution of OQ-02 for all `k ≤ 26`.**  Combines the location bound at
`k ≤ 25` (`deficiency_le_nine_of_k_le_25`) with the location bound at `k = 26`
(`deficiency_le_nine_of_k_eq_26`).  Strictly extends the `k ≤ 25` reach of Section XXVI. -/
theorem deficiency_le_nine_of_k_le_26 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 26) : deficiency n k ≤ 9 := by
  by_cases hk25 : k ≤ 25
  · exact deficiency_le_nine_of_k_le_25 hn h hk25
  · have hk26 : k = 26 := by omega
    subst hk26
    exact deficiency_le_nine_of_k_eq_26 (by omega) h

/-- **Sharpened reduction to `k ≥ 27`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 27`: the cases `k ≤ 25` are discharged by the
sharp/location bounds and `k = 26` by the location bound (`deficiency_le_nine_of_k_le_26`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe26`; the entire remaining open
content of OQ-02 now lives at `k ≥ 27`. -/
theorem maximalDeficiencyIs_nine_iff_kGe27 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 27 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 26
    · exact deficiency_le_nine_of_k_le_26 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-
## Section XXVIII: The location bound closes `k = 27` — frontier `k ≥ 27` → `k ≥ 28`

Section XXVII cashed out the effective, ELS-free location bound at the open frontier
`k = 26`.  The same mechanism advances one further — and final elementary — step, to
`k = 27`.  A deficiency `≥ 10` forces the window-floor power bound `(n - 26)^{10} ≤ 27!`,
and `27! < 637^{10}` (`factorial_27_lt_637_pow_ten`), so `n - 26 < 637`, i.e. `n ≤ 662`.
With the admissibility floor `n ≥ 54` (`= 2·27`) this leaves the finite window
`n ∈ {54, 55, …, 662}` (six hundred and nine values).

As at `k = 18, …, 26`, `C(n,27)` is **not** uniformly even on this window: by
Kummer/Lucas `C(n,27)` is odd exactly when the binary digits of `27 = 11011₂` sit inside
those of `n`, which happens for thirty-eight values of `n` in the window, so the single
prime `2` no longer certifies inadmissibility.  It remains true — and this is what closes
the slice — that *some* prime `≤ 27` divides `C(n,27)` for every one of the six hundred and
nine values: `2` for the five hundred and seventy-one even ones, `3` for twelve of the
thirty-eight odd ones, `7` for twenty-four more, and `11` for the last two odd exceptions
`n = 223` and `n = 475` (which no prime `≤ 7` reaches).  So the four-prime disjunction
`2 ∣ C(n,27) ∨ 3 ∣ C(n,27) ∨ 7 ∣ C(n,27) ∨ 11 ∣ C(n,27)` holds throughout the window —
the same four-prime economy that closed `k = 25` (`5` again dispensable, `11` again the
largest prime required) — so no pair is admissible and no admissible pair at `k = 27` has
deficiency exceeding `9`.

As before the `(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only
the *location* bound closes the slice, through the uniform engine
`deficiency_le_nine_of_location` (Section XVIIB).  The elementary resolution of OQ-02 now
covers **all `k ≤ 27`**, moving the open frontier to `k ≥ 28` — the exact slice where the
record pair `(284, 28)` lives, at which the location window is inhabited by a genuine
admissible deficiency-`9` example and the ladder terminates.  The structural results remain
`ofReduceBool`-free; only the concrete divisibility facts use `native_decide`. -/

/-- `27! < 637^10`, the numeric input that pins the `k = 27` window: `(n-26)^{10} ≤ 27!`
forces `n - 26 < 637`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `27! = 10888869450418352160768000000 <
11000041493002581448023079849 = 637^{10}`; and `637` is sharp: `636^{10} =
10828571200835477863557758976 ≤ 27!`). -/
theorem factorial_27_lt_637_pow_ten : Nat.factorial 27 < 637 ^ 10 := by decide

/-- For `54 ≤ n ≤ 662` some prime `≤ 27` divides `C(n,27)`: `2` for the even values, `3`
for twelve of the odd binomials, `7` for twenty-four more, and `11` for the two odd
exceptions `n = 223` and `n = 475`.  Stated as the disjunction
`2 ∣ · ∨ 3 ∣ · ∨ 7 ∣ · ∨ 11 ∣ ·`, which holds across the whole window.  Uses
`native_decide` (⇒ `Lean.ofReduceBool`) because the naive `Nat.choose` recursion is
infeasible for kernel `decide`. -/
theorem smallPrime_dvd_choose_27_of_range {n : ℕ} (hlo : 54 ≤ n) (hhi : n ≤ 662) :
    2 ∣ Nat.choose n 27 ∨ 3 ∣ Nat.choose n 27 ∨ 7 ∣ Nat.choose n 27 ∨
      11 ∣ Nat.choose n 27 := by
  interval_cases n <;> native_decide

/-- The six hundred and nine small pairs left by the `k = 27` location window are all
inadmissible: some prime `p ∈ {2, 3, 7, 11}` (each `≤ 27`) divides `C(n,27)`, contradicting
`NoSmallPrimeFactors n 27` (which would force `27 < p`). -/
theorem not_admissible_k27_of_range {n : ℕ} (hlo : 54 ≤ n) (hhi : n ≤ 662) :
    ¬ NoSmallPrimeFactors n 27 := by
  intro h
  rcases smallPrime_dvd_choose_27_of_range hlo hhi with hd | hd | hd | hd
  · have := h 2 Nat.prime_two hd; omega
  · have := h 3 Nat.prime_three hd; omega
  · have := h 7 (by norm_num) hd; omega
  · have := h 11 (by norm_num) hd; omega

/-- **The location bound closes `k = 27`.**  For an admissible pair with `k = 27` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor
bound, `(n - 26)^{10} ≤ 27! < 637^{10}`, hence `n ≤ 662`; with the admissibility floor
`n ≥ 54` this leaves only `n ∈ {54,…,662}`, none admissible (some prime `≤ 27` divides
`C(n,27)`, even where `C(n,27)` is odd).  A one-line instantiation of the uniform engine
`deficiency_le_nine_of_location` at `k = 27, M = 637`. -/
theorem deficiency_le_nine_of_k_eq_27 {n : ℕ} (hn : 54 ≤ n)
    (h : NoSmallPrimeFactors n 27) : deficiency n 27 ≤ 9 :=
  deficiency_le_nine_of_location (k := 27) (M := 637) (by omega) h
    factorial_27_lt_637_pow_ten
    (fun m hlo hhi => not_admissible_k27_of_range (by omega) (by omega))

/-- **Elementary resolution of OQ-02 for all `k ≤ 27`.**  Combines the location bound at
`k ≤ 26` (`deficiency_le_nine_of_k_le_26`) with the location bound at `k = 27`
(`deficiency_le_nine_of_k_eq_27`).  Strictly extends the `k ≤ 26` reach of Section XXVII. -/
theorem deficiency_le_nine_of_k_le_27 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 27) : deficiency n k ≤ 9 := by
  by_cases hk26 : k ≤ 26
  · exact deficiency_le_nine_of_k_le_26 hn h hk26
  · have hk27 : k = 27 := by omega
    subst hk27
    exact deficiency_le_nine_of_k_eq_27 (by omega) h

/-- **Sharpened reduction to `k ≥ 28`.**  `MaximalDeficiencyIs 9` is equivalent to the
open universal bound restricted to `k ≥ 28`: the cases `k ≤ 26` are discharged by the
sharp/location bounds and `k = 27` by the location bound (`deficiency_le_nine_of_k_le_27`).
Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe27`.  This is the terminal
elementary reduction: the open content of OQ-02 now lives entirely at `k ≥ 28`, the slice
containing the record pair `(284, 28)`, where the location window admits a genuine
deficiency-`9` example and no elementary window-inadmissibility argument can succeed — the
remaining bound is the irreducibly analytic Erdős–Lacampagne–Selfridge input. -/
theorem maximalDeficiencyIs_nine_iff_kGe28 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 28 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 27
    · exact deficiency_le_nine_of_k_le_27 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-
## Section XXIX: The location bound closes `k = 28` — frontier `k ≥ 28` → `k ≥ 29`

Section XXVIII was described as the *terminal* elementary step, on the ground that the
`k = 28` location window is inhabited by the genuine admissible deficiency-`9` example
`(284, 28)`, so the pure **inadmissibility** argument that closes every earlier slice
(`k = 16, …, 27`: *some* prime `≤ k` divides `C(n,k)` for **every** `n` in the window)
provably fails at `k = 28`.  That is correct — but it is not the end of the elementary
road, because the location window is *finite* and the deficiency of each admissible pair in
it is a *decidable* quantity.  We close `k = 28` by the stronger, still elementary,
**window-check** argument: instead of showing every window pair is inadmissible, we show
that every *admissible* window pair has deficiency `≤ 9`.

Concretely, a deficiency `≥ 10` at `k = 28` forces the window-floor power bound
`(n - 27)^{10} ≤ 28!`, and `28! < 889^{10}` (`factorial_28_lt_889_pow_ten`), so
`n - 27 < 889`, i.e. `n ≤ 915`.  With the admissibility floor `n ≥ 56 (= 2·28)` this
leaves the finite window `n ∈ {56, 57, …, 915}` (eight hundred and sixty values).  Across
that whole window there is **exactly one** admissible pair — the record `(284, 28)` itself
— and its deficiency is `9`, not `≥ 10`.  Every other `n ∈ {56, …, 915}` is *inadmissible*:
some prime `p ≤ 28` (in fact `p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23}`) divides `C(n,28)`.
The single decidable fact `window_k28_admissible_deficiency_le_nine` records exactly this
— for each `m` in the window, either a small prime divides `C(m,28)` or `deficiency m 28 ≤ 9`
— and closes the slice.

This is the *record* slice of the elementary ladder: `k = 28` is the slice that *contains*
the record, and the argument works precisely because the location window isolates the
record as the **unique** admissible pair, whose deficiency is the record value `9`.  For
`k ≥ 29` the record pair is gone, so no *unique-admissible-pair* phenomenon is available;
one might expect the remaining universal bound to require the analytic Erdős–Lacampagne–
Selfridge input.  Section XXX below shows the window-check engine nonetheless still closes
`k = 29` computationally: across the (larger) `k = 29` window every admissible pair — not
just a single record — has deficiency `≤ 9`, verified by one `native_decide`.  So the
elementary resolution of OQ-02 now covers **all `k ≤ 29`** (see
`deficiency_le_nine_of_k_le_29`), moving the open frontier to `k ≥ 30`.  As before the
`(k!)²` factorial method is powerless here
(`sharp_bound_permits_deficiency_ten` permits deficiency `10` for every `k ≥ 16`); only the
window-check refinement of the *location* bound closes the slice.  The structural results
remain `ofReduceBool`-free; only the concrete window fact uses `native_decide`. -/

/-- `28! < 889^10`, the numeric input that pins the `k = 28` window: `(n-27)^{10} ≤ 28!`
forces `n - 27 < 889`.  `ofReduceBool`-free (`Nat.factorial` and `Nat.pow` on literals
reduce under kernel `decide`; `28! = 304888344611713860501504000000 <
308331296938836253127540655601 = 889^{10}`; and `889` is sharp: `888^{10} =
304880506868562346036873396224 ≤ 28!`). -/
theorem factorial_28_lt_889_pow_ten : Nat.factorial 28 < 889 ^ 10 := by decide

/-- **The `k = 28` window check.**  For every `m` in the location window `56 ≤ m ≤ 915`
either some prime `p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23}` (each `≤ 28`) divides `C(m,28)` —
so `m` is inadmissible — or `deficiency m 28 ≤ 9`.  Equivalently: the only *admissible*
pair in the window is the record `(284, 28)`, and its deficiency is `9`.  Uses
`native_decide` (⇒ `Lean.ofReduceBool`): computing `C(m,28)` and the smooth-window count
`deficiency m 28` for the eight hundred and sixty values is infeasible for kernel `decide`. -/
theorem window_k28_admissible_deficiency_le_nine :
    ∀ m ∈ Finset.Icc 56 915,
      (2 ∣ Nat.choose m 28 ∨ 3 ∣ Nat.choose m 28 ∨ 5 ∣ Nat.choose m 28 ∨
       7 ∣ Nat.choose m 28 ∨ 11 ∣ Nat.choose m 28 ∨ 13 ∣ Nat.choose m 28 ∨
       17 ∣ Nat.choose m 28 ∨ 19 ∣ Nat.choose m 28 ∨ 23 ∣ Nat.choose m 28)
      ∨ deficiency m 28 ≤ 9 := by
  native_decide

/-- Every *admissible* pair in the `k = 28` location window has deficiency `≤ 9`.  From the
window check: an admissible `m` cannot have any prime `≤ 28` dividing `C(m,28)`, so the
divisibility disjunction is impossible and `deficiency m 28 ≤ 9` remains.  (The single
admissible `m` in the window is the record `m = 284`, with deficiency exactly `9`.) -/
theorem admissible_k28_window_deficiency_le_nine {m : ℕ} (hlo : 56 ≤ m) (hhi : m ≤ 915)
    (h : NoSmallPrimeFactors m 28) : deficiency m 28 ≤ 9 := by
  have hm : m ∈ Finset.Icc 56 915 := Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  rcases window_k28_admissible_deficiency_le_nine m hm with hdvd | hdef
  · exfalso
    rcases hdvd with hd | hd | hd | hd | hd | hd | hd | hd | hd
    · have := h 2 Nat.prime_two hd; omega
    · have := h 3 Nat.prime_three hd; omega
    · have := h 5 (by norm_num) hd; omega
    · have := h 7 (by norm_num) hd; omega
    · have := h 11 (by norm_num) hd; omega
    · have := h 13 (by norm_num) hd; omega
    · have := h 17 (by norm_num) hd; omega
    · have := h 19 (by norm_num) hd; omega
    · have := h 23 (by norm_num) hd; omega
  · exact hdef

/-- **Window-check location engine.**  A variant of `deficiency_le_nine_of_location`
(Section XVIIB) whose finite-window hypothesis is the *window check* "every admissible pair
in the window has deficiency `≤ 9`" rather than "every window pair is inadmissible".  This
is the strictly weaker requirement needed once the window is inhabited by an admissible pair
(as at `k = 28`): from the certificate `k! < M^{10}` a deficiency `≥ 10` would land `n` in
the window `2k ≤ n ≤ k + M - 2`, where the check already caps the deficiency at `9`.
Independent of the axiomatized ELS bound `els_upper_bound`. -/
theorem deficiency_le_nine_of_location_window {n k M : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k)
    (hnum : Nat.factorial k < M ^ 10)
    (hwin : ∀ m : ℕ, 2 * k ≤ m → m ≤ k + M - 2 → NoSmallPrimeFactors m k →
      deficiency m k ≤ 9) :
    deficiency n k ≤ 9 := by
  by_contra hcon
  push_neg at hcon
  have hpow : (n - k + 1) ^ 10 ≤ Nat.factorial k :=
    windowFloor_pow_le_factorial_of_le hn h (by omega)
  have hlt : (n - k + 1) ^ 10 < M ^ 10 := lt_of_le_of_lt hpow hnum
  have hfloor : n - k + 1 < M := by
    by_contra hge
    push_neg at hge
    exact absurd (Nat.pow_le_pow_left hge 10) (not_le.mpr hlt)
  have hle := hwin n hn (by omega) h
  omega

/-- **The location bound closes `k = 28`.**  For an admissible pair with `k = 28` the
deficiency never exceeds `9`.  A deficiency `≥ 10` would force, via the window-floor bound,
`(n - 27)^{10} ≤ 28! < 889^{10}`, hence `n ≤ 915`; with the admissibility floor `n ≥ 56`
this leaves only `n ∈ {56,…,915}`, whose sole admissible member is the record `(284, 28)`
of deficiency `9` (`admissible_k28_window_deficiency_le_nine`).  A one-line instantiation of
the window-check engine `deficiency_le_nine_of_location_window` at `k = 28, M = 889`.  This
is the slice containing the record pair itself. -/
theorem deficiency_le_nine_of_k_eq_28 {n : ℕ} (hn : 56 ≤ n)
    (h : NoSmallPrimeFactors n 28) : deficiency n 28 ≤ 9 :=
  deficiency_le_nine_of_location_window (k := 28) (M := 889) (by omega) h
    factorial_28_lt_889_pow_ten
    (fun m hlo hhi hadm => admissible_k28_window_deficiency_le_nine (by omega) (by omega) hadm)

/-- **Elementary resolution of OQ-02 for all `k ≤ 28`.**  Combines the location bound at
`k ≤ 27` (`deficiency_le_nine_of_k_le_27`) with the window-check location bound at `k = 28`
(`deficiency_le_nine_of_k_eq_28`).  Strictly extends the `k ≤ 27` reach of Section XXVIII to
the slice `k = 28` that contains the record pair. -/
theorem deficiency_le_nine_of_k_le_28 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 28) : deficiency n k ≤ 9 := by
  by_cases hk27 : k ≤ 27
  · exact deficiency_le_nine_of_k_le_27 hn h hk27
  · have hk28 : k = 28 := by omega
    subst hk28
    exact deficiency_le_nine_of_k_eq_28 (by omega) h

/-- **Sharpened reduction to `k ≥ 29`.**  `MaximalDeficiencyIs 9` is equivalent to the open
universal bound restricted to `k ≥ 29`: the cases `k ≤ 27` are discharged by the
sharp/location bounds and `k = 28` by the window-check location bound
(`deficiency_le_nine_of_k_le_28`).  Strictly sharper than `maximalDeficiencyIs_nine_iff_kGe28`:
the `k = 28` slice — the one containing the record `(284, 28)` — is now *closed*, because the
location window isolates the record as the unique admissible pair and its deficiency is the
record value `9`.  The remaining open content of OQ-02 lives entirely at `k ≥ 29`, where no
record pair survives and the universal bound is the irreducibly analytic Erdős–Lacampagne–
Selfridge input. -/
theorem maximalDeficiencyIs_nine_iff_kGe29 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 29 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 28
    · exact deficiency_le_nine_of_k_le_28 hv.1 hv.2 hk
    · exact h n k (by omega) hv

/-! ### Section XXX: the window check closes `k = 29`

The `k = 28` slice was the record slice; for `k = 29` the record pair `(284, 28)` is
gone, but the *window-check* engine still applies computationally.  A deficiency `≥ 10`
at `k = 29` forces `(n - 28)^{10} ≤ 29!`, and `29! < 1244^{10}`
(`factorial_29_lt_1244_pow_ten`), so `n - 28 < 1244`, i.e. `n ≤ 1271`.  With the floor
`n ≥ 58 (= 2·29)` this leaves the finite window `n ∈ {58, …, 1271}` (1214 values), and a
single `native_decide` verifies that across the whole window every admissible pair has
deficiency `≤ 9` — so the slice closes.  This pushes the elementary resolution of OQ-02 to
**all `k ≤ 29`**, one slice past the record.  As always only the concrete window fact uses
`native_decide` (⇒ `Lean.ofReduceBool`); the structural engine
`deficiency_le_nine_of_location_window` is `ofReduceBool`-free. -/

/-- `29! < 1244^10`, the numeric input pinning the `k = 29` window: `(n-28)^{10} ≤ 29!`
forces `n - 28 < 1244`.  `ofReduceBool`-free (kernel `decide`). -/
theorem factorial_29_lt_1244_pow_ten : Nat.factorial 29 < 1244 ^ 10 := by decide

/-- **The `k = 29` window check.**  For every `m` in the location window `58 ≤ m ≤ 1271`
either some prime `p ∈ {2,3,5,7,11,13,17,19,23,29}` (each `≤ 29`) divides `C(m,29)` — so
`m` is inadmissible — or `deficiency m 29 ≤ 9`.  Uses `native_decide` (⇒ `Lean.ofReduceBool`):
computing `C(m,29)` and `deficiency m 29` for the 1214 values is infeasible for kernel
`decide`. -/
theorem window_k29_admissible_deficiency_le_nine :
    ∀ m ∈ Finset.Icc 58 1271,
      (2 ∣ Nat.choose m 29 ∨ 3 ∣ Nat.choose m 29 ∨ 5 ∣ Nat.choose m 29 ∨
       7 ∣ Nat.choose m 29 ∨ 11 ∣ Nat.choose m 29 ∨ 13 ∣ Nat.choose m 29 ∨
       17 ∣ Nat.choose m 29 ∨ 19 ∣ Nat.choose m 29 ∨ 23 ∣ Nat.choose m 29 ∨
       29 ∣ Nat.choose m 29)
      ∨ deficiency m 29 ≤ 9 := by
  native_decide

/-- Every *admissible* pair in the `k = 29` location window has deficiency `≤ 9`.  From the
window check: an admissible `m` cannot have any prime `≤ 29` dividing `C(m,29)`, so the
divisibility disjunction is impossible and `deficiency m 29 ≤ 9` remains. -/
theorem admissible_k29_window_deficiency_le_nine {m : ℕ} (hlo : 58 ≤ m) (hhi : m ≤ 1271)
    (h : NoSmallPrimeFactors m 29) : deficiency m 29 ≤ 9 := by
  have hm : m ∈ Finset.Icc 58 1271 := Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  rcases window_k29_admissible_deficiency_le_nine m hm with hdvd | hdef
  · exfalso
    rcases hdvd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
    · have := h 2 Nat.prime_two hd; omega
    · have := h 3 Nat.prime_three hd; omega
    · have := h 5 (by norm_num) hd; omega
    · have := h 7 (by norm_num) hd; omega
    · have := h 11 (by norm_num) hd; omega
    · have := h 13 (by norm_num) hd; omega
    · have := h 17 (by norm_num) hd; omega
    · have := h 19 (by norm_num) hd; omega
    · have := h 23 (by norm_num) hd; omega
    · have := h 29 (by norm_num) hd; omega
  · exact hdef

/-- **The location bound closes `k = 29`.**  A one-line instantiation of the window-check
engine `deficiency_le_nine_of_location_window` at `k = 29, M = 1244`.  This is the first
slice *past* the record pair — the window is no longer inhabited by a record, yet the
computational check still caps every admissible pair's deficiency at `9`. -/
theorem deficiency_le_nine_of_k_eq_29 {n : ℕ} (hn : 58 ≤ n)
    (h : NoSmallPrimeFactors n 29) : deficiency n 29 ≤ 9 :=
  deficiency_le_nine_of_location_window (k := 29) (M := 1244) (by omega) h
    factorial_29_lt_1244_pow_ten
    (fun m hlo hhi hadm => admissible_k29_window_deficiency_le_nine (by omega) (by omega) hadm)

/-- **Elementary resolution of OQ-02 for all `k ≤ 29`.**  Combines the `k ≤ 28` reach
(`deficiency_le_nine_of_k_le_28`) with the window-check bound at `k = 29`
(`deficiency_le_nine_of_k_eq_29`).  Extends the record slice by one. -/
theorem deficiency_le_nine_of_k_le_29 {n k : ℕ} (hn : 2 * k ≤ n)
    (h : NoSmallPrimeFactors n k) (hk : k ≤ 29) : deficiency n k ≤ 9 := by
  by_cases hk28 : k ≤ 28
  · exact deficiency_le_nine_of_k_le_28 hn h hk28
  · have hk29 : k = 29 := by omega
    subst hk29
    exact deficiency_le_nine_of_k_eq_29 (by omega) h

/-- **Sharpened reduction to `k ≥ 30`.**  `MaximalDeficiencyIs 9` is equivalent to the open
universal bound restricted to `k ≥ 30`: the cases `k ≤ 29` are now discharged, the `k = 29`
slice by the window-check location bound `deficiency_le_nine_of_k_le_29`.  Strictly sharper
than `maximalDeficiencyIs_nine_iff_kGe29`: the window-check engine closes `k = 29`
computationally even though no record pair survives there, so the remaining open content of
OQ-02 lives entirely at `k ≥ 30`. -/
theorem maximalDeficiencyIs_nine_iff_kGe30 :
    MaximalDeficiencyIs 9 ↔
      ∀ n k, 30 ≤ k → ValidDeficiencyExample n k → deficiency n k ≤ 9 := by
  rw [maximalDeficiencyIs_nine_iff_upperBound]
  constructor
  · intro h n k _ hv; exact h n k hv
  · intro h n k hv
    by_cases hk : k ≤ 29
    · exact deficiency_le_nine_of_k_le_29 hv.1 hv.2 hk
    · exact h n k (by omega) hv
