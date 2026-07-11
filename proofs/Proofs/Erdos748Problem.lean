/-
Erdős Problem #748: The Cameron-Erdős Conjecture on Sum-Free Sets

Source: https://erdosproblems.com/748
Status: PROVED (Green 2004, Sapozhenko 2003)

Statement:
Let f(n) count the number of sum-free subsets A ⊆ {1,...,n}.
A set is sum-free if it contains no solutions to a = b + c with a,b,c ∈ A.
Is it true that f(n) = 2^{(1+o(1))n/2}?

Answer: YES

Background:
- Trivial lower bound: f(n) ≥ 2^{n/2} (all subsets of [n/2, n] are sum-free)
- The conjecture asks if this is tight up to lower-order terms

Solution:
- Green (2004, Bull. London Math. Soc.): Proved f(n) ≪ 2^{n/2}
- Sapozhenko (2003, Dokl. Akad. Nauk): Proved independently
- Both proved stronger: f(n) ~ c_n · 2^{n/2} where c_n depends on parity of n

Key Insight:
Sum-free sets are "essentially" subsets of [n/2, n] or similar structures.
The upper bound uses sophisticated counting techniques and structure theorems.

References:
- Cameron-Erdős (original conjecture)
- Green (2004): "The Cameron-Erdős conjecture", Bull. London Math. Soc.
- Sapozhenko (2003): "The Cameron-Erdős conjecture", Dokl. Akad. Nauk
- OEIS A007865: Number of sum-free subsets of {1,...,n}
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace Erdos748

/-
## Part I: Sum-Free Sets
-/

/--
**Sum-Free Set:**
A set A is sum-free if there are no a, b, c ∈ A with a = b + c.

Equivalently, A contains no arithmetic progressions of length 3 starting at 0.
-/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a ≠ b + c

/--
`IsSumFree` is decidable: although the quantifiers range over all of `ℕ`, the
guards `a ∈ A`, `b ∈ A`, `c ∈ A` restrict each variable to the finite set `A`,
so the property is equivalent to a bounded `∀ … ∈ A` statement.
-/
instance decidableIsSumFree (A : Finset ℕ) : Decidable (IsSumFree A) :=
  decidable_of_iff (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c)
    ⟨fun h a b c ha hb hc => h a ha b hb c hc, fun h a ha b hb c hc => h a b c ha hb hc⟩

/--
**Alternative definition:**
A is sum-free iff A ∩ (A + A) = ∅.
-/
def IsSumFree' (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, b + c ≠ a

theorem sumFree_iff (A : Finset ℕ) : IsSumFree A ↔ IsSumFree' A := by
  unfold IsSumFree IsSumFree'
  constructor
  · intro h a ha b hb c hc
    exact fun heq => h a b c ha hb hc heq.symm
  · intro h a b c ha hb hc heq
    exact h a ha b hb c hc heq.symm

/-
## Part II: Counting Sum-Free Sets
-/

/--
**Sum-Free Subsets of {1,...,n}:**
The collection of all sum-free subsets.
-/
def sumFreeSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter IsSumFree

/--
**The Counting Function f(n):**
The number of sum-free subsets of {1,...,n}.
-/
def f (n : ℕ) : ℕ := (sumFreeSubsets n).card

/-
## Part III: Trivial Lower Bound
-/

/--
**Upper Half is Sum-Free:**
Any subset of {⌈n/2⌉, ..., n} is sum-free because
for any a, b in this range, a + b > n ≥ any element.
-/
theorem upperHalf_sumFree (n : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, n / 2 + 1 ≤ a ∧ a ≤ n) :
    IsSumFree A := by
  intro a b c ha hb hc heq
  have hca : n / 2 + 1 ≤ c := (hA c hc).1
  have hcb : n / 2 + 1 ≤ b := (hA b hb).1
  have han : a ≤ n := (hA a ha).2
  omega

/--
**Trivial Lower Bound:**
f(n) ≥ 2^{⌊n/2⌋} because all 2^{⌈n/2⌉} subsets of the upper half are sum-free.

Proof: Let U = {⌊n/2⌋+1, ..., n}. By `upperHalf_sumFree` every subset of U is
sum-free, and every subset of U is a subset of {1,...,n}, so `U.powerset` embeds
into `sumFreeSubsets n`. Hence f(n) ≥ |U.powerset| = 2^{|U|} = 2^{n-⌊n/2⌋} ≥ 2^{⌊n/2⌋}.
-/
theorem trivial_lower_bound (n : ℕ) (hn : n ≥ 2) :
    f n ≥ 2 ^ (n / 2) := by
  -- The upper half U = {⌊n/2⌋+1, ..., n}
  set U : Finset ℕ := Finset.Icc (n / 2 + 1) n with hU
  -- Every subset of U is a sum-free subset of {1,...,n}
  have hsub : U.powerset ⊆ sumFreeSubsets n := by
    intro A hAmem
    rw [Finset.mem_powerset] at hAmem
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hAmem.trans ?_, ?_⟩
    · -- U ⊆ {1,...,n}
      rw [hU]
      exact Finset.Icc_subset_Icc (by omega) (le_refl n)
    · -- A is sum-free since A ⊆ U
      apply upperHalf_sumFree n A
      intro a ha
      have haU : a ∈ U := hAmem ha
      rw [hU, Finset.mem_Icc] at haU
      exact haU
  -- Cardinality bound: f n ≥ 2^|U|
  have hcard : 2 ^ U.card ≤ f n :=
    calc 2 ^ U.card = U.powerset.card := (Finset.card_powerset U).symm
      _ ≤ (sumFreeSubsets n).card := Finset.card_le_card hsub
      _ = f n := rfl
  -- |U| = n - ⌊n/2⌋ ≥ ⌊n/2⌋
  have hUcard : U.card = n - n / 2 := by rw [hU, Nat.card_Icc]; omega
  have hexp : n / 2 ≤ U.card := by rw [hUcard]; omega
  calc 2 ^ (n / 2) ≤ 2 ^ U.card := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ f n := hcard

/--
**Sharp Trivial Lower Bound:**
`f(n) ≥ 2^{⌈n/2⌉}`.

The upper half `U = {⌊n/2⌋+1, …, n}` has *exactly* `⌈n/2⌉ = n − ⌊n/2⌋` elements,
and by `upperHalf_sumFree` **all** `2^{⌈n/2⌉}` of its subsets are sum-free. This
sharpens `trivial_lower_bound`, which only extracted the weaker exponent `⌊n/2⌋`:
for odd `n`, `⌈n/2⌉ = ⌊n/2⌋ + 1`, so the bound here is a full factor of `2`
(i.e. `√2` per element) larger. It is the largest power of two the upper-half
construction can yield. In `ℕ`, the ceiling `⌈n/2⌉` is written `(n + 1) / 2`.
-/
theorem sharp_lower_bound (n : ℕ) :
    f n ≥ 2 ^ ((n + 1) / 2) := by
  -- Same upper half U = {⌊n/2⌋+1, …, n}, but we keep its full cardinality.
  set U : Finset ℕ := Finset.Icc (n / 2 + 1) n with hU
  have hsub : U.powerset ⊆ sumFreeSubsets n := by
    intro A hAmem
    rw [Finset.mem_powerset] at hAmem
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hAmem.trans ?_, ?_⟩
    · rw [hU]; exact Finset.Icc_subset_Icc (by omega) (le_refl n)
    · apply upperHalf_sumFree n A
      intro a ha
      have haU : a ∈ U := hAmem ha
      rw [hU, Finset.mem_Icc] at haU
      exact haU
  have hcard : 2 ^ U.card ≤ f n :=
    calc 2 ^ U.card = U.powerset.card := (Finset.card_powerset U).symm
      _ ≤ (sumFreeSubsets n).card := Finset.card_le_card hsub
      _ = f n := rfl
  -- |U| = n − ⌊n/2⌋ = ⌈n/2⌉ = (n+1)/2.
  have hUcard : U.card = (n + 1) / 2 := by rw [hU, Nat.card_Icc]; omega
  rw [hUcard] at hcard
  exact hcard

/--
**Monotonicity, ground step:**
Every sum-free subset of {1,...,n} is also a sum-free subset of {1,...,n+1}.
Sum-freeness is a property of the set itself (no `a = b + c` among its own
elements), so enlarging the ambient range cannot break it; the only change is
that the subset is now allowed to live in the larger box.
-/
theorem sumFreeSubsets_subset_succ (n : ℕ) :
    sumFreeSubsets n ⊆ sumFreeSubsets (n + 1) := by
  intro A hA
  rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset] at hA ⊢
  exact ⟨hA.1.trans (Finset.Icc_subset_Icc (le_refl 1) (Nat.le_succ n)), hA.2⟩

/--
**The counting function `f` is monotone.**
Since the family of sum-free subsets only grows as the ambient range grows
(`sumFreeSubsets_subset_succ`), its cardinality `f n` is non-decreasing in `n`.
This is the structural fact underlying the trivial lower bound: the supply of
sum-free sets never shrinks.
-/
theorem f_monotone : Monotone f :=
  monotone_nat_of_le_succ fun n =>
    Finset.card_le_card (sumFreeSubsets_subset_succ n)

/--
**The counting function `f` is strictly monotone.**
Passing from `{1,…,n}` to `{1,…,n+1}` keeps every existing sum-free subset
(`sumFreeSubsets_subset_succ`) and adds at least one genuinely new one: the
singleton `{n+1}`, which is sum-free (`n+1 ≠ (n+1)+(n+1)`) but cannot fit inside
`{1,…,n}`. Hence the inclusion of families is *strict*, so the count grows by at
least one at every step (`f n < f (n+1)`). This sharpens `f_monotone`, which now
follows as `f_strictMono.monotone`.
-/
theorem f_strictMono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro n
  show (sumFreeSubsets n).card < (sumFreeSubsets (n + 1)).card
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (sumFreeSubsets_subset_succ n)]
  refine ⟨{n + 1}, ?_, ?_⟩
  · -- `{n+1}` is a sum-free subset of `{1,…,n+1}`.
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      rw [Finset.mem_Icc]
      omega
    · -- `{n+1}` is sum-free: `n+1 ≠ (n+1) + (n+1)` (inlined `singleton_sumFree`).
      intro a b c ha hb hc
      rw [Finset.mem_singleton] at ha hb hc
      omega
  · -- `{n+1} ⊄ {1,…,n}`, so it is not counted by `sumFreeSubsets n`.
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    rintro ⟨hsub, -⟩
    have hmem : (n + 1) ∈ Finset.Icc 1 n := hsub (Finset.mem_singleton_self _)
    rw [Finset.mem_Icc] at hmem
    omega

/--
**`f` is injective.**  Strict monotonicity (`f_strictMono`) makes the counting
function injective: distinct ambient sizes give distinct sum-free subset counts.
-/
theorem f_injective : Function.Injective f := f_strictMono.injective

/--
**`f` grows by at least one at each step**, `f n < f (n+1)`.  The explicit
successor form of `f_strictMono`, witnessing the strict inclusion of the
sum-free families (`{n+1}` is the new member at step `n+1`).
-/
theorem f_lt_succ (n : ℕ) : f n < f (n + 1) := f_strictMono (Nat.lt_succ_self n)

/--
**`f` is unbounded**: for every target `M` there is an `n` with `f n ≥ M`, so
there are arbitrarily many sum-free subsets.  Take `n = 2M`: the sharp lower
bound gives `f (2M) ≥ 2^{⌈(2M+1)/2⌉} = 2^M ≥ M` (since `M < 2^M`).  This is the
qualitative core of the Cameron–Erdős growth `f(n) = 2^{(1+o(1))n/2}` that the
axiomatized asymptotics make precise. -/
theorem f_unbounded (M : ℕ) : ∃ n, M ≤ f n := by
  refine ⟨2 * M, ?_⟩
  have h1 : (2 * M + 1) / 2 = M := by omega
  calc M ≤ 2 ^ M := M.lt_two_pow_self.le
    _ = 2 ^ ((2 * M + 1) / 2) := by rw [h1]
    _ ≤ f (2 * M) := sharp_lower_bound (2 * M)

/-
## Part IV: The Cameron-Erdős Conjecture
-/

/--
**The Cameron-Erdős Conjecture:**
f(n) = 2^{(1 + o(1))n/2}

This means:
  lim_{n→∞} log₂(f(n)) / (n/2) = 1
-/
def cameronErdosConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (1 - ε) * (n / 2 : ℝ) ≤ Real.log (f n) / Real.log 2 ∧
    Real.log (f n) / Real.log 2 ≤ (1 + ε) * (n / 2 : ℝ)

/-
## Part V: The Solution
-/

/--
**Green's Theorem (2004):**
f(n) ≪ 2^{n/2}, i.e., there exists a constant C such that f(n) ≤ C · 2^{n/2}.
-/
axiom green_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * 2 ^ (n / 2)

/-
**Sapozhenko's Theorem (2003):**
Same result, proved independently.
-/
/--
**The Precise Asymptotic:**
f(n) ~ c_n · 2^{n/2} where c_n depends on the parity of n.

- c_n = c_even when n is even
- c_n = c_odd when n is odd
-/
axiom precise_asymptotic :
    ∃ c_even c_odd : ℝ, c_even > 0 ∧ c_odd > 0 ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
        if n % 2 = 0 then
          |((f n : ℝ) / 2 ^ (n / 2)) - c_even| < ε
        else
          |((f n : ℝ) / 2 ^ (n / 2)) - c_odd| < ε

/--
**Cameron-Erdős Conjecture: PROVED**
-/
theorem cameron_erdos_proved : cameronErdosConjecture := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := green_upper_bound
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  let K := max 0 (Real.log C / Real.log 2)
  have hK_nn : 0 ≤ K := le_max_left 0 _
  obtain ⟨N_lb, hN_lb⟩ := exists_nat_gt (1 / ε)
  obtain ⟨N_ub, hN_ub⟩ := exists_nat_gt (2 * K / ε)
  refine ⟨max (max N_lb N_ub) 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hN_lb_n : N_lb ≤ n :=
    le_trans ((Nat.le_max_left N_lb N_ub).trans (Nat.le_max_left _ 2)) hn
  have hN_ub_n : N_ub ≤ n :=
    le_trans ((Nat.le_max_right N_lb N_ub).trans (Nat.le_max_left _ 2)) hn
  have h1_ε_n : 1 / ε < (n : ℝ) := lt_of_lt_of_le hN_lb (by exact_mod_cast hN_lb_n)
  have h2K_ε_n : 2 * K / ε < (n : ℝ) := lt_of_lt_of_le hN_ub (by exact_mod_cast hN_ub_n)
  have hε_n2 : 1 / 2 ≤ ε * ((n : ℝ) / 2) := by
    have : 1 < (n : ℝ) * ε := by
      have h := mul_lt_mul_of_pos_right h1_ε_n hε
      linarith [show (1 / ε) * ε = 1 from by field_simp]
    linarith
  have hK_ε_n2 : K ≤ ε * ((n : ℝ) / 2) := by
    have h := mul_lt_mul_of_pos_right h2K_ε_n hε
    linarith [show (2 * K / ε) * ε = 2 * K from by field_simp]
  have hlb_R : (2 : ℝ) ^ (n / 2) ≤ (f n : ℝ) := by
    exact_mod_cast trivial_lower_bound n hn2
  have hfn_pos : (0 : ℝ) < f n :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0:ℝ) < 2) _) hlb_R
  have hub_R : (f n : ℝ) ≤ C * (2 : ℝ) ^ (n / 2) := hbound n (by omega)
  have hdiv_R : (n : ℝ) = ↑(n / 2 : ℕ) * 2 + ↑(n % 2 : ℕ) := by
    exact_mod_cast (show n = n / 2 * 2 + n % 2 by omega)
  have hmod_R_nn : (0 : ℝ) ≤ ↑(n % 2 : ℕ) := Nat.cast_nonneg _
  have hmod_R_le : ↑(n % 2 : ℕ) ≤ (1 : ℝ) := by exact_mod_cast (show n % 2 ≤ 1 by omega)
  have hn_half_lo : (n : ℝ) / 2 - 1 / 2 ≤ ↑(n / 2 : ℕ) := by linarith
  have hn_half_hi : ↑(n / 2 : ℕ) ≤ (n : ℝ) / 2 := by linarith
  have hlog_lb : ↑(n / 2 : ℕ) * Real.log 2 ≤ Real.log (f n) := by
    have h := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) _) hlb_R
    rwa [Real.log_pow] at h
  have hlog_ub : Real.log (f n) ≤ Real.log C + ↑(n / 2 : ℕ) * Real.log 2 := by
    have h := Real.log_le_log hfn_pos hub_R
    rw [Real.log_mul (ne_of_gt hC) (pow_pos (by norm_num : (0:ℝ) < 2) _).ne',
        Real.log_pow] at h
    linarith
  constructor
  · rw [le_div_iff₀ hlog2_pos]
    have h_step : (1 - ε) * ((n : ℝ) / 2) ≤ ↑(n / 2 : ℕ) := by linarith
    linarith [mul_le_mul_of_nonneg_right h_step hlog2_pos.le]
  · rw [div_le_iff₀ hlog2_pos]
    have hlogC : Real.log C ≤ ε * ((n : ℝ) / 2) * Real.log 2 := by
      have h := (div_le_iff₀ hlog2_pos).mp ((le_max_right 0 _ : Real.log C / Real.log 2 ≤ K).trans hK_ε_n2)
      linarith
    linarith [mul_le_mul_of_nonneg_right hn_half_hi hlog2_pos.le]

/-
## Part VI: Examples
-/

/--
**Empty set is sum-free:**
-/
theorem empty_sumFree : IsSumFree ∅ := by
  intro a b c ha _ _
  exact (Finset.notMem_empty a ha).elim

/--
**Singletons are sum-free:**
-/
theorem singleton_sumFree (x : ℕ) (hx : x > 0) : IsSumFree {x} := by
  intro a b c ha hb hc heq
  simp at ha hb hc
  rw [ha, hb, hc] at heq
  omega

/--
**Odd numbers in [1,n] are sum-free:**
Sum of two odd numbers is even, so can't equal an odd number.
-/
theorem oddNumbers_sumFree (n : ℕ) :
    IsSumFree ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)) := by
  intro a b c ha hb hc heq
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb hc
  have hodd_a : a % 2 = 1 := ha.2
  have hodd_b : b % 2 = 1 := hb.2
  have hodd_c : c % 2 = 1 := hc.2
  -- b + c is even (odd + odd = even)
  have heven : (b + c) % 2 = 0 := by omega
  -- But a is odd
  rw [heq] at hodd_a
  omega

/--
**Sum-freeness is downward closed:**
A subset of a sum-free set is sum-free. Sum-freeness only forbids solutions of
`a = b + c` among a set's *own* elements, so discarding elements can never create
one. (Formal witness for the two families below.)
-/
theorem sumFree_of_subset {A B : Finset ℕ} (hAB : A ⊆ B) (hB : IsSumFree B) :
    IsSumFree A :=
  fun a b c ha hb hc => hB a b c (hAB ha) (hAB hb) (hAB hc)

/--
**Two-family lower bound (odd sets ⋃ upper-half sets):**
`f(n) ≥ 2^{|O|} + 2^{|U|} − 2^{|O ∩ U|}`, where `O` is the set of odd numbers in
`[1,n]` and `U = {⌊n/2⌋+1, …, n}` is the upper half.

Both are families of sum-free sets: every subset of `U` is sum-free
(`upperHalf_sumFree`) and every subset of `O` is sum-free (`oddNumbers_sumFree`
via `sumFree_of_subset`). Hence `𝒫(O) ∪ 𝒫(U) ⊆ sumFreeSubsets n`, and by
inclusion–exclusion — using `𝒫(O) ∩ 𝒫(U) = 𝒫(O ∩ U)` —
`|𝒫(O) ∪ 𝒫(U)| = 2^{|O|} + 2^{|U|} − 2^{|O ∩ U|}`.

Because `O ∩ U ⊆ O`, this is `≥ 2^{|U|} = 2^{⌈n/2⌉}`, so it dominates
`sharp_lower_bound`; the inequality is strict whenever some odd number lies in
the lower half (`O ⊄ U`, i.e. all `n ≥ 3`). This is the formal shadow of the
Cameron–Erdős fact that the count is governed by **two** dominant families — the
reason the leading constant `c_n` depends on the parity of `n`.
-/
theorem two_family_lower_bound (n : ℕ) :
    f n ≥ 2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card
          + 2 ^ (Finset.Icc (n / 2 + 1) n).card
          - 2 ^ (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
                  ∩ Finset.Icc (n / 2 + 1) n).card := by
  set O : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k % 2 = 1) with hO
  set U : Finset ℕ := Finset.Icc (n / 2 + 1) n with hU
  -- Every subset of `O` is a sum-free subset of `{1,…,n}`.
  have hPO : O.powerset ⊆ sumFreeSubsets n := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hA.trans ?_, sumFree_of_subset hA (oddNumbers_sumFree n)⟩
    intro x hx
    rw [hO, Finset.mem_filter, Finset.mem_range] at hx
    rw [Finset.mem_Icc]
    omega
  -- Every subset of `U` is a sum-free subset of `{1,…,n}`.
  have hPU : U.powerset ⊆ sumFreeSubsets n := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hA.trans ?_, ?_⟩
    · rw [hU]; exact Finset.Icc_subset_Icc (by omega) (le_refl n)
    · apply upperHalf_sumFree n A
      intro a ha
      have haU := hA ha
      rw [hU, Finset.mem_Icc] at haU
      exact haU
  -- `𝒫(O) ∩ 𝒫(U) = 𝒫(O ∩ U)`.
  have hpi : O.powerset ∩ U.powerset = (O ∩ U).powerset := by
    ext A
    constructor
    · intro h
      rw [Finset.mem_inter, Finset.mem_powerset, Finset.mem_powerset] at h
      rw [Finset.mem_powerset]
      exact Finset.subset_inter h.1 h.2
    · intro h
      rw [Finset.mem_powerset] at h
      rw [Finset.mem_inter, Finset.mem_powerset, Finset.mem_powerset]
      exact ⟨h.trans Finset.inter_subset_left, h.trans Finset.inter_subset_right⟩
  -- Inclusion–exclusion on the two powerset families.
  have hkey : (O.powerset ∪ U.powerset).card + 2 ^ (O ∩ U).card
      = 2 ^ O.card + 2 ^ U.card := by
    have h1 := Finset.card_union_add_card_inter O.powerset U.powerset
    rw [hpi] at h1
    simp only [Finset.card_powerset] at h1
    exact h1
  -- The union embeds into the sum-free family, so `f n` bounds its cardinality.
  have hle : (O.powerset ∪ U.powerset).card ≤ f n :=
    Finset.card_le_card (Finset.union_subset hPO hPU)
  omega

/--
**The two-family bound dominates the single upper-half (`sharp`) bound.**
The right-hand side of `two_family_lower_bound`,
`2^{|O|} + 2^{|U|} − 2^{|O ∩ U|}`, is always at least `2^{|U|} = 2^{⌈n/2⌉}` — the value
delivered by `sharp_lower_bound`. This is because `O ∩ U ⊆ O`, so `2^{|O ∩ U|} ≤ 2^{|O|}`
and the surplus `2^{|O|} − 2^{|O ∩ U|}` is nonnegative. It formalises the prose claim in
`two_family_lower_bound` that adding the odd family can only *improve* the count coming from
the upper half alone, confirming the two-family construction never loses to the one-family one.
-/
theorem two_family_bound_ge_upperHalf (n : ℕ) :
    2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card
      + 2 ^ (Finset.Icc (n / 2 + 1) n).card
      - 2 ^ (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
              ∩ Finset.Icc (n / 2 + 1) n).card
    ≥ 2 ^ (Finset.Icc (n / 2 + 1) n).card := by
  have hsub : (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
                ∩ Finset.Icc (n / 2 + 1) n).card
              ≤ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hpow : 2 ^ (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
                ∩ Finset.Icc (n / 2 + 1) n).card
              ≤ 2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card :=
    Nat.pow_le_pow_right (by norm_num) hsub
  omega

/--
**The two-family bound STRICTLY dominates the single upper-half bound for `n ≥ 3`.**
This sharpens `two_family_bound_ge_upperHalf` from `≥` to `>`, formalising the prose
claim in `two_family_lower_bound` that the inequality "is strict whenever some odd
number lies in the lower half (`O ⊄ U`, i.e. all `n ≥ 3`)". The witness is `1`: it is
odd and lies in `[1,n]` (so `1 ∈ O`) but `1 < n/2 + 1` for `n ≥ 3`, so `1 ∉ U`. Hence
`O ∩ U ⊊ O`, giving `|O ∩ U| < |O|` and therefore `2^{|O∩U|} < 2^{|O|}`; the surplus
`2^{|O|} − 2^{|O∩U|}` is then strictly positive. So the two dominant sum-free families
together always count *strictly* more sets than the upper half alone — the structural
reason the leading constant genuinely combines both families rather than reducing to one.
-/
theorem two_family_bound_gt_upperHalf (n : ℕ) (hn : 3 ≤ n) :
    2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card
      + 2 ^ (Finset.Icc (n / 2 + 1) n).card
      - 2 ^ (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
              ∩ Finset.Icc (n / 2 + 1) n).card
    > 2 ^ (Finset.Icc (n / 2 + 1) n).card := by
  set O : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k % 2 = 1) with hO
  set U : Finset ℕ := Finset.Icc (n / 2 + 1) n with hU
  -- `1 ∈ O` (odd, in `[1,n]`) but `1 ∉ U` (since `n/2 + 1 ≥ 2` for `n ≥ 3`).
  have h1O : (1 : ℕ) ∈ O := by
    rw [hO, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, by omega⟩
  have h1U : (1 : ℕ) ∉ U := by
    simp only [hU, Finset.mem_Icc]; omega
  -- Therefore `O ∩ U ⊊ O`, so `|O ∩ U| < |O|`.
  have hssub : O ∩ U ⊂ O :=
    (Finset.ssubset_iff_of_subset Finset.inter_subset_left).2
      ⟨1, h1O, fun h => h1U (Finset.mem_of_mem_inter_right h)⟩
  have hcard : (O ∩ U).card < O.card := Finset.card_lt_card hssub
  -- Strictly monotone `2^·` turns the strict cardinality gap into a strict power gap.
  have hpow : 2 ^ (O ∩ U).card < 2 ^ O.card :=
    Nat.pow_lt_pow_right (by norm_num) hcard
  omega

/--
**The two-family bound also dominates the single *odd-family* bound.**
Symmetric companion of `two_family_bound_ge_upperHalf`: the right-hand side of
`two_family_lower_bound`, `2^{|O|} + 2^{|U|} − 2^{|O ∩ U|}`, is always at least
`2^{|O|}` — the value coming from the odd family alone. Here `O ∩ U ⊆ U`, so
`2^{|O ∩ U|} ≤ 2^{|U|}` and the surplus `2^{|U|} − 2^{|O ∩ U|}` is nonnegative.
Together with `two_family_bound_ge_upperHalf` this shows the two-family count
never loses to *either* single family. -/
theorem two_family_bound_ge_oddFamily (n : ℕ) :
    2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card
      + 2 ^ (Finset.Icc (n / 2 + 1) n).card
      - 2 ^ (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
              ∩ Finset.Icc (n / 2 + 1) n).card
    ≥ 2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card := by
  have hsub : (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
                ∩ Finset.Icc (n / 2 + 1) n).card
              ≤ (Finset.Icc (n / 2 + 1) n).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpow : 2 ^ (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
                ∩ Finset.Icc (n / 2 + 1) n).card
              ≤ 2 ^ (Finset.Icc (n / 2 + 1) n).card :=
    Nat.pow_le_pow_right (by norm_num) hsub
  omega

/--
**The two-family bound STRICTLY dominates the single *odd-family* bound for `n ≥ 2`.**
Strict counterpart of `two_family_bound_ge_oddFamily`, mirroring
`two_family_bound_gt_upperHalf` on the other side: the right-hand side of
`two_family_lower_bound`, `2^{|O|} + 2^{|U|} − 2^{|O ∩ U|}`, is *strictly* greater
than `2^{|O|}` for all `n ≥ 2`. The witness is the largest even number `w = 2⌊n/2⌋`
in `[1,n]`: it is even (so `w ∉ O`) yet lies in the upper half `U = {⌊n/2⌋+1,…,n}`
(since `⌊n/2⌋+1 ≤ 2⌊n/2⌋ ≤ n` once `⌊n/2⌋ ≥ 1`, i.e. `n ≥ 2`). Hence `O ∩ U ⊊ U`,
giving `|O ∩ U| < |U|` and therefore `2^{|O∩U|} < 2^{|U|}`; the surplus
`2^{|U|} − 2^{|O∩U|}` is then strictly positive. Together with
`two_family_bound_gt_upperHalf` this shows the two dominant sum-free families jointly
count *strictly* more sets than *either* single family alone — the structural reason
the leading constant genuinely combines both the odd and upper-half constructions. -/
theorem two_family_bound_gt_oddFamily (n : ℕ) (hn : 2 ≤ n) :
    2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card
      + 2 ^ (Finset.Icc (n / 2 + 1) n).card
      - 2 ^ (((Finset.range (n + 1)).filter (fun k => k % 2 = 1))
              ∩ Finset.Icc (n / 2 + 1) n).card
    > 2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card := by
  set O : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k % 2 = 1) with hO
  set U : Finset ℕ := Finset.Icc (n / 2 + 1) n with hU
  -- `w = 2⌊n/2⌋` (the largest even number ≤ n) is in `U` but not in `O` (it is even).
  have hwU : (2 * (n / 2) : ℕ) ∈ U := by
    simp only [hU, Finset.mem_Icc]; omega
  have hwO : (2 * (n / 2) : ℕ) ∉ O := by
    intro h
    rw [hO] at h
    simp only [Finset.mem_filter, Finset.mem_range] at h
    omega
  -- Therefore `O ∩ U ⊊ U`, so `|O ∩ U| < |U|`.
  have hssub : O ∩ U ⊂ U :=
    (Finset.ssubset_iff_of_subset Finset.inter_subset_right).2
      ⟨2 * (n / 2), hwU, fun h => hwO (Finset.mem_of_mem_inter_left h)⟩
  have hcard : (O ∩ U).card < U.card := Finset.card_lt_card hssub
  -- Strictly monotone `2^·` turns the strict cardinality gap into a strict power gap.
  have hpow : 2 ^ (O ∩ U).card < 2 ^ U.card :=
    Nat.pow_lt_pow_right (by norm_num) hcard
  omega

/--
**Odd-family lower bound:** `f(n) ≥ 2^{|O|}`, where `O` is the set of odd numbers
in `[1,n]`. Every subset of `O` is sum-free (odd + odd is even, so no `a = b + c`
among odds), so the `2^{|O|}` subsets of `O` are all counted by `f n`. This is
the "type 2" dominant family of Part VII, isolated as a standalone bound: it is
obtained from `two_family_lower_bound` by discarding the upper-half contribution
via `two_family_bound_ge_oddFamily`. Since `|O| = ⌈n/2⌉`, it gives the same
`2^{⌈n/2⌉}` exponent as `sharp_lower_bound` but through the *odd* construction
rather than the upper half — a genuinely distinct witnessing family. -/
theorem oddFamily_lower_bound (n : ℕ) :
    f n ≥ 2 ^ ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card :=
  le_trans (two_family_bound_ge_oddFamily n) (two_family_lower_bound n)

/--
**The odd family has size exactly `⌈n/2⌉`.**
`|O| = (n+1)/2`, where `O` is the set of odd numbers in `[1,n]` (the odd elements
of `{0,…,n}`, since `0` is even). This discharges the previously prose-only claim
in `oddFamily_lower_bound` that "`|O| = ⌈n/2⌉`". The proof is a direct induction on
`n`: passing from `{0,…,n}` to `{0,…,n+1}` adds the new top element `n+1`, which is
counted iff it is odd, and `omega` checks that this matches the increment of the
ceiling `(n+1)/2 ↦ (n+2)/2`. In `ℕ` the ceiling `⌈n/2⌉` is written `(n+1)/2`. -/
theorem oddNumbers_card (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)).card = (n + 1) / 2 := by
  induction n with
  | zero => decide
  | succ m ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : (m + 1) % 2 = 1
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
      omega
    · rw [if_neg h, ih]
      omega

/--
**Sharp lower bound via the *odd* family:** `f(n) ≥ 2^{⌈n/2⌉}`.
This re-derives the exponent of `sharp_lower_bound` through a genuinely different
witnessing construction: instead of the upper half `U = {⌊n/2⌋+1,…,n}`, it uses the
`⌈n/2⌉` odd numbers in `[1,n]`, all of whose `2^{⌈n/2⌉}` subsets are sum-free
(`oddFamily_lower_bound`). Combining `oddFamily_lower_bound` with the exact count
`oddNumbers_card` (`|O| = (n+1)/2`) yields the same `2^{⌈n/2⌉}` bound as
`sharp_lower_bound`, confirming that the odd family alone already attains the sharp
trivial exponent — the "type 2" dominant family of Part VII carries full weight. -/
theorem oddFamily_lower_bound_ceil (n : ℕ) : f n ≥ 2 ^ ((n + 1) / 2) := by
  have h := oddFamily_lower_bound n
  rwa [oddNumbers_card] at h

/-
## Part VII: Structure of Sum-Free Sets
-/

/-
**Types of Sum-Free Sets:**
Most sum-free sets are "essentially" one of:
1. Subsets of [n/2+1, n] (type 1)
2. Subsets of odd numbers (type 2)
3. Various other sparse structures

Green's proof shows type 1 and 2 dominate the count.

**Schur's Theorem Connection:**
Sum-free sets are related to Schur numbers.
The maximum size of a sum-free subset of [1,n] is ⌈n/2⌉.
-/

/--
**Achievability of the maximum sum-free size `⌈n/2⌉`.**
There is a sum-free subset of `{1,…,n}` of cardinality exactly `⌈n/2⌉ = (n+1)/2`,
namely the upper half `U = {⌊n/2⌋+1, …, n}`: it is sum-free by
`upperHalf_sumFree`, and `Nat.card_Icc` computes `|U| = n − ⌊n/2⌋ = ⌈n/2⌉`.

This formalises the *achievable* direction of the Part VII prose claim that "the
maximum size of a sum-free subset of `[1,n]` is `⌈n/2⌉`": the extremal size is
attained. (The matching upper bound — that no sum-free subset can exceed
`⌈n/2⌉` — is the classical hard direction and is left to the informal discussion.)
It also witnesses that the exponent in `sharp_lower_bound` comes from a single
genuine sum-free set of that size, not merely a counting artefact. -/
theorem exists_sumFree_card_ceil (n : ℕ) :
    ∃ A ∈ sumFreeSubsets n, A.card = (n + 1) / 2 := by
  set U : Finset ℕ := Finset.Icc (n / 2 + 1) n with hU
  refine ⟨U, ?_, ?_⟩
  · -- `U` is a sum-free subset of `{1,…,n}`.
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · rw [hU]; exact Finset.Icc_subset_Icc (by omega) (le_refl n)
    · apply upperHalf_sumFree n U
      intro a ha
      rw [hU, Finset.mem_Icc] at ha
      exact ha
  · -- `|U| = n − ⌊n/2⌋ = ⌈n/2⌉ = (n+1)/2`.
    rw [hU, Nat.card_Icc]; omega

/-
## Part VIII: OEIS A007865
-/

/--
**Small Values (OEIS A007865):**
f(1) = 2: {}, {1}
f(2) = 3: {}, {1}, {2}
f(3) = 6: {}, {1}, {2}, {3}, {1,3}, {2,3}
f(4) = 9
f(5) = 16
...
-/
-- Kernel `decide` suffices (axiom-free): the `decidableIsSumFree` instance reduces
-- `IsSumFree` to a bounded `∀ … ∈ A` decision, so these small `f n` values compute
-- in the kernel without `native_decide` (which would add `Lean.ofReduceBool`).
theorem f_1 : f 1 = 2 := by decide
theorem f_2 : f 2 = 3 := by decide
theorem f_3 : f 3 = 6 := by decide

/-- `f 4 = 9`: the nine sum-free subsets of `{1,2,3,4}` are `∅`, `{1}`, `{2}`, `{3}`,
    `{4}`, `{1,3}`, `{2,3}`, `{3,4}`, `{1,4}` (every subset containing `{1,2}`, `{2,4}`,
    or `{1,3,4}` is excluded, since `2 = 1+1`, `4 = 2+2`, `4 = 1+3`). This upgrades the
    table value `f(4) = 9` above from prose to a machine-checked (kernel `decide`) fact. -/
theorem f_4 : f 4 = 9 := by decide

/-- `f 5 = 16`: upgrades the table value `f(5) = 16` above from prose to a kernel-`decide`
    fact. Beyond the `n = 4` exclusions this adds `5 = 1+4` and `5 = 2+3`, forbidding the
    subsets containing `{1,4,5}` or `{2,3,5}`. -/
theorem f_5 : f 5 = 16 := by decide

/-
## Part IX: Summary
-/

/--
**Erdős Problem #748: PROVED**

The Cameron-Erdős conjecture is true.

f(n) = 2^{(1+o(1))n/2}

More precisely:
1. f(n) ≥ 2^{n/2} (trivial, from upper half)
2. f(n) ≤ C · 2^{n/2} (Green, Sapozhenko)
3. f(n) ~ c_n · 2^{n/2} with c_n depending on parity
-/
theorem erdos_748_summary :
    -- Sharp trivial lower bound (uses the full ⌈n/2⌉ exponent)
    (∀ n : ℕ, f n ≥ 2 ^ ((n + 1) / 2)) ∧
    -- Upper bound exists
    (∃ C : ℝ, C > 0 ∧ ∀ n ≥ 1, (f n : ℝ) ≤ C * 2 ^ (n / 2)) ∧
    -- Precise asymptotic exists
    (∃ c_even c_odd : ℝ, c_even > 0 ∧ c_odd > 0) := by
  constructor
  · exact sharp_lower_bound
  constructor
  · exact green_upper_bound
  · obtain ⟨ce, co, hce, hco, _⟩ := precise_asymptotic
    exact ⟨ce, co, hce, hco⟩

/-!
## Part VI: The lower half of the log-asymptotic is unconditional

The Cameron–Erdős conjecture `cameronErdosConjecture` is a two-sided estimate on
`log₂ (f n) = Real.log (f n) / Real.log 2`. Its upper half needs the deep Green/Sapozhenko
input (the axiom `green_upper_bound`). Its **lower** half, however, is elementary: the
sharp counting bound `sharp_lower_bound` (`f n ≥ 2^⌈n/2⌉`) gives `log₂ (f n) ≥ ⌈n/2⌉ ≥ n/2`
with no axiom at all — and it holds for *every* `n`, not merely eventually. The theorems
below isolate this axiom-free lower half.
-/

/-- **Unconditional log₂ lower bound.**  For every `n`, `log₂ (f n) ≥ n/2`.  Taking the
base-2 logarithm of the sharp counting bound `f n ≥ 2^⌈n/2⌉` (`sharp_lower_bound`) and
using `⌈n/2⌉ = (n+1)/2 ≥ n/2`.  Axiom-free: the lower half of the Cameron–Erdős asymptotic
needs none of the Green/Sapozhenko machinery. -/
theorem logDiv_log_two_f_ge (n : ℕ) :
    (n : ℝ) / 2 ≤ Real.log (f n) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- real-cast lower bound on `f n`
  have hfge : (2 : ℝ) ^ ((n + 1) / 2) ≤ (f n : ℝ) := by
    have h := sharp_lower_bound n
    calc (2 : ℝ) ^ ((n + 1) / 2) = ((2 ^ ((n + 1) / 2) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (f n : ℝ) := by exact_mod_cast h
  have hfpos : (0 : ℝ) < f n := lt_of_lt_of_le (by positivity) hfge
  -- log of the power bound
  have hloglb : ((n + 1) / 2 : ℕ) * Real.log 2 ≤ Real.log (f n) := by
    calc ((n + 1) / 2 : ℕ) * Real.log 2
          = Real.log ((2 : ℝ) ^ ((n + 1) / 2)) := by rw [Real.log_pow]
      _ ≤ Real.log (f n) := Real.log_le_log (by positivity) hfge
  -- `n/2 ≤ ⌈n/2⌉ = (n+1)/2` as reals
  have hceil : (n : ℝ) / 2 ≤ ((n + 1) / 2 : ℕ) := by
    have h2 : n ≤ 2 * ((n + 1) / 2) := by omega
    have : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  rw [le_div_iff₀ hlog2]
  calc (n : ℝ) / 2 * Real.log 2
        ≤ ((n + 1) / 2 : ℕ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hceil (le_of_lt hlog2)
    _ ≤ Real.log (f n) := hloglb

/-- **The Cameron–Erdős lower bound, unconditionally and for all `n`.**  The lower conjunct
of `cameronErdosConjecture` — `(1 − ε)·(n/2) ≤ log₂ (f n)` — holds for *every* `ε > 0` and
*every* `n`, with no threshold `N` and no axiom.  It follows from the exact bound
`log₂ (f n) ≥ n/2` (`logDiv_log_two_f_ge`) since `(1 − ε)·(n/2) ≤ n/2`.  So only the upper
half of the conjecture carries the Green/Sapozhenko content. -/
theorem cameronErdos_lower_unconditional {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (1 - ε) * (n / 2 : ℝ) ≤ Real.log (f n) / Real.log 2 := by
  have hhalf : (0 : ℝ) ≤ (n / 2 : ℝ) := by positivity
  calc (1 - ε) * (n / 2 : ℝ)
        ≤ 1 * (n / 2 : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hhalf
    _ = (n / 2 : ℝ) := one_mul _
    _ ≤ Real.log (f n) / Real.log 2 := logDiv_log_two_f_ge n

/--
**Erdős Problem #748: PROVED**
-/
theorem erdos_748 : cameronErdosConjecture := cameron_erdos_proved

end Erdos748
