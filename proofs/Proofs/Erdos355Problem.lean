/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2ebf5c7a-116c-437b-b939-5baf0dc3a8cd

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem lacunary_strictMono (a : ℕ → ℕ) (lam : ℝ) (h : IsLacunaryWith a lam) :
    StrictMono a

- theorem lacunary_reciprocal_sum_converges (a : ℕ → ℕ) (h : IsLacunary a) :
    ∃ S : ℝ, ∀ ε > 0, ∃ N, ∀ n ≥ N, |∑ i ∈ range n, (1 : ℝ) / a i - S| < ε

- theorem powers_of_two_gaps :
    ¬∃ u v : ℝ, u < v ∧ RepresentsRationalsIn (fun n => 2^(n+1)) u v
-/

/-
Erdős Problem #355: Lacunary Sequences and Rational Representation

Source: https://erdosproblems.com/355
Status: SOLVED (van Doorn & Kovač 2025) - Answer is YES

Statement:
Is there a lacunary sequence A ⊆ ℕ (where a_{n+1}/a_n ≥ λ > 1 for all n) such that
the set of all finite reciprocal sums { ∑_{a ∈ A'} 1/a : A' ⊆ A finite } contains
all rationals in some open interval?

Answer: YES, for any lacunarity constant λ ∈ (1,2), though not for λ = 2.

Historical Context:
- Bleicher and Erdős conjectured the answer was NO [BlEr76, p.167]
- van Doorn and Kovač proved YES for λ ∈ (1,2) [DoKo25, arXiv:2509.24971]
- The construction uses carefully chosen lacunary sequences to achieve density

References:
- [DoKo25] van Doorn, W. and Kovač, V., "Lacunary sequences whose reciprocal sums
  represent all rationals in an interval", arXiv:2509.24971 (2025)
- [BlEr76] Bleicher, M. N. and Erdős, P., "Denominators of Egyptian fractions I",
  Journal of Number Theory (1976)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic


open Finset Set

namespace Erdos355

/-
## Part I: Definitions

We define lacunary sequences and the set of achievable reciprocal sums.
-/

/-- A sequence is lacunary with parameter lam > 1 if consecutive terms
    satisfy a_{n+1}/a_n ≥ lam for all n. This means the sequence grows
    at least exponentially. -/
def IsLacunaryWith (a : ℕ → ℕ) (lam : ℝ) : Prop :=
  lam > 1 ∧ (∀ n, a n > 0) ∧ ∀ n, (a (n + 1) : ℝ) / a n ≥ lam

/-- A sequence is lacunary if it's lacunary for some lam > 1. -/
def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∃ lam > 1, (∀ n, a n > 0) ∧ ∀ n, (a (n + 1) : ℝ) / a n ≥ lam

/-- The set of all finite reciprocal sums achievable from a sequence.
    For any finite subset of the sequence's range, we can sum their reciprocals. -/
def ReciprocalSums (a : ℕ → ℕ) : Set ℚ :=
  { q | ∃ (S : Finset ℕ) (k : ℕ), (∀ i ∈ S, i < k) ∧
        q = ∑ i ∈ S, (1 : ℚ) / a i }

/-- Alternative characterization using index subsets. -/
def ReciprocalSumsAlt (a : ℕ → ℕ) : Set ℚ :=
  { ∑ i ∈ S, (1 : ℚ) / a i | S : Finset ℕ }

/-- A sequence represents all rationals in an interval if every rational
    in that interval is a finite reciprocal sum from the sequence. -/
def RepresentsRationalsIn (a : ℕ → ℕ) (u v : ℝ) : Prop :=
  u < v ∧ ∀ q : ℚ, u < q ∧ (q : ℝ) < v → q ∈ ReciprocalSumsAlt a

/-
## Part II: Properties of Lacunary Sequences

Lacunary sequences grow exponentially and have convergent reciprocal sums.
-/

/-- A lacunary sequence is strictly increasing. -/
theorem lacunary_strictMono (a : ℕ → ℕ) (lam : ℝ) (h : IsLacunaryWith a lam) :
    StrictMono a := by
  intro m n hmn
  -- Since a_{n+1}/a_n ≥ lam > 1, we have a_{n+1} > a_n
  -- Repeated application shows a_m < a_n when m < n
  -- Since $a$ is lacunary with parameter $\lambda > 1$, we have $a (n + 1) / a n \geq \lambda$ for all $n$.
  obtain ⟨hlam, hpos, hdiv⟩ := h;
  have h_seq_inc : ∀ n, a (n + 1) > a n := by
    exact fun n => by have := hdiv n; rw [ ge_iff_le ] at this; rw [ le_div_iff₀ ( Nat.cast_pos.mpr ( hpos n ) ) ] at this; exact_mod_cast ( by nlinarith [ ( by norm_cast; linarith [ hpos n ] : ( 1 :ℝ ) ≤ a n ) ] : ( a n :ℝ ) < a ( n + 1 ) ) ;
  exact ( strictMono_nat_of_lt_succ h_seq_inc ) hmn

/-- The sum of reciprocals of a lacunary sequence converges. -/
theorem lacunary_reciprocal_sum_converges (a : ℕ → ℕ) (h : IsLacunary a) :
    ∃ S : ℝ, ∀ ε > 0, ∃ N, ∀ n ≥ N, |∑ i ∈ range n, (1 : ℝ) / a i - S| < ε := by
  -- The series ∑ 1/a_n converges by comparison with geometric series
  have h_abs_conv : Summable (fun i => (1 / (a i) : ℝ)) := by
    have h_lam_gt_1 : ∃ lam > 1, (∀ n, a n > 0) ∧ ∀ n, (a (n + 1) : ℝ) / (a n) ≥ lam := h
    obtain ⟨ lam, hl1, hl2, hl3 ⟩ := h_lam_gt_1
    have h_exp_growth : ∀ n, a n ≥ a 0 * lam ^ n := by
      exact fun x => Nat.recOn x ( by norm_num ) fun n ihn => by have := hl3 n; rw [ ge_iff_le, le_div_iff₀ ( Nat.cast_pos.mpr <| hl2 _ ) ] at this; push_cast [ pow_succ' ] at *; nlinarith;
    have h_summable : Summable (fun i => (1 / (a 0 * lam ^ i) : ℝ)) := by
      simpa using Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ hl1 ) );
    exact Summable.of_nonneg_of_le ( fun i => one_div_nonneg.mpr ( Nat.cast_nonneg _ ) ) ( fun i => one_div_le_one_div_of_le ( mul_pos ( Nat.cast_pos.mpr ( hl2 _ ) ) ( pow_pos ( zero_lt_one.trans hl1 ) _ ) ) ( h_exp_growth _ ) ) h_summable;
  exact ⟨ _, Metric.tendsto_atTop.mp h_abs_conv.hasSum.tendsto_sum_nat ⟩

/-- Powers of 2 form a lacunary sequence with lam = 2. -/
theorem powers_of_two_lacunary : IsLacunaryWith (fun n => 2^(n+1)) 2 := by
  constructor
  · norm_num
  constructor
  · intro n
    positivity
  · intro n
    simp only
    have h1 : (2 ^ (n + 1) : ℕ) > 0 := by positivity
    have h2 : (2 ^ (n + 1 + 1) : ℕ) = 2 * 2 ^ (n + 1) := by ring
    have h3 : ((2 ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [h2]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_div_assoc, div_self h3, mul_one]

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos355.geometric_series_sum', 'harmonicSorry405658']-/
/-
## Part III: The Critical λ = 2 Boundary

Powers of 2 (λ = 2) cannot represent all rationals in any interval.
-/

/-- The sum of all reciprocals of powers of 2 is exactly 1.
    ∑_{n=1}^∞ 1/2^n = 1 (geometric series). -/
axiom geometric_series_sum : ∑' n, (1 : ℝ) / 2^(n+1) = 1

/- For λ = 2 (powers of 2), the achievable sums are exactly the dyadic rationals
    in [0, 1]. These are rationals of the form k/2^n and don't fill any interval. -/
noncomputable section AristotleLemmas

/-
The denominator of a finite sum of reciprocals of powers of 2 is itself a power of 2.
-/
open Finset Set

lemma Erdos355.sum_pow_two_den_pow_two (S : Finset ℕ) : ∃ n : ℕ, (∑ i ∈ S, (1 : ℚ) / 2^(i+1)).den = 2 ^ n := by
  -- The sum $\sum_{i \in S} \frac{1}{2^{i+1}}$ can be written as $\frac{m}{2^k}$ for some integer $m$ and natural $k$.
  obtain ⟨m, k, hmk⟩ : ∃ m : ℤ, ∃ k : ℕ, (∑ i ∈ S, (1 : ℚ) / (2 ^ (i + 1))) = m / 2 ^ k := by
    field_simp;
    use ∑ x ∈ S, 2 ^ ( Finset.sup S id - x ), Finset.sup S id + 1;
    norm_num [ Finset.sum_mul _ _ _ ];
    refine Finset.sum_congr rfl fun x hx => ?_ ; rw [ inv_mul_eq_div, div_eq_iff ( by positivity ) ] ; ring;
    rw [ ← pow_add, Nat.sub_add_cancel ( show x ≤ S.sup id from Finset.le_sup ( f := id ) hx ) ];
  rw [ hmk ];
  -- The denominator of a fraction $m / 2^k$ is $2^k$.
  have h_denom : ((m : ℚ) / 2 ^ k).den ∣ 2 ^ k := by
    erw [ div_eq_mul_inv ];
    erw [ Rat.mul_den ] ; norm_num;
    exact Nat.div_dvd_of_dvd <| Nat.gcd_dvd_right _ _;
  rw [ Nat.dvd_prime_pow ] at h_denom <;> norm_num at * ; tauto

/-
A rational number with an odd denominator greater than 1 cannot be represented as a sum of reciprocals of powers of 2.
-/
open Finset Set

lemma Erdos355.not_rep_of_odd_denom_gt_one (q : ℚ) (h_odd : q.den % 2 = 1) (h_gt_1 : q.den > 1) :
    q ∉ ReciprocalSumsAlt (fun n => 2^(n+1)) := by
      rintro ⟨ S, rfl ⟩;
      have := Erdos355.sum_pow_two_den_pow_two S;
      aesop

/-
We define triadic rationals as those of the form k/3^n.
We prove that the denominator of a triadic rational is odd.
-/
open Finset Set

def Erdos355.IsTriadic (q : ℚ) : Prop := ∃ k : ℤ, ∃ n : ℕ, q = k / (3 ^ n : ℚ)

lemma Erdos355.isTriadic_odd_den (q : ℚ) (h : Erdos355.IsTriadic q) : Odd q.den := by
  cases' h with n hn;
  -- Since $q = n / 3^n_1$, the denominator $q.den$ must be $3^n_1$.
  obtain ⟨n_1, hn_eq⟩ := hn
  have h_den : q.den ∣ 3 ^ n_1 := by
    rw [ hn_eq ];
    norm_num [ div_eq_mul_inv, Rat.mul_den ];
    exact Nat.div_dvd_of_dvd <| Nat.gcd_dvd_right _ _;
  exact Odd.of_dvd_nat ( by exact Odd.pow ( by decide ) ) h_den

/-
In any open interval (u, v), there exists a triadic rational.
-/
open Finset Set

lemma Erdos355.exists_triadic_in_interval (u v : ℝ) (h : u < v) :
    ∃ q : ℚ, u < q ∧ q < v ∧ Erdos355.IsTriadic q := by
      -- Choose n such that 1/3^n < v - u.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 : ℝ) / 3 ^ n < v - u := by
        simpa using exists_pow_lt_of_lt_one ( sub_pos.mpr h ) ( by norm_num : ( 1 : ℝ ) / 3 < 1 );
      -- Let this multiple be k/3^n. It is a triadic rational.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, u < k / (3 ^ n : ℚ) ∧ k / (3 ^ n : ℚ) < v := by
        use ⌊3^n * u⌋ + 1;
        norm_num at *;
        constructor <;> nlinarith [ Int.floor_le ( 3 ^ n * u ), Int.lt_floor_add_one ( 3 ^ n * u ), pow_pos ( zero_lt_three' ℝ ) n, mul_div_cancel₀ ( ( ⌊3 ^ n * u⌋ : ℝ ) + 1 ) ( by positivity : ( 3 ^ n : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( 3 ^ n : ℝ ) ≠ 0 ) ];
      exact ⟨ k / 3 ^ n, by simpa using hk.1, by simpa using hk.2, ⟨ k, n, by ring ⟩ ⟩

/-
In any open interval (u, v), there exists a rational with odd denominator greater than 1.
-/
open Finset Set

lemma Erdos355.exists_odd_denom_gt_one_in_interval (u v : ℝ) (h : u < v) :
    ∃ q : ℚ, u < q ∧ q < v ∧ Odd q.den ∧ q.den > 1 := by
      by_contra h_contra;
      -- Choose $n$ such that $3^n > 2 / (v - u)$. Then $1/3^n < (v - u) / 2$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 : ℝ) / 3 ^ n < (v - u) / 2 := by
        simpa using exists_pow_lt_of_lt_one ( half_pos ( sub_pos.mpr h ) ) ( by norm_num : ( 1 : ℝ ) / 3 < 1 );
      -- The interval $(u, v)$ has length $v - u > 2/3^n$, so it contains at least two multiples of $1/3^n$.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, (u < (k : ℝ) / 3 ^ n ∧ (k : ℝ) / 3 ^ n < v) ∧ (u < ((k + 1) : ℝ) / 3 ^ n ∧ ((k + 1) : ℝ) / 3 ^ n < v) := by
        refine' ⟨ ⌊u * 3 ^ n⌋ + 1, _, _, _ ⟩ <;> norm_num at *;
        · exact ⟨ by rw [ lt_div_iff₀ ( by positivity ) ] ; linarith [ Int.lt_floor_add_one ( u * 3 ^ n ) ], by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Int.floor_le ( u * 3 ^ n ), Int.lt_floor_add_one ( u * 3 ^ n ), pow_pos ( by norm_num : ( 0 : ℝ ) < 3 ) n, mul_inv_cancel₀ ( by positivity : ( 3 : ℝ ) ^ n ≠ 0 ) ] ⟩;
        · rw [ lt_div_iff₀ ] <;> first | positivity | linarith [ Int.lt_floor_add_one ( u * 3 ^ n ) ] ;
        · rw [ div_lt_iff₀ ] <;> nlinarith [ Int.floor_le ( u * 3 ^ n ), Int.lt_floor_add_one ( u * 3 ^ n ), show ( 3 : ℝ ) ^ n > 0 by positivity, mul_inv_cancel₀ ( show ( 3 : ℝ ) ^ n ≠ 0 by positivity ) ];
      -- At most one of them can be an integer (since integers are distance 1 apart, and $1/3^n < 1/2 < 1$).
      have h_int : ¬(∃ m : ℤ, (k : ℝ) / 3 ^ n = m) ∨ ¬(∃ m : ℤ, ((k + 1) : ℝ) / 3 ^ n = m) := by
        by_cases h_int_k : ∃ m : ℤ, (k : ℝ) / 3 ^ n = m;
        · simp_all +decide [ div_eq_iff ];
          intro x hx; norm_cast at *; replace hx := congr_arg ( fun z => z % 3 ^ n ) hx; norm_num [ Int.add_emod, Int.mul_emod ] at hx;
          rcases h_int_k with ⟨ m, rfl ⟩ ; norm_num [ Int.add_emod, Int.mul_emod ] at hx;
          rw [ Int.dvd_iff_emod_eq_zero ] at hx; rcases n with ( _ | _ | n ) <;> norm_num [ pow_succ' ] at *;
          · have := h_contra ( m + 1 / 3 ) ?_ ?_ ?_ <;> norm_num at *;
            · linarith;
            · linarith;
          · exact absurd ( Int.le_of_dvd ( by norm_num ) hx ) ( by linarith [ pow_pos ( by norm_num : ( 0 : ℤ ) < 3 ) n ] );
        · exact Or.inl h_int_k;
      -- Pick the one that is not an integer. Let it be $q$.
      obtain ⟨q, hq⟩ : ∃ q : ℚ, u < q ∧ q < v ∧ IsTriadic q ∧ ¬(∃ m : ℤ, q = m) := by
        rcases h_int with h_int | h_int <;> [ refine' ⟨ k / 3 ^ n, _, _, _, _ ⟩ ; refine' ⟨ ( k + 1 ) / 3 ^ n, _, _, _, _ ⟩ ] <;> norm_cast at * <;> simp_all +decide [ div_eq_mul_inv ];
        · exact ⟨ k, n, by simp +decide [ Rat.divInt_eq_div ] ⟩;
        · exact ⟨ k + 1, n, by simp +decide [ Rat.divInt_eq_div ] ⟩;
      refine h_contra ⟨ q, hq.1, hq.2.1, ?_, ?_ ⟩;
      · exact Erdos355.isTriadic_odd_den q hq.2.2.1;
      · exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ q.pos.ne', fun h => hq.2.2.2 ⟨ q.num, by simpa [ h ] using q.num_div_den.symm ⟩ ⟩

end AristotleLemmas

theorem powers_of_two_gaps :
    ¬∃ u v : ℝ, u < v ∧ RepresentsRationalsIn (fun n => 2^(n+1)) u v := by
  -- Dyadic rationals are nowhere dense in ℝ, so any interval (u,v) contains
  -- non-dyadic rationals that cannot be represented
  intro ⟨u, v, huv, hrep⟩
  -- For example, 1/3 cannot be expressed as a finite sum of powers of 1/2
  -- Choose an interval containing 1/3
  -- By definition, this means every rational q in (u, v) is in ReciprocalSumsAlt (fun n => 2^(n+1)).
  obtain ⟨q, hq⟩ : ∃ q : ℚ, u < q ∧ q < v ∧ Odd q.den ∧ q.den > 1 := Erdos355.exists_odd_denom_gt_one_in_interval u v huv;
  exact Erdos355.not_rep_of_odd_denom_gt_one q ( Nat.odd_iff.mp hq.2.2.1 ) hq.2.2.2 ( hrep.2 q ⟨ hq.1, hq.2.1 ⟩ )

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry624596', 'Erdos355.vanDoorn_Kovac_theorem']-/
/-
## Part IV: van Doorn-Kovač Theorem (Main Result)

For λ ∈ (1, 2), there exist lacunary sequences whose reciprocal sums
represent all rationals in an interval.
-/

/-- **van Doorn-Kovač Theorem (2025)** - Erdős Problem #355 SOLVED

    For any lacunarity constant lam ∈ (1, 2), there exists a lacunary sequence
    A with ratio parameter lam such that the set of finite reciprocal sums
    from A contains all rationals in some open interval.

    This resolved Erdős Problem #355 in the affirmative, disproving the
    Bleicher-Erdős conjecture. -/
axiom vanDoorn_Kovac_theorem :
  ∀ lam : ℝ, 1 < lam ∧ lam < 2 →
    ∃ (a : ℕ → ℕ), IsLacunaryWith a lam ∧ ∃ u v : ℝ, RepresentsRationalsIn a u v

/-- The main theorem: there exists a lacunary sequence whose reciprocal sums
    contain all rationals in some open interval. -/
theorem erdos_355_solved :
    ∃ (a : ℕ → ℕ), IsLacunary a ∧ ∃ u v : ℝ, RepresentsRationalsIn a u v := by
  -- Take lam = 3/2 which is in (1, 2)
  have h32 : (1 : ℝ) < (3 : ℝ)/2 ∧ (3 : ℝ)/2 < 2 := by norm_num
  obtain ⟨a, hLac, u, v, hrep⟩ := vanDoorn_Kovac_theorem ((3 : ℝ)/2) h32
  exact ⟨a, ⟨(3 : ℝ)/2, h32.1, hLac.2⟩, u, v, hrep⟩

/-- Alternative statement matching formal-conjectures format. -/
theorem erdos_355 :
    ∃ A : ℕ → ℕ, IsLacunary A ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, ↑q ∈ Ioo u v →
      q ∈ ReciprocalSumsAlt A := by
  obtain ⟨a, hLac, u, v, ⟨huv, hrep⟩⟩ := erdos_355_solved
  use a, hLac, u, v, huv
  intro q ⟨hqu, hqv⟩
  exact hrep q ⟨hqu, hqv⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry512907', 'Erdos355.lambda_two_fails']-/
/-
## Part V: The Sharp Boundary

The condition λ < 2 is necessary. For λ = 2, no lacunary sequence works.
-/

/-- For λ ≥ 2, no lacunary sequence can represent all rationals in an interval. -/
axiom lambda_two_fails :
  ∀ (a : ℕ → ℕ), IsLacunaryWith a 2 →
    ¬∃ u v : ℝ, RepresentsRationalsIn a u v

/-- The threshold lam = 2 is sharp: (1,2) works, [2,∞) doesn't. -/
theorem sharp_threshold :
    (∀ lam : ℝ, 1 < lam ∧ lam < 2 →
      ∃ (a : ℕ → ℕ), IsLacunaryWith a lam ∧ ∃ u v, RepresentsRationalsIn a u v) ∧
    (∀ (a : ℕ → ℕ), IsLacunaryWith a 2 →
      ¬∃ u v : ℝ, RepresentsRationalsIn a u v) :=
  ⟨vanDoorn_Kovac_theorem, lambda_two_fails⟩

/-
## Part VI: Examples and Intuition

Understanding why the gap at λ = 2 exists.
-/

/-- Example: {1, 2, 3, 5, 8, 13, ...} (Fibonacci-like) has λ ≈ φ ≈ 1.618.
    Since 1 < φ < 2, this sequence could represent rationals in an interval. -/
def fibLikeSeq : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => fibLikeSeq n + fibLikeSeq (n + 1)

/-- The Fibonacci-like sequence has positive terms. -/
theorem fibLikeSeq_pos : ∀ n, fibLikeSeq n > 0 := by
  intro n
  induction n with
  | zero => simp [fibLikeSeq]
  | succ n ih =>
    cases n with
    | zero => simp [fibLikeSeq]
    | succ m =>
      simp only [fibLikeSeq]
      omega

/-- Key insight: Why does λ < 2 work but λ = 2 fail?

    For λ = 2 (powers of 2), the reciprocal sums are dyadic rationals k/2^n.
    These form a discrete set with gaps, so they can't fill an interval.

    For λ < 2, the overlap between consecutive "levels" of the sequence
    allows the reciprocal sums to become dense, eventually covering all
    rationals in some interval.

    The van Doorn-Kovač proof constructs explicit sequences achieving this. -/
theorem intuition_explained : True := trivial

/-- Summary: Erdős Problem #355 (SOLVED - YES)

    Main Results:
    1. For λ ∈ (1,2): There exist lacunary sequences whose reciprocal sums
       represent all rationals in an open interval (van Doorn-Kovač 2025)
    2. For λ = 2: No such sequence exists (powers of 2 give only dyadic rationals)
    3. The Bleicher-Erdős conjecture (that no such sequence exists) was disproved -/
theorem erdos_355_summary :
    (∃ (a : ℕ → ℕ), IsLacunary a ∧ ∃ u v : ℝ, RepresentsRationalsIn a u v) ∧
    IsLacunaryWith (fun n => 2^(n+1)) 2 ∧
    (1 : ℝ) < (3 : ℝ)/2 ∧ (3 : ℝ)/2 < 2 := by
  refine ⟨erdos_355_solved, powers_of_two_lacunary, ?_, ?_⟩ <;> norm_num

end Erdos355