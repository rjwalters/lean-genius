/-
Kummer's Theorem OQ-02-OQ-03: Mixed-Radix Carry Law

Parent (q-Kummer, KummerTheoremOQ02) established that for a *single* base d ≥ 2,
the cyclotomic multiplicity of Φ_d in the q-binomial [n choose k]_q equals the
floor deficiency

    e_d = ⌊n/d⌋ − ⌊k/d⌋ − ⌊(n−k)/d⌋ ∈ {0, 1},

which is exactly the carry crossing the d-boundary when adding k and (n−k) in
base d.  Parent open question #3 asks:

    "Can the floor deficiency be related to carries in MIXED-RADIX numeral systems?"

This file answers it.  We fix an arbitrary sequence of bases  b : ℕ → ℕ  (each
b i ≥ 1) with positional weights

    W₀ = 1,   W_{i+1} = W_i · b_i,

so a number is written in the mixed-radix system  (b₀, b₁, b₂, …)  with digit
    digᵢ(x) = ⌊x / Wᵢ⌋ mod bᵢ.

For two summands a, c the per-weight floor deficiency is

    δ(j) = ⌊(a+c)/W_j⌋ − ⌊a/W_j⌋ − ⌊c/W_j⌋ ∈ {0, 1},

and δ(i+1) is precisely the carry out of digit position i (it is 1 iff the low
parts overflow:  W_{i+1} ≤ a mod W_{i+1} + c mod W_{i+1}).  The headline result
is the mixed-radix generalization of Kummer's carry/digit-sum identity:

    S(a) + S(c) = S(a+c) + Σ_i δ(i+1) · (b_i − 1),                    (★)

where S is the mixed-radix digit sum.  When every b_i equals a fixed d this
collapses to the classical law  s_d(a) + s_d(c) − s_d(a+c) = (d−1)·#carries,
the number of carries being Σ_i δ(i+1) (a sum of {0,1} indicators).

Main results:
1. `mixedWeight_pos`        — the positional weights are positive
2. `defc_eq_indicator`      — δ(i+1) is the carry indicator (∈ {0,1})  [Engine: Nat.add_div]
3. `mixedDigit_eq`          — digit recurrence  digᵢ(x) = ⌊x/Wᵢ⌋ − bᵢ·⌊x/W_{i+1}⌋
4. `mixedRadix_kummer`      — the carry law (★)
5. `const_base_carry_law`   — specialization recovering the classical single-base law

Everything is elementary (ℕ/ℤ arithmetic + Finset telescoping); no axioms beyond
Mathlib's foundations.

References:
- Kummer (1852): carries and binomial valuations
- Cantor (1869): mixed-radix numeral systems
- Parent: KummerTheoremOQ02 (q-Kummer, floorDeficiency)
-/

import Mathlib

namespace KummerTheoremOQ02OQ03

open Finset

-- ══════════════════════════════════════════════════════════════════
-- § Part I: Mixed-radix weights, digits, and digit sums
-- ══════════════════════════════════════════════════════════════════

/-- Positional weights of the mixed-radix system with base sequence `b`:
    `W₀ = 1` and `W_{i+1} = W_i · b_i`.  So `W_i = b₀·b₁·⋯·b_{i-1}`. -/
def mixedWeight (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | (i + 1) => mixedWeight b i * b i

@[simp] theorem mixedWeight_zero (b : ℕ → ℕ) : mixedWeight b 0 = 1 := rfl

theorem mixedWeight_succ (b : ℕ → ℕ) (i : ℕ) :
    mixedWeight b (i + 1) = mixedWeight b i * b i := rfl

/-- All weights are positive when every base is. -/
theorem mixedWeight_pos (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) :
    ∀ i, 0 < mixedWeight b i
  | 0 => by simp
  | (i + 1) => by
    rw [mixedWeight_succ]
    exact Nat.mul_pos (mixedWeight_pos b hb i) (hb i)

/-- The `i`-th mixed-radix digit of `x`. -/
def mixedDigit (b : ℕ → ℕ) (i x : ℕ) : ℕ := (x / mixedWeight b i) % b i

/-- The mixed-radix digit sum of `x` over the first `N` positions. -/
def mixedDigitSum (b : ℕ → ℕ) (N x : ℕ) : ℕ :=
  ∑ i ∈ range N, mixedDigit b i x

/-- The floor deficiency of `a + c` at weight `W_j`:
    `δ(j) = ⌊(a+c)/W_j⌋ − ⌊a/W_j⌋ − ⌊c/W_j⌋`, an integer (always ≥ 0). -/
def defc (b : ℕ → ℕ) (a c j : ℕ) : ℤ :=
  (((a + c) / mixedWeight b j : ℕ) : ℤ) - ((a / mixedWeight b j : ℕ) : ℤ)
    - ((c / mixedWeight b j : ℕ) : ℤ)

-- ══════════════════════════════════════════════════════════════════
-- § Part II: The carry indicator (Engine — Nat.add_div)
-- ══════════════════════════════════════════════════════════════════

/-- `δ(0) = 0`: the weight `W₀ = 1` divides everything. -/
@[simp] theorem defc_zero (b : ℕ → ℕ) (a c : ℕ) : defc b a c 0 = 0 := by
  simp [defc]

/-- Above the top weight the deficiency vanishes: if `a + c < W_N` then `δ(N) = 0`. -/
theorem defc_high (b : ℕ → ℕ) (a c N : ℕ) (hN : a + c < mixedWeight b N) :
    defc b a c N = 0 := by
  have ha : a < mixedWeight b N := lt_of_le_of_lt (Nat.le_add_right a c) hN
  have hc : c < mixedWeight b N := lt_of_le_of_lt (Nat.le_add_left c a) hN
  simp only [defc, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hN]
  norm_num

/-- **Carry indicator.** The deficiency at weight `W_{j+1}` is exactly the carry
    crossing that boundary: it is `1` when the low parts overflow and `0`
    otherwise.  This is Kummer's "carry" reading, now at a mixed-radix weight. -/
theorem defc_eq_indicator (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) (a c j : ℕ) :
    defc b a c (j + 1) =
      (if mixedWeight b (j + 1) ≤ a % mixedWeight b (j + 1) + c % mixedWeight b (j + 1)
        then 1 else 0) := by
  have hW : 0 < mixedWeight b (j + 1) := mixedWeight_pos b hb (j + 1)
  have h : (a + c) / mixedWeight b (j + 1)
      = a / mixedWeight b (j + 1) + c / mixedWeight b (j + 1)
        + (if mixedWeight b (j + 1) ≤ a % mixedWeight b (j + 1) + c % mixedWeight b (j + 1)
            then 1 else 0) := Nat.add_div hW
  simp only [defc]
  rw [h]
  split <;> push_cast <;> ring

/-- The carry indicator is `0` or `1`. -/
theorem defc_mem_zero_one (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) (a c j : ℕ) :
    defc b a c (j + 1) = 0 ∨ defc b a c (j + 1) = 1 := by
  rw [defc_eq_indicator b hb]
  split
  · right; rfl
  · left; rfl

/-- A carry happens at position `j` exactly when the low parts overflow `W_{j+1}`. -/
theorem defc_eq_one_iff (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) (a c j : ℕ) :
    defc b a c (j + 1) = 1 ↔
      mixedWeight b (j + 1) ≤ a % mixedWeight b (j + 1) + c % mixedWeight b (j + 1) := by
  rw [defc_eq_indicator b hb]
  split <;> simp_all

-- ══════════════════════════════════════════════════════════════════
-- § Part III: The digit recurrence and digit-sum expansion
-- ══════════════════════════════════════════════════════════════════

/-- The mixed-radix digit recurrence (over ℤ):
    `digᵢ(x) = ⌊x/Wᵢ⌋ − bᵢ · ⌊x/W_{i+1}⌋`.
    This is just `(x/Wᵢ) mod bᵢ` rewritten via `Nat.mod_add_div` together with
    `⌊⌊x/Wᵢ⌋ / bᵢ⌋ = ⌊x/W_{i+1}⌋`. -/
theorem mixedDigit_eq (b : ℕ → ℕ) (i x : ℕ) :
    (mixedDigit b i x : ℤ) =
      ((x / mixedWeight b i : ℕ) : ℤ)
        - (b i : ℤ) * ((x / mixedWeight b (i + 1) : ℕ) : ℤ) := by
  have hdd : x / mixedWeight b i / b i = x / mixedWeight b (i + 1) := by
    rw [Nat.div_div_eq_div_mul]; rfl
  have h1 : (x / mixedWeight b i) % b i + b i * (x / mixedWeight b i / b i)
      = x / mixedWeight b i := Nat.mod_add_div _ _
  rw [hdd] at h1
  have h1' : ((x / mixedWeight b i % b i : ℕ) : ℤ)
      + (b i : ℤ) * ((x / mixedWeight b (i + 1) : ℕ) : ℤ)
        = ((x / mixedWeight b i : ℕ) : ℤ) := by
    exact_mod_cast h1
  simp only [mixedDigit]
  linarith

/-- The digit sum expanded as a telescoping-ready ℤ sum. -/
theorem mixedDigitSum_expand (b : ℕ → ℕ) (N x : ℕ) :
    (mixedDigitSum b N x : ℤ) =
      ∑ i ∈ range N,
        (((x / mixedWeight b i : ℕ) : ℤ)
          - (b i : ℤ) * ((x / mixedWeight b (i + 1) : ℕ) : ℤ)) := by
  simp only [mixedDigitSum, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => mixedDigit_eq b i x)

-- ══════════════════════════════════════════════════════════════════
-- § Part IV: The mixed-radix Kummer carry law
-- ══════════════════════════════════════════════════════════════════

/-- Combined digit-sum difference as a single sum of per-position terms
    `bᵢ·δ(i+1) − δ(i)`. -/
theorem mixedDigitSum_diff (b : ℕ → ℕ) (a c N : ℕ) :
    (mixedDigitSum b N a : ℤ) + mixedDigitSum b N c - mixedDigitSum b N (a + c)
      = ∑ i ∈ range N, ((b i : ℤ) * defc b a c (i + 1) - defc b a c i) := by
  rw [mixedDigitSum_expand b N a, mixedDigitSum_expand b N c,
      mixedDigitSum_expand b N (a + c), ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [defc]
  push_cast
  ring

/-- **Mixed-radix Kummer carry law.**
    For any base sequence `b` (each `bᵢ ≥ 1`) and any `N` with `a + c < W_N`,

        S(a) + S(c) = S(a+c) + Σ_{i<N} δ(i+1) · (bᵢ − 1),

    where `S = mixedDigitSum` and `δ(i+1)` is the carry out of position `i`.
    The right-hand sum is the carry contribution weighted by `bᵢ − 1`; with each
    `δ(i+1) ∈ {0,1}` (see `defc_mem_zero_one`, which needs `bᵢ ≥ 1`) it literally
    counts carries.  The identity itself is purely algebraic and needs no
    hypothesis on the bases. -/
theorem mixedRadix_kummer (b : ℕ → ℕ) (a c N : ℕ)
    (hN : a + c < mixedWeight b N) :
    (mixedDigitSum b N a : ℤ) + mixedDigitSum b N c
      = (mixedDigitSum b N (a + c) : ℤ)
        + ∑ i ∈ range N, defc b a c (i + 1) * ((b i : ℤ) - 1) := by
  have hdiff := mixedDigitSum_diff b a c N
  -- rewrite each per-position term:  bᵢ·δ(i+1) − δ(i)
  --   = δ(i+1)·(bᵢ−1) + (δ(i+1) − δ(i))
  have hsplit :
      ∑ i ∈ range N, ((b i : ℤ) * defc b a c (i + 1) - defc b a c i)
        = (∑ i ∈ range N, defc b a c (i + 1) * ((b i : ℤ) - 1))
          + ∑ i ∈ range N, (defc b a c (i + 1) - defc b a c i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- telescoping
  have htel : ∑ i ∈ range N, (defc b a c (i + 1) - defc b a c i)
      = defc b a c N - defc b a c 0 :=
    Finset.sum_range_sub (fun i => defc b a c i) N
  have key : (mixedDigitSum b N a : ℤ) + mixedDigitSum b N c - mixedDigitSum b N (a + c)
      = ∑ i ∈ range N, defc b a c (i + 1) * ((b i : ℤ) - 1) := by
    rw [hdiff, hsplit, htel, defc_zero, defc_high b a c N hN]
    ring
  linarith [key]

-- ══════════════════════════════════════════════════════════════════
-- § Part V: Recovering the classical single-base law
-- ══════════════════════════════════════════════════════════════════

/-- For a constant base `d`, the mixed-radix weights are the powers `d^i`. -/
theorem mixedWeight_const (d : ℕ) : ∀ i, mixedWeight (fun _ => d) i = d ^ i
  | 0 => by simp
  | (i + 1) => by rw [mixedWeight_succ, mixedWeight_const d i, pow_succ]

/-- **Classical Kummer/Legendre digit-sum law, recovered.**
    Taking every base equal to a fixed `d ≥ 1` collapses (★) to

        s_d(a) + s_d(c) = s_d(a+c) + (d − 1) · Σ_{i<N} δ(i+1),

    i.e. `s_d(a) + s_d(c) − s_d(a+c) = (d−1) · (number of carries)`, the standard
    statement for ordinary base-`d` addition. -/
theorem const_base_carry_law (d a c N : ℕ) (hN : a + c < d ^ N) :
    (mixedDigitSum (fun _ => d) N a : ℤ) + mixedDigitSum (fun _ => d) N c
      = (mixedDigitSum (fun _ => d) N (a + c) : ℤ)
        + ((d : ℤ) - 1) * ∑ i ∈ range N, defc (fun _ => d) a c (i + 1) := by
  have hN' : a + c < mixedWeight (fun _ => d) N := by
    rwa [mixedWeight_const]
  have h := mixedRadix_kummer (fun _ => d) a c N hN'
  -- factor the constant `(d − 1)` out of the carry sum (matching `h`'s RHS exactly)
  have e : ∑ i ∈ range N, defc (fun _ => d) a c (i + 1) * (((fun _ => d) i : ℤ) - 1)
      = ((d : ℤ) - 1) * ∑ i ∈ range N, defc (fun _ => d) a c (i + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show defc (fun _ => d) a c (i + 1) * ((d : ℤ) - 1)
        = ((d : ℤ) - 1) * defc (fun _ => d) a c (i + 1)
    ring
  rw [e] at h
  exact h

end KummerTheoremOQ02OQ03
