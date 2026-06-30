import Mathlib

/-!
# Waring g(k) Lower Bound — Parametric / General-k (S24 ACT)

This file ships a **parametric** lower-bound theorem for slug
`lagrange-four-squares-waring-g2-oq-01`, subsuming the five fixed-`k`
instances already in the gallery
(`…OQ01.lean` k=3, `…Counting.lean` k=3, `…CountingG4/G5/G6/G7.lean`)
into a single statement that holds for **every** `k ≥ 1`:

> For every `k ≥ 1`, the integer `n_k = ⌊(3/2)^k⌋ · 2^k − 1` is **not** a
> sum of `2^k + ⌊(3/2)^k⌋ − 3` perfect `k`-th powers.
> Equivalently `g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2`.

In `ℕ`, `⌊(3/2)^k⌋ = 3^k / 2^k` (truncated division). The witness
`n_k = (3^k / 2^k) · 2^k − 1` instantiates to the classical lower-bound
witnesses for the small cases:

| k | M=2^k | Q=⌊(3/2)^k⌋ | n_k = Q·M−1 | g(k)=M+Q−2 (= OEIS A002804) |
|--:|------:|------------:|------------:|----------------------------:|
| 2 | 4     | 2           | 7           | 4   |
| 3 | 8     | 3           | 23          | 9   |
| 4 | 16    | 5           | 79          | 19  |
| 5 | 32    | 7           | 223         | 37  |
| 6 | 64    | 11          | 703         | 73  |
| 7 | 128   | 17          | 2175        | 143 |

This is the **unconditional, elementary** half of Waring's problem
(the matching upper bound `g(k) ≤ 2^k + ⌊(3/2)^k⌋ − 2`, valid when
`{(3/2)^k} ≤ 1 − (3/4)^k` — Mahler 1957, all but finitely many `k`, and
verified to `k ≈ 4.7·10^8` by Kubina–Wunderlich 1990 — is research-level
and remains a Mathlib gap / open axiomatic target).

## Why one theorem instead of six copies

The five existing instances are byte-for-byte specialisations of the same
counting+omega template. The mathematical reason they all succeed is a
single uniform fact: **for the witness `n_k`, the only `k`-th powers `≤ n_k`
are `0`, `1`, and `2^k`.** Indeed `Q·2^k ≤ 3^k` (definition of truncated
division), so `n_k = Q·2^k − 1 < 3^k`, forcing every summand base `< 3`.
The representation problem then collapses to the linear system

* `c₀ + c₁ + c₂ = 2^k + Q − 3`  (number of summands)
* `c₁ + 2^k · c₂ = Q·2^k − 1`    (value)

whose infeasibility over `ℕ` is the one-line algebra
`c₁ + c₂ = (2^k − 1)(Q − c₂) + Q − 1 ≥ 2^k + Q − 2 > 2^k + Q − 3`, so
`c₀ < 0` — impossible. Because the coefficients `2^k`, `Q` are now
symbolic, the final discharge moves from `omega` (fixed coefficients) to a
short `ℤ`-cast argument whose only nonlinear ingredient is the product
witness `(2^k−1)(Q−1−c₂) ≥ 0`; that witness is supplied as a deterministic
`linear_combination` certificate rather than left to a heuristic search, so
the closing step is plain `linarith`.

## ⚠️ BUILD STATUS — NOT build-verified (dual-backend blackout)

Written 2026-06-14 (researcher-10) while **both** verification backends were
unavailable: the host Docker daemon was unresponsive (`docker info` hung) so
`docker-build.sh` could not run, and the Aristotle MCP returned
`Resource not found`. The proof mirrors the proven idioms of the sibling
`…CountingG4.lean` (built clean at 7743 jobs) for Steps 1–5. The final `ℤ`
Step-6 discharge — the one piece of new logic and the sole residual build-risk
flagged by the S27 lemma audit — was hardened from a heuristic `nlinarith`
search into a **deterministic certificate**: a single `linear_combination`
establishes the polynomial identity `(M−1)(Q−1−c₂) = c₁+c₂−M−Q+2`
(coefficient certificate `−hZeqn − hcomm`, machine-checked by `ring`), after
which the contradiction closes by plain `linarith`. No nonlinear search
remains.

**For safety this file is deliberately NOT registered in `proofs/Proofs.lean`,**
so it cannot break the whole-library build. A follow-up session with Docker
(or Aristotle) up should:
1. `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01General`
2. fix any v4.26.0 lemma-name drift (candidates flagged inline),
3. then add the `import` line to `proofs/Proofs.lean` and retire the six
   redundant fixed-`k` files (or keep them as worked examples).

## Bearer lemmas (Mathlib v4.26.0, lake-pinned SHA `2df2f01…`)

Same set as `…CountingG4.lean` plus, for the symbolic final step:
`Nat.pow_le_pow_left`, `Nat.pow_le_pow_right`, `Nat.div_mul_le_self`,
`Nat.div_pos`, `Nat.mul_pos`, `Finset.single_le_sum`,
`Finset.sum_fiberwise`, `Finset.card_eq_sum_card_fiberwise`,
`Fin.sum_univ_three`, `Finset.sum_const`, `zero_pow`, `one_pow`,
`mul_le_mul_of_nonneg_left`, `mul_nonneg`, `linear_combination`, and `linarith`.
-/

namespace WaringG2OQ01.General

open Finset

/-- `IsSumOfKthPowers s k n`: there exist `s` natural numbers (possibly zero)
whose `k`-th powers sum to `n`. Parametric generalisation of the per-`k`
`IsSumOfCubes` / `IsSumOfFourthPowers` / … definitions. -/
def IsSumOfKthPowers (s k n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ k) = n

/-- **General Waring lower bound.** For every `k ≥ 1`, the integer
`n_k = (3^k / 2^k) · 2^k − 1` is not a sum of `2^k + 3^k / 2^k − 3` perfect
`k`-th powers; hence `g(k) ≥ 2^k + ⌊(3/2)^k⌋ − 2`.

Specialises to the classical witnesses `7, 23, 79, 223, 703, 2175` for
`k = 2, …, 7`. -/
theorem waring_lower_general (k : ℕ) (hk : 1 ≤ k) :
    ¬ IsSumOfKthPowers (2 ^ k + 3 ^ k / 2 ^ k - 3) k (3 ^ k / 2 ^ k * 2 ^ k - 1) := by
  -- Abbreviations `M = 2^k`, `Q = ⌊(3/2)^k⌋ = 3^k / 2^k`.
  set M : ℕ := 2 ^ k with hM
  set Q : ℕ := 3 ^ k / 2 ^ k with hQ
  have hk0 : k ≠ 0 := by omega
  -- `M ≥ 2` (since `k ≥ 1`), hence `M ≥ 1`.
  have hM2 : 2 ≤ M := by
    rw [hM]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hM1 : 1 ≤ M := le_trans (by norm_num) hM2
  -- `2^k ≤ 3^k`, hence `Q ≥ 1` and `Q·M ≤ 3^k`.
  have hge : (2 : ℕ) ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have hQ1 : 1 ≤ Q := by
    rw [hQ]; exact Nat.div_pos hge (by positivity)
  have hQM_le : Q * M ≤ 3 ^ k := by
    rw [hQ, hM]; exact Nat.div_mul_le_self _ _
  have hQM1 : 1 ≤ Q * M := Nat.mul_pos hQ1 hM1
  rintro ⟨f, hf⟩
  -- Step 1: each summand base is `< 3` (else `3^k ≤ (f i)^k ≤ n < 3^k`).
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge3
    push_neg at hge3
    have h3k : (3 : ℕ) ^ k ≤ (f i) ^ k := Nat.pow_le_pow_left hge3 k
    have hsing : (f i) ^ k ≤ ∑ j, (f j) ^ k :=
      Finset.single_le_sum (f := fun j => (f j) ^ k)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hf] at hsing
    -- `3^k ≤ (f i)^k ≤ Q·M − 1 < Q·M ≤ 3^k`; `omega` abstracts the powers.
    omega
  -- Step 2: lift `Fin (M+Q-3) → ℕ` to `Fin (M+Q-3) → Fin 3`.
  let g : Fin (M + Q - 3) → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  have hf_g : (∑ i, ((g i : ℕ)) ^ k) = Q * M - 1 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- Step 3: fiberwise counts `c j = #{i | g i = j}`.
  set c : Fin 3 → ℕ := fun j => #{i : Fin (M + Q - 3) | g i = j} with hc
  have fib :
      ∑ i, ((g i : ℕ)) ^ k = ∑ j : Fin 3, ((j : ℕ)) ^ k * c j := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin (M + Q - 3))) g
          (fun i => ((g i : ℕ)) ^ k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = j),
          ((g i : ℕ)) ^ k = ((j : ℕ)) ^ k := by
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul, mul_comm]
  -- Step 4: partition `c 0 + c 1 + c 2 = M + Q − 3`.
  have card_part : c 0 + c 1 + c 2 = M + Q - 3 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin (M + Q - 3))))
      (t := (Finset.univ : Finset (Fin 3))) (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    simpa [c] using h.symm
  -- Step 5: value `∑ j, (j)^k · c j = c 1 + M · c 2` (since `0^k=0, 1^k=1, 2^k=M`).
  have value_sum :
      (∑ j : Fin 3, ((j : ℕ)) ^ k * c j) = c 1 + M * c 2 := by
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, one_pow, one_mul]
    rw [zero_pow hk0, hM]
    ring
  have eqn : c 1 + M * c 2 = Q * M - 1 := by
    rw [← value_sum, ← fib]; exact hf_g
  -- Additive form to avoid truncated `ℕ` subtraction when casting.
  have eqnN : c 1 + M * c 2 + 1 = Q * M := by
    rw [eqn, Nat.sub_add_cancel hQM1]
  -- Step 6: final contradiction over `ℤ`.
  have hZpart : (c 0 : ℤ) + c 1 + c 2 + 3 = (M : ℤ) + Q := by
    have hN : c 0 + c 1 + c 2 + 3 = M + Q := by omega
    exact_mod_cast hN
  have hZeqn : (c 1 : ℤ) + (M : ℤ) * c 2 + 1 = (Q : ℤ) * M := by
    exact_mod_cast eqnN
  have hZM2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM2
  have hZQ1 : (1 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ1
  have hc0 : (0 : ℤ) ≤ (c 0 : ℤ) := by positivity
  have hc1 : (0 : ℤ) ≤ (c 1 : ℤ) := by positivity
  have hcomm : (Q : ℤ) * M = (M : ℤ) * Q := mul_comm _ _
  -- `c 2 ≤ Q − 1` (else `M·Q ≤ M·c₂` forces `c₁ + 1 ≤ 0`).
  have hdQ : (c 2 : ℤ) ≤ (Q : ℤ) - 1 := by
    by_contra hcon
    push_neg at hcon
    have hQc : (Q : ℤ) ≤ (c 2 : ℤ) := by linarith
    have hmul : (M : ℤ) * Q ≤ (M : ℤ) * c 2 :=
      mul_le_mul_of_nonneg_left hQc (by linarith)
    linarith [hZeqn, hc1, hcomm, hmul]
  -- `c₁ + c₂ ≥ M + Q − 2`, contradicting `c₀ + c₁ + c₂ = M + Q − 3` with `c₀ ≥ 0`.
  -- Deterministic certificate (replaces the prior `nlinarith` search): the key
  -- product expands EXACTLY to the linear quantity `c₁ + c₂ − M − Q + 2` once the
  -- value equation `hZeqn` and the commutation `hcomm` are substituted. Verified
  -- `(M−1)(Q−1−c₂) − (c₁+c₂−M−Q+2) = −hZeqn − hcomm` as a polynomial identity.
  have hexpand : ((M : ℤ) - 1) * ((Q : ℤ) - 1 - c 2) = (c 1 : ℤ) + c 2 - M - Q + 2 := by
    linear_combination -hZeqn - hcomm
  have hprod : (0 : ℤ) ≤ ((M : ℤ) - 1) * ((Q : ℤ) - 1 - c 2) :=
    mul_nonneg (by linarith) (by linarith)
  -- `0 ≤ c₁ + c₂ − M − Q + 2` (from `hexpand`+`hprod`), then `c₀ ≤ −1` via `hZpart`,
  -- contradicting `hc0 : 0 ≤ c₀`. All three steps are purely linear.
  linarith [hexpand, hprod, hZpart, hc0]

end WaringG2OQ01.General
