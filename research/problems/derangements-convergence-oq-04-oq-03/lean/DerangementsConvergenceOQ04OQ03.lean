/-
  Sharp combined congruence for derangement numbers, and the structural
  "CRT engine" behind divisibility results for r-derangement families.

  Problem: derangements-convergence-oq-04-oq-03
  Parent : derangements-convergence-oq-04

  ## Status: UNVERIFIED DRAFT

  The Docker Lean build harness is unavailable this session (corrupted
  containerd image blob → the build image cannot be inspected or rebuilt),
  and the Aristotle MCP endpoint returns 404. This file therefore has NOT
  been machine-checked. It lives under `research/problems/.../lean/`, which
  is NOT globbed by `proofs/lakefile.toml`, so it cannot break the gallery
  build. Promote it into `proofs/Proofs/` only after a clean Docker build.

  ## What the parent proved (derangements-convergence-oq-04)

  For D(n) = numDerangements n, the parent established TWO separate facts:
    * (n − 1) ∣ D(n)                    [from the additive recurrence
                                         D(n) = (n−1)·(D(n−2)+D(n−1))]
    * n ∣ (D(n) − (−1)^n), i.e.
      D(n) ≡ (−1)^n (mod n)             [from the multiplicative recurrence
                                         D(n+1) = (n+1)·D(n) − (−1)^n]

  ## What this file adds (the child problem)

  The child asks whether "an analogous divisibility or sign-congruence
  survives" for generalised r-derangement families. The honest answer,
  developed here, has two parts.

  1. **A structural theorem (`crt_combine`).** The two parent facts are not
     independent: because gcd(n, n−1) = 1, the Chinese Remainder Theorem
     fuses them into a single sharp congruence *modulo n(n−1)*. We isolate
     the mechanism as an abstract lemma about ANY integer `a`:

        if (n−1) ∣ a  and  n ∣ (a − u),  then  n(n−1) ∣ (a + u·(n−1)).

     This is exactly the "recurrence-driven identity" the problem asks for,
     stripped of the combinatorial object: any counting sequence `a = D_r(n)`
     that inherits BOTH a `(n−1)`-factor additive recurrence AND a
     `±1`-corrected multiplicative recurrence automatically satisfies the
     fused congruence. So the phenomenon is not special to ordinary
     derangements — it is a property of the recurrence *shape*.

  2. **The sharp combined congruence for D(n) (`numDerangements_combined_*`).**
     Instantiating the engine at `a = D(n)`, `u = (−1)^n` yields

        D(n) ≡ (−1)^(n+1)·(n − 1)   (mod n(n−1)).

     This is strictly stronger than either parent fact and pins D(n) down
     modulo n(n−1) exactly (verified numerically for 2 ≤ n ≤ 9:
       n=4: D=9 ≡ 9,  n=5: D=44 ≡ 4,  n=6: D=265 ≡ 25,  n=7: D=1854 ≡ 6,
       n=8: D=14833 ≡ 49,  n=9: D=133496 ≡ 8, all mod n(n−1)).

  ## On the literal "r-derangement numbers"

  Mathlib has no native definition of r-derangements (permutations avoiding
  a prescribed cycle structure), so a fully combinatorial treatment would
  require building that object and its recurrence from scratch (an EGF /
  species argument, > 500 lines, not attempted under the build blackout).
  The value of `crt_combine` is precisely that it makes the combinatorial
  definition irrelevant to the *arithmetic* conclusion: the moment one has
  the two recurrences for a family D_r, the fused congruence follows for free.

  All results below are elementary (integer arithmetic + the two standard
  Mathlib recurrences `numDerangements_add_two` and `numDerangements_succ`).
-/

import Mathlib

open Nat

namespace DerangementsConvergenceOQ04OQ03

/-! ### The structural CRT engine -/

/-- **Structural theorem.** Because `n` and `n − 1` are coprime, the two
    divisibility facts `(n−1) ∣ a` and `n ∣ (a − u)` fuse, via the Chinese
    Remainder Theorem, into a single congruence modulo `n(n−1)`:

      `n(n−1) ∣ (a + u·(n−1))`,  i.e.  `a ≡ −u·(n−1)  (mod n(n−1))`.

    The proof is a direct elimination and needs no coprimality hypothesis:
    write `a = (n−1)·k`; the second hypothesis forces `n ∣ (k + u)`, and
    multiplying back by `(n−1)` gives the claim. It holds for every `n`
    (including the degenerate `n = 0, 1`). -/
theorem crt_combine (n : ℕ) (a u : ℤ)
    (h1 : ((n : ℤ) - 1) ∣ a) (h2 : (n : ℤ) ∣ (a - u)) :
    ((n : ℤ) * ((n : ℤ) - 1)) ∣ (a + u * ((n : ℤ) - 1)) := by
  obtain ⟨k, hk⟩ := h1
  -- From `n ∣ (a − u)` and `a = (n−1)·k ≡ −k (mod n)` we get `n ∣ (k + u)`.
  have hn : (n : ℤ) ∣ (k + u) := by
    have e : (k + u) = (n : ℤ) * k - (a - u) := by rw [hk]; ring
    rw [e]
    exact dvd_sub' (dvd_mul_right (n : ℤ) k) h2
  obtain ⟨t, ht⟩ := hn
  refine ⟨t, ?_⟩
  have e2 : a + u * ((n : ℤ) - 1) = ((n : ℤ) - 1) * (k + u) := by rw [hk]; ring
  rw [e2, ht]; ring

/-! ### The two parent recurrence facts, self-contained -/

/-- `(n − 1) ∣ D(n)` over `ℤ`, read off the additive recurrence
    `D(m+2) = (m+1)·(D(m) + D(m+1))`. Stated over `ℤ` so it feeds
    `crt_combine` directly and covers the degenerate cases `n = 0, 1`. -/
theorem sub_one_dvd (n : ℕ) : ((n : ℤ) - 1) ∣ (numDerangements n : ℤ) := by
  match n with
  | 0 =>
      rw [show numDerangements 0 = 1 from by decide]
      exact ⟨-1, by norm_num⟩
  | 1 =>
      rw [show numDerangements 1 = 0 from by decide]
      simp
  | (m + 2) =>
      have h : ((numDerangements (m + 2) : ℤ))
          = ((m : ℤ) + 1) * ((numDerangements m : ℤ) + (numDerangements (m + 1) : ℤ)) := by
        exact_mod_cast numDerangements_add_two m
      refine ⟨(numDerangements m : ℤ) + (numDerangements (m + 1) : ℤ), ?_⟩
      rw [h]; push_cast; ring

/-- `n ∣ (D(n) − (−1)^n)`, i.e. `D(n) ≡ (−1)^n (mod n)`, read off the
    multiplicative recurrence `D(n+1) = (n+1)·D(n) − (−1)^n`. -/
theorem dvd_numDerangements_sub_sign (n : ℕ) :
    (n : ℤ) ∣ ((numDerangements n : ℤ) - (-1) ^ n) := by
  cases n with
  | zero => simp
  | succ k =>
    refine ⟨numDerangements k, ?_⟩
    rw [numDerangements_succ k, pow_succ]
    push_cast
    ring

/-! ### The sharp combined congruence for D(n) -/

/-- **Main result (divisibility form).** For every `n`,
      `n(n−1) ∣ (D(n) + (−1)^n·(n−1))`.
    Obtained by feeding the two recurrence facts into `crt_combine`. -/
theorem numDerangements_combined_dvd (n : ℕ) :
    ((n : ℤ) * ((n : ℤ) - 1)) ∣ ((numDerangements n : ℤ) + (-1) ^ n * ((n : ℤ) - 1)) :=
  crt_combine n (numDerangements n : ℤ) ((-1) ^ n) (sub_one_dvd n)
    (dvd_numDerangements_sub_sign n)

/-- **Main result (congruence form).** For every `n`,
      `D(n) ≡ (−1)^(n+1)·(n − 1)   (mod n(n−1))`.
    Equivalent restatement of `numDerangements_combined_dvd`, since
    `(−1)^(n+1)·(n−1) = −(−1)^n·(n−1)`. This is strictly stronger than
    each of the parent facts `(n−1) ∣ D(n)` and `D(n) ≡ (−1)^n (mod n)`,
    and determines `D(n)` modulo `n(n−1)` exactly. -/
theorem numDerangements_combined_congr (n : ℕ) :
    ((n : ℤ) * ((n : ℤ) - 1)) ∣ ((numDerangements n : ℤ) - (-1) ^ (n + 1) * ((n : ℤ) - 1)) := by
  have h := numDerangements_combined_dvd n
  have e : (numDerangements n : ℤ) - (-1) ^ (n + 1) * ((n : ℤ) - 1)
      = (numDerangements n : ℤ) + (-1) ^ n * ((n : ℤ) - 1) := by
    rw [pow_succ]; ring
  rw [e]; exact h

/-! ### Sanity checks (values match the classical derangement sequence) -/

example : numDerangements 4 = 9 := by decide
example : numDerangements 5 = 44 := by decide
example : numDerangements 6 = 265 := by decide

end DerangementsConvergenceOQ04OQ03
