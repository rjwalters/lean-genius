/-
  Happy / unhappy dichotomy for the sum-of-squares-of-digits map.

  Let `S n` be the sum of the squares of the decimal digits of `n`.  A positive
  integer is *happy* if iterating `S` eventually reaches `1`, and *unhappy*
  otherwise.  The classical theorem is that there is no third possibility: every
  positive integer's orbit under `S` is eventually absorbed into

      T = {1} ∪ {4, 16, 37, 58, 89, 145, 42, 20},

  i.e. it reaches the fixed point `1` (happy) or lands on the 8-cycle

      4 → 16 → 37 → 58 → 89 → 145 → 42 → 20 → 4

  (unhappy).  Equivalently every `n ≥ 1` satisfies `∃ k, S^[k] n = 1` or
  `∃ k, S^[k] n = 4`.

  PROOF STRATEGY (genuinely covers all infinitely many `n`):
    * `descent`: for every `n ≥ 1000`, `S n < n`.  This is a real bound, not an
      enumeration: if `L = (digits 10 n).length` then `S n ≤ 81 · L` (each digit
      is `≤ 9`) while `10^(L-1) ≤ n` and `81 · L < 10^(L-1)` for `L ≥ 4`.
    * Strong induction then reduces every `n` to the finite window `[1, 999]`.
    * `base_reaches`: a finite check (`native_decide`) that every `n ∈ [1, 999]`
      reaches `T` within 15 iterations (the true maximum is 11, at `n = 269`).

  All numeric claims were cross-checked independently in Python
  (`research/problems/happy-number-oq-01/verify_happy.py`).

  STATUS: build-pending.  This file is NOT registered in `Proofs.lean` and has
  not been compiled this session (Docker build pool saturated / daemon
  unresponsive).  The finite checks use `native_decide`, which introduces the
  `Lean.ofReduceBool` axiom; the gallery status for this entry is therefore
  `axiomatized`, NOT `verified`.
-/
import Mathlib

namespace HappyNumberOQ01

/-- Sum of the squares of the decimal digits of `n`. -/
def S (n : ℕ) : ℕ := ((Nat.digits 10 n).map (· ^ 2)).sum

/-- The absorbing set: the happy fixed point `1` together with the eight numbers
of the unhappy cycle `4 → 16 → 37 → 58 → 89 → 145 → 42 → 20 → 4`. -/
def T : Finset ℕ := {1, 4, 16, 37, 58, 89, 145, 42, 20}

/-- `1` is a fixed point of `S`. -/
theorem S_one : S 1 = 1 := by native_decide

/-- The unhappy cycle, made explicit. -/
theorem unhappy_cycle :
    S 4 = 16 ∧ S 16 = 37 ∧ S 37 = 58 ∧ S 58 = 89 ∧ S 89 = 145 ∧
      S 145 = 42 ∧ S 42 = 20 ∧ S 20 = 4 := by native_decide

/-- `T` is closed under `S`: once an orbit reaches `T` it stays there. -/
theorem T_absorbing : ∀ m ∈ T, S m ∈ T := by native_decide

/-- Exponential beats linear: `81 · L < 10^(L-1)` for every `L ≥ 4`. -/
theorem aux_exp : ∀ L, 4 ≤ L → 81 * L < 10 ^ (L - 1) := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have e : (10 : ℕ) ^ L = 10 ^ (L - 1) * 10 := by
      conv_lhs => rw [show L = (L - 1) + 1 by omega]
      rw [pow_succ]
    have hbig : (1000 : ℕ) ≤ 10 ^ (L - 1) := by
      calc (1000 : ℕ) = 10 ^ 3 := by norm_num
        _ ≤ 10 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show L + 1 - 1 = L by omega, e]
    nlinarith [ih, hbig]

/-- **Descent.** For every `n ≥ 1000`, applying `S` strictly decreases `n`. -/
theorem descent (n : ℕ) (hn : 1000 ≤ n) : S n < n := by
  have hn0 : n ≠ 0 := by omega
  -- `n` has at least 4 digits.
  have hL4 : 4 ≤ (Nat.digits 10 n).length := by
    have hupper : n < 10 ^ (Nat.digits 10 n).length :=
      Nat.lt_base_pow_length_digits (by norm_num)
    have h3 : (10 : ℕ) ^ 3 ≤ n := by
      have h1000 : (10 : ℕ) ^ 3 = 1000 := by norm_num
      omega
    have hlt : (10 : ℕ) ^ 3 < 10 ^ (Nat.digits 10 n).length := lt_of_le_of_lt h3 hupper
    have h3L : 3 < (Nat.digits 10 n).length := (pow_lt_pow_iff_right' (by norm_num)).mp hlt
    omega
  -- Lower bound on `n` from its digit count.
  have hlow : 10 ^ ((Nat.digits 10 n).length - 1) ≤ n := by
    have hbpl : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
      Nat.base_pow_length_digits_le 10 n (by norm_num) hn0
    have e : (10 : ℕ) ^ (Nat.digits 10 n).length
        = 10 ^ ((Nat.digits 10 n).length - 1) * 10 := by
      conv_lhs => rw [show (Nat.digits 10 n).length = ((Nat.digits 10 n).length - 1) + 1 by omega]
      rw [pow_succ]
    rw [e] at hbpl
    have hbpl' : 10 * 10 ^ ((Nat.digits 10 n).length - 1) ≤ 10 * n := by
      rw [mul_comm]; exact hbpl
    exact Nat.le_of_mul_le_mul_left hbpl' (by norm_num)
  -- Upper bound on `S n`: at most `81` per digit.
  have hSle : S n ≤ 81 * (Nat.digits 10 n).length := by
    have hb : ∀ x ∈ (Nat.digits 10 n).map (· ^ 2), x ≤ 81 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      have hd9 : d ≤ 9 := by have := Nat.digits_lt_base (by norm_num) hd; omega
      calc d ^ 2 ≤ 9 ^ 2 := Nat.pow_le_pow_left hd9 2
        _ = 81 := by norm_num
    have h := List.sum_le_card_nsmul ((Nat.digits 10 n).map (· ^ 2)) 81 hb
    simp only [List.length_map, nsmul_eq_mul, Nat.cast_id] at h
    show ((Nat.digits 10 n).map (· ^ 2)).sum ≤ 81 * (Nat.digits 10 n).length
    omega
  have hexp : 81 * (Nat.digits 10 n).length < 10 ^ ((Nat.digits 10 n).length - 1) :=
    aux_exp _ hL4
  calc S n ≤ 81 * (Nat.digits 10 n).length := hSle
    _ < 10 ^ ((Nat.digits 10 n).length - 1) := hexp
    _ ≤ n := hlow

/-- For positive `n`, `S n` is positive (the leading digit contributes a positive
square), so the orbit never falls to `0`. -/
theorem S_pos {n : ℕ} (hn : n ≠ 0) : 0 < S n := by
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits 10 n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 hn
  have hmem : (Nat.digits 10 n).getLast hne ∈ Nat.digits 10 n := List.getLast_mem hne
  have hsqmem : ((Nat.digits 10 n).getLast hne) ^ 2 ∈ (Nat.digits 10 n).map (· ^ 2) :=
    List.mem_map.mpr ⟨_, hmem, rfl⟩
  have hle : ((Nat.digits 10 n).getLast hne) ^ 2 ≤ S n := List.le_sum_of_mem hsqmem
  have hpos : 0 < ((Nat.digits 10 n).getLast hne) ^ 2 :=
    pow_pos (Nat.pos_of_ne_zero hlast) 2
  omega

/-- Bounded reachability checker: does the orbit of `n` hit `T` within 15 steps? -/
def reachesT (n : ℕ) : Bool := (List.range 15).any (fun k => decide (S^[k] n ∈ T))

/-- Finite verification: every `n ∈ [1, 999]` reaches `T` within 15 iterations. -/
theorem reachesT_below : ∀ n, n < 1000 → 1 ≤ n → reachesT n = true := by native_decide

/-- Base case of the induction: every `n ∈ [1, 999]` reaches `T`. -/
theorem base_reaches (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 1000) : ∃ k, S^[k] n ∈ T := by
  have h := reachesT_below n hn hn1
  simp only [reachesT, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨k, _, hk⟩ := h
  exact ⟨k, hk⟩

/-- **Main theorem.** For every positive integer `n`, iterating `S` eventually
lands in the absorbing set `T`. -/
theorem reaches_T : ∀ n, 1 ≤ n → ∃ k, S^[k] n ∈ T := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hbig : 1000 ≤ n
    · have hdesc : S n < n := descent n hbig
      have hpos : 1 ≤ S n := S_pos (by omega)
      obtain ⟨k, hk⟩ := ih (S n) hdesc hpos
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
    · push_neg at hbig
      exact base_reaches n hn hbig

/-- **Happy / unhappy dichotomy.** Every positive integer is happy (its orbit
reaches the fixed point `1`) or unhappy (its orbit reaches `4`, hence enters the
8-cycle). -/
theorem reaches_one_or_four (n : ℕ) (hn : 1 ≤ n) :
    (∃ k, S^[k] n = 1) ∨ (∃ k, S^[k] n = 4) := by
  obtain ⟨k, hk⟩ := reaches_T n hn
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with h | h | h | h | h | h | h | h | h
  · exact Or.inl ⟨k, h⟩
  · exact Or.inr ⟨k, h⟩
  · exact Or.inr ⟨7 + k, by rw [Function.iterate_add_apply, h]; native_decide⟩
  · exact Or.inr ⟨6 + k, by rw [Function.iterate_add_apply, h]; native_decide⟩
  · exact Or.inr ⟨5 + k, by rw [Function.iterate_add_apply, h]; native_decide⟩
  · exact Or.inr ⟨4 + k, by rw [Function.iterate_add_apply, h]; native_decide⟩
  · exact Or.inr ⟨3 + k, by rw [Function.iterate_add_apply, h]; native_decide⟩
  · exact Or.inr ⟨2 + k, by rw [Function.iterate_add_apply, h]; native_decide⟩
  · exact Or.inr ⟨1 + k, by rw [Function.iterate_add_apply, h]; native_decide⟩

end HappyNumberOQ01
