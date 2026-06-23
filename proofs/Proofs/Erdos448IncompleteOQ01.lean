/-
  Erdős Problem #448 — Incomplete OQ-01: Proving τ⁺(n) ≤ τ(n) from definitions

  The parent proof (Erdos448Problem.lean) axiomatized:
    axiom tauPlus_le_tau (n : ℕ) (hn : n ≥ 1) : τ⁺(n) ≤ τ(n)

  This file proves it rigorously.

  OQ-01: Can the bound τ⁺(n) ≤ τ(n) be derived from the definitions of τ and τ⁺?

  Answer: YES.

  Proof idea: The "occupied dyadic intervals" are exactly the image of divisors
  under the map d ↦ Nat.log 2 d. Since image size ≤ source size, τ⁺(n) ≤ τ(n).

  Key lemma: if 2^k ≤ d < 2^(k+1) (i.e., d is in dyadic interval k), then
  Nat.log 2 d = k. This makes the map d ↦ Nat.log 2 d surjective onto occupied
  intervals, giving τ⁺(n) = |occupied intervals| ≤ |n.divisors| = τ(n).
-/

import Mathlib
import Proofs.Erdos448Problem

namespace Erdos448IncompleteOQ01

open Nat Finset BigOperators Erdos448

/-══════════════════════════════════════════════════════════════════
  Part I: Log characterizes dyadic interval membership
══════════════════════════════════════════════════════════════════-/

/-- If d ≥ 1 is in dyadic interval k (i.e., 2^k ≤ d < 2^(k+1)),
    then Nat.log 2 d = k.

    Proof:
    - Upper bound: if log₂ d ≥ k+1, then 2^(k+1) ≤ 2^(log₂ d) ≤ d,
      contradicting d < 2^(k+1).
    - Lower bound: if log₂ d < k, then d < 2^(log₂ d + 1) ≤ 2^k ≤ d,
      contradicting 2^k ≤ d. -/
private lemma log_eq_of_inDyadicInterval {d k : ℕ} (hd_pos : 0 < d)
    (h : inDyadicInterval d k) : Nat.log 2 d = k := by
  have h1 : 2 ^ k ≤ d := h.1
  have h2 : d < 2 ^ (k + 1) := h.2
  -- Upper bound: Nat.log 2 d ≤ k
  have hlog_upper : Nat.log 2 d ≤ k := by
    by_contra hlt
    push_neg at hlt
    -- hlt : k + 1 ≤ Nat.log 2 d
    have h_pow : 2 ^ (k + 1) ≤ 2 ^ (Nat.log 2 d) :=
      Nat.pow_le_pow_right (by omega) hlt
    have h_log : 2 ^ Nat.log 2 d ≤ d := Nat.pow_log_le_self 2 hd_pos.ne'
    linarith
  -- Lower bound: k ≤ Nat.log 2 d
  have hlog_lower : k ≤ Nat.log 2 d := by
    by_contra hlt
    push_neg at hlt
    -- hlt : Nat.log 2 d + 1 ≤ k
    have h_succ : d < 2 ^ (Nat.log 2 d + 1) :=
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) d
    have h_pow : 2 ^ (Nat.log 2 d + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) hlt
    linarith
  omega

/-══════════════════════════════════════════════════════════════════
  Part II: Occupied intervals ⊆ image of divisors
══════════════════════════════════════════════════════════════════-/

/-- The set of occupied dyadic intervals is a subset of the image
    of n.divisors under Nat.log 2.

    Proof: for each occupied interval k, there exists d ∈ n.divisors
    with Nat.log 2 d = k (since d is in the k-th dyadic interval). -/
private lemma occupied_subset_image_log {n : ℕ} (hn : 0 < n) :
    (Finset.range (Nat.log 2 n + 1)).filter
      (fun k => ∃ d ∈ n.divisors, inDyadicInterval d k) ⊆
    Finset.image (fun d => Nat.log 2 d) n.divisors := by
  intro k hk
  simp only [Finset.mem_filter] at hk
  obtain ⟨_, d, hd_mem, hd_interval⟩ := hk
  simp only [Finset.mem_image]
  have hdn : d ∣ n := (Nat.mem_divisors.mp hd_mem).1
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  exact ⟨d, hd_mem, log_eq_of_inDyadicInterval hd_pos hd_interval⟩

/-══════════════════════════════════════════════════════════════════
  Part III: Main theorem τ⁺(n) ≤ τ(n)
══════════════════════════════════════════════════════════════════-/

/-- **τ⁺(n) ≤ τ(n)**: the number of occupied dyadic intervals is at most
    the total number of divisors.

    Proof:
    1. occupied_intervals ⊆ image (Nat.log 2) n.divisors
       (by log_eq_of_inDyadicInterval)
    2. |image f S| ≤ |S| for any f, S  (Finset.card_image_le)
    3. Therefore τ⁺(n) = |occupied_intervals| ≤ |n.divisors| = τ(n)

    This proves the axiom `tauPlus_le_tau` from Erdos448Problem.lean. -/
theorem tauPlus_le_tau_proved (n : ℕ) (hn : 0 < n) : τ⁺(n) ≤ τ(n) := by
  simp only [tauPlus, tau, hn.ne', ite_false]
  calc ((Finset.range (Nat.log 2 n + 1)).filter
        (fun k => ∃ d ∈ n.divisors, inDyadicInterval d k)).card
      ≤ (Finset.image (fun d => Nat.log 2 d) n.divisors).card :=
          Finset.card_le_card (occupied_subset_image_log hn)
    _ ≤ n.divisors.card := Finset.card_image_le

/-- Compatibility with the parent axiom's statement (n ≥ 1 form). -/
theorem tauPlus_le_tau_compat (n : ℕ) (hn : n ≥ 1) : τ⁺(n) ≤ τ(n) :=
  tauPlus_le_tau_proved n (by omega)

/-══════════════════════════════════════════════════════════════════
  Part IV: Additional consequences
══════════════════════════════════════════════════════════════════-/

/-- Strict inequality example: n = 6 has τ(6) = 4 divisors but τ⁺(6) = 3
    occupied intervals, since [2,4) contains both 2 and 3. -/
theorem tau_six_eq_four : τ(6) = 4 := by native_decide
theorem tauPlus_six_eq_three : τ⁺(6) = 3 := by decide
theorem strict_example : τ⁺(6) < τ(6) := by decide

end Erdos448IncompleteOQ01
