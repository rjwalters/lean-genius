/-
Erdős Problem #493 — OQ-01, result (C2): the ORDERED representation count.

  #{ (a, b) : a, b ≥ 2,  a*b - (a+b) = n }  =  τ(n + 1)

(the number of positive divisors of n + 1). This is the counting refinement of the
exact-image / factorization-bijection results in `Proofs.Erdos493OQ01`; it makes
the bijection `(a, b) ↔ (u, v)` with `u = a-1, v = b-1, u*v = n+1` an explicit
cardinality identity via the divisor map `u ↦ (u+1, (n+1)/u + 1)`.

Self-contained over ℕ (multiplicative form `a*b = a+b+n` avoids ℕ subtraction;
no dependency on the parent file). Numerically cross-checked in
`research/problems/erdos-493-oq-01/verify_prodminussum.py` (C2 = τ(n+1), ALL PASS).

BUILD-PENDING / UNREGISTERED: deliberately NOT added to `Proofs.lean`. The whole
`card_bij` proof below could not be machine-verified this session — Docker
(containerd blob store I/O-corrupt + host data volume 100% full) and Aristotle
(404) were both down. Per repo policy this is held out of the auto-merged build
until a Lean build is available; register + `docker-build.sh Proofs.Erdos493OQ01C2`
then, fix any lemma-name nits, and fold into `Erdos493OQ01.lean`.

Reference: https://erdosproblems.com/493
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors

namespace Erdos493OQ01C2

/-- Finset of ordered `a, b ≥ 2` representations of `n` (multiplicative form
`a*b = a+b+n`, avoiding `ℕ` subtraction). The bounds `a, b ≤ n + 2` are forced by
`a*b = a+b+n` together with `a, b ≥ 2`. -/
def repsFinset (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 (n + 2)) ×ˢ (Finset.Icc 2 (n + 2))).filter
    (fun p => p.1 * p.2 = p.1 + p.2 + n)

@[simp] theorem mem_repsFinset {n a b : ℕ} :
    (a, b) ∈ repsFinset n ↔
      (2 ≤ a ∧ a ≤ n + 2) ∧ (2 ≤ b ∧ b ≤ n + 2) ∧ a * b = a + b + n := by
  simp [repsFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- **(C2) Ordered representation count `= τ(n+1)`.** The number of ordered pairs
`(a, b)` with `a, b ≥ 2` and `a*b - (a+b) = n` equals the number of positive
divisors of `n + 1`. The bijection sends a divisor `u ∣ n+1` to the representation
`(u + 1, (n+1)/u + 1)`, inverting the central identity `a*b-(a+b) = (a-1)(b-1) - 1`
with `u = a - 1`. -/
theorem reps_card_eq_tau (n : ℕ) :
    (repsFinset n).card = (n + 1).divisors.card := by
  symm
  apply Finset.card_bij (fun u _ => (u + 1, (n + 1) / u + 1))
  · intro u hu
    have hu_pos : 0 < u := Nat.pos_of_mem_divisors hu
    have hdvd : u ∣ (n + 1) := (Nat.mem_divisors.mp hu).1
    have hule : u ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
    have huw : u * ((n + 1) / u) = n + 1 := Nat.mul_div_cancel' hdvd
    have hw1 : 1 ≤ (n + 1) / u := (Nat.one_le_div_iff hu_pos).mpr hule
    have hwle : (n + 1) / u ≤ n + 1 := Nat.div_le_self _ _
    simp only [mem_repsFinset]
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
    have key : (u + 1) * ((n + 1) / u + 1)
             = u * ((n + 1) / u) + (u + (n + 1) / u + 1) := by ring
    rw [key, huw]; ring
  · intro u₁ _ u₂ _ h
    simp only [Prod.mk.injEq] at h; omega
  · rintro ⟨a, b⟩ hp
    simp only [mem_repsFinset] at hp
    obtain ⟨⟨ha2, _⟩, ⟨hb2, _⟩, hprod⟩ := hp
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha2
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hb2
    have hst : (s + 1) * (r + 1) = n + 1 := by
      have key : (2 + s) * (2 + r) = (s + 1) * (r + 1) + (s + r + 3) := by ring
      rw [key] at hprod; linarith
    refine ⟨s + 1, Nat.mem_divisors.mpr ⟨⟨r + 1, hst.symm⟩, by omega⟩, ?_⟩
    have hdiv : (n + 1) / (s + 1) = r + 1 := by
      rw [← hst]; exact Nat.mul_div_cancel_left _ (by omega)
    simp only [Prod.mk.injEq, hdiv]; omega

end Erdos493OQ01C2
