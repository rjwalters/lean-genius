/-
Test file for hl_conjectures_tension proof approach
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace TestHLTension

open Nat Finset

-- Basic definitions
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p

def HardyLittlewoodConjecture : Prop :=
  ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 1 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ ∀ h ∈ H, Nat.Prime (n + h)

def SecondHardyLittlewoodConjecture : Prop :=
  ∀ x y : ℕ, x ≥ 2 → y ≥ 2 →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y

/-- Key counting lemma: if we have k distinct primes all in [a, b],
    then count(b+1) - count(a) ≥ k. -/
theorem count_primes_in_range (S : Finset ℕ) (a b : ℕ) (hab : a ≤ b + 1)
    (hS : ∀ s ∈ S, a ≤ s ∧ s ≤ b)
    (hprime : ∀ s ∈ S, Nat.Prime s) :
    Nat.count Nat.Prime (b + 1) ≥ Nat.count Nat.Prime a + S.card := by
  -- The primes in S are a subset of {i | a ≤ i ∧ i < b+1 ∧ Prime i}
  -- count(b+1) - count(a) = #{i | a ≤ i < b+1 ∧ Prime i} ≥ |S|
  have hle : S.card ≤ Nat.count Nat.Prime (b + 1) - Nat.count Nat.Prime a := by
    -- S ⊆ {a, a+1, ..., b} ∩ {primes}
    -- The set {i | a ≤ i < b+1 ∧ Prime i} has cardinality count(b+1) - count(a)
    -- S maps injectively into this set
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    have hsub : S ⊆ (Finset.range (b + 1)).filter Nat.Prime \ (Finset.range a).filter Nat.Prime := by
      intro s hs
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range,
          Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨by omega, hprime s hs⟩, fun ⟨hlt, _⟩ => by have := (hS s hs).1; omega⟩
    calc S.card ≤ ((Finset.range (b + 1)).filter Nat.Prime \
                   (Finset.range a).filter Nat.Prime).card := Finset.card_le_card hsub
      _ = ((Finset.range (b + 1)).filter Nat.Prime).card -
          ((Finset.range a).filter Nat.Prime ∩
           (Finset.range (b + 1)).filter Nat.Prime).card := by
            rw [Finset.card_sdiff_eq_card_sub_card_inter]
      _ ≤ ((Finset.range (b + 1)).filter Nat.Prime).card -
          ((Finset.range a).filter Nat.Prime).card := by
            have hsubset : (Finset.range a).filter Nat.Prime ⊆
                          (Finset.range (b + 1)).filter Nat.Prime := by
              intro i hi
              rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
              exact ⟨by omega, hi.2⟩
            have hinter : (Finset.range a).filter Nat.Prime ∩
                          (Finset.range (b + 1)).filter Nat.Prime =
                          (Finset.range a).filter Nat.Prime :=
              Finset.inter_eq_left.mpr hsubset
            rw [hinter]
  omega

/-- Corrected version: π(d+1) ≥ k (not π(d) ≥ k).

    The original theorem claimed π(d) ≥ k which is FALSE:
    counterexample {0, 2} with d = 2: π(2) = 1 < 2 = k. -/
theorem hl_conjectures_tension_corrected (hHL1 : HardyLittlewoodConjecture)
    (hHL2 : SecondHardyLittlewoodConjecture) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 1 →
    ∀ d : ℕ, (∀ h ∈ H, h ≤ d) → d ≥ 2 →
    Nat.primeCounting (d + 1) ≥ H.card := by
  intro H hadm hcard d hle hd
  -- Get n large enough from HL1
  obtain ⟨n, hn, hprimes⟩ := hHL1 H hadm hcard (d + 3)
  -- n ≥ d + 3, so n - 1 ≥ d + 2 ≥ 4 ≥ 2
  have hn3 : n ≥ d + 3 := hn
  have hn1_ge2 : n - 1 ≥ 2 := by omega
  -- Apply HL2 with x = n-1, y = d+1
  have hd1_ge2 : d + 1 ≥ 2 := by omega
  have hhl2 := hHL2 (n - 1) (d + 1) hn1_ge2 hd1_ge2
  -- (n-1) + (d+1) = n + d
  have heq : n - 1 + (d + 1) = n + d := by omega
  rw [heq] at hhl2
  -- The primes {n+h : h ∈ H} are all in [n, n+d]
  -- Build the Finset of these primes
  have hprimes_range : ∀ h ∈ H, n ≤ n + h ∧ n + h ≤ n + d := by
    intro h hh
    exact ⟨by omega, by have := hle h hh; omega⟩
  -- The map h ↦ n+h is injective on H
  have hinj : (H.image (· + n)).card = H.card := by
    rw [Finset.card_image_of_injective]
    intro a b hab; omega
  -- count(n+d+1) ≥ count(n) + |H|
  have hcount : Nat.count Nat.Prime (n + d + 1) ≥ Nat.count Nat.Prime n + H.card := by
    rw [← hinj]
    apply count_primes_in_range (H.image (· + n)) n (n + d) (by omega)
    · intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨h, hh, rfl⟩ := hs
      exact hprimes_range h hh
    · intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨h, hh, rfl⟩ := hs
      have := hprimes h hh
      rw [Nat.add_comm] at this
      exact this
  -- primeCounting(n+d) = count(n+d+1)
  -- primeCounting(n-1) = count(n)
  unfold Nat.primeCounting Nat.primeCounting' at hhl2
  -- count(n+d+1) ≤ count(n) + count(d+2)
  -- So count(d+2) ≥ |H|
  -- primeCounting(d+1) = count(d+2) ≥ |H|
  unfold Nat.primeCounting Nat.primeCounting'
  have hpc : Nat.count Nat.Prime (n + d + 1) ≤
      Nat.count Nat.Prime n + Nat.count Nat.Prime (d + 2) := by
    convert hhl2 using 2 <;> omega
  omega

end TestHLTension
