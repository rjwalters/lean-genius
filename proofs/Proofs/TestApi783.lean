-- Test API availability for Erdős #783
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- Test 1: distinct primes are coprime
example (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne

-- Test 2: Finset.pairwise for coprime primes
example (S : Finset ℕ) (hS : ∀ a ∈ S, Nat.Prime a) (hinj : S.Pairwise (· ≠ ·)) :
    S.Pairwise (fun a b => Nat.Coprime a b) := by
  intro a ha b hb hab
  exact (Nat.coprime_primes (hS a ha) (hS b hb)).mpr hab

-- Test 3: Finset.sum basic
example : ({2, 3} : Finset ℕ).sum (fun _ => (1 : ℕ)) = 2 := by decide

-- Test 4: Coprime → product structure
-- Nat.Coprime.mul_dvd_of_dvd_of_dvd
example (a b m : ℕ) (hab : Nat.Coprime a b) (ha : a ∣ m) (hb : b ∣ m) :
    a * b ∣ m := hab.mul_dvd_of_dvd_of_dvd ha hb
