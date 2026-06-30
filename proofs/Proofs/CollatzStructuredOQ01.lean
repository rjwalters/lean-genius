/-
# Collatz Conjecture (Erdős-adjacent OQ-01): Reduction to Odd Inputs

  Source problem: the Collatz ("3n+1") conjecture — every positive integer
  reaches 1 under n ↦ n/2 (n even), n ↦ 3n+1 (n odd). This is OPEN and is
  **not** proved here.

  The parent file `Proofs.CollatzStructured` proves the easy structured cases
  (powers of two reach 1; the reaching set is closed under doubling) and
  records the full conjecture as an axiom. The Collatz-cycle files handle the
  no-short-cycle side. What none of them record is the elementary but genuinely
  useful **structural reduction**: the conjecture for all n ≥ 1 is *equivalent*
  to the conjecture restricted to odd n.

  This file proves, with **0 axioms and 0 sorries** (it does NOT use the
  parent's `collatz_conjecture` axiom):

  1. **One-step invariance.** `ReachesOne (collatz n) ↔ ReachesOne n`: a number
     reaches 1 iff its Collatz successor does. The reaching set is invariant
     under the dynamics in both directions.

  2. **Doubling invariance (both directions).** `ReachesOne (2 * n) ↔
     ReachesOne n`, hence `ReachesOne (2 ^ m * n) ↔ ReachesOne n`. The parent
     only had the forward implication; the reverse is what powers the reduction.

  3. **Reduction to odd inputs (headline).**
     `collatz_reduces_to_odd : (∀ n ≥ 1, ReachesOne n) ↔ (∀ m ≥ 1, m odd → ReachesOne m)`.
     Every n ≥ 1 factors as `2 ^ v₂(n) · oddPart n` with `oddPart n` odd, and
     reaching 1 is invariant under stripping the powers of two. So to settle
     Collatz it suffices to settle it on odd numbers — and a minimal
     counterexample, if one exists, may be taken odd (`collatz_counterexample_odd`).

  Honesty note: the Collatz conjecture itself remains OPEN. The new content here
  is the equivalence machinery (one-step / doubling / odd reduction), which is
  standard folklore but was not formalized in the gallery. Nothing here brings
  the open problem closer to resolution; it organizes the search space.

  Tags: number-theory, collatz, dynamical-systems, reduction, open-problem
-/

import Mathlib
import Proofs.CollatzStructured

namespace Collatz

/-!
## One-step invariance of the reaching set

`ReachesOne n` means some Collatz iterate of `n` equals `1`. We show membership
is invariant under one step of the dynamics, in both directions.
-/

/-- **Backward step.** If the successor `collatz n` reaches 1, so does `n`
    (prepend the first step). Unconditional. -/
theorem reachesOne_of_reachesOne_collatz {n : ℕ} (h : ReachesOne (collatz n)) :
    ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  simp only [collatzIter] at hk ⊢
  rw [Function.iterate_succ_apply]
  exact hk

/-- **Forward step.** If `n` reaches 1, so does its successor `collatz n`.
    The only subtlety is the base case `n = 1` (where the witness is `0` steps):
    there `collatz 1 = 4 = 2²` reaches 1 by the powers-of-two lemma. -/
theorem reachesOne_collatz_of_reachesOne {n : ℕ} (h : ReachesOne n) :
    ReachesOne (collatz n) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    simp only [collatzIter, Function.iterate_zero_apply] at hk
    subst hk
    rw [collatz_one]
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact pow_two_reaches_one 2 (by norm_num)
  | succ j =>
    refine ⟨j, ?_⟩
    simp only [collatzIter] at hk ⊢
    rwa [Function.iterate_succ_apply] at hk

/-- **One-step invariance.** `n` reaches 1 iff `collatz n` does. -/
theorem reachesOne_collatz_iff (n : ℕ) : ReachesOne (collatz n) ↔ ReachesOne n :=
  ⟨reachesOne_of_reachesOne_collatz, reachesOne_collatz_of_reachesOne⟩

/-!
## Doubling invariance

The parent file proves `ReachesOne n → ReachesOne (2 * n)` (closure under
doubling). Using one-step invariance we get the reverse, hence an equivalence,
and by induction the same for any power of two.
-/

/-- **Doubling invariance.** `2 * n` reaches 1 iff `n` does. Forward direction
    is `collatz (2 * n) = n` composed with one-step invariance; the reverse is
    the parent's `reaches_one_double`. -/
theorem reachesOne_two_mul_iff (n : ℕ) : ReachesOne (2 * n) ↔ ReachesOne n := by
  constructor
  · intro h
    have h' : ReachesOne (collatz (2 * n)) := reachesOne_collatz_of_reachesOne h
    rwa [collatz_two_mul] at h'
  · exact reaches_one_double

/-- **Power-of-two invariance.** `2 ^ m * n` reaches 1 iff `n` does. -/
theorem reachesOne_pow_two_mul_iff (m n : ℕ) :
    ReachesOne (2 ^ m * n) ↔ ReachesOne n := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    rw [h2, reachesOne_two_mul_iff, ih]

/-!
## The odd part and the reduction to odd inputs

`oddPart n = ordCompl[2] n = n / 2 ^ v₂(n)` is `n` with all factors of two
removed. For `n ≥ 1` it is odd and positive, and `n = 2 ^ v₂(n) · oddPart n`.
-/

/-- The odd part of `n`: `n` with every factor of two stripped. -/
def oddPart (n : ℕ) : ℕ := ordCompl[2] n

/-- For `n ≥ 1`, the odd part is positive. -/
theorem oddPart_pos {n : ℕ} (hn : n ≥ 1) : oddPart n ≥ 1 := by
  unfold oddPart
  have := Nat.ordCompl_pos (n := n) 2 (by omega)
  omega

/-- For `n ≥ 1`, the odd part is genuinely odd. -/
theorem oddPart_odd {n : ℕ} (hn : n ≥ 1) : oddPart n % 2 = 1 := by
  unfold oddPart
  have h : ¬ (2 ∣ ordCompl[2] n) := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  omega

/-- The two-adic factorization: `n = 2 ^ v₂(n) · oddPart n`. -/
theorem pow_factorization_mul_oddPart (n : ℕ) :
    2 ^ (n.factorization 2) * oddPart n = n := by
  unfold oddPart
  exact Nat.ordProj_mul_ordCompl_eq_self n 2

/-- `n` reaches 1 iff its odd part does (for `n ≥ 1`). -/
theorem reachesOne_oddPart_iff {n : ℕ} (hn : n ≥ 1) :
    ReachesOne (oddPart n) ↔ ReachesOne n := by
  have hd := pow_factorization_mul_oddPart n
  constructor
  · intro h
    rw [← hd]
    exact (reachesOne_pow_two_mul_iff _ _).mpr h
  · intro h
    rw [← hd] at h
    exact (reachesOne_pow_two_mul_iff _ _).mp h

/-!
## Headline: the conjecture reduces to the odd case
-/

/-- **The Collatz conjecture reduces to odd inputs.** Every positive integer
    reaches 1 *iff* every odd positive integer does. Forward is immediate;
    backward strips the powers of two via `reachesOne_oddPart_iff`. -/
theorem collatz_reduces_to_odd :
    (∀ n, n ≥ 1 → ReachesOne n) ↔ (∀ m, m ≥ 1 → m % 2 = 1 → ReachesOne m) := by
  refine ⟨fun H m hm _ => H m hm, fun H n hn => ?_⟩
  have hodd : ReachesOne (oddPart n) :=
    H (oddPart n) (oddPart_pos hn) (oddPart_odd hn)
  exact (reachesOne_oddPart_iff hn).mp hodd

/-- **Minimal counterexamples may be taken odd.** If some `n ≥ 1` fails to reach
    1, then some *odd* `m ≥ 1` also fails. Contrapositive of the reduction. -/
theorem collatz_counterexample_odd
    (h : ∃ n, n ≥ 1 ∧ ¬ ReachesOne n) :
    ∃ m, m ≥ 1 ∧ m % 2 = 1 ∧ ¬ ReachesOne m := by
  by_contra hc
  push_neg at hc
  -- hc : ∀ m, m ≥ 1 → m % 2 = 1 → ReachesOne m
  obtain ⟨n, hn, hnot⟩ := h
  exact hnot (collatz_reduces_to_odd.mpr (fun m hm hodd => hc m hm hodd) n hn)

/-!
## The Syracuse (accelerated odd) map

The standard *accelerated* Collatz map acts on odd numbers by `n ↦ (3n+1)/2^v₂(3n+1)`,
i.e. it does the `3n+1` step and then strips **all** the resulting powers of two in one
move, landing on the next odd number in the trajectory. Concretely

    `syracuse n = oddPart (3 n + 1)`.

We show this map is realised by finitely many ordinary Collatz steps, that its reaching
set is *exactly* the Collatz reaching set on odd inputs, and hence that the Collatz
conjecture is **equivalent** to "every odd `m ≥ 1` reaches 1 under `syracuse`". This is
the second item on the file's research agenda (equireachability for the accelerated map).
-/

/-- The Syracuse / accelerated odd map: `n ↦ (3n+1)` with all factors of two stripped. -/
def syracuse (n : ℕ) : ℕ := oddPart (3 * n + 1)

/-- The Syracuse map always lands on an odd number (`3n+1 ≥ 1`, so its odd part is odd). -/
theorem syracuse_odd (n : ℕ) : syracuse n % 2 = 1 :=
  oddPart_odd (by omega)

/-- **Halving a pure power-of-two multiple.** Applying `collatz` `i ≤ v` times to
    `2^v · q` strips `i` factors of two: `collatz^[i] (2^v · q) = 2^(v-i) · q`. -/
theorem collatz_iter_pow_two_mul_le (q : ℕ) :
    ∀ i v, i ≤ v → collatz^[i] (2 ^ v * q) = 2 ^ (v - i) * q := by
  intro i
  induction i with
  | zero => intro v _; simp
  | succ j ih =>
    intro v hv
    have hv1 : 1 ≤ v := by omega
    rw [Function.iterate_succ_apply]
    have hsplit : 2 ^ v * q = 2 * (2 ^ (v - 1) * q) := by
      rw [← mul_assoc]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    rw [hsplit, collatz_two_mul, ih (v - 1) (by omega)]
    have hexp : v - 1 - j = v - (j + 1) := by omega
    rw [hexp]

/-- **Collatz realises Syracuse.** From an odd `n`, exactly `v₂(3n+1) + 1` ordinary
    Collatz steps reach `syracuse n` (the `3n+1` step plus the halvings). -/
theorem collatz_iter_eq_syracuse {n : ℕ} (hodd : n % 2 = 1) :
    collatz^[(3 * n + 1).factorization 2 + 1] n = syracuse n := by
  set v := (3 * n + 1).factorization 2 with hvdef
  have hfac : 2 ^ v * syracuse n = 3 * n + 1 := by
    rw [hvdef]; unfold syracuse; exact pow_factorization_mul_oddPart (3 * n + 1)
  rw [Function.iterate_succ_apply, collatz_odd hodd, ← hfac,
      collatz_iter_pow_two_mul_le _ v v (le_refl v)]
  simp

/-- **Per-step equireachability.** For odd `n`, `syracuse n` reaches 1 iff `n` does. -/
theorem reachesOne_syracuse_iff {n : ℕ} (hodd : n % 2 = 1) :
    ReachesOne (syracuse n) ↔ ReachesOne n := by
  unfold syracuse
  rw [reachesOne_oddPart_iff (n := 3 * n + 1) (by omega), ← collatz_odd hodd]
  exact reachesOne_collatz_iff n

/-- Iterating the Syracuse map preserves oddness. -/
theorem syracuseIter_odd {n : ℕ} (hodd : n % 2 = 1) (k : ℕ) :
    (syracuse^[k] n) % 2 = 1 := by
  cases k with
  | zero => simpa using hodd
  | succ j => rw [Function.iterate_succ_apply']; exact syracuse_odd _

/-- **Iterated equireachability.** For odd `n`, any Syracuse iterate `syracuse^[k] n`
    reaches 1 iff `n` does. -/
theorem reachesOne_syracuseIter_iff {n : ℕ} (hodd : n % 2 = 1) (k : ℕ) :
    ReachesOne (syracuse^[k] n) ↔ ReachesOne n := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', reachesOne_syracuse_iff (syracuseIter_odd hodd j), ih]

/-!
## The Syracuse reaching predicate and full equivalence

`SyrReachesOne n` means some *Syracuse* iterate of `n` equals 1. For odd inputs this is
**equivalent** to the ordinary Collatz reaching predicate `ReachesOne`.
-/

/-- `n` reaches 1 under the Syracuse map. -/
def SyrReachesOne (n : ℕ) : Prop := ∃ k : ℕ, syracuse^[k] n = 1

/-- **Forward direction.** If an odd `n` reaches 1 under Syracuse, it reaches 1 under
    ordinary Collatz (each accelerated step is a block of ordinary steps). -/
theorem reachesOne_of_syrReachesOne {n : ℕ} (hodd : n % 2 = 1)
    (h : SyrReachesOne n) : ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  have h1 : ReachesOne (syracuse^[k] n) := by rw [hk]; exact one_reaches_one
  exact (reachesOne_syracuseIter_iff hodd k).mp h1

/-- Auxiliary for the converse: strong induction on the Collatz step count. -/
theorem syrReaches_aux : ∀ k n, n % 2 = 1 → collatz^[k] n = 1 → SyrReachesOne n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hodd hk
    by_cases hn1 : n = 1
    · subst hn1; exact ⟨0, rfl⟩
    · have hn_gt1 : n > 1 := by omega
      set v := (3 * n + 1).factorization 2 with hvdef
      have hfac : 2 ^ v * syracuse n = 3 * n + 1 := by
        rw [hvdef]; unfold syracuse; exact pow_factorization_mul_oddPart (3 * n + 1)
      -- `v + 1` Collatz steps realise one Syracuse step.
      have hreal : collatz^[v + 1] n = syracuse n := by
        rw [Function.iterate_succ_apply, collatz_odd hodd, ← hfac,
            collatz_iter_pow_two_mul_le _ v v (le_refl v)]
        simp
      -- The trajectory cannot reach 1 before step `v + 1`, so `v + 1 ≤ k`.
      have hsle : v + 1 ≤ k := by
        rcases Nat.lt_or_ge k (v + 1) with hlt | hge
        · exfalso
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0; simp only [Function.iterate_zero_apply] at hk; omega
          · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
            have hval : collatz^[i + 1] n = 2 ^ (v - i) * syracuse n := by
              rw [Function.iterate_succ_apply, collatz_odd hodd, ← hfac,
                  collatz_iter_pow_two_mul_le _ i v (by omega)]
            rw [hval] at hk
            have hdvd : 2 ∣ 2 ^ (v - i) * syracuse n :=
              (dvd_pow_self 2 (by omega : v - i ≠ 0)).mul_right _
            rw [hk] at hdvd
            omega
        · exact hge
      -- Recurse on the smaller residual count for `syracuse n`.
      have hk' : collatz^[k - (v + 1)] (syracuse n) = 1 := by
        have hcomp : collatz^[k - (v + 1)] (collatz^[v + 1] n) = 1 := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hsle]; exact hk
        rwa [hreal] at hcomp
      have hlt' : k - (v + 1) < k := by omega
      obtain ⟨t, ht⟩ := ih _ hlt' _ (syracuse_odd n) hk'
      exact ⟨t + 1, by rw [Function.iterate_succ_apply, ht]⟩

/-- **Converse direction.** If an odd `n` reaches 1 under ordinary Collatz, it reaches 1
    under the accelerated Syracuse map. -/
theorem syrReachesOne_of_reachesOne {n : ℕ} (hodd : n % 2 = 1)
    (h : ReachesOne n) : SyrReachesOne n := by
  obtain ⟨k, hk⟩ := h
  simp only [collatzIter] at hk
  exact syrReaches_aux k n hodd hk

/-- **Full equireachability (headline).** For odd `n`, the Syracuse and Collatz reaching
    predicates coincide. -/
theorem reachesOne_iff_syrReachesOne {n : ℕ} (hodd : n % 2 = 1) :
    SyrReachesOne n ↔ ReachesOne n :=
  ⟨reachesOne_of_syrReachesOne hodd, syrReachesOne_of_reachesOne hodd⟩

/-- **The Collatz conjecture is equivalent to its Syracuse form.** Every positive integer
    reaches 1 under Collatz iff every odd positive integer reaches 1 under the accelerated
    Syracuse map. This refines `collatz_reduces_to_odd` from the slow map to the fast one. -/
theorem collatz_iff_syracuse :
    (∀ n, n ≥ 1 → ReachesOne n) ↔ (∀ m, m ≥ 1 → m % 2 = 1 → SyrReachesOne m) := by
  rw [collatz_reduces_to_odd]
  constructor
  · intro H m hm hodd; exact (reachesOne_iff_syrReachesOne hodd).mpr (H m hm hodd)
  · intro H m hm hodd; exact (reachesOne_iff_syrReachesOne hodd).mp (H m hm hodd)

#check @collatz_reduces_to_odd
#check @reachesOne_collatz_iff
#check @collatz_iff_syracuse
#check @reachesOne_iff_syrReachesOne
#print axioms collatz_reduces_to_odd
#print axioms reachesOne_pow_two_mul_iff
#print axioms collatz_iff_syracuse

end Collatz
