import Mathlib

/-
# Erdős #1000 OQ-03 → OQ-02: Explicit values of the combinatorial Jordan totient

## Open question

The sibling entry `erdos-1000-oq-03-oq-01` establishes the **combinatorial
characterisation** of Jordan's totient `J_k` (the count of setwise-coprime
`k`-tuples) and Möbius-inverts it to the convolution form developed in the parent
`erdos-1000-oq-03` (`J_k = μ * pow k`).  This companion entry focuses on the
**explicit arithmetic values** of that count — its prime-power closed form, the
recovery of Euler's `φ`, and Gauss's classical totient identity — all derived
self-containedly from the same geometric divisor-sum identity.

## What this file proves (0 axioms, 0 sorries)

We take the **honest combinatorial definition**
`jordanCount k n = #{ a : Fin k → {0,…,n-1} : gcd(a₀,…,a_{k-1}, n) = 1 }`
and prove, entirely from first principles, the explicit values that make it the
genuine `k`-dimensional generalisation of Euler's `φ`:

* `jordan_count_divisor_sum` : `∑_{d ∣ n} jordanCount k d = n^k`  — **headline**,
  the geometric Gauss identity (every one of the `n^k` tuples is classified by the
  divisor `gcd(a, n)`, and the fibre over `d` rescales to the coprime tuples mod
  `n/d`); generalises Gauss's `∑_{d∣n} φ(d) = n`.
* `jordan_count_one` : `jordanCount k 1 = 1`.
* `jordan_count_le_pow` : `jordanCount k n ≤ n^k`.
* `jordan_count_eq_totient` : `jordanCount 1 n = φ(n)`  — recovers Euler's totient.
* `sum_totient_eq_self` : `∑_{d∣n} φ(d) = n`  — Gauss's classical identity, here a
  combinatorial corollary of the `k = 1` case.
* `jordan_count_prime_pow` / `jordan_count_prime_pow_sub` :
  `J_k(p^{m+1}) = p^{(m+1)k} - p^{mk}` for `p` prime (telescoping the divisor sum);
  for `k = 1` this is `φ(p^{m+1}) = p^{m+1} - p^m`.

## Method

The crux is `fiber_card`: a `Finset.card_bij'` exhibiting, for each `d ∣ n`, an
explicit bijection `a ↦ (aⱼ/d)` between the `k`-tuples in `{0,…,n-1}` with
`gcd(a, n) = d` and the coprime `k`-tuples in `{0,…,n/d-1}`.  The gcd of a
coordinatewise-scaled tuple is handled by `Finset.gcd_mul_left` (`gcd_smul`), and
the divisor sum is assembled with `Finset.card_eq_sum_card_fiberwise` and the
divisor reindexing `Nat.sum_div_divisors`.  The prime-power values then telescope
out of the divisor sum via `Nat.sum_divisors_prime_pow`.

## Significance relative to the gallery

This is the combinatorial counterpart of the parent `erdos-1000-oq-03` (which gives
the convolution/multiplicative theory): together they show the two standard
definitions of `J_k` — the analytic `μ * pow k` and the geometric tuple count —
satisfy the same Gauss divisor-sum law, and both restrict to Euler's `φ` at `k = 1`.

## Tags

erdos, number-theory, jordan-totient, euler-totient, gauss-identity,
divisor-sum, combinatorics, bijection, multiplicative-function
-/


namespace Erdos1000OQ03OQ02

open Finset

/-- The **combinatorial Jordan totient** of order `k`: the number of `k`-tuples
`a : Fin k → {0,…,n-1}` whose entries are *setwise coprime to `n`*, i.e.
`gcd(a₀,…,a_{k-1}, n) = 1`.  For `k = 1` this is Euler's `φ`. -/
def jordanCount (k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k => range n).filter
    (fun a => Nat.Coprime ((univ : Finset (Fin k)).gcd a) n)).card

/-- The gcd of a tuple scaled coordinatewise by `d` is `d` times the gcd. -/
lemma gcd_smul (k d : ℕ) (b : Fin k → ℕ) :
    (univ : Finset (Fin k)).gcd (fun j => d * b j)
      = d * (univ : Finset (Fin k)).gcd b := by
  rw [Finset.gcd_mul_left]; simp

/-- **Fiber count.** Among all `k`-tuples in `{0,…,n-1}`, those whose entrywise
gcd with `n` equals a fixed divisor `d` are in bijection (via `aⱼ ↦ aⱼ/d`) with the
tuples in `{0,…,n/d-1}` setwise coprime to `n/d`.  Hence the fiber has
`jordanCount k (n/d)` elements. -/
lemma fiber_card (k : ℕ) {n d : ℕ} (hd : d ∈ n.divisors) :
    ((Fintype.piFinset fun _ : Fin k => range n).filter
        (fun a => Nat.gcd ((univ : Finset (Fin k)).gcd a) n = d)).card
      = jordanCount k (n / d) := by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.mp hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  unfold jordanCount
  apply Finset.card_bij'
    (fun a _ => fun j => a j / d)
    (fun b _ => fun j => d * b j)
  · -- hi : forward maps into target
    intro a ha
    rw [mem_filter, Fintype.mem_piFinset] at ha
    obtain ⟨hapi, hgcd⟩ := ha
    -- d divides every a j
    have hdG : d ∣ (univ : Finset (Fin k)).gcd a := by
      rw [← hgcd]; exact Nat.gcd_dvd_left _ _
    have hdaj : ∀ j, d ∣ a j := fun j =>
      hdG.trans (Finset.gcd_dvd (mem_univ j))
    rw [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun j => ?_, ?_⟩
    · -- a j / d < n / d
      rw [mem_range, Nat.div_lt_iff_lt_mul hdpos, Nat.div_mul_cancel hdn]
      exact mem_range.mp (hapi j)
    · -- Coprime (gcd of reduced tuple) (n/d)
      have hGeq : (univ : Finset (Fin k)).gcd a
          = d * (univ : Finset (Fin k)).gcd (fun j => a j / d) := by
        conv_lhs => rw [show a = (fun j => d * (a j / d)) from
          funext (fun j => (Nat.mul_div_cancel' (hdaj j)).symm)]
        exact gcd_smul k d _
      have hkey : d * Nat.gcd ((univ : Finset (Fin k)).gcd (fun j => a j / d)) (n / d) = d := by
        have : Nat.gcd ((univ : Finset (Fin k)).gcd a) n = d := hgcd
        rw [hGeq, show n = d * (n / d) from (Nat.mul_div_cancel' hdn).symm,
          Nat.gcd_mul_left] at this
        -- this : d * gcd (..) ((d*(n/d))/d) = d ; simplify d*(n/d)/d = n/d
        simpa [Nat.mul_div_cancel_left _ hdpos] using this
      have : Nat.gcd ((univ : Finset (Fin k)).gcd (fun j => a j / d)) (n / d) = 1 :=
        Nat.eq_of_mul_eq_mul_left hdpos (by rw [hkey, mul_one])
      exact this
  · -- hj : backward maps into source
    intro b hb
    rw [mem_filter, Fintype.mem_piFinset] at hb
    obtain ⟨hbpi, hcop⟩ := hb
    rw [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun j => ?_, ?_⟩
    · -- d * b j < n
      rw [mem_range]
      calc d * b j < d * (n / d) := by
              exact (Nat.mul_lt_mul_left hdpos).mpr (mem_range.mp (hbpi j))
        _ = n := Nat.mul_div_cancel' hdn
    · -- gcd (gcd of scaled tuple) n = d
      rw [gcd_smul k d b, show n = d * (n / d) from (Nat.mul_div_cancel' hdn).symm,
        Nat.gcd_mul_left]
      rw [show ((univ : Finset (Fin k)).gcd b).gcd (n / d) = 1 from hcop, mul_one]
  · -- left inverse: j (i a) = a
    intro a ha
    rw [mem_filter, Fintype.mem_piFinset] at ha
    obtain ⟨-, hgcd⟩ := ha
    have hdG : d ∣ (univ : Finset (Fin k)).gcd a := by
      rw [← hgcd]; exact Nat.gcd_dvd_left _ _
    have hdaj : ∀ j, d ∣ a j := fun j =>
      hdG.trans (Finset.gcd_dvd (mem_univ j))
    funext j
    exact Nat.mul_div_cancel' (hdaj j)
  · -- right inverse: i (j b) = b
    intro b _
    funext j
    exact Nat.mul_div_cancel_left _ hdpos

/-- **Headline (geometric Gauss identity).** The combinatorial Jordan totients of the
divisors of `n` sum to `n^k`:
`∑_{d ∣ n} jordanCount k d = n^k`.
For `k = 1` this is Gauss's `∑_{d ∣ n} φ(d) = n`. -/
theorem jordan_count_divisor_sum (k : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, jordanCount k d = n ^ k := by
  have hmaps : Set.MapsTo
      (fun a : Fin k → ℕ => Nat.gcd ((univ : Finset (Fin k)).gcd a) n)
      ↑(Fintype.piFinset fun _ : Fin k => range n) ↑n.divisors := by
    intro a _
    simp only [Finset.mem_coe]
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hn.ne'⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ d ∈ n.divisors,
      ((Fintype.piFinset fun _ : Fin k => range n).filter
        (fun a => Nat.gcd ((univ : Finset (Fin k)).gcd a) n = d)).card
        = jordanCount k (n / d) := fun d hd => fiber_card k hd
  rw [Finset.sum_congr rfl hfib] at hcard
  have hpc : (Fintype.piFinset fun _ : Fin k => range n).card = n ^ k := by
    rw [Fintype.card_piFinset]; simp
  rw [hpc] at hcard
  rw [Nat.sum_div_divisors] at hcard
  exact hcard.symm

/-- `jordanCount k 1 = 1`: the single all-zero tuple is (vacuously) coprime to `1`. -/
theorem jordan_count_one (k : ℕ) : jordanCount k 1 = 1 := by
  have h := jordan_count_divisor_sum k (n := 1) one_pos
  simpa using h

/-- `jordanCount k n ≤ n^k`: the coprime tuples are a subset of all `n^k` tuples. -/
theorem jordan_count_le_pow (k : ℕ) {n : ℕ} (hn : 0 < n) :
    jordanCount k n ≤ n ^ k := by
  rw [← jordan_count_divisor_sum k hn]
  exact Finset.single_le_sum (f := fun d => jordanCount k d)
    (fun i _ => Nat.zero_le _) (Nat.mem_divisors_self n hn.ne')

/-- The entrywise gcd of a length-one tuple is its single entry. -/
lemma gcd_fin_one (a : Fin 1 → ℕ) : (univ : Finset (Fin 1)).gcd a = a 0 := by
  rw [Finset.univ_unique]
  simp [Finset.gcd_singleton]

/-- **Euler recovery.** For `k = 1` the combinatorial Jordan totient is exactly
Euler's totient: `jordanCount 1 n = φ(n)`.  Indeed the entrywise-gcd condition on a
length-one tuple `(a₀)` is just `gcd(a₀, n) = 1`. -/
theorem jordan_count_eq_totient (n : ℕ) : jordanCount 1 n = Nat.totient n := by
  rw [Nat.totient_eq_card_coprime]
  unfold jordanCount
  refine Finset.card_bij' (fun a _ => a 0) (fun x _ => (fun _ => x)) ?hi ?hj ?li ?ri
  case hi =>
    intro a ha
    rw [mem_filter, Fintype.mem_piFinset] at ha
    obtain ⟨hapi, hcop⟩ := ha
    rw [gcd_fin_one] at hcop
    rw [mem_filter]
    exact ⟨hapi 0, (Nat.coprime_comm.mp hcop)⟩
  case hj =>
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hxr, hcop⟩ := hx
    rw [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun _ => hxr, ?_⟩
    rw [gcd_fin_one]
    exact Nat.coprime_comm.mp hcop
  case li =>
    intro a ha
    funext j
    rw [Subsingleton.elim j 0]
  case ri =>
    intro x _
    rfl

/-- **Gauss's totient identity, derived combinatorially.** Specialising the geometric
divisor-sum identity to `k = 1` (where the count *is* Euler's `φ`) recovers
`∑_{d ∣ n} φ(d) = n` — the count of all `n` residues partitioned by the exact
denominator of `m/n`. -/
theorem sum_totient_eq_self {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, Nat.totient d = n := by
  have h := jordan_count_divisor_sum 1 hn
  simp only [jordan_count_eq_totient, pow_one] at h
  exact h

/-- **Prime-power values (additive form).** `J_k(p^{m+1}) + p^{mk} = p^{(m+1)k}`,
obtained by telescoping the divisor sum over `divisors(p^{m+1}) = {p^0,…,p^{m+1}}`. -/
theorem jordan_count_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    jordanCount k (p ^ (m + 1)) + p ^ (m * k) = p ^ ((m + 1) * k) := by
  have h1 := jordan_count_divisor_sum k (n := p ^ (m + 1)) (pow_pos hp.pos _)
  have h2 := jordan_count_divisor_sum k (n := p ^ m) (pow_pos hp.pos _)
  rw [Nat.sum_divisors_prime_pow hp, ← pow_mul] at h1
  rw [Nat.sum_divisors_prime_pow hp, ← pow_mul] at h2
  rw [Finset.sum_range_succ, h2] at h1
  omega

/-- **Prime-power values (closed form).** `J_k(p^{m+1}) = p^{(m+1)k} - p^{mk}`.
For `k = 1` this is Euler's `φ(p^{m+1}) = p^{m+1} - p^m`. -/
theorem jordan_count_prime_pow_sub (k : ℕ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    jordanCount k (p ^ (m + 1)) = p ^ ((m + 1) * k) - p ^ (m * k) := by
  have := jordan_count_prime_pow k hp m; omega

end Erdos1000OQ03OQ02
