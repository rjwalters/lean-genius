/-
# Erdős Problem 681: Large Least Prime Factor in Shifted Composites

For all sufficiently large `n`, does there exist a positive integer `k`
such that `n + k` is composite and `p(n + k) > k²`, where `p(m)` is
the least prime factor of `m`?

A generalisation asks whether `p(n + k) > k^d` for any fixed `d`.

Posed by Erdős, Eggleton, and Selfridge.

*Reference:* [erdosproblems.com/681](https://www.erdosproblems.com/681)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Least prime factor -/

/-- The least prime factor of `m`, using `Nat.minFac`. Returns 1 if
`m ≤ 1`. -/
noncomputable def leastPrimeFactor (m : ℕ) : ℕ :=
    if m ≤ 1 then 1 else m.minFac

/-- `p` is the least prime factor of `m`. -/
def IsLeastPrimeFactor (p m : ℕ) : Prop :=
    p.Prime ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q

/- ## Proved infrastructure -/

/-- `Nat.minFac` gives the least prime factor for `m ≥ 2`. -/
theorem minFac_is_lpf (m : ℕ) (hm : 2 ≤ m) :
    IsLeastPrimeFactor m.minFac m := by
  refine ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, ?_⟩
  intro q hq hqd
  exact Nat.minFac_le_of_dvd hq.two_le hqd

/-- A composite number has a least prime factor that is prime. -/
theorem composite_has_lpf (m : ℕ) (_hm : ¬m.Prime) (hm2 : 2 ≤ m) :
    ∃ p : ℕ, IsLeastPrimeFactor p m :=
  ⟨m.minFac, minFac_is_lpf m hm2⟩

/-- If `n + k` is prime, it trivially has least prime factor `n + k`
itself, which is large. The conjecture requires `n + k` composite. -/
theorem prime_lpf_self (p : ℕ) (hp : p.Prime) :
    IsLeastPrimeFactor p p := by
  refine ⟨hp, dvd_refl p, ?_⟩
  intro q hq hqd
  have hq1 : q ≠ 1 := Nat.Prime.one_lt hq |>.ne'
  rcases hp.eq_one_or_self_of_dvd q hqd with h | h
  · exact absurd h hq1
  · exact le_of_eq h.symm

/-- The least prime factor of a composite `m` satisfies
`p(m) ≤ √m`, i.e. `p(m)² ≤ m`. -/
theorem lpf_le_sqrt (m : ℕ) (hm : ¬m.Prime) (hm2 : 2 ≤ m) :
    ∃ p : ℕ, IsLeastPrimeFactor p m ∧ p * p ≤ m := by
  refine ⟨m.minFac, minFac_is_lpf m hm2, ?_⟩
  have := Nat.minFac_sq_le_self (by omega : 0 < m) hm
  rwa [sq] at this

/-- The least prime factor is unique: if both `p` and `q` are least
prime factors of `m`, then `p = q`. -/
theorem lpf_unique (p q m : ℕ) (hp : IsLeastPrimeFactor p m)
    (hq : IsLeastPrimeFactor q m) : p = q := by
  have hpq := hp.2.2 q hq.1 hq.2.1
  have hqp := hq.2.2 p hp.1 hp.2.1
  exact le_antisymm hpq hqp |>.symm ▸ rfl

/-- `leastPrimeFactor m` equals `m.minFac` when `m ≥ 2`. -/
theorem leastPrimeFactor_eq_minFac (m : ℕ) (hm : 2 ≤ m) :
    leastPrimeFactor m = m.minFac := by
  simp [leastPrimeFactor, show ¬(m ≤ 1) by omega]

/-- `leastPrimeFactor m` is a least prime factor for `m ≥ 2`. -/
theorem leastPrimeFactor_is_lpf (m : ℕ) (hm : 2 ≤ m) :
    IsLeastPrimeFactor (leastPrimeFactor m) m := by
  rw [leastPrimeFactor_eq_minFac m hm]
  exact minFac_is_lpf m hm

/-- For prime `p`, `leastPrimeFactor p = p`. -/
theorem leastPrimeFactor_prime (p : ℕ) (hp : p.Prime) :
    leastPrimeFactor p = p := by
  rw [leastPrimeFactor_eq_minFac p hp.two_le]
  exact hp.minFac_eq

/-- The least prime factor of a composite divides it. -/
theorem lpf_dvd (m : ℕ) (hm : 2 ≤ m) :
    leastPrimeFactor m ∣ m := by
  exact (leastPrimeFactor_is_lpf m hm).2.1

/-- The least prime factor of a composite is prime. -/
theorem lpf_prime (m : ℕ) (hm : 2 ≤ m) :
    (leastPrimeFactor m).Prime := by
  exact (leastPrimeFactor_is_lpf m hm).1

/- ## The conjecture -/

/-- Erdős Problem 681: For all sufficiently large `n`, there exists
`k > 0` such that `n + k` is composite and its least prime factor
exceeds `k²`. -/
def ErdosProblem681 : Prop :=
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 0 < k ∧
        ¬(n + k).Prime ∧ 2 ≤ n + k ∧
        ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p

/- ## Generalisation -/

/-- Generalised conjecture: for any fixed `d`, for all large `n`,
there exists `k > 0` with `n + k` composite and `p(n+k) > k^d`. -/
def ErdosProblem681General (d : ℕ) : Prop :=
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 0 < k ∧
        ¬(n + k).Prime ∧ 2 ≤ n + k ∧
        ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ d < p

/-- The original conjecture is exactly the `d = 2` case of the
generalisation. -/
theorem erdos681_is_general_d2 :
    ErdosProblem681 ↔ ErdosProblem681General 2 := by
  rfl

/- ## Structural observations -/

/-- When n + k is prime, minFac(n+k) = n+k, which easily exceeds k² + 1
for large n. -/
theorem prime_offset_gives_large_lpf (n k : ℕ) (_hk : 0 < k)
    (hp : (n + k).Prime) (hn : k ^ 2 < n + k) :
    ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p := by
  intro p hlpf
  have := lpf_unique p (n + k) (n + k) hlpf (prime_lpf_self (n + k) hp)
  rw [this]
  exact hn

/-- For the conjecture, the difficulty lies in composite numbers: if `n + k`
is composite then `p(n+k) ≤ √(n+k)`, giving the constraint
`k² < p(n+k) ≤ √(n+k)`, i.e. `k⁴ < n + k`. -/
theorem composite_constraint (n k : ℕ) (_hk : 0 < k) (hm : ¬(n + k).Prime)
    (hm2 : 2 ≤ n + k)
    (hlpf : ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p) :
    k ^ 4 < n + k := by
  obtain ⟨p, hp, hpsq⟩ := lpf_le_sqrt (n + k) hm hm2
  have hk2 := hlpf p hp
  -- k² < p and p * p ≤ n + k, so k⁴ = (k²)² < p² ≤ n + k
  calc k ^ 4 = (k ^ 2) ^ 2 := by ring
    _ = k ^ 2 * k ^ 2 := by ring
    _ < p * p := by nlinarith
    _ ≤ n + k := hpsq

/-- When `d = 1`, the conjecture asks for `p(n+k) > k`. For k = 1, this
means `p(n+1) > 1`, which holds for all `n ≥ 1` (since `p(m) ≥ 2`
for `m ≥ 2`). -/
theorem d1_k1_trivial (n : ℕ) (_hn : 1 ≤ n) (_hc : ¬(n + 1).Prime) (_hn2 : 2 ≤ n + 1) :
    ∀ p : ℕ, IsLeastPrimeFactor p (n + 1) → 1 ^ 1 < p := by
  intro p ⟨hp, _, _⟩
  simp
  exact hp.one_lt

/-- The `d = 0` case of the generalisation is trivially true:
we need `p(n+k) > k⁰ = 1`, which holds since all prime factors
are `≥ 2`. We pick k = n to get n + k = 2n which is composite
for n ≥ 2. -/
theorem general_d0_trivial :
    ErdosProblem681General 0 := by
  refine ⟨2, fun n hn => ⟨n, by omega, ?_, ?_, ?_⟩⟩
  · -- ¬(n + n).Prime: 2n is even and ≥ 4
    intro hp
    have h2 : 2 ∣ (n + n) := ⟨n, by ring⟩
    have := hp.eq_one_or_self_of_dvd 2 h2
    rcases this with h | h <;> omega
  · omega
  · intro p ⟨hp, _, _⟩
    simp
    exact hp.one_lt

/-- For `d ≥ 1`, the generalised conjecture implies the original. -/
theorem general_monotone (d₁ d₂ : ℕ) (hd : d₁ ≤ d₂)
    (h : ErdosProblem681General d₂) : ErdosProblem681General d₁ := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨k, hk, hc, hm2, hlpf⟩ := hN n hn
  exact ⟨k, hk, hc, hm2, fun p hp => lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (hlpf p hp)⟩

/- ## Connection to Erdős 680 -/

/-- The formulations of #680 and #681 are closely related. Problem 680
uses `minFac` directly, while 681 uses the `IsLeastPrimeFactor` predicate.
This shows equivalence of the core condition. -/
theorem lpf_condition_equiv (m k : ℕ) (hm : 2 ≤ m) :
    (∀ p : ℕ, IsLeastPrimeFactor p m → k < p) ↔ k < m.minFac := by
  constructor
  · intro h
    exact h m.minFac (minFac_is_lpf m hm)
  · intro h p hp
    have := lpf_unique p m.minFac m hp (minFac_is_lpf m hm)
    rw [this]
    exact h
