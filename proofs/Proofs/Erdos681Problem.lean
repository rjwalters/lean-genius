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
    _ < p * p := mul_lt_mul' (le_of_lt hk2) hk2 (Nat.zero_le _)
        (lt_of_le_of_lt (Nat.zero_le _) hk2)
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

/- ## The k = 1 resolution -/

/-- **k = 1 resolves the conjecture when n+1 is composite.**
For ANY d ≥ 0: if n + 1 is composite (and ≥ 2), then k = 1 satisfies
p(n+1) > 1^d = 1, since all prime factors are ≥ 2.

This means the conjecture is open ONLY for those n where n+1 is prime
(i.e., n = p - 1 for some prime p). -/
theorem k1_resolves_all_d (d : ℕ) (n : ℕ) (hn : 2 ≤ n + 1)
    (hc : ¬(n + 1).Prime) :
    0 < 1 ∧ ¬(n + 1).Prime ∧ 2 ≤ n + 1 ∧
      ∀ p : ℕ, IsLeastPrimeFactor p (n + 1) → 1 ^ d < p := by
  refine ⟨Nat.one_pos, hc, hn, fun p ⟨hp, _, _⟩ => ?_⟩
  simp
  exact hp.one_lt

/-- **The d=1 generalization holds whenever n+1 is composite.**
For n ≥ 3 with n+1 composite, ErdosProblem681General 1 is witnessed by k = 1. -/
theorem general_d1_at_composite_succ (n : ℕ) (hn : 3 ≤ n) (hc : ¬(n + 1).Prime) :
    ∃ k : ℕ, 0 < k ∧ ¬(n + k).Prime ∧ 2 ≤ n + k ∧
      ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 1 < p :=
  ⟨1, Nat.one_pos, hc, by omega, fun p ⟨hp, _, _⟩ => by simp; exact hp.one_lt⟩

/-- For odd n ≥ 3, the d=1 generalisation holds with k = 1: n+1 is even
and ≥ 4 hence composite, with p(n+1) ≥ 2 > 1 = 1^1. This covers all
odd integers ≥ 3 without requiring a hypothesis that n+1 is composite. -/
theorem general_d1_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ k : ℕ, 0 < k ∧ ¬(n + k).Prime ∧ 2 ≤ n + k ∧
      ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 1 < p := by
  refine ⟨1, one_pos, ?_, by omega, ?_⟩
  · intro hp
    obtain ⟨m, hm⟩ := hodd
    have h2 : 2 ∣ (n + 1) := ⟨m + 1, by omega⟩
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  · intro p ⟨hp, _, _⟩
    simp
    exact hp.one_lt

/-- **The original d=2 conjecture holds whenever n+1 is composite.**
Since p(n+1) ≥ 2 > 1 = 1², k = 1 always works. -/
theorem conjecture_at_composite_succ (n : ℕ) (hn : 3 ≤ n) (hc : ¬(n + 1).Prime) :
    ∃ k : ℕ, 0 < k ∧ ¬(n + k).Prime ∧ 2 ≤ n + k ∧
      ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 2 < p :=
  ⟨1, Nat.one_pos, hc, by omega, fun p ⟨hp, _, _⟩ => by simp; exact hp.one_lt⟩

/-- **The hard case: n+1 is prime.**
When n + 1 is prime, k = 1 is excluded (n+1 is not composite).
For k ≥ 2, we need a composite m = n + k with p(m) > k^d.
Since p(m) ≤ √m for composite m, this forces k^{2d} < n + k ≈ n,
so k ≲ n^{1/(2d)}. The difficulty is finding such a k. -/
theorem hard_case_constraint (n k d : ℕ) (_hk : 2 ≤ k)
    (hm : ¬(n + k).Prime) (hm2 : 2 ≤ n + k)
    (hlpf : ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ d < p) :
    k ^ (2 * d) < n + k := by
  obtain ⟨p, hp, hpsq⟩ := lpf_le_sqrt (n + k) hm hm2
  have hkd := hlpf p hp
  -- k^d < p and p² ≤ n + k, so k^{2d} < p² ≤ n + k
  have hkd_pos : 0 < k ^ d := by positivity
  calc k ^ (2 * d) = (k ^ d) ^ 2 := by ring
    _ = k ^ d * k ^ d := by ring
    _ < k ^ d * p := Nat.mul_lt_mul_of_pos_left hkd hkd_pos
    _ ≤ p * p := Nat.mul_le_mul_right p (le_of_lt hkd)
    _ ≤ n + k := hpsq

/- ## Witness parity constraints -/

/-- For even m ≥ 4, the least prime factor is 2. -/
theorem minFac_of_even (m : ℕ) (hm : 4 ≤ m) (heven : 2 ∣ m) :
    m.minFac = 2 := by
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd (by norm_num) heven
  · exact (Nat.minFac_prime (by omega)).two_le

/-- When n+1 ≥ 3 is prime, n is even (since the only even prime is 2). -/
theorem even_of_prime_succ (n : ℕ) (hn : 2 ≤ n) (hp : (n + 1).Prime) :
    Even n := by
  rw [Nat.even_iff]
  by_contra h
  have hmod : n % 2 = 1 := by omega
  have : (n + 1) % 2 = 0 := by omega
  have h2dvd : 2 ∣ (n + 1) := Nat.dvd_of_mod_eq_zero (by omega)
  have := hp.eq_one_or_self_of_dvd 2 h2dvd
  omega

/-- Even offsets k ≥ 2 never witness the generalised conjecture
(for d ≥ 1) when n is even: the least prime factor of the even
composite n + k is 2, but k^d ≥ 2. -/
theorem even_offset_excluded (n k d : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (hne : Even n) (hke : Even k) :
    ¬(∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ d < p) := by
  intro hlpf
  have heven : 2 ∣ (n + k) := by
    obtain ⟨a, ha⟩ := hne; obtain ⟨b, hb⟩ := hke
    exact ⟨a + b, by omega⟩
  have hmf : (n + k).minFac = 2 := minFac_of_even (n + k) (by omega) heven
  have hlpf2 : IsLeastPrimeFactor 2 (n + k) := by
    rw [← hmf]; exact minFac_is_lpf (n + k) (by omega)
  have hkd_ge : 2 ≤ k ^ d := by
    have h1 : k ^ 1 ≤ k ^ d := Nat.pow_le_pow_right (by omega : 0 < k) hd
    simp at h1; omega
  have hlt := hlpf 2 hlpf2
  omega

/-- When n+1 ≥ 3 is prime and d ≥ 1, any witness k ≥ 2 for the
generalised conjecture must be odd. Even k produces even composites
with minFac = 2, but k^d ≥ 2^d ≥ 2. -/
theorem witness_must_be_odd (n k d : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (hd : 1 ≤ d)
    (hp : (n + 1).Prime)
    (hlpf : ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ d < p) :
    ¬Even k := by
  intro hke
  exact even_offset_excluded n k d hn hk hd (even_of_prime_succ n hn hp) hke hlpf

/-- Generalises `hard_case_constraint` with the weaker hypothesis k ≥ 1.
Shows k^(2d) < n+k for any valid (n, k, d) triple, bounding the search
range at O(n^{1/(2d)}). -/
theorem general_constraint (n k d : ℕ) (_hk : 0 < k) (hm : ¬(n + k).Prime)
    (hm2 : 2 ≤ n + k) (hlpf : ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ d < p) :
    k ^ (2 * d) < n + k := by
  obtain ⟨p, hp, hpsq⟩ := lpf_le_sqrt (n + k) hm hm2
  have hkd := hlpf p hp
  have h2d : k ^ (2 * d) = k ^ d * k ^ d := by
    rw [show 2 * d = d + d from by omega, pow_add]
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.zero_le (k ^ d)) hkd
  rw [h2d]
  calc k ^ d * k ^ d
      _ < k ^ d * p := Nat.mul_lt_mul_of_pos_left hkd hkd_pos
      _ ≤ p * p := Nat.mul_le_mul_right p (le_of_lt hkd)
      _ ≤ n + k := hpsq

/- ## d=1 residue class resolution -/

/-- When n+1 = p is prime with p ≡ 2 (mod 3) and n+3 = p+2 is composite,
k = 3 witnesses the d=1 case. Since n is even (n+1 is odd prime), n+3
is odd. And p ≡ 2 (mod 3) gives (n+3) = p+2 ≡ 1 (mod 3), so 3 ∤ n+3.
Hence minFac(n+3) ≥ 5 > 3 = k^1. -/
theorem d1_at_2_mod_3 (n : ℕ) (hn : 4 ≤ n)
    (hp : (n + 1).Prime)
    (hmod : (n + 1) % 3 = 2)
    (hc : ¬(n + 3).Prime) :
    ∃ k : ℕ, 0 < k ∧ ¬(n + k).Prime ∧ 2 ≤ n + k ∧
      ∀ p : ℕ, IsLeastPrimeFactor p (n + k) → k ^ 1 < p := by
  refine ⟨3, by omega, hc, by omega, ?_⟩
  intro p ⟨hprime, hdvd, hmin⟩
  simp only [pow_one]
  -- n+3 is odd (n is even since n+1 is odd prime ≥ 5)
  have h2 : ¬(2 ∣ (n + 3)) := by
    intro ⟨m, hm⟩
    have hne := even_of_prime_succ n (by omega) hp
    obtain ⟨a, ha⟩ := hne
    omega
  -- (n+1) % 3 = 2 implies (n+3) % 3 = 1, so 3 ∤ n+3
  have h3 : ¬(3 ∣ (n + 3)) := by
    intro ⟨m, hm⟩
    omega
  -- p is prime, p ∣ n+3, but 2 ∤ n+3 and 3 ∤ n+3, so p ≠ 2, p ≠ 3
  have hp2 : p ≠ 2 := fun heq => h2 (heq ▸ hdvd)
  have hp3 : p ≠ 3 := fun heq => h3 (heq ▸ hdvd)
  -- p is prime and p ≠ 2, p ≠ 3, so p ≥ 5 > 3
  have := hprime.two_le
  omega

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
