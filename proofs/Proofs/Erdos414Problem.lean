/-
# Erdős Problem #414: Merging Orbits of h(n) = n + τ(n)

Let h(n) = n + τ(n) where τ(n) is the number of divisors of n.
Define h_k(n) by iterating: h_1(n) = h(n), h_k(n) = h(h_{k-1}(n)).
Is it true that for any m, n > 0, there exist i, j such that
h_i(m) = h_j(n)?

## Key Results

- Erdős and Graham believed the answer is YES
- The sequence h^k(n) is strictly increasing since τ(n) ≥ 1
- Related to OEIS A064491

## References

- Erdős–Graham [ErGr80], p. 82
- Related: Problems #412, #413 (similar iterated function questions)
- <https://erdosproblems.com/414>
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The function h(n) = n + τ(n), where τ(n) counts divisors. -/
def h (n : ℕ) : ℕ := n + n.divisors.card

/-- The orbit of n under iteration of h: {n, h(n), h(h(n)), ...}. -/
def hOrbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => h (hOrbit n k)

/- ## Basic Properties -/

/-- Every n ≥ 1 has at least one divisor (namely 1). -/
private theorem divisors_card_pos (n : ℕ) (hn : n ≥ 1) :
    n.divisors.card ≥ 1 := by
  have h1 : 1 ∈ n.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd n, by omega⟩
  exact Finset.card_pos.mpr ⟨1, h1⟩

/-- h(n) > n for all n ≥ 1 since τ(n) ≥ 1. -/
theorem h_strictly_increasing (n : ℕ) (hn : n ≥ 1) :
    h n > n := by
  unfold h
  have := divisors_card_pos n hn
  omega

/-- The orbit values are at least 1 when starting from n ≥ 1. -/
private theorem hOrbit_pos (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    hOrbit n k ≥ 1 := by
  induction k with
  | zero => simp [hOrbit]; exact hn
  | succ k ih =>
    simp [hOrbit]
    have := h_strictly_increasing (hOrbit n k) ih
    omega

/-- The orbit is strictly increasing: h^{k+1}(n) > h^k(n) for n ≥ 1. -/
theorem orbit_strictly_increasing (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    hOrbit n (k + 1) > hOrbit n k := by
  simp [hOrbit]
  exact h_strictly_increasing (hOrbit n k) (hOrbit_pos n hn k)

/-- h(n) ≤ 2n for all n ≥ 1 (since τ(n) ≤ n).
    Proof: divisors of n are in [1, n], so |divisors| ≤ |[1,n]| = n. -/
theorem h_upper (n : ℕ) (hn : n ≥ 1) :
    h n ≤ 2 * n := by
  simp only [h]
  suffices (Nat.divisors n).card ≤ n by omega
  calc (Nat.divisors n).card
      ≤ (Finset.Icc 1 n).card := by
        apply Finset.card_le_card
        intro d hd
        simp only [Finset.mem_Icc]
        have hdvd := (Nat.mem_divisors.mp hd).1
        exact ⟨Nat.pos_of_dvd_of_pos hdvd (by omega), Nat.le_of_dvd (by omega) hdvd⟩
    _ = n := by simp [Nat.card_Icc]

/-- For primes p, h(p) = p + 2 (since τ(p) = 2). -/
theorem h_prime (p : ℕ) (hp : p.Prime) :
    h p = p + 2 := by
  simp [h, Nat.Prime.divisors hp, Finset.card_pair (ne_of_lt hp.one_lt)]

/-- h(1) = 1 + τ(1) = 1 + 1 = 2. -/
theorem h_one : h 1 = 2 := by native_decide

/-- h(2) = 2 + τ(2) = 2 + 2 = 4. -/
theorem h_two : h 2 = 4 := by native_decide

/-- h(3) = 3 + τ(3) = 3 + 2 = 5. -/
theorem h_three : h 3 = 5 := by native_decide

/-- For n ≥ 2, τ(n) ≥ 2 (since 1 and n are distinct divisors), so h(n) ≥ n + 2. -/
theorem h_lower_bound_ge2 (n : ℕ) (hn : n ≥ 2) : h n ≥ n + 2 := by
  unfold h
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have hsub : {1, n} ⊆ n.divisors := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_pair (by omega : (1 : ℕ) ≠ n)] at this
  omega

/-- h(4) = 4 + τ(4) = 4 + 3 = 7. -/
theorem h_four : h 4 = 7 := by native_decide

/-- h(5) = 5 + τ(5) = 5 + 2 = 7. Both 4 and 5 map to 7 under h. -/
theorem h_five : h 5 = 7 := by native_decide

/- ## Main Conjecture -/

/-- **Erdős Problem #414** (OPEN): For any m, n ≥ 1, the orbits
    of m and n under h eventually merge: there exist i, j such
    that h^i(m) = h^j(n). -/
axiom erdos_414_conjecture :
  ∀ m n : ℕ, m ≥ 1 → n ≥ 1 → ∃ i j : ℕ, hOrbit m i = hOrbit n j

/-- Key lemma: once two orbits meet, they stay merged forever.
    If h^i(a) = h^j(b), then h^{i+d}(a) = h^{j+d}(b) for all d. -/
theorem hOrbit_continuation (a b : ℕ) (i j d : ℕ)
    (hmeet : hOrbit a i = hOrbit b j) :
    hOrbit a (i + d) = hOrbit b (j + d) := by
  induction d with
  | zero => simpa using hmeet
  | succ d ih => simp [hOrbit, ih]

/-- Equivalently: there is a single eventual orbit that all
    positive integers converge to.
    PROVED from erdos_414_conjecture via orbit continuation:
    take the orbit of 1 as the reference orbit S. -/
theorem single_eventual_orbit :
    ∃ S : ℕ → ℕ, ∀ n : ℕ, n ≥ 1 →
      ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
        ∃ j : ℕ, hOrbit n k = S j := by
  refine ⟨hOrbit 1, fun n hn => ?_⟩
  obtain ⟨i, j, hij⟩ := erdos_414_conjecture n 1 hn (by omega)
  exact ⟨i, fun k hk => ⟨j + (k - i), by
    have := hOrbit_continuation n 1 i j (k - i) hij
    rwa [Nat.add_sub_cancel' hk] at this⟩⟩

/- ## Orbit Examples -/

/-- Orbit of 1: 1 → 2 → 4 → 7 → 9 → 12 → 18 → 24 → 32 → ... -/
theorem orbit_1_start :
    hOrbit 1 0 = 1 ∧ hOrbit 1 1 = 2 ∧ hOrbit 1 2 = 4 ∧
    hOrbit 1 3 = 7 ∧ hOrbit 1 4 = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Orbit of 3: 3 → 5 → 7 → 9 → 12 → 18 → 24 → 32 → ...
    Merges with orbit of 1 at value 7 (h_3(1) = h_1(3) = 7). -/
theorem orbit_3_merges_with_1 :
    hOrbit 3 2 = hOrbit 1 3 := by  -- both equal 7
  native_decide

/- ## Growth Rate Analysis -/

/-- **τ(n) ≤ 2√n**: The divisor count is bounded by twice the integer square root.
    Proof: split divisors into small (d ≤ √n) and large (d > √n). Each set
    has ≤ √n elements: small ones by direct bound, large ones because the map
    d ↦ n/d injects large divisors into {1, ..., √n}. -/
theorem divisors_card_le_two_sqrt (n : ℕ) (hn : 1 ≤ n) :
    n.divisors.card ≤ 2 * n.sqrt := by
  -- Split divisors into small (≤ √n) and large (> √n)
  set small := n.divisors.filter (· ≤ n.sqrt) with small_def
  set large := n.divisors.filter (fun d => n.sqrt < d) with large_def
  -- Partition
  have h_union : n.divisors = small ∪ large := by
    ext d; simp [small_def, large_def]; omega
  have h_disj : Disjoint small large := by
    rw [Finset.disjoint_filter]
    intro d _ h1 h2; omega
  have h_card : n.divisors.card = small.card + large.card := by
    rw [h_union]; exact Finset.card_union_of_disjoint h_disj
  -- |small| ≤ √n: all elements in {1, ..., √n}
  have h_small : small.card ≤ n.sqrt := by
    calc small.card
        ≤ (Finset.Icc 1 n.sqrt).card := by
          apply Finset.card_le_card
          intro d hd
          simp [small_def] at hd
          simp only [Finset.mem_Icc]
          exact ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
      _ = n.sqrt := by simp [Nat.card_Icc]
  -- |large| ≤ √n: injection d ↦ n/d into {1, ..., √n}
  have h_large : large.card ≤ n.sqrt := by
    calc large.card
        ≤ (Finset.Icc 1 n.sqrt).card := by
          apply Finset.card_le_card_of_injOn (fun d => n / d)
          · -- n/d ∈ {1, ..., √n} for d ∈ large
            intro d hd
            simp [large_def] at hd
            obtain ⟨hd_mem, hd_gt⟩ := hd
            have hdvd := (Nat.mem_divisors.mp hd_mem).1
            simp only [Finset.mem_Icc]
            constructor
            · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
            · -- n / d ≤ √n because d > √n implies n / d < d and n/d · d = n
              -- Since d ≥ √n + 1 and (√n + 1)² > n, we get n / d < √n + 1
              have hlt : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt' n
              have hd_pos : 0 < d := by omega
              have : n / d < n.sqrt + 1 := by
                rw [Nat.div_lt_iff_lt_mul hd_pos]
                calc n < (n.sqrt + 1) * (n.sqrt + 1) := hlt
                  _ ≤ d * (n.sqrt + 1) := Nat.mul_le_mul_right _ (by omega)
              omega
          · -- Injectivity: if d₁, d₂ | n and n/d₁ = n/d₂, then d₁ = d₂
            intro d₁ hd₁ d₂ hd₂ heq
            simp [large_def] at hd₁ hd₂
            have hd1_dvd := (Nat.mem_divisors.mp hd₁.1).1
            have hd2_dvd := (Nat.mem_divisors.mp hd₂.1).1
            have h1 := Nat.div_mul_cancel hd1_dvd  -- n / d₁ * d₁ = n
            have h2 := Nat.div_mul_cancel hd2_dvd  -- n / d₂ * d₂ = n
            rw [heq] at h1
            have heqm : n / d₂ * d₁ = n / d₂ * d₂ := by linarith
            have hk_pos : 0 < n / d₂ :=
              Nat.div_pos (Nat.le_of_dvd (by omega) hd2_dvd) (by omega)
            exact mul_left_cancel₀ (by omega) heqm
      _ = n.sqrt := by simp [Nat.card_Icc]
  omega

/-- h(n) ≤ n + 2√n for all n ≥ 1 (tighter than h(n) ≤ 2n). -/
theorem h_upper_sqrt (n : ℕ) (hn : n ≥ 1) :
    h n ≤ n + 2 * n.sqrt := by
  simp only [h]
  have := divisors_card_le_two_sqrt n hn
  omega

/-- The orbit grows at least linearly: h^k(n) ≥ n + k for n ≥ 1.
    Proved by induction using h(m) > m for m ≥ 1. -/
theorem orbit_linear_lower (n : ℕ) (hn : n ≥ 1) (k : ℕ) :
    hOrbit n k ≥ n + k := by
  induction k with
  | zero => simp [hOrbit]
  | succ k ih =>
    simp [hOrbit]
    have hpos := hOrbit_pos n hn k
    have hgt := h_strictly_increasing (hOrbit n k) hpos
    omega

/-- For n ≥ 2, h^k(n) ≥ n + 2k (each step adds ≥ 2). Stronger than orbit_linear_lower. -/
theorem orbit_linear_lower_ge2 (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    hOrbit n k ≥ n + 2 * k := by
  induction k with
  | zero => simp [hOrbit]
  | succ k ih =>
    simp [hOrbit]
    have hge2 : hOrbit n k ≥ 2 := by omega
    have := h_lower_bound_ge2 (hOrbit n k) hge2
    omega

/-- Orbit of 5 merges with orbit of 1 at value 7: h(5) = 7 = h³(1). -/
theorem orbit_5_merges_with_1 : hOrbit 5 1 = hOrbit 1 3 := by native_decide

/-- More computed h values. -/
theorem h_six : h 6 = 10 := by native_decide
theorem h_seven : h 7 = 9 := by native_decide
theorem h_eight : h 8 = 12 := by native_decide
theorem h_nine : h 9 = 12 := by native_decide
theorem h_ten : h 10 = 14 := by native_decide

/-- Orbit of 2 merges with orbit of 1 at value 4: h(2) = 4 = h²(1). -/
theorem orbit_2_merges_with_1 : hOrbit 2 1 = hOrbit 1 2 := by native_decide

/-- Orbit of 4 merges with orbit of 1 at value 7: h(4) = 7 = h³(1). -/
theorem orbit_4_merges_with_1 : hOrbit 4 1 = hOrbit 1 3 := by native_decide

/-- Orbit of 6 merges with orbit of 1: h⁴(6) = 24 = h⁶(1). -/
theorem orbit_6_merges_with_1 : hOrbit 6 4 = hOrbit 1 7 := by native_decide

/-- Orbit of 7 merges with orbit of 1 at value 9: h(7) = 9 = h⁴(1). -/
theorem orbit_7_merges_with_1 : hOrbit 7 1 = hOrbit 1 4 := by native_decide

/-- Orbit of 8 merges with orbit of 1 at value 12: h(8) = 12 = h⁵(1). -/
theorem orbit_8_merges_with_1 : hOrbit 8 1 = hOrbit 1 5 := by native_decide

/-- Orbit of 9 merges with orbit of 1 at value 12: h(9) = 12 = h⁵(1). -/
theorem orbit_9_merges_with_1 : hOrbit 9 1 = hOrbit 1 5 := by native_decide

/-- Orbit of 10 merges with orbit of 1: h²(10) = 18 = h⁶(1). -/
theorem orbit_10_merges_with_1 : hOrbit 10 2 = hOrbit 1 6 := by native_decide

/-- Two orbits starting at m and n eventually merge (from the conjecture),
    so their distance eventually becomes 0. This is strictly stronger than
    "orbits get close".
    PROVED from erdos_414_conjecture: once orbits merge at h^i(m) = h^j(n),
    the distance is zero, which is ≤ D for any D.
    (Previously axiom with a soundness bug: the original < D formulation
    was False for D = 0. Fixed to use ≤ D and proved from conjecture.
    Axiom count reduced 2→1.) -/
theorem orbits_get_close :
    ∀ m n : ℕ, m ≥ 1 → n ≥ 1 →
      ∀ D : ℕ, ∃ i j : ℕ,
        |(hOrbit m i : ℤ) - (hOrbit n j : ℤ)| ≤ D := by
  intro m n hm hn D
  obtain ⟨i, j, hij⟩ := erdos_414_conjecture m n hm hn
  exact ⟨i, j, by rw [hij]; simp⟩
