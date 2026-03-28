/-
# Infinitely Many Wolstenholme Primes

Conjecture: infinitely many primes p satisfy C(2p-1,p-1) ≡ 1 (mod p⁴).

Only two such primes are known: 16843 (McIntosh, 1995) and 2124679
(McIntosh-Roettger, 2007). No others exist below 10⁹.

Heuristic: P(p is WP) ≈ 1/p for large p. Since Σ_{p prime} 1/p = ∞ (Euler),
one expects infinitely many WPs — though convergence is extremely slow.
The expected count below N is roughly ln(ln(N)).

This formalization:
1. States the infinitude conjecture and its negation
2. Proves the finite/infinite dichotomy (classical logic)
3. Establishes at least 2 WPs exist
4. Proves conditional bounds: if bounded, the largest is ≥ 2124679
5. Axiomatizes the McIntosh-Roettger computational search bound
6. States the Bernoulli number characterization p | B_{p-3}
7. Draws the parallel to Wieferich primes (2^{p-1} ≡ 1 mod p²)
-/
import Mathlib

namespace WolstenholmeInfinitude

open Nat

-- ============================================================
-- Efficient Binomial Coefficient Computation
-- ============================================================

/-- O(k) computation of C(n, k) via the multiplicative recurrence
    C(n, k+1) = C(n, k) · (n - k) / (k + 1).
    Lean's Nat.choose uses Pascal's triangle (exponential without memoization),
    making native_decide infeasible for large inputs. This version enables
    computational verification of specific binomial values. -/
def choose_fast : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 => choose_fast n k * (n - k) / (k + 1)

/-- choose_fast agrees with Nat.choose -/
theorem choose_fast_eq (n k : ℕ) : choose_fast n k = Nat.choose n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold choose_fast
    rw [ih, ← Nat.choose_succ_right_eq n k]
    exact Nat.mul_div_cancel _ (Nat.succ_pos k)

-- ============================================================
-- Section 1: Core Definitions
-- ============================================================

/-- The binomial coefficient C(2p-1, p-1) -/
def cb (p : ℕ) : ℕ := Nat.choose (2 * p - 1) (p - 1)

/-- A Wolstenholme prime: prime p with C(2p-1,p-1) ≡ 1 (mod p⁴) -/
def IsWP (p : ℕ) : Prop := Nat.Prime p ∧ cb p % (p ^ 4) = 1

-- ============================================================
-- Section 2: Known Wolstenholme Primes
-- ============================================================

/-- 16843 is prime -/
theorem prime_16843 : Nat.Prime 16843 := by native_decide

/-- 2124679 is prime -/
theorem prime_2124679 : Nat.Prime 2124679 := by native_decide

/-- C(33685, 16842) ≡ 1 (mod 16843⁴). Verified computationally via choose_fast.
    McIntosh, Acta Arith. 71 (1995), 381-389. -/
theorem cb_16843 : cb 16843 % (16843 ^ 4) = 1 := by
  unfold cb; rw [← choose_fast_eq]; native_decide

/-- C(4249357, 2124678) ≡ 1 (mod 2124679⁴). Axiomatized: binomial too large.
    McIntosh-Roettger, Math. Comp. 76 (2007), 2087-2094. -/
axiom cb_2124679 : cb 2124679 % (2124679 ^ 4) = 1

/-- 16843 is a Wolstenholme prime -/
theorem isWP_16843 : IsWP 16843 := ⟨prime_16843, cb_16843⟩

/-- 2124679 is a Wolstenholme prime -/
theorem isWP_2124679 : IsWP 2124679 := ⟨prime_2124679, cb_2124679⟩

/-- At least two distinct Wolstenholme primes exist -/
theorem at_least_two_wp : ∃ p q : ℕ, p ≠ q ∧ IsWP p ∧ IsWP q :=
  ⟨16843, 2124679, by omega, isWP_16843, isWP_2124679⟩

/-- The gap between the two known WPs exceeds 2 million -/
theorem wp_gap : 2124679 - 16843 = 2107836 := by norm_num

/-- The second known WP exceeds 126 times the first -/
theorem wp_ratio : 2124679 / 16843 = 126 := by norm_num

-- ============================================================
-- Section 3: The Infinitude Conjecture
-- ============================================================

/-- **The Infinitude Conjecture**: For every bound N, a WP exceeds it.

    Heuristic motivation: if P(p is WP) ≈ 1/p for large primes,
    the expected count below N is ≈ Σ_{p ≤ N, p prime} 1/p ≈ ln(ln N),
    which diverges — suggesting infinitely many WPs. -/
def InfinitelyManyWP : Prop := ∀ N : ℕ, ∃ p : ℕ, p > N ∧ IsWP p

/-- The complementary hypothesis: WPs have an upper bound -/
def BoundedWP : Prop := ∃ N : ℕ, ∀ p : ℕ, IsWP p → p ≤ N

/-- The two hypotheses are exactly complementary -/
theorem bounded_iff_not_infinite : BoundedWP ↔ ¬InfinitelyManyWP := by
  unfold BoundedWP InfinitelyManyWP
  constructor
  · rintro ⟨N, hN⟩ hinf
    obtain ⟨p, hpgt, hpwp⟩ := hinf N
    exact absurd (hN p hpwp) (by omega)
  · intro hni
    push_neg at hni
    obtain ⟨N, hN⟩ := hni
    exact ⟨N, fun p hp => by
      by_contra hgt
      exact hN p (by omega) hp⟩

/-- InfinitelyManyWP is equivalent to: no bound contains all WPs -/
theorem infinite_iff_no_bound : InfinitelyManyWP ↔ ¬BoundedWP := by
  rw [bounded_iff_not_infinite, not_not]

-- ============================================================
-- Section 4: Structural Properties
-- ============================================================

/-- Every Wolstenholme prime is ≥ 5 -/
theorem wp_ge_five (p : ℕ) (h : IsWP p) : p ≥ 5 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨hp, hcb⟩ := h
  have : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hcb (by native_decide)
  · exact absurd hcb (by native_decide)
  · exact absurd hp (by decide)

/-- Every Wolstenholme prime is odd -/
theorem wp_odd (p : ℕ) (h : IsWP p) : p % 2 = 1 := by
  have hge := wp_ge_five p h
  have hp := h.1
  have h2 : ¬(2 ∣ p) := by
    intro hdvd
    have := hp.eq_one_or_self_of_dvd 2 hdvd
    omega
  omega

-- ============================================================
-- Section 5: Consequences of Finiteness
-- ============================================================

/-- If WPs are bounded by N, then N ≥ 2124679 -/
theorem bounded_implies_large (N : ℕ) (hN : ∀ p, IsWP p → p ≤ N) :
    N ≥ 2124679 :=
  hN 2124679 isWP_2124679

/-- If WPs are bounded by N, then N ≥ 16843 -/
theorem bounded_implies_ge_first (N : ℕ) (hN : ∀ p, IsWP p → p ≤ N) :
    N ≥ 16843 :=
  hN 16843 isWP_16843

/-- Both known WPs lie below any bound -/
theorem known_wps_bounded (N : ℕ) (hN : ∀ p, IsWP p → p ≤ N) :
    16843 ≤ N ∧ 2124679 ≤ N :=
  ⟨bounded_implies_ge_first N hN, bounded_implies_large N hN⟩

-- ============================================================
-- Section 6: McIntosh-Roettger Computational Bound
-- ============================================================

/-- No WPs below 10⁹ other than 16843 and 2124679.
    McIntosh-Roettger, Math. Comp. 76 (2007), 2087-2094. -/
axiom no_wp_below_billion (p : ℕ) (h : IsWP p) (hlt : p < 10 ^ 9) :
  p = 16843 ∨ p = 2124679

/-- A third WP exceeds 10⁹ -/
theorem third_wp_large (p : ℕ) (h : IsWP p)
    (h1 : p ≠ 16843) (h2 : p ≠ 2124679) : p ≥ 10 ^ 9 := by
  by_contra hlt
  push_neg at hlt
  exact absurd (no_wp_below_billion p h hlt) (by tauto)

/-- Any WP other than 16843 is at least 2124679 -/
theorem wp_second_or_larger (p : ℕ) (h : IsWP p) (hne : p ≠ 16843) :
    p ≥ 2124679 := by
  by_contra hlt
  push_neg at hlt
  have hb := no_wp_below_billion p h (by omega)
  rcases hb with rfl | rfl
  · exact absurd rfl hne
  · omega

-- ============================================================
-- Section 7: Bernoulli Number Characterization
-- ============================================================

/-- **Bernoulli number characterization** (McIntosh 1995):
    A prime p ≥ 5 is a Wolstenholme prime iff p divides the
    numerator of the Bernoulli number B_{p-3}.

    This connects WPs to irregular prime theory: p is irregular
    iff p | B_{2k} for some 0 < 2k < p-1. The WP condition
    singles out the specific index p-3, which for odd p ≥ 5
    is even and ≥ 2. Thus every WP is an irregular prime. -/
axiom bernoulli_characterization (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) :
  IsWP p ↔ (p : ℤ) ∣ (bernoulli (p - 3)).num

-- ============================================================
-- Section 8: Parallel with Wieferich Primes
-- ============================================================

/-- A Wieferich prime: 2^{p-1} ≡ 1 (mod p²).
    Only two known: 1093 (Meissner 1913) and 3511 (Beeger 1922).
    Like WPs, conjectured to be infinite but unproved. -/
def IsWieferich (p : ℕ) : Prop := Nat.Prime p ∧ 2 ^ (p - 1) % (p ^ 2) = 1

/-- The Wieferich infinitude conjecture -/
def InfinitelyManyWieferich : Prop := ∀ N : ℕ, ∃ p : ℕ, p > N ∧ IsWieferich p

/-- 1093 is a Wieferich prime (Meissner 1913) -/
theorem isWieferich_1093 : IsWieferich 1093 :=
  ⟨by native_decide, by native_decide⟩

/-- 3511 is a Wieferich prime (Beeger 1922) -/
theorem isWieferich_3511 : IsWieferich 3511 :=
  ⟨by native_decide, by native_decide⟩

/-- At least two distinct Wieferich primes exist -/
theorem at_least_two_wieferich : ∃ p q : ℕ, p ≠ q ∧ IsWieferich p ∧ IsWieferich q :=
  ⟨1093, 3511, by omega, isWieferich_1093, isWieferich_3511⟩

/-- The structural parallel: both exceptional prime families have exactly
    two known examples and similar heuristic density (≈ 1/p).
    | Property           | Wolstenholme primes | Wieferich primes   |
    |---------------------|--------------------|--------------------|
    | Base congruence     | C(2p-1,p-1) ≡ 1 (mod p³) | 2^{p-1} ≡ 1 (mod p) |
    | Exceptional upgrade | mod p⁴             | mod p²             |
    | Known examples      | 16843, 2124679     | 1093, 3511         |
    | Search bound        | < 10⁹              | < 6.7 × 10¹⁵      |
    | Expected density    | ≈ 1/p              | ≈ 1/p              |  -/

-- ============================================================
-- Section 9: Connection to Wolstenholme's Theorem
-- ============================================================

/-- If n ≡ 1 (mod p⁴) then n ≡ 1 (mod p³), since p³ | p⁴ -/
theorem mod_pow4_implies_pow3 {n p : ℕ} (h : n % (p ^ 4) = 1) (hp : p ≥ 2) :
    n % (p ^ 3) = 1 := by
  have h34 : p ^ 3 ∣ p ^ 4 := ⟨p, by ring⟩
  rw [← Nat.mod_mod_of_dvd n h34, h]
  exact Nat.mod_eq_of_lt (by nlinarith [show p * p ≥ 4 from by nlinarith])

/-- Every WP satisfies the ordinary Wolstenholme theorem (mod p³) -/
theorem wp_satisfies_wolstenholme (p : ℕ) (h : IsWP p) :
    cb p % (p ^ 3) = 1 :=
  mod_pow4_implies_pow3 h.2 (by have := wp_ge_five p h; omega)

/-- Similarly, mod p⁴ implies mod p² (Babbage level) -/
theorem wp_satisfies_babbage (p : ℕ) (h : IsWP p) :
    cb p % (p ^ 2) = 1 := by
  have h23 : p ^ 2 ∣ p ^ 3 := ⟨p, by ring⟩
  rw [← Nat.mod_mod_of_dvd _ h23, wp_satisfies_wolstenholme p h]
  exact Nat.mod_eq_of_lt (by have := wp_ge_five p h; nlinarith)

end WolstenholmeInfinitude
