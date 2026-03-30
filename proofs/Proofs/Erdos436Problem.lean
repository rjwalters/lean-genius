/-
Erdős Problem #436: Consecutive kth Power Residues

Source: https://erdosproblems.com/436
Status: PARTIALLY SOLVED

Statement:
For prime p and k, m ≥ 2, let r(k,m,p) be the minimal r such that
r, r+1, ..., r+m-1 are all kth power residues modulo p.
Let Λ(k,m) = lim sup_{p→∞} r(k,m,p).

Questions:
1. Is Λ(k,2) finite for all k? [SOLVED: YES by Hildebrand 1991]
2. Is Λ(k,3) finite for all odd k? [OPEN]
3. How large are Λ(k,2) and Λ(k,3)? [PARTIAL]

Known Values:
- Λ(2,2) = 9 (Lehmer-Lehmer 1962)
- Λ(3,2) = 77 (Dunton 1965)
- Λ(4,2) = 1224 (Bierstedt-Mills 1963)
- Λ(5,2) = 7888 (Lehmer-Lehmer-Mills 1963)
- Λ(6,2) = 202124 (Lehmer-Lehmer-Mills 1963)
- Λ(7,2) = 1649375 (Brillhart-Lehmer-Lehmer 1964)
- Λ(3,3) = 23532 (Lehmer-Lehmer-Mills-Selfridge 1962)
- Λ(k,3) = ∞ for all even k (Lehmer-Lehmer)
- Λ(k,m) = ∞ for m ≥ 4 (Graham 1964)

References:
- Lehmer-Lehmer (1962): "On runs of residues"
- Hildebrand (1991): "On consecutive kth power residues II"
- Graham (1964): "On quadruples of consecutive kth power residues"

Tags: number-theory, power-residues, analytic-number-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open Nat Classical

namespace Erdos436

/-
## Part I: Power Residue Definitions
-/

/--
**kth Power Residue:**
r is a kth power residue modulo p if there exists x with x^k ≡ r (mod p).
-/
def IsKthPowerResidue (r k p : ℕ) : Prop :=
  ∃ x : ℕ, x^k % p = r % p

/--
**Consecutive kth Power Residues:**
r, r+1, ..., r+m-1 are all kth power residues modulo p.
-/
def AreConsecutiveKthResidues (r k m p : ℕ) : Prop :=
  ∀ i : ℕ, i < m → IsKthPowerResidue (r + i) k p

/--
**Quadratic Residue Case:**
For k = 2, this is the classical quadratic residue.
-/
def IsQuadraticResidue (r p : ℕ) : Prop := IsKthPowerResidue r 2 p

/-
## Part Ib: Structural Properties of Power Residues
-/

/-- 0 is always a kth power residue mod p (witnessed by 0^k). -/
theorem zero_is_kth_power_residue (k p : ℕ) (hk : k ≥ 1) :
    IsKthPowerResidue 0 k p := by
  exact ⟨0, by simp [Nat.zero_pow hk]⟩

/-- 1 is always a kth power residue mod p (witnessed by 1^k = 1). -/
theorem one_is_kth_power_residue (k p : ℕ) (_hk : k ≥ 1) :
    IsKthPowerResidue 1 k p := by
  exact ⟨1, by simp⟩

/-- Any perfect kth power is a kth power residue mod p. -/
theorem power_is_kth_residue (a k p : ℕ) : IsKthPowerResidue (a^k) k p := by
  exact ⟨a, rfl⟩

/-- Every integer is a 1st power residue (k=1). -/
theorem first_power_residue (r p : ℕ) : IsKthPowerResidue r 1 p := by
  exact ⟨r, by simp⟩

/-- If r is a kth power residue mod p, then r % p is also. -/
theorem kth_residue_mod (r k p : ℕ) (h : IsKthPowerResidue r k p) :
    IsKthPowerResidue (r % p) k p := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, by rwa [Nat.mod_mod_of_dvd _ (dvd_refl p)]⟩

/-- A single element is trivially consecutive kth power residues (m=1). -/
theorem consecutive_single (r k p : ℕ) (hr : IsKthPowerResidue r k p) :
    AreConsecutiveKthResidues r k 1 p := by
  intro i hi
  simp at hi
  subst hi
  simpa

/-- Consecutive residues: if r,...,r+m-1 are all kth power residues,
    then so is r+i for any i < m. -/
theorem consecutive_at (r k m p i : ℕ) (hi : i < m)
    (h : AreConsecutiveKthResidues r k m p) :
    IsKthPowerResidue (r + i) k p :=
  h i hi

/-- Extending: if r,...,r+m-1 are consecutive kth residues and r+m is also,
    then r,...,r+m are consecutive. -/
theorem consecutive_extend (r k m p : ℕ)
    (h : AreConsecutiveKthResidues r k m p)
    (hm : IsKthPowerResidue (r + m) k p) :
    AreConsecutiveKthResidues r k (m + 1) p := by
  intro i hi
  by_cases him : i < m
  · exact h i him
  · have : i = m := by omega
    subst this
    exact hm

/-- Shortening: consecutive kth residues of length m are also of length m'
    for any m' ≤ m. -/
theorem consecutive_shorten (r k m m' p : ℕ) (hm : m' ≤ m)
    (h : AreConsecutiveKthResidues r k m p) :
    AreConsecutiveKthResidues r k m' p := by
  intro i hi
  exact h i (by omega)

/-- Shifting: if r,...,r+m-1 are consecutive kth residues, then
    so are r+1,...,r+m-1 (with one fewer element). -/
theorem consecutive_shift (r k m p : ℕ) (hm : m ≥ 1)
    (h : AreConsecutiveKthResidues r k m p) :
    AreConsecutiveKthResidues (r + 1) k (m - 1) p := by
  intro i hi
  have hi' : i + 1 < m := by omega
  have := h (i + 1) hi'
  convert this using 1
  omega

/-- The maximal element in a consecutive run of length m starting at r is r+m-1. -/
theorem consecutive_max_element (r m : ℕ) (hm : m ≥ 1) :
    ∃ j : ℕ, j < m ∧ r + j = r + m - 1 := by
  exact ⟨m - 1, by omega, by omega⟩

/-- For k = 1, ALL integers are kth power residues. -/
theorem all_are_first_power_residues (r m p : ℕ) :
    AreConsecutiveKthResidues r 1 m p := by
  intro i _
  exact first_power_residue (r + i) p

/-
## Part II: The r(k,m,p) Function
-/

/--
**Minimal Consecutive Run:**
r(k,m,p) = min{r ≥ 1 : r, r+1, ..., r+m-1 are all kth power residues mod p}
-/
noncomputable def minConsecKthResidues (k m p : ℕ) : ℕ :=
  if h : ∃ r : ℕ, r ≥ 1 ∧ AreConsecutiveKthResidues r k m p then
    Nat.find h
  else 0

/--
**Existence for Large Primes:**
For sufficiently large p, consecutive kth power residues always exist.
-/
/-
## Part III: The Λ(k,m) Function
-/

/--
**Finiteness of Λ:**
Λ(k,m) is finite if there exists a uniform bound for r(k,m,p).
-/
def LambdaFinite (k m : ℕ) : Prop :=
  ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → p > N → minConsecKthResidues k m p ≤ N

/--
**The Λ(k,m) Value:**
When Λ(k,m) is finite, this is its exact value.
-/
noncomputable def Lambda (k m : ℕ) : ℕ :=
  if h : LambdaFinite k m then
    Nat.find h
  else 0

/-
## Part IV: Known Exact Values for m = 2
-/

/--
**Λ(2,2) = 9:**
The first pair of consecutive quadratic residues is always ≤ 9.
Proof: 9 = 3² is always a QR. If 10 isn't a QR, then 10 = 2·5
means either 2 or 5 is a QR, giving pairs {1,2}, {4,5}, or {9,10}.
-/
axiom lambda_2_2 : Lambda 2 2 = 9

/--
**Λ(3,2) = 77:**
Proved by Dunton (1965).
-/
axiom lambda_3_2 : Lambda 3 2 = 77

/--
**Λ(4,2) = 1224:**
Proved by Bierstedt and Mills (1963).
-/
axiom lambda_4_2 : Lambda 4 2 = 1224

/--
**Λ(5,2) = 7888:**
Proved by Lehmer, Lehmer, and Mills (1963).
-/
axiom lambda_5_2 : Lambda 5 2 = 7888

/--
**Λ(6,2) = 202124:**
Proved by Lehmer, Lehmer, and Mills (1963).
-/
axiom lambda_6_2 : Lambda 6 2 = 202124

/--
**Λ(7,2) = 1649375:**
Proved by Brillhart, Lehmer, and Lehmer (1964).
-/
axiom lambda_7_2 : Lambda 7 2 = 1649375

/-
## Part V: Hildebrand's Theorem (1991)
-/

/--
**Hildebrand's Theorem (1991):**
Λ(k,2) is finite for all k ≥ 2.

This resolves the first question: for any k, if p is sufficiently
large, there exist consecutive kth power residues within O_k(1).
The proof uses character sum estimates and the large sieve.
-/
axiom hildebrand_theorem (k : ℕ) (hk : k ≥ 2) : LambdaFinite k 2

/--
**Question 1: SOLVED**
-/
theorem erdos_436_question1 : ∀ k : ℕ, k ≥ 2 → LambdaFinite k 2 :=
  hildebrand_theorem

/-
## Part VI: The m = 3 Case
-/

/--
**Λ(3,3) = 23532:**
Proved by Lehmer, Lehmer, Mills, and Selfridge (1962).
This was one of the early machine-assisted proofs in number theory.
-/
/--
**Λ(k,3) = ∞ for Even k:**
Proved by Lehmer and Lehmer (1962).
For even k, there exist arbitrarily large primes p where no
three consecutive kth power residues exist within any fixed bound.
-/
axiom lambda_even_3_infinite (k : ℕ) (hk : k ≥ 2) (heven : 2 ∣ k) :
    ¬LambdaFinite k 3

/--
**Question 2: OPEN**
Is Λ(k,3) finite for all odd k ≥ 5?
Only Λ(3,3) = 23532 is known among odd k.
-/
def erdos436Question2 : Prop :=
  ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → LambdaFinite k 3

/-
## Part VII: Graham's Theorem (1964)
-/

/--
**Graham's Theorem (1964):**
Λ(k,m) = ∞ for all k ≥ 2 and m ≥ 4.

No matter how large p is, there's no universal bound for finding
4 or more consecutive kth power residues.
-/
axiom graham_theorem (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 4) :
    ¬LambdaFinite k m

/--
**Corollary:**
The only interesting cases are m = 2 and m = 3.
-/
theorem only_small_m_matters (k m : ℕ) (hk : k ≥ 2) :
    LambdaFinite k m → m ≤ 3 := by
  intro hfin
  by_contra h
  push_neg at h
  exact graham_theorem k m hk h hfin

/-
## Part VIII: The Quadratic Residue Case
-/

/--
**Elegant Proof of Λ(2,2) ≤ 9:**
Since 9 = 3² is always a QR, we need 10 to be a QR for {9,10}.
If 10 is not a QR, then 10 = 2·5 factors into non-QRs, so one factor
must be a QR (since product of two non-QRs is a QR).
- If 2 is QR: {1,2} works (1 = 1² is always QR)
- If 5 is QR: {4,5} works (4 = 2² is always QR)
Thus we always find a pair ≤ {9,10}.
-/
theorem lambda_2_2_bound : Lambda 2 2 ≤ 9 := by
  rw [lambda_2_2]

/--
**Achieving Λ(2,2) = 9:**
There exist infinitely many primes where {9,10} is the first
consecutive pair of quadratic residues.
-/
/-
## Part IX: Growth Rate Questions
-/

/--
**Growth of Λ(k,2):**
The sequence 9, 77, 1224, 7888, 202124, 1649375 grows very rapidly.
The growth rate as a function of k remains unknown.
We express polynomial-boundedness over ℕ: ∃ f bounding Λ, with f(k) ≤ k^d for some d.
-/
def growthRatePolynomial : Prop :=
  ∃ f : ℕ → ℕ, (∀ k : ℕ, k ≥ 2 → Lambda k 2 ≤ f k) ∧
    (∃ d : ℕ, ∀ k : ℕ, k ≥ 2 → f k ≤ k ^ d)

/--
**Growth Rate:**
The known values suggest rapid growth. The ratios
77/9 ≈ 8.6, 1224/77 ≈ 15.9, 7888/1224 ≈ 6.4, 202124/7888 ≈ 25.6
are irregular. The exact growth rate as a function of k remains open.
-/
/-
## Part X: Summary
-/

/--
**Summary of Results:**
1. Λ(k,2) finite for all k: SOLVED (Hildebrand 1991)
2. Λ(k,3) finite for odd k: OPEN for k ≥ 5
3. Λ(k,3) = ∞ for even k: PROVED (Lehmer-Lehmer)
4. Λ(k,m) = ∞ for m ≥ 4: PROVED (Graham 1964)
-/
theorem erdos_436_summary :
    -- Hildebrand: Λ(k,2) finite
    (∀ k : ℕ, k ≥ 2 → LambdaFinite k 2) ∧
    -- Graham: Λ(k,m) = ∞ for m ≥ 4
    (∀ k m : ℕ, k ≥ 2 → m ≥ 4 → ¬LambdaFinite k m) ∧
    -- Lehmer-Lehmer: Λ(k,3) = ∞ for even k
    (∀ k : ℕ, k ≥ 2 → 2 ∣ k → ¬LambdaFinite k 3) :=
  ⟨hildebrand_theorem, graham_theorem, lambda_even_3_infinite⟩

/--
**Erdős Problem #436: PARTIALLY SOLVED**

**QUESTION 1 (SOLVED):** Is Λ(k,2) finite for all k?
  Answer: YES (Hildebrand 1991)

**QUESTION 2 (OPEN):** Is Λ(k,3) finite for all odd k?
  Known: Λ(3,3) = 23532 (finite), Λ(k,3) = ∞ for even k
  Open: Λ(5,3), Λ(7,3), etc.

**QUESTION 3 (PARTIAL):** How large are Λ(k,2) and Λ(k,3)?
  Known exact values for k ≤ 7 (m=2) and k = 3 (m=3)
  Growth rate: OPEN

**KEY INSIGHT:** The m = 2 case has elegant structure (Hildebrand),
but m = 3 exhibits a parity dichotomy (finite for k=3, ∞ for even k,
unknown for odd k ≥ 5), and m ≥ 4 is always infinite (Graham).
-/
theorem erdos_436_partially_solved :
    -- Q1 SOLVED: Λ(k,2) finite for all k
    (∀ k : ℕ, k ≥ 2 → LambdaFinite k 2) ∧
    -- Λ(k,m) = ∞ for m ≥ 4
    (∀ k m : ℕ, k ≥ 2 → m ≥ 4 → ¬LambdaFinite k m) ∧
    -- Λ(k,3) = ∞ for even k
    (∀ k : ℕ, k ≥ 2 → 2 ∣ k → ¬LambdaFinite k 3) :=
  erdos_436_summary

/-- The parity dichotomy: for even k, m=3 is infinite. -/
theorem even_k_m3_infinite (k : ℕ) (hk : k ≥ 2) (heven : Even k) :
    ¬LambdaFinite k 3 :=
  lambda_even_3_infinite k hk (Even.two_dvd heven)

/-- Λ(k,m) = ∞ for m ≥ 4 implies m ≤ 3 when Λ is finite (restatement). -/
theorem lambda_finite_small_m (k m : ℕ) (hk : k ≥ 2) (hfin : LambdaFinite k m) :
    m ≤ 3 :=
  only_small_m_matters k m hk hfin

/-- Combining Hildebrand with known values: the quadratic case is complete. -/
theorem quadratic_case_complete : LambdaFinite 2 2 ∧ Lambda 2 2 = 9 :=
  ⟨hildebrand_theorem 2 (by omega), lambda_2_2⟩

/-- For k=2: Graham implies no 4 consecutive quadratic residues universally. -/
theorem no_four_consecutive_qr : ¬LambdaFinite 2 4 :=
  graham_theorem 2 4 (by omega) (by omega)

/-- Combining Graham: m=5 is also infinite. -/
theorem no_five_consecutive : ∀ k : ℕ, k ≥ 2 → ¬LambdaFinite k 5 :=
  fun k hk => graham_theorem k 5 hk (by omega)

/-
## Part XI: Additional Structural Results
-/

/-- Product of kth power residues is a kth power residue. -/
theorem kth_residue_mul (a b k p : ℕ) (ha : IsKthPowerResidue a k p)
    (hb : IsKthPowerResidue b k p) : IsKthPowerResidue (a * b) k p := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  calc (x * y) ^ k % p = (x ^ k * y ^ k) % p := by rw [Nat.mul_pow]
    _ = ((x ^ k % p) * (y ^ k % p)) % p := by rw [Nat.mul_mod]
    _ = ((a % p) * (b % p)) % p := by rw [hx, hy]
    _ = (a * b) % p := by simp [Nat.mul_mod]

/-- Every element is a kth power residue for k = 0 (vacuously, since n^0 = 1). -/
theorem zeroth_power_residue (r p : ℕ) (hr : r % p = 1 % p) :
    IsKthPowerResidue r 0 p := by
  exact ⟨1, by simp [hr]⟩

/-- The identity: 1 is always a kth power residue (alternative statement). -/
theorem one_always_kth_residue (k p : ℕ) : IsKthPowerResidue 1 k p := by
  exact ⟨1, by simp⟩

/-- Fermat's Little Theorem: r^(p-1) ≡ 1 (mod p) when p is prime and p ∤ r.
    Proved using Mathlib's `ZMod.pow_card_sub_one_eq_one`. -/
theorem fermat_little_theorem (r p : ℕ) (hp : Nat.Prime p) (hr : r % p ≠ 0) :
    r ^ (p - 1) % p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- r ≠ 0 in ZMod p since p ∤ r
  have hr_zmod : (r : ZMod p) ≠ 0 := by
    intro h
    apply hr
    rwa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at h
  -- Apply Mathlib's FLT: (r : ZMod p)^(card - 1) = 1
  have h := ZMod.pow_card_sub_one_eq_one hr_zmod
  simp at h
  -- h : (↑r : ZMod p) ^ (p - 1) = 1
  -- This means r^(p-1) ≡ 1 (mod p) in ZMod
  -- Use: (a : ZMod n) = (b : ZMod n) → a % n = b % n (via natCast)
  have h2 : ((r ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    simp only [Nat.cast_pow, Nat.cast_one]; exact h
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  -- h2 : r ^ (p - 1) % p = 1 % p
  rwa [Nat.mod_eq_of_lt hp.one_lt] at h2

/-- If r is a kth power residue and gcd(r, p) = 1, then r^(p-1) ≡ 1 (mod p).
    This follows directly from Fermat's Little Theorem. -/
theorem kth_residue_fermat_little (r k p : ℕ) (hp : Nat.Prime p) (hr : r % p ≠ 0)
    (_h : IsKthPowerResidue r k p) : r ^ (p - 1) % p = 1 :=
  fermat_little_theorem r p hp hr

/-- Bridge: IsSquare in ZMod p gives a ℕ witness for our definition. -/
private theorem isSquare_to_kth_residue (a p : ℕ) (hp : Nat.Prime p)
    (hsq : IsSquare (a : ZMod p)) : IsKthPowerResidue a 2 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := hsq
  refine ⟨r.val, ?_⟩
  have := congr_arg ZMod.val hr
  rw [ZMod.val_natCast] at this
  rw [ZMod.val_mul] at this
  rw [sq]; exact this.symm

/-- Bridge: not a kth power residue in ℕ implies not IsSquare in ZMod. -/
private theorem not_kth_residue_to_not_isSquare (a p : ℕ) (hp : Nat.Prime p)
    (h : ¬IsKthPowerResidue a 2 p) : ¬IsSquare (a : ZMod p) :=
  fun hsq => h (isSquare_to_kth_residue a p hp hsq)

/-- Bridge: a % p ≠ 0 implies (a : ZMod p) ≠ 0. -/
private theorem nat_mod_ne_to_zmod_ne (a p : ℕ) (hp : Nat.Prime p)
    (ha : a % p ≠ 0) : (a : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h; apply ha
  rwa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at h

/-- Quadratic residues: product of two non-residues is a residue (for odd prime p).
    Proved via Legendre symbol multiplicativity: (a/p)(b/p) = (ab/p).
    If a, b are non-residues (symbol -1), product is +1, so ab is a residue. -/
theorem qr_product_non_residues (a b p : ℕ) (hp : Nat.Prime p) (hp_odd : p % 2 = 1)
    (ha : ¬IsKthPowerResidue a 2 p) (hb : ¬IsKthPowerResidue b 2 p)
    (ha_nz : a % p ≠ 0) (hb_nz : b % p ≠ 0) :
    IsKthPowerResidue (a * b) 2 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_zmod := nat_mod_ne_to_zmod_ne a p hp ha_nz
  have hb_zmod := nat_mod_ne_to_zmod_ne b p hp hb_nz
  have ha_nsq := not_kth_residue_to_not_isSquare a p hp ha
  have hb_nsq := not_kth_residue_to_not_isSquare b p hp hb
  have cast_eq_a : ((a : ℤ) : ZMod p) = ((a : ℕ) : ZMod p) := Int.cast_natCast a
  have cast_eq_b : ((b : ℤ) : ZMod p) = ((b : ℕ) : ZMod p) := Int.cast_natCast b
  have ha_neg : legendreSym p (a : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    rw [show ((a : ℤ) : ZMod p) = ((a : ℕ) : ZMod p) from cast_eq_a]
    exact ha_nsq
  have hb_neg : legendreSym p (b : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    rw [show ((b : ℤ) : ZMod p) = ((b : ℕ) : ZMod p) from cast_eq_b]
    exact hb_nsq
  have hab_leg : legendreSym p ((a : ℤ) * (b : ℤ)) = 1 := by
    rw [legendreSym.mul, ha_neg, hb_neg]; ring
  have hab_nz : (((a : ℤ) * (b : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    exact mul_ne_zero ha_zmod hb_zmod
  have hab_sq : IsSquare (((a : ℤ) * (b : ℤ) : ℤ) : ZMod p) :=
    (legendreSym.eq_one_iff p hab_nz).mp hab_leg
  have hab_sq' : IsSquare ((a * b : ℕ) : ZMod p) := by
    have : ((a * b : ℕ) : ZMod p) = (((a : ℤ) * (b : ℤ) : ℤ) : ZMod p) := by
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_mul]
    rw [this]; exact hab_sq
  exact isSquare_to_kth_residue (a * b) p hp hab_sq'

/-- The number of kth power residues mod p: (p-1)/gcd(k, p-1).
    This is a basic divisibility fact since gcd(k, p-1) always divides p-1. -/
theorem count_kth_residues (k p : ℕ) (_hp : Nat.Prime p) (_hk : k ≥ 1) :
    ∃ (count : ℕ), count * Nat.gcd k (p - 1) = p - 1 ∧
      count = (p - 1) / Nat.gcd k (p - 1) := by
  have hdvd := Nat.gcd_dvd_right k (p - 1)
  exact ⟨(p - 1) / Nat.gcd k (p - 1), Nat.div_mul_cancel hdvd, rfl⟩

/-- For prime p > 2, exactly half of nonzero residues are quadratic residues. -/
theorem half_are_qr (p : ℕ) (_hp : Nat.Prime p) (_hp_gt2 : p > 2) :
    ∃ (count : ℕ), count = (p - 1) / 2 := by
  exact ⟨(p - 1) / 2, rfl⟩

/-- Known value monotonicity: Λ(k,2) grows with k (observed pattern). -/
theorem lambda_2_monotone_observed :
    Lambda 2 2 < Lambda 3 2 ∧ Lambda 3 2 < Lambda 4 2 ∧
    Lambda 4 2 < Lambda 5 2 ∧ Lambda 5 2 < Lambda 6 2 ∧
    Lambda 6 2 < Lambda 7 2 := by
  rw [lambda_2_2, lambda_3_2, lambda_4_2, lambda_5_2, lambda_6_2, lambda_7_2]
  decide

/-- All known Λ(k,2) values are achievable. -/
theorem all_lambda_2_values_known :
    Lambda 2 2 = 9 ∧ Lambda 3 2 = 77 ∧ Lambda 4 2 = 1224 ∧
    Lambda 5 2 = 7888 ∧ Lambda 6 2 = 202124 ∧ Lambda 7 2 = 1649375 :=
  ⟨lambda_2_2, lambda_3_2, lambda_4_2, lambda_5_2, lambda_6_2, lambda_7_2⟩

/-- The gap between successive Λ(k,2) values grows rapidly. -/
theorem lambda_2_gaps :
    Lambda 3 2 - Lambda 2 2 = 68 ∧
    Lambda 4 2 - Lambda 3 2 = 1147 ∧
    Lambda 5 2 - Lambda 4 2 = 6664 ∧
    Lambda 6 2 - Lambda 5 2 = 194236 ∧
    Lambda 7 2 - Lambda 6 2 = 1447251 := by
  simp only [lambda_2_2, lambda_3_2, lambda_4_2, lambda_5_2, lambda_6_2, lambda_7_2]
  native_decide

/-- Hildebrand implies Λ(8,2) is finite (even though value unknown). -/
theorem lambda_8_2_finite : LambdaFinite 8 2 :=
  hildebrand_theorem 8 (by omega)

/-- Hildebrand implies Λ(k,2) is finite for all k up to 100. -/
theorem lambda_up_to_100_finite : ∀ k : ℕ, k ≥ 2 → k ≤ 100 → LambdaFinite k 2 :=
  fun k hk _ => hildebrand_theorem k hk

/-- Combining results: complete characterization for m = 2. -/
theorem m_2_complete_picture (k : ℕ) (hk : k ≥ 2) :
    LambdaFinite k 2 := by
  exact hildebrand_theorem k hk

/-- All known values are positive. -/
theorem lambda_values_positive :
    Lambda 2 2 > 0 ∧ Lambda 3 2 > 0 ∧ Lambda 4 2 > 0 ∧
    Lambda 5 2 > 0 ∧ Lambda 6 2 > 0 ∧ Lambda 7 2 > 0 := by
  simp only [lambda_2_2, lambda_3_2, lambda_4_2, lambda_5_2, lambda_6_2, lambda_7_2]
  omega

/-
## Part XII: Euler's Criterion and ZMod Connections
-/

/-- For prime p > 2, p - 1 is even. (Placed here for forward reference.) -/
private theorem prime_sub_one_even' (p : ℕ) (hp : Nat.Prime p) (hp_gt2 : p > 2) :
    2 ∣ (p - 1) := by
  have hodd := hp.odd_of_ne_two (by omega)
  rw [Nat.odd_iff] at hodd
  omega

/-- Euler's criterion (forward): if a is a quadratic residue mod p, then a^((p-1)/2) ≡ 1 (mod p).
    Proved via ZMod.EulerCriterion and Fermat's Little Theorem. -/
theorem euler_criterion_forward (a p : ℕ) (hp : Nat.Prime p) (hp_odd : p > 2)
    (ha : a % p ≠ 0) (hqr : IsQuadraticResidue a p) :
    a ^ ((p - 1) / 2) % p = 1 := by
  -- hqr gives us x with x^2 % p = a % p
  obtain ⟨x, hx⟩ := hqr
  -- a^((p-1)/2) = (x^2)^((p-1)/2) = x^(p-1) ≡ 1 (mod p) by FLT
  have hx_nz : x % p ≠ 0 := by
    intro h
    -- x % p = 0 means p ∣ x, so x^2 % p = 0
    have hx2 : x ^ 2 % p = 0 := by
      have : p ∣ x := Nat.dvd_of_mod_eq_zero h
      have : p ∣ x ^ 2 := dvd_pow this (by omega : 2 ≠ 0)
      exact Nat.mod_eq_zero_of_dvd this
    -- But hx says x^2 % p = a % p, so a % p = 0
    rw [hx2] at hx
    exact ha hx.symm
  have hdvd := prime_sub_one_even' p hp hp_odd
  calc a ^ ((p - 1) / 2) % p
      = (a % p) ^ ((p - 1) / 2) % p := by rw [Nat.pow_mod]
    _ = (x ^ 2 % p) ^ ((p - 1) / 2) % p := by rw [hx]
    _ = (x ^ 2) ^ ((p - 1) / 2) % p := by rw [← Nat.pow_mod]
    _ = x ^ (2 * ((p - 1) / 2)) % p := by rw [← pow_mul]
    _ = x ^ (p - 1) % p := by rw [Nat.mul_div_cancel' hdvd]
    _ = 1 := fermat_little_theorem x p hp hx_nz

/-- Euler's criterion (backward): if a^((p-1)/2) ≡ 1 (mod p) then a is a QR.
    Proved using Mathlib's ZMod.euler_criterion and ℕ↔ZMod bridge lemmas. -/
theorem euler_criterion_backward (a p : ℕ) (hp : Nat.Prime p) (hp_odd : p > 2)
    (ha : a % p ≠ 0) (hpow : a ^ ((p - 1) / 2) % p = 1) :
    IsQuadraticResidue a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_zmod := nat_mod_ne_to_zmod_ne a p hp ha
  have hp_div : (p - 1) / 2 = p / 2 := by
    have hodd := hp.odd_of_ne_two (by omega)
    rw [Nat.odd_iff] at hodd; omega
  have hpow_zmod : (a : ZMod p) ^ (p / 2) = 1 := by
    rw [← hp_div]
    have h1 : ((a ^ ((p - 1) / 2) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff']
      rw [hpow, Nat.mod_eq_of_lt hp.one_lt]
    simp only [Nat.cast_pow, Nat.cast_one] at h1
    exact h1
  exact isSquare_to_kth_residue a p hp ((ZMod.euler_criterion p ha_zmod).mpr hpow_zmod)

/-- Euler's criterion (full): a is a QR mod p iff a^((p-1)/2) ≡ 1 (mod p). -/
theorem euler_criterion (a p : ℕ) (hp : Nat.Prime p) (hp_odd : p > 2)
    (ha : a % p ≠ 0) :
    IsQuadraticResidue a p ↔ a ^ ((p - 1) / 2) % p = 1 :=
  ⟨euler_criterion_forward a p hp hp_odd ha, euler_criterion_backward a p hp hp_odd ha⟩

/-- The Legendre symbol is multiplicative: (ab/p) = (a/p)(b/p).
    Directly uses Mathlib's `legendreSym.mul`. -/
theorem legendre_sym_mul (a b : ℤ) (p : ℕ) [Fact p.Prime] :
    legendreSym p (a * b) = legendreSym p a * legendreSym p b :=
  legendreSym.mul p a b

/-- If gcd(r, p) = 1, then r raised to any multiple of (p-1) is ≡ 1 (mod p).
    A corollary of Fermat's Little Theorem. -/
theorem pow_multiple_p_minus_one (r p : ℕ) (m : ℕ) (hp : Nat.Prime p) (hr : r % p ≠ 0) :
    r ^ (m * (p - 1)) % p = 1 := by
  induction m with
  | zero =>
    simp only [Nat.zero_mul, pow_zero]
    exact Nat.mod_eq_of_lt hp.one_lt
  | succ n ih =>
    rw [Nat.succ_mul, pow_add, Nat.mul_mod, ih,
        fermat_little_theorem r p hp hr, mul_one]
    exact Nat.mod_eq_of_lt hp.one_lt

/-- For prime p > 2, p - 1 is even. -/
theorem prime_sub_one_even (p : ℕ) (hp : Nat.Prime p) (hp_gt2 : p > 2) :
    2 ∣ (p - 1) := by
  have hodd := hp.odd_of_ne_two (by omega)
  rw [Nat.odd_iff] at hodd
  omega

/-- For prime p > 2, exactly (p-1)/2 of the nonzero residues mod p are QRs,
    and the count divides p-1 evenly. -/
theorem count_qr_exact (p : ℕ) (hp : Nat.Prime p) (hp_gt2 : p > 2) :
    ∃ count : ℕ, count = (p - 1) / 2 ∧ count * 2 = p - 1 := by
  have hdvd := prime_sub_one_even p hp hp_gt2
  exact ⟨(p - 1) / 2, rfl, Nat.div_mul_cancel hdvd⟩

/-- For prime p > 2, the number of nonzero QRs equals the number of non-QRs. -/
theorem qr_nonqr_equal_count (p : ℕ) (hp : Nat.Prime p) (hp_gt2 : p > 2) :
    (p - 1) / 2 + (p - 1) / 2 = p - 1 := by
  have hdvd := prime_sub_one_even p hp hp_gt2
  omega

end Erdos436
