import Mathlib

/-!
# GCD-LCM Distributive Law for Euclidean Domains

## Research Problem: chinese-remainder-non-coprime-oq-03-oq-02

**Open Question**: Formalize the GCD-LCM distributive law as a standalone theorem
for Euclidean Domains. The law states:

  `gcd(lcm(a,b), c) ∼ lcm(gcd(a,c), gcd(b,c))`

where `∼` denotes *Associated* (equal up to a unit factor) in a general Euclidean
domain, or exact equality in normalized domains like ℕ.

## The Two Equivalent Forms

GCD and LCM distribute over each other in two dual forms:
1. `gcd(lcm(a,b), c) = lcm(gcd(a,c), gcd(b,c))`   (gcd distributes over lcm)
2. `lcm(gcd(a,b), c) = gcd(lcm(a,c), lcm(b,c))`   (lcm distributes over gcd)

This file formalizes form (1) — both divisibility directions and the equality for ℕ.

## Historical Context and Motivation

The GCD-LCM distributive law is a classical identity in elementary number theory.
For positive integers, it is equivalent to the lattice identity in the distributive
lattice (ℕ, gcd, lcm). The law is also the key technical lemma in the Chinese
Remainder Theorem for non-coprime moduli with three or more congruences:
the condition for solvability of x ≡ aᵢ (mod mᵢ) reduces to verifying
gcd(lcm(m₁,m₂), m₃) ∣ (a₁-a₃), and the distributive law shows this
equals lcm(gcd(m₁,m₃), gcd(m₂,m₃)).

## Mathlib Status (v4.26)

Mathlib has `gcd_mul_lcm` and individual gcd/lcm properties, but no standalone
theorem `gcd_lcm_distrib` for EuclideanDomains or GCDMonoids. This fills that gap.

## Proof Structure

- **Easy direction** (8 lines): lcm(gcd(a,c), gcd(b,c)) ∣ gcd(lcm(a,b), c)
  Uses only that gcd divides both arguments and lcm is the least common multiple.

- **Hard direction** (~150 lines): gcd(lcm(a,b), c) ∣ lcm(gcd(a,c), gcd(b,c))
  Bézout-based: factor g=gcd(a,b), write a=g·α, b=g·β (coprime α,β), express
  M=lcm(gcd(a,c),gcd(b,c)) as linear combinations of a and c (and b and c),
  then show M = m·g·α·β + T·c where gcd(lcm(a,b),c) divides each term.

- **Equality for ℕ** (via Nat.dvd_antisymm): exact equality holds in ℕ since
  gcd and lcm of naturals are unique (not just up to units).

## Tags: number-theory, gcd, lcm, euclidean-domains, chinese-remainder-theorem, lattice-theory
-/

namespace ChineseRemainderNonCoprimeOQ03OQ02

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

-- ============================================================================
-- Section 1: Easy Direction
-- ============================================================================

/-- **Easy Direction**: `lcm(gcd(a,c), gcd(b,c))` divides `gcd(lcm(a,b), c)`.

    Proof: To show lcm(p,q) ∣ d, it suffices to show p ∣ d and q ∣ d (by lcm_dvd).
    - gcd(a,c) ∣ lcm(a,b): since gcd(a,c) ∣ a ∣ lcm(a,b)
    - gcd(b,c) ∣ lcm(a,b): since gcd(b,c) ∣ b ∣ lcm(a,b)
    - gcd(a,c) ∣ c and gcd(b,c) ∣ c: by definition of gcd -/
theorem lcm_gcd_dvd_gcd_lcm (a b c : R) :
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) ∣
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c := by
  apply EuclideanDomain.dvd_gcd
  · apply EuclideanDomain.lcm_dvd
    · exact dvd_trans (EuclideanDomain.gcd_dvd_left a c) (EuclideanDomain.dvd_lcm_left a b)
    · exact dvd_trans (EuclideanDomain.gcd_dvd_left b c) (EuclideanDomain.dvd_lcm_right a b)
  · apply EuclideanDomain.lcm_dvd
    · exact EuclideanDomain.gcd_dvd_right a c
    · exact EuclideanDomain.gcd_dvd_right b c

-- ============================================================================
-- Section 2: Helper Lemmas for Hard Direction
-- ============================================================================

private theorem lcm_dvd_mul (a b : R) :
    EuclideanDomain.lcm a b ∣ a * b :=
  EuclideanDomain.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)

private theorem gcd_lcm_dvd_mul (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ a * b :=
  dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (lcm_dvd_mul a b)

/-- `gcd(lcm(a,b), c)` divides the product `gcd(a,c) * gcd(b,c)`.

    The key Bézout identity: `gcd(a,c) = a·u + c·v` and `gcd(b,c) = b·u' + c·v'`,
    so their product = `a·b·(u·u') + c·(a·u·v' + b·v·u' + c·v·v')`.
    Since `gcd(lcm(a,b),c)` divides both `a·b` and `c`, it divides the product. -/
private theorem gcd_lcm_dvd_prod_gcd (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
    EuclideanDomain.gcd a c * EuclideanDomain.gcd b c := by
  have hd_ab := gcd_lcm_dvd_mul a b c
  have hd_c := EuclideanDomain.gcd_dvd_right (EuclideanDomain.lcm a b) c
  suffices h : ∃ s t : R,
      EuclideanDomain.gcd a c * EuclideanDomain.gcd b c = a * b * s + c * t by
    obtain ⟨s, t, ht⟩ := h
    rw [ht]; exact dvd_add (hd_ab.mul_right s) (hd_c.mul_right t)
  exact ⟨EuclideanDomain.gcdA a c * EuclideanDomain.gcdA b c,
         a * EuclideanDomain.gcdA a c * EuclideanDomain.gcdB b c +
         b * EuclideanDomain.gcdB a c * EuclideanDomain.gcdA b c +
         c * EuclideanDomain.gcdB a c * EuclideanDomain.gcdB b c,
    by rw [EuclideanDomain.gcd_eq_gcd_ab a c, EuclideanDomain.gcd_eq_gcd_ab b c]; ring⟩

-- ============================================================================
-- Section 3: Hard Direction (Bézout Factoring Argument)
-- ============================================================================

/-- **Hard Direction**: `gcd(lcm(a,b), c)` divides `lcm(gcd(a,c), gcd(b,c))`.

    **Proof strategy** (adapted from ChineseRemainderNonCoprimeOQ03):
    Let g = gcd(a,b), a = g·α, b = g·β, with IsCoprime α β (via Bézout).
    Let d = gcd(g,c), g = d·g', c = d·c', with IsCoprime g' c' (via Bézout).
    Set M = lcm(gcd(a,c), gcd(b,c)).

    By Bézout for gcd(a,c):
      M = r₁·a + s₁·c = r₁·g·α + s₁·c
    By Bézout for gcd(b,c):
      M = r₂·b + s₂·c = r₂·g·β + s₂·c

    Subtracting: g·(r₁α - r₂β) = (s₂-s₁)·c
    Dividing by d: g'·(r₁α - r₂β) = (s₂-s₁)·c'
    Since IsCoprime g' c': c' ∣ (r₁α - r₂β), write r₁α - r₂β = c'·w.
    Since IsCoprime α β: β ∣ (r₁ - p_b·c'·w), write r₁ - p_b·c'·w = β·m.
    So r₁ = m·β + p_b·c'·w, giving:
      M = r₁·g·α + s₁·c = m·(g·α·β) + (p_b·w·g'·α + s₁)·c

    Now gcd(lcm(a,b),c) ∣ g·α·β (since g·α·β = g·α·β is a common multiple of a=g·α
    and b=g·β), and gcd(lcm(a,b),c) ∣ c, so it divides M. ∎ -/
theorem gcd_lcm_dvd_lcm_gcd (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) := by
  -- Zero case
  by_cases hg : EuclideanDomain.gcd a b = 0
  · have ha : a = 0 := zero_dvd_iff.mp (hg ▸ EuclideanDomain.gcd_dvd_left a b)
    have hb : b = 0 := zero_dvd_iff.mp (hg ▸ EuclideanDomain.gcd_dvd_right a b)
    simp [ha, hb, EuclideanDomain.lcm, EuclideanDomain.dvd_lcm_left]
  -- Main case: factor a = g*α, b = g*β
  · set g := EuclideanDomain.gcd a b with hg_def
    obtain ⟨α, hα⟩ := EuclideanDomain.gcd_dvd_left a b
    obtain ⟨β, hβ⟩ := EuclideanDomain.gcd_dvd_right a b
    -- α and β are coprime: Bézout gives u*α + v*β = 1
    have hcop_αβ : IsCoprime α β := by
      refine ⟨EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b, ?_⟩
      apply mul_left_cancel₀ hg
      calc g * (EuclideanDomain.gcdA a b * α + EuclideanDomain.gcdB a b * β)
          = g * α * EuclideanDomain.gcdA a b + g * β * EuclideanDomain.gcdB a b := by ring
        _ = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b := by rw [← hα, ← hβ]
        _ = g := (EuclideanDomain.gcd_eq_gcd_ab a b).symm
        _ = g * 1 := (mul_one _).symm
    -- Factor d = gcd(g,c), g = d*g', c = d*c'
    set d' := EuclideanDomain.gcd g c with hd'_def
    have hd'_ne : d' ≠ 0 := by
      intro h; exact hg (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_left g c))
    obtain ⟨g', hg'⟩ := EuclideanDomain.gcd_dvd_left g c
    obtain ⟨c', hc'⟩ := EuclideanDomain.gcd_dvd_right g c
    -- g' and c' are coprime: Bézout gives u*g' + v*c' = 1
    have hcop_gc : IsCoprime g' c' := by
      refine ⟨EuclideanDomain.gcdA g c, EuclideanDomain.gcdB g c, ?_⟩
      apply mul_left_cancel₀ hd'_ne
      calc d' * (EuclideanDomain.gcdA g c * g' + EuclideanDomain.gcdB g c * c')
          = d' * g' * EuclideanDomain.gcdA g c + d' * c' * EuclideanDomain.gcdB g c := by ring
        _ = g * EuclideanDomain.gcdA g c + c * EuclideanDomain.gcdB g c := by rw [← hg', ← hc']
        _ = d' := (EuclideanDomain.gcd_eq_gcd_ab g c).symm
        _ = d' * 1 := (mul_one _).symm
    -- Bézout representations of M = lcm(gcd(a,c), gcd(b,c))
    set M := EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
    obtain ⟨k₁, hk₁⟩ := EuclideanDomain.dvd_lcm_left
      (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
    obtain ⟨k₂, hk₂⟩ := EuclideanDomain.dvd_lcm_right
      (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
    -- M = r₁·a + s₁·c  (Bézout expansion of gcd(a,c))
    have hM1 : M = (EuclideanDomain.gcdA a c * k₁) * a + (EuclideanDomain.gcdB a c * k₁) * c := by
      show EuclideanDomain.lcm _ _ = _
      conv_lhs => rw [hk₁, EuclideanDomain.gcd_eq_gcd_ab a c]; ring
    -- M = r₂·b + s₂·c  (Bézout expansion of gcd(b,c))
    have hM2 : M = (EuclideanDomain.gcdA b c * k₂) * b + (EuclideanDomain.gcdB b c * k₂) * c := by
      show EuclideanDomain.lcm _ _ = _
      conv_lhs => rw [hk₂, EuclideanDomain.gcd_eq_gcd_ab b c]; ring
    set r₁ := EuclideanDomain.gcdA a c * k₁
    set s₁ := EuclideanDomain.gcdB a c * k₁
    set r₂ := EuclideanDomain.gcdA b c * k₂
    set s₂ := EuclideanDomain.gcdB b c * k₂
    -- r₁*a - r₂*b = (s₂ - s₁)*c  (subtract the two representations)
    have hrab : r₁ * a - r₂ * b = (s₂ - s₁) * c := by
      have heq := hM1.symm.trans hM2
      calc r₁ * a - r₂ * b
          = (r₁ * a + s₁ * c) - (r₂ * b + s₂ * c) + (s₂ - s₁) * c := by ring
        _ = (r₂ * b + s₂ * c) - (r₂ * b + s₂ * c) + (s₂ - s₁) * c := by rw [heq]
        _ = (s₂ - s₁) * c := by ring
    -- g*(r₁α - r₂β) = (s₂-s₁)*c  (substitute a = g*α, b = g*β)
    have hgrab : g * (r₁ * α - r₂ * β) = (s₂ - s₁) * c := by
      calc g * (r₁ * α - r₂ * β)
          = r₁ * (g * α) - r₂ * (g * β) := by ring
        _ = r₁ * a - r₂ * b := by rw [← hα, ← hβ]
        _ = (s₂ - s₁) * c := hrab
    -- g'*(r₁α - r₂β) = (s₂-s₁)*c'  (cancel d')
    have hgrab' : g' * (r₁ * α - r₂ * β) = (s₂ - s₁) * c' := by
      apply mul_left_cancel₀ hd'_ne
      calc d' * (g' * (r₁ * α - r₂ * β))
          = (d' * g') * (r₁ * α - r₂ * β) := by ring
        _ = g * (r₁ * α - r₂ * β) := by rw [← hg']
        _ = (s₂ - s₁) * c := hgrab
        _ = (s₂ - s₁) * (d' * c') := by rw [← hc']
        _ = d' * ((s₂ - s₁) * c') := by ring
    -- c' ∣ (r₁α - r₂β)  (since IsCoprime g' c' and g' | g'*(r₁α-r₂β) = (s₂-s₁)*c')
    have hc'_dvd : c' ∣ (r₁ * α - r₂ * β) := by
      obtain ⟨u, v, huv⟩ := hcop_gc
      have hk : c' ∣ g' * (r₁ * α - r₂ * β) := ⟨s₂ - s₁, hgrab'.symm⟩
      obtain ⟨k, hk_eq⟩ := hk
      exact ⟨u * k + v * (r₁ * α - r₂ * β), by
        calc r₁ * α - r₂ * β
            = (r₁ * α - r₂ * β) * (u * g' + v * c') := by rw [huv, mul_one]
          _ = u * (g' * (r₁ * α - r₂ * β)) + v * c' * (r₁ * α - r₂ * β) := by ring
          _ = u * (c' * k) + v * c' * (r₁ * α - r₂ * β) := by rw [hk_eq]
          _ = c' * (u * k + v * (r₁ * α - r₂ * β)) := by ring⟩
    obtain ⟨w, hw⟩ := hc'_dvd
    -- β ∣ (r₁ - p_b*c'*w)  (using IsCoprime α β)
    obtain ⟨p_b, q_b, hpq⟩ := hcop_αβ
    have hβ_dvd : β ∣ (r₁ - p_b * (c' * w)) := by
      have hr₁α : r₁ * α = r₂ * β + c' * w := by
        calc r₁ * α = (r₁ * α - r₂ * β) + r₂ * β := by ring
          _ = c' * w + r₂ * β := by rw [hw]
          _ = r₂ * β + c' * w := by ring
      have hqβ : q_b * β = 1 - p_b * α := by
        calc q_b * β = (p_b * α + q_b * β) - p_b * α := by ring
          _ = 1 - p_b * α := by rw [hpq]
      have key : (r₁ - p_b * (c' * w)) * α = (r₂ + q_b * (c' * w)) * β := by
        calc (r₁ - p_b * (c' * w)) * α
            = r₁ * α - p_b * (c' * w) * α := by ring
          _ = r₂ * β + c' * w - p_b * (c' * w) * α := by rw [hr₁α]
          _ = r₂ * β + c' * w * (q_b * β) := by rw [← hqβ]; ring
          _ = (r₂ + q_b * (c' * w)) * β := by ring
      exact ⟨p_b * (r₂ + q_b * (c' * w)) + q_b * (r₁ - p_b * (c' * w)), by
        calc r₁ - p_b * (c' * w)
            = (r₁ - p_b * (c' * w)) * (p_b * α + q_b * β) := by rw [hpq, mul_one]
          _ = p_b * ((r₁ - p_b * (c' * w)) * α) + q_b * (r₁ - p_b * (c' * w)) * β := by ring
          _ = p_b * ((r₂ + q_b * (c' * w)) * β) + q_b * (r₁ - p_b * (c' * w)) * β := by rw [key]
          _ = β * (p_b * (r₂ + q_b * (c' * w)) + q_b * (r₁ - p_b * (c' * w))) := by ring⟩
    obtain ⟨m, hm⟩ := hβ_dvd
    -- r₁ = m*β + p_b*c'*w
    have hr₁ : r₁ = m * β + p_b * (c' * w) := by
      calc r₁ = (r₁ - p_b * (c' * w)) + p_b * (c' * w) := by ring
        _ = β * m + p_b * (c' * w) := by rw [hm]
        _ = m * β + p_b * (c' * w) := by ring
    -- c'*g = c*g'  (from d'*g' = g and d'*c' = c)
    have hcg : c' * g = c * g' := by
      calc c' * g = c' * (d' * g') := by rw [hg']
        _ = (d' * c') * g' := by ring
        _ = c * g' := by rw [← hc']
    -- Decompose M = m*(g*α*β) + (p_b*w*g'*α + s₁)*c
    have hM_decomp : M =
        m * (g * α * β) + (p_b * w * g' * α + s₁) * c := by
      show EuclideanDomain.lcm _ _ = _
      calc M = r₁ * a + s₁ * c := hM1
        _ = r₁ * (g * α) + s₁ * c := by rw [hα]
        _ = (m * β + p_b * (c' * w)) * (g * α) + s₁ * c := by rw [hr₁]
        _ = m * (g * α * β) + p_b * w * α * (c' * g) + s₁ * c := by ring
        _ = m * (g * α * β) + p_b * w * α * (c * g') + s₁ * c := by rw [hcg]
        _ = m * (g * α * β) + (p_b * w * g' * α + s₁) * c := by ring
    -- g*α*β is a common multiple of a=g*α and b=g*β, so lcm(a,b) ∣ g*α*β
    have hd_gab : EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ g * α * β :=
      dvd_trans (EuclideanDomain.gcd_dvd_left _ _)
        (EuclideanDomain.lcm_dvd ⟨β, by rw [hα]; ring⟩ ⟨α, by rw [hβ]; ring⟩)
    -- Conclude: gcd(lcm(a,b),c) ∣ M = m*(g*α*β) + T*c
    show EuclideanDomain.gcd _ _ ∣ M
    rw [hM_decomp]
    exact dvd_add (hd_gab.mul_left m)
      ((EuclideanDomain.gcd_dvd_right (EuclideanDomain.lcm a b) c).mul_left _)

-- ============================================================================
-- Section 4: The Full Distributive Law
-- ============================================================================

/-- **GCD-LCM Distributive Law** (Associated): In any Euclidean domain,
    `gcd(lcm(a,b), c)` and `lcm(gcd(a,c), gcd(b,c))` are associated (equal up to a unit).

    This is immediate from the two divisibility directions. -/
theorem gcd_lcm_associated (a b c : R) :
    Associated (EuclideanDomain.gcd (EuclideanDomain.lcm a b) c)
               (EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)) :=
  associated_of_dvd_dvd (gcd_lcm_dvd_lcm_gcd a b c) (lcm_gcd_dvd_gcd_lcm a b c)

/-- The symmetric statement. -/
theorem lcm_gcd_associated (a b c : R) :
    Associated (EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c))
               (EuclideanDomain.gcd (EuclideanDomain.lcm a b) c) :=
  (gcd_lcm_associated a b c).symm

-- ============================================================================
-- Section 5: Exact Equality for ℕ
-- ============================================================================

/-- **GCD-LCM Distributive Law for ℕ** (exact equality):
    `Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c)`.

    Since ℕ is a NormalizedGCDMonoid, divisibility is antisymmetric for natural
    numbers, so the two divisibility directions give exact equality via dvd_antisymm.

    Proof: Direct application of Nat.dvd_antisymm to the two directions. -/
theorem nat_gcd_lcm_distrib (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  apply Nat.dvd_antisymm
  · -- gcd(lcm(a,b), c) ∣ lcm(gcd(a,c), gcd(b,c))
    apply Nat.lcm_dvd
    · exact Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left a b))
                        (Nat.gcd_dvd_right _ _)
    · exact Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_right a b))
                        (Nat.gcd_dvd_right _ _)
  · -- lcm(gcd(a,c), gcd(b,c)) ∣ gcd(lcm(a,b), c)
    apply Nat.dvd_gcd
    · apply Nat.lcm_dvd
      · exact dvd_trans (Nat.gcd_dvd_left a c) (Nat.dvd_lcm_left a b)
      · exact dvd_trans (Nat.gcd_dvd_left b c) (Nat.dvd_lcm_right a b)
    · apply Nat.lcm_dvd
      · exact Nat.gcd_dvd_right a c
      · exact Nat.gcd_dvd_right b c

-- ============================================================================
-- Section 6: Concrete Numerical Verification
-- ============================================================================

/-- gcd(lcm(4,6), 12) = lcm(gcd(4,12), gcd(6,12))
    i.e., gcd(12, 12) = lcm(4, 6) → 12 = 12  ✓ -/
example : Nat.gcd (Nat.lcm 4 6) 12 = Nat.lcm (Nat.gcd 4 12) (Nat.gcd 6 12) := by
  native_decide

/-- gcd(lcm(6,10), 15) = lcm(gcd(6,15), gcd(10,15))
    i.e., gcd(30, 15) = lcm(3, 5) → 15 = 15  ✓ -/
example : Nat.gcd (Nat.lcm 6 10) 15 = Nat.lcm (Nat.gcd 6 15) (Nat.gcd 10 15) := by
  native_decide

/-- gcd(lcm(12,18), 24) = lcm(gcd(12,24), gcd(18,24))
    i.e., gcd(36, 24) = lcm(12, 6) → 12 = 12  ✓ -/
example : Nat.gcd (Nat.lcm 12 18) 24 = Nat.lcm (Nat.gcd 12 24) (Nat.gcd 18 24) := by
  native_decide

-- ============================================================================
-- Section 7: Connection to CRT
-- ============================================================================

/-- **CRT Connection**: The GCD-LCM distributive law is the key lemma in the
    3-moduli Chinese Remainder Theorem. If x₀ satisfies m₁ ∣ (x₀-a₁) and
    m₂ ∣ (x₀-a₂), then to find x also satisfying m₃ ∣ (x-a₃), we need
    gcd(lcm(m₁,m₂), m₃) ∣ (x₀-a₃). By the distributive law:

      gcd(lcm(m₁,m₂), m₃) ~ lcm(gcd(m₁,m₃), gcd(m₂,m₃))

    The pairwise conditions gcd(m₁,m₃) ∣ (a₁-a₃) and gcd(m₂,m₃) ∣ (a₂-a₃)
    together imply that lcm(gcd(m₁,m₃), gcd(m₂,m₃)) ∣ (x₀-a₃). -/
theorem crt_gcd_lcm_condition (m₁ m₂ m₃ a₁ a₂ a₃ x₀ : R)
    (hx₁ : m₁ ∣ (x₀ - a₁)) (hx₂ : m₂ ∣ (x₀ - a₂))
    (h₁₃ : EuclideanDomain.gcd m₁ m₃ ∣ (a₁ - a₃))
    (h₂₃ : EuclideanDomain.gcd m₂ m₃ ∣ (a₂ - a₃)) :
    EuclideanDomain.lcm (EuclideanDomain.gcd m₁ m₃) (EuclideanDomain.gcd m₂ m₃) ∣
    (x₀ - a₃) := by
  -- gcd(m₁,m₃) ∣ (x₀-a₃): since gcd(m₁,m₃) ∣ m₁ ∣ (x₀-a₁) and gcd(m₁,m₃) ∣ (a₁-a₃)
  have hd₁ : EuclideanDomain.gcd m₁ m₃ ∣ (x₀ - a₃) := by
    have := dvd_trans (EuclideanDomain.gcd_dvd_left m₁ m₃) hx₁
    have : EuclideanDomain.gcd m₁ m₃ ∣ (x₀ - a₁) := dvd_trans (EuclideanDomain.gcd_dvd_left m₁ m₃) hx₁
    calc EuclideanDomain.gcd m₁ m₃ ∣ (x₀ - a₁) + (a₁ - a₃) := dvd_add this h₁₃
      _ = x₀ - a₃ := by ring
  -- gcd(m₂,m₃) ∣ (x₀-a₃): since gcd(m₂,m₃) ∣ m₂ ∣ (x₀-a₂) and gcd(m₂,m₃) ∣ (a₂-a₃)
  have hd₂ : EuclideanDomain.gcd m₂ m₃ ∣ (x₀ - a₃) := by
    have this₂ : EuclideanDomain.gcd m₂ m₃ ∣ (x₀ - a₂) := dvd_trans (EuclideanDomain.gcd_dvd_left m₂ m₃) hx₂
    calc EuclideanDomain.gcd m₂ m₃ ∣ (x₀ - a₂) + (a₂ - a₃) := dvd_add this₂ h₂₃
      _ = x₀ - a₃ := by ring
  -- lcm(gcd(m₁,m₃), gcd(m₂,m₃)) ∣ (x₀-a₃): since both divide it
  exact EuclideanDomain.lcm_dvd hd₁ hd₂

end ChineseRemainderNonCoprimeOQ03OQ02
