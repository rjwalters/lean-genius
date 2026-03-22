/-
  CRT Non-Coprime OQ-03: Pairwise GCD Sufficiency for Three Moduli

  Extends the non-coprime CRT from 2 moduli to 3 moduli:
  Given m₁, m₂, m₃ in a EuclideanDomain R, and a₁, a₂, a₃ in R:
  ∃ x, m₁ ∣ (x-a₁) ∧ m₂ ∣ (x-a₂) ∧ m₃ ∣ (x-a₃)
  ↔ pairwise: gcd(mᵢ,mⱼ) ∣ (aᵢ-aⱼ) for all i ≠ j.

  Necessity: proved in OQ02 (ed_crt_three_necessary)
  Sufficiency: proved by reducing to the 2-moduli case:
    1. Solve first pair (m₁,m₂) to get x₀
    2. Show gcd(lcm(m₁,m₂), m₃) ∣ (x₀-a₃) via GCD-LCM distributive law
    3. Solve second pair (lcm(m₁,m₂), m₃) to get final solution

  Parent: ChineseRemainderNonCoprimeOQ02.lean (0 axioms, 0 sorries)
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace ChineseRemainderNonCoprimeOQ03

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-
## Part 0: 2-Moduli CRT (self-contained, from OQ02)
-/

/-- Necessity: if x solves both congruences, then gcd(m,n) ∣ (a - b). -/
private theorem ed_crt_necessary {m n a b : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) :
    EuclideanDomain.gcd m n ∣ (a - b) := by
  obtain ⟨x, hm, hn⟩ := h
  have h1 := dvd_trans (EuclideanDomain.gcd_dvd_left m n) hm
  have h2 := dvd_trans (EuclideanDomain.gcd_dvd_right m n) hn
  have : EuclideanDomain.gcd m n ∣ ((x - b) - (x - a)) := dvd_sub h2 h1
  rwa [show (x - b) - (x - a) = a - b from by ring] at this

/-- Sufficiency: if gcd(m,n) ∣ (a - b), construct a solution via Bézout. -/
private theorem ed_crt_sufficient {m n a b : R}
    (h : EuclideanDomain.gcd m n ∣ (a - b)) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨a - m * (EuclideanDomain.gcdA m n * q), ?_, ?_⟩
  · exact ⟨-(EuclideanDomain.gcdA m n * q), by ring⟩
  · refine ⟨EuclideanDomain.gcdB m n * q, ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab m n
    have hkey : EuclideanDomain.gcd m n - m * EuclideanDomain.gcdA m n =
        n * EuclideanDomain.gcdB m n := by rw [hbez]; ring
    calc a - m * (EuclideanDomain.gcdA m n * q) - b
        = (a - b) - m * EuclideanDomain.gcdA m n * q := by ring
      _ = EuclideanDomain.gcd m n * q - m * EuclideanDomain.gcdA m n * q := by rw [hq]
      _ = (EuclideanDomain.gcd m n - m * EuclideanDomain.gcdA m n) * q := by ring
      _ = n * EuclideanDomain.gcdB m n * q := by rw [hkey]
      _ = n * (EuclideanDomain.gcdB m n * q) := by ring

/-- Necessity for 3 moduli (pairwise conditions). -/
private theorem ed_crt_three_necessary {m n p a b c : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) ∧ p ∣ (x - c)) :
    EuclideanDomain.gcd m n ∣ (a - b) ∧
    EuclideanDomain.gcd m p ∣ (a - c) ∧
    EuclideanDomain.gcd n p ∣ (b - c) := by
  obtain ⟨x, hm, hn, hp⟩ := h
  exact ⟨ed_crt_necessary ⟨x, hm, hn⟩, ed_crt_necessary ⟨x, hm, hp⟩,
         ed_crt_necessary ⟨x, hn, hp⟩⟩

/-
## Part I: Intermediate Lemmas
-/

/-- If m ∣ (x-a) then gcd(m,p) ∣ (x-a). -/
theorem gcd_dvd_of_dvd_sub {m p a x : R} (h : m ∣ (x - a)) :
    EuclideanDomain.gcd m p ∣ (x - a) :=
  dvd_trans (EuclideanDomain.gcd_dvd_left m p) h

/-- If m ∣ (x₀-a₁) and gcd(m,m₃) ∣ (a₁-a₃), then gcd(m,m₃) ∣ (x₀-a₃). -/
theorem gcd_dvd_sub_of_congr {m m₃ a₁ a₃ x₀ : R}
    (hcong : m ∣ (x₀ - a₁))
    (hpair : EuclideanDomain.gcd m m₃ ∣ (a₁ - a₃)) :
    EuclideanDomain.gcd m m₃ ∣ (x₀ - a₃) := by
  have h1 : EuclideanDomain.gcd m m₃ ∣ (x₀ - a₁) := gcd_dvd_of_dvd_sub hcong
  have : x₀ - a₃ = (x₀ - a₁) + (a₁ - a₃) := by ring
  rw [this]
  exact dvd_add h1 hpair

/-
## Part II: GCD-LCM Distributive Law
-/

/-- Easy direction: lcm(gcd(a,c), gcd(b,c)) divides gcd(lcm(a,b), c). -/
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

/-- lcm(a,b) divides a*b: a*b is a common multiple of a and b. -/
private theorem lcm_dvd_mul (a b : R) :
    EuclideanDomain.lcm a b ∣ a * b :=
  EuclideanDomain.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)

/-- gcd(lcm(a,b), c) divides a*b, since gcd divides lcm which divides a*b. -/
private theorem gcd_lcm_dvd_mul (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ a * b :=
  dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (lcm_dvd_mul a b)

/-- Key Bézout-based lemma: gcd(lcm(a,b), c) divides gcd(a,c) * gcd(b,c).
    Proof: By Bézout, gcd(a,c) = a*u + c*v and gcd(b,c) = b*u' + c*v'.
    Their product = a*b*u*u' + c*(...). Since gcd(lcm(a,b),c) | a*b (via lcm)
    and gcd(lcm(a,b),c) | c, it divides both summands, hence the product. -/
private theorem gcd_lcm_dvd_prod_gcd (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
    EuclideanDomain.gcd a c * EuclideanDomain.gcd b c := by
  have hd_ab : EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ a * b :=
    gcd_lcm_dvd_mul a b c
  have hd_c : EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ c :=
    EuclideanDomain.gcd_dvd_right _ _
  -- p*q is a ℤ-linear combination of a*b and c (via Bézout expansion)
  suffices h : ∃ s t : R,
      EuclideanDomain.gcd a c * EuclideanDomain.gcd b c = a * b * s + c * t by
    obtain ⟨s, t, ht⟩ := h
    rw [ht]
    exact dvd_add (hd_ab.mul_right s) (hd_c.mul_right t)
  refine ⟨EuclideanDomain.gcdA a c * EuclideanDomain.gcdA b c,
          a * EuclideanDomain.gcdA a c * EuclideanDomain.gcdB b c +
          b * EuclideanDomain.gcdB a c * EuclideanDomain.gcdA b c +
          c * EuclideanDomain.gcdB a c * EuclideanDomain.gcdB b c, ?_⟩
  rw [EuclideanDomain.gcd_eq_gcd_ab a c, EuclideanDomain.gcd_eq_gcd_ab b c]
  ring

/-- Hard direction of the GCD-LCM distributive law:
    gcd(lcm(a,b), c) divides lcm(gcd(a,c), gcd(b,c)).

    Proof strategy: We show that any common multiple z of gcd(a,c) and gcd(b,c)
    is divisible by gcd(lcm(a,b), c). Applied to z = lcm(gcd(a,c), gcd(b,c)),
    this gives the result.

    The key step is writing z as a linear combination of g·α·β and c, where
    g = gcd(a,b), a = g·α, b = g·β with IsCoprime α β. Since g·α·β is a
    common multiple of a and b, lcm(a,b) divides it, so gcd(lcm(a,b),c) divides
    both terms. The algebraic decomposition uses Bézout twice (for gcd(a,c) and
    gcd(b,c)) plus coprime factoring through gcd(a,b) and gcd(gcd(a,b),c). -/
theorem gcd_lcm_dvd_lcm_gcd (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) := by
  -- Handle zero case: gcd(a,b) = 0 implies a = b = 0
  by_cases hg : EuclideanDomain.gcd a b = 0
  · have ha : a = 0 := by
      have := EuclideanDomain.gcd_dvd_left a b; rw [hg] at this
      exact (zero_dvd_iff.mp this)
    have hb : b = 0 := by
      have := EuclideanDomain.gcd_dvd_right a b; rw [hg] at this
      exact (zero_dvd_iff.mp this)
    rw [ha, hb]
    -- Goal: gcd(lcm(0,0), c) | lcm(gcd(0,c), gcd(0,c))
    -- lcm(0,0) = 0, so gcd(0,c) | lcm(gcd(0,c), gcd(0,c)) by dvd_lcm_left
    have h0 : EuclideanDomain.lcm (0 : R) 0 = 0 := by
      simp [EuclideanDomain.lcm]
    rw [h0]
    exact EuclideanDomain.dvd_lcm_left _ _
  · -- Main case: g = gcd(a,b) ≠ 0
    -- Make gcd(a,b) opaque to prevent rw from rewriting inside it
    set g := EuclideanDomain.gcd a b with hg_def
    -- Factor a = g*α, b = g*β
    obtain ⟨α, hα⟩ := EuclideanDomain.gcd_dvd_left a b
    obtain ⟨β, hβ⟩ := EuclideanDomain.gcd_dvd_right a b
    -- IsCoprime α β via Bézout cancellation
    have hcop_αβ : IsCoprime α β := by
      refine ⟨EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b, ?_⟩
      apply mul_left_cancel₀ hg
      calc g * (EuclideanDomain.gcdA a b * α + EuclideanDomain.gcdB a b * β)
          = g * α * EuclideanDomain.gcdA a b +
            g * β * EuclideanDomain.gcdB a b := by ring
        _ = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b := by
            rw [← hα, ← hβ]
        _ = g := (EuclideanDomain.gcd_eq_gcd_ab a b).symm
        _ = g * 1 := (mul_one _).symm
    -- Factor through gcd(g, c)
    set d' := EuclideanDomain.gcd g c with hd'_def
    have hd'_ne : d' ≠ 0 := by
      intro h; apply hg
      exact (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_left g c))
    obtain ⟨g', hg'⟩ := EuclideanDomain.gcd_dvd_left g c
    obtain ⟨c', hc'⟩ := EuclideanDomain.gcd_dvd_right g c
    -- IsCoprime g' c' via Bézout cancellation
    have hcop_gc : IsCoprime g' c' := by
      refine ⟨EuclideanDomain.gcdA g c, EuclideanDomain.gcdB g c, ?_⟩
      apply mul_left_cancel₀ hd'_ne
      calc d' * (EuclideanDomain.gcdA g c * g' + EuclideanDomain.gcdB g c * c')
          = d' * g' * EuclideanDomain.gcdA g c +
            d' * c' * EuclideanDomain.gcdB g c := by ring
        _ = g * EuclideanDomain.gcdA g c + c * EuclideanDomain.gcdB g c := by
            rw [← hg', ← hc']
        _ = d' := (EuclideanDomain.gcd_eq_gcd_ab g c).symm
        _ = d' * 1 := (mul_one _).symm
    -- Bézout representations: M as combination of a,c and b,c
    obtain ⟨k₁, hk₁⟩ := EuclideanDomain.dvd_lcm_left
      (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
    obtain ⟨k₂, hk₂⟩ := EuclideanDomain.dvd_lcm_right
      (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
    -- M = r₁*a + s₁*c  (from gcd(a,c) | M and Bézout for gcd(a,c))
    have hM1 : EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) =
        (EuclideanDomain.gcdA a c * k₁) * a +
        (EuclideanDomain.gcdB a c * k₁) * c := by
      conv_lhs => rw [hk₁, EuclideanDomain.gcd_eq_gcd_ab a c]
      ring
    -- M = r₂*b + s₂*c  (from gcd(b,c) | M and Bézout for gcd(b,c))
    have hM2 : EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) =
        (EuclideanDomain.gcdA b c * k₂) * b +
        (EuclideanDomain.gcdB b c * k₂) * c := by
      conv_lhs => rw [hk₂, EuclideanDomain.gcd_eq_gcd_ab b c]
      ring
    -- Make Bézout coefficient expressions opaque for safe rewriting later
    set r₁ := EuclideanDomain.gcdA a c * k₁
    set s₁ := EuclideanDomain.gcdB a c * k₁
    set r₂ := EuclideanDomain.gcdA b c * k₂
    set s₂ := EuclideanDomain.gcdB b c * k₂
    -- Subtract: r₁*a - r₂*b = (s₂ - s₁)*c
    have hrab : r₁ * a - r₂ * b = (s₂ - s₁) * c := by
      have heq := hM1.symm.trans hM2
      calc r₁ * a - r₂ * b
          = (r₁ * a + s₁ * c) - (r₂ * b + s₂ * c) + (s₂ - s₁) * c := by ring
        _ = (r₂ * b + s₂ * c) - (r₂ * b + s₂ * c) + (s₂ - s₁) * c := by rw [heq]
        _ = (s₂ - s₁) * c := by ring
    -- Substitute a = g*α, b = g*β: g*(r₁*α - r₂*β) = (s₂-s₁)*c
    have hgrab : g * (r₁ * α - r₂ * β) = (s₂ - s₁) * c := by
      calc g * (r₁ * α - r₂ * β)
          = r₁ * (g * α) - r₂ * (g * β) := by ring
        _ = r₁ * a - r₂ * b := by rw [← hα, ← hβ]
        _ = _ := hrab
    -- Cancel d' from both sides: g'*(r₁*α - r₂*β) = (s₂-s₁)*c'
    have hgrab' : g' * (r₁ * α - r₂ * β) = (s₂ - s₁) * c' := by
      apply mul_left_cancel₀ hd'_ne
      have hlhs : d' * (g' * (r₁ * α - r₂ * β)) = (s₂ - s₁) * c := by
        calc d' * (g' * (r₁ * α - r₂ * β))
            = (d' * g') * (r₁ * α - r₂ * β) := by ring
          _ = g * (r₁ * α - r₂ * β) := by rw [← hg']
          _ = (s₂ - s₁) * c := hgrab
      have hrhs : d' * ((s₂ - s₁) * c') = (s₂ - s₁) * c := by
        calc d' * ((s₂ - s₁) * c') = (s₂ - s₁) * (d' * c') := by ring
          _ = (s₂ - s₁) * c := by rw [← hc']
      exact hlhs.trans hrhs.symm
    -- c' divides (r₁*α - r₂*β) via IsCoprime g' c'
    have hc'_dvd : c' ∣ (r₁ * α - r₂ * β) := by
      obtain ⟨u, v, huv⟩ := hcop_gc  -- u * g' + v * c' = 1
      obtain ⟨k, hk⟩ : c' ∣ g' * (r₁ * α - r₂ * β) := by
        rw [hgrab']; exact dvd_mul_left c' _
      exact ⟨u * k + v * (r₁ * α - r₂ * β), by
        calc r₁ * α - r₂ * β
            = (r₁ * α - r₂ * β) * (u * g' + v * c') := by rw [huv, mul_one]
          _ = u * (g' * (r₁ * α - r₂ * β)) + v * c' * (r₁ * α - r₂ * β) := by ring
          _ = u * (c' * k) + v * c' * (r₁ * α - r₂ * β) := by rw [hk]
          _ = c' * (u * k + v * (r₁ * α - r₂ * β)) := by ring⟩
    obtain ⟨w, hw⟩ := hc'_dvd
    -- β divides (r₁ - p_b * c' * w) via IsCoprime α β
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
          _ = (r₂ * β + c' * w) - p_b * (c' * w) * α := by rw [hr₁α]
          _ = r₂ * β + c' * w * (1 - p_b * α) := by ring
          _ = r₂ * β + c' * w * (q_b * β) := by rw [← hqβ]
          _ = (r₂ + q_b * (c' * w)) * β := by ring
      exact ⟨p_b * (r₂ + q_b * (c' * w)) + q_b * (r₁ - p_b * (c' * w)), by
        calc r₁ - p_b * (c' * w)
            = (r₁ - p_b * (c' * w)) * (p_b * α + q_b * β) := by rw [hpq, mul_one]
          _ = p_b * ((r₁ - p_b * (c' * w)) * α) +
              q_b * (r₁ - p_b * (c' * w)) * β := by ring
          _ = p_b * ((r₂ + q_b * (c' * w)) * β) +
              q_b * (r₁ - p_b * (c' * w)) * β := by rw [key]
          _ = β * (p_b * (r₂ + q_b * (c' * w)) + q_b * (r₁ - p_b * (c' * w))) := by ring⟩
    obtain ⟨m, hm⟩ := hβ_dvd
    -- r₁ = m*β + p_b*c'*w
    have hr₁ : r₁ = m * β + p_b * (c' * w) := by
      calc r₁ = (r₁ - p_b * (c' * w)) + p_b * (c' * w) := by ring
        _ = β * m + p_b * (c' * w) := by rw [hm]
        _ = m * β + p_b * (c' * w) := by ring
    -- Key identity: c' * g = c * g'
    have hcg : c' * g = c * g' := by
      calc c' * g = c' * (d' * g') := by rw [hg']
        _ = (d' * c') * g' := by ring
        _ = c * g' := by rw [← hc']
    -- Decompose M = m*(g*α*β) + T*c  (safe: g, r₁, s₁ are opaque)
    have hM_decomp :
        EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) =
        m * (g * α * β) + (p_b * w * g' * α + s₁) * c := by
      calc EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
          = r₁ * a + s₁ * c := hM1
        _ = r₁ * (g * α) + s₁ * c := by rw [hα]
        _ = (m * β + p_b * (c' * w)) * (g * α) + s₁ * c := by rw [hr₁]
        _ = m * (g * α * β) + p_b * w * α * (c' * g) + s₁ * c := by ring
        _ = m * (g * α * β) + p_b * w * α * (c * g') + s₁ * c := by rw [hcg]
        _ = m * (g * α * β) + (p_b * w * g' * α + s₁) * c := by ring
    -- d | g*α*β  (since lcm(a,b) | g*α*β, and d | lcm(a,b))
    have hd_gab : EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ g * α * β := by
      refine dvd_trans (EuclideanDomain.gcd_dvd_left _ _) ?_
      refine EuclideanDomain.lcm_dvd ?_ ?_
      · -- a | g*α*β (safe: rw [hα] only affects standalone a, g is opaque)
        rw [hα]; exact dvd_mul_right _ _
      · -- b | g*α*β
        exact ⟨α, by calc g * α * β = g * β * α := by ring
          _ = b * α := by rw [← hβ]⟩
    -- Conclude: d | M
    rw [hM_decomp]
    exact dvd_add
      (hd_gab.mul_left m)
      ((EuclideanDomain.gcd_dvd_right (EuclideanDomain.lcm a b) c).mul_left _)

/-
## Part III: Three-Moduli CRT Sufficiency
-/

/-- Sufficiency: pairwise GCD conditions imply the system is solvable. -/
theorem ed_crt_three_sufficient {m₁ m₂ m₃ a₁ a₂ a₃ : R}
    (h12 : EuclideanDomain.gcd m₁ m₂ ∣ (a₁ - a₂))
    (h13 : EuclideanDomain.gcd m₁ m₃ ∣ (a₁ - a₃))
    (h23 : EuclideanDomain.gcd m₂ m₃ ∣ (a₂ - a₃)) :
    ∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃) := by
  obtain ⟨x₀, hx₀_m₁, hx₀_m₂⟩ := ed_crt_sufficient h12
  have hg13 : EuclideanDomain.gcd m₁ m₃ ∣ (x₀ - a₃) :=
    gcd_dvd_sub_of_congr hx₀_m₁ h13
  have hg23 : EuclideanDomain.gcd m₂ m₃ ∣ (x₀ - a₃) :=
    gcd_dvd_sub_of_congr hx₀_m₂ h23
  have hlcm : EuclideanDomain.lcm (EuclideanDomain.gcd m₁ m₃) (EuclideanDomain.gcd m₂ m₃) ∣
    (x₀ - a₃) := EuclideanDomain.lcm_dvd hg13 hg23
  have hgcd_lcm : EuclideanDomain.gcd (EuclideanDomain.lcm m₁ m₂) m₃ ∣ (x₀ - a₃) :=
    dvd_trans (gcd_lcm_dvd_lcm_gcd m₁ m₂ m₃) hlcm
  obtain ⟨x, hx_lcm, hx_m₃⟩ := ed_crt_sufficient hgcd_lcm
  refine ⟨x, ?_, ?_, hx_m₃⟩
  · have h_m₁_lcm : m₁ ∣ (x - x₀) :=
      dvd_trans (EuclideanDomain.dvd_lcm_left m₁ m₂) hx_lcm
    have : x - a₁ = (x - x₀) + (x₀ - a₁) := by ring
    rw [this]; exact dvd_add h_m₁_lcm hx₀_m₁
  · have h_m₂_lcm : m₂ ∣ (x - x₀) :=
      dvd_trans (EuclideanDomain.dvd_lcm_right m₁ m₂) hx_lcm
    have : x - a₂ = (x - x₀) + (x₀ - a₂) := by ring
    rw [this]; exact dvd_add h_m₂_lcm hx₀_m₂

/-- The full iff for 3 moduli: system solvable ↔ pairwise GCD conditions. -/
theorem ed_crt_three_iff {m₁ m₂ m₃ a₁ a₂ a₃ : R} :
    (∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃)) ↔
    (EuclideanDomain.gcd m₁ m₂ ∣ (a₁ - a₂) ∧
     EuclideanDomain.gcd m₁ m₃ ∣ (a₁ - a₃) ∧
     EuclideanDomain.gcd m₂ m₃ ∣ (a₂ - a₃)) :=
  ⟨ed_crt_three_necessary,
   fun ⟨h12, h13, h23⟩ => ed_crt_three_sufficient h12 h13 h23⟩

/-- Uniqueness for 3 moduli: solutions agree modulo lcm(m₁, lcm(m₂, m₃)). -/
theorem ed_crt_three_unique {m₁ m₂ m₃ a₁ a₂ a₃ x y : R}
    (hx : m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃))
    (hy : m₁ ∣ (y - a₁) ∧ m₂ ∣ (y - a₂) ∧ m₃ ∣ (y - a₃)) :
    EuclideanDomain.lcm m₁ (EuclideanDomain.lcm m₂ m₃) ∣ (x - y) := by
  have h1 : m₁ ∣ (x - y) := by
    have := dvd_sub hx.1 hy.1; rwa [show (x - a₁) - (y - a₁) = x - y from by ring] at this
  have h2 : m₂ ∣ (x - y) := by
    have := dvd_sub hx.2.1 hy.2.1; rwa [show (x - a₂) - (y - a₂) = x - y from by ring] at this
  have h3 : m₃ ∣ (x - y) := by
    have := dvd_sub hx.2.2 hy.2.2; rwa [show (x - a₃) - (y - a₃) = x - y from by ring] at this
  exact EuclideanDomain.lcm_dvd h1 (EuclideanDomain.lcm_dvd h2 h3)

/-
## Summary

### Theorems proved (0 axioms, 0 sorries):
1. `gcd_dvd_of_dvd_sub` — gcd divisibility from full divisibility
2. `gcd_dvd_sub_of_congr` — pairwise condition transfers through solution
3. `lcm_gcd_dvd_gcd_lcm` — easy direction of distributive law
4. `gcd_lcm_dvd_lcm_gcd` — hard direction (PROVED via Bézout decomposition)
5. `ed_crt_three_sufficient` — 3-moduli CRT sufficiency
6. `ed_crt_three_iff` — full iff for 3 moduli
7. `ed_crt_three_unique` — uniqueness for 3 moduli

### History: 1 axiom (gcd_lcm_distrib) → 1 sorry → 0 sorries (fully verified)
### Status: COMPLETE — all theorems machine-checked, 0 axioms, 0 sorries
### Proof technique: Direct Bézout expansion + coprime factoring through gcd(a,b) and gcd(gcd(a,b),c)
-/

end ChineseRemainderNonCoprimeOQ03
