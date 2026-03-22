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

/-
## Helpers for the hard direction
-/

/-- If g ≠ 0, a = g*α, b = g*β, and gcd(a,b) = g, then IsCoprime α β. -/
private theorem coprime_of_gcd {a b g α β : R} (hg : g ≠ 0)
    (hα : a = g * α) (hβ : b = g * β)
    (hgcd : EuclideanDomain.gcd a b = g) :
    IsCoprime α β := by
  have hbez := EuclideanDomain.gcd_eq_gcd_ab a b
  refine ⟨EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b, ?_⟩
  apply mul_left_cancel₀ hg
  rw [mul_one]
  calc g = EuclideanDomain.gcd a b := hgcd.symm
    _ = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b := hbez
    _ = g * (α * EuclideanDomain.gcdA a b) + g * (β * EuclideanDomain.gcdB a b) := by
        rw [hα, hβ]; ring
    _ = g * (α * EuclideanDomain.gcdA a b + β * EuclideanDomain.gcdB a b) := by ring

/-- IsCoprime α β implies IsCoprime (gcd α c) (gcd β c). -/
private theorem isCoprime_gcd_right {α β c : R} (hcop : IsCoprime α β) :
    IsCoprime (EuclideanDomain.gcd α c) (EuclideanDomain.gcd β c) := by
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨α', hα'⟩ := EuclideanDomain.gcd_dvd_left α c
  obtain ⟨β', hβ'⟩ := EuclideanDomain.gcd_dvd_left β c
  exact ⟨u * α', v * β', by
    calc (u * α') * EuclideanDomain.gcd α c + (v * β') * EuclideanDomain.gcd β c
        = u * (EuclideanDomain.gcd α c * α') + v * (EuclideanDomain.gcd β c * β') := by ring
      _ = u * α + v * β := by rw [← hα', ← hβ']
      _ = 1 := huv⟩

/-- IsCoprime k n → gcd(k*m, n) | gcd(m, n): coprime factor cancels from gcd. -/
private theorem gcd_coprime_cancel {k m n : R} (hcop : IsCoprime k n) :
    EuclideanDomain.gcd (k * m) n ∣ EuclideanDomain.gcd m n := by
  have h1 : EuclideanDomain.gcd (k * m) n ∣ (k * m) := EuclideanDomain.gcd_dvd_left _ _
  have h2 : EuclideanDomain.gcd (k * m) n ∣ n := EuclideanDomain.gcd_dvd_right _ _
  have hcop2 : IsCoprime k (EuclideanDomain.gcd (k * m) n) :=
    hcop.coprime_dvd_right h2
  have h3 : EuclideanDomain.gcd (k * m) n ∣ m := hcop2.symm.dvd_of_dvd_mul_left h1
  exact EuclideanDomain.dvd_gcd h3 h2

/-- gcd(k*a, k*b) | k * gcd(a, b), via Bézout's identity. -/
private theorem gcd_mul_dvd {k a b : R} :
    EuclideanDomain.gcd (k * a) (k * b) ∣ k * EuclideanDomain.gcd a b := by
  have hbez := EuclideanDomain.gcd_eq_gcd_ab a b
  have : k * EuclideanDomain.gcd a b =
      k * a * EuclideanDomain.gcdA a b + k * b * EuclideanDomain.gcdB a b := by
    rw [hbez]; ring
  rw [this]
  exact dvd_add
    ((EuclideanDomain.gcd_dvd_left _ _).mul_right _)
    ((EuclideanDomain.gcd_dvd_right _ _).mul_right _)

/-- Monotonicity: if a | b, then gcd(a, c) | gcd(b, c). -/
private theorem gcd_dvd_gcd_of_dvd_left {a b c : R} (h : a ∣ b) :
    EuclideanDomain.gcd a c ∣ EuclideanDomain.gcd b c :=
  EuclideanDomain.dvd_gcd
    (dvd_trans (EuclideanDomain.gcd_dvd_left a c) h)
    (EuclideanDomain.gcd_dvd_right a c)

/-- Hard direction of the GCD-LCM distributive law:
    gcd(lcm(a,b), c) divides lcm(gcd(a,c), gcd(b,c)).

    Proof strategy: Factor a = g*α, b = g*β (coprime) where g = gcd(a,b),
    and g = δ*γ, c = δ*ε (coprime) where δ = gcd(g,c).
    Then d = gcd(lcm(a,b), c) divides δ*gcd(α,ε)*gcd(β,ε) (Part 1),
    and δ*gcd(α,ε)*gcd(β,ε) divides M = lcm(gcd(a,c), gcd(b,c)) (Part 2).
    Part 2 uses IsCoprime(gcd(α,ε), gcd(β,ε)) to cancel within the lcm. -/
theorem gcd_lcm_dvd_lcm_gcd (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) := by
  -- Zero cases
  by_cases ha : a = 0
  · -- gcd(lcm(0,b), c) | lcm(gcd(0,c), gcd(b,c))
    -- gcd(...) | c by gcd_dvd_right; gcd(0,c) = c; c | lcm(c, ...) by dvd_lcm_left
    subst ha; rw [EuclideanDomain.gcd_zero_left]
    exact dvd_trans (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.dvd_lcm_left _ _)
  by_cases hb : b = 0
  · subst hb; rw [EuclideanDomain.gcd_zero_right]
    exact dvd_trans (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.dvd_lcm_right _ _)
  by_cases hc : c = 0
  · subst hc; simp only [EuclideanDomain.gcd_zero_right]
  -- Nonzero case: factor through gcd(a,b) = g
  -- g | a and g | b with a = g*α, b = g*β, IsCoprime α β
  have hg_ne : EuclideanDomain.gcd a b ≠ 0 := by
    intro h; exact ha (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_left a b))
  obtain ⟨α, hα⟩ := EuclideanDomain.gcd_dvd_left a b
  obtain ⟨β, hβ⟩ := EuclideanDomain.gcd_dvd_right a b
  have hcop_αβ : IsCoprime α β := coprime_of_gcd hg_ne hα hβ rfl
  -- Factor gcd(a,b) and c through δ = gcd(gcd(a,b), c)
  -- gcd(a,b) = δ*γ, c = δ*ε, IsCoprime γ ε
  have hδ_ne : EuclideanDomain.gcd (EuclideanDomain.gcd a b) c ≠ 0 := by
    intro h
    exact hg_ne (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_left _ c))
  obtain ⟨γ, hγ⟩ := EuclideanDomain.gcd_dvd_left (EuclideanDomain.gcd a b) c
  obtain ⟨ε, hε⟩ := EuclideanDomain.gcd_dvd_right (EuclideanDomain.gcd a b) c
  have hcop_γε : IsCoprime γ ε := coprime_of_gcd hδ_ne hγ hε rfl
  -- Abbreviations (let, not set, to avoid syntactic issues)
  let δ := EuclideanDomain.gcd (EuclideanDomain.gcd a b) c
  let X := EuclideanDomain.gcd α ε
  let Y := EuclideanDomain.gcd β ε
  -- Key identity: a = δ*γ*α (from hα and hγ)
  have ha_eq : a = δ * γ * α := by rw [hα, hγ]; ring
  have hb_eq : b = δ * γ * β := by rw [hβ, hγ]; ring
  have hc_eq : c = δ * ε := hε
  -- Part 1: gcd(lcm(a,b), c) | δ * (X * Y)
  -- Step 1a: g*α*β = δ*γ*α*β is a common multiple of a and b
  have ha_dvd : a ∣ δ * γ * α * β := ⟨β, by rw [ha_eq]; ring⟩
  have hb_dvd : b ∣ δ * γ * α * β := ⟨α, by rw [hb_eq]; ring⟩
  have hlcm_dvd : EuclideanDomain.lcm a b ∣ δ * γ * (α * β) :=
    EuclideanDomain.lcm_dvd (by rwa [show δ * γ * (α * β) = δ * γ * α * β from by ring])
      (by rwa [show δ * γ * (α * β) = δ * γ * α * β from by ring])
  -- Step 1b: d | gcd(δ*(γ*α*β), δ*ε)
  have hd_dvd_gcd1 :
      EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
      EuclideanDomain.gcd (δ * (γ * (α * β))) (δ * ε) := by
    apply EuclideanDomain.dvd_gcd
    · exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _)
        (by rwa [show δ * (γ * (α * β)) = δ * γ * (α * β) from by ring])
    · rw [show δ * ε = c from hc_eq.symm]; exact EuclideanDomain.gcd_dvd_right _ _
  -- Step 1c: pull out δ, cancel γ, use coprime product
  have part1 : EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ δ * (X * Y) :=
    calc EuclideanDomain.gcd (EuclideanDomain.lcm a b) c
        ∣ EuclideanDomain.gcd (δ * (γ * (α * β))) (δ * ε) := hd_dvd_gcd1
      _ ∣ δ * EuclideanDomain.gcd (γ * (α * β)) ε := gcd_mul_dvd
      _ ∣ δ * EuclideanDomain.gcd (α * β) ε :=
          mul_dvd_mul_left δ (gcd_coprime_cancel hcop_γε)
      _ ∣ δ * EuclideanDomain.gcd (EuclideanDomain.lcm α β) ε :=
          mul_dvd_mul_left δ (gcd_dvd_gcd_of_dvd_left
            (hcop_αβ.mul_dvd (EuclideanDomain.dvd_lcm_left α β)
              (EuclideanDomain.dvd_lcm_right α β)))
      _ ∣ δ * (EuclideanDomain.gcd α ε * EuclideanDomain.gcd β ε) :=
          mul_dvd_mul_left δ (gcd_lcm_dvd_prod_gcd α β ε)
  -- Part 2: δ * (X * Y) | lcm(gcd(a,c), gcd(b,c))
  -- Step 2a: δ*X | a and δ*X | c, hence δ*X | gcd(a,c)
  have hδX_dvd_a : δ * X ∣ a := by
    rw [ha_eq]; show δ * EuclideanDomain.gcd α ε ∣ δ * γ * α
    calc δ * EuclideanDomain.gcd α ε
        ∣ δ * α := mul_dvd_mul_left δ (EuclideanDomain.gcd_dvd_left α ε)
      _ ∣ δ * γ * α := by rw [mul_assoc]; exact dvd_mul_of_dvd_right (dvd_refl _) γ
  have hδX_dvd_c : δ * X ∣ c := by
    rw [hc_eq]; exact mul_dvd_mul_left δ (EuclideanDomain.gcd_dvd_right α ε)
  have hδX_dvd_p : δ * X ∣ EuclideanDomain.gcd a c :=
    EuclideanDomain.dvd_gcd hδX_dvd_a hδX_dvd_c
  -- Step 2b: δ*Y | b and δ*Y | c, hence δ*Y | gcd(b,c)
  have hδY_dvd_b : δ * Y ∣ b := by
    rw [hb_eq]; show δ * EuclideanDomain.gcd β ε ∣ δ * γ * β
    calc δ * EuclideanDomain.gcd β ε
        ∣ δ * β := mul_dvd_mul_left δ (EuclideanDomain.gcd_dvd_left β ε)
      _ ∣ δ * γ * β := by rw [mul_assoc]; exact dvd_mul_of_dvd_right (dvd_refl _) γ
  have hδY_dvd_c : δ * Y ∣ c := by
    rw [hc_eq]; exact mul_dvd_mul_left δ (EuclideanDomain.gcd_dvd_right β ε)
  have hδY_dvd_q : δ * Y ∣ EuclideanDomain.gcd b c :=
    EuclideanDomain.dvd_gcd hδY_dvd_b hδY_dvd_c
  -- Step 2c: δ*X and δ*Y divide M = lcm(gcd(a,c), gcd(b,c))
  have hδX_dvd_M : δ * X ∣ EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) :=
    dvd_trans hδX_dvd_p (EuclideanDomain.dvd_lcm_left _ _)
  have hδY_dvd_M : δ * Y ∣ EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) :=
    dvd_trans hδY_dvd_q (EuclideanDomain.dvd_lcm_right _ _)
  -- Step 2d: M = (δ*X)*m₁ for some m₁
  obtain ⟨m₁, hm₁⟩ := hδX_dvd_M
  -- Step 2e: Y | X*m₁ (cancel δ from δ*Y | δ*X*m₁)
  have hY_dvd_Xm : Y ∣ X * m₁ := by
    have h : δ * Y ∣ δ * (X * m₁) := by
      rw [show δ * (X * m₁) = δ * X * m₁ from by ring]; rw [← hm₁]; exact hδY_dvd_M
    exact (mul_dvd_mul_iff_left hδ_ne).mp h
  -- Step 2f: IsCoprime X Y, so Y | m₁ (Euclid's lemma)
  have hcop_XY : IsCoprime X Y := isCoprime_gcd_right hcop_αβ
  have hY_dvd_m₁ : Y ∣ m₁ := by
    exact hcop_XY.symm.dvd_of_dvd_mul_right hY_dvd_Xm
  -- Step 2g: δ*(X*Y) | M
  obtain ⟨m₂, hm₂⟩ := hY_dvd_m₁
  have part2 : δ * (X * Y) ∣ EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) := by
    refine ⟨m₂, ?_⟩; rw [hm₁, hm₂]; ring
  -- Conclusion: chain Part 1 and Part 2
  exact dvd_trans part1 part2

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

### Theorems proved (0 axioms, 0 sorries — FULLY VERIFIED):
1. `gcd_dvd_of_dvd_sub` — gcd divisibility from full divisibility
2. `gcd_dvd_sub_of_congr` — pairwise condition transfers through solution
3. `lcm_gcd_dvd_gcd_lcm` — easy direction of distributive law
4. `gcd_lcm_dvd_lcm_gcd` — hard direction (GCD-LCM distributive law)
5. `ed_crt_three_sufficient` — 3-moduli CRT sufficiency
6. `ed_crt_three_iff` — full iff for 3 moduli
7. `ed_crt_three_unique` — uniqueness for 3 moduli

### History: 0 sorries, 1 axiom → 1 sorry, 0 axioms → 0 sorries, 0 axioms
### Status: FULLY VERIFIED — all theorems proved, no axioms, no sorries
### Proof of distributive law: coprime factoring + Euclid's lemma (no UFD needed)
-/

end ChineseRemainderNonCoprimeOQ03
