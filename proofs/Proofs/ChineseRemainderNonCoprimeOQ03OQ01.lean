/-
  CRT Non-Coprime OQ-03-OQ-01: n-Moduli Generalization by Induction

  Answers the first open question of ChineseRemainderNonCoprimeOQ03:
  generalize the non-coprime Chinese Remainder Theorem from a fixed number
  of moduli (2, 3) to an ARBITRARY finite family, organized as a list of
  (modulus, residue) pairs over a EuclideanDomain R.

  Main results (0 axioms, 0 sorries):
  * `crt_list_iff`        : the system { x ≡ aᵢ [mod mᵢ] } is solvable
                             ↔ for every pair i, j: gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ).
  * `crt_list_sufficient` : the (hard) sufficiency direction, by induction
                             on the list, combining the head modulus with the
                             lcm of the tail via the GCD–LCM distributive law.
  * `crt_list_necessary`  : the (easy) necessity direction.
  * `crt_list_unique`     : any two solutions agree modulo the lcm of all moduli.

  The engine is a generalized GCD–LCM distributive law over a list,
  `gcd_lcmList_dvd : gcd (lcmList l) c ∣ lcmList (l.map (gcd · c))`,
  obtained by a one-step induction from the binary distributive law.

  The binary hard direction `gcd_lcm_dvd_lcm_gcd` (gcd(lcm a b, c) ∣
  lcm(gcd a c, gcd b c)) is reproduced verbatim from the parent entry
  ChineseRemainderNonCoprimeOQ03.lean (where it was proved, 0 axioms) so
  that this file is self-contained; the genuinely new contribution is the
  n-fold generalization (lcmList infrastructure + the list-indexed CRT).

  Parent: ChineseRemainderNonCoprimeOQ03.lean (0 axioms, 0 sorries)
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace ChineseRemainderNonCoprimeOQ03OQ01

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-
## Part 0: Binary CRT core and the binary GCD–LCM distributive law

`ed_crt_sufficient` and `gcd_lcm_dvd_lcm_gcd` are reproduced from the parent
entry ChineseRemainderNonCoprimeOQ03 (verified there, 0 axioms). They serve as
imported infrastructure for the new n-fold results below.
-/

/-- Binary sufficiency: if gcd(m,n) ∣ (a - b), construct a solution via Bézout. -/
theorem ed_crt_sufficient {m n a b : R}
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

/-- Hard direction of the GCD–LCM distributive law:
    gcd(lcm(a,b), c) divides lcm(gcd(a,c), gcd(b,c)).
    Reproduced verbatim from the parent (ChineseRemainderNonCoprimeOQ03). -/
theorem gcd_lcm_dvd_lcm_gcd (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) := by
  by_cases hg : EuclideanDomain.gcd a b = 0
  · have ha : a = 0 := by
      have := EuclideanDomain.gcd_dvd_left a b; rw [hg] at this
      exact (zero_dvd_iff.mp this)
    have hb : b = 0 := by
      have := EuclideanDomain.gcd_dvd_right a b; rw [hg] at this
      exact (zero_dvd_iff.mp this)
    rw [ha, hb]
    have h0 : EuclideanDomain.lcm (0 : R) 0 = 0 := by
      simp [EuclideanDomain.lcm]
    rw [h0]
    exact EuclideanDomain.dvd_lcm_left _ _
  · set g := EuclideanDomain.gcd a b with hg_def
    obtain ⟨α, hα⟩ := EuclideanDomain.gcd_dvd_left a b
    obtain ⟨β, hβ⟩ := EuclideanDomain.gcd_dvd_right a b
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
    set d' := EuclideanDomain.gcd g c with hd'_def
    have hd'_ne : d' ≠ 0 := by
      intro h; apply hg
      exact (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_left g c))
    obtain ⟨g', hg'⟩ := EuclideanDomain.gcd_dvd_left g c
    obtain ⟨c', hc'⟩ := EuclideanDomain.gcd_dvd_right g c
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
    obtain ⟨k₁, hk₁⟩ := EuclideanDomain.dvd_lcm_left
      (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
    obtain ⟨k₂, hk₂⟩ := EuclideanDomain.dvd_lcm_right
      (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c)
    have hM1 : EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) =
        (EuclideanDomain.gcdA a c * k₁) * a +
        (EuclideanDomain.gcdB a c * k₁) * c := by
      conv_lhs => rw [hk₁, EuclideanDomain.gcd_eq_gcd_ab a c]
      ring
    have hM2 : EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) =
        (EuclideanDomain.gcdA b c * k₂) * b +
        (EuclideanDomain.gcdB b c * k₂) * c := by
      conv_lhs => rw [hk₂, EuclideanDomain.gcd_eq_gcd_ab b c]
      ring
    set r₁ := EuclideanDomain.gcdA a c * k₁
    set s₁ := EuclideanDomain.gcdB a c * k₁
    set r₂ := EuclideanDomain.gcdA b c * k₂
    set s₂ := EuclideanDomain.gcdB b c * k₂
    have hrab : r₁ * a - r₂ * b = (s₂ - s₁) * c := by
      have heq := hM1.symm.trans hM2
      calc r₁ * a - r₂ * b
          = (r₁ * a + s₁ * c) - (r₂ * b + s₂ * c) + (s₂ - s₁) * c := by ring
        _ = (r₂ * b + s₂ * c) - (r₂ * b + s₂ * c) + (s₂ - s₁) * c := by rw [heq]
        _ = (s₂ - s₁) * c := by ring
    have hgrab : g * (r₁ * α - r₂ * β) = (s₂ - s₁) * c := by
      calc g * (r₁ * α - r₂ * β)
          = r₁ * (g * α) - r₂ * (g * β) := by ring
        _ = r₁ * a - r₂ * b := by rw [← hα, ← hβ]
        _ = _ := hrab
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
    have hc'_dvd : c' ∣ (r₁ * α - r₂ * β) := by
      obtain ⟨u, v, huv⟩ := hcop_gc
      obtain ⟨k, hk⟩ : c' ∣ g' * (r₁ * α - r₂ * β) := by
        rw [hgrab']; exact dvd_mul_left c' _
      exact ⟨u * k + v * (r₁ * α - r₂ * β), by
        calc r₁ * α - r₂ * β
            = (r₁ * α - r₂ * β) * (u * g' + v * c') := by rw [huv, mul_one]
          _ = u * (g' * (r₁ * α - r₂ * β)) + v * c' * (r₁ * α - r₂ * β) := by ring
          _ = u * (c' * k) + v * c' * (r₁ * α - r₂ * β) := by rw [hk]
          _ = c' * (u * k + v * (r₁ * α - r₂ * β)) := by ring⟩
    obtain ⟨w, hw⟩ := hc'_dvd
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
    have hr₁ : r₁ = m * β + p_b * (c' * w) := by
      calc r₁ = (r₁ - p_b * (c' * w)) + p_b * (c' * w) := by ring
        _ = β * m + p_b * (c' * w) := by rw [hm]
        _ = m * β + p_b * (c' * w) := by ring
    have hcg : c' * g = c * g' := by
      calc c' * g = c' * (d' * g') := by rw [hg']
        _ = (d' * c') * g' := by ring
        _ = c * g' := by rw [← hc']
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
    have hd_gab : EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣ g * α * β := by
      refine dvd_trans (EuclideanDomain.gcd_dvd_left _ _) ?_
      refine EuclideanDomain.lcm_dvd ?_ ?_
      · rw [hα]; exact dvd_mul_right _ _
      · exact ⟨α, by calc g * α * β = g * β * α := by ring
          _ = b * α := by rw [← hβ]⟩
    rw [hM_decomp]
    exact dvd_add
      (hd_gab.mul_left m)
      ((EuclideanDomain.gcd_dvd_right (EuclideanDomain.lcm a b) c).mul_left _)

/-
## Part I: lcm over a list of moduli
-/

/-- lcm of all elements of a list (empty list ↦ 1). -/
def lcmList (l : List R) : R := l.foldr EuclideanDomain.lcm 1

@[simp] theorem lcmList_nil : lcmList ([] : List R) = 1 := rfl

@[simp] theorem lcmList_cons (m : R) (l : List R) :
    lcmList (m :: l) = EuclideanDomain.lcm m (lcmList l) := rfl

/-- Each element of the list divides the list lcm. -/
theorem dvd_lcmList {z : R} : ∀ {l : List R}, z ∈ l → z ∣ lcmList l
  | m :: rest, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact EuclideanDomain.dvd_lcm_left _ _
      · exact dvd_trans (dvd_lcmList h') (EuclideanDomain.dvd_lcm_right _ _)

/-- If every element of the list divides `t`, so does the list lcm. -/
theorem lcmList_dvd {l : List R} {t : R} (h : ∀ z ∈ l, z ∣ t) : lcmList l ∣ t := by
  induction l with
  | nil => exact one_dvd t
  | cons m rest ih =>
      rw [lcmList_cons]
      exact EuclideanDomain.lcm_dvd (h m (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun z hz => h z (List.mem_cons.mpr (Or.inr hz))))

/-
## Part II: Generalized GCD–LCM distributive law over a list

`gcd (lcmList l) c` divides `lcmList (l.map (· gcd-with c))`, by a one-step
induction from the binary `gcd_lcm_dvd_lcm_gcd`.
-/
theorem gcd_lcmList_dvd (c : R) (l : List R) :
    EuclideanDomain.gcd (lcmList l) c ∣
    lcmList (l.map (fun m => EuclideanDomain.gcd m c)) := by
  induction l with
  | nil =>
      show EuclideanDomain.gcd (1 : R) c ∣ (1 : R)
      exact EuclideanDomain.gcd_dvd_left 1 c
  | cons m rest ih =>
      rw [lcmList_cons, List.map_cons, lcmList_cons]
      refine dvd_trans (gcd_lcm_dvd_lcm_gcd m (lcmList rest) c) ?_
      exact EuclideanDomain.lcm_dvd (EuclideanDomain.dvd_lcm_left _ _)
        (dvd_trans ih (EuclideanDomain.dvd_lcm_right _ _))

/-
## Part III: n-Moduli (list-indexed) Chinese Remainder Theorem

A system is a list `l : List (R × R)` of (modulus, residue) pairs.
-/

/-- `x` solves the system: for each pair (m, a), m ∣ (x - a). -/
def Solves (x : R) (l : List (R × R)) : Prop := ∀ p ∈ l, p.1 ∣ (x - p.2)

/-- Pairwise compatibility: for every pair of entries, gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ). -/
def Compat (l : List (R × R)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, EuclideanDomain.gcd p.1 q.1 ∣ (p.2 - q.2)

/-- Necessity: a solvable system is pairwise compatible. -/
theorem crt_list_necessary {l : List (R × R)} (h : ∃ x, Solves x l) : Compat l := by
  obtain ⟨x, hx⟩ := h
  intro p hp q hq
  have h1 : p.1 ∣ (x - p.2) := hx p hp
  have h2 : q.1 ∣ (x - q.2) := hx q hq
  have d1 : EuclideanDomain.gcd p.1 q.1 ∣ (x - p.2) :=
    dvd_trans (EuclideanDomain.gcd_dvd_left _ _) h1
  have d2 : EuclideanDomain.gcd p.1 q.1 ∣ (x - q.2) :=
    dvd_trans (EuclideanDomain.gcd_dvd_right _ _) h2
  have hsub : EuclideanDomain.gcd p.1 q.1 ∣ ((x - q.2) - (x - p.2)) := dvd_sub d2 d1
  rwa [show (x - q.2) - (x - p.2) = p.2 - q.2 from by ring] at hsub

/-- Sufficiency (hard direction): a pairwise-compatible system is solvable.
    Proof by induction on the list. To combine the head modulus `m₀` with a
    solution `x₀` of the tail (whose combined modulus is `M = lcm` of the tail
    moduli), we show `gcd(M, m₀) ∣ (a₀ - x₀)`: each tail modulus `mᵢ` gives
    `gcd(m₀, mᵢ) ∣ (a₀ - x₀)`, and the generalized distributive law upgrades
    the lcm of those gcds — which divides `(a₀ - x₀)` — to `gcd(M, m₀)`. -/
theorem crt_list_sufficient {l : List (R × R)} (h : Compat l) : ∃ x, Solves x l := by
  induction l with
  | nil => exact ⟨0, fun p hp => by simp at hp⟩
  | cons p rest ih =>
      have hcompat_rest : Compat rest := fun a ha b hb =>
        h a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb))
      obtain ⟨x₀, hx₀⟩ := ih hcompat_rest
      -- head is compatible with every tail entry
      have hhead : ∀ q ∈ rest, EuclideanDomain.gcd p.1 q.1 ∣ (p.2 - q.2) :=
        fun q hq => h p (List.mem_cons.mpr (Or.inl rfl)) q (List.mem_cons.mpr (Or.inr hq))
      -- transfer through the tail solution: gcd(m₀, mᵢ) ∣ (a₀ - x₀)
      have hpx0 : ∀ q ∈ rest, EuclideanDomain.gcd p.1 q.1 ∣ (p.2 - x₀) := by
        intro q hq
        have hq_sol : q.1 ∣ (x₀ - q.2) := hx₀ q hq
        have hg2 : EuclideanDomain.gcd p.1 q.1 ∣ (x₀ - q.2) :=
          dvd_trans (EuclideanDomain.gcd_dvd_right _ _) hq_sol
        have hg1 : EuclideanDomain.gcd p.1 q.1 ∣ (p.2 - q.2) := hhead q hq
        have hsub : EuclideanDomain.gcd p.1 q.1 ∣ ((p.2 - q.2) - (x₀ - q.2)) :=
          dvd_sub hg1 hg2
        rwa [show (p.2 - q.2) - (x₀ - q.2) = p.2 - x₀ from by ring] at hsub
      -- distributive law: gcd(M, m₀) ∣ (a₀ - x₀), where M = lcm of tail moduli
      have hgcdM : EuclideanDomain.gcd (lcmList (rest.map Prod.fst)) p.1 ∣ (p.2 - x₀) := by
        refine dvd_trans (gcd_lcmList_dvd p.1 (rest.map Prod.fst)) ?_
        apply lcmList_dvd
        intro z hz
        obtain ⟨w, hw_mem, rfl⟩ := List.mem_map.mp hz
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw_mem
        -- need gcd q.1 p.1 ∣ (p.2 - x₀); bridge gcd q.1 p.1 ∣ gcd p.1 q.1
        have hbridge : EuclideanDomain.gcd q.1 p.1 ∣ EuclideanDomain.gcd p.1 q.1 :=
          EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_right _ _)
            (EuclideanDomain.gcd_dvd_left _ _)
        exact dvd_trans hbridge (hpx0 q hq)
      -- orient for the 2-moduli solver (a₀ on the second slot)
      have hgcdM' : EuclideanDomain.gcd (lcmList (rest.map Prod.fst)) p.1 ∣ (x₀ - p.2) := by
        have h' := dvd_neg.mpr hgcdM
        rwa [neg_sub] at h'
      obtain ⟨x, hxM, hxp⟩ := ed_crt_sufficient hgcdM'
      -- hxM : M ∣ (x - x₀), hxp : m₀ ∣ (x - a₀)
      refine ⟨x, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact hxp
      · have hs1_dvd_M : s.1 ∣ lcmList (rest.map Prod.fst) :=
          dvd_lcmList (List.mem_map.mpr ⟨s, hs', rfl⟩)
        have hs_xx0 : s.1 ∣ (x - x₀) := dvd_trans hs1_dvd_M hxM
        have hs_x0 : s.1 ∣ (x₀ - s.2) := hx₀ s hs'
        rw [show x - s.2 = (x - x₀) + (x₀ - s.2) from by ring]
        exact dvd_add hs_xx0 hs_x0

/-- The full iff for n moduli: solvability ↔ pairwise GCD compatibility. -/
theorem crt_list_iff {l : List (R × R)} :
    (∃ x, Solves x l) ↔ Compat l :=
  ⟨crt_list_necessary, crt_list_sufficient⟩

/-- Uniqueness: any two solutions agree modulo the lcm of all moduli. -/
theorem crt_list_unique {l : List (R × R)} {x y : R}
    (hx : Solves x l) (hy : Solves y l) :
    lcmList (l.map Prod.fst) ∣ (x - y) := by
  apply lcmList_dvd
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  have h1 : p.1 ∣ (x - p.2) := hx p hp
  have h2 : p.1 ∣ (y - p.2) := hy p hp
  have hsub : p.1 ∣ ((x - p.2) - (y - p.2)) := dvd_sub h1 h2
  rwa [show (x - p.2) - (y - p.2) = x - y from by ring] at hsub

/-
## Summary

### Theorems proved (0 axioms, 0 sorries):
1. `ed_crt_sufficient`     — binary CRT sufficiency (from parent OQ-03)
2. `gcd_lcm_dvd_lcm_gcd`   — binary GCD–LCM distributive law (from parent OQ-03)
3. `dvd_lcmList`           — each modulus divides the list lcm
4. `lcmList_dvd`           — list lcm divides any common multiple
5. `gcd_lcmList_dvd`       — NEW: generalized GCD–LCM distributive law (n-fold)
6. `crt_list_necessary`    — NEW: necessity for n moduli
7. `crt_list_sufficient`   — NEW: sufficiency for n moduli (induction + distributive law)
8. `crt_list_iff`          — NEW: full iff for n moduli
9. `crt_list_unique`       — NEW: uniqueness modulo lcm of all moduli

### Status: COMPLETE — answers OQ-03's first open question
### Technique: induction on the modulus list; combine head with lcm of tail via
### the generalized GCD–LCM distributive law (built from the binary case).
-/

end ChineseRemainderNonCoprimeOQ03OQ01
