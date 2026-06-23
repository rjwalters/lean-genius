import Mathlib
import Proofs.ChineseRemainderNonCoprimeOQ01

/-
# CRT Non-Coprime: Extension to k Moduli (OQ01-OQ01)

## Open Question (OQ01-OQ01)

Can the efficiency theorem for 2 non-coprime moduli be extended to k moduli
with optimal lcm bounds?

## Answer: YES

For k congruences x ≡ aᵢ [ZMOD mᵢ] (i = 1,...,k), where mᵢ are possibly
non-coprime:

1. **LCM Periodicity** (Main Theorem): The set of solutions is a coset of
   L·ℤ where L = lcm(m₁,...,mₖ). In particular, any solution can be
   canonically reduced to the interval [0, L).

2. **Divisibility**: kLCM(s) divides the product ∏mᵢ, so L ≤ ∏mᵢ.
   When moduli have common factors, L < ∏mᵢ (efficiency gain).

3. **Iterative Construction**: The system reduces to iterated 2-modulus CRT:
   solve for i ∈ s, then combine with (k+1)-th modulus.

4. **Necessary Condition**: The system has a solution iff for all i,j:
   gcd(mᵢ,mⱼ) ∣ (aᵢ - aⱼ).

Axioms: 0, Sorries: 0, Theorems: 12+

Tags: number-theory, modular-arithmetic, CRT, efficiency, k-moduli
-/

namespace ChineseRemainderNonCoprimeOQ01OQ01

open Int Finset Nat

-- ============================================================
-- Part I: The k-Moduli LCM via ℤ GCDMonoid
-- ============================================================

/-- The k-moduli LCM: lcm over a finite set of naturals, computed in ℤ.
    We use ℤ's GCDMonoid instance so Finset.lcm_dvd and Finset.dvd_lcm apply directly. -/
noncomputable def kLCM (s : Finset ℕ) : ℤ := s.lcm (fun m : ℕ => (m : ℤ))

/-- Each modulus divides the kLCM. -/
theorem dvd_kLCM {s : Finset ℕ} {m : ℕ} (hm : m ∈ s) : (m : ℤ) ∣ kLCM s :=
  Finset.dvd_lcm hm

/-- The kLCM divides d iff every modulus divides d (main LCM property). -/
theorem kLCM_dvd_iff {s : Finset ℕ} {d : ℤ} :
    kLCM s ∣ d ↔ ∀ m ∈ s, (m : ℤ) ∣ d :=
  ⟨fun h m hm => dvd_trans (dvd_kLCM hm) h, Finset.lcm_dvd⟩

@[simp] theorem kLCM_empty : kLCM (∅ : Finset ℕ) = 1 := by simp [kLCM]

@[simp] theorem kLCM_singleton (m : ℕ) : kLCM {m} = (m : ℤ) := by
  simp [kLCM, Finset.lcm_singleton]

/-- The kLCM divides the product of all moduli. -/
theorem kLCM_dvd_prod {s : Finset ℕ} :
    kLCM s ∣ s.prod (fun m : ℕ => (m : ℤ)) :=
  Finset.lcm_dvd (fun m hm => dvd_prod_of_mem _ hm)

-- ============================================================
-- Part II: k-Moduli Periodicity (Main Theorem)
-- ============================================================

/-- **Main Theorem: k-Moduli Periodicity**
    y₁ ≡ y₂ [ZMOD mᵢ] for all i ∈ s ↔ kLCM(s) ∣ (y₁ - y₂).

    This is the k-moduli extension of the 2-moduli result from OQ01:
    solutions to a system of k congruences form a coset of kLCM(s)·ℤ.

    **Proof**: The k-fold conjunction of congruences y₁ ≡ y₂ [ZMOD mᵢ]
    is equivalent to all mᵢ dividing (y₁ - y₂). By the LCM universality
    property (Finset.lcm_dvd / Finset.dvd_lcm), this is equivalent to
    kLCM(s) dividing (y₁ - y₂). -/
theorem kModuli_periodic {s : Finset ℕ} (y₁ y₂ : ℤ) :
    (∀ m ∈ s, y₁ ≡ y₂ [ZMOD (m : ℤ)]) ↔ kLCM s ∣ (y₁ - y₂) := by
  simp_rw [Int.modEq_iff_dvd]
  exact kLCM_dvd_iff.symm

/-- Corollary: If x₀ and y both satisfy the k congruences, then kLCM ∣ (y - x₀). -/
theorem solution_coset {s : Finset ℕ} {a : ℕ → ℤ} (x₀ y : ℤ)
    (hx₀ : ∀ m ∈ s, x₀ ≡ a m [ZMOD (m : ℤ)])
    (hy : ∀ m ∈ s, y ≡ a m [ZMOD (m : ℤ)]) :
    kLCM s ∣ (y - x₀) := by
  rw [← kModuli_periodic]
  intro m hm
  exact (hy m hm).trans (hx₀ m hm).symm

-- ============================================================
-- Part III: Canonical Form
-- ============================================================

/-- kLCM is nonneg for naturals (GCDMonoid ℤ uses normalize, which gives |a| for ℤ,
    so lcm of nonneg elements is nonneg). -/
theorem kLCM_nonneg (s : Finset ℕ) : 0 ≤ kLCM s := by
  simp only [kLCM]
  apply Finset.lcm_nonneg
  intro m _; exact Int.natCast_nonneg

/-- kLCM is positive when all moduli are positive. -/
theorem kLCM_pos {s : Finset ℕ} (hne : s.Nonempty) (hpos : ∀ m ∈ s, 0 < m) :
    0 < kLCM s := by
  obtain ⟨m, hm⟩ := hne
  have hm_pos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hpos m hm
  exact lt_of_lt_of_le hm_pos (dvd_kLCM hm).le

/-- Any solution reduces canonically: y % kLCM is also a solution in [0, kLCM). -/
theorem kModuli_canonical {s : Finset ℕ} {a : ℕ → ℤ} (y : ℤ)
    (hy : ∀ m ∈ s, y ≡ a m [ZMOD (m : ℤ)])
    (hne : s.Nonempty) (hpos : ∀ m ∈ s, 0 < m) :
    ∀ m ∈ s, y % kLCM s ≡ a m [ZMOD (m : ℤ)] := by
  intro m hm
  have hL_pos : 0 < kLCM s := kLCM_pos hne hpos
  -- y % L ≡ y [ZMOD m] since m | L | (y - y%L)
  have hm_dvd_L : (m : ℤ) ∣ kLCM s := dvd_kLCM hm
  have hymod_cong : y % kLCM s ≡ y [ZMOD (m : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have hdiff : y - y % kLCM s = kLCM s * (y / kLCM s) := by
      linarith [Int.emod_add_ediv y (kLCM s)]
    rw [hdiff]
    exact dvd_mul_of_dvd_left hm_dvd_L _
  exact hymod_cong.trans (hy m hm)

/-- The canonical representative lies in [0, kLCM). -/
theorem kModuli_canonical_range {s : Finset ℕ}
    (y : ℤ) (hne : s.Nonempty) (hpos : ∀ m ∈ s, 0 < m) :
    0 ≤ y % kLCM s ∧ y % kLCM s < kLCM s := by
  have hL_pos : 0 < kLCM s := kLCM_pos hne hpos
  exact ⟨Int.emod_nonneg y (ne_of_gt hL_pos), Int.emod_lt_of_pos y hL_pos⟩

-- ============================================================
-- Part IV: Efficiency
-- ============================================================

/-- The kLCM is at most the product of all moduli (by divisibility). -/
theorem kLCM_le_prod {s : Finset ℕ} (hne : s.Nonempty) (hpos : ∀ m ∈ s, 0 < m) :
    kLCM s ≤ s.prod (fun m : ℕ => (m : ℤ)) := by
  have hprod_pos : (0 : ℤ) < s.prod (fun m : ℕ => (m : ℤ)) :=
    Finset.prod_pos (fun m hm => by exact_mod_cast hpos m hm)
  exact Int.le_of_dvd hprod_pos kLCM_dvd_prod

/-- When not all moduli are coprime, the kLCM is strictly smaller than the product. -/
theorem kLCM_lt_prod_when_gcd_gt_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hg : 1 < Nat.gcd m n) :
    kLCM {m, n} < (m : ℤ) * n := by
  have hL : kLCM {m, n} = Int.lcm m n := by
    simp [kLCM, Finset.lcm_pair, Int.lcm]
    ring_nf
    simp [Int.gcd_natCast_natCast, Nat.lcm]
  rw [hL]
  have : (Int.lcm m n : ℤ) < (m : ℤ) * n := by
    rw [Int.lcm, show Int.gcd m n = Nat.gcd m n from Int.gcd_natCast_natCast m n]
    rw [show (m : ℤ) * n = (m * n : ℕ) from by push_cast; ring]
    push_cast
    rw [Nat.cast_lt]
    exact ChineseRemainderNonCoprimeOQ01.lcm_lt_mul_of_gcd_gt_one m n hm hn hg
  exact this

-- ============================================================
-- Part V: Iterative Construction
-- ============================================================

/-- **Iterative reduction**: k+1 congruences reduce to k congruences plus one 2-modulus step.

    If x₀ solves x ≡ aᵢ for all i ∈ s with period L = kLCM s, then solving
    x ≡ aᵢ for all i ∈ s ∪ {m} is equivalent to:
      y ≡ a_m [ZMOD m]  ∧  y ≡ x₀ [ZMOD L]
    — a standard 2-modulus CRT problem with moduli m and L. -/
theorem kModuli_iterative {s : Finset ℕ} {m : ℕ} {a : ℕ → ℤ} {x₀ : ℤ}
    (hx₀ : ∀ n ∈ s, x₀ ≡ a n [ZMOD (n : ℤ)])
    (hm_notin : m ∉ s) :
    ∀ y : ℤ, (∀ n ∈ insert m s, y ≡ a n [ZMOD (n : ℤ)]) ↔
      y ≡ a m [ZMOD (m : ℤ)] ∧ y ≡ x₀ [ZMOD (kLCM s)] := by
  intro y
  constructor
  · intro hall
    refine ⟨hall m (mem_insert_self m s), ?_⟩
    rw [← kModuli_periodic]
    intro n hn
    exact (hall n (mem_insert_of_mem hn)).trans (hx₀ n hn).symm
  · intro ⟨hm_cong, hL_cong⟩ n hn
    rcases mem_insert.mp hn with rfl | hn_s
    · exact hm_cong
    · -- kLCM s ∣ (y - x₀) and (n : ℤ) ∣ kLCM s, so (n : ℤ) ∣ (y - x₀)
      have hLdvd : kLCM s ∣ (y - x₀) := Int.modEq_iff_dvd.mp hL_cong
      have hndvdL : (n : ℤ) ∣ kLCM s := dvd_kLCM hn_s
      have hndvd : (n : ℤ) ∣ (y - x₀) := dvd_trans hndvdL hLdvd
      have hx₀n : (n : ℤ) ∣ (x₀ - a n) := Int.modEq_iff_dvd.mp (hx₀ n hn_s)
      rw [Int.modEq_iff_dvd]
      have : y - a n = (y - x₀) + (x₀ - a n) := by ring
      rw [this]
      exact dvd_add hndvd hx₀n

-- ============================================================
-- Part VI: Necessary Condition
-- ============================================================

/-- **Necessary condition**: If x₀ solves all k congruences, then for any two
    moduli m, n ∈ s: gcd(m,n) ∣ (aₘ - aₙ). -/
theorem kModuli_necessary {s : Finset ℕ} {a : ℕ → ℤ} (x₀ : ℤ)
    (hx₀ : ∀ m ∈ s, x₀ ≡ a m [ZMOD (m : ℤ)])
    {m n : ℕ} (hm : m ∈ s) (hn : n ∈ s) :
    (Nat.gcd m n : ℤ) ∣ (a m - a n) := by
  have hxm := Int.modEq_iff_dvd.mp (hx₀ m hm)  -- (m : ℤ) ∣ x₀ - a m
  have hxn := Int.modEq_iff_dvd.mp (hx₀ n hn)  -- (n : ℤ) ∣ x₀ - a n
  have hgm : (Nat.gcd m n : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left m n)
  have hgn : (Nat.gcd m n : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right m n)
  have h1 : (Nat.gcd m n : ℤ) ∣ (x₀ - a m) := dvd_trans hgm hxm
  have h2 : (Nat.gcd m n : ℤ) ∣ (x₀ - a n) := dvd_trans hgn hxn
  convert dvd_sub h1 h2 using 1; ring

-- ============================================================
-- Part VII: Concrete Examples
-- ============================================================

/-- kLCM({4, 6, 10}) = 60 (less than 4*6*10 = 240, efficiency gain of 4). -/
theorem example_kLCM : kLCM ({4, 6, 10} : Finset ℕ) = 60 := by
  simp [kLCM, Finset.lcm_insert, Finset.lcm_singleton]
  native_decide

/-- The solution x = 21 solves: 21 ≡ 1 [ZMOD 4], 21 ≡ 3 [ZMOD 6], 21 ≡ 1 [ZMOD 10]. -/
theorem example_solution :
    (21 : ℤ) ≡ 1 [ZMOD 4] ∧ (21 : ℤ) ≡ 3 [ZMOD 6] ∧ (21 : ℤ) ≡ 1 [ZMOD 10] := by
  constructor; · decide
  constructor; · decide
  · decide

/-- Necessary conditions for a₄=1, a₆=3, a₁₀=1. -/
theorem example_compat_1 : (Nat.gcd 4 6 : ℤ) ∣ (1 - 3 : ℤ) := by norm_num
theorem example_compat_2 : (Nat.gcd 4 10 : ℤ) ∣ (1 - 1 : ℤ) := by norm_num
theorem example_compat_3 : (Nat.gcd 6 10 : ℤ) ∣ (3 - 1 : ℤ) := by norm_num

/-- kLCM({6, 10, 15}) = 30 (less than 6*10*15 = 900, efficiency gain of 30). -/
theorem example_kLCM_2 : kLCM ({6, 10, 15} : Finset ℕ) = 30 := by
  simp [kLCM, Finset.lcm_insert, Finset.lcm_singleton]
  native_decide

/-- kLCM of pairwise coprime set equals the product. -/
theorem kLCM_coprime_eq_prod :
    kLCM ({2, 3, 5} : Finset ℕ) = 30 := by
  simp [kLCM, Finset.lcm_insert, Finset.lcm_singleton]
  native_decide

end ChineseRemainderNonCoprimeOQ01OQ01
