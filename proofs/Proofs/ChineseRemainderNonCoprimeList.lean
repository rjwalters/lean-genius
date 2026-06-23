/-
  Non-Coprime Chinese Remainder Theorem for Arbitrary Lists

  Extends the non-coprime CRT from 2-3 moduli (OQ03) to arbitrary-length lists.
  For moduli m₁, ..., mₖ and targets a₁, ..., aₖ in a Euclidean domain R,
  the system mᵢ ∣ (x - aᵢ) is solvable iff pairwise gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ).

  Key proof technique:
  - Induction on list length, reducing to the 2-moduli case at each step.
  - The distributive law gcd(lcm(a,b), c) ∣ lcm(gcd(a,c), gcd(b,c))
    from OQ03 extends to gcd(listLcm ms, c) ∣ listLcm (ms.map (gcd · c)).

  Parent: ChineseRemainderNonCoprimeOQ03.lean (0 axioms, 0 sorries)
  Extends: ChineseRemainderConstructiveOQ04.lean (list CRT for coprime moduli)
-/
import Proofs.ChineseRemainderNonCoprimeOQ03

namespace ChineseRemainderNonCoprimeList

open ChineseRemainderNonCoprimeOQ03

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

-- ═══════════════════════════════════════════════════
-- Part I: List LCM and Compatibility
-- ═══════════════════════════════════════════════════

/-- LCM of a list of elements. The empty LCM is 1. -/
def listLcm : List R → R
  | [] => 1
  | m :: ms => EuclideanDomain.lcm m (listLcm ms)

/-- Each element of a list divides its LCM. -/
theorem dvd_listLcm {m : R} {ms : List R} (hm : m ∈ ms) : m ∣ listLcm ms := by
  induction ms with
  | nil => exact nomatch hm
  | cons a as ih =>
    simp only [listLcm]
    rcases List.mem_cons.mp hm with rfl | has
    · exact EuclideanDomain.dvd_lcm_left a (listLcm as)
    · exact dvd_trans (ih has) (EuclideanDomain.dvd_lcm_right a (listLcm as))

/-- If each element of a list divides d, then listLcm divides d. -/
theorem listLcm_dvd {ms : List R} {d : R} (h : ∀ m ∈ ms, m ∣ d) : listLcm ms ∣ d := by
  induction ms with
  | nil => simp [listLcm]; exact one_dvd d
  | cons a as ih =>
    simp only [listLcm]
    exact EuclideanDomain.lcm_dvd
      (h a (List.mem_cons_self a as))
      (ih (fun m hm => h m (List.mem_cons.mpr (Or.inr hm))))

/-- A system of congruences: list of (target, modulus) pairs. -/
abbrev System (R : Type*) := List (R × R)

/-- A value x satisfies all congruences in the system. -/
def Satisfies (x : R) (sys : System R) : Prop :=
  ∀ p ∈ sys, p.2 ∣ (x - p.1)

/-- Pairwise compatibility: gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ) for all pairs. -/
def Compatible (sys : System R) : Prop :=
  ∀ p q, p ∈ sys → q ∈ sys →
    EuclideanDomain.gcd p.2 q.2 ∣ (p.1 - q.1)

/-- The moduli of a system. -/
def moduli (sys : System R) : List R := sys.map Prod.snd

-- ═══════════════════════════════════════════════════
-- Part II: Extended Distributive Law
-- ═══════════════════════════════════════════════════

/-- LCM monotonicity: if a ∣ b then lcm(c, a) ∣ lcm(c, b). -/
private theorem lcm_dvd_lcm_right {a b c : R} (h : a ∣ b) :
    EuclideanDomain.lcm c a ∣ EuclideanDomain.lcm c b :=
  EuclideanDomain.lcm_dvd
    (EuclideanDomain.dvd_lcm_left c b)
    (dvd_trans h (EuclideanDomain.dvd_lcm_right c b))

/-- Extended distributive law for lists:
    gcd(listLcm ms, c) ∣ listLcm (ms.map (gcd · c)).

    Base: gcd(1, c) ∣ 1 trivially (gcd(1,c) is a unit).
    Step: gcd(lcm(m, L), c) ∣ lcm(gcd(m,c), gcd(L,c)) by OQ03's gcd_lcm_dvd_lcm_gcd,
          and gcd(L, c) ∣ listLcm (rest.map (gcd · c)) by IH,
          so lcm(gcd(m,c), gcd(L,c)) ∣ lcm(gcd(m,c), listLcm(rest.map(gcd · c))). -/
theorem gcd_listLcm_dvd_listLcm_gcd (ms : List R) (c : R) :
    EuclideanDomain.gcd (listLcm ms) c ∣
    listLcm (ms.map (fun m => EuclideanDomain.gcd m c)) := by
  induction ms with
  | nil =>
    simp only [listLcm, List.map_nil]
    -- gcd(1, c) ∣ 1
    exact dvd_trans (EuclideanDomain.gcd_dvd_left 1 c) (one_dvd 1)
  | cons m rest ih =>
    simp only [listLcm, List.map_cons]
    -- gcd(lcm(m, listLcm rest), c) ∣ lcm(gcd(m, c), listLcm(rest.map(gcd · c)))
    -- Step 1: by OQ03, gcd(lcm(m, L), c) ∣ lcm(gcd(m,c), gcd(L,c))
    have h1 := gcd_lcm_dvd_lcm_gcd m (listLcm rest) c
    -- Step 2: by IH, gcd(L, c) ∣ listLcm(rest.map(gcd · c))
    -- Step 3: monotonicity of lcm
    have h2 := lcm_dvd_lcm_right ih
    exact dvd_trans h1 h2

-- ═══════════════════════════════════════════════════
-- Part III: Key Transfer Lemma
-- ═══════════════════════════════════════════════════

/-- If x satisfies a list of congruences and compatibility holds with a new modulus c,
    then gcd(listLcm(moduli), c) ∣ (x - a) for any compatible target a. -/
theorem gcd_listLcm_dvd_sub {sys : System R} {x a c : R}
    (hx : Satisfies x sys)
    (hcompat : ∀ p ∈ sys, EuclideanDomain.gcd p.2 c ∣ (p.1 - a)) :
    EuclideanDomain.gcd (listLcm (moduli sys)) c ∣ (x - a) := by
  -- Each gcd(mⱼ, c) ∣ (x - a):
  --   gcd(mⱼ, c) ∣ (aⱼ - a) by hcompat
  --   gcd(mⱼ, c) ∣ mⱼ ∣ (x - aⱼ) by hx
  --   so gcd(mⱼ, c) ∣ (x - aⱼ) + (aⱼ - a) = (x - a)
  have h_each : ∀ p ∈ sys, EuclideanDomain.gcd p.2 c ∣ (x - a) := by
    intro p hp
    have hg_dvd_m := EuclideanDomain.gcd_dvd_left p.2 c
    have hm_dvd := hx p hp  -- p.2 ∣ (x - p.1)
    have hg_dvd_xp := dvd_trans hg_dvd_m hm_dvd  -- gcd(p.2, c) ∣ (x - p.1)
    have hg_dvd_pa := hcompat p hp  -- gcd(p.2, c) ∣ (p.1 - a)
    have : (x - a) = (x - p.1) + (p.1 - a) := by ring
    rw [this]; exact dvd_add hg_dvd_xp hg_dvd_pa
  -- listLcm of these gcd's divides (x - a)
  have h_lcm : listLcm ((moduli sys).map (fun m => EuclideanDomain.gcd m c)) ∣ (x - a) := by
    apply listLcm_dvd
    intro d hd
    simp only [moduli, List.map_map] at hd
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
    exact h_each p hp
  -- And gcd(listLcm(moduli), c) ∣ listLcm(gcd's) by the extended distributive law
  exact dvd_trans (gcd_listLcm_dvd_listLcm_gcd (moduli sys) c) h_lcm

-- ═══════════════════════════════════════════════════
-- Part IV: Main Theorems
-- ═══════════════════════════════════════════════════

/-- **Non-coprime CRT for lists (existence)**:
    If all pairs satisfy the GCD compatibility condition, a solution exists. -/
theorem ed_crt_list_sufficient {sys : System R}
    (hcompat : Compatible sys) :
    ∃ x : R, Satisfies x sys := by
  induction sys with
  | nil => exact ⟨0, fun _ h => nomatch h⟩
  | cons pair rest ih =>
    -- By induction, solve the tail system
    have hcompat_rest : Compatible rest := by
      intro p q hp hq
      exact hcompat p q (List.mem_cons.mpr (Or.inr hp)) (List.mem_cons.mpr (Or.inr hq))
    obtain ⟨y, hy⟩ := ih hcompat_rest
    -- Need: gcd(listLcm(moduli rest), pair.2) ∣ (y - pair.1)
    have hcompat_head : ∀ p ∈ rest, EuclideanDomain.gcd p.2 pair.2 ∣ (p.1 - pair.1) := by
      intro p hp
      exact hcompat p pair (List.mem_cons.mpr (Or.inr hp)) (List.mem_cons_self pair rest)
    have h_gcd_dvd := gcd_listLcm_dvd_sub hy hcompat_head
    -- Apply 2-moduli CRT
    obtain ⟨x, hx_lcm, hx_pair⟩ := ed_crt_sufficient h_gcd_dvd
    refine ⟨x, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hrest
    · -- Head: x satisfies pair.2 ∣ (x - pair.1) directly
      exact hx_pair
    · -- Tail: listLcm(moduli rest) ∣ (x - y), and p.2 ∣ listLcm(moduli rest), and p.2 ∣ (y - p.1)
      have h_p_dvd_lcm : p.2 ∣ listLcm (moduli rest) :=
        dvd_listLcm (List.mem_map.mpr ⟨p, hrest, rfl⟩)
      have h_lcm_dvd_xy := dvd_trans h_p_dvd_lcm hx_lcm  -- p.2 ∣ (x - y)
      have h_p_dvd_ya := hy p hrest  -- p.2 ∣ (y - p.1)
      have : (x - p.1) = (x - y) + (y - p.1) := by ring
      rw [this]; exact dvd_add h_lcm_dvd_xy h_p_dvd_ya

/-- **Non-coprime CRT for lists (necessity)**:
    If a solution exists, pairwise GCD conditions hold. -/
theorem ed_crt_list_necessary {sys : System R} {x : R}
    (hx : Satisfies x sys) : Compatible sys := by
  intro p q hp hq
  have hp_dvd := hx p hp  -- p.2 ∣ (x - p.1)
  have hq_dvd := hx q hq  -- q.2 ∣ (x - q.1)
  have hg_p := dvd_trans (EuclideanDomain.gcd_dvd_left p.2 q.2) hp_dvd
  have hg_q := dvd_trans (EuclideanDomain.gcd_dvd_right p.2 q.2) hq_dvd
  have : (p.1 - q.1) = (x - q.1) - (x - p.1) := by ring
  rw [this]; exact dvd_sub hg_q hg_p

/-- **Non-coprime CRT for lists (iff)**: Full characterization. -/
theorem ed_crt_list_iff {sys : System R} :
    (∃ x : R, Satisfies x sys) ↔ Compatible sys :=
  ⟨fun ⟨_, hx⟩ => ed_crt_list_necessary hx, ed_crt_list_sufficient⟩

/-- **Non-coprime CRT for lists (uniqueness)**:
    Any two solutions agree modulo listLcm of all moduli. -/
theorem ed_crt_list_unique {sys : System R} {x y : R}
    (hx : Satisfies x sys) (hy : Satisfies y sys) :
    listLcm (moduli sys) ∣ (x - y) := by
  apply listLcm_dvd
  intro m hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  have hx_p := hx p hp  -- p.2 ∣ (x - p.1)
  have hy_p := hy p hp  -- p.2 ∣ (y - p.1)
  have : (x - y) = (x - p.1) - (y - p.1) := by ring
  rw [this]; exact dvd_sub hx_p hy_p

-- ═══════════════════════════════════════════════════
-- Part V: Connection to Coprime Case
-- ═══════════════════════════════════════════════════

/-- When moduli are pairwise coprime, compatibility is automatic. -/
theorem coprime_implies_compatible {sys : System R}
    (hpc : ∀ p q, p ∈ sys → q ∈ sys → p ≠ q →
      IsUnit (EuclideanDomain.gcd p.2 q.2)) :
    Compatible sys := by
  intro p q hp hq
  by_cases heq : p = q
  · rw [heq]; simp
  · exact (hpc p q hp hq heq).dvd

end ChineseRemainderNonCoprimeList
