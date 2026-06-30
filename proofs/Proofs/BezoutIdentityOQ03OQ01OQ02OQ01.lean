import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Proofs.BezoutIdentityOQ03OQ01OQ02
import Mathlib.Tactic

/-
# Iterated CRT for k Congruences (bezout-identity-oq-03-oq-01-oq-02-oq-01)

## Problem
The parent (`bezout-identity-oq-03-oq-01-oq-02`) characterizes the image of
ℤ → ℤ/mℤ × ℤ/nℤ for **two** non-coprime moduli: the system
x ≡ a (mod m), x ≡ b (mod n) is solvable iff gcd(m,n) ∣ (a-b), with the solution
unique mod lcm(m,n).

This file generalizes to a **system of k congruences** x ≡ aᵢ (mod mᵢ):

> The system is solvable **iff** it is *pairwise compatible*:
>   gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ)  for all i, j.
> When solvable, the solution is **unique modulo lcm(m₁, …, mₖ)**.

## Method
The whole result reduces to ONE lemma that Mathlib does **not** provide: the
distributivity of `gcd` over `lcm` on ℕ,
  gcd(a, lcm(b,c)) = lcm(gcd(a,b), gcd(a,c)),
proved here via prime factorizations (`min` distributes over `max`).
Everything else is a clean induction on the list of congruences, reusing the
parent's two-modulus merge (`gcd_dvd_implies_solvable`) and uniqueness
(`crt_unique_mod_lcm`).

The naive induction "merge the first two, recurse" needs exactly this
distributivity: after merging the tail into a single congruence mod the running
lcm L, compatibility of the head m₀ with L is
  gcd(m₀, L) = gcd(m₀, lcm mᵢ) = lcm gcd(m₀, mᵢ),
and each gcd(m₀, mᵢ) ∣ (a₀ - aᵢ), so their lcm divides it too.

## Status
- All theorems proved (0 sorries, 0 axioms).
-/

namespace IteratedCRT

open NonCoprimeCRT

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: gcd DISTRIBUTES OVER lcm  (the Mathlib gap)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **gcd/lcm distributivity on ℕ** (not in Mathlib). For nonzero a, b, c,
    `gcd a (lcm b c) = lcm (gcd a b) (gcd a c)`.
    Proof: compare prime-exponent vectors; `min` distributes over `max`. -/
theorem nat_gcd_lcm_distrib {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.gcd a (Nat.lcm b c) = Nat.lcm (Nat.gcd a b) (Nat.gcd a c) := by
  have hbc : Nat.lcm b c ≠ 0 := Nat.lcm_ne_zero hb hc
  have hab : Nat.gcd a b ≠ 0 := fun h => ha (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hac : Nat.gcd a c ≠ 0 := fun h => ha (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hL : Nat.gcd a (Nat.lcm b c) ≠ 0 := fun h => ha (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hR : Nat.lcm (Nat.gcd a b) (Nat.gcd a c) ≠ 0 := Nat.lcm_ne_zero hab hac
  apply Nat.eq_of_factorization_eq hL hR
  intro p
  rw [Nat.factorization_gcd ha hbc, Nat.factorization_lcm hb hc,
      Nat.factorization_lcm hab hac, Nat.factorization_gcd ha hb, Nat.factorization_gcd ha hc]
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  exact inf_sup_left _ _ _

/-- **Int version of distributivity**: `gcd a (lcm b c) = lcm (gcd a b) (gcd a c)`
    as natural numbers, where the inner `lcm b c` is taken in ℤ. -/
theorem int_gcd_lcm_distrib {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Int.gcd a (Int.lcm b c : ℤ) = Nat.lcm (Int.gcd a b) (Int.gcd a c) := by
  have hna : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  have hnb : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  have hnc : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  unfold Int.gcd Int.lcm
  simp only [Int.natAbs_natCast]
  exact nat_gcd_lcm_distrib hna hnb hnc

/-- If `(u:ℤ) ∣ d` and `(v:ℤ) ∣ d` then `(lcm u v : ℤ) ∣ d`. -/
theorem int_natLcm_dvd {u v : ℕ} {d : ℤ} (hu : (u : ℤ) ∣ d) (hv : (v : ℤ) ∣ d) :
    (Nat.lcm u v : ℤ) ∣ d := by
  rw [Int.natCast_dvd] at *
  exact Nat.lcm_dvd hu hv

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: lcm OF A LIST OF MODULI
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The lcm of all the moduli appearing in a list of congruences `(aᵢ, mᵢ)`. -/
def lcmList : List (ℤ × ℤ) → ℤ
  | [] => 1
  | p :: ps => (Int.lcm p.2 (lcmList ps) : ℤ)

@[simp] theorem lcmList_nil : lcmList [] = 1 := rfl

theorem lcmList_cons (p : ℤ × ℤ) (ps : List (ℤ × ℤ)) :
    lcmList (p :: ps) = (Int.lcm p.2 (lcmList ps) : ℤ) := rfl

/-- The list lcm is nonzero when all moduli are nonzero. -/
theorem lcmList_ne_zero {l : List (ℤ × ℤ)} (hl : ∀ p ∈ l, p.2 ≠ 0) : lcmList l ≠ 0 := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [lcmList_cons]
    have hp : p.2 ≠ 0 := hl p (List.mem_cons_self)
    have hps : lcmList ps ≠ 0 := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have : Int.lcm p.2 (lcmList ps) ≠ 0 := by
      rw [Int.lcm_def]
      exact Nat.lcm_ne_zero (Int.natAbs_ne_zero.mpr hp) (Int.natAbs_ne_zero.mpr hps)
    exact_mod_cast this

/-- Each modulus divides the list lcm. -/
theorem dvd_lcmList {l : List (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ l) : p.2 ∣ lcmList l := by
  induction l with
  | nil => exact absurd hp List.not_mem_nil
  | cons q qs ih =>
    rw [lcmList_cons]
    rcases List.mem_cons.mp hp with h | h
    · -- p = q : q.2 ∣ lcm q.2 (lcmList qs)
      subst h
      rw [Int.lcm_def, ← Int.natAbs_dvd, Int.natCast_dvd_natCast]
      exact Nat.dvd_lcm_left _ _
    · -- p ∈ qs : p.2 ∣ lcmList qs ∣ lcm q.2 (lcmList qs)
      refine dvd_trans (ih h) ?_
      rw [Int.lcm_def]
      rw [show ((Nat.lcm q.2.natAbs (lcmList qs).natAbs : ℕ) : ℤ)
            = (Int.lcm q.2 (lcmList qs) : ℤ) from by rw [Int.lcm_def]]
      have : lcmList qs ∣ (Int.lcm q.2 (lcmList qs) : ℤ) := by
        rw [Int.lcm_def, ← Int.natAbs_dvd, Int.natCast_dvd_natCast]
        exact Nat.dvd_lcm_right _ _
      simpa [Int.lcm_def] using this

/-- **Key divisibility step.** If each `gcd(m₀, mᵢ)` divides `d`, then so does
    `gcd(m₀, lcm mᵢ)`. This is where distributivity is used. -/
theorem gcd_lcmList_dvd (m₀ : ℤ) (hm₀ : m₀ ≠ 0) :
    ∀ (l : List (ℤ × ℤ)), (∀ p ∈ l, p.2 ≠ 0) → ∀ {d : ℤ},
      (∀ p ∈ l, (Int.gcd m₀ p.2 : ℤ) ∣ d) → (Int.gcd m₀ (lcmList l) : ℤ) ∣ d := by
  intro l
  induction l with
  | nil =>
    intro _ d _
    simp only [lcmList_nil]
    have : Int.gcd m₀ (1 : ℤ) = 1 := by simp [Int.gcd]
    rw [this]; simp
  | cons p ps ih =>
    intro hl d h
    have hp : p.2 ≠ 0 := hl p (List.mem_cons_self)
    have hps_ne : ∀ q ∈ ps, q.2 ≠ 0 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hLps : lcmList ps ≠ 0 := lcmList_ne_zero hps_ne
    rw [lcmList_cons, int_gcd_lcm_distrib hm₀ hp hLps]
    apply int_natLcm_dvd
    · exact h p (List.mem_cons_self)
    · exact ih hps_ne (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE SYSTEM AND ITS SOLVABILITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- `x` solves the system `l` of congruences `(aᵢ, mᵢ)`: `x ≡ aᵢ (mod mᵢ)` for all i. -/
def CongSolves (x : ℤ) (l : List (ℤ × ℤ)) : Prop :=
  ∀ p ∈ l, x ≡ p.1 [ZMOD p.2]

/-- The system `l` is **pairwise compatible**: `gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ)` for all i, j. -/
def Compatible (l : List (ℤ × ℤ)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, (Int.gcd p.2 q.2 : ℤ) ∣ (p.1 - q.1)

/-- **Necessity**: any common solution forces pairwise compatibility.
    (Holds for *all* moduli, no nonzero hypothesis needed.) -/
theorem compatible_of_solves {x : ℤ} {l : List (ℤ × ℤ)} (hx : CongSolves x l) :
    Compatible l := by
  intro p hp q hq
  exact solvable_implies_gcd_dvd p.2 q.2 p.1 q.1 x (hx p hp) (hx q hq)

/-- **Sufficiency (existence)**: a pairwise-compatible system with nonzero moduli
    has a common solution. Proved by induction, merging the head congruence with
    the inductively-built solution of the tail via the parent's two-modulus CRT. -/
theorem solves_of_compatible :
    ∀ (l : List (ℤ × ℤ)), (∀ p ∈ l, p.2 ≠ 0) → Compatible l → ∃ x, CongSolves x l := by
  intro l
  induction l with
  | nil =>
    intro _ _
    exact ⟨0, by intro p hp; exact absurd hp List.not_mem_nil⟩
  | cons p ps ih =>
    intro hl hcompat
    have hp : p.2 ≠ 0 := hl p (List.mem_cons_self)
    have hps_ne : ∀ q ∈ ps, q.2 ≠ 0 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    -- compatibility restricts to the tail
    have hcompat_ps : Compatible ps := by
      intro a ha b hb
      exact hcompat a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    obtain ⟨Y, hY⟩ := ih hps_ne hcompat_ps
    -- need gcd(p.2, lcmList ps) ∣ (p.1 - Y)
    have hdvd : (Int.gcd p.2 (lcmList ps) : ℤ) ∣ (p.1 - Y) := by
      apply gcd_lcmList_dvd p.2 hp ps hps_ne
      intro q hq
      -- gcd(p.2, q.2) ∣ (p.1 - q.1) and ∣ (q.1 - Y), so ∣ (p.1 - Y)
      have h1 : (Int.gcd p.2 q.2 : ℤ) ∣ (p.1 - q.1) :=
        hcompat p (List.mem_cons_self) q (List.mem_cons_of_mem _ hq)
      have hqY : q.2 ∣ (q.1 - Y) := by
        have := hY q hq            -- Y ≡ q.1 [ZMOD q.2]
        exact (Int.modEq_iff_dvd.mp this)
      have h2 : (Int.gcd p.2 q.2 : ℤ) ∣ (q.1 - Y) :=
        dvd_trans (Int.gcd_dvd_right p.2 q.2) hqY
      have : p.1 - Y = (p.1 - q.1) + (q.1 - Y) := by ring
      rw [this]; exact dvd_add h1 h2
    -- merge head congruence with the tail solution mod lcmList ps
    obtain ⟨x, hx_p, hx_L⟩ := gcd_dvd_implies_solvable p.2 (lcmList ps) p.1 Y hdvd
    refine ⟨x, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with h | h
    · subst h; exact hx_p
    · -- r ∈ ps : x ≡ Y (mod lcmList ps) and r.2 ∣ lcmList ps, and Y ≡ r.1 (mod r.2)
      have hr2L : r.2 ∣ lcmList ps := dvd_lcmList h
      have hxY : x ≡ Y [ZMOD r.2] := by
        rw [Int.modEq_iff_dvd] at hx_L ⊢
        exact dvd_trans hr2L hx_L
      exact hxY.trans (hY r h)

/-- **Generalized CRT — solvability criterion.**
    A system of congruences with nonzero moduli is solvable **iff** it is
    pairwise compatible. -/
theorem solvable_iff_compatible (l : List (ℤ × ℤ)) (hl : ∀ p ∈ l, p.2 ≠ 0) :
    (∃ x, CongSolves x l) ↔ Compatible l :=
  ⟨fun ⟨_, hx⟩ => compatible_of_solves hx, solves_of_compatible l hl⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: UNIQUENESS MODULO THE LIST lcm
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Uniqueness**: any two solutions of the same system agree modulo
    `lcm(m₁, …, mₖ)`. -/
theorem solutions_unique_mod_lcmList {l : List (ℤ × ℤ)} {x y : ℤ}
    (hx : CongSolves x l) (hy : CongSolves y l) :
    x ≡ y [ZMOD lcmList l] := by
  induction l with
  | nil => simp only [lcmList_nil]; exact Int.modEq_one
  | cons p ps ih =>
    rw [lcmList_cons]
    have hxp : x ≡ p.1 [ZMOD p.2] := hx p (List.mem_cons_self)
    have hyp : y ≡ p.1 [ZMOD p.2] := hy p (List.mem_cons_self)
    have hp : x ≡ y [ZMOD p.2] := hxp.trans hyp.symm
    have hxps : CongSolves x ps := fun q hq => hx q (List.mem_cons_of_mem _ hq)
    have hyps : CongSolves y ps := fun q hq => hy q (List.mem_cons_of_mem _ hq)
    have hL : x ≡ y [ZMOD lcmList ps] := ih hxps hyps
    exact crt_unique_mod_lcm p.2 (lcmList ps) x y hp hL

/-- **Full generalized CRT**: existence + uniqueness modulo the list lcm. -/
theorem iterated_crt_full (l : List (ℤ × ℤ)) (hl : ∀ p ∈ l, p.2 ≠ 0)
    (hcompat : Compatible l) :
    ∃ x, CongSolves x l ∧ ∀ y, CongSolves y l → x ≡ y [ZMOD lcmList l] := by
  obtain ⟨x, hx⟩ := solves_of_compatible l hl hcompat
  exact ⟨x, hx, fun y hy => solutions_unique_mod_lcmList hx hy⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: SANITY EXAMPLES
═══════════════════════════════════════════════════════════════════════════════ -/

section Examples

/-- Three pairwise-coprime congruences x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7).
    x = 23 is the classical Sun-Tzu solution. -/
example : CongSolves 23 [(2, 3), (3, 5), (2, 7)] := by
  intro p hp
  fin_cases hp <;> decide

/-- A non-coprime but compatible system: x ≡ 1 (mod 4), x ≡ 3 (mod 6), x ≡ 0 (mod 9).
    gcd(4,6)=2 ∣ (1-3), gcd(4,9)=1 ∣ (1-0), gcd(6,9)=3 ∣ (3-0). x = 9 works. -/
example : CongSolves 9 [(1, 4), (3, 6), (0, 9)] := by
  intro p hp
  fin_cases hp <;> decide

/-- The distributivity lemma on a concrete instance: gcd(12, lcm(8,18)) = lcm(gcd 12 8, gcd 12 18). -/
example : Nat.gcd 12 (Nat.lcm 8 18) = Nat.lcm (Nat.gcd 12 8) (Nat.gcd 12 18) := by decide

end Examples

#check @nat_gcd_lcm_distrib
#check @int_gcd_lcm_distrib
#check @gcd_lcmList_dvd
#check @compatible_of_solves
#check @solves_of_compatible
#check @solvable_iff_compatible
#check @solutions_unique_mod_lcmList
#check @iterated_crt_full

end IteratedCRT
