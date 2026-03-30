/-
# Erdős Problem #1062: Maximum "No Divides Two Others" Sets

Let f(n) be the maximum size of A ⊆ {1,…,n} such that no element
divides two distinct others. How large is f(n)? Is lim f(n)/n irrational?

## Status: OPEN

## References
- Guy (2004), Problem B24
- Lebensold (1976), bounds 0.6725n ≤ f(n) ≤ 0.6736n
-/

import Mathlib

/-
## Section I: The Divisibility Condition
-/

/-- A set A has the "no divides two others" property if no element
divides two distinct other elements. Equivalently, each element
has at most one proper multiple in A. -/
def NoDividesTwoOthers (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ∣ b → a ∣ c → a ≠ b → a ≠ c → b ≠ c → False

/-
## Section II: The Extremal Function
-/

/-- f(n): the maximum size of a subset of {1,…,n} satisfying
the "no divides two others" property. -/
noncomputable def maxNDTOSize (n : ℕ) : ℕ :=
  Finset.sup
    ((Finset.Icc 1 n).powerset.filter (fun A => NoDividesTwoOthers A))
    Finset.card

/-
## Section III: Lower Bound Construction
-/

/-- The upper interval [n/3+1, n] satisfies NDTO: if a divides two distinct
elements b,c in the interval, one requires multiplier ≥ 3 giving
a*k ≥ (n/3+1)*3 > n, contradicting membership. -/
private lemma ndto_upper_interval (n : ℕ) (hn : n ≥ 3) :
    NoDividesTwoOthers (Finset.Icc (n / 3 + 1) n) := by
  intro a b c ha hb hc hab hac hne_ab hne_ac hne_bc
  simp only [Finset.mem_Icc] at ha hb hc
  obtain ⟨kb, rfl⟩ := hab
  obtain ⟨kc, rfl⟩ := hac
  -- kb ≥ 2: kb=0 gives 0 ∈ [n/3+1,n] (impossible); kb=1 gives a = a*1 (contradicts ≠)
  have hkb : kb ≥ 2 := by
    by_contra h; push_neg at h; interval_cases kb <;> simp_all <;> omega
  have hkc : kc ≥ 2 := by
    by_contra h; push_neg at h; interval_cases kc <;> simp_all <;> omega
  have hkne : kb ≠ kc := fun heq => hne_bc (by rw [heq])
  -- One multiplier ≥ 3, giving a*k ≥ (n/3+1)*3 > n, contradicting a*k ≤ n
  rcases le_or_lt 3 kb with hkb3 | hkb3
  · have h1 : a * 3 ≤ a * kb := Nat.mul_le_mul_left a hkb3
    have h2 : (n / 3 + 1) * 3 ≤ a * 3 := Nat.mul_le_mul_right 3 ha.1
    have : (n / 3 + 1) * 3 ≤ n := le_trans (le_trans h2 h1) hb.2
    omega
  · -- kb = 2 forces kc ≥ 3
    have h1 : a * 3 ≤ a * kc := Nat.mul_le_mul_left a (by omega)
    have h2 : (n / 3 + 1) * 3 ≤ a * 3 := Nat.mul_le_mul_right 3 ha.1
    have : (n / 3 + 1) * 3 ≤ n := le_trans (le_trans h2 h1) hc.2
    omega

/-- The interval [m+1, 3m+2] has no element dividing two others,
since the ratio max/min < 3, so each element has at most one
multiple in the range. This gives f(n) ≥ ⌈2n/3⌉. -/
theorem lower_bound_construction (n : ℕ) (hn : n ≥ 3) :
    maxNDTOSize n ≥ (2 * n + 2) / 3 := by
  -- Witness: the upper ≈2/3 of {1,...,n}
  have hle : (Finset.Icc (n / 3 + 1) n).card ≤ maxNDTOSize n :=
    Finset.le_sup (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr
        (fun x hx => by simp only [Finset.mem_Icc] at hx ⊢; omega),
       ndto_upper_interval n hn⟩)
  rw [Nat.card_Icc] at hle
  omega

/-
## Section IV: Lebensold's Bounds
-/

/-- Lebensold (1976): for large n, f(n) ≥ 0.6725n. -/
/-- Lebensold (1976): for large n, f(n) ≤ 0.6736n. -/
/-
## Section V: The Conjectures
-/

/-- The limiting density lim f(n)/n exists and lies in [0.6725, 0.6736]. -/
/-- **Erdős Problem #1062**: Is the limiting density irrational? -/
def ErdosProblem1062 : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (maxNDTOSize n : ℝ) / n)
    Filter.atTop (nhds L) ∧
    Irrational L

/-
## Section VI: Comparison with Primitive Sets
-/

/-- A primitive set has no element dividing any other. This is strictly
stronger than NoDividesTwoOthers. -/
def IsPrimitiveFinset (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → ¬(a ∣ b)

/-- Every primitive set satisfies "no divides two others". -/
theorem primitive_implies_ndto (A : Finset ℕ) :
    IsPrimitiveFinset A → NoDividesTwoOthers A := by
  intro hprim a b c ha hb hc hab _ hab' _ _
  exact hprim a b ha hb hab' hab

/-- The "no divides two others" condition is strictly weaker:
{2, 6, 9} satisfies it (2 divides only 6, not 9) but is not
primitive (since 2 ∣ 6). -/
theorem ndto_strictly_weaker :
    NoDividesTwoOthers ({2, 6, 9} : Finset ℕ) ∧
      ¬IsPrimitiveFinset ({2, 6, 9} : Finset ℕ) := by
  constructor
  · intro a b c ha hb hc hab hac hne_ab hne_ac hne_bc
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;> simp_all <;> omega
  · intro h
    exact h 2 6 (by simp) (by simp) (by omega) (by omega)

/-
## Section VII: Structural Properties of NDTO
-/

/-- The NDTO property is hereditary: subsets of NDTO sets are NDTO.
This is because the universal quantification over triples restricts
to fewer candidates in a smaller set. -/
theorem ndto_subset {A B : Finset ℕ} (hBA : B ⊆ A) (hA : NoDividesTwoOthers A) :
    NoDividesTwoOthers B := by
  intro a b c ha hb hc
  exact hA a b c (hBA ha) (hBA hb) (hBA hc)

/-- Any pair satisfies NDTO: the condition requires three distinct elements,
so sets of size ≤ 2 satisfy it vacuously (pigeonhole on {a, b}). -/
theorem ndto_pair (a b : ℕ) : NoDividesTwoOthers ({a, b} : Finset ℕ) := by
  intro x y z hx hy hz _ _ hxy hxz hyz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> simp_all

/-
## Section VIII: Properties of the Extremal Function
-/

/-- The extremal function f is monotonically non-decreasing: any NDTO
subset of {1,…,m} is also a valid subset of {1,…,n} when m ≤ n. -/
theorem maxNDTOSize_mono {m n : ℕ} (hmn : m ≤ n) : maxNDTOSize m ≤ maxNDTOSize n := by
  unfold maxNDTOSize
  apply Finset.sup_le
  intro A hA
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
  refine ⟨fun x hx => ?_, hA.2⟩
  have := hA.1 hx
  simp only [Finset.mem_Icc] at this ⊢
  omega

/-- Any singleton set satisfies NDTO (fewer than 3 distinct elements). -/
theorem ndto_singleton (x : ℕ) : NoDividesTwoOthers ({x} : Finset ℕ) := by
  intro a b _ ha hb _ _ _ hne_ab _ _
  exact hne_ab (Finset.mem_singleton.mp ha ▸ (Finset.mem_singleton.mp hb).symm)

/-- f(n) ≥ 1 for n ≥ 1: the singleton {1} is a valid NDTO subset. -/
theorem maxNDTOSize_ge_one (n : ℕ) (hn : n ≥ 1) : maxNDTOSize n ≥ 1 := by
  have : ({1} : Finset ℕ).card ≤ maxNDTOSize n :=
    Finset.le_sup (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (fun x hx => by
        simp only [Finset.mem_singleton] at hx; subst hx
        simp only [Finset.mem_Icc]; omega),
       ndto_singleton 1⟩)
  simpa using this

/-- f(n) ≤ n: a subset of {1,…,n} has at most n elements. -/
theorem maxNDTOSize_le (n : ℕ) : maxNDTOSize n ≤ n := by
  unfold maxNDTOSize
  apply Finset.sup_le
  intro A hA
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  have h := Finset.card_le_card hA.1
  rw [Nat.card_Icc] at h
  omega
