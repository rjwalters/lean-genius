import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Proofs.SchursTheorem

/-
# Erdős Problem #483: Growth Rate of Schur Numbers

The Schur number f(k) is the minimal N such that every k-coloring of
{1, ..., N} contains a monochromatic solution to a + b = c.

Question: Is f(k) < c^k for some constant c > 0?

Known:
- f(1) = 2 (proved), f(2) = 5 (proved), f(3) = 14 (proved via native_decide)
- f(4) = 45, f(5) = 161 (axiomatized — too large for native_decide)
- Lower bound: f(k) ≥ 380^{k/5} - O(1) (Ageron et al.)
- Upper bound: f(k) ≤ ⌊(e - 1/24)k!⌋ - 1 (Whitehead, 1973)
- Schur's theorem (1916): f(k) is finite for all k

Status: OPEN.
Axioms: 5 (schurNumber_4, schurNumber_5, schur_lower_bound, schur_upper_bound, erdos_483_conjecture)

Reference: https://erdosproblems.com/483
-/

open SchursTheorem

-- ## Defining the Schur Number

/-- The Schur property: N is large enough that every k-coloring of {1,...,N}
    contains a monochromatic solution to x + y = z. -/
def SchurProp (N k : ℕ) : Prop :=
  ∀ (c : IntegerColoring N k), HasMonochromaticSchurTriple c

/-- For any k ≥ 1, there exists an N with the Schur property. -/
theorem schurProp_exists (k : ℕ) (hk : k ≥ 1) : ∃ N, SchurProp N k := by
  obtain ⟨S, _, hS⟩ := schur_theorem_existence k hk
  exact ⟨S, hS⟩

/-- If SchurProp N k holds, then SchurProp M k holds for any M ≥ N. -/
theorem schurProp_mono {N M k : ℕ} (hNM : N ≤ M) (hN : SchurProp N k) : SchurProp M k := by
  intro c
  let c' : IntegerColoring N k := fun i => c ⟨i.val, Nat.lt_of_lt_of_le i.isLt hNM⟩
  obtain ⟨i, j, kk, hsum, hci, hcj⟩ := hN c'
  exact ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hNM⟩,
         ⟨j.val, Nat.lt_of_lt_of_le j.isLt hNM⟩,
         ⟨kk.val, Nat.lt_of_lt_of_le kk.isLt hNM⟩,
         hsum, hci, hcj⟩

-- ## The Schur Number as a Proper Definition

open Classical in
/-- The Schur number S(k) is the smallest N such that every k-coloring
    of {1,...,N} has a monochromatic solution to x + y = z. -/
noncomputable def schurNumber (k : ℕ) : ℕ :=
  if hk : k ≥ 1 then Nat.find (schurProp_exists k hk)
  else 0

open Classical in
/-- The Schur number satisfies its defining property. -/
theorem schurNumber_spec (k : ℕ) (hk : k ≥ 1) :
    SchurProp (schurNumber k) k := by
  have : schurNumber k = Nat.find (schurProp_exists k hk) := by
    unfold schurNumber
    rw [dif_pos hk]
  rw [this]
  exact Nat.find_spec (schurProp_exists k hk)

open Classical in
/-- The Schur number is minimal. -/
theorem schurNumber_min (k : ℕ) (hk : k ≥ 1) (N : ℕ) (hN : N < schurNumber k) :
    ¬SchurProp N k := by
  have : N < Nat.find (schurProp_exists k hk) := by
    unfold schurNumber at hN
    rwa [dif_pos hk] at hN
  exact Nat.find_min (schurProp_exists k hk) this

-- ## Proved: S(1) = 2

/-- S(1) ≤ 2: any 1-coloring of {1,2} has a monochromatic Schur triple. -/
theorem schurProp_2_1 : SchurProp 2 1 := schur_1

/-- S(1) > 1: {1} alone has no Schur triple. -/
theorem not_schurProp_1_1 : ¬SchurProp 1 1 := by
  intro h
  obtain ⟨i, j, k, hsum, _, _⟩ := h (fun _ => (0 : Fin 1))
  have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
  have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
  have hk : k.val = 0 := Nat.lt_one_iff.mp k.isLt
  omega

/-- S(1) = 2. -/
theorem schurNumber_1 : schurNumber 1 = 2 := by
  have hspec := schurNumber_spec 1 (by omega)
  have hmin := schurNumber_min 1 (by omega)
  have h_le : schurNumber 1 ≤ 2 := by
    by_contra h
    push_neg at h
    exact hmin 2 (by omega) schurProp_2_1
  have h_ge : schurNumber 1 ≥ 2 := by
    by_contra h
    push_neg at h
    have h1 : SchurProp 1 1 := schurProp_mono (by omega) hspec
    exact not_schurProp_1_1 h1
  omega

-- ## Proved: S(2) = 5

/-- S(2) ≤ 5. -/
theorem schurProp_5_2 : SchurProp 5 2 := schur_2_upper

/-- S(2) > 4. -/
theorem not_schurProp_4_2 : ¬SchurProp 4 2 := by
  intro h
  obtain ⟨c, hc⟩ := schur_2_lower
  exact hc (h c)

/-- S(2) = 5. -/
theorem schurNumber_2 : schurNumber 2 = 5 := by
  have hspec := schurNumber_spec 2 (by omega)
  have hmin := schurNumber_min 2 (by omega)
  have h_le : schurNumber 2 ≤ 5 := by
    by_contra h
    push_neg at h
    exact hmin 5 (by omega) schurProp_5_2
  have h_ge : schurNumber 2 ≥ 5 := by
    by_contra h
    push_neg at h
    have h4 : SchurProp 4 2 := schurProp_mono (by omega) hspec
    exact not_schurProp_4_2 h4
  omega

-- ## Structural Properties

/-- Schur numbers are positive for k ≥ 1. -/
theorem schurNumber_pos (k : ℕ) (hk : k ≥ 1) : schurNumber k ≥ 1 := by
  by_contra h
  push_neg at h
  have h0 : schurNumber k = 0 := by omega
  have hspec := schurNumber_spec k hk
  rw [h0] at hspec
  obtain ⟨i, _, _, _, _, _⟩ := hspec Fin.elim0
  exact Fin.elim0 i

/-- Schur numbers are non-decreasing: S(k₁) ≤ S(k₂) when k₁ ≤ k₂. -/
theorem schurNumber_nondecreasing {k₁ k₂ : ℕ} (hk1 : k₁ ≥ 1) (hle : k₁ ≤ k₂) :
    schurNumber k₁ ≤ schurNumber k₂ := by
  have hk2 : k₂ ≥ 1 := by omega
  by_contra h
  push_neg at h
  have hno := schurNumber_min k₁ hk1 (schurNumber k₂) h
  apply hno
  intro c
  let c' : IntegerColoring (schurNumber k₂) k₂ := fun i =>
    ⟨(c i).val, Nat.lt_of_lt_of_le (c i).isLt hle⟩
  obtain ⟨i, j, kk, hsum, hci, hcj⟩ := schurNumber_spec k₂ hk2 c'
  refine ⟨i, j, kk, hsum, ?_, ?_⟩
  · have hval : (c i).val = (c j).val := by
      have := congr_arg Fin.val hci
      simp only [c'] at this
      exact this
    exact Fin.ext hval
  · have hval : (c j).val = (c kk).val := by
      have := congr_arg Fin.val hcj
      simp only [c'] at this
      exact this
    exact Fin.ext hval

-- ## Proved: S(3) = 14

/-- A sum-free 3-coloring of {1,...,13}: {1,4,10,13} / {2,3,11,12} / {5,...,9}. -/
def sumFreeColoring13 : IntegerColoring 13 3 := fun i =>
  if i.val = 0 ∨ i.val = 3 ∨ i.val = 9 ∨ i.val = 12 then (0 : Fin 3)
  else if i.val = 1 ∨ i.val = 2 ∨ i.val = 10 ∨ i.val = 11 then (1 : Fin 3)
  else (2 : Fin 3)

/-- The witness coloring has no monochromatic Schur triple. -/
theorem sumFreeColoring13_no_triple : ¬HasMonochromaticSchurTriple sumFreeColoring13 := by
  native_decide

/-- S(3) > 13: some 3-coloring of {1,...,13} avoids monochromatic triples. -/
theorem not_schurProp_13_3 : ¬SchurProp 13 3 := by
  intro h
  exact sumFreeColoring13_no_triple (h sumFreeColoring13)

/-- S(3) ≤ 14: every 3-coloring of {1,...,14} has a monochromatic Schur triple. -/
theorem schurProp_14_3 : SchurProp 14 3 := by native_decide

/-- S(3) = 14. -/
theorem schurNumber_3 : schurNumber 3 = 14 := by
  have hspec := schurNumber_spec 3 (by omega)
  have hmin := schurNumber_min 3 (by omega)
  have h_le : schurNumber 3 ≤ 14 := by
    by_contra h
    push_neg at h
    exact hmin 14 (by omega) schurProp_14_3
  have h_ge : schurNumber 3 ≥ 14 := by
    by_contra h
    push_neg at h
    have h13 : SchurProp 13 3 := schurProp_mono (by omega) hspec
    exact not_schurProp_13_3 h13
  omega

-- ## Known Values (larger cases - axiomatized)

/-- f(4) = 45. -/
axiom schurNumber_4 : schurNumber 4 = 45

/-- f(5) = 161 (Heule, 2017). -/
axiom schurNumber_5 : schurNumber 5 = 161

-- ## Bounds

/-- Lower bound: f(k) grows at least exponentially. -/
axiom schur_lower_bound :
  ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 1 ≤ k →
    C ^ k ≤ (schurNumber k : ℝ)

/-- Upper bound: f(k) ≤ C * k! for some constant C (Whitehead 1973). -/
axiom schur_upper_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
    (schurNumber k : ℝ) ≤ C * (Nat.factorial k : ℝ)

-- ## Recursive Lower Bound: S(k+1) ≥ 3·S(k) - 1

/-- castSucc is injective. -/
private theorem castSucc_inj {m : ℕ} {a b : Fin m}
    (h : a.castSucc = b.castSucc) : a = b :=
  Fin.ext (congr_arg Fin.val h)

/-- Recursive lower bound on Schur numbers.

    Given a Schur-free k-coloring c of {1,...,S(k)-1}, construct a Schur-free
    (k+1)-coloring of {1,...,3(S(k)-1)+1} by:
    - Region A (indices < n): original colors (castSucc)
    - Region B (n ≤ index ≤ 2n): new color (Fin.last k)
    - Region C (index > 2n): mirror of original colors (castSucc) -/
open Classical in
theorem schurNumber_recursive_lower (k : ℕ) (hk : k ≥ 1) :
    schurNumber (k + 1) ≥ 3 * schurNumber k - 1 := by
  have hm : schurNumber k ≥ 2 :=
    le_trans (schurNumber_1 ▸ le_refl 2) (schurNumber_nondecreasing (by omega) hk)
  set n := schurNumber k - 1 with hn_def
  have hn : n ≥ 1 := by omega
  -- By minimality, ∃ Schur-free k-coloring of {1,...,n}
  have hmin := schurNumber_min k hk n (by omega)
  unfold SchurProp at hmin; push_neg at hmin
  obtain ⟨c, hc⟩ := hmin
  -- Suffices: S(k+1) > 3n + 1 = 3S(k) - 2
  suffices hsuff : ¬SchurProp (3 * n + 1) (k + 1) by
    by_contra hlt; push_neg at hlt
    exact hsuff (schurProp_mono (show schurNumber (k + 1) ≤ 3 * n + 1 by omega)
      (schurNumber_spec (k + 1) (by omega)))
  -- Construct extended Schur-free (k+1)-coloring of {1,...,3n+1}
  intro habs
  apply hc
  -- Define c': Region A → castSucc(c), Region B → Fin.last k, Region C → castSucc(c(·-2n-1))
  let c' : IntegerColoring (3 * n + 1) (k + 1) := fun i =>
    if h₁ : i.val < n then (c ⟨i.val, h₁⟩).castSucc
    else if h₂ : i.val ≤ 2 * n then Fin.last k
    else (c ⟨i.val - (2 * n + 1), by omega⟩).castSucc
  obtain ⟨a, b, d, hsum, hab, hbd⟩ := habs c'
  -- Helpers: unfold c' in each region
  have c'_A : ∀ (i : Fin (3 * n + 1)) (hi : i.val < n),
      c' i = (c ⟨i.val, hi⟩).castSucc := by
    intro i hi; simp only [c']; rw [dif_pos hi]
  have c'_C : ∀ (i : Fin (3 * n + 1)) (hi : 2 * n < i.val),
      c' i = (c ⟨i.val - (2 * n + 1), by omega⟩).castSucc := by
    intro i hi; simp only [c']
    rw [dif_neg (show ¬(i.val < n) by omega), dif_neg (show ¬(i.val ≤ 2 * n) by omega)]
  -- Color value analysis
  have val_AC : ∀ (i : Fin (3 * n + 1)), (i.val < n ∨ 2 * n < i.val) →
      (c' i).val < k := by
    intro i hi; rcases hi with h | h
    · rw [c'_A i h]; exact (c _).isLt
    · rw [c'_C i h]; exact (c _).isLt
  have val_B : ∀ (i : Fin (3 * n + 1)), n ≤ i.val → i.val ≤ 2 * n →
      (c' i).val = k := by
    intro i h1 h2; simp only [c']
    rw [dif_neg (show ¬(i.val < n) by omega), dif_pos h2]; rfl
  -- Same color ⟹ same region type (B vs A∪C)
  -- because B gives .val = k while A∪C gives .val < k
  by_cases ha_B : n ≤ a.val ∧ a.val ≤ 2 * n
  · -- a in B: color value = k. Same for b and d by hab/hbd.
    have hca := val_B a ha_B.1 ha_B.2
    have hcb : (c' b).val = k := by have := congr_arg Fin.val hab; omega
    have hb_B : n ≤ b.val ∧ b.val ≤ 2 * n := by
      by_contra h; push_neg at h; exact absurd hcb (val_AC b h).ne
    have hcd : (c' d).val = k := by have := congr_arg Fin.val hbd; omega
    have hd_B : n ≤ d.val ∧ d.val ≤ 2 * n := by
      by_contra h; push_neg at h; exact absurd hcd (val_AC d h).ne
    -- All in B: (a+1)+(b+1) ≥ 2(n+1) > 2n+1 ≥ d+1. Contradiction.
    omega
  · -- a in A∪C: color value < k. Same for b and d.
    have ha_AC : a.val < n ∨ 2 * n < a.val := by omega
    have hca := val_AC a ha_AC
    have hcb : (c' b).val < k := by have := congr_arg Fin.val hab; omega
    have hb_AC : b.val < n ∨ 2 * n < b.val := by
      by_contra h; push_neg at h; have := val_B b h.1 h.2; omega
    have hcd : (c' d).val < k := by have := congr_arg Fin.val hbd; omega
    have hd_AC : d.val < n ∨ 2 * n < d.val := by
      by_contra h; push_neg at h; have := val_B d h.1 h.2; omega
    -- All in A∪C. Sub-case analysis: each in A or C.
    rcases ha_AC with ha | ha <;> rcases hb_AC with hb | hb <;> rcases hd_AC with hd | hd
    -- (A,A,A): direct triple in c
    · exact ⟨⟨a.val, ha⟩, ⟨b.val, hb⟩, ⟨d.val, hd⟩, hsum,
        castSucc_inj (by rw [← c'_A a ha, ← c'_A b hb]; exact hab),
        castSucc_inj (by rw [← c'_A b hb, ← c'_A d hd]; exact hbd)⟩
    -- (A,A,C): a+1+b+1 ≤ 2n, d+1 ≥ 2n+2. Contradiction.
    · omega
    -- (A,C,A): a+1 ≤ n, b+1 ≥ 2n+2, sum ≥ 2n+3 > n ≥ d+1. Contradiction.
    · omega
    -- (A,C,C): reduce (a, b-2n-1, d-2n-1) to triple in c
    · exact ⟨⟨a.val, ha⟩, ⟨b.val - (2*n+1), by omega⟩, ⟨d.val - (2*n+1), by omega⟩,
        by omega,
        castSucc_inj (by rw [← c'_A a ha, ← c'_C b hb]; exact hab),
        castSucc_inj (by rw [← c'_C b hb, ← c'_C d hd]; exact hbd)⟩
    -- (C,A,A): a+1 ≥ 2n+2, sum ≥ 2n+3 > n ≥ d+1. Contradiction.
    · omega
    -- (C,A,C): reduce (a-2n-1, b, d-2n-1) to triple in c
    · exact ⟨⟨a.val - (2*n+1), by omega⟩, ⟨b.val, hb⟩, ⟨d.val - (2*n+1), by omega⟩,
        by omega,
        castSucc_inj (by rw [← c'_C a ha, ← c'_A b hb]; exact hab),
        castSucc_inj (by rw [← c'_A b hb, ← c'_C d hd]; exact hbd)⟩
    -- (C,C,A): sum ≥ 4n+4, d+1 ≤ n. Contradiction.
    · omega
    -- (C,C,C): sum ≥ 4n+4, d+1 ≤ 3n+1. Contradiction for n ≥ 1.
    · omega

/-- S(6) ≥ 482 (from S(5) = 161 and the recursive bound). -/
theorem schurNumber_6_lower : schurNumber 6 ≥ 482 := by
  have h := schurNumber_recursive_lower 5 (by omega)
  rw [schurNumber_5] at h; omega

-- ## The Conjecture

/-- Erdős Problem #483: Is f(k) < c^k for some constant c > 0?
    That is, are Schur numbers bounded by a simple exponential? -/
axiom erdos_483_conjecture :
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
    (schurNumber k : ℝ) < c ^ k
