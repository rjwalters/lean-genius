/-
Erdős Problem #476, Open Question 5: Vosper's Theorem — AP endpoint position analysis.

Standalone proof of `ap_sdiff_endpoint`, the lemma that identifies the position of
a removed element `a₀` relative to the arithmetic progression `A' = A.erase a₀`,
used in the AP pull-back step of the Dyson e-transform induction. This discharges
the `sorry` at `Erdos476OQ05Aristotle.lean:132`.

Math: map both APs to "intervals mod p" via x ↦ (x - s₂)·d⁻¹ (a ZMod-p bijection).
AP₂ becomes {0,…,m-1} and AP₁ becomes {c, c+1, …, c+(n-1)} with c = (s₁-s₂)·d⁻¹.
With n + m ≤ p there is no double wraparound, so |AP₁ \ AP₂| = #{i < n : (γ+i) mod p ≥ m}
where γ = c.val. Setting this count to 1 forces γ = m-n+1 (successor) or γ = p-1
(predecessor), i.e. s₁ = s₂ + (m-n+1)·d or s₁ = s₂ - d.

No `sorry`, no `axiom`.
-/
import Mathlib

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05APEndpoint

variable {p : ℕ} [hp : Fact p.Prime]

/-- An arithmetic progression in ZMod p starting at `a` with difference `d`. -/
def IsArithmeticProgression (A : Finset (ZMod p)) (a d : ZMod p) : Prop :=
  A = (Finset.range A.card).image (fun (i : ℕ) => a + (i : ZMod p) * d)

/-- Pure-Nat counting core: with no double wraparound (`n + m ≤ p`), the count of
`i < n` whose shifted residue `(γ + i) mod p` lands at or beyond `m` equals 1 only
when `γ = m - n + 1` (no wrap) or `γ = p - 1` (wrap). -/
lemma count_eq_one_aux {n m p γ : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m)
    (hnmp : n + m ≤ p) (hγ : γ < p)
    (hcount : ((Finset.range n).filter (fun i => m ≤ (γ + i) % p)).card = 1) :
    γ = m - n + 1 ∨ γ = p - 1 := by
  by_cases hwrap : γ + n ≤ p
  · -- No wrap: every residue is exact, the count is a clean interval length.
    left
    have hfilter : (Finset.range n).filter (fun i => m ≤ (γ + i) % p)
        = Finset.Ico (m - γ) n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hi, hmod⟩
        have hlt : γ + i < p := by omega
        rw [Nat.mod_eq_of_lt hlt] at hmod
        omega
      · rintro ⟨hge, hi⟩
        refine ⟨hi, ?_⟩
        have hlt : γ + i < p := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
    rw [hfilter, Nat.card_Ico] at hcount
    omega
  · -- Wrap: exactly the high block {γ,…,p-1} clears the threshold, count = p - γ.
    right
    push_neg at hwrap
    have hfilter : (Finset.range n).filter (fun i => m ≤ (γ + i) % p)
        = Finset.range (p - γ) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hi, hmod⟩
        by_cases hip : γ + i < p
        · omega
        · -- i ≥ p - γ would push the wrapped residue below m, contradicting hmod
          have hmodval : (γ + i) % p = γ + i - p := by
            conv_lhs => rw [show γ + i = p + (γ + i - p) by omega]
            rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          rw [hmodval] at hmod
          omega
      · intro hi
        have hin : i < n := by omega
        have hlt : γ + i < p := by omega
        refine ⟨hin, ?_⟩
        rw [Nat.mod_eq_of_lt hlt]
        omega
    rw [hfilter, Finset.card_range] at hcount
    omega

/-- **Position analysis** (Vosper AP pull-back). When `AP₁` (start `s₁`, length `n`,
diff `d`) and `AP₂` (start `s₂`, length `m`, diff `d`) satisfy `(AP₁ \ AP₂).card = 1`
with `n ≤ m` and `n + m ≤ p`, then `s₁ = s₂ - d` (predecessor) or
`s₁ = s₂ + (m - n + 1)·d` (successor). -/
lemma ap_sdiff_endpoint (AP₁ AP₂ : Finset (ZMod p)) (s₁ s₂ d : ZMod p)
    (hAP₁ : IsArithmeticProgression AP₁ s₁ d)
    (hAP₂ : IsArithmeticProgression AP₂ s₂ d)
    (hd : d ≠ 0)
    (h₁ : 2 ≤ AP₁.card)
    (h₁₂ : AP₁.card ≤ AP₂.card)
    (hlt : AP₁.card + AP₂.card ≤ p)
    (h_sdiff : (AP₁ \ AP₂).card = 1) :
    s₁ = s₂ - d ∨ s₁ = s₂ + ((AP₂.card - AP₁.card + 1 : ℕ) : ZMod p) * d := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  -- Abbreviations
  set n := AP₁.card with hn_def
  set m := AP₂.card with hm_def
  set f : ℕ → ZMod p := fun i => s₁ + (i : ZMod p) * d with hf_def
  set c : ZMod p := (s₁ - s₂) * d⁻¹ with hc_def
  set γ : ℕ := c.val with hγ_def
  -- AP defining equations
  simp only [IsArithmeticProgression] at hAP₁ hAP₂
  rw [← hn_def] at hAP₁
  rw [← hm_def] at hAP₂
  -- Bounds
  have hn2 : 2 ≤ n := h₁
  have hnm : n ≤ m := h₁₂
  have hnmp : n + m ≤ p := hlt
  have hnp : n < p := by omega
  have hmp : m < p := by omega
  have hγp : γ < p := ZMod.val_lt c
  -- `f` is injective on `range n` (n < p, d ≠ 0)
  have hf_inj : Set.InjOn f (Finset.range n) := by
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rw [hf_def] at hfij
    simp only at hfij
    have h1 : (i : ZMod p) * d = (j : ZMod p) * d := by
      have := add_left_cancel hfij; exact this
    have h2 : (i : ZMod p) = (j : ZMod p) := mul_right_cancel₀ hd h1
    have hval := congrArg ZMod.val h2
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at hval
  -- Residue bridge: for i < p, (c + i).val = (γ + i) % p
  have hres : ∀ i : ℕ, i < p → (c + (i : ZMod p)).val = (γ + i) % p := by
    intro i hip
    rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hip, hγ_def]
  -- Membership characterization: for i < n, f i ∈ AP₂ ↔ (γ + i) % p < m
  have hmem : ∀ i : ℕ, i < n → (f i ∈ AP₂ ↔ (γ + i) % p < m) := by
    intro i hin
    have hip : i < p := by omega
    rw [hAP₂]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hji⟩
      -- s₂ + j·d = f i = s₁ + i·d  ⟹  (j : ZMod p) = c + i
      have hjc : (j : ZMod p) = c + (i : ZMod p) := by
        rw [hf_def] at hji; simp only at hji
        have hstep : (j : ZMod p) * d = (s₁ - s₂) + (i : ZMod p) * d := by
          linear_combination hji
        apply mul_right_cancel₀ hd
        rw [hstep, hc_def, add_mul, mul_assoc, inv_mul_cancel₀ hd, mul_one]
      have hvalj : (γ + i) % p = j := by
        rw [← hres i hip, ← hjc, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      omega
    · intro hwm
      refine ⟨(γ + i) % p, by omega, ?_⟩
      -- reconstruct: s₂ + ((γ+i)%p)·d = f i
      have hcast : (((γ + i) % p : ℕ) : ZMod p) = c + (i : ZMod p) := by
        rw [← hres i hip, ZMod.natCast_zmod_val]
      rw [hf_def]; simp only
      rw [hcast, hc_def]
      field_simp
      ring
  -- Reduce |AP₁ \ AP₂| to the Nat count
  have hsdiff_eq : AP₁ \ AP₂
      = ((Finset.range n).filter (fun i => m ≤ (γ + i) % p)).image f := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx1, hx2⟩
      rw [hAP₁] at hx1
      simp only [Finset.mem_image, Finset.mem_range] at hx1
      obtain ⟨i, hin, hfi⟩ := hx1
      refine ⟨i, ⟨hin, ?_⟩, hfi⟩
      rw [← hfi] at hx2
      have := (hmem i hin).not.mp hx2
      omega
    · rintro ⟨i, ⟨hin, hge⟩, hfi⟩
      refine ⟨?_, ?_⟩
      · rw [hAP₁]; simp only [Finset.mem_image, Finset.mem_range]; exact ⟨i, hin, hfi⟩
      · rw [← hfi]
        rw [hmem i hin]; omega
  have hcard : (AP₁ \ AP₂).card
      = ((Finset.range n).filter (fun i => m ≤ (γ + i) % p)).card := by
    rw [hsdiff_eq, Finset.card_image_of_injOn]
    apply hf_inj.mono
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_range, Set.mem_setOf_eq] at hx ⊢
    exact hx.1
  rw [hcard] at h_sdiff
  -- Apply the Nat counting core
  have hcore := count_eq_one_aux hn2 hnm hnmp hγp h_sdiff
  -- Translate γ-conclusion back to s₁
  have hcd : c * d = s₁ - s₂ := by
    rw [hc_def, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  rcases hcore with hgeq | hgeq
  · -- γ = m - n + 1  ⟹  c = (m-n+1 : ZMod p)  ⟹  successor
    right
    have hcval : c = ((m - n + 1 : ℕ) : ZMod p) := by
      rw [← ZMod.natCast_zmod_val c, ← hγ_def, hgeq]
    have : s₁ - s₂ = ((m - n + 1 : ℕ) : ZMod p) * d := by rw [← hcd, hcval]
    rw [hm_def, hn_def] at this ⊢
    linear_combination this
  · -- γ = p - 1  ⟹  c = -1  ⟹  predecessor
    left
    have hcval : c = ((p - 1 : ℕ) : ZMod p) := by
      rw [← ZMod.natCast_zmod_val c, ← hγ_def, hgeq]
    have hcneg : c = -1 := by
      rw [hcval, Nat.cast_sub hp.out.pos, ZMod.natCast_self]
      simp
    have : s₁ - s₂ = -1 * d := by rw [← hcd, hcneg]
    linear_combination this

end Erdos476OQ05APEndpoint
