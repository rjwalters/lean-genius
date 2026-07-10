/-
  SLₙ(ℤ) acts transitively on primitive integer vectors — the general induction
  Open Question: bezout-identity-oq-01-oq-02-oq-02

  The grandparent `BezoutIdentityOQ01OQ02` realizes the extended Euclidean algorithm as a single
  unimodular matrix `U(a,b) ∈ SL₂(ℤ)` sending a primitive pair to `(1, 0)`; the companion
  `BezoutIdentityOQ01OQ02OQ02Descent` builds the block-embedding engine (`embedOneSL`,
  `headBlockNSL`) and the first concrete cases `sl2_transitive`, `sl3_transitive`, leaving the
  *general* induction on `n` (the sufficiency direction of transitivity) as the remaining step.

  This module closes that gap.  Working entirely in the `Fin (2 + m)` index convention — so that
  `2 + (m + 1)` is *definitionally* `(2 + m) + 1` and the `Fin.cons` / `embedOne` / `headBlockN`
  types line up without transport — it proves the sharp statement

    * `reduce_to_gcd` : every `v ∈ ℤ^{2+m}` is carried by some `M ∈ SL₍₂₊ₘ₎(ℤ)` to its gcd-normal
      form `(g, 0, …, 0)` with `g = gcd(vᵢ) ≥ 0`, tracking the divisibility `∀ i, g ∣ vᵢ`;

  from which the two headline results follow immediately:

    * `sl2_gcd_reduction` : the honest base case — an *arbitrary* pair `(a, b)` (not only coprime)
      is reduced to `(gcd a b, 0)` by `SL₂(ℤ)`;
    * `sln_transitive` : a **primitive** `v ∈ ℤ^{2+m}` is carried to the first standard basis vector
      `e₀ = (1, 0, …, 0)` by `SL₍₂₊ₘ₎(ℤ)` — exactly the converse (sufficiency) direction the open
      question asks for, and the arbitrary-`n` generalization of the grandparent's `n = 2` Bézout
      reduction.

  The induction is the two-step template `headBlockN` ∘ `embedOne` made uniform in `n`: `embedOne`
  of the `SL₍₂₊ₘ₎` gcd-reducer of the tail clears coordinates `2 … n` against coordinate `1`,
  leaving `(v₀, g_tail, 0, …, 0)`; then the head block `headBlockN` applied to the `SL₂` gcd-reducer
  of `(v₀, g_tail)` clears coordinate `1` against coordinate `0`.  The single content bridge is
  `cons_gcdForm`, repackaging the `Fin.cons`-shaped output of `embedOne` as the `Fin.append`-shaped
  input of `headBlockN`.  No new axioms are introduced.

  References:
  - Newman, "Integral Matrices" (1972), Ch. II (unimodular reduction, elementary divisors).
  - Grandparent `BezoutIdentityOQ01OQ02` (`bezoutMatrix`, `bezoutMatrix_mulVec`).
  - Companion `BezoutIdentityOQ01OQ02OQ02Descent` (`embedOneSL`, `headBlockNSL`).

  BUILD STATUS (2026-07-09): **UNVERIFIED — not yet machine-checked.**  The Docker build
  infrastructure was down this session (containerd content-store blob I/O error, operator-level)
  and the Aristotle service was unreachable, so this file could not be elaborated even once.  The
  proof strategy was validated by hand and every Mathlib API call was cross-checked against the
  pinned Mathlib source (`Fin.append`/`cons` lemmas, `Matrix.mulVec_mulVec`,
  `SpecialLinearGroup.coe_mul`, `Int.gcd_dvd_left/right`, `Int.eq_one_of_dvd_one`), but the two
  pure-`Fin` bridge lemmas below (`gcdForm_two`, `cons_gcdForm`) are finicky index-arithmetic
  tactic proofs and are the most likely to need adjustment on first build.  Do NOT report this entry
  as `verified` until a clean build confirms it.
-/

import Mathlib
import Proofs.BezoutIdentityOQ01OQ02
import Proofs.BezoutIdentityOQ01OQ02OQ02
import Proofs.BezoutIdentityOQ01OQ02OQ02Descent

namespace BezoutDescent

open Matrix

/-! ### Base case, general form: `SL₂(ℤ)` reduces an arbitrary pair to `(gcd, 0)` -/

/-- **Full `n = 2` gcd reduction.**  For *any* pair `(a, b)` — not only coprime ones — there is an
element of `SL₂(ℤ)` carrying `(a, b)` to `(gcd a b, 0)`.  The coprime `sl2_transitive` is the
special case `gcd a b = 1`; the degenerate `gcd a b = 0` case (`a = b = 0`) uses the identity. -/
theorem sl2_gcd_reduction (a b : ℤ) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (M : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  by_cases h : Int.gcd a b = 0
  · obtain ⟨ha, hb⟩ := Int.gcd_eq_zero_iff.mp h
    refine ⟨1, ?_⟩
    subst ha; subst hb
    simp [h]
  · exact ⟨⟨BezoutIdentityOQ01OQ02.bezoutMatrix a b,
        BezoutIdentityOQ01OQ02.bezoutMatrix_det a b h⟩,
      BezoutIdentityOQ01OQ02.bezoutMatrix_mulVec a b⟩

/-! ### The gcd-normal form vector and the `cons`/`append` content bridge -/

/-- The gcd-normal form target vector `(g, 0, …, 0) ∈ ℤ^{2+m}`, written with `Fin.append` so that it
matches the output shape of the head-block action `headBlockN_mulVec`. -/
def gcdForm (m : ℕ) (g : ℤ) : Fin (2 + m) → ℤ :=
  Fin.append (![g, 0] : Fin 2 → ℤ) (0 : Fin m → ℤ)

theorem gcdForm_two (g : ℤ) : gcdForm 0 g = ![g, 0] := by
  funext i
  fin_cases i <;> simp [gcdForm, Fin.append_left]

/-- **Content bridge.**  Prepending `a` to the gcd-normal form `(b, 0, …, 0) ∈ ℤ^{2+m}` gives the
vector `(a, b, 0, …, 0) ∈ ℤ^{2+(m+1)}`, repackaged in `Fin.append` shape so the head block acts. -/
theorem cons_gcdForm (m : ℕ) (a b : ℤ) :
    Fin.cons a (gcdForm m b) = Fin.append (![a, b] : Fin 2 → ℤ) (0 : Fin (m + 1) → ℤ) := by
  funext i
  -- split the ambient `Fin (2 + (m + 1))` into the first two coordinates and the tail
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · -- left block: the two leading coordinates, `j : Fin 2`
    rw [Fin.append_left]
    fin_cases j
    · -- coordinate 0 → `a` (head of the `Fin.cons`)
      simp [gcdForm]
    · -- coordinate 1 → `b` (head of the inner `Fin.append` inside `gcdForm`)
      simp [gcdForm, Fin.append_left]
  · -- right block: the remaining coordinates, `j : Fin (m + 1)`; every entry is `0`
    rw [Fin.append_right]
    -- `Fin.natAdd 2 j = (Fin.natAdd 1 j).succ`, so the `Fin.cons` peels to the tail append
    have hj : (Fin.natAdd 2 j : Fin (2 + (m + 1))) = (Fin.natAdd 1 j).succ := by
      apply Fin.ext; simp [Fin.natAdd, Fin.succ, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
    rw [hj, Fin.cons_succ]
    simp [gcdForm, Fin.append_right]

/-! ### The general reduction to gcd-normal form -/

/-- **General gcd reduction / transitivity engine.**  Every integer vector `v ∈ ℤ^{2+m}` is carried
by an element of `SL₍₂₊ₘ₎(ℤ)` to its gcd-normal form `(g, 0, …, 0)`, where `g = gcd(vᵢ) ≥ 0`.  The
divisibility clause `∀ i, g ∣ vᵢ` is what threads the gcd through the induction and lets primitivity
collapse `g` to `1`.

Proof by induction on `m` in the `2 + m` convention.  The base case `m = 0` is `sl2_gcd_reduction`;
the step reduces the tail with the induction hypothesis (via `embedOne`), then clears the second
coordinate against the first with the `SL₂` gcd-reducer of `(v₀, g_tail)` (via `headBlockN`). -/
theorem reduce_to_gcd (m : ℕ) :
    ∀ v : Fin (2 + m) → ℤ,
      ∃ (M : Matrix.SpecialLinearGroup (Fin (2 + m)) ℤ) (g : ℤ),
        (M : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) *ᵥ v = gcdForm m g ∧
          0 ≤ g ∧ ∀ i, g ∣ v i := by
  induction m with
  | zero =>
    intro v
    obtain ⟨N, hN⟩ := sl2_gcd_reduction (v 0) (v 1)
    refine ⟨N, (Int.gcd (v 0) (v 1) : ℤ), ?_, Int.natCast_nonneg _, ?_⟩
    · rw [gcdForm_two, ← hN]
      congr 1
      funext i; fin_cases i <;> rfl
    · intro i
      fin_cases i
      · exact Int.gcd_dvd_left ..
      · exact Int.gcd_dvd_right ..
  | succ m ih =>
    intro v
    obtain ⟨T, gw, hT, _hgw_nonneg, hgw_dvd⟩ := ih (Fin.tail v)
    obtain ⟨N, hN⟩ := sl2_gcd_reduction (v 0) gw
    set g : ℤ := (Int.gcd (v 0) gw : ℤ) with hg
    -- Step 1: `embedOne` of the tail reducer clears coordinates `2 … n`.
    have hE : (embedOneSL T : Matrix (Fin (2 + (m + 1))) (Fin (2 + (m + 1))) ℤ) *ᵥ v
        = Fin.cons (v 0) (gcdForm m gw) := by
      rw [embedOneSL_coe]
      have h1 := embedOne_mulVec (T : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) (v 0) (Fin.tail v)
      rw [Fin.cons_self_tail] at h1
      rw [h1, hT]
    -- Step 2: the head block clears coordinate `1` against coordinate `0`.
    have hHd : (headBlockNSL N : Matrix (Fin (2 + (m + 1))) (Fin (2 + (m + 1))) ℤ)
        *ᵥ Fin.cons (v 0) (gcdForm m gw) = gcdForm (m + 1) g := by
      rw [cons_gcdForm]
      show headBlockN (N : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ Fin.append ![v 0, gw] (0 : Fin (m + 1) → ℤ)
          = gcdForm (m + 1) g
      rw [headBlockN_mulVec, hN]
      rfl
    refine ⟨headBlockNSL N * embedOneSL T, g, ?_, Int.natCast_nonneg _, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hE, hHd]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [hg]; exact Int.gcd_dvd_left ..
      · have hgw : g ∣ gw := by rw [hg]; exact Int.gcd_dvd_right ..
        have := hgw.trans (hgw_dvd j)
        simpa [Fin.tail] using this

/-! ### Headline: transitivity on primitive vectors -/

/-- **`SLₙ(ℤ)` acts transitively on primitive vectors** (`n = 2 + m ≥ 2`).  A primitive vector
`v ∈ ℤ^{2+m}` (some integer combination of its entries equals `1`) is carried to the first standard
basis vector `e₀ = (1, 0, …, 0)` by an element of `SL₍₂₊ₘ₎(ℤ)`.  This is the sufficiency (converse)
direction of transitivity — the arbitrary-`n` generalization of the grandparent's Bézout reduction
and the open question's target.  `gcdForm m 1` is `(1, 0, …, 0)`. -/
theorem sln_transitive {m : ℕ} (v : Fin (2 + m) → ℤ) (h : BezoutPrimitive.IsPrimitive v) :
    ∃ M : Matrix.SpecialLinearGroup (Fin (2 + m)) ℤ,
      (M : Matrix (Fin (2 + m)) (Fin (2 + m)) ℤ) *ᵥ v = gcdForm m 1 := by
  obtain ⟨M, g, hM, hg0, hgdvd⟩ := reduce_to_gcd m v
  obtain ⟨w, hw⟩ := h
  have hg1 : g ∣ (w ⬝ᵥ v) := Finset.dvd_sum (fun i _ => (hgdvd i).mul_left (w i))
  rw [hw] at hg1
  have : g = 1 := Int.eq_one_of_dvd_one hg0 hg1
  rw [this] at hM
  exact ⟨M, hM⟩

end BezoutDescent
