/-
  HGCD (Half-GCD) -- Schönhage's recursive cofactor algorithm

  Open question OQ-02 of binary-gcd-OQ-03: can Schönhage's recursive
  HGCD be formalized?  We split the question into three parts:

  (A) **Correctness**: there is a function `hgcdMatrix : ℕ → ℕ → CofactorMatrix`
      such that for all `a b : ℕ`, `(hgcdMatrix a b).det ∈ {±1}` and
      applying it to `(a, b)` preserves `Nat.gcd a b`.

  (B) **Size reduction**: applying `hgcdMatrix a b` reduces the bitsize
      of `max a b` by approximately half (the genuinely new mathematical
      content vs. plain Lehmer).

  (C) **Bit complexity** O(M(n) log n): currently inexpressible in Mathlib
      because there is no bit-complexity model of arithmetic and no fast
      multiplication. Deferred -- documented as a Mathlib infrastructure gap.

  This file establishes (A) and the structural skeleton for (B). The
  size-reduction lemma is stated with the precise quantitative bound and
  marked `sorry`; closing it is the focus of follow-up sessions.

  All cofactor-matrix machinery (det, mul, apply, GCD invariance under
  unimodular matrices) is reused from `BinaryGcdOQ03.lean`.

  **Cofactor convention.** `lehmerCofactors` accumulates the cofactor
  matrix in the row-vector convention: each Lehmer step `S_k`
  right-multiplies the accumulator (`M' = M · S_k`), so the invariant
  maintained is `(a₀, b₀) · M = (current pair)`.

  Consequently this file's `applyToNat M a b` performs the row-vector
  product `(a, b) · M = (a·M.α + b·M.γ, a·M.β + b·M.δ)`, *not* the
  column-vector `M.apply` from `BinaryGcdOQ03.lean`. Both products
  preserve `Nat.gcd` when `det M = ±1`, but only the row product yields
  the actual reduced pair from the iterated Lehmer steps. The
  composition order in `hgcdMatrix` (`M_top.mul M_rec`, with the top
  step on the *left*) is similarly chosen so that
  `(a, b) · (M_top · M_rec) = ((a, b) · M_top) · M_rec` matches "apply
  the top-half step first, then recurse".

  References:
  - Schönhage (1971), "Schnelle Berechnung von Kettenbruchentwicklungen"
  - Brent & Zimmermann, "Modern Computer Arithmetic", §1.6.3
  - Stehlé & Zimmermann (2004), "A binary recursive gcd algorithm"
-/

import Proofs.BinaryGcdOQ03

open Nat Int

namespace LehmerGcd

-- ═══════════════════════════════════════════════════════════════
-- PART I: HGCD DEFINITION
-- ═══════════════════════════════════════════════════════════════

/-- Threshold below which HGCD bottoms out and returns the identity
    cofactor matrix. The caller is expected to fall back to plain
    Euclidean / Lehmer reduction below this size. -/
def hgcdThreshold : ℕ := 4

/-- One Lehmer-style reduction step on the top half of the bits of `(a, b)`.
    Given `a b : ℕ` with `max a b ≥ 2^hgcdThreshold`, extracts the top
    `n - n/2` bits and runs `lehmerCofactors` on the approximation to
    get a cofactor matrix.  Used as the recursive base step inside HGCD. -/
def hgcdTopHalfStep (a b : ℕ) : CofactorMatrix :=
  let n := Nat.log 2 (max a b) + 1
  let shift := n / 2
  let aHi := a / 2 ^ shift
  let bHi := b / 2 ^ shift
  -- Run plain Lehmer cofactor accumulation on the top half.
  -- Using the same `lehmerCofactors` routine that already has det-unit
  -- accounted for in BinaryGcdOQ03.
  lehmerCofactors n aHi bHi CofactorMatrix.id

/-- Apply a cofactor matrix to a non-negative pair, taking absolute values
    of the result.

    **Convention.** `lehmerCofactors` accumulates the cofactor matrix in the
    *row-vector* convention: each Lehmer step `S_k` right-multiplies the
    accumulator (`M' = M · S_k`), so the invariant maintained is
    `(a₀, b₀) · M = (current pair)`. Hence "applying" `M` to `(a, b)` to
    obtain the Lehmer-reduced pair means computing the row-vector product
    `(a, b) · M = (a·M.α + b·M.γ, a·M.β + b·M.δ)`.

    This is *not* the column-vector product `M.apply (a, b)` from
    `BinaryGcdOQ03.lean` (which would give `(M.α·a + M.β·b, M.γ·a + M.δ·b)`).
    Both products preserve `Nat.gcd` when `det M = ±1`, but only the
    row-vector product yields the actual reduced pair from the iterated
    Lehmer steps. See knowledge.md / state.md for the worked counterexample
    `(a, b) = (1000, 300)` where the column form does *not* reduce. -/
def applyToNat (M : CofactorMatrix) (a b : ℕ) : ℕ × ℕ :=
  let u : ℤ := (a : ℤ) * M.α + (b : ℤ) * M.γ
  let v : ℤ := (a : ℤ) * M.β + (b : ℤ) * M.δ
  (u.natAbs, v.natAbs)

/-- Recursive HGCD with explicit fuel. Returns a cofactor matrix `M` whose
    determinant is `±1` and which preserves `Nat.gcd`. The size-reduction
    property is stated separately.

    The recursive composition order — `M_top.mul M_rec` rather than
    `M_rec.mul M_top` — matches the row-vector convention: row-applying
    the composite is `(a, b) · M_top · M_rec`, i.e. apply the top-half
    step first, then apply the recursive matrix to the reduced pair. -/
def hgcdMatrix : (fuel a b : ℕ) → CofactorMatrix
  | 0,        _, _ => CofactorMatrix.id
  | fuel + 1, a, b =>
    if max a b < 2 ^ hgcdThreshold then
      CofactorMatrix.id
    else
      -- Step 1: reduce on the top half of the bits.
      -- Step 2: recurse on the reduced pair, compose, and return.
      -- (Branching on whether the half-reduced pair is small enough
      --  to skip the recursive call.)
      if (max (applyToNat (hgcdTopHalfStep a b) a b).1
              (applyToNat (hgcdTopHalfStep a b) a b).2)
          < 2 ^ hgcdThreshold then
        hgcdTopHalfStep a b
      else
        (hgcdTopHalfStep a b).mul
          (hgcdMatrix fuel
            (applyToNat (hgcdTopHalfStep a b) a b).1
            (applyToNat (hgcdTopHalfStep a b) a b).2)

-- ═══════════════════════════════════════════════════════════════
-- PART II: DETERMINANT IS ±1
-- ═══════════════════════════════════════════════════════════════

/-- The Lehmer cofactor accumulator preserves det = ±1 starting from
    the identity. Re-stated here for `hgcdTopHalfStep`. -/
theorem hgcdTopHalfStep_det_unit (a b : ℕ) :
    (hgcdTopHalfStep a b).det = 1 ∨ (hgcdTopHalfStep a b).det = -1 := by
  unfold hgcdTopHalfStep
  exact lehmerCofactors_det_unit _ _ _ _ (Or.inl CofactorMatrix.det_id)

/-- Helper: a product of two `±1` integers is itself `±1`. -/
private theorem mul_unit_of_unit_of_unit {x y : ℤ}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    subst hx <;> subst hy <;> simp

/-- The recursive HGCD matrix has determinant `±1`.

    Proof is by induction on the fuel. The fuel-zero case returns the
    identity matrix (det = 1). At successor fuel the definition has two
    nested `if`s; we branch on each and use `hgcdTopHalfStep_det_unit`
    plus the inductive hypothesis. The composed case uses
    `CofactorMatrix.det_mul`. -/
theorem hgcdMatrix_det_unit (fuel a b : ℕ) :
    (hgcdMatrix fuel a b).det = 1 ∨ (hgcdMatrix fuel a b).det = -1 := by
  induction fuel generalizing a b with
  | zero => left; exact CofactorMatrix.det_id
  | succ n ih =>
    simp only [hgcdMatrix]
    split_ifs with h₁ h₂
    · left; exact CofactorMatrix.det_id
    · exact hgcdTopHalfStep_det_unit a b
    · rw [CofactorMatrix.det_mul]
      exact mul_unit_of_unit_of_unit
        (hgcdTopHalfStep_det_unit a b)
        (ih (applyToNat (hgcdTopHalfStep a b) a b).1
            (applyToNat (hgcdTopHalfStep a b) a b).2)

-- ═══════════════════════════════════════════════════════════════
-- PART III: GCD PRESERVATION
-- ═══════════════════════════════════════════════════════════════

/-- Applying `hgcdMatrix` to `(a, b)` (row convention) preserves the GCD.
    This is the row-vector analogue of `cofactor_apply_gcd`; it follows from
    `gcd_cofactor_eq` applied to the relabelled coefficients
    `(α, β, γ, δ) ← (M.α, M.γ, M.β, M.δ)`, since the determinant condition
    `α·δ - β·γ = M.α·M.δ - M.γ·M.β = M.det = ±1` is symmetric under the
    swap `β ↔ γ`. -/
theorem hgcdMatrix_apply_gcd (fuel a b : ℕ) :
    let M := hgcdMatrix fuel a b
    Int.gcd ((↑a : ℤ) * M.α + ↑b * M.γ) ((↑a : ℤ) * M.β + ↑b * M.δ)
      = Nat.gcd a b := by
  set M := hgcdMatrix fuel a b
  have hdet : M.α * M.δ - M.γ * M.β = 1 ∨ M.α * M.δ - M.γ * M.β = -1 := by
    have h := hgcdMatrix_det_unit fuel a b
    simp only [CofactorMatrix.det] at h
    rcases h with h | h
    · left; linarith
    · right; linarith
  have h := gcd_cofactor_eq (α := M.α) (β := M.γ) (γ := M.β) (δ := M.δ)
              (a := a) (b := b) hdet
  -- h : Int.gcd (M.α * ↑a + M.γ * ↑b) (M.β * ↑a + M.δ * ↑b) = Nat.gcd a b
  -- Goal differs only by commutativity of `*` on `ℤ`.
  have eq1 : (↑a : ℤ) * M.α + ↑b * M.γ = M.α * ↑a + M.γ * ↑b := by ring
  have eq2 : (↑a : ℤ) * M.β + ↑b * M.δ = M.β * ↑a + M.δ * ↑b := by ring
  rw [eq1, eq2]
  exact h

-- ═══════════════════════════════════════════════════════════════
-- PART IV: SIZE REDUCTION (the genuinely new content)
-- ═══════════════════════════════════════════════════════════════

/-- The bitsize of a natural number: `Nat.log 2 n + 1` for `n > 0`,
    and `0` for `n = 0`. -/
def bitsize (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log 2 n + 1

@[simp] theorem bitsize_zero : bitsize 0 = 0 := by simp [bitsize]

/-- **Size reduction (statement)**: for inputs above the HGCD threshold,
    one application of `hgcdMatrix` reduces `bitsize (max a b)` to
    approximately `bitsize (max a b) / 2 + c`.

    This is the only mathematically novel claim in the file relative to
    `BinaryGcdOQ03.lean`; closing it is the next-session focus.

    The constant `c = hgcdThreshold + 2` is an over-approximation; the
    Brent–Zimmermann analysis gives `c = O(1)` more precisely. -/
theorem hgcdMatrix_size_reduction (fuel a b : ℕ)
    (hfuel : bitsize (max a b) ≤ fuel)
    (hbig : 2 ^ hgcdThreshold ≤ max a b) :
    bitsize (max (applyToNat (hgcdMatrix fuel a b) a b).1
                 (applyToNat (hgcdMatrix fuel a b) a b).2)
      ≤ bitsize (max a b) / 2 + (hgcdThreshold + 2) := by
  -- Deferred: this is the substantive next-session goal. The proof
  -- requires:
  --   (a) bounding the entries of `hgcdTopHalfStep a b` by
  --       2^(bitsize(max a b)/2 + 2) (a Lehmer accumulator entry-bound
  --       lemma — likely Mathlib gap, may need to prove inline);
  --   (b) using the unimodularity to bound the entries of the inverse
  --       and hence the difference between (a, b) and the new pair;
  --   (c) iterating the half-reduction twice (once for the top step,
  --       once for the recursive call) to halve the bitsize.
  -- See research/problems/binary-gcd-oq-03-oq-02/state.md.
  sorry

-- ═══════════════════════════════════════════════════════════════
-- PART V: COMPLEXITY (DEFERRED)
-- ═══════════════════════════════════════════════════════════════

/-! ### Bit-complexity claim — deferred

The classical Schönhage analysis gives `T_hgcd(n) = O(M(n) · log n)`
where `M(n)` is the bit cost of multiplying two `n`-bit integers and
`n = bitsize(max a b)`. We **cannot state this in Lean today** because:

* Mathlib has no bit-complexity model for arithmetic. `Computability`
  has Turing machines and `primrec` / `partrec`, but nothing that
  attaches "bit operations" to integer arithmetic primitives.
* Mathlib has no fast multiplication (Karatsuba, Toom–Cook,
  Schönhage–Strassen). All multiplication on `ℕ` / `ℤ` is opaque.
* There is no big-integer-as-array-of-words representation in Mathlib;
  `ℕ` and `ℤ` are abstract algebraic structures.

Filling these gaps is a multi-thousand-line Mathlib-contribution
initiative; we therefore document the complexity claim here without
attempting to formalise it. -/

-- ═══════════════════════════════════════════════════════════════
-- PART VI: COMPUTATIONAL SANITY CHECKS
-- ═══════════════════════════════════════════════════════════════

example : (hgcdMatrix 0 100 80).det = 1 := by
  unfold hgcdMatrix
  exact CofactorMatrix.det_id

example : (hgcdMatrix 5 7 3).det = 1 ∨ (hgcdMatrix 5 7 3).det = -1 :=
  hgcdMatrix_det_unit 5 7 3

example :
    let M := hgcdMatrix 4 5 3
    Int.gcd ((5 : ℤ) * M.α + (3 : ℤ) * M.γ) ((5 : ℤ) * M.β + (3 : ℤ) * M.δ)
      = Nat.gcd 5 3 :=
  hgcdMatrix_apply_gcd 4 5 3

/-- **Convention sanity check.** For `(a, b) = (1000, 300)` the top-half
    Lehmer step extracts `aHi = 31, bHi = 9` (`shift = 5`) and runs two
    cofactor steps, yielding `M = ⟨1, -2, -3, 7⟩`.

    * Row-apply (this file's convention):
      `(1000·1 + 300·(-3), 1000·(-2) + 300·7) = (100, 100)` — reduced.
    * Column-apply (the previous, *incorrect*, convention):
      `(1·1000 + (-2)·300, (-3)·1000 + 7·300) = (400, -900)` — *not* reduced.

    Both pairs preserve `Nat.gcd 1000 300 = 100`, but only the row-apply
    pair is a valid Lehmer reduction (max bit-size 7 < 10). -/
example : applyToNat (hgcdTopHalfStep 1000 300) 1000 300 = (100, 100) := by
  native_decide

/-! ## Summary

**Established (1 sorry, 0 axioms)**

* Definitions: `hgcdThreshold`, `hgcdTopHalfStep`, `applyToNat`, `hgcdMatrix`.
* `hgcdTopHalfStep_det_unit`: the top-half Lehmer step keeps `det = ±1`.
* `hgcdMatrix_det_unit`: the recursive HGCD matrix is unimodular.
* `hgcdMatrix_apply_gcd`: applying the HGCD matrix preserves `Nat.gcd`.

**Deferred**

* `hgcdMatrix_size_reduction`: stated, currently `sorry`. Proving it is
  the genuinely new mathematical content of this OQ; see Part IV docstring.
* Bit complexity `O(M(n) log n)`: not formulable in Mathlib today; see
  Part V docstring for the foundational gaps.
-/

end LehmerGcd
