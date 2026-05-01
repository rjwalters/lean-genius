import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Proofs.BezoutIdentityOQ03

/-!
# CRT for Finitely Many Coprime Moduli via Bézout (bezout-identity-oq-03-oq-02)

## Open Question
Extend the 2-moduli CRT (`bezout-identity-oq-03`) to finitely many pairwise
coprime moduli `m : Fin k → ℤ`, by induction on `k`.

## Approach
- Base case `k = 0`: trivially `x = 0` works (no constraints).
- Inductive step: split off the last index. Get a solution `y` for indices
  `Fin k` (without the last one). Then apply the 2-moduli CRT
  (`crt_via_bezout`) to combine `y` (mod `M = ∏ i, m i.castSucc`) with
  `a (Fin.last k)` (mod `m (Fin.last k)`). Coprimality of `m (Fin.last k)`
  with `M` follows from `IsCoprime.prod_right`.
- Uniqueness mirrors existence: any two solutions are congruent modulo the
  product, by `IsCoprime.mul_dvd` + induction.

## Status
- 0 sorries, 0 axioms
- Builds directly on `BezoutIdentityOQ03` (parent: 2-moduli CRT via Bézout)
- Uses `IsCoprime.prod_right` and `Finset.dvd_prod_of_mem` from Mathlib
-/

set_option maxHeartbeats 400000

namespace BezoutIdentityOQ03OQ02

open BezoutIdentityOQ03

/-! ## Lifting lemma -/

/-- If `a ∣ b` and `x ≡ y [ZMOD b]`, then `x ≡ y [ZMOD a]`. Standard fact:
    a finer modulus implies a coarser one. -/
theorem modEq_of_dvd_modulus {a b : ℤ} (hd : a ∣ b) {x y : ℤ}
    (h : x ≡ y [ZMOD b]) : x ≡ y [ZMOD a] := by
  rw [Int.modEq_iff_dvd] at *
  exact dvd_trans hd h

/-! ## Pairwise coprimality and product -/

/-- If `m i` is pairwise coprime over `Fin (k+1)`, the last modulus is coprime
    to the product of the first `k`. Direct application of `IsCoprime.prod_right`. -/
theorem isCoprime_last_prod {k : ℕ} (m : Fin (k + 1) → ℤ)
    (hpw : Pairwise (fun i j : Fin (k + 1) => IsCoprime (m i) (m j))) :
    IsCoprime (m (Fin.last k)) (∏ i : Fin k, m i.castSucc) := by
  apply IsCoprime.prod_right
  intro i _
  exact hpw (Fin.castSucc_lt_last i).ne'

/-- If `m` is pairwise coprime on `Fin (k+1)`, restricting to `Fin k` (via
    `castSucc`) is also pairwise coprime. -/
theorem pairwise_castSucc {k : ℕ} (m : Fin (k + 1) → ℤ)
    (hpw : Pairwise (fun i j : Fin (k + 1) => IsCoprime (m i) (m j))) :
    Pairwise (fun i j : Fin k => IsCoprime (m i.castSucc) (m j.castSucc)) := by
  intro i j hij
  exact hpw (Fin.castSucc_injective k |>.ne hij)

/-! ## k-fold CRT: existence -/

/-- **k-moduli CRT (existence)**: For pairwise coprime `m : Fin k → ℤ` and any
    desired residues `a : Fin k → ℤ`, there is `x : ℤ` simultaneously satisfying
    `x ≡ a i [ZMOD m i]` for every `i : Fin k`.

    Proved by induction on `k`, combining the inductive solution for the first
    `k` indices with `a (Fin.last k)` via the 2-moduli CRT (`crt_via_bezout`). -/
theorem crt_finitely_many_exists :
    ∀ {k : ℕ} (m : Fin k → ℤ) (a : Fin k → ℤ),
      Pairwise (fun i j : Fin k => IsCoprime (m i) (m j)) →
      ∃ x : ℤ, ∀ i : Fin k, x ≡ a i [ZMOD m i]
  | 0, _, _, _ => ⟨0, fun i => Fin.elim0 i⟩
  | k + 1, m, a, hpw => by
    -- Step 1: solve the first k indices by IH
    let m' : Fin k → ℤ := fun i => m i.castSucc
    let a' : Fin k → ℤ := fun i => a i.castSucc
    have hpw' : Pairwise (fun i j : Fin k => IsCoprime (m' i) (m' j)) :=
      pairwise_castSucc m hpw
    obtain ⟨y, hy⟩ := crt_finitely_many_exists m' a' hpw'
    -- Step 2: combine y (mod ∏ m') with a (Fin.last k) (mod m (Fin.last k))
    set M : ℤ := ∏ i : Fin k, m' i with hM_def
    have hcop_lastM : IsCoprime (m (Fin.last k)) M := isCoprime_last_prod m hpw
    -- IsCoprime.symm so the moduli appear in the order (M, m_last) for crt_iscop
    obtain ⟨x, hxM, hxlast⟩ := crt_iscop M (m (Fin.last k)) y (a (Fin.last k))
      hcop_lastM.symm
    -- Step 3: verify x satisfies all k+1 congruences
    refine ⟨x, ?_⟩
    intro i
    induction i using Fin.lastCases with
    | last =>
      -- For i = Fin.last k: x ≡ a (Fin.last k) [ZMOD m (Fin.last k)]
      exact hxlast
    | cast j =>
      -- For i = j.castSucc : Fin k: x ≡ y ≡ a j [ZMOD m j.castSucc]
      -- m j.castSucc divides M, so x ≡ y [ZMOD m j.castSucc] from x ≡ y [ZMOD M]
      have hdvd : m j.castSucc ∣ M :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have hxy : x ≡ y [ZMOD m j.castSucc] := modEq_of_dvd_modulus hdvd hxM
      exact hxy.trans (hy j)

/-! ## k-fold CRT: uniqueness -/

/-- **k-moduli CRT (uniqueness)**: Any two simultaneous solutions are congruent
    modulo the product of the moduli. Proved by induction on `k`, using
    `IsCoprime.mul_dvd` to combine the inductive case. -/
theorem crt_finitely_many_unique :
    ∀ {k : ℕ} (m : Fin k → ℤ),
      Pairwise (fun i j : Fin k => IsCoprime (m i) (m j)) →
      ∀ x y : ℤ, (∀ i : Fin k, x ≡ y [ZMOD m i]) →
      x ≡ y [ZMOD ∏ i : Fin k, m i]
  | 0, _, _, x, y, _ => by
    -- Empty product: ∏ = 1, and x ≡ y [ZMOD 1] is trivial
    simp [Int.ModEq, Finset.prod_empty]
  | k + 1, m, hpw, x, y, hcong => by
    let m' : Fin k → ℤ := fun i => m i.castSucc
    have hpw' : Pairwise (fun i j : Fin k => IsCoprime (m' i) (m' j)) :=
      pairwise_castSucc m hpw
    -- IH: x ≡ y [ZMOD ∏ m'] (over the first k indices)
    have h_M : x ≡ y [ZMOD ∏ i : Fin k, m' i] := by
      apply crt_finitely_many_unique m' hpw'
      intro j; exact hcong j.castSucc
    -- The last congruence: x ≡ y [ZMOD m (Fin.last k)]
    have h_last : x ≡ y [ZMOD m (Fin.last k)] := hcong (Fin.last k)
    -- Combine via IsCoprime.mul_dvd
    have hcop : IsCoprime (m (Fin.last k)) (∏ i : Fin k, m' i) :=
      isCoprime_last_prod m hpw
    -- ∏ over Fin (k+1) = (∏ over Fin k) * m (Fin.last k)
    rw [Fin.prod_univ_castSucc]
    -- Goal: x ≡ y [ZMOD (∏ i, m i.castSucc) * m (Fin.last k)]
    rw [Int.modEq_iff_dvd] at *
    rw [show (∏ i : Fin k, m i.castSucc) * m (Fin.last k)
        = m (Fin.last k) * ∏ i : Fin k, m i.castSucc from by ring]
    exact hcop.mul_dvd h_last h_M

/-! ## Combined existence-uniqueness statement -/

/-- **k-moduli CRT (full form)**: Combined existence and uniqueness. -/
theorem crt_finitely_many {k : ℕ} (m a : Fin k → ℤ)
    (hpw : Pairwise (fun i j : Fin k => IsCoprime (m i) (m j))) :
    ∃ x : ℤ, (∀ i : Fin k, x ≡ a i [ZMOD m i]) ∧
      ∀ y : ℤ, (∀ i : Fin k, y ≡ a i [ZMOD m i]) →
        x ≡ y [ZMOD ∏ i : Fin k, m i] := by
  obtain ⟨x, hx⟩ := crt_finitely_many_exists m a hpw
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply crt_finitely_many_unique m hpw
  intro i
  exact (hx i).trans (hy i).symm

/-! ## Worked example: x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7) -/

section Example

/-- Three pairwise-coprime moduli (3, 5, 7), packaged as a `Fin 3 → ℤ`. -/
def m357 : Fin 3 → ℤ := ![3, 5, 7]

/-- Worked residues a = (2, 3, 2) for moduli (3, 5, 7).
    Classical answer: x = 23. -/
def a357 : Fin 3 → ℤ := ![2, 3, 2]

example : (23 : ℤ) ≡ 2 [ZMOD 3] := by decide
example : (23 : ℤ) ≡ 3 [ZMOD 5] := by decide
example : (23 : ℤ) ≡ 2 [ZMOD 7] := by decide

/-- The product of (3, 5, 7) is 105. Uniqueness: solutions are unique mod 105. -/
example : (∏ i : Fin 3, m357 i) = 105 := by decide

/-- (23 + 105) = 128 also satisfies the system; uniqueness modulo 105. -/
example : (128 : ℤ) ≡ 23 [ZMOD 105] := by decide

end Example

/-! ## Summary

- `crt_finitely_many_exists`: explicit Fin-induction k-moduli CRT existence.
- `crt_finitely_many_unique`: matching uniqueness modulo the product.
- `crt_finitely_many`: packaged existence + uniqueness.
- Built directly on `BezoutIdentityOQ03.crt_iscop` (2-moduli base case).
- Key Mathlib tools: `IsCoprime.prod_right`, `IsCoprime.mul_dvd`,
  `Finset.dvd_prod_of_mem`, `Fin.prod_univ_castSucc`, `Fin.lastCases`.
-/

end BezoutIdentityOQ03OQ02
