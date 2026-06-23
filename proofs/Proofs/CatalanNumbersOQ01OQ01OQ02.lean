import Mathlib

/-
# Generalized Ballot Numbers via the Reflection Principle

Mathlib (`Mathlib/Combinatorics/Enumerative/Catalan.lean`) records the Catalan
numbers `catalan` with the bridge `succ_mul_catalan_eq_centralBinom`
(`(n + 1) * catalan n = centralBinom n`), and `Mathlib.Probability` contains the
*probabilistic* ballot problem.  Neither records the **arithmetic** ballot
number / Catalan-triangle entry in closed form.

This file gives a purely arithmetic, `0`-axiom development of the generalized
ballot number

  `B(p, q) = C(p + q, q) - C(p + q, p + 1)`,

the number of lattice paths from `(0,0)` to `(q, p)` with unit right/up steps that
stay weakly below the diagonal (`#down ≥ #up` at every prefix).  Writing the
subtrahend with the index `p + 1` (rather than the "reflected" index `q - 1`)
keeps every index free of truncated `ℕ`-subtraction, so the boundary values
`B(p, 0) = 1` and `B(p, q) = 0` for `q > p` come out correctly.

The entire two-parameter family flows from a single nonlinear identity

  `ballot_key : (p + 1) · C(p + q, p + 1) = q · C(p + q, q)`,

a one-line consequence of `Nat.choose_succ_right_eq` together with the symmetry
`Nat.choose_symm_add`.  From it we obtain:

* `ballot_genuine`     — the subtraction is genuine when `q ≤ p`;
* `ballot_closed_form` — the division-free **Bertrand ratio**
                          `(p + 1) · B(p, q) = (p + 1 - q) · C(p + q, q)`;
* `ballot_diag`        — the diagonal `B(n, n) = catalan n`;
* `ballot_zero`        — `B(p, 0) = 1`;
* `ballot_eq_zero_of_lt` — `B(p, q) = 0` whenever `p < q`.

Everything is over `ℕ`, fully machine-checked, `0`-axiom.
-/

/-- **Generalized ballot number** (Catalan-triangle entry).

`ballot p q = C(p + q, q) - C(p + q, p + 1)` counts the lattice paths to `(q, p)`
staying weakly below the diagonal. -/
def ballot (p q : ℕ) : ℕ := (p + q).choose q - (p + q).choose (p + 1)

/-- **Key nonlinear identity.**  `(p + 1) · C(p + q, p + 1) = q · C(p + q, q)`.

A one-line consequence of `Nat.choose_succ_right_eq` at `(p + q, p)` (which gives
`C(p+q, p+1)·(p+1) = C(p+q, p)·q`) combined with the symmetry
`C(p + q, p) = C(p + q, q)`. -/
theorem ballot_key (p q : ℕ) :
    (p + 1) * (p + q).choose (p + 1) = q * (p + q).choose q := by
  have h := Nat.choose_succ_right_eq (p + q) p
  -- h : (p+q).choose (p+1) * (p+1) = (p+q).choose p * (p+q - p)
  have e : p + q - p = q := by omega
  rw [e] at h
  have hsym : (p + q).choose p = (p + q).choose q := Nat.choose_symm_add
  rw [hsym] at h
  -- h : (p+q).choose (p+1) * (p+1) = (p+q).choose q * q
  calc (p + 1) * (p + q).choose (p + 1)
        = (p + q).choose (p + 1) * (p + 1) := by ring
    _ = (p + q).choose q * q := h
    _ = q * (p + q).choose q := by ring

/-- **Genuineness (regime `q ≤ p`).**  The right neighbour never exceeds the
diagonal coefficient, so the `ℕ` subtraction in `ballot p q` is not truncated.

From `ballot_key`, `(p + 1)·C(p+q, p+1) = q·C(p+q, q) ≤ (p + 1)·C(p+q, q)` because
`q ≤ p + 1`; cancelling the positive factor `p + 1` gives the claim. -/
theorem ballot_genuine {p q : ℕ} (h : q ≤ p) :
    (p + q).choose (p + 1) ≤ (p + q).choose q := by
  have hk := ballot_key p q
  have hle : (p + 1) * (p + q).choose (p + 1) ≤ (p + 1) * (p + q).choose q := by
    rw [hk]
    exact mul_le_mul_right' (by omega) _
  exact Nat.le_of_mul_le_mul_left hle (by omega)

/-- **Bertrand ratio / closed form (regime `q ≤ p`).**

  `(p + 1) · ballot p q = (p + 1 - q) · C(p + q, q)`.

The division-free form of the classical Bertrand ballot theorem
`B(p, q) = (p + 1 - q)/(p + 1) · C(p + q, q)`.  Proved by partitioning the
diagonal coefficient `C(p+q, q) = ballot p q + C(p+q, p+1)` (licensed by
`ballot_genuine`) and eliminating `C(p+q, p+1)` via `ballot_key`. -/
theorem ballot_closed_form {p q : ℕ} (h : q ≤ p) :
    (p + 1) * ballot p q = (p + 1 - q) * (p + q).choose q := by
  have hk := ballot_key p q
  -- additive partition, genuine since `q ≤ p`
  have hadd : (p + q).choose q = ballot p q + (p + q).choose (p + 1) := by
    have hg := ballot_genuine h
    unfold ballot
    omega
  -- multiply the partition by `p + 1`, then use `ballot_key`
  have expand :
      (p + 1) * ((p + q).choose q)
        = (p + 1) * ballot p q + (p + 1) * ((p + q).choose (p + 1)) := by
    rw [hadd]; ring
  rw [hk] at expand
  -- expand : (p+1)·C(q) = (p+1)·ballot + q·C(q)
  have hsub :
      (p + 1 - q) * ((p + q).choose q)
        = (p + 1) * ((p + q).choose q) - q * ((p + q).choose q) :=
    Nat.sub_mul (p + 1) q ((p + q).choose q)
  omega

/-- **Diagonal = Catalan.**  `ballot n n = catalan n`.

At `p = q = n` the closed form reads `(n + 1)·ballot n n = 1·C(2n, n)`, while
`succ_mul_catalan_eq_centralBinom` gives `(n + 1)·catalan n = C(2n, n)`; cancelling
`n + 1` identifies the two. -/
theorem ballot_diag (n : ℕ) : ballot n n = catalan n := by
  have hcf := ballot_closed_form (le_refl n)
  have e : n + 1 - n = 1 := by omega
  rw [e, one_mul] at hcf
  -- hcf : (n + 1) * ballot n n = (n + n).choose n
  have hcat : (n + 1) * catalan n = (n + n).choose n := by
    have h := succ_mul_catalan_eq_centralBinom n
    have hc : Nat.centralBinom n = (n + n).choose n := by
      show (2 * n).choose n = (n + n).choose n
      rw [two_mul]
    rw [h, hc]
  have key : (n + 1) * ballot n n = (n + 1) * catalan n := by rw [hcf, hcat]
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-- **Boundary `q = 0`.**  `ballot p 0 = 1` — the single all-down path. -/
theorem ballot_zero (p : ℕ) : ballot p 0 = 1 := by
  simp only [ballot, Nat.add_zero, Nat.choose_zero_right,
    Nat.choose_eq_zero_of_lt (show p < p + 1 by omega), Nat.sub_zero]

/-- **Vanishing above the diagonal.**  `p < q → ballot p q = 0`.

Symmetric to `ballot_genuine`: from `ballot_key`,
`(p + 1)·C(p+q, p+1) = q·C(p+q, q) ≥ (p + 1)·C(p+q, q)` because `p + 1 ≤ q`, so
`C(p+q, q) ≤ C(p+q, p+1)` and the truncated subtraction collapses to `0`. -/
theorem ballot_eq_zero_of_lt {p q : ℕ} (h : p < q) : ballot p q = 0 := by
  unfold ballot
  have hk := ballot_key p q
  have hge : (p + 1) * ((p + q).choose q) ≤ (p + 1) * ((p + q).choose (p + 1)) := by
    rw [hk]
    exact mul_le_mul_right' (by omega) _
  have hle : (p + q).choose q ≤ (p + q).choose (p + 1) :=
    Nat.le_of_mul_le_mul_left hge (by omega)
  omega

/-- Sanity check: the Catalan diagonal `B(3,3) = C(6,3) - C(6,4) = 20 - 15 = 5`
(`= catalan 3` by `ballot_diag`). -/
example : ballot 3 3 = 5 := by decide

/-- Sanity check: `B(4, 2) = C(6, 2) - C(6, 5) = 15 - 6 = 9`. -/
example : ballot 4 2 = 9 := by decide

/-- Sanity check: above the diagonal vanishes, `B(2, 5) = 0`. -/
example : ballot 2 5 = 0 := by decide
