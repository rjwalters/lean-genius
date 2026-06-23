/-
# Generalizations of the Markov Equation — Parametric and Markov–Hurwitz

The classical Markov equation `x² + y² + z² = 3xyz` (formalized in
`Proofs.MarkovEquation`) is the `k = 0`, `n = 3`, `a = 3` member of two natural
families, both of which inherit the **Vieta-jump** structure that drives the
classical descent:

* the **parametric Markov equation** `x² + y² + z² = 3xyz + k` for a fixed
  integer parameter `k`; and
* the **Markov–Hurwitz equation** `x₁² + ⋯ + xₙ² = a · x₁⋯xₙ` in `n` variables
  with multiplier `a` (Hurwitz, 1907).

This file isolates the part of the theory that survives both generalizations:
the Vieta jump is still a solution-preserving involution, with the same root
sum/product relations. For the `n`-variable family we additionally show that the
jump preserves **positivity** (so the descent tree is well-defined over the
positive integers) and we pin down the exact **descent criterion** — the jump on
a coordinate strictly decreases it iff that coordinate dominates the sum of the
squares of the others. The latter is precisely the inequality that holds
automatically for the maximal coordinate when `n = 3` but becomes delicate for
larger `n`, which is why the full classification (a Markov *tree*) is special to
three variables.

Everything here is elementary and axiom-free: the Vieta identities are pure
polynomial algebra (`linear_combination` / `ring`), and the structural facts are
Finset manipulations.

Connections to the parent file are recorded by `isMH_three_iff` /
`genMarkov_zero_iff`, which identify the `(a = 3, n = 3)` and `k = 0` members
with the classical equation.
-/
import Mathlib

namespace MarkovHurwitz

open Finset

/-! ## Part A. The parametric Markov equation `x² + y² + z² = 3xyz + k`

Fix an integer parameter `k`. The Vieta jump `z ↦ 3xy − z` (fixing `x`, `y`) is
solution-preserving for **every** `k`, because the parameter cancels in exactly
the same way as in the homogeneous case. -/

/-- A solution of the parametric Markov equation with parameter `k`. -/
def IsGenMarkov (k x y z : ℤ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z + k

/-- Swapping the first two coordinates preserves solutions. -/
theorem genMarkov_swap12 {k x y z : ℤ} (h : IsGenMarkov k x y z) :
    IsGenMarkov k y x z := by
  unfold IsGenMarkov at *; linear_combination h

/-- Swapping the last two coordinates preserves solutions. -/
theorem genMarkov_swap23 {k x y z : ℤ} (h : IsGenMarkov k x y z) :
    IsGenMarkov k x z y := by
  unfold IsGenMarkov at *; linear_combination h

/-- **Vieta jump** `z ↦ 3xy − z` preserves solutions, for any parameter `k`. -/
theorem genMarkov_vieta {k x y z : ℤ} (h : IsGenMarkov k x y z) :
    IsGenMarkov k x y (3 * x * y - z) := by
  unfold IsGenMarkov at *; linear_combination h

/-- The Vieta jump is an involution: applying it twice restores `z`. -/
theorem genMarkov_vieta_involutive (x y z : ℤ) :
    3 * x * y - (3 * x * y - z) = z := by ring

/-- Root sum relation: the two `z`-roots sum to `3xy` (independent of `k`). -/
theorem genMarkov_root_sum (x y z : ℤ) : z + (3 * x * y - z) = 3 * x * y := by
  ring

/-- Root product relation: the two `z`-roots multiply to `x² + y² − k`. -/
theorem genMarkov_root_prod {k x y z : ℤ} (h : IsGenMarkov k x y z) :
    z * (3 * x * y - z) = x ^ 2 + y ^ 2 - k := by
  unfold IsGenMarkov at h; linear_combination -h

/-- At `k = 0` we recover exactly the classical Markov equation. -/
theorem genMarkov_zero_iff (x y z : ℤ) :
    IsGenMarkov 0 x y z ↔ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z := by
  unfold IsGenMarkov; constructor <;> intro h <;> linarith

/-- For each `(x, y, z)` there is a unique parameter making it a solution, namely
`k = x² + y² + z² − 3xyz`. So the parametric family foliates all integer triples. -/
theorem genMarkov_param_unique (x y z : ℤ) :
    IsGenMarkov (x ^ 2 + y ^ 2 + z ^ 2 - 3 * x * y * z) x y z := by
  unfold IsGenMarkov; ring

/-! ## Part B. The Markov–Hurwitz equation `∑ xᵢ² = a · ∏ xᵢ`

Now the number of variables is arbitrary. We index the variables by `Fin n` and
write the equation as `∑ i, (v i)² = a · ∏ i, v i`. The Vieta jump at coordinate
`i` replaces `v i` by `a · (∏_{j ≠ i} v j) − v i`. -/

variable {n : ℕ}

/-- A solution of the Markov–Hurwitz equation with multiplier `a`. -/
def IsMH (a : ℤ) (v : Fin n → ℤ) : Prop :=
  ∑ i, (v i) ^ 2 = a * ∏ i, v i

/-- The Vieta partner value at coordinate `i`: `a · ∏_{j ≠ i} vⱼ − vᵢ`. -/
def vietaVal (a : ℤ) (v : Fin n → ℤ) (i : Fin n) : ℤ :=
  a * ∏ j ∈ univ.erase i, v j - v i

/-- The Vieta jump at coordinate `i` (update `v i` to its Vieta partner). -/
def vietaJump (a : ℤ) (v : Fin n → ℤ) (i : Fin n) : Fin n → ℤ :=
  Function.update v i (vietaVal a v i)

@[simp] theorem vietaJump_self (a : ℤ) (v : Fin n → ℤ) (i : Fin n) :
    vietaJump a v i i = vietaVal a v i := by
  simp [vietaJump]

theorem vietaJump_of_ne {a : ℤ} {v : Fin n → ℤ} {i j : Fin n} (h : j ≠ i) :
    vietaJump a v i j = v j := by
  simp only [vietaJump, Function.update_of_ne h]

/-- The product over the *other* coordinates is unaffected by a jump at `i`. -/
theorem prod_erase_vietaJump (a : ℤ) (v : Fin n → ℤ) (i : Fin n) :
    ∏ j ∈ univ.erase i, vietaJump a v i j = ∏ j ∈ univ.erase i, v j := by
  apply Finset.prod_congr rfl
  intro j hj
  exact vietaJump_of_ne (Finset.mem_erase.1 hj).1

/-- The sum of squares over the *other* coordinates is unaffected by a jump at `i`. -/
theorem sum_erase_sq_vietaJump (a : ℤ) (v : Fin n → ℤ) (i : Fin n) :
    ∑ j ∈ univ.erase i, (vietaJump a v i j) ^ 2 = ∑ j ∈ univ.erase i, (v j) ^ 2 := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [vietaJump_of_ne (Finset.mem_erase.1 hj).1]

/-- Vieta sum relation: the partner and original at `i` sum to `a · ∏_{j ≠ i} vⱼ`. -/
theorem vietaVal_add (a : ℤ) (v : Fin n → ℤ) (i : Fin n) :
    vietaVal a v i + v i = a * ∏ j ∈ univ.erase i, v j := by
  unfold vietaVal; ring

/-- Vieta product relation: `vᵢ · (partner) = ∑_{j ≠ i} vⱼ²`, valid on any solution. -/
theorem vietaVal_mul {a : ℤ} {v : Fin n → ℤ} (i : Fin n) (h : IsMH a v) :
    v i * vietaVal a v i = ∑ j ∈ univ.erase i, (v j) ^ 2 := by
  have hsplit : (v i) ^ 2 + ∑ j ∈ univ.erase i, (v j) ^ 2 = ∑ j, (v j) ^ 2 :=
    Finset.add_sum_erase univ (fun j => (v j) ^ 2) (mem_univ i)
  have hprod : v i * ∏ j ∈ univ.erase i, v j = ∏ j, v j :=
    Finset.mul_prod_erase univ v (mem_univ i)
  unfold IsMH at h
  unfold vietaVal
  -- v i * (a * P − v i) = a * (v i * P) − v i² = a * ∏v − v i² = ∑v² − v i² = ∑_{erase} v²
  have : v i * (a * ∏ j ∈ univ.erase i, v j - v i)
        = a * (v i * ∏ j ∈ univ.erase i, v j) - (v i) ^ 2 := by ring
  rw [this, hprod, ← h, ← hsplit]; ring

/-- **Vieta jump preserves Markov–Hurwitz solutions**, in any number of variables
and for any multiplier. This is the dimension-free heart of the theory. -/
theorem isMH_vietaJump {a : ℤ} {v : Fin n → ℤ} (i : Fin n) (h : IsMH a v) :
    IsMH a (vietaJump a v i) := by
  set P := ∏ j ∈ univ.erase i, v j with hP
  -- Split sum of squares of the jumped tuple at coordinate `i`.
  have hsplit_w : ∑ j, (vietaJump a v i j) ^ 2
      = (vietaVal a v i) ^ 2 + ∑ j ∈ univ.erase i, (v j) ^ 2 := by
    rw [← Finset.add_sum_erase univ (fun j => (vietaJump a v i j) ^ 2) (mem_univ i),
        vietaJump_self, sum_erase_sq_vietaJump]
  -- Product of the jumped tuple factors through the unchanged `P`.
  have hprod_w : ∏ j, vietaJump a v i j = (vietaVal a v i) * P := by
    rw [← Finset.mul_prod_erase univ (vietaJump a v i) (mem_univ i),
        vietaJump_self, prod_erase_vietaJump]
  -- The sum of the other squares, from the original solution.
  have hS : ∑ j ∈ univ.erase i, (v j) ^ 2 = v i * vietaVal a v i := (vietaVal_mul i h).symm
  unfold IsMH
  rw [hsplit_w, hprod_w, hS]
  -- (a·P − vᵢ)² + vᵢ(a·P − vᵢ) = a·(a·P − vᵢ)·P  — pure algebra in `vietaVal = a·P − vᵢ`.
  have hval : vietaVal a v i = a * P - v i := rfl
  rw [hval]; ring

/-- The Vieta jump is an involution at each coordinate. -/
theorem vietaJump_involutive (a : ℤ) (v : Fin n → ℤ) (i : Fin n) :
    vietaJump a (vietaJump a v i) i = v := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [vietaJump_self]
    unfold vietaVal
    rw [prod_erase_vietaJump, vietaJump_self]
    unfold vietaVal
    ring
  · rw [vietaJump_of_ne hj, vietaJump_of_ne hj]

/-! ### Positivity and the descent criterion

Over the positive integers the Vieta jump stays positive, so the move relation is
well-defined on positive solutions. We then characterize exactly when the jump
strictly decreases a coordinate. -/

/-- On a positive solution with at least two variables, the Vieta partner of any
coordinate is again positive — the jump never leaves the positive orthant. -/
theorem vietaVal_pos {a : ℤ} {v : Fin n → ℤ} (i : Fin n) (h : IsMH a v)
    (hpos : ∀ j, 0 < v j) (hn : 2 ≤ n) : 0 < vietaVal a v i := by
  -- `vᵢ · partner = ∑_{j ≠ i} vⱼ²`, and the right side is a positive sum of squares.
  have hmul : v i * vietaVal a v i = ∑ j ∈ univ.erase i, (v j) ^ 2 := vietaVal_mul i h
  -- there is a coordinate `≠ i` (since n ≥ 2), giving a strictly positive term.
  have hne : (univ.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := hne
  have hsum_pos : 0 < ∑ j ∈ univ.erase i, (v j) ^ 2 :=
    Finset.sum_pos' (fun k _ => sq_nonneg (v k)) ⟨j, hj, pow_pos (hpos j) 2⟩
  rw [← hmul] at hsum_pos
  exact (mul_pos_iff_of_pos_left (hpos i)).mp hsum_pos

/-- **Descent criterion.** With `vᵢ > 0`, the Vieta jump strictly *decreases* the
`i`-th coordinate iff that coordinate dominates the sum of the squares of the
others. For `n = 3` this holds automatically at the maximal coordinate (driving
the classical descent); for larger `n` it can fail. -/
theorem vietaVal_lt_iff {a : ℤ} {v : Fin n → ℤ} (i : Fin n) (h : IsMH a v)
    (hi : 0 < v i) :
    vietaVal a v i < v i ↔ ∑ j ∈ univ.erase i, (v j) ^ 2 < (v i) ^ 2 := by
  have hmul : v i * vietaVal a v i = ∑ j ∈ univ.erase i, (v j) ^ 2 := vietaVal_mul i h
  constructor
  · intro hlt
    have := mul_lt_mul_of_pos_left hlt hi
    rw [hmul] at this; nlinarith [this]
  · intro hlt
    have h2 : v i * vietaVal a v i < v i * v i := by rw [hmul]; nlinarith [hlt]
    exact lt_of_mul_lt_mul_left h2 (le_of_lt hi)

/-! ## Bridges to the classical equation and concrete instances -/

/-- The three-variable Markov–Hurwitz equation, written out coordinatewise. -/
theorem isMH_three_iff (a x y z : ℤ) :
    IsMH a ![x, y, z] ↔ x ^ 2 + y ^ 2 + z ^ 2 = a * (x * y * z) := by
  unfold IsMH
  rw [Fin.sum_univ_three, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The `(a = 3, n = 3)` Markov–Hurwitz equation is the classical Markov equation. -/
theorem isMH_three_markov (x y z : ℤ) :
    IsMH 3 ![x, y, z] ↔ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z := by
  rw [isMH_three_iff]; constructor <;> intro h <;> linear_combination h

/-- The singular Markov triple `(1,1,1)` as a Markov–Hurwitz solution (`a = 3`). -/
theorem isMH_ones : IsMH 3 (fun _ : Fin 3 => (1 : ℤ)) := by
  simp [IsMH]

/-- The Hurwitz solution `(3,3,3)` of `x² + y² + z² = xyz` (`a = 1`). -/
theorem isMH_threes : IsMH 1 ![3, 3, 3] := by
  rw [isMH_three_iff]; norm_num

/-- A four-variable solution of `∑ xᵢ² = 4 ∏ xᵢ`: the all-ones tuple
(`1+1+1+1 = 4 = 4·1`). -/
theorem isMH_ones_four : IsMH 4 (fun _ : Fin 4 => (1 : ℤ)) := by
  simp [IsMH]

/-- A worked Vieta jump in three variables: jumping the third coordinate of
`(1,1,1)` (with `a = 3`) gives `3·(1·1) − 1 = 2`, i.e. the triple `(1,1,2)`. -/
theorem vietaVal_ones_two :
    vietaVal 3 ![(1 : ℤ), 1, 1] 2 = 2 := by
  have hp : ∏ j ∈ univ.erase (2 : Fin 3), ![(1 : ℤ), 1, 1] j = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    fin_cases hj <;> rfl
  unfold vietaVal
  rw [hp]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

end MarkovHurwitz
