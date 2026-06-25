import Mathlib

/-
# Sum of squares of Lucas numbers: ∑ L_i² = L_n · L_{n+1} − 2

The Lucas analogue of the Fibonacci square-sum identity
`F_1² + ⋯ + F_n² = F_n · F_{n+1}` (entry `fibonacci-identities-oq-03-oq-02`).

The Lucas numbers `L_n` satisfy the Fibonacci recurrence `L_{n+2} = L_n + L_{n+1}`
but start `L_0 = 2`, `L_1 = 1`, giving `2, 1, 3, 4, 7, 11, 18, …`.  Their squares
sum to a consecutive Lucas product, shifted by the constant `2`:

  `L_1² + L_2² + ⋯ + L_n² = L_n · L_{n+1} − 2`.

The constant correction `−2` is the signature difference from the Fibonacci case
(where the analogous sum is *exactly* `F_n · F_{n+1}`): it is exactly the leftover
`L_0² − 2 = 4 − 2` carried by the `L_0 = 2` initial value.  Concretely the clean,
subtraction-free statement is the `0`-indexed form

  `L_0² + L_1² + ⋯ + L_n² = L_n · L_{n+1} + 2`,

and discarding the `L_0² = 4` term turns the `+2` into the classical `−2`.

Lucas numbers are not packaged in Mathlib, so we define the sequence locally
(matching the convention used elsewhere in the Fibonacci gallery) and prove the
identity by the textbook one-line induction.  The inductive step is the telescoping
observation
  `L_{n+1} · L_{n+2} − L_n · L_{n+1} = L_{n+1} · (L_{n+2} − L_n) = L_{n+1}²`,
i.e. adding the next square `L_{n+1}²` advances the running product from
`L_n · L_{n+1}` to `L_{n+1} · L_{n+2}` using only `L_{n+2} = L_n + L_{n+1}` and `ring`.
-/

namespace FibonacciIdentitiesOQ03OQ02OQ02

/-- **Lucas numbers** `L_n`: `L_0 = 2`, `L_1 = 1`, `L_{n+2} = L_n + L_{n+1}`.
The Lucas sequence shares the Fibonacci recurrence but starts `2, 1, 3, 4, 7, 11, …`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining Lucas recurrence `L_{n+2} = L_n + L_{n+1}`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-- **Sum of squares of Lucas numbers** (`0`-indexed, subtraction-free form).
`∑_{i ∈ range (n+1)} L_i² = L_n · L_{n+1} + 2`.

Proof by induction on `n`: `Finset.sum_range_succ` peels off the top square
`L_{k+1}²`, the induction hypothesis rewrites the remaining sum to `L_k · L_{k+1} + 2`,
and the recurrence `L_{k+2} = L_k + L_{k+1}` together with `ring` closes
`L_k · L_{k+1} + 2 + L_{k+1}² = L_{k+1} · L_{k+2} + 2`. -/
theorem lucas_sum_sq (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), lucas i ^ 2 = lucas n * lucas (n + 1) + 2 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : lucas (k + 1 + 1) = lucas k + lucas (k + 1) := lucas_add_two k
    rw [hrec]
    ring

/-- **Sum of squares of Lucas numbers** (`1`-indexed, subtraction-free `ℕ` form).
`(∑_{i ∈ Icc 1 n} L_i²) + 2 = L_n · L_{n+1}`.

This is the classical `∑_{i=1}^n L_i² = L_n · L_{n+1} − 2` rearranged to avoid `ℕ`
truncated subtraction.  Derived from `lucas_sum_sq` by discarding the `i = 0` term
`L_0² = 4`: `range (n+1) = insert 0 (Icc 1 n)`, so the `0`-indexed `+2` loses `4` and
becomes `−2`. -/
theorem lucas_sum_sq_Icc_add_two (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, lucas i ^ 2) + 2 = lucas n * lucas (n + 1) := by
  have hsplit : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h := lucas_sum_sq n
  rw [hsplit, Finset.sum_insert (by simp)] at h
  simp only [lucas_zero] at h
  -- h : 2 ^ 2 + ∑ i ∈ Icc 1 n, lucas i ^ 2 = lucas n * lucas (n + 1) + 2
  omega

/-- **Integer form** matching the classical statement verbatim.
`∑_{i ∈ Icc 1 n} (L_i : ℤ)² = L_n · L_{n+1} − 2`.

Over `ℤ` the `−2` is literal (no truncation), obtained by moving the `+2` of
`lucas_sum_sq_Icc_add_two` to the right-hand side. -/
theorem lucas_sum_sq_Icc_int (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (lucas i : ℤ) ^ 2 = (lucas n : ℤ) * (lucas (n + 1) : ℤ) - 2 := by
  have h : ((∑ i ∈ Finset.Icc 1 n, lucas i ^ 2) + 2 : ℤ) = (lucas n * lucas (n + 1) : ℤ) := by
    exact_mod_cast lucas_sum_sq_Icc_add_two n
  push_cast at h ⊢
  linarith

/-- **Telescoping reading.** Adding the next square advances the running product by one
index: `(∑_{i ∈ range (n+1)} L_i²) + L_{n+1}² = L_{n+1} · L_{n+2} + 2`.  This is the
inductive step in standalone form, exhibiting the partial sums as the consecutive
products `L_n · L_{n+1} + 2`. -/
theorem lucas_sum_sq_succ (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), lucas i ^ 2) + lucas (n + 1) ^ 2
      = lucas (n + 1) * lucas (n + 2) + 2 := by
  rw [lucas_sum_sq, lucas_add_two]
  ring

/-- Numerical check at `n = 4`: the `1`-indexed sum
`1 + 9 + 16 + 49 = 75` equals `L_4 · L_5 − 2 = 7 · 11 − 2 = 75`.
Verified by `decide` (kernel reduction — no `native_decide`, so the entry stays
`Lean.ofReduceBool`-free). -/
example : (∑ i ∈ Finset.Icc 1 4, lucas i ^ 2) + 2 = lucas 4 * lucas 5 := lucas_sum_sq_Icc_add_two 4

example : lucas 4 * lucas 5 = 77 := by decide

example : ∑ i ∈ Finset.range 5, lucas i ^ 2 = lucas 4 * lucas 5 + 2 := lucas_sum_sq 4

end FibonacciIdentitiesOQ03OQ02OQ02
