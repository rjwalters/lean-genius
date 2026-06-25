/-
# Cantor Diagonalization OQ-07-OQ-01: n-fold and countable continuum powers

## Open Question
Formalize the n-fold and countable versions of the continuum's multiplicative
idempotence (cantor-diagonalization-oq-07, `#(ℝ × ℝ) = #ℝ`):

  * `#(ℝⁿ) = #ℝ`   (finite dimension does not raise cardinality, for `n ≥ 1`)
  * `#(ℕ → ℝ) = 𝔠`  (the space of real sequences still has the cardinality of the line)

## Approach
The plane result `𝔠 · 𝔠 = 𝔠` (`Cardinal.continuum_mul_self`) is the `n = 2` instance of
the general fact that an infinite cardinal absorbs finite powers. Two clean Mathlib levers
do the lifting:

  * **Finite power.** `Cardinal.mk_arrow` rewrites `#(Fin n → ℝ)` to `#ℝ ^ #(Fin n)`,
    i.e. `𝔠 ^ (n : ℕ)`. `Cardinal.power_nat_eq` (any `ℵ₀ ≤ c` and `1 ≤ n` give `c ^ n = c`)
    collapses `𝔠 ^ n` to `𝔠`. Geometrically: ℝⁿ — Euclidean n-space — is equinumerous
    with the line for every `n ≥ 1`.
  * **Countable power.** For the sequence space `ℕ → ℝ` the exponent is `ℵ₀`, and
    `Cardinal.continuum_power_aleph0 : 𝔠 ^ ℵ₀ = 𝔠` (from `2 ^ ℵ₀ = 𝔠` and
    `ℵ₀ · ℵ₀ = ℵ₀`) shows even countably-infinite-dimensional real space stays at `𝔠`.

Each cardinal equality unpacks, via `Cardinal.eq`, to an honest bijection. As with the
parent, the witnesses are classical: they come from the cardinal-arithmetic proof, not an
explicit coordinate formula.

Sorry-free and axiom-free.
-/
import Mathlib

namespace CantorDiagonalizationOQ07OQ01

open Cardinal

/-- **Finite continuum powers collapse: `𝔠 ^ n = 𝔠` for `n ≥ 1`.** The engine behind the
`ℝⁿ` results: an infinite cardinal absorbs any positive finite power
(`Cardinal.power_nat_eq` at `c = 𝔠`, using `ℵ₀ ≤ 𝔠`). -/
theorem continuum_pow_eq {n : ℕ} (hn : 1 ≤ n) : (𝔠 : Cardinal) ^ n = 𝔠 :=
  power_nat_eq aleph0_le_continuum hn

/-- **`#(ℝⁿ) = 𝔠` for `n ≥ 1`.** `Cardinal.mk_arrow` expands `#(Fin n → ℝ)` to
`#ℝ ^ #(Fin n)`; `mk_real` and `mk_fin` turn this into `𝔠 ^ (n : ℕ)`; `continuum_pow_eq`
collapses it to `𝔠`. -/
theorem mk_pi_real_eq_continuum {n : ℕ} (hn : 1 ≤ n) : #(Fin n → ℝ) = 𝔠 := by
  rw [mk_arrow, lift_id, lift_id, mk_real, mk_fin, power_natCast]
  exact continuum_pow_eq hn

/-- **Euclidean `n`-space and the line are equinumerous: `#(ℝⁿ) = #ℝ` for `n ≥ 1`.**
Raising the dimension from `1` to any finite `n` does not change cardinality — the
finite-dimensional companion to the parent's `#(ℝ × ℝ) = #ℝ`. Both sides equal `𝔠`. -/
theorem mk_pi_real {n : ℕ} (hn : 1 ≤ n) : #(Fin n → ℝ) = #ℝ := by
  rw [mk_pi_real_eq_continuum hn, mk_real]

/-- **An explicit bijection `ℝⁿ ≃ ℝ` exists for `n ≥ 1`.** The cardinal equality
`#(Fin n → ℝ) = #ℝ` is, by `Cardinal.eq`, exactly the existence of a bijection. -/
theorem nonempty_equiv_pi_real {n : ℕ} (hn : 1 ≤ n) : Nonempty ((Fin n → ℝ) ≃ ℝ) :=
  Cardinal.eq.mp (mk_pi_real hn)

/-- **The space of real sequences has cardinality the continuum: `#(ℕ → ℝ) = 𝔠`.**
`Cardinal.mk_arrow` gives `#ℝ ^ #ℕ = 𝔠 ^ ℵ₀`, and `Cardinal.continuum_power_aleph0`
collapses `𝔠 ^ ℵ₀` to `𝔠`. Countably-infinite-dimensional real space is no larger than
the line. -/
theorem mk_nat_arrow_real_eq_continuum : #(ℕ → ℝ) = 𝔠 := by
  rw [mk_arrow, lift_id, lift_id, mk_real, mk_nat, continuum_power_aleph0]

/-- **Real sequences and the line are equinumerous: `#(ℕ → ℝ) = #ℝ`.** Both sides
equal `𝔠`. -/
theorem mk_nat_arrow_real : #(ℕ → ℝ) = #ℝ := by
  rw [mk_nat_arrow_real_eq_continuum, mk_real]

/-- **An explicit bijection `(ℕ → ℝ) ≃ ℝ` exists.** The cardinal equality
`#(ℕ → ℝ) = #ℝ` is, by `Cardinal.eq`, exactly the existence of a bijection between the
sequence space and the line. -/
theorem nonempty_equiv_nat_arrow_real : Nonempty ((ℕ → ℝ) ≃ ℝ) :=
  Cardinal.eq.mp mk_nat_arrow_real

/-- **Sanity check against the parent.** The `n = 2` instance recovers `#(Fin 2 → ℝ) = #ℝ`,
the `Fin`-indexed form of the parent's `#(ℝ × ℝ) = #ℝ`. -/
theorem mk_pi_two_real : #(Fin 2 → ℝ) = #ℝ :=
  mk_pi_real (by norm_num)

end CantorDiagonalizationOQ07OQ01
