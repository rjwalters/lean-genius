import Mathlib
import Proofs.CubeRoot3IrrationalOQ03

/-!
# ∛3, child OQ-03-OQ-01: doubling the cube is impossible

The parent `cube-root-3-irrational-oq-03` proves `[ℚ(∛3):ℚ] = 3`
(`finrank_adjoin_cbrt3`). This entry draws the classical geometric consequence —
the second open question posed there:

> **∛3 is not constructible by ruler and compass**, because its degree over ℚ is
> `3`, which is not a power of `2`.

A ruler-and-compass constructible real lies in a tower of quadratic extensions,
hence in some subfield `E ⊆ ℝ` with `[E:ℚ]` a power of `2`. We show `∛3` lies in
**no** such field: if `∛3 ∈ E` then `ℚ(∛3) ⊆ E`, so `3 = [ℚ(∛3):ℚ]` divides
`[E:ℚ] = 2^k`, forcing `3 ∣ 2` — impossible. This is the algebraic heart of the
classical impossibility of **doubling the cube** (the Delian problem).

Results:
* `cbrt3_notMem_of_finrank_pow_two` — `∛3 ∉ E` whenever `[E:ℚ] = 2^k`.
* `cbrt3_notMem_of_finrank_two` — the quadratic case `k = 1`.
* `three_not_pow_two` — `3` is not a power of `2` (the arithmetic obstruction).

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).

## References
* Doubling the cube (the Delian problem) and Wantzel's degree criterion for
  constructibility.
-/

open CubeRoot3Irrational CubeRoot3IrrationalOQ03 IntermediateField

namespace CubeRoot3IrrationalOQ03OQ01

/-- `3` is not a power of `2` — the arithmetic obstruction behind the
    impossibility of doubling the cube. -/
theorem three_not_pow_two : ¬ ∃ k : ℕ, (3 : ℕ) = 2 ^ k := by
  rintro ⟨k, hk⟩
  have : (3 : ℕ) ∣ 2 ^ k := ⟨1, by omega⟩
  have := Nat.prime_three.dvd_of_dvd_pow this
  omega

/-- **∛3 lies in no field of `2`-power degree over ℚ.** If `E ⊆ ℝ` is an
    intermediate field with `[E:ℚ] = 2^k`, then `∛3 ∉ E`: otherwise
    `ℚ(∛3) ⊆ E` would force `3 = [ℚ(∛3):ℚ]` to divide `2^k`. This is exactly the
    obstruction that makes `∛3` non-constructible, since every ruler-and-compass
    constructible real lies in such a `2`-power-degree field. -/
theorem cbrt3_notMem_of_finrank_pow_two
    (E : IntermediateField ℚ ℝ) [FiniteDimensional ℚ E] (k : ℕ)
    (hE : Module.finrank ℚ E = 2 ^ k) : cbrt3 ∉ E := by
  intro hmem
  have hle : ℚ⟮cbrt3⟯ ≤ E := (IntermediateField.adjoin_simple_le_iff).mpr hmem
  have hdvd : Module.finrank ℚ ℚ⟮cbrt3⟯ ∣ Module.finrank ℚ E :=
    ⟨_, (IntermediateField.finrank_bot_mul_relfinrank hle).symm⟩
  rw [finrank_adjoin_cbrt3, hE] at hdvd
  have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
  omega

/-- **∛3 is not contained in any quadratic extension of ℚ** (the `k = 1` case):
    the first, decisive obstruction — the doubled cube's side length cannot even
    be reached by a single square-root construction. -/
theorem cbrt3_notMem_of_finrank_two
    (E : IntermediateField ℚ ℝ) [FiniteDimensional ℚ E]
    (hE : Module.finrank ℚ E = 2) : cbrt3 ∉ E :=
  cbrt3_notMem_of_finrank_pow_two E 1 (by rw [hE]; ring)

end CubeRoot3IrrationalOQ03OQ01
