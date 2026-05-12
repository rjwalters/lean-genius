# Knowledge: minkowski-theorem-oq-02-oq-03

## Mathlib API Map (used by parent / sibling files; lift directly to general n)

### Minkowski's theorem (the n-dim step is FREE)

```
MinkowskiProved.minkowski_integer_lattice_proved
    (s : Set (Fin n → ℝ))
    (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s)
    (h_vol  : (2 : ENNReal) ^ n < volume s) :
    ∃ x : (stdLattice n).toAddSubgroup, x ≠ 0 ∧ (x : Fin n → ℝ) ∈ s
```

Location: `proofs/Proofs/MinkowskiFundamentalTheorem.lean:638` (gallery
proof `minkowski-fundamental-theorem`, 0 axioms, 0 sorries). Stated for
arbitrary `n` already; we will call it with the lattice dimension
`m = n + 1` (one common-denominator coordinate + `n` approximation
coordinates).

### Shear-map volume identity (used in the OQ-02-OQ-01 sibling)

```
map_matrix_volume_pi_eq_smul_volume_pi
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.det ≠ 0) :
    Measure.map M.toLin' volume = ENNReal.ofReal |M.det|⁻¹ • volume
```

Location: standard Mathlib (`Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`).
Used at `MinkowskiTheoremOQ02OQ01.lean:103` for the 2x2 shear; lifts to
arbitrary `n` for the lower-triangular shear

```
M = !![1, 0, …, 0; α 0, -1, 0, …, 0; α 1, 0, -1, …, 0; …; α (n-1), 0, …, -1]
```

with `M.det = (-1)^n`, so `|M.det| = 1`.

### Open-set measurability (the OQ-02-OQ-01 sibling's measurability step)

```
IsOpen.measurableSet : IsOpen s → MeasurableSet s
```

`dirichletSetN α Q` is `(fun v => v 0) ⁻¹' Ioo (-Qⁿ-1) (Qⁿ+1)` intersected
with `n` further `Ioo`-preimages under continuous functions
`α i * v 0 - v i.succ`, hence open.

### Linear-preimage convexity

```
Convex.linear_preimage : Convex 𝕜 s → ∀ (f : F →ₗ[𝕜] E), Convex 𝕜 (f ⁻¹' s)
Convex.iInter : (∀ i, Convex 𝕜 (s i)) → Convex 𝕜 (⋂ i, s i)
```

Used at `MinkowskiTheoremOQ02OQ01.lean:73-78`. Each predicate in
`dirichletSetN` is the preimage of an `Ioo` under a linear functional
(`LinearMap.proj 0` for the first; `α i • LinearMap.proj 0 - LinearMap.proj i.succ`
for the rest), so finite-intersection convexity follows.

### Integer-coordinate extraction

```
Submodule.mem_span_range_iff_exists_fun :
    x ∈ Submodule.span ℤ (Set.range b) ↔ ∃ c : ι → ℤ, x = ∑ i, c i • b i
```

Used in both `MinkowskiTheoremOQ02.lean` and `MinkowskiTheoremOQ02OQ01.lean`
to extract the integer-valued solution `(q, p₁, …, pₙ)` from the
`stdLattice (n+1)` membership returned by Minkowski.

## Three-axiom analog table (1D → n-dim)

| 1D parent (`MinkowskiTheoremOQ02.lean`)              | n-dim target (this OQ)                                | Proof technique (lifted from `OQ-02-OQ-01`)                                                                |
|------------------------------------------------------|-------------------------------------------------------|-------------------------------------------------------------------------------------------------------------|
| `dirichletSet_convex`                                | `dirichletSetN_convex`                                | `Convex.iInter` over `Fin n` of linear-preimages of `convex_Ioo`                                            |
| `dirichletSet_measurable`                            | `dirichletSetN_measurable`                            | `IsOpen.measurableSet` after rewriting as `Set.iInter` of preimages of `Ioo` under continuous maps          |
| `dirichletSet_volume = ENNReal.ofReal (4(Q+1)/Q)`    | `dirichletSetN_volume = ENNReal.ofReal (2^(n+1)(Qⁿ+1)/Qⁿ)` | `map_matrix_volume_pi_eq_smul_volume_pi` + `volume_pi_Ioo` + `Fin.prod_univ_succ`                       |

## Volume calculation (target identity)

After the lower-triangular shear
`T v = (v 0, α 0 * v 0 - v 1, …, α (n-1) * v 0 - v n)`,
the image of `dirichletSetN α Q` is

```
Set.pi univ (fun i : Fin (n+1) =>
  if i = 0 then Ioo (-(Qⁿ + 1)) (Qⁿ + 1)
            else Ioo (-1/Q) (1/Q))
```

with measure

```
volume(image) = 2(Qⁿ + 1) · (2/Q)ⁿ
              = 2^(n+1) · (Qⁿ + 1) / Qⁿ
              > 2^(n+1) since Qⁿ + 1 > Qⁿ.
```

`|det T| = 1`, so `volume(dirichletSetN α Q) = volume(image)`.

## Insights from the OBSERVE survey

- **The n-dim infrastructure is fully in place.** No new Mathlib
  imports are needed beyond what `MinkowskiTheoremOQ02OQ01.lean`
  already uses; the only difference is the indexing.
- **The shear determinant is `(-1)^n`, not the 1D `-1`.** A
  one-line `simp [Matrix.det_of_lowerTriangular]` (if available) or
  cofactor-expansion lemma closes it; the determinant's sign is
  irrelevant since the volume identity uses `|det T|`.
- **Indexing choice matters.** Use `Fin (n+1)` with `v 0` =
  common-denominator coordinate and `v i.succ` = i-th approximation
  coordinate. The alternative `Sum Unit (Fin n)` indexing makes the
  shear map's matrix harder to state and `Linear`-preimage
  manipulations less uniform.
- **The conclusion bound `q ≤ Qⁿ` matches Cassels (1957) and is sharp:**
  the box width in coordinate 0 must be `2(Qⁿ + 1)` (not `2(Q + 1)`)
  to push volume past `2^(n+1)` while keeping each approximation
  width at `2/Q`.

## Open meta-questions for S2+

1. **Should the result also prove the "infinitely many denominators" corollary?**
   For irrational tuples (with `1, α₁, …, αₙ` linearly independent over `ℚ`),
   the corollary states that there are infinitely many `q` with
   `max |αᵢ - pᵢ/q| < 1/q^(1+1/n)`. This is the metric-theory entry
   point. Decision: defer to a follow-up sub-OQ; OQ-02-OQ-03 should
   match the finite Q-bounded statement, parallel to OQ-02's
   1D version.

2. **Axiom-free from the start, or axiomatized + sibling OQ?**
   Given that the 1D case already has both an axiomatized parent
   (OQ-02) and an axiom-free sibling (OQ-02-OQ-01), this OQ should
   aim directly for axiom-free in `MinkowskiTheoremOQ02OQ03.lean`
   from S2 onward (no separate "axiomatized first, axiom-free
   later" split).

3. **Companion `*Aristotle.lean` file scope?**
   Routine lemmas (cardinality bounds, `Fin.prod_univ_succ`,
   `Matrix.det_of_lowerTriangular`-driven sign manipulations) are
   already in Mathlib. The companion file may be empty or contain
   only one or two technical bridges. Decision: defer companion
   creation to S5 (when the shear / volume step may surface
   technical sub-lemmas worth Aristotle-shaped probes).
