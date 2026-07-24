/-
# Minkowski–Hlawka Theorem (OQ-06): the averaging skeleton, staged

The parent entry (`minkowski-fundamental-theorem`) formalizes Minkowski's *obstruction*
theorem. This node targets the complementary *existence* statement, the
**Minkowski–Hlawka theorem**: for every bounded set `S ⊆ ℝⁿ` of volume `< ζ(n)` there
is a unimodular lattice avoiding `S \ {0}`; consequently there exist lattices of
packing density `≥ ζ(n)/2^(n-1)`.

The classical proof averages over the space `Xₙ = SLₙ(ℤ)\SLₙ(ℝ)` of unimodular
lattices. Its analytic core — the **Siegel–Rogers primitive mean-value identity**

  `∫_{Xₙ} #{w ∈ Λ primitive, w ∈ S} dμ(Λ) = vol(S)/ζ(n)`

— requires the finite Haar probability measure on `Xₙ`, which is absent from Mathlib
(>1000 LOC of missing measure theory; see the node's blocker registry). Following the
staged plan recorded in the node's knowledge (ORIENT sessions 2026-06-14 … 2026-07-22),
this file proves everything *around* that identity unconditionally, and states the
identity as an **explicit hypothesis** of the two main theorems — NOT as an `axiom`.

**Unconditional results (Mathlib-only):**

* `zetaSum` — `ζ(n)` as the real series `∑' m, 1/m^n` (the `m = 0` term vanishes by
  the division-by-zero convention), with `zetaSum_summable` (`n ≥ 2`),
  `one_le_zetaSum`, `zetaSum_pos`.
* `IsPrimitive` — a lattice vector not of the form `m • w` (`m ≥ 2`, `w` in the
  lattice).
* `minimal_isPrimitive` — a nonzero vector of minimal norm is primitive.
* `exists_primitive_norm_le` — **the bridge lemma** identified by the previous
  session: in a uniformly discrete subgroup, below every nonzero vector sits a
  primitive vector of no larger norm (norm-halving descent, strong induction on
  `⌈‖v‖/r₀⌉`).
* `no_nonzero_of_no_primitive_in_ball` — hence "no primitive vector in `ball r`"
  upgrades to "no nonzero vector in `ball r`".
* `exists_count_zero_of_integral_lt_one` — the **better-than-average extraction**:
  an integer-valued random variable with mean `< 1` vanishes somewhere.

**Staged results (Siegel–Rogers identity as hypothesis):**

* `hlawka_avoidance` — `vol(S) < ζ(n)` ⟹ some lattice in the family has no
  primitive vector in `S`.
* `hlawka_ball` — for `S` a ball, the avoidance upgrades via the bridge to a
  **minimum-distance** conclusion: some lattice has all nonzero vectors of norm
  `≥ r`. This is Minkowski–Hlawka in min-distance form (the packing-density
  form `δₙ ≥ ζ(n)/2^n` follows by packing balls of radius `r/2`; the classical
  `ζ(n)/2^(n-1)` needs the additional `±`-pairing refinement of the identity,
  deliberately not staged here — see knowledge.md).

**Honesty.** No `axiom` declarations, no sorries; the two `hlawka_*` theorems are
*conditional* on their `hMV` (mean-value), `hInt` (integrability) and `hFin`
(finiteness of the counted set) hypotheses, which the full (out-of-reach) proof
would supply from the geometry of `Xₙ`. Everything else is unconditional.

Axioms: 0
Sorries: 0
-/

import Mathlib

open MeasureTheory

namespace MinkowskiFundamentalTheoremOQ06

/-! ## ζ(n) as a real series -/

/-- `ζ(n)` as a real series over all of `ℕ`: the `m = 0` term is `1/0 = 0` by the
division-by-zero convention, so this equals `∑_{m ≥ 1} 1/m^n`. -/
noncomputable def zetaSum (n : ℕ) : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ n

/-- The `ζ`-series converges for `n ≥ 2`. -/
theorem zetaSum_summable {n : ℕ} (hn : 2 ≤ n) :
    Summable (fun m : ℕ => 1 / (m : ℝ) ^ n) :=
  Real.summable_one_div_nat_pow.mpr hn

/-- `1 ≤ ζ(n)` for `n ≥ 2`: the `m = 1` term alone is `1`, and all terms are
nonnegative. -/
theorem one_le_zetaSum {n : ℕ} (hn : 2 ≤ n) : 1 ≤ zetaSum n := by
  have h := (zetaSum_summable hn).le_tsum 1 (fun i _ => by positivity)
  simpa [zetaSum] using h

/-- `ζ(n) > 0` for `n ≥ 2`. -/
theorem zetaSum_pos {n : ℕ} (hn : 2 ≤ n) : 0 < zetaSum n :=
  lt_of_lt_of_le one_pos (one_le_zetaSum hn)

/-! ## Primitive vectors and the descent bridge -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A vector of a subgroup `L` is **primitive** if it is a nonzero element of `L`
that is not a proper multiple `m • w` (`m ≥ 2`) of another element of `L`.
(Geometrically: `v` is *visible from the origin* in the lattice `L`.) -/
def IsPrimitive (L : AddSubgroup E) (v : E) : Prop :=
  v ∈ L ∧ v ≠ 0 ∧ ∀ m : ℕ, ∀ w ∈ L, 2 ≤ m → v ≠ m • w

/-- The norm of a natural multiple in a real normed space: `‖m • w‖ = m * ‖w‖`. -/
theorem norm_nsmul_eq (m : ℕ) (w : E) : ‖(m • w : E)‖ = (m : ℝ) * ‖w‖ := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]

/-- **A nonzero vector of minimal norm is primitive.** If `v = m • w` with `m ≥ 2`
then `‖w‖ = ‖v‖/m < ‖v‖`, contradicting minimality. This is the "shortest nonzero
lattice vector is primitive" fact flagged as Mathlib-tractable in the node's
knowledge. -/
theorem minimal_isPrimitive (L : AddSubgroup E) (v : E) (hv : v ∈ L) (hv0 : v ≠ 0)
    (hmin : ∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖) : IsPrimitive L v := by
  refine ⟨hv, hv0, fun m w hw hm heq => ?_⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [smul_zero] at heq
    exact hv0 heq
  have hnorm : ‖v‖ = (m : ℝ) * ‖w‖ := by rw [heq, norm_nsmul_eq]
  have hle : ‖v‖ ≤ ‖w‖ := hmin w hw hw0
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- **The descent bridge.** In a *uniformly discrete* subgroup (all nonzero vectors
have norm `≥ r₀ > 0`), below every nonzero vector sits a primitive vector of no
larger norm. Proof: if `v` is not primitive, write `v = m • w` (`m ≥ 2`); then
`2‖w‖ ≤ ‖v‖`, and since `‖w‖ ≥ r₀` the bound `‖v‖ ≤ (k+1) • r₀` improves to
`‖w‖ ≤ k • r₀` — strong induction on `k` terminates the halving descent. -/
theorem exists_primitive_norm_le (L : AddSubgroup E) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdisc : ∀ u ∈ L, u ≠ 0 → r₀ ≤ ‖u‖) :
    ∀ v ∈ L, v ≠ 0 → ∃ w, IsPrimitive L w ∧ ‖w‖ ≤ ‖v‖ := by
  suffices h : ∀ k : ℕ, ∀ v ∈ L, v ≠ 0 → ‖v‖ ≤ k * r₀ →
      ∃ w, IsPrimitive L w ∧ ‖w‖ ≤ ‖v‖ by
    intro v hv hv0
    obtain ⟨k, hk⟩ := exists_nat_ge (‖v‖ / r₀)
    exact h k v hv hv0 ((div_le_iff₀ hr₀).mp hk)
  intro k
  induction k with
  | zero =>
    intro v hv hv0 hle
    have := hdisc v hv hv0
    simp only [Nat.cast_zero, zero_mul] at hle
    linarith
  | succ k ih =>
    intro v hv hv0 hle
    by_cases hprim : IsPrimitive L v
    · exact ⟨v, hprim, le_refl _⟩
    · -- Not primitive: extract a proper multiple decomposition `v = m • w`.
      have hdecomp : ∃ m : ℕ, ∃ w ∈ L, 2 ≤ m ∧ v = m • w := by
        by_contra hcon
        push_neg at hcon
        exact hprim ⟨hv, hv0, fun m w hw hm heq => hcon m w hw hm heq⟩
      obtain ⟨m, w, hw, hm, heq⟩ := hdecomp
      have hw0 : w ≠ 0 := by
        rintro rfl
        rw [smul_zero] at heq
        exact hv0 heq
      have hnorm : ‖v‖ = (m : ℝ) * ‖w‖ := by rw [heq, norm_nsmul_eq]
      have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hwr : r₀ ≤ ‖w‖ := hdisc w hw hw0
      have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hr₀ hwr
      -- `2‖w‖ ≤ ‖v‖ ≤ (k+1)r₀` and `‖w‖ ≥ r₀` give `‖w‖ ≤ k·r₀`.
      have hwk : ‖w‖ ≤ k * r₀ := by
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hle
        nlinarith
      obtain ⟨u, hup, hule⟩ := ih w hw hw0 hwk
      refine ⟨u, hup, le_trans hule ?_⟩
      nlinarith
    -- (halving descent uses only `m ≥ 2`, never the exact value of `m`)

/-- **Bridge, avoidance form.** If a uniformly discrete subgroup has *no primitive
vector* in the open ball of radius `r`, it has *no nonzero vector at all* there:
minimum distance `≥ r`. -/
theorem no_nonzero_of_no_primitive_in_ball (L : AddSubgroup E) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdisc : ∀ u ∈ L, u ≠ 0 → r₀ ≤ ‖u‖) {r : ℝ}
    (hnoprim : ∀ w, IsPrimitive L w → r ≤ ‖w‖) :
    ∀ v ∈ L, v ≠ 0 → r ≤ ‖v‖ := by
  intro v hv hv0
  by_contra hlt
  push_neg at hlt
  obtain ⟨w, hwp, hwle⟩ := exists_primitive_norm_le L hr₀ hdisc v hv hv0
  exact absurd (lt_of_le_of_lt hwle hlt) (not_lt.mpr (hnoprim w hwp))

/-! ## The better-than-average extraction -/

/-- **An integer-valued random variable with mean `< 1` vanishes somewhere.** This
is the entire non-constructive engine of the Minkowski–Hlawka averaging argument:
if the *average* number of (primitive) lattice points in `S` is below `1`, some
lattice contains none. -/
theorem exists_count_zero_of_integral_lt_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (N : Ω → ℕ)
    (hInt : Integrable (fun ω => (N ω : ℝ)) μ)
    (hmean : ∫ ω, (N ω : ℝ) ∂μ < 1) : ∃ ω, N ω = 0 := by
  by_contra h
  push_neg at h
  have h1 : ∀ ω, (1 : ℝ) ≤ (N ω : ℝ) := fun ω => by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (h ω)
  have hint1 : ∫ ω, (1 : ℝ) ∂μ ≤ ∫ ω, (N ω : ℝ) ∂μ :=
    integral_mono (integrable_const 1) hInt h1
  simp at hint1
  linarith

/-! ## The staged Minkowski–Hlawka theorems

The space of unimodular lattices is abstracted to a probability space `Ω` with a
lattice-valued map `latticeOf`. The Siegel–Rogers primitive mean-value identity
enters as the hypothesis `hMV` — the single deep input the gallery cannot yet
prove (see the node's blocker registry). -/

/-- The number of primitive vectors of `L` lying in `S` (finite by `hFin` in the
theorems below; `Set.ncard` of an infinite set would be `0`, which is why the
staged theorems carry an explicit finiteness hypothesis). -/
noncomputable def primCount (L : AddSubgroup E) (S : Set E) : ℕ :=
  (S ∩ {v | IsPrimitive L v}).ncard

/-- **Minkowski–Hlawka, avoidance form (staged).** Let `latticeOf : Ω → lattices`
be a family over a probability space satisfying the Siegel–Rogers primitive
mean-value identity `hMV` for the set `S`. If `vol(S) < ζ(n)`, then some lattice
in the family has **no primitive vector in `S`**.

Hypotheses `hMV`/`hInt`/`hFin` are exactly what the (Mathlib-absent) geometry of
`SLₙ(ℤ)\SLₙ(ℝ)` would provide; the extraction itself is unconditional. -/
theorem hlawka_avoidance {n : ℕ} (hn : 2 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hMV : ∫ ω, (primCount (latticeOf ω) S : ℝ) ∂μ = (volume S).toReal / zetaSum n)
    (hInt : Integrable (fun ω => (primCount (latticeOf ω) S : ℝ)) μ)
    (hFin : ∀ ω, (S ∩ {v | IsPrimitive (latticeOf ω) v}).Finite)
    (hvol : (volume S).toReal < zetaSum n) :
    ∃ ω, ∀ v, IsPrimitive (latticeOf ω) v → v ∉ S := by
  have hζ : 0 < zetaSum n := zetaSum_pos hn
  have hmean : ∫ ω, (primCount (latticeOf ω) S : ℝ) ∂μ < 1 := by
    rw [hMV]
    rw [div_lt_one hζ]
    exact hvol
  obtain ⟨ω, hω⟩ := exists_count_zero_of_integral_lt_one _ hInt hmean
  refine ⟨ω, fun v hvp hvS => ?_⟩
  have hempty : S ∩ {v | IsPrimitive (latticeOf ω) v} = ∅ :=
    (Set.ncard_eq_zero (hFin ω)).mp hω
  exact absurd (Set.mem_inter hvS hvp) (by rw [hempty]; exact Set.notMem_empty v)

/-- **Minkowski–Hlawka, minimum-distance form (staged).** Specializing the
avoidance theorem to `S = ball 0 r` and upgrading through the descent bridge:
if `vol(ball r) < ζ(n)` then some lattice in the family has minimum distance
`≥ r` — all its nonzero vectors have norm at least `r`. Existence of dense
lattice packings follows by packing balls of radius `r/2` (density form not
formalized here; see file header). -/
theorem hlawka_ball {n : ℕ} (hn : 2 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (r₀ : Ω → ℝ) (hr₀ : ∀ ω, 0 < r₀ ω)
    (hdisc : ∀ ω, ∀ u ∈ latticeOf ω, u ≠ 0 → r₀ ω ≤ ‖u‖)
    {r : ℝ}
    (hMV : ∫ ω, (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ) ∂μ =
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal / zetaSum n)
    (hInt : Integrable
      (fun ω => (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ)) μ)
    (hFin : ∀ ω,
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ∩
        {v | IsPrimitive (latticeOf ω) v}).Finite)
    (hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal < zetaSum n) :
    ∃ ω, ∀ v ∈ latticeOf ω, v ≠ 0 → r ≤ ‖v‖ := by
  obtain ⟨ω, hω⟩ := hlawka_avoidance hn μ latticeOf _ hMV hInt hFin hvol
  refine ⟨ω, no_nonzero_of_no_primitive_in_ball (latticeOf ω) (hr₀ ω) (hdisc ω) ?_⟩
  intro w hwp
  by_contra hlt
  push_neg at hlt
  exact hω w hwp (Metric.mem_ball.mpr (by simpa using hlt))

#check @zetaSum_summable
#check @one_le_zetaSum
#check @minimal_isPrimitive
#check @exists_primitive_norm_le
#check @no_nonzero_of_no_primitive_in_ball
#check @exists_count_zero_of_integral_lt_one
#check @hlawka_avoidance
#check @hlawka_ball

end MinkowskiFundamentalTheoremOQ06
