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
* `finite_inter_of_isBounded_of_uniform_discrete` — in a proper space, a bounded
  set meets a uniformly discrete subgroup finitely often (cover by `r₀/3`-balls;
  each holds ≤ 1 subgroup point). Discharges the `hFin` staging hypothesis:
  `hlawka_avoidance_of_isBounded` / `hlawka_ball_of_discrete` need only the
  analytic hypotheses `hMV` and `hInt`.

**Staged results (Siegel–Rogers identity as hypothesis):**

* `hlawka_avoidance` — `vol(S) < ζ(n)` ⟹ some lattice in the family has no
  primitive vector in `S`.
* `hlawka_ball` — for `S` a ball, the avoidance upgrades via the bridge to a
  **minimum-distance** conclusion: some lattice has all nonzero vectors of norm
  `≥ r`. This is Minkowski–Hlawka in min-distance form (the packing-density
  form `δₙ ≥ ζ(n)/2^n` follows by packing balls of radius `r/2`).
* `hlawka_avoidance_symm` / `hlawka_ball_symm` — the **`±`-pairing rung** (S5):
  on a symmetric set a lattice with one primitive vector has two (`v` and
  `-v`), so the volume threshold doubles to `2·ζ(n)` with the SAME mean-value
  hypothesis — the classical route to `δₙ ≥ ζ(n)/2^(n-1)` (the residual
  `2^(1-n)` is ball-volume scaling, not averaging).
* `hlawka_density_symm` — the **density rung** (S6): combining the doubled
  threshold with the unconditional ball-volume bookkeeping
  (`volume_ball_toReal`, `volume_ball_half_toReal`, `exists_radius_of_density`
  — all pure Mathlib measure theory via `Measure.addHaar_ball`), every packing
  density `d < ζ(n)/2^(n-1)` is realized by a lattice of the family: this is
  the classical `δₙ ≥ ζ(n)/2^(n-1)` statement, staged only on `hMV`/`hInt`.

**Honesty.** No `axiom` declarations, no sorries; the `hlawka_*` theorems are
*conditional* on their `hMV` (mean-value) and `hInt` (integrability) hypotheses
(and, in the original two, `hFin` — now discharged for bounded sets by
`finite_inter_of_isBounded_of_uniform_discrete`), which the full (out-of-reach)
proof would supply from the geometry of `Xₙ`. Everything else is unconditional.

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

/-! ## Discharging the finiteness hypothesis

The `hFin` staging hypothesis of the theorems above is not deep: in a *proper*
normed space (in particular `EuclideanSpace ℝ (Fin n)`), a bounded set can only
meet a uniformly discrete subgroup in finitely many points. Cover the bounded
set by finitely many balls of radius `r₀/3` (total boundedness via compact
closure); two distinct subgroup points in one such ball would differ by a
nonzero subgroup element of norm `< 2r₀/3 < r₀`, contradicting uniform
discreteness — so each ball holds at most one point.

Note the properness hypothesis is essential, not decorative: in `ℓ²` the
subgroup generated by the orthonormal basis vectors is uniformly discrete
(every nonzero element has norm `≥ 1`), yet the bounded ball of radius `3/2`
contains all infinitely many basis vectors. -/

/-- A ball of radius `r₀/3` contains at most one point of a uniformly discrete
subgroup: two such points differ by a nonzero element of norm `< r₀`. -/
theorem subsingleton_ball_inter_of_uniform_discrete (L : AddSubgroup E) {r₀ : ℝ}
    (hdisc : ∀ u ∈ L, u ≠ 0 → r₀ ≤ ‖u‖) (y : E) :
    (Metric.ball y (r₀ / 3) ∩ (L : Set E)).Subsingleton := by
  intro a ha b hb
  by_contra hne
  have hab : a - b ∈ L := L.sub_mem ha.2 hb.2
  have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hr := hdisc _ hab hab0
  have hd : ‖a - b‖ < 2 * (r₀ / 3) := by
    have h1 : dist a y < r₀ / 3 := Metric.mem_ball.mp ha.1
    have h2 : dist b y < r₀ / 3 := Metric.mem_ball.mp hb.1
    have h3 : dist a b ≤ dist a y + dist y b := dist_triangle a y b
    rw [dist_comm y b] at h3
    rw [← dist_eq_norm]
    linarith
  have hn0 : (0 : ℝ) ≤ ‖a - b‖ := norm_nonneg _
  linarith

/-- **A bounded set meets a uniformly discrete subgroup finitely often** (in a
proper space). This is the lemma that discharges the `hFin` hypothesis of the
staged theorems. -/
theorem finite_inter_of_isBounded_of_uniform_discrete [ProperSpace E]
    (L : AddSubgroup E) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdisc : ∀ u ∈ L, u ≠ 0 → r₀ ≤ ‖u‖) {S : Set E}
    (hS : Bornology.IsBounded S) : (S ∩ (L : Set E)).Finite := by
  have htb : TotallyBounded S :=
    TotallyBounded.subset subset_closure hS.isCompact_closure.totallyBounded
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp htb (r₀ / 3)
    (by positivity)
  refine Set.Finite.subset (htfin.biUnion
    (fun y _ => (subsingleton_ball_inter_of_uniform_discrete L hdisc y).finite))
    fun x hx => ?_
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx.1)
  exact Set.mem_biUnion hyt ⟨hxy, hx.2⟩

/-- The primitive vectors of `L` in a bounded set form a finite set: primitive
vectors are in particular subgroup elements. Discharges `hFin`. -/
theorem finite_primitive_inter_of_isBounded [ProperSpace E]
    (L : AddSubgroup E) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdisc : ∀ u ∈ L, u ≠ 0 → r₀ ≤ ‖u‖) {S : Set E}
    (hS : Bornology.IsBounded S) : (S ∩ {v | IsPrimitive L v}).Finite :=
  (finite_inter_of_isBounded_of_uniform_discrete L hr₀ hdisc hS).subset
    fun _ hx => ⟨hx.1, hx.2.1⟩

/-- **Minkowski–Hlawka, avoidance form, for bounded sets.** Same as
`hlawka_avoidance` but with the finiteness hypothesis *discharged*: for a
bounded `S` and a family of uniformly discrete lattices, `hFin` is a theorem
(`finite_primitive_inter_of_isBounded`), not an assumption. The staging
hypotheses are now exactly the analytic ones (`hMV`, `hInt`). -/
theorem hlawka_avoidance_of_isBounded {n : ℕ} (hn : 2 ≤ n) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (r₀ : Ω → ℝ) (hr₀ : ∀ ω, 0 < r₀ ω)
    (hdisc : ∀ ω, ∀ u ∈ latticeOf ω, u ≠ 0 → r₀ ω ≤ ‖u‖)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Bornology.IsBounded S)
    (hMV : ∫ ω, (primCount (latticeOf ω) S : ℝ) ∂μ = (volume S).toReal / zetaSum n)
    (hInt : Integrable (fun ω => (primCount (latticeOf ω) S : ℝ)) μ)
    (hvol : (volume S).toReal < zetaSum n) :
    ∃ ω, ∀ v, IsPrimitive (latticeOf ω) v → v ∉ S :=
  hlawka_avoidance hn μ latticeOf S hMV hInt
    (fun ω => finite_primitive_inter_of_isBounded (latticeOf ω) (hr₀ ω)
      (hdisc ω) hS) hvol

/-- **Minkowski–Hlawka, minimum-distance form, finiteness discharged.** Same
as `hlawka_ball`, but `hFin` is derived from the uniform discreteness the
theorem already assumes (balls are bounded). The remaining staging hypotheses
are exactly the Siegel–Rogers identity `hMV` and its integrability `hInt`. -/
theorem hlawka_ball_of_discrete {n : ℕ} (hn : 2 ≤ n) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (r₀ : Ω → ℝ) (hr₀ : ∀ ω, 0 < r₀ ω)
    (hdisc : ∀ ω, ∀ u ∈ latticeOf ω, u ≠ 0 → r₀ ω ≤ ‖u‖)
    {r : ℝ}
    (hMV : ∫ ω, (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ) ∂μ =
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal / zetaSum n)
    (hInt : Integrable
      (fun ω => (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ)) μ)
    (hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal < zetaSum n) :
    ∃ ω, ∀ v ∈ latticeOf ω, v ≠ 0 → r ≤ ‖v‖ :=
  hlawka_ball hn μ latticeOf r₀ hr₀ hdisc hMV hInt
    (fun ω => finite_primitive_inter_of_isBounded (latticeOf ω) (hr₀ ω)
      (hdisc ω) Metric.isBounded_ball) hvol

/-! ## The ±-pairing rung (S5)

Primitive vectors come in pairs `{v, -v}`: negation preserves membership,
nonzeroness, and primitivity, and `-v ≠ v` in a real vector space (no
2-torsion). Consequently, on a *symmetric* set `S = -S` a lattice either has
no primitive vector in `S` or at least **two** — so in the averaging argument
a mean below `2` (not merely below `1`) already forces an avoiding lattice.
This doubles the volume threshold of the staged Minkowski–Hlawka theorems
from `ζ(n)` to `2·ζ(n)`, the classical route to the density bound
`δ_n ≥ ζ(n)/2^(n-1)` (the remaining factor `2^(1-n)` is the ball-volume
scaling `vol(ball r) = r^n·vol(ball 1)` in the packing-density bookkeeping,
not part of the averaging engine). -/

/-- Negation preserves primitivity: if `-v = m • w` with `m ≥ 2` then
`v = m • (-w)` exhibits the same proper-multiple decomposition. -/
theorem IsPrimitive.neg {L : AddSubgroup E} {v : E} (h : IsPrimitive L v) :
    IsPrimitive L (-v) := by
  obtain ⟨hvL, hv0, hprim⟩ := h
  refine ⟨neg_mem hvL, neg_ne_zero.mpr hv0, fun m w hw hm heq => ?_⟩
  apply hprim m (-w) (neg_mem hw) hm
  rw [← neg_neg v, heq, smul_neg]

/-- In a real vector space, `-v ≠ v` for `v ≠ 0` (no 2-torsion): from `-v = v`
one gets `(2 : ℝ) • v = 0`, forcing `v = 0`. -/
theorem neg_ne_self_of_ne_zero {v : E} (hv0 : v ≠ 0) : -v ≠ v := by
  intro hEq
  apply hv0
  have h2v : v + v = 0 := by
    nth_rewrite 1 [← hEq]
    exact neg_add_cancel v
  have h2 : (2 : ℝ) • v = 0 := by rw [two_smul]; exact h2v
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- **The pairing bound.** On a symmetric set, one primitive vector in `S`
forces two: `v` and `-v` are distinct primitive members. -/
theorem two_le_primCount_of_symm_of_mem (L : AddSubgroup E)
    (S : Set E) (hSymm : ∀ v ∈ S, -v ∈ S)
    (hFin : (S ∩ {u | IsPrimitive L u}).Finite)
    {v : E} (hvp : IsPrimitive L v) (hvS : v ∈ S) : 2 ≤ primCount L S := by
  have hne : v ≠ -v := (neg_ne_self_of_ne_zero hvp.2.1).symm
  have hsub : ({v, -v} : Set E) ⊆ S ∩ {u | IsPrimitive L u} := by
    intro u hu
    rcases hu with rfl | hu
    · exact ⟨hvS, hvp⟩
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨hSymm v hvS, hvp.neg⟩
  calc 2 = ({v, -v} : Set E).ncard := (Set.ncard_pair hne).symm
    _ ≤ (S ∩ {u | IsPrimitive L u}).ncard := Set.ncard_le_ncard hsub hFin

/-- **Minkowski–Hlawka, avoidance form, symmetric sets (doubled threshold).**
For `S = -S` the volume threshold improves from `ζ(n)` to `2·ζ(n)`: a lattice
with any primitive vector in `S` has at least two (pairing), so a mean below
`2` already forces an avoiding lattice. -/
theorem hlawka_avoidance_symm {n : ℕ} (hn : 2 ≤ n) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hSymm : ∀ v ∈ S, -v ∈ S)
    (hMV : ∫ ω, (primCount (latticeOf ω) S : ℝ) ∂μ = (volume S).toReal / zetaSum n)
    (hInt : Integrable (fun ω => (primCount (latticeOf ω) S : ℝ)) μ)
    (hFin : ∀ ω, (S ∩ {v | IsPrimitive (latticeOf ω) v}).Finite)
    (hvol : (volume S).toReal < 2 * zetaSum n) :
    ∃ ω, ∀ v, IsPrimitive (latticeOf ω) v → v ∉ S := by
  have hζ : 0 < zetaSum n := zetaSum_pos hn
  by_contra h
  push Not at h
  have h2 : ∀ ω, (2 : ℝ) ≤ (primCount (latticeOf ω) S : ℝ) := by
    intro ω
    obtain ⟨v, hvp, hvS⟩ := h ω
    exact_mod_cast two_le_primCount_of_symm_of_mem (latticeOf ω) S hSymm
      (hFin ω) hvp hvS
  have hint2 : (2 : ℝ) ≤ ∫ ω, (primCount (latticeOf ω) S : ℝ) ∂μ := by
    have hmono := integral_mono (integrable_const 2) hInt h2
    simpa using hmono
  rw [hMV, le_div_iff₀ hζ] at hint2
  linarith

/-- **Minkowski–Hlawka, minimum-distance form, doubled threshold.** Balls are
symmetric, so the pairing rung applies: `vol(ball r) < 2·ζ(n)` suffices for a
lattice of minimum distance `≥ r`. Combined with `vol(ball r) = r^n·vol(ball 1)`
this is the classical `δ_n ≥ ζ(n)/2^(n-1)` averaging input. -/
theorem hlawka_ball_symm {n : ℕ} (hn : 2 ≤ n) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (r₀ : Ω → ℝ) (hr₀ : ∀ ω, 0 < r₀ ω)
    (hdisc : ∀ ω, ∀ u ∈ latticeOf ω, u ≠ 0 → r₀ ω ≤ ‖u‖)
    {r : ℝ}
    (hMV : ∫ ω, (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ) ∂μ =
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal / zetaSum n)
    (hInt : Integrable
      (fun ω => (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ)) μ)
    (hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal <
      2 * zetaSum n) :
    ∃ ω, ∀ v ∈ latticeOf ω, v ≠ 0 → r ≤ ‖v‖ := by
  have hSymm : ∀ v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
      -v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    simpa using hv
  obtain ⟨ω, hω⟩ := hlawka_avoidance_symm hn μ latticeOf _ hSymm hMV hInt
    (fun ω => finite_primitive_inter_of_isBounded (latticeOf ω) (hr₀ ω)
      (hdisc ω) Metric.isBounded_ball) hvol
  refine ⟨ω, no_nonzero_of_no_primitive_in_ball (latticeOf ω) (hr₀ ω) (hdisc ω) ?_⟩
  intro w hwp
  by_contra hlt
  push Not at hlt
  exact hω w hwp (Metric.mem_ball.mpr (by simpa using hlt))

/-! ## Density bookkeeping: ball-volume scaling (S6)

The scaling law `vol(ball r) = rⁿ·vol(ball 1)` converts the doubled threshold
`2·ζ(n)` of `hlawka_ball_symm` into the classical **packing-density** form of
Minkowski–Hlawka: a covolume-1 lattice of minimum distance `≥ r` packs balls of
radius `r/2` at density `vol(ball (r/2)) = vol(ball r)/2ⁿ` per unit covolume,
so every density `d < ζ(n)/2^(n-1)` is realized by some lattice in the family.
All new lemmas in this section are unconditional Mathlib measure theory
(`Measure.addHaar_ball`); the headline `hlawka_density_symm` carries only the
same `hMV`/`hInt` staging hypotheses as before, now quantified over radii. -/

/-- The volume of the unit ball of `EuclideanSpace ℝ (Fin n)`, as a real. -/
noncomputable def unitBallVol (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- Ball-volume scaling in real form: `vol(ball 0 r) = rⁿ · vol(ball 0 1)`.
(The Haar-scaling identity `Measure.addHaar_ball`, pushed through `toReal`;
the ball has finite volume, so nothing is lost.) -/
theorem volume_ball_toReal {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal
      = r ^ n * unitBallVol n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Measure.addHaar_ball volume 0 hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
  rfl

/-- The unit ball has positive volume (`volume` is an open-positive Haar
measure and the ball is finite by properness). -/
theorem unitBallVol_pos {n : ℕ} (hn : 1 ≤ n) : 0 < unitBallVol n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
    measure_ball_lt_top.ne

/-- Half-radius scaling: `vol(ball (r/2)) = vol(ball r) / 2ⁿ` — the exact
`2^(1-n)` bookkeeping factor between the doubled avoidance threshold and the
packing-density bound. -/
theorem volume_ball_half_toReal {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2))).toReal
      = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal / 2 ^ n := by
  rw [volume_ball_toReal hn (by positivity), volume_ball_toReal hn hr, div_pow]
  ring

/-- Radius realization: every positive real `c` is the volume of some ball
(`r = (c/vol(B₁))^(1/n)`, inverted through `Real.rpow`). -/
theorem exists_radius_volume_eq {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal = c := by
  have hv := unitBallVol_pos (n := n) hn
  have hbase : (0 : ℝ) < c / unitBallVol n := by positivity
  refine ⟨(c / unitBallVol n) ^ ((n : ℝ)⁻¹), by positivity, ?_⟩
  rw [volume_ball_toReal hn (by positivity),
    Real.rpow_inv_natCast_pow hbase.le (by omega)]
  field_simp

/-- **Density bookkeeping (unconditional).** Every target density
`0 < d < ζ(n)/2^(n-1)` arises as `vol(ball (r/2))` for a radius `r` whose ball
clears the doubled avoidance threshold: `vol(ball r) < 2·ζ(n)`. -/
theorem exists_radius_of_density {n : ℕ} (hn : 2 ≤ n) {d : ℝ} (hd : 0 < d)
    (hdlt : d < zetaSum n / 2 ^ (n - 1)) :
    ∃ r : ℝ, 0 < r ∧
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2))).toReal = d ∧
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal
        < 2 * zetaSum n := by
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  obtain ⟨r, hr, hvol⟩ :=
    exists_radius_volume_eq hn1 (c := 2 ^ n * d) (by positivity)
  have h2 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  refine ⟨r, hr, ?_, ?_⟩
  · rw [volume_ball_half_toReal hn1 hr.le, hvol]
    field_simp
  · rw [hvol, h2, mul_assoc]
    have := mul_lt_mul_of_pos_left hdlt
      (show (0 : ℝ) < 2 ^ (n - 1) * 2 by positivity)
    calc 2 * (2 ^ (n - 1) * d) = 2 ^ (n - 1) * 2 * d := by ring
      _ < 2 ^ (n - 1) * 2 * (zetaSum n / 2 ^ (n - 1)) := this
      _ = 2 * zetaSum n := by field_simp; ring

/-- **Minkowski–Hlawka, packing-density form (staged, S6).** Under the
primitive Siegel–Rogers staging hypotheses (`hMV`, `hInt` — quantified over
all radii, as the true identity holds for every Borel set), every density
`d < ζ(n)/2^(n-1)` is realized: there is a radius `r` with
`vol(ball (r/2)) = d` and a lattice in the family of minimum distance `≥ r`,
i.e. whose balls of radius `r/2` pack at density `d` per unit covolume. This
is the classical density statement `δₙ ≥ ζ(n)/2^(n-1)`, with the sole missing
input the Siegel–Rogers identity itself (the node's registry blocker). -/
theorem hlawka_density_symm {n : ℕ} (hn : 2 ≤ n) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (latticeOf : Ω → AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (r₀ : Ω → ℝ) (hr₀ : ∀ ω, 0 < r₀ ω)
    (hdisc : ∀ ω, ∀ u ∈ latticeOf ω, u ≠ 0 → r₀ ω ≤ ‖u‖)
    (hMV : ∀ r : ℝ, 0 < r →
      ∫ ω, (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ) ∂μ =
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)).toReal / zetaSum n)
    (hInt : ∀ r : ℝ, 0 < r →
      Integrable (fun ω => (primCount (latticeOf ω) (Metric.ball 0 r) : ℝ)) μ)
    {d : ℝ} (hd : 0 < d) (hdlt : d < zetaSum n / 2 ^ (n - 1)) :
    ∃ r : ℝ, 0 < r ∧
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2))).toReal = d ∧
      ∃ ω, ∀ v ∈ latticeOf ω, v ≠ 0 → r ≤ ‖v‖ := by
  obtain ⟨r, hr, hhalf, hvol⟩ := exists_radius_of_density hn hd hdlt
  exact ⟨r, hr, hhalf,
    hlawka_ball_symm hn μ latticeOf r₀ hr₀ hdisc (hMV r hr) (hInt r hr) hvol⟩

#check @zetaSum_summable
#check @one_le_zetaSum
#check @minimal_isPrimitive
#check @exists_primitive_norm_le
#check @no_nonzero_of_no_primitive_in_ball
#check @exists_count_zero_of_integral_lt_one
#check @hlawka_avoidance
#check @hlawka_ball
#check @finite_inter_of_isBounded_of_uniform_discrete
#check @finite_primitive_inter_of_isBounded
#check @hlawka_avoidance_of_isBounded
#check @hlawka_ball_of_discrete
#check @IsPrimitive.neg
#check @two_le_primCount_of_symm_of_mem
#check @hlawka_avoidance_symm
#check @hlawka_ball_symm
#check @volume_ball_toReal
#check @unitBallVol_pos
#check @volume_ball_half_toReal
#check @exists_radius_volume_eq
#check @exists_radius_of_density
#check @hlawka_density_symm

end MinkowskiFundamentalTheoremOQ06
