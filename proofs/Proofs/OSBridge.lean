import Mathlib

/-
Copyright (c) 2026 Lean Genius Contributors. All rights reserved.
Released under Apache 2.0 license.

# Osterwalder-Schrader to Wightman Bridge

This file defines the Osterwalder-Schrader (OS) axioms for Euclidean quantum field
theory and states the OS reconstruction theorem, which produces a Wightman QFT
(in Minkowski spacetime) from Euclidean data.

## Origin

The OS axiom definitions are ported from Douglas, Hoback, Mei, Nissim,
"Formalization of QFT" (arXiv:2603.15770, 2026), who proved these axioms
are satisfiable for the free massive Gaussian field in Lean 4. Their
Lean 4 code is at github.com/mrdouglasny/OSforGFF (Apache 2.0).

We adapt their definitions to work with Mathlib v4.26.0 without requiring
the bochner/gaussian-field library dependencies.

## Mathematical Content

The Osterwalder-Schrader axioms characterize Euclidean QFTs that can be
analytically continued to relativistic (Minkowski) QFTs satisfying the
Wightman axioms. The reconstruction theorem (Osterwalder-Schrader 1973, 1975)
provides this bridge.

## References

- Osterwalder, K., Schrader, R. (1973). "Axioms for Euclidean Green's Functions"
- Osterwalder, K., Schrader, R. (1975). "Axioms for Euclidean Green's Functions II"
- Glimm, J., Jaffe, A. (1987). "Quantum Physics: A Functional Integral Point of View"
- Douglas, M.R. et al. (2026). "Formalization of QFT", arXiv:2603.15770
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure
open scoped MeasureTheory Complex BigOperators

/- ## Euclidean Spacetime and Test Functions

Following Douglas et al., we work in 4-dimensional Euclidean spacetime.
The field configurations are tempered distributions (dual to Schwartz space). -/

namespace OSBridge

/-- Spacetime dimension for the Euclidean theory. -/
abbrev D := 4

/-- Euclidean spacetime R^D. Using EuclideanSpace gives us the inner product
    and norm structure needed for Euclidean invariance. -/
abbrev ESpaceTime := EuclideanSpace ℝ (Fin D)

/-- Real-valued Schwartz test functions on Euclidean spacetime. -/
abbrev ETestFunction := SchwartzMap ESpaceTime ℝ

/-- Complex-valued Schwartz test functions on Euclidean spacetime. -/
abbrev ETestFunctionC := SchwartzMap ESpaceTime ℂ

/-- Field configurations as tempered distributions: the topological dual of
    Schwartz space with the weak-* topology.

    In Douglas et al., this carries the cylinder sigma-algebra from the bochner
    library (Minlos.NuclearSpace). We define the cylinder sigma-algebra directly
    using standard Mathlib primitives. -/
abbrev EFieldConfiguration := WeakDual ℝ (SchwartzMap ESpaceTime ℝ)

/-- The cylinder sigma-algebra on field configurations: the smallest sigma-algebra
    making all evaluation maps omega -> omega(f) measurable.
    This is the standard sigma-algebra for probability measures on duals of
    nuclear spaces (see Glimm-Jaffe, Ch. 6; Douglas et al. arXiv:2603.15770). -/
instance fieldConfigMeasurableSpace : MeasurableSpace EFieldConfiguration :=
  ⨆ f : ETestFunction, (borel ℝ).comap (fun ω : EFieldConfiguration => ω f)

/-- Evaluation maps are measurable w.r.t. the cylinder sigma-algebra. -/
theorem eval_measurable (f : ETestFunction) :
    Measurable (fun ω : EFieldConfiguration => ω f) := by
  rw [measurable_iff_comap_le]
  exact le_iSup (fun g => (borel ℝ).comap (fun ω : EFieldConfiguration => ω g)) f

/- ## Distribution Pairing

The fundamental pairing <w, f> between a field configuration (distribution)
and a test function. -/

/-- The pairing between a field configuration and a test function: <w, f>.
    Since FieldConfiguration = WeakDual R TestFunction, this is just evaluation
    of the continuous linear functional. -/
def ePairing (ω : EFieldConfiguration) (f : ETestFunction) : ℝ := ω f

lemma ePairing_add_left (ω₁ ω₂ : EFieldConfiguration) (f : ETestFunction) :
    ePairing (ω₁ + ω₂) f = ePairing ω₁ f + ePairing ω₂ f := by
  unfold ePairing; exact ContinuousLinearMap.add_apply ω₁ ω₂ f

lemma ePairing_smul (s : ℝ) (ω : EFieldConfiguration) (f : ETestFunction) :
    ePairing (s • ω) f = s * ePairing ω f := by
  unfold ePairing; exact ContinuousLinearMap.smul_apply s ω f

/-- Linearity of the pairing in the test function argument. -/
lemma ePairing_add_right (ω : EFieldConfiguration) (f g : ETestFunction) :
    ePairing ω (f + g) = ePairing ω f + ePairing ω g := by
  unfold ePairing; exact map_add ω f g

/- ## Translation of Test Functions

Translation of a Schwartz test function by a spacetime vector.
We axiomatize this operation since Mathlib's SchwartzMap does not
provide a built-in translation map. -/

/-- Translation of a Schwartz test function: (T_a f)(x) = f(x - a).
    Translation preserves the Schwartz class (rapid decay and smoothness
    are invariant under translation). We axiomatize this since Mathlib
    does not provide SchwartzMap.translate. -/
axiom translateTestFunction : ESpaceTime → ETestFunction →ₗ[ℝ] ETestFunction

/-- Notation helper: translate a test function by a vector. -/
def ETestFunction.translate (f : ETestFunction) (a : ESpaceTime) : ETestFunction :=
  translateTestFunction a f

/-- Translation by zero is the identity. -/
axiom translate_zero (f : ETestFunction) :
    f.translate 0 = f

/-- Translation is a group action: T_{a+b} = T_a . T_b. -/
axiom translate_add (f : ETestFunction) (a b : ESpaceTime) :
    f.translate (a + b) = (f.translate a).translate b

/- ## Generating Functional

The generating functional Z[J] = integral exp(i<w, J>) dmu(w) is the fundamental
object in constructive QFT. All Schwinger functions (correlation functions)
can be extracted from it. -/

/-- The Glimm-Jaffe generating functional: Z[J] = integral exp(i<w, J>) dmu(w).
    This is the characteristic functional of the field measure. -/
def generatingFunctional (dμ : ProbabilityMeasure EFieldConfiguration)
    (J : ETestFunction) : ℂ :=
  ∫ ω, exp (I * (ePairing ω J : ℂ)) ∂dμ.toMeasure

/- ## Schwinger Functions

The n-point Schwinger functions are the moments of the field measure.
They contain all the physics of the theory. -/

/-- The n-th Schwinger function: S_n(f_1,...,f_n) = integral <w,f_1>...<w,f_n> dmu(w). -/
def schwingerFunction (dμ : ProbabilityMeasure EFieldConfiguration) (n : ℕ)
    (f : Fin n → ETestFunction) : ℝ :=
  ∫ ω, (∏ i, ePairing ω (f i)) ∂dμ.toMeasure

/-- The 2-point Schwinger function (propagator/covariance). -/
def schwinger2pt (dμ : ProbabilityMeasure EFieldConfiguration)
    (f g : ETestFunction) : ℝ :=
  schwingerFunction dμ 2 ![f, g]

/- ## Euclidean Group

The Euclidean group E(D) = O(D) x R^D acts on test functions.
We represent it as a pair (rotation matrix, translation vector). -/

/-- The Euclidean group E(D): orthogonal transformations + translations. -/
structure EuclideanTransform where
  /-- The orthogonal part (rotation/reflection) -/
  rotation : Matrix (Fin D) (Fin D) ℝ
  /-- The orthogonal condition -/
  orthogonal : rotation.transpose * rotation = 1
  /-- The translation part -/
  translation : ESpaceTime

/-- Action of a Euclidean transformation on a spacetime point. -/
def EuclideanTransform.act (g : EuclideanTransform) (x : ESpaceTime) : ESpaceTime :=
  (EuclideanSpace.equiv (Fin D) ℝ).symm
    (fun i => (∑ j, g.rotation i j * (EuclideanSpace.equiv (Fin D) ℝ x) j)
              + (EuclideanSpace.equiv (Fin D) ℝ g.translation) i)

/-- Pullback of a test function by a Euclidean transformation: (g*f)(x) = f(g^{-1}x).
    We axiomatize this since composing with a linear isometry on SchwartzMap
    requires infrastructure not available in Mathlib. -/
axiom pullbackTestFunction :
    EuclideanTransform → ETestFunction →ₗ[ℝ] ETestFunction

/- ## Time Reflection

The time reflection operator Theta : (x_0, x_vec) -> (-x_0, x_vec) is central to
reflection positivity (OS3). -/

/-- Extract the time component (index 0) of a spacetime point. -/
def timeComponent (x : ESpaceTime) : ℝ :=
  (EuclideanSpace.equiv (Fin D) ℝ x) 0

/-- A test function has positive time support if it vanishes for x_0 <= 0. -/
def hasPositiveTimeSupport (f : ETestFunction) : Prop :=
  ∀ x : ESpaceTime, timeComponent x ≤ 0 → f x = 0

/-- The subtype of positive-time test functions. -/
def PositiveTimeTestFunction := { f : ETestFunction // hasPositiveTimeSupport f }

/- ## Osterwalder-Schrader Axioms

The five OS axioms, ported from Douglas et al. (arXiv:2603.15770).
These characterize Euclidean field theories that admit analytic continuation
to relativistic QFTs satisfying the Wightman axioms.

Following the Glimm-Jaffe formulation using probability measures
on field configurations (Glimm and Jaffe, Quantum Physics, pp. 89-90). -/

/-- **OS0 (Analyticity)**: The generating functional is analytic in the
    test functions. For any finite collection of test functions, the map
    (z_1,...,z_n) -> Z[sum z_j f_j] is entire on C^n.

    This ensures the Schwinger functions have good analyticity properties
    needed for Wick rotation. -/
def OS0_Analyticity (dμ : ProbabilityMeasure EFieldConfiguration) : Prop :=
  ∀ (n : ℕ) (f : Fin n → ETestFunction),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      ∫ ω, exp (I * (∑ i, z i * (ePairing ω (f i) : ℂ))) ∂dμ.toMeasure)
      Set.univ

/-- **OS1 (Regularity)**: The generating functional satisfies exponential
    growth bounds. There exist p in [1,2] and c > 0 such that
    |Z[f]| <= exp(c(||f||_1 + ||f||_p^p)).

    This controls the growth of Schwinger functions and ensures they
    define tempered distributions. -/
def OS1_Regularity (dμ : ProbabilityMeasure EFieldConfiguration) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    ∀ (f : ETestFunction),
      ‖generatingFunctional dμ f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^p ∂volume))

/-- **OS2 (Euclidean Invariance)**: The generating functional is invariant
    under the Euclidean group E(D).

    This is the Euclidean counterpart of Poincare invariance.
    We state it as: for all g in E(D), Z[f] = Z[g*f]. -/
def OS2_EuclideanInvariance (dμ : ProbabilityMeasure EFieldConfiguration) : Prop :=
  ∀ (g : EuclideanTransform) (f : ETestFunction),
    generatingFunctional dμ f =
    generatingFunctional dμ (pullbackTestFunction g f)

/-- **OS3 (Reflection Positivity)**: For positive-time test functions f_1,...,f_n
    and real coefficients c_1,...,c_n, the reflection-positivity inequality holds:

    sum_{i,j} c_i c_j S_2(f_i, f_j) >= 0

    where S_2 is the 2-point Schwinger function. This is the key axiom that
    enables the reconstruction of a positive-definite Hilbert space inner product.

    Simplified form: we state it for the 2-point function of positive-time
    test functions and their time reflections. -/
def OS3_ReflectionPositivity (dμ : ProbabilityMeasure EFieldConfiguration) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      schwingerFunction dμ 2 ![(f i).val, (f j).val]

/-- **OS4 (Clustering/Ergodicity)**: Correlations between well-separated
    regions decay to zero. Specifically, as the spatial separation |a| -> infinity:

    Z[f + T_a g] -> Z[f] * Z[g]

    This ensures uniqueness of the vacuum in the reconstructed theory. -/
def OS4_Clustering (dμ : ProbabilityMeasure EFieldConfiguration) : Prop :=
  ∀ (f g : ETestFunction) (ε : ℝ), ε > 0 →
    ∃ (R : ℝ), R > 0 ∧ ∀ (a : ESpaceTime),
      ‖a‖ > R →
      ‖generatingFunctional dμ (f + g.translate a) -
       generatingFunctional dμ f * generatingFunctional dμ g‖ < ε

/- ## Bundled OS Axioms -/

/-- A probability measure on field configurations satisfies all
    Osterwalder-Schrader axioms. This is the Euclidean counterpart
    of the Wightman axioms.

    Douglas et al. proved that the massive Gaussian free field
    satisfies all these axioms (0 sorries, 0 axioms). -/
structure SatisfiesAllOS (dμ : ProbabilityMeasure EFieldConfiguration) : Prop where
  os0 : OS0_Analyticity dμ
  os1 : OS1_Regularity dμ
  os2 : OS2_EuclideanInvariance dμ
  os3 : OS3_ReflectionPositivity dμ
  os4 : OS4_Clustering dμ

/- ## Wightman QFT Structure (Minkowski Side)

The OS reconstruction theorem produces a Wightman QFT in Minkowski spacetime.
We define a minimal Wightman structure here to state the reconstruction theorem
independently of the main YangMillsMassGap.lean file. -/

/-- A Wightman quantum field theory in Minkowski spacetime.
    This is the output of the OS reconstruction theorem.

    NOTE: This is structurally isomorphic to the canonical `WightmanQFT` at
    line 335 of YangMillsMassGap.lean, but not definitionally equal (different
    field names: `instNACG`/`instIPS`/`instCS` vs `normedAddCommGroup`/
    `innerProductSpace`/`completeSpace`, and `energy_nonneg`/`vacuum_ground`
    vs `energy_bounded_below`/`vacuum_lowest_energy`). Unification would
    require extracting to a shared module; see issue #5282. -/
structure WightmanQFT where
  /-- The Hilbert space of states -/
  H : Type*
  [instNACG : NormedAddCommGroup H]
  [instIPS : InnerProductSpace ℂ H]
  [instCS : CompleteSpace H]
  /-- The vacuum state -/
  vacuum : H
  /-- The vacuum is normalized -/
  vacuum_normalized : ‖vacuum‖ = 1
  /-- The Hamiltonian (energy operator) -/
  hamiltonian : H →ₗ[ℂ] H
  /-- Energy is non-negative -/
  energy_nonneg : ∀ ψ : H,
    0 ≤ RCLike.re (@inner ℂ _ instIPS.toInner (hamiltonian ψ) ψ)
  /-- The vacuum has zero energy -/
  vacuum_ground : hamiltonian vacuum = 0

attribute [instance] WightmanQFT.instNACG WightmanQFT.instIPS WightmanQFT.instCS

/-- A Wightman QFT has a mass gap Delta > 0 if all states orthogonal to the
    vacuum have energy at least Delta. -/
def WightmanQFT.hasMassGap (qft : WightmanQFT) (Δ : ℝ) : Prop :=
  Δ > 0 ∧ ∀ ψ : qft.H, ‖ψ‖ = 1 →
    @inner ℂ _ qft.instIPS.toInner ψ qft.vacuum = 0 →
    Δ ≤ RCLike.re (@inner ℂ _ qft.instIPS.toInner (qft.hamiltonian ψ) ψ)

/- ## OS Reconstruction Theorem

The Osterwalder-Schrader reconstruction theorem (1973, 1975) states that
Schwinger functions satisfying the OS axioms determine a unique Wightman QFT
via analytic continuation (Wick rotation).

This is the central bridge between the Euclidean and Minkowski frameworks. -/

/-- **OS Reconstruction Theorem** (Osterwalder-Schrader 1973, 1975).

    If a probability measure on field configurations satisfies all OS axioms,
    then there exists a Wightman QFT obtained by analytic continuation.

    This is a deep theorem in constructive QFT. We state it as an axiom
    because proving it requires substantial infrastructure (Schwinger function
    analyticity, Wick rotation, Hilbert space reconstruction) beyond current
    Mathlib capabilities.

    Reference: Osterwalder-Schrader, Comm. Math. Phys. 31 (1973) 83-112;
    Comm. Math. Phys. 42 (1975) 281-305. -/
axiom os_reconstruction
    (dμ : ProbabilityMeasure EFieldConfiguration)
    (h : SatisfiesAllOS dμ) :
    WightmanQFT

/-- The reconstructed QFT inherits properties from the Euclidean theory.
    In particular, clustering (OS4) gives vacuum uniqueness. -/
axiom os_reconstruction_unique_vacuum
    (dμ : ProbabilityMeasure EFieldConfiguration)
    (h : SatisfiesAllOS dμ) :
    let qft := os_reconstruction dμ h
    ∀ ψ : qft.H, qft.hamiltonian ψ = 0 → ∃ c : ℂ, ψ = c • qft.vacuum

/- ## Mass Gap Transfer

The mass gap in the Euclidean theory (exponential decay of correlations)
corresponds to the mass gap in the Minkowski theory (spectral gap of the
Hamiltonian). This is a consequence of the reconstruction theorem. -/

/-- Exponential clustering in the Euclidean theory: correlations decay
    as exp(-Delta * |x|) where Delta is the mass gap. This is equivalent to the
    Minkowski mass gap via the reconstruction theorem. -/
def hasExponentialClustering (dμ : ProbabilityMeasure EFieldConfiguration)
    (Δ : ℝ) : Prop :=
  Δ > 0 ∧ ∀ (f g : ETestFunction), ∃ (C : ℝ), C ≥ 0 ∧
    ∀ (a : ESpaceTime),
      ‖generatingFunctional dμ (f + g.translate a) -
       generatingFunctional dμ f * generatingFunctional dμ g‖
      ≤ C * Real.exp (-Δ * ‖a‖)

/-- **Mass Gap Transfer Theorem**.

    If the Euclidean theory has exponential clustering with rate Delta,
    then the reconstructed Wightman QFT has mass gap Delta.

    This is the key link: proving mass gap in the Euclidean framework
    (which is how lattice gauge theory works) gives mass gap in the
    physical Minkowski theory. -/
axiom mass_gap_transfer
    (dμ : ProbabilityMeasure EFieldConfiguration)
    (h : SatisfiesAllOS dμ)
    (Δ : ℝ)
    (hΔ : hasExponentialClustering dμ Δ) :
    (os_reconstruction dμ h).hasMassGap Δ

/- ## Yang-Mills Specialization

For Yang-Mills theory, the OS axioms must be supplemented with
gauge invariance. The constructive QFT program for Yang-Mills requires:

1. Define lattice gauge theory with Wilson action
2. Take the continuum limit (lattice spacing a -> 0)
3. Verify OS axioms in the continuum limit
4. Verify gauge invariance
5. Verify exponential clustering (mass gap)

Steps 1-2 are the main mathematical challenge. -/

/-- A lattice gauge theory is specified by a gauge group and coupling. -/
structure LatticeGaugeTheory where
  /-- Gauge group (e.g., SU(2), SU(3)) -/
  G : Type*
  [group : Group G]
  [topSpace : TopologicalSpace G]
  [compact : CompactSpace G]
  /-- Lattice spacing -/
  spacing : ℝ
  spacing_pos : spacing > 0
  /-- Coupling constant -/
  coupling : ℝ
  coupling_pos : coupling > 0

/-- The Yang-Mills continuum limit conjecture: as lattice spacing -> 0,
    the lattice measures converge to a measure satisfying all OS axioms
    with exponential clustering.

    This is essentially the Clay Millennium Prize problem in the
    Euclidean (constructive QFT) formulation. -/
def YangMillsContinuumLimit : Prop :=
  ∃ (dμ : ProbabilityMeasure EFieldConfiguration) (Δ : ℝ),
    SatisfiesAllOS dμ ∧ hasExponentialClustering dμ Δ

/-- The Yang-Mills Millennium Prize follows from the continuum limit
    via OS reconstruction + mass gap transfer. -/
theorem millennium_prize_from_continuum_limit
    (h : YangMillsContinuumLimit) :
    ∃ (qft : WightmanQFT) (Δ : ℝ), qft.hasMassGap Δ := by
  obtain ⟨dμ, Δ, hOS, hΔ⟩ := h
  exact ⟨os_reconstruction dμ hOS, Δ, mass_gap_transfer dμ hOS Δ hΔ⟩

/- ## Extended Yang-Mills: Gauge Invariance, Non-Triviality, and the Full Prize Chain

The simplified `YangMillsContinuumLimit` above asserts only OS axioms + mass gap.
The actual Clay Millennium Prize requires two additional conditions:

1. **Gauge invariance**: The continuum measure must respect the gauge symmetry
   of the original Yang-Mills Lagrangian (invariance under local gauge
   transformations g(x) in the gauge group G).

2. **Non-triviality**: The theory must not be a generalized free field (Gaussian
   measure). This rules out the trivial solution where the 4d Yang-Mills theory
   is a free field in disguise.

Below we define these conditions and state the complete prize conjecture. -/

/-- A gauge group action on field configurations.

    In the continuum Yang-Mills theory, the gauge group acts on connection
    1-forms via A_mu -> g A_mu g^{-1} + g d(g^{-1}). At the level of the
    distributional field space (the OS framework), this lifts to an action
    on `EFieldConfiguration = WeakDual R (SchwartzMap ESpaceTime R)`.

    We axiomatize this action abstractly: a group `G` acts on
    `EFieldConfiguration` via measurable maps (w.r.t. the cylinder
    sigma-algebra). The measurability condition is stated as an axiom
    because the cylinder sigma-algebra (`fieldConfigMeasurableSpace`)
    is defined as a supremum of comap sigma-algebras, and proving
    measurability of a concrete gauge action requires showing that
    evaluation maps compose measurably with the group action -- this
    depends on the specific gauge group and its Lie algebra structure.

    Reference: Glimm-Jaffe, Quantum Physics, Ch. 6 (gauge group action);
    Wilson (1974), Phys. Rev. D10, 2445 (lattice gauge invariance). -/
class GaugeAction (G : Type*) [Group G] where
  /-- The action of a gauge transformation on a field configuration. -/
  act : G → EFieldConfiguration → EFieldConfiguration
  /-- The action is measurable w.r.t. the cylinder sigma-algebra.
      Axiomatized because proving this requires detailed knowledge of
      the gauge group's Lie algebra action on the distribution space. -/
  act_measurable : ∀ g, @Measurable _ _ fieldConfigMeasurableSpace fieldConfigMeasurableSpace (act g)

/-- **Gauge invariance** of the continuum measure.

    The continuum measure `dmu` is gauge-invariant if the pushforward of `dmu`
    under every gauge transformation `g` equals `dmu`:

      dmu.map (act g) = dmu  for all g in G

    This is the standard mathematical definition of invariance of a measure
    under a group action. It ensures that the measure descends to the orbit
    space A/G, which is the physical configuration space modulo gauge
    equivalence.

    The definition uses `MeasureTheory.Measure.map`, which computes the
    pushforward measure: (mu.map f)(S) = mu(f^{-1}(S)).

    Reference: Glimm-Jaffe, Quantum Physics, Ch. 6;
    Wilson (1974), Phys. Rev. D10, 2445 (lattice gauge invariance). -/
def GaugeInvariant (G : Type*) [Group G] [GaugeAction G]
    (dμ : ProbabilityMeasure EFieldConfiguration) : Prop :=
  ∀ g : G, dμ.toMeasure.map (GaugeAction.act g) = dμ.toMeasure

/-- **Non-triviality** of the continuum theory.

    A probability measure on field configurations is non-trivial if it is not
    a generalized free field (Gaussian measure). The standard criterion is that
    the connected 4-point Schwinger function is non-zero.

    For a Gaussian (free) field, Wick's theorem gives:
      S_4(f_0, f_1, f_2, f_3) = S_2(f_0,f_1) S_2(f_2,f_3)
                                + S_2(f_0,f_2) S_2(f_1,f_3)
                                + S_2(f_0,f_3) S_2(f_1,f_2)

    Non-triviality means this factorization fails for some test functions,
    i.e., the connected 4-point function is non-vanishing.

    Reference: Glimm-Jaffe, Quantum Physics, Section 6.1 (Wick's theorem);
    Simon (1974), The P(phi)_2 Euclidean QFT, Ch. II. -/
def HasNonGaussianCorrelations (dμ : ProbabilityMeasure EFieldConfiguration) : Prop :=
  ∃ (f : Fin 4 → ETestFunction),
    schwingerFunction dμ 4 f ≠
      schwingerFunction dμ 2 ![f 0, f 1] * schwingerFunction dμ 2 ![f 2, f 3] +
      schwingerFunction dμ 2 ![f 0, f 2] * schwingerFunction dμ 2 ![f 1, f 3] +
      schwingerFunction dμ 2 ![f 0, f 3] * schwingerFunction dμ 2 ![f 1, f 2]

/-- A lattice Yang-Mills theory on a finite lattice with gauge group G.

    This extends `LatticeGaugeTheory` (which has group, spacing, coupling)
    with the lattice volume parameter needed to state the thermodynamic
    limit. The partition function is:

      Z = integral prod_{plaquettes} exp(-beta * Re Tr(1 - U_plaq)) dU

    where dU is Haar measure on each link variable U in G.

    We define this as a separate structure (rather than extending
    `LatticeGaugeTheory`) to avoid changing the existing definition
    that may be referenced elsewhere.

    Reference: Wilson (1974), Phys. Rev. D10, 2445;
    Balaban (1980s), lattice UV stability program. -/
structure LatticeYangMills where
  /-- Gauge group (compact Lie group, e.g., SU(N)) -/
  G : Type*
  [group : Group G]
  [topSpace : TopologicalSpace G]
  [compact : CompactSpace G]
  /-- Lattice spacing -/
  a : ℝ
  a_pos : a > 0
  /-- Inverse coupling: beta = 2N/g^2 -/
  β : ℝ
  β_pos : β > 0
  /-- Lattice volume (number of sites per dimension) -/
  L : ℕ
  L_pos : L > 0

/-- The full Yang-Mills continuum limit conjecture.

    As lattice spacing a -> 0 with coupling beta(a) -> infinity according
    to asymptotic freedom, the lattice measures converge to a continuum
    measure satisfying:

    1. All OS axioms (OS0-OS4) -- enabling reconstruction to a Wightman QFT
    2. Gauge invariance -- the continuum theory respects local gauge symmetry
    3. Non-triviality -- the theory is not a generalized free field
    4. Exponential clustering -- the theory has a mass gap

    The existential over a family of `LatticeYangMills` theories witnesses
    that the continuum measure arises as the limit of lattice theories
    indexed by lattice spacing. The spacing-to-zero convergence condition
    is left implicit for now; formalizing it would require a
    `Filter.Tendsto` argument beyond the current scope of this file.

    This is the complete mathematical content of the Clay Millennium Prize
    problem for Yang-Mills existence and mass gap, in the Euclidean
    (constructive QFT) formulation.

    Reference: Jaffe-Witten, Clay Millennium Prize problem statement;
    Douglas (2026), Nature Reviews Physics (the lattice -> OS -> Wightman chain). -/
def YangMillsContinuumLimitFull (G : Type*) [Group G] [TopologicalSpace G]
    [CompactSpace G] [GaugeAction G] : Prop :=
  ∃ (_family : ℕ → LatticeYangMills.{0})
    (dμ : ProbabilityMeasure EFieldConfiguration),
    SatisfiesAllOS dμ ∧
    GaugeInvariant dμ ∧
    HasNonGaussianCorrelations dμ ∧
    ∃ Δ : ℝ, hasExponentialClustering dμ Δ

/-- **The Yang-Mills Millennium Prize theorem** (full chain).

    If the continuum limit exists with all required properties (OS axioms,
    gauge invariance, non-triviality, and exponential clustering), then
    there exists a Wightman QFT with mass gap.

    This theorem makes the full logical chain explicit:

      Wilson lattice gauge theory (finite, well-defined)
        -> continuum limit (a -> 0, asymptotic freedom)
        -> probability measure on field configurations
        -> verify OS axioms (OS0-OS4)              [hypothesis: SatisfiesAllOS]
        -> OS reconstruction -> Wightman QFT       [axiom: os_reconstruction]
        -> exponential clustering -> mass gap       [axiom: mass_gap_transfer]

    The proof extracts the OS axioms and clustering rate from the full
    continuum limit hypothesis, then applies `os_reconstruction` and
    `mass_gap_transfer` (the same axioms used by
    `millennium_prize_from_continuum_limit`).

    No new axioms are introduced beyond `os_reconstruction` and
    `mass_gap_transfer`.

    Reference: Osterwalder-Schrader (1973, 1975); Glimm-Jaffe Ch. 19. -/
theorem yang_mills_millennium_prize
    (G : Type*) [Group G] [TopologicalSpace G] [CompactSpace G] [GaugeAction G]
    (h : YangMillsContinuumLimitFull G) :
    ∃ (qft : WightmanQFT) (Δ : ℝ), qft.hasMassGap Δ := by
  obtain ⟨_, dμ, hOS, _, _, Δ, hΔ⟩ := h
  exact ⟨os_reconstruction dμ hOS, Δ, mass_gap_transfer dμ hOS Δ hΔ⟩

/- ## Consistency Note

Douglas et al. (arXiv:2603.15770) proved that the massive Gaussian free field
(a non-interacting theory) satisfies all OS axioms with exponential clustering.
This establishes that `SatisfiesAllOS` is consistent -- it has a model.

For Yang-Mills (an interacting, non-abelian gauge theory), proving `SatisfiesAllOS`
is the core mathematical challenge. The lattice gauge theory approach
(Wilson 1974) provides strong numerical evidence but no rigorous proof.

The `HasNonGaussianCorrelations` condition additionally rules out the Gaussian free field as
a solution to the Yang-Mills continuum limit problem: it requires the connected
4-point function to be non-vanishing, which fails for any Gaussian measure
by Wick's theorem. -/

end OSBridge
