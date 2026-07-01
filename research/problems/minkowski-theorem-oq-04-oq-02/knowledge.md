# Knowledge Base: minkowski-theorem-oq-04-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: Blichfeldt's theorem for an arbitrary full-rank ℤ-lattice Λ ⊆ ℝⁿ with the covolume
threshold vol(S) > k·covol(Λ), and the corresponding general-lattice Minkowski convex body
theorem.

---

## Insights

- **The parent already contains the lattice-parametric engine.**
  `Proofs/MinkowskiTheoremOQ04.lean` proves `blichfeldt_general_lattice` (verified, 0-axiom):
  for a basis `b`, `(k:ℝ≥0∞) * volume (ZSpan.fundamentalDomain b) < volume s` yields k+1
  points with pairwise differences in `span ℤ (range b)`. The hard analytic step (the
  covering-count integral identity `volume_eq_setLIntegral_indicator_tsum_lattice`) is also
  already general. So the "open" child theorem, in its raw ℝ≥0∞ form, was in fact done.

- **The genuine gap = the covolume-facing statement.** The parent's threshold uses the raw
  ℝ≥0∞ fundamental-domain volume; the geometry-of-numbers standard (Cassels/Siegel) uses the
  real covolume `ZLattice.covolume`. Bridging them is the new content, plus the general-lattice
  Minkowski convex body theorem (parent has Minkowski only for ℤⁿ).

- **Covolume bridge (Mathlib v4.26.0).**
  `ZLattice.covolume L μ = μ.real F` (`ZLattice.covolume_eq_measure_fundamentalDomain`) for any
  `IsAddFundamentalDomain L F μ`. For `L = span ℤ (range b)` use `ZSpan.isAddFundamentalDomain b
  volume` (note: the *Submodule* version, not the `.toAddSubgroup` primed one, matches
  covolume's `L : Submodule ℤ E`). `μ.real F = (μ F).toReal` is `measureReal_def`. Instances
  `DiscreteTopology (span ℤ (range b))` and `IsZLattice ℝ (span ℤ (range b))`
  (`instIsZLatticeRealSpan`) are found automatically for `[Finite ι]`.

- **Finiteness of the fundamental-domain volume** is the one analytic fact needed:
  `(Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded b)).ne`. It makes
  `ENNReal.ofReal ∘ toReal` the identity on `volume F`, giving
  `(k:ℝ≥0∞)·volume F = ENNReal.ofReal (k·covol Λ)`.

- **Threshold phrasing.** Stating the hypothesis as `ENNReal.ofReal (k·covol Λ) < volume s`
  (rather than a real inequality with `(volume s).toReal`) is robust: when `volume s = ⊤` the
  hypothesis is automatically satisfied and the theorem still holds, with no extra finiteness
  assumption on S.

- **Minkowski half-scaling is lattice-agnostic.** Scaling `T = (1/2)·S` acts on S, not Λ, so
  the parent's ℤⁿ proof (`minkowski_from_blichfeldt`) transfers verbatim: measurability via the
  doubling-map preimage, `Measure.addHaar_smul` + `(2⁻¹)ⁿ·2ⁿ = 1` ENNReal arithmetic, with the
  constant `1` (= covol ℤⁿ) replaced by `volume (ZSpan.fundamentalDomain b)`.

---

## Dead Ends

- Approach 2 (pull back to ℤⁿ via the basis linear map + Jacobian) was unnecessary: the parent's
  already-general Move A made the direct covolume bridge far cheaper.
