# Research State: hurwitz-theorem-wip-01

## Current State

**Phase**: BLOCKED (6 iterations, single-step Mathlib blocker; pin-gated)
**Path**: full
**Since**: 2026-05-25T07:22:00Z
**Iteration**: 6

## Current Focus

Iteration 6 (BLOCKED): re-confirmed the blocker stands and identified the
**dependency-pin gate** the prior five sessions missed. The project does not
track Mathlib master — `proofs/lake-manifest.json` pins mathlib4 to release
**v4.26.0** (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). v4.26.0 has no
real-Clifford structure classification, no Frobenius-for-real-division-algebras
theorem, and no parallelogram-identity-from-NormedDivisionRing. So the S3–S5
"wait for Mathlib master" unblock plan was necessary but **not sufficient**:
even if crit-F / crit-PI land upstream, this project cannot compile against
them until someone bumps the Mathlib pin to a release containing them. This
explains why five sessions of "waiting" produced zero movement — the project
isn't tracking the branch they were watching.

State verified this session: 2 genuine open sorries remain
(`HurwitzTheorem.lean:1937` even n∉{2,4,8}; `HurwitzOnlyIf.lean:111`
`hurwitz_only_if_ring`), 0 axioms across all three Hurwitz files,
`HurwitzTheoremOQ04.lean` has 0 genuine sorries (its "sorry" mentions are
docstring annotations on already-proved lemmas). All linear-algebra
infrastructure for the impossibility argument is in place; the sole gap is
the Clifford structure theorem (~1000 lines of Mathlib additions).

**Iteration 5 (prior, PARK)**: second Mathlib master re-survey, ~9 hours after
S4. **No movement** on either crit-F (Frobenius for real division algebras) or
crit-IPS (InnerProductSpace from NormedDivisionRing). Mathlib commits to
`Mathlib/LinearAlgebra/CliffordAlgebra/` since 2026-04-15 are all chore-only
(documented in S5 report). The single missing theorem from S4 stands.

**S5 refinement**: `Mathlib/Analysis/InnerProductSpace/OfNorm.lean` provides
`InnerProductSpace.ofNorm` — an inner product structure on a normed space
**conditional on the parallelogram identity**
`‖x + y‖² + ‖x - y‖² = 2 (‖x‖² + ‖y‖²)`. This refactors crit-IPS into a
**three-step bridge**: (a) prove parallelogram identity for any finite-dim
NormedDivisionRing over ℝ; (b) apply `InnerProductSpace.ofNorm`;
(c) execute the option-B coordinate construction. Step (b) is now cheap;
step (a) is the new bottleneck and is itself essentially equivalent to
Frobenius — so the refactor does not shorten the path, but it pins down
**where** the Frobenius-style argument has to live.

The remaining blocker continues to collapse to **a single Mathlib-level
missing theorem**: the classical Frobenius theorem for real division
algebras (every finite-dim associative division algebra over ℝ has
`finrank ∈ {1, 2, 4}`, i.e., is ℝ, ℂ, or ℍ). With Wedderburn–Artin already
available, Frobenius alone suffices to pin down the `D` in the
`Cl(0, n-1) ≅ M_d(D)` decomposition, which closes both open sorries
(`HurwitzTheorem.lean:1937`, `HurwitzOnlyIf.lean:111`).

## Active Approach

**BLOCKED — recommend pool status `blocked` and move on.** Six sessions have
converged on the same single-step Mathlib blocker, which is additionally
pin-gated (project tracks mathlib4 v4.26.0, not master). Per the researcher
STUCK rule (3+ sessions on the same sorry → flag BLOCKED), this problem should
be removed from the active claim pool until the two-part unblock condition
below is met. The candidate-pool entry currently reads `available` even though
the problem JSON already reads `blocked`; aligning the pool to `blocked` stops
the depth-first claimer from repeatedly serving this RICH problem to
researchers who can only re-confirm the blocker.

## Attempt Count

- Total attempts: 6
- Approaches tried:
  1. (S2, prior session) OBSERVE / SURVEY: enumerate proved infrastructure,
     classify what's left, identify Mathlib gap precisely.
  2. (S3, prior session) Re-confirm BLOCKED + correct S2 cost estimate
     for option B (refactor): the "~80 lines" estimate misjudged the
     bridge construction.
  3. (S4, prior session) Mathlib re-survey: discovered Wedderburn–Artin
     **already landed**; pruned blocker list; sharpened the unblock
     criteria to a two-bullet wishlist (Frobenius theorem OR
     `InnerProductSpace`-from-`NormedDivisionRing`).
  4. (S5, prior session) Second Mathlib re-survey (~9h after S4): no
     movement on crit-F or crit-IPS; CliffordAlgebra/ commits all
     chore-only since 2026-04-15. Discovered
     `Mathlib.Analysis.InnerProductSpace.OfNorm.InnerProductSpace.ofNorm`,
     which refactors crit-IPS into a three-step bridge with a cheap
     middle step — the new bottleneck is the parallelogram identity for
     finite-dim NormedDivisionRing, which is itself Frobenius in disguise.
  5. (S6, this session) Verified current file state (2 open sorries, 0
     axioms) and identified the **dependency-pin gate**: project pins
     mathlib4 v4.26.0 (lake-manifest), so it does not see master. Unblock
     now requires BOTH an upstream theorem AND a Mathlib pin bump.
     Recommend pool status `blocked`; declined the n=6/n=10 small-case
     route (enumeration theater that saturates per S2/S5 insights and still
     needs the Wedderburn structure of Cl(0,5)/Cl(0,9)).

## Blockers (revised after S5)

1. **Frobenius theorem for real division algebras** — not in Mathlib master
   as of 2026-05-08T16:30Z (verified via `gh api git/trees`). Tree-recursive
   search for `Frobenius`-named files yields only Galois Frobenius
   (`Mathlib/RingTheory/Frobenius.lean`), char-p endomorphisms
   (`Mathlib/Algebra/CharP/Frobenius.lean`), Witt-vector Frobenius
   (`Mathlib/RingTheory/WittVector/{Frobenius,FrobeniusFractionField}.lean`),
   and the number-theoretic `FrobeniusNumber.lean` — none give the
   real-division-algebra theorem.
2. **Parallelogram identity from NormedDivisionRing**
   (refines former crit-IPS) — not in Mathlib. With this in hand,
   `Mathlib.Analysis.InnerProductSpace.OfNorm.InnerProductSpace.ofNorm`
   immediately provides the InnerProductSpace structure needed for
   option B. Without it, the polarization argument has no starting point.
3. **Bott periodicity for real Clifford algebras** — still not in Mathlib;
   commits to `Mathlib/LinearAlgebra/CliffordAlgebra/` since 2026-04-15
   are all chore-only (set_option cleanup, erw removal, algebraMap export,
   docstring fixes — no structural content).

(Removed from prior list: "Artin-Wedderburn for real semisimple algebras" —
**now available** in `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`.)

## Next Action

1. **(option D, current)** Wait for Mathlib upstream. Specifically watch for
   any of:
   - A theorem with conclusion `finrank ℝ D ∈ ({1, 2, 4} : Set ℕ)` for finite-
     dim associative division algebras.
   - An `InnerProductSpace ℝ A` instance derivable from `NormedDivisionRing A`
     and `FiniteDimensional ℝ A`.
   - Any new file under `Mathlib/LinearAlgebra/CliffordAlgebra/` named
     `Periodicity` or `RealClassification`.

2. **(option C, NEW)** Open a Mathlib RFC / draft PR proposing
   `frobenius_theorem_real_division_ring`. With the Wedderburn–Artin API
   now present, this is the *single* missing piece for completing Hurwitz.
   Estimated ~300-500 lines via the classical imaginary-subspace argument.
   References: arXiv:2405.01876 (Frobenius theorem formalized in Coq, May
   2024 — natural source for translation).

3. **(option A, deferred)** Small-case decomposition for n=6, 10. Cost
   reduced from ~400 to ~250 lines/case using the new Wedderburn–Artin
   API; still leaves the open sorry's general case unhandled and requires
   ad-hoc identification of `D` for each `Cl(0, 2k-1)`.

4. **(option B, deferred)** Algebra-level refactor of
   `HurwitzOnlyIf.hurwitz_only_if_ring`. Still blocked on the
   `InnerProductSpace`-from-`NormedDivisionRing` construction.

5. **(do NOT)** Submit to Aristotle. Both sorries are OPEN (genuine missing
   infrastructure), not routine lemmas.

## Unblock Criteria (concrete, revised after S5)

Promote phase from PARK back to ACT when **any** of the following lands
in mathlib4 master:

- **(crit-F)** A theorem in `Mathlib.Algebra.*` or
  `Mathlib.Analysis.NormedSpace.*` with conclusion
  `∀ D : Type*, [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D] →
   finrank ℝ D ∈ ({1, 2, 4} : Set ℕ)` (or equivalent: an
  `AlgEquiv` to one of `ℝ`, `ℂ`, `Quaternion ℝ`).
- **(crit-PI, refines former crit-IPS)** A theorem proving the
  parallelogram identity for any finite-dim `NormedDivisionRing` over `ℝ`:
  `∀ A : Type*, [NormedDivisionRing A] [NormedAlgebra ℝ A] [Module.Finite ℝ A]
   ∀ x y : A, ‖x + y‖^2 + ‖x - y‖^2 = 2 * (‖x‖^2 + ‖y‖^2)`.
  Mathlib already has the second half of the bridge:
  `Mathlib.Analysis.InnerProductSpace.OfNorm.InnerProductSpace.ofNorm`
  promotes any norm satisfying parallelogram to an inner product. So
  crit-PI + `ofNorm` gives a complete option-B chain.
- **(crit-IPS, original)** A direct `InnerProductSpace ℝ A` instance /
  theorem derivable from `NormedDivisionRing A` plus `FiniteDimensional ℝ A`
  (the imaginary-subspace polarization construction). Subsumed by crit-PI
  via `ofNorm`, but still useful if a contributor takes the direct route.

Any one suffices: `crit-F` + already-available Wedderburn–Artin closes the
sorry directly; `crit-PI` (or equivalently `crit-IPS`) enables the option-B
refactor.

- **(crit-PIN, S6)** **Necessary in addition to any of the above.** The
  project pins mathlib4 to release **v4.26.0** in
  `proofs/lake-manifest.json` (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
  inputRev `v4.26.0`). A theorem landing in Mathlib *master* does not unblock
  this project until the pin is bumped to a tagged release that contains it.
  So the real trigger is: (crit-F ∨ crit-PI ∨ crit-IPS) lands in a Mathlib
  release **AND** this repo bumps its Mathlib pin to ≥ that release. The pin
  bump is an infrastructure/tooling change, not a researcher action — track it
  separately (it may carry its own downstream breakage to fix across the
  proof corpus).

**Note on crit-PI**: the parallelogram identity for any finite-dim NDR over
ℝ is **essentially equivalent** to the conclusion we want (it implies the
norm comes from an inner product, which together with norm-multiplicativity
forces dim ∈ {1, 2, 4} via Frobenius). So crit-PI is not strictly weaker
than crit-F — it is a re-statement that pins down the *Mathlib filename*
(`InnerProductSpace/OfNorm.lean` is the natural home) rather than the
mathematical content. Useful for any future Mathlib contribution.

## References

- `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean` — **landed**;
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F R` is the
  workhorse for option A and for any ad-hoc structural argument on
  `Cl(0, n-1)`.
- `Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean` — sibling file with
  the algebraically-closed-field specialization (over ℂ).
- `Mathlib/Analysis/InnerProductSpace/OfNorm.lean` — **available**;
  `InnerProductSpace.ofNorm` constructs an inner product from any norm
  satisfying the parallelogram identity. New (S5) intermediate stop on
  the option-B chain; halves the work between NormedDivisionRing and
  NSquareIdentity.
- `Mathlib/LinearAlgebra/CliffordAlgebra/{Basic,Equivs,...}` — universal
  property and conjugation only; **no** structural classification.
- arXiv:2405.01876 — Frobenius theorem formalization (Coq, 2024); reference
  for a future Mathlib contribution.
- `proofs/Proofs/HurwitzTheorem.lean:1937` — the open sorry (even
  n ∉ {2, 4, 8}).
- `proofs/Proofs/HurwitzOnlyIf.lean:111` — parallel open sorry
  (`hurwitz_only_if_ring`).
