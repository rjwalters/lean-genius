# Research State: hurwitz-theorem-wip-01

## Current State

**Phase**: PARK (still BLOCKED, but with a sharper, one-step blocker)
**Path**: full
**Since**: 2026-05-08T07:30:00Z
**Iteration**: 4

## Current Focus

Iteration 4 (PARK): re-survey Mathlib master for upstream movement. **Important
correction**: Wedderburn–Artin for general rings (and finite-dim algebras over
an arbitrary base ring) **is now in Mathlib** as
`Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean` (Junyan Xu, 2025). Prior
state.md / JSON listed Artin-Wedderburn as a primary blocker; that bullet is
no longer accurate.

The remaining blocker collapses to **a single Mathlib-level missing theorem**:
the **classical Frobenius theorem for real division algebras** (every
finite-dimensional associative division algebra over ℝ has `finrank ∈ {1, 2, 4}`,
i.e., is ℝ, ℂ, or ℍ). With Wedderburn–Artin already available, Frobenius
alone suffices to pin down the `D` in the `Cl(0, n-1) ≅ M_d(D)` decomposition,
which closes both open sorries (`HurwitzTheorem.lean:1937`,
`HurwitzOnlyIf.lean:111`).

## Active Approach

**Wait** — until Mathlib gains a Frobenius-for-real-division-algebras theorem
or an InnerProductSpace-from-NormedDivisionRing construction. See "Unblock
Criteria" for concrete trigger conditions.

## Attempt Count

- Total attempts: 4
- Approaches tried:
  1. (S2, prior session) OBSERVE / SURVEY: enumerate proved infrastructure,
     classify what's left, identify Mathlib gap precisely.
  2. (S3, prior session) Re-confirm BLOCKED + correct S2 cost estimate
     for option B (refactor): the "~80 lines" estimate misjudged the
     bridge construction.
  3. (S4, this session) Mathlib re-survey: discovered Wedderburn–Artin
     **already landed**; pruned blocker list; sharpened the unblock
     criteria to a two-bullet wishlist (Frobenius theorem OR
     `InnerProductSpace`-from-`NormedDivisionRing`).

## Blockers (revised after S4)

1. **Frobenius theorem for real division algebras** — not in Mathlib v4.26.0.
   The `Frobenius`-named files cover Galois-element Frobenius, char-p ring
   endomorphisms, and Witt-vector Frobenius — none give the
   real-division-algebra theorem.
2. **InnerProductSpace from NormedDivisionRing** — not in Mathlib (the
   imaginary-subspace polarization construction is absent).
3. **Bott periodicity for real Clifford algebras** — still not in Mathlib;
   most recent `Mathlib/LinearAlgebra/CliffordAlgebra/` change is
   2026-05-01 (chore-only).

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

## Unblock Criteria (concrete, revised)

Promote phase from PARK back to ACT when **either** of the following lands
in mathlib4 master:

- **(crit-F)** A theorem in `Mathlib.Algebra.*` or
  `Mathlib.Analysis.NormedSpace.*` with conclusion
  `∀ D : Type*, [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D] →
   finrank ℝ D ∈ ({1, 2, 4} : Set ℕ)` (or equivalent: an
  `AlgEquiv` to one of `ℝ`, `ℂ`, `Quaternion ℝ`).
- **(crit-IPS)** An `InnerProductSpace ℝ A` instance / theorem derivable from
  `NormedDivisionRing A` plus `FiniteDimensional ℝ A` (the imaginary-subspace
  polarization construction).

Either suffices: `crit-F` + already-available Wedderburn–Artin closes the
sorry directly; `crit-IPS` enables the option-B refactor.

## References

- `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean` — **landed**;
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F R` is the
  workhorse for option A and for any ad-hoc structural argument on
  `Cl(0, n-1)`.
- `Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean` — sibling file with
  the algebraically-closed-field specialization (over ℂ).
- `Mathlib/LinearAlgebra/CliffordAlgebra/{Basic,Equivs,...}` — universal
  property and conjugation only; **no** structural classification.
- arXiv:2405.01876 — Frobenius theorem formalization (Coq, 2024); reference
  for a future Mathlib contribution.
- `proofs/Proofs/HurwitzTheorem.lean:1937` — the open sorry (even
  n ∉ {2, 4, 8}).
- `proofs/Proofs/HurwitzOnlyIf.lean:111` — parallel open sorry
  (`hurwitz_only_if_ring`).
