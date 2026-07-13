# Problem: Bochner generalization of `intervalIntegral_swap`

## Statement

### Plain Language

The parent gallery entry `greens-theorem-oq-01-oq-01-oq-02`
(`Proofs/GreensTheoremOQ01OQ01OQ02.lean`) proves three real-valued
versions of an iterated interval-integral Fubini lemma:

```
intervalIntegral_swap_of_le        -- ordered case (a ≤ b, c ≤ d)
intervalIntegral_swap              -- general case (any orderings, sign-flip reduction)
intervalIntegral_swap_of_continuous -- continuous case (no integrability hypothesis)
```

all stated for `f : ℝ → ℝ → ℝ`.

The open question (extracted from the parent's "Future Work" /
seeker pool note) asks:

> Do these lemmas extend cleanly to **Bochner-valued** interval
> integrals — that is, with integrand
>   `f : ℝ → ℝ → E`
> for `E` a Banach space, so that `∫ x in a..b, f x : E` is the
> Bochner integral?

The pool synopsis (`.lean/state/candidate-pool.json` candidate
note) hints at the expected answer:

> "Mathlib's `MeasureTheory.integral_integral_swap` does
>  generalize to Bochner int…"

So the goal is to (i) confirm that hint with a precise Mathlib
audit, (ii) classify which steps in the parent proof are
codomain-agnostic and which are not, (iii) decide whether the
existing real-valued proof script ports verbatim or requires
adjustments (e.g. `linarith → abel`).

### Formal Statement

We seek Lean statements of the form:

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem intervalIntegral_swap_of_le {f : ℝ → ℝ → E}
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := …

theorem intervalIntegral_swap {f : ℝ → ℝ → E} … : … := …

theorem intervalIntegral_swap_of_continuous {f : ℝ → ℝ → E}
    (a b c d : ℝ) (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := …
```

each provable from the same Mathlib lemmas as the parent (see
§ "Mathlib API audit" in `knowledge.md`), with the only adjustment
being `linarith → abel` in the 4-case sign analysis of
`intervalIntegral_swap` (since `linarith` does not act on a
general additive group `E`).

## Why It Matters

1. **Mathlib reusability.** A real-valued `intervalIntegral.swap`
   is already not in Mathlib (per parent finding); a
   Bochner-valued version is even more reusable — vector-field
   line integrals, complex-valued contour integrals, and
   Banach-valued PDE/probability work all need iterated interval
   integrals over Banach codomains.
2. **Proof economy.** If the parent's proof script ports
   essentially verbatim (modulo `linarith → abel`), this is a
   genuine "free" generalization: ~230 lines of Bochner-valued
   `intervalIntegral` Fubini for one tactic substitution. That is
   a strong signal that the parent's lemma is in the right place
   in the Mathlib hierarchy.
3. **Unblocks Banach-valued Green / Stokes.** Several open Green
   variants in the gallery (`greens-theorem-oq-02-oq-02`,
   `greens-theorem-oq-02-oq-04`, etc.) state versions for
   complex-valued or vector-valued planar fields. Each currently
   carries an `hFubini` axiom that this lemma would discharge in
   the Banach setting.

## Decomposition

- **S1 (this iteration, OBSERVE).** Audit Mathlib's
  `MeasureTheory.integral_integral_swap` and the
  `intervalIntegral` API for codomain genericity. Identify the
  one tactic substitution needed and confirm the rest of the
  proof script is codomain-agnostic. **No Lean changes.**
- **S2 (next, SCAFFOLD).** Create
  `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` with the
  Bochner-valued statements as `theorem … := by sorry` plus the
  ordered-case proof actually filled in (smallest closeable
  version). Companion file `…OQ03Aristotle.lean` for the routine
  side-lemmas (e.g. `flip_bounds`, `neg_outside` lifted to `E`).
- **S3 (after S2 build-verifies).** Port the general 4-case
  proof, replacing `linarith` with `abel`. Discharge the
  continuous-case theorem.
- **S4 (final).** Gallery entry (`src/data/proofs/<slug>/`) and
  Mathlib-contribution discussion in the docstring.

## References

- Parent proof: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean`
  (231 lines, 0 sorries, 0 axioms, status: `verified`).
- Grandparent finding: `proofs/Proofs/GreensTheoremOQ01OQ01.lean`
  identified the absence of `intervalIntegral_swap` from Mathlib
  as a "future-work" open question that the parent then resolved
  for `ℝ`-valued integrands.
- Mathlib reference: `MeasureTheory.integral_integral_swap` in
  `Mathlib.MeasureTheory.Integral.Prod`.
