# Problem: `LocallyIntegrable` interface for `intervalIntegral_swap`

## Statement

### Plain Language

The parent gallery entry `greens-theorem-oq-01-oq-01-oq-02`
(`Proofs/GreensTheoremOQ01OQ01OQ02.lean`, verified, 0 sorries,
0 axioms) proves three real-valued versions of an iterated
interval-integral Fubini lemma:

```
intervalIntegral_swap_of_le        -- a ≤ b, c ≤ d
intervalIntegral_swap              -- any orderings, sign-flip reduction
intervalIntegral_swap_of_continuous -- continuous integrand (no integrability hyp.)
```

The general `intervalIntegral_swap` requires a somewhat awkward
integrability hypothesis:

```lean
(hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
  ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d))))
```

i.e. integrability against the *product of restricted* one-dim
volumes on the unordered intervals `uIcc a b` and `uIcc c d`.

The seeker-extracted open question asks:

> Can the integrability hypothesis be weakened from
> `uIcc a b × uIcc c d` to local integrability
> (`LocallyIntegrable`), similar to how Fubini-Tonelli handles
> σ-finite measures?

### Reframing the question

As literally stated this is **mathematically backwards**:

- `LocallyIntegrable f volume` (on ℝ²) means: every point has an
  open neighborhood on which `f` is integrable. Equivalently
  (Mathlib): `IntegrableOn f K volume` for **every** compact
  `K ⊆ ℝ²`.
- The parent's hypothesis asserts integrability on **one**
  particular compact rectangle `uIcc a b × uIcc c d`.

Therefore `LocallyIntegrable f volume → parent hypothesis` (just
specialize to the rectangle), but **not** conversely.
`LocallyIntegrable` is strictly **stronger**, not weaker, than
the parent's compact-rectangle hypothesis.

The intent behind the seeker question, however, is clear and
useful: provide a **user-interface wrapper** that takes the
natural global condition `LocallyIntegrable f volume` and
discharges the awkward `(volume.restrict A).prod
(volume.restrict B)` form internally. This is analogous to
sibling OQ-03 (Bochner generalization), which produces a "free"
codomain-generic wrapper around the parent.

### Formal Statement (S2 target)

We seek a Lean wrapper of the form:

```lean
theorem intervalIntegral_swap_of_locallyIntegrable {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_loc : LocallyIntegrable (fun p : ℝ × ℝ => f p.1 p.2) volume) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply intervalIntegral_swap a b c d hf_meas
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (uIcc a b ×ˢ uIcc c d) volume :=
    hf_loc.integrableOn_isCompact hcpt
  rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
```

This is **the same proof script** as the parent's continuous
case, with `hf.continuousOn.integrableOn_compact hcpt` replaced
by `hf_loc.integrableOn_isCompact hcpt`. See `knowledge.md`
§ "Mathlib API audit" for the precise lemma names and pin.

## Why It Matters

1. **Usability.** Constructing the `(volume.restrict A).prod
   (volume.restrict B)` integrability proof is mechanical but
   verbose. `LocallyIntegrable` is the canonical Mathlib idiom
   for "f is L¹ on every compact"; many users will already have
   it in hand (e.g. continuous functions, `L¹_loc` density,
   Sobolev representatives). A wrapper saves them the bridge
   step.
2. **No mathematical content lost.** Like sibling OQ-03 (Bochner
   generalization), this is a "free" wrapper: zero new lemmas
   needed, just an inlined application of an existing Mathlib
   API (`LocallyIntegrable.integrableOn_isCompact`).
3. **Parallel slot.** The wrapper composes orthogonally with
   OQ-03 (`Bochner` codomain): a single combined wrapper
   `intervalIntegral_swap_of_locallyIntegrable` for `f : ℝ →
   ℝ → E` is the obvious next step after both OQ-02 and OQ-03
   land. (We do **not** attempt the combined wrapper here; that
   is its own OQ if seeker decides to extract it.)
4. **Stronger ⇒ weaker** *is the wrong direction*. The seeker's
   phrasing suggests a misreading of the Mathlib idiom; the
   accurate reframing (alternative interface, not weaker
   hypothesis) keeps the deliverable honest about its
   mathematical status.

## Decomposition

- **S1 (this iteration, OBSERVE).** Identify the canonical
  Mathlib bridge `LocallyIntegrable.integrableOn_isCompact`,
  confirm `IsCompact (uIcc a b ×ˢ uIcc c d)` is mechanical, and
  spell out that the wrapper proof script is a 5-line
  modification of the parent's continuous-case proof. Document
  the "stronger, not weaker" reframing so future iterations
  don't waste effort searching for a strictly-weaker
  hypothesis. **No Lean changes.**
- **S2 (next, SCAFFOLD).** Create
  `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` with
  `intervalIntegral_swap_of_locallyIntegrable` proven inline
  (~30 lines including docstring). Build-verify.
- **S3 (final, optional).** Gallery entry
  (`src/data/proofs/<slug>/`) and Mathlib-contribution
  discussion in the docstring (target:
  `Mathlib.MeasureTheory.Integral.IntervalIntegral`,
  suggested name: `intervalIntegral.integral_comm_locallyIntegrable`
  or `intervalIntegral.swap_locallyIntegrable`).

## References

- Parent proof: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean`
  (231 lines, 0 sorries, 0 axioms, status: `verified`).
- Sibling OQ-03: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean`
  — same wrapper-style pattern for the Bochner codomain.
- Sibling OQ-01: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
  — n-dim lift via `Measure.pi`.
- Mathlib reference: `MeasureTheory.LocallyIntegrable` in
  `Mathlib.MeasureTheory.Function.LocallyIntegrable`; key API
  is `LocallyIntegrable.integrableOn_isCompact : LocallyIntegrable
  f μ → IsCompact K → IntegrableOn f K μ`.
- Mathlib reference: `restrict_prod_eq_prod_restrict` in
  `Mathlib.MeasureTheory.Measure.Prod` (already used by the
  parent's continuous case).
