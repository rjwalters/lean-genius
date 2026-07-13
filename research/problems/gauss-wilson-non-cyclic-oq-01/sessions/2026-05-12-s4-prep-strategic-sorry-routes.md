# S4 PREP — Mathlib API routes for closing the Phase B strategic sorry

**Date**: 2026-05-12
**Researcher**: researcher-10
**Phase**: PREP (scoping for S4 — does **not** modify the Lean file)
**Conditional on**: PR #18232 (S3 ACT Phase B partial) merged, so
`proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` carries the strategic
sorry `prod_univ_eq_pow_card_div_two_of_elementary`.

This document is **doc-only**. It surveys the Mathlib API surface that
a future S4 ACT iteration must navigate to close the strategic sorry
and ranks four candidate routes by Lean LOC, Mathlib coverage risk,
and prerequisite typeclass/instance machinery.

The Phase B helpers themselves
(`mul_left_self_inv_of_elementary`, `mul_left_ne_self_of_ne_one`,
`pow_eq_one_of_sq_eq_one`, `pow_eq_self_of_sq_eq_one`,
`exists_two_distinct_ne_one`) are all build-pending in PR #18232; an
S3.5 / drift-fix pass to add `lake check` results is orthogonal to this
plan and can run in parallel.

## 1. The strategic sorry (verbatim from `GaussWilsonNonCyclicOQ01B.lean:131-137`)

```lean
/-- **(SORRY — strategic)** For elementary 2-abelian `H` and any
    non-identity `h ∈ H`, the product over `Finset.univ` factors as
    `h ^ (Fintype.card H / 2)` via the pairing induced by left
    translation. -/
theorem prod_univ_eq_pow_card_div_two_of_elementary
    [Fintype H] [DecidableEq H]
    (hexp : ∀ x : H, x ^ 2 = 1) {h : H} (hne : h ≠ 1) :
    ∏ x : H, x = h ^ (Fintype.card H / 2) := by
  -- Deferred to S4: transversal-pairing construction.
  -- See module docstring for the proof outline.
  sorry
```

Variable context (full): `{H : Type*} [CommGroup H]`, then the
inline `[Fintype H] [DecidableEq H]` hypotheses and the two named
arguments `hexp`, `hne`.

The conclusion is an equation in `H`. Both sides are
elements of `H`; `h ^ (Fintype.card H / 2)` uses
`Monoid.npow` (the natural-number power operation), so unification
flows entirely inside the `CommGroup H` instance.

## 2. Mathematical content (recap, with explicit cardinalities)

The map `σ_h : H ≃ H`, `σ_h x := h * x`, is

- **an involution**, since `σ_h (σ_h x) = h * (h * x) = h^2 * x = 1 * x = x`
  (uses `hexp h : h^2 = 1`);
- **fixed-point-free**, since `σ_h x = x ⟹ h * x = x ⟹ h = 1`,
  contradicting `hne` (uses `mul_left_ne_self_of_ne_one`).

Therefore `σ_h` partitions `Finset.univ : Finset H` into orbits of size
exactly `2`. There are `Fintype.card H / 2` such orbits (this implicitly
uses that `Fintype.card H` is even, which is forced once we pick a
non-identity `h` and observe that the FPF involution `σ_h` cannot exist
on a set of odd cardinality — but in fact this is also a *consequence*
of the orbit decomposition rather than a separate hypothesis).

For each orbit `{x, h * x}`, the product `x * (h * x) = h * x^2 = h`
(uses `hexp x : x^2 = 1` and commutativity). So the total product
`∏ x ∈ Finset.univ, x` equals `h` multiplied by itself `Fintype.card H / 2`
times, i.e. `h ^ (Fintype.card H / 2)`. □

## 3. Candidate Mathlib API routes

Four routes, ordered from most-to-least direct. Each entry gives the
**key Mathlib identifier**, the **rough Lean LOC** required, and the
**main risk** (alignment with the v4.26.0 Mathlib that the project
pins).

### Route A — Explicit transversal Finset via `Finset.prod_union` and `Finset.prod_image`

**Idea.** Construct a `Finset H` `T` of size `Fintype.card H / 2` with
the property that `T` and `T.image (h * ·)` are disjoint and union to
`Finset.univ`. Then

```
∏ x : H, x
  = (∏ x ∈ T, x) * (∏ x ∈ T.image (h * ·), x)            -- prod_union
  = (∏ x ∈ T, x) * (∏ x ∈ T, h * x)                       -- prod_image, mulLeft inj
  = (∏ x ∈ T, x) * h^|T| * (∏ x ∈ T, x)                   -- prod_mul_distrib + prod_const
  = h^|T| * (∏ x ∈ T, x)^2                                -- commutativity
  = h^|T| * 1                                             -- (∏ x ∈ T, x)^2 = ∏ x ∈ T, x^2 = 1
  = h^(Fintype.card H / 2)
```

**Mathlib identifiers (v4.26.0-likely):**
- `Finset.prod_union` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`)
- `Finset.prod_image` (verified at line 95; injective on the filter follows from `mul_right_cancel`)
- `Finset.prod_mul_distrib`
- `Finset.prod_const : ∏ _ ∈ s, b = b ^ #s` (verified at line 629)
- `Finset.prod_pow : ∏ x ∈ s, f x ^ n = (∏ x ∈ s, f x) ^ n` for `n=2`
- `Function.Injective.mulLeft` (in `Mathlib/Algebra/Group/Basic.lean`)

**Constructing the transversal `T`.** This is the load-bearing step.
Three sub-options:

- **A.1.** `LinearOrder H` not generally available. **Rejected** —
  `CommGroup H` does not imply any order, and we cannot synthesise
  one without choice.
- **A.2.** Classical-choice transversal via `Quot.exists_rep`:
  use `setoid := MulAction.orbitRel (Subgroup.zpowers h) H` and
  define `T : Finset H := Finset.image Quot.out (Finset.univ : Finset (H ⧸ Subgroup.zpowers h))`.
  Disjointness of `T` and `T.image (h * ·)` then reduces to
  `Quot.out_eq` + the orbit characterisation. **Estimated 30 LOC**
  but the `Finset (H ⧸ Subgroup.zpowers h)` instance requires either
  a `Fintype (H ⧸ Subgroup.zpowers h)` instance (available via
  `QuotientGroup.fintype`) or manual `Finset` construction.
- **A.3.** Avoid the transversal entirely by working with `Finset.attach`
  and a `Fin 2`-indexed partition. Define
  `e : H ≃ (H ⧸ Subgroup.zpowers h) × Fin 2` by sending `x` to
  `(⟦x⟧, if Decidable.decide (x = (Quot.mk _ x).out) then 0 else 1)`.
  Then `∏ x : H, x = ∏ (q, i), e.symm (q, i)`. The inner product over
  `Fin 2` is `q.out * (h * q.out) = h`, summing to `h^|H/⟨h⟩|`.
  **Estimated 50 LOC** but elegant; depends on `Fintype` instance
  alignment.

**Total Lean LOC (A.2):** ~50–70. **Total Lean LOC (A.3):** ~60–80.

**Main risk.** The interaction between `Finset.prod_image` (which
requires `DecidableEq` on the target) and the `Quot.out`-defined
transversal is bookkeeping-heavy. Two-three iterations of `Finset.prod_bij`
massaging are likely.

### Route B — `MulAction.selfEquivSigmaOrbits` via `MulAction (Subgroup.zpowers h) H`

**Idea.** The Mathlib type-level equivalence

```lean
MulAction.selfEquivSigmaOrbits (G α : Type*) [Group G] [MulAction G α] :
    α ≃ Σ ω : orbitRel.Quotient G α, MulAction.orbit G ω.out
```

(`Mathlib/GroupTheory/GroupAction/Basic.lean:476`, verified) gives a
type-level decomposition. Use it with `G := Subgroup.zpowers h`
acting on `H` by left multiplication.

```
∏ x : H, x
  = ∏ (ω, y) : Σ ω, orbit (zpowers h) ω.out, (ω, y).snd        -- re-index via selfEquivSigmaOrbits
  = ∏ ω, (∏ y : orbit (zpowers h) ω.out, y)                    -- Finset.prod_sigma
  = ∏ ω, h                                                      -- each orbit product = h
  = h ^ (Fintype.card (orbitRel.Quotient (zpowers h) H))        -- Finset.prod_const
  = h ^ (Fintype.card H / 2)                                    -- card_quotient via orbit-stabilizer
```

**Mathlib identifiers (v4.26.0-likely):**
- `MulAction.selfEquivSigmaOrbits`
  (`Mathlib/GroupTheory/GroupAction/Basic.lean:476`)
- `Finset.prod_sigma`
  (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`)
- `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
  (`Mathlib/GroupTheory/GroupAction/Quotient.lean:182`)
- `Subgroup.card_zpowers` or `Subgroup.zpowers_card` (need exact name)
- `Subgroup.zpowers_eq_top_iff` (likely not used; instead use the
  fact that `orderOf h = 2` for `h ≠ 1` with `h^2 = 1`).

**Subtle prerequisite:** the `MulAction (Subgroup.zpowers h) H` instance
needs `Subgroup.zpowers h ≤ ⊤`, i.e. the subgroup-action lifting. Most
of this is automatic via `Subgroup.MulAction` (the subgroup inherits
the ambient group's action). The orbit `MulAction.orbit (zpowers h) y`
should have cardinality `2` when `h ≠ 1` and `h^2 = 1`; this requires
proving `Fintype.card (zpowers h) = 2`, which follows from
`Subgroup.zpowers_card` + `orderOf h = 2`. The latter needs
`orderOf_eq_two_iff_of_nonidentity` or manual case split.

**Total Lean LOC:** ~70–100. **Main risk:** the `orderOf h = 2` step
requires either a direct calculation
(`(hexp h : h^2 = 1) ∧ (hne : h ≠ 1) ⟹ orderOf h = 2`) or invoking
`orderOf_eq_iff` with `2`-specific case splits. Either way it's a
named-lemma-chase exercise that's hard to estimate without a fresh
Mathlib build.

**Advantage over Route A:** no manual transversal construction; the
sigma-equivalence machinery does the bookkeeping. **Disadvantage:**
heavier categorical setup; more chances for `to_additive`-induced
namespace drift.

### Route C — `Equiv.Perm.cycleType` of the involution `Equiv.mulLeft h`

**Idea.** View `σ_h := Equiv.mulLeft h : Equiv H H` as a permutation of
the finite set `H`. Since `σ_h` is a fixed-point-free involution, its
cycle decomposition consists entirely of 2-cycles (transpositions);
each 2-cycle is `{x, h * x}` and its product (in `H`) is `h`. So

```
∏ x : H, x = ∏ c ∈ σ_h.cycleType.support, (∏ x ∈ c.support, x)
            = ∏ c ∈ σ_h.cycleType.support, h                        -- each 2-cycle product = h
            = h ^ (number of 2-cycles)
            = h ^ (Fintype.card H / 2)
```

**Mathlib identifiers (v4.26.0-likely):**
- `Equiv.Perm.cycleType` (`Mathlib/GroupTheory/Perm/Cycle/Type.lean`)
- `Equiv.Perm.IsCycle.prod_of_support_eq` (need exact name)
- `Equiv.Perm.cycleType_eq_replicate_two_of_FPF_involution` (likely
  does not exist as-named; would need to prove it)
- `Equiv.Perm.support_card_eq_sum_cycleType`
  (or `Equiv.Perm.cycleType_sum`)

**Main risk.** Mathlib's `cycleType` machinery is heavyweight and
optimised for sign/parity arguments rather than direct product
computation. The bridge between "product over a 2-cycle's support" and
"`x * (h * x) = h`" is not a packaged Mathlib lemma; we would write it
ourselves. **Estimated 80–120 LOC.** **Not recommended** unless future
Mathlib upstream changes add a `Equiv.Perm.prod_apply` API.

### Route D — Avoid the strategic sorry via `Module (ZMod 2) (Additive H)` structure theorem

**Idea.** Bypass the per-`h` identity entirely. For elementary 2-abelian
`H`, the additive shadow `Additive H` is a finite `ZMod 2`-module
(`x^2 = 1` ⇔ `2 • x = 0` in additive notation), hence by finite-
dimensional `ZMod 2`-vector-space theory, `Additive H ≃ₗ[ZMod 2] Fin k →₀ ZMod 2`
for some `k`. The sum `∑ x : Fin k → ZMod 2, x` over the finite cube
`(ZMod 2)^k` is `((2^(k-1)) % 2, …, (2^(k-1)) % 2) = (0, …, 0)` for
`k ≥ 2`, so directly `∏ x : H, x = 1` (multiplicative form).

This **replaces the strategic sorry with a different sorry** — namely
the structure theorem and the explicit basis. Net sorry count: 1 → 1,
but the residual gap is reusable across other elementary-2-abelian
theorems.

**Mathlib identifiers (v4.26.0-likely):**
- `Module (ZMod 2) (Additive H)` instance (need exact path)
- `Module.Finite.exists_basis` / `Basis.exists_of_module_finite`
- `Finsupp.prod_univ_eq_sum` over `Fin k → ZMod 2`

**Main risk.** The `Module (ZMod 2)` instance on `Additive H` may not
exist as a direct synthesisable instance; we would need to construct it
manually using `AddCommGroup → Module ℤ → Module (ZMod 2)` for
2-torsion groups. **Estimated 100–150 LOC**, much of which is
prerequisite setup. **Not recommended for S4** but worth noting as a
medium-term gallery refactor candidate (e.g. to support a future
"elementary-2-abelian Wilson product" reusable Mathlib lemma).

## 4. Comparison table

| Route | Total LOC | Main risk | Reusability | Recommend? |
|-------|-----------|-----------|-------------|-----------|
| **A.2** transversal via `Quot.out` | ~50–70 | `Finset.prod_image` bookkeeping | Low (slug-specific) | ✅ **S4 ACT first attempt** |
| **A.3** `H ≃ Q × Fin 2` re-index | ~60–80 | `Decidable` on canonical-rep predicate | Low | Backup if A.2 stalls |
| **B** `selfEquivSigmaOrbits` | ~70–100 | `orderOf h = 2` lemma chase | Medium (any FPF-involution proof) | Acceptable; slower |
| **C** `Equiv.Perm.cycleType` | ~80–120 | No packaged product-over-cycles API | Medium | ❌ defer |
| **D** `Module (ZMod 2)` structure | ~100–150 | Instance synthesis | High (multi-slug) | ❌ defer (gallery-refactor scope) |

**Recommendation:** **Route A.2**. Lowest total LOC, cleanest cancellation
chain in the calc proof, and the `Quot.out`-based transversal pattern
appears multiple times elsewhere in this project (cf. orbit decompositions
in `MosersCircleProblem.lean` and `BurnsidesOrbitCounting.lean` if
present — outside this file's scope to confirm).

## 5. Sketched Route A.2 skeleton (no Lean edits implied)

For the next S4 ACT iteration to translate directly:

```lean
theorem prod_univ_eq_pow_card_div_two_of_elementary
    [Fintype H] [DecidableEq H]
    (hexp : ∀ x : H, x ^ 2 = 1) {h : H} (hne : h ≠ 1) :
    ∏ x : H, x = h ^ (Fintype.card H / 2) := by
  classical
  -- 1. The MulAction of ⟨h⟩ on H by left multiplication.
  let G := Subgroup.zpowers h
  haveI : Fintype G := Subgroup.zpowers.fintype h
  -- 2. orderOf h = 2 (uses hexp h + hne).
  have h_orderOf : orderOf h = 2 := by
    apply Nat.le_antisymm
    · exact orderOf_le_of_pow_eq_one (by decide) (hexp h)
    · -- orderOf h ≥ 2 from h ≠ 1
      rcases (Nat.lt_or_ge 1 (orderOf h)) with h | h
      · exact h
      · interval_cases (orderOf h)
        · exact absurd (orderOf_eq_zero_iff.mp ‹_›) sorry  -- finite group
        · exact absurd (orderOf_eq_one_iff.mp ‹_›) hne
  -- 3. |G| = 2.
  have hG_card : Fintype.card G = 2 := by
    rw [Subgroup.card_zpowers, h_orderOf]   -- v4.26.0 name TBD
  -- 4. The quotient orbitRel.Quotient G H has card = card H / 2.
  -- Use card_orbit_mul_card_stabilizer_eq_card_group + the fact that
  -- each orbit has size 2 (FPF involution).
  --
  -- 5. Build transversal T := Finset.image Quot.out (Finset.univ).
  let T : Finset H := Finset.image Quot.out (Finset.univ : Finset (MulAction.orbitRel.Quotient G H))
  --
  -- 6. Show univ = T ∪ T.image (h * ·) with disjoint union.
  -- 7. Apply Finset.prod_union; rewrite via Finset.prod_image; use hexp x.
  sorry  -- placeholder; full proof in S4 ACT
```

This skeleton is **for documentation**; the file in PR #18232 is
unchanged by this PREP. Steps 1–4 are mechanical (~25 LOC).
Steps 5–7 are the load-bearing transversal-pairing computation (~30–40
LOC).

## 6. Anti-targets

The following are **explicitly out of scope for S4**:

- **Closing OQ-01 Phase C (`prod_univ_units_zmod_eq_neg_one_iff_isCyclic`).**
  That is the S5 deliverable per state.md line 135 and depends on this
  S4 closing first.
- **Replacing the helper lemmas in `GaussWilsonNonCyclicOQ01B.lean`.**
  The 5 build-pending helpers (lines 57–116) are correct as written;
  drift-fix is a separate PR.
- **Adding `Module (ZMod 2)`-typeclass infrastructure to elementary
  2-abelian groups.** That is Route D and a gallery-refactor task
  (multi-slug scope).
- **Generalising to `IsPGroup p H` for arbitrary primes `p`.** The
  Phase B identity only works for `p = 2` (squaring kills cross-terms);
  any attempt to abstract to general `p` will mislead future readers.
- **Touching the sibling OQ-03 (`GaussWilsonNonCyclicOQ03.lean`).**
  OQ-03 is on an independent S4 trajectory (exact CRT count).

## 7. Build-state observation

`proofs/.lake` in this worktree is the recursive self-symlink documented
in `feedback_researcher_lake_symlink_broken.md`; a fresh Docker
Mathlib clone is required (~25–45 min). PR #18232 was merged
build-pending per gallery convention, and the 5 helper lemmas have
≤ 5-line mechanical proofs with no exotic tactics, so the inherited
risk surface for S4 is small. An S3.5 drift-fix verification pass is
useful but orthogonal to closing the strategic sorry.

## 8. Race awareness

At the time of writing (2026-05-12 22:50 UTC, ~50 min after PR #18232
merge):

- `gh pr list --search gauss-wilson-non-cyclic-oq-01 --state open` → empty
- `git branch -r | grep gauss-wilson-non-cyclic-oq-01` → only the
  merged S3 Phase B branch
- The sibling OQ-03 has independent S4+ activity (PRs #18125, #18072,
  #18005); no cross-pollution risk.

A parallel S4 ACT (researcher attempting the strategic sorry directly)
is plausible within the next 30–60 min given the marketable
"Gauss–Wilson" framing. This PREP is intentionally a **separate
session-note file** (`sessions/2026-05-12-s4-prep-strategic-sorry-routes.md`)
that does NOT modify `state.md`, `knowledge.md`, `problem.md`, or any
Lean file. It can land in parallel with any S4 ACT attempt without
merge-conflicts; conversely an S4 ACT that lands first does not
invalidate this analysis (the Mathlib API survey remains useful
regardless of which route the implementer picks).

## 9. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/GaussWilsonNonCyclic.lean` (parent, 323 lines)
- `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` (Phase A, 66 lines, verified)
- `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` (Phase B partial, 165 lines, build-pending)
- `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` (sibling)
- `proofs/Proofs.lean` (manifest)
- `research/problems/gauss-wilson-non-cyclic-oq-01/{state,knowledge,problem}.md`
- `src/data/proofs/gauss-wilson-non-cyclic/` (gallery, untouched)
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-01.json`
- `.lean/state/candidate-pool.json`

Only this single new file is added. Future status field for this slug:
remains `axiomatized` (PR #18232 carries 1 strategic sorry; S4 ACT
will reduce to 0 sorries upon successful Route A.2/A.3 implementation,
at which point Phase B graduates to `verified`). No claim of
`verified` is implied here.

## 10. Verification checklist for S4 ACT (future researcher)

Before pushing an S4 ACT PR, the implementer should confirm:

1. ☐ `Finset.prod_image` accepts the injective-on-Finset form, not
   `Set.InjOn` (v4.26.0 changed signatures in some Group bigops files).
2. ☐ `Subgroup.zpowers.fintype` exists and is auto-inferred from
   `[Fintype H]`.
3. ☐ `orderOf h = 2` proof closes in ≤ 10 lines via
   `orderOf_le_of_pow_eq_one + orderOf_ne_one_iff_ne_one` (or analogue).
4. ☐ The transversal disjointness lemma
   `T ∩ T.image (h * ·) = ∅` reduces cleanly to
   `mul_left_ne_self_of_ne_one` (already proven in the file at line 68).
5. ☐ Total LOC ≤ 80 (else Route A.2 is failing and a Route-B pivot
   is warranted).
6. ☐ The Phase B main theorem
   `prod_univ_eq_one_of_elementary_card_ge_four` (line 141) still
   builds verbatim after the strategic sorry is closed — no signature
   drift introduced.

---

**End of S4 PREP — no Lean changes shipped; survey only.**
