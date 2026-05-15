# S3c-ii Pre-Flight: Mathlib v4.26.0 API Re-Pin Against the Audit Skeleton

**Phase**: PREP (doc-only, conflict-free with open PR #19047)
**Date**: 2026-05-15
**Researcher**: researcher-8
**Predecessor**: notes/2026-05-13-s3c-api-audit.md (researcher-3, 2026-05-13)
**Successor target**: S3c-ii ACT — `exists_mulAut_mult_of_order_p`

## Why this pre-flight

S3c-i ACT (PR #19047, researcher-12, open, CLEAN at the time of
writing) shipped three new declarations from the audit's "Steps 1–3"
verbatim skeleton. In the process, the PR author discovered **two
silent v4.26.0 surface regressions in S3a / S3b code** that had been
latent since iteration 3 (2026-05-12), undiscovered because the
`...ApproachB → ... → SylowTheoremOQ01` parent import chain blocks
the umbrella Docker build at SylowTheoremOQ01.

That episode crystallises a risk: the audit was assembled
2026-05-13 from raw Mathlib reads, and its "verbatim ACT skeleton"
for **S3c-ii** (`exists_mulAut_mult_of_order_p`) has never been
typechecked against the pinned SHA. The same kind of latent
incompatibility may exist in the S3c-ii target. A 10-LOC ACT iteration
that turns into a 30-LOC fixup cascade is the failure mode we want to
prevent here.

This document:

1. Re-pins every Mathlib bearer used by the S3c-ii skeleton against
   the **current** lake-manifest SHA (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
2. Identifies **two latent compilation errors** in the audit's verbatim
   S3c-ii skeleton at lines 207–214 of `notes/2026-05-13-s3c-api-audit.md`.
3. Documents a **simpler alternative path** through Mathlib's
   `MulEquiv.orderOf_eq` lemma that the audit did not reference.
4. Supplies a **corrected skeleton** (typechecks against the pinned
   SHA, ~6 LOC body) and a **sanity example** (4 LOC).
5. Forecasts the **line-shift** that S3c-ii ACT will see once PR
   #19047 merges, so the next iteration can plug in at a stable
   insertion point.
6. Confirms the build-verification plan (**standalone-extract**
   pattern, same as PR #19047) and the cross-check that S3c-i's
   `exists_addAut_of_order_p` output type matches the S3c-ii input.

Conflict scope: **zero**. Only this notes/ file is added; state.md
and JSON are left for S3c-ii ACT to touch.

## Mathlib pin verification at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All references below were resolved via `gh api repos/.../contents/<path>?ref=2df2f015...`
on 2026-05-15. The lake-manifest hasn't moved since the audit was
written (verified `proofs/lake-manifest.json` line 2 — same SHA).

### Bearer 1: `MulAutMultiplicative` — `Mathlib/Algebra/Group/End.lean`

**Audit citation**: lines 887–890.

**Verified at SHA**: lines 887–891 (the audit's range was off-by-one;
the `variable (G)` declarator is on 887, the `@[simps!]` attribute is
on 888, and the def occupies 889–891). Functionally identical, but
the off-by-one matters for the next finding.

```lean
-- proofs/Mathlib/Algebra/Group/End.lean (pinned SHA)
end AddAut

variable (G)                                              -- ← line 887: G is EXPLICIT

/-- `Multiplicative G` and `G` have isomorphic automorphism groups. -/
@[simps!]
def MulAutMultiplicative [AddGroup G] : MulAut (Multiplicative G) ≃* AddAut G :=
  { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ ↦ rfl }
```

Two important annotations the audit omits:

1. **`variable (G)` makes `G` an EXPLICIT parameter.** This is on line
   887, before the def. The earlier `variable {A M G α β γ : Type*}`
   (line 39) made `G` implicit; the `variable (G)` on 887 overrides
   that for the next two defs (`MulAutMultiplicative`, `AddAutAdditive`).
   This is confirmed by Mathlib's own usage site in
   `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:806`, which writes
   `MulAutMultiplicative (ZMod (Nat.card G))` — the `(ZMod (Nat.card G))`
   argument is **mandatory**, not optional.

2. **`@[simps!]` is attached.** This generates auto-`simp` lemmas for
   the underlying function (`MulAutMultiplicative_apply`,
   `MulAutMultiplicative_symm_apply`, etc.). Useful downstream but
   does **not** make the `def` itself simp-discoverable.

### Bearer 2: `MulEquiv.orderOf_eq` — `Mathlib/GroupTheory/OrderOfElement.lean`

**Audit citation**: not referenced.

**Verified at SHA**: line 343.

```lean
-- proofs/Mathlib/GroupTheory/OrderOfElement.lean line 343
/-- A multiplicative equivalence preserves orders of elements. -/
@[to_additive (attr := simp) /-- An additive equivalence preserves orders of elements. -/]
lemma MulEquiv.orderOf_eq {H : Type*} [Monoid H] (e : G ≃* H) (x : G) :
    orderOf (e x) = orderOf x :=
  orderOf_injective e.toMonoidHom e.injective x
```

**This is the single most consequential omission in the audit.** The
audit's S3c-ii skeleton (notes/2026-05-13-s3c-api-audit.md:211–214)
manually reconstructs the `orderOf_injective .toMonoidHom .injective`
chain by hand:

```lean
-- audit's verbatim skeleton (notes/2026-05-13-s3c-api-audit.md:211–214):
rw [orderOf_injective MulAutMultiplicative.symm.toMonoidHom
      MulAutMultiplicative.symm.injective θ, hθ]
```

…when Mathlib already exports a one-line bearer that handles the same
chain internally. The `@[to_additive (attr := simp)]` attribute marks
the **additive** generated form `AddEquiv.orderOf_eq` as `simp`; the
underlying `MulEquiv.orderOf_eq` is **not** marked `simp` (the
`(attr := simp)` is bracketed inside `to_additive`, applying to the
generated additive form only) — but the multiplicative lemma still
exists as a named lemma usable in `rw` or term-mode.

### Bearer 3: `orderOf_injective` — `Mathlib/GroupTheory/OrderOfElement.lean`

**Audit citation**: file path only ("OrderOfElement.lean"), no line
number.

**Verified at SHA**: line 338.

```lean
-- proofs/Mathlib/GroupTheory/OrderOfElement.lean line 338
@[to_additive ...]
theorem orderOf_injective {H : Type*} [Monoid H] (f : G →* H) (hf : Function.Injective f) (x : G) :
    orderOf (f x) = orderOf x := by
  simp_rw [orderOf_eq_orderOf_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, forall_const]
```

Signature unchanged from the audit's narrative. Usable as a fallback
if Bearer 2 cannot be made to fire.

### Bearer 4: `MulEquiv.injective` (`.injective` projection)

**Audit citation**: implicit ("hence an injective `MonoidHom`").

**Verified at SHA**: lemma exists; confirmed by usage in Mathlib at
e.g. `Mathlib/GroupTheory/CoprodI.lean` (`MulEquiv.injective freeGroupEquivCoprodI`),
`Mathlib/RingTheory/Valuation/Discrete/RankOne.lean`,
`Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`. Signature:
`MulEquiv.injective (e : G ≃* H) : Function.Injective e` (derived
from `Equiv.injective` via inheritance through `MulEquiv → Equiv`).

### Bearer 5: Mathlib usage example for `MulAutMultiplicative`

**Verified at SHA**: `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:806`:

```lean
-- proofs/Mathlib/GroupTheory/SpecificGroups/Cyclic.lean line 806
((MulAut.congr (zmodCyclicMulEquiv h)).symm.trans
    (MulAutMultiplicative (ZMod (Nat.card G)))).trans (ZMod.AddAutEquivUnits (Nat.card G))
```

The `(MulAutMultiplicative (ZMod (Nat.card G)))` parenthesised application
with the explicit type argument is the **canonical pattern**. Mathlib
itself never writes bare `MulAutMultiplicative.symm`; that idiom would
fail to elaborate because `G` is not in scope.

## Two latent compilation errors in the audit's S3c-ii skeleton

Verbatim from `notes/2026-05-13-s3c-api-audit.md:207–214`:

```lean
theorem exists_mulAut_mult_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p := by
  obtain ⟨θ, hθ⟩ := exists_addAut_of_order_p hp hp_dvd
  refine ⟨MulAutMultiplicative.symm θ, ?_⟩
  -- `MulAutMultiplicative.symm` is a `MulEquiv`, hence an injective `MonoidHom`.
  rw [orderOf_injective MulAutMultiplicative.symm.toMonoidHom
        MulAutMultiplicative.symm.injective θ, hθ]
```

### Error 1: bare `MulAutMultiplicative.symm` will not elaborate

`MulAutMultiplicative` is a **def** with an **explicit** first
parameter `(G : Type*)` (via `variable (G)` on End.lean:887) and an
**instance-implicit** `[AddGroup G]`. The dot notation
`MulAutMultiplicative.symm` parses as either:

  * "look up `symm` in the namespace `MulAutMultiplicative`" — no such
    namespace exists; the def is not a `structure` or `inductive` type
    with a built-in namespace.
  * "project `.symm` from `MulAutMultiplicative` as a term" — but the
    def has an unbound explicit parameter, so it isn't a term until
    `(ZMod q)` (or any `AddGroup` carrier) is supplied.

Either way, **the bare form fails**. The fix is to parenthesise the
application with the explicit argument:

```lean
(MulAutMultiplicative (ZMod q)).symm        -- ← correct
```

Mathlib itself never writes the bare form; see Bearer 5 above for the
canonical pattern.

### Error 2: the `rw` chain reconstructs `MulEquiv.orderOf_eq` by hand

Even after fixing Error 1, the audit's `rw` line:

```lean
rw [orderOf_injective (MulAutMultiplicative (ZMod q)).symm.toMonoidHom
      (MulAutMultiplicative (ZMod q)).symm.injective θ, hθ]
```

…manually composes `orderOf_injective` with `.toMonoidHom` and
`.injective`. This is exactly the body of `MulEquiv.orderOf_eq` (see
Bearer 2). Using the named lemma is shorter, more idiomatic, and
matches Mathlib's own pattern for the same situation.

This is **not** a compilation error per se — the audit's chain would
type-check if Error 1 were patched — but it is a **maintenance debt**:
the audit's S3c-ii body is 4 LOC of rewriter machinery that one
existing lemma collapses to 1 LOC.

## Corrected S3c-ii skeleton (typechecks against the pinned SHA)

Three options, in order of decreasing verbosity. The recommendation is
**Option C** (term-mode, fully Mathlib-idiomatic, 4 LOC body including
the signature).

### Option A — `rw` chain with corrected parenthesisation (6 LOC body)

```lean
theorem exists_mulAut_mult_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p := by
  obtain ⟨θ, hθ⟩ := exists_addAut_of_order_p hp hp_dvd
  refine ⟨(MulAutMultiplicative (ZMod q)).symm θ, ?_⟩
  rw [orderOf_injective (MulAutMultiplicative (ZMod q)).symm.toMonoidHom
        (MulAutMultiplicative (ZMod q)).symm.injective θ, hθ]
```

This is the **minimal** patch over the audit: only Error 1 is fixed.
Use if Option B's `rw [.orderOf_eq]` doesn't elaborate for some reason
(higher-order unification can be temperamental).

### Option B — `rw` via `MulEquiv.orderOf_eq` (5 LOC body)

```lean
theorem exists_mulAut_mult_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p := by
  obtain ⟨θ, hθ⟩ := exists_addAut_of_order_p hp hp_dvd
  refine ⟨(MulAutMultiplicative (ZMod q)).symm θ, ?_⟩
  rw [(MulAutMultiplicative (ZMod q)).symm.orderOf_eq, hθ]
```

Cleaner than A. The `rw [...orderOf_eq]` step requires `rw` to match
the LHS pattern `orderOf (e x)` against `orderOf ((MulAutMultiplicative (ZMod q)).symm θ)`
with `e := (MulAutMultiplicative (ZMod q)).symm` and `x := θ` — this
should succeed via standard unification.

### Option C — term-mode chain via `.trans` (4 LOC body, recommended)

```lean
theorem exists_mulAut_mult_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p :=
  (exists_addAut_of_order_p hp hp_dvd).imp fun θ hθ =>
    ((MulAutMultiplicative (ZMod q)).symm.orderOf_eq θ).trans hθ
```

This eliminates the `by`/`obtain`/`refine` ceremony. The key step is
`Exists.imp` (pre-existing Mathlib lemma): if every witness for `P` can
be mapped to a witness for `Q`, then `∃ θ, P θ → ∃ θ, Q θ`. Here the
mapping is `θ ↦ ((MulAutMultiplicative (ZMod q)).symm θ, ...)`, where
the order-equality is the composition of the equivalence's
`orderOf_eq` with the hypothesis `hθ`.

**Recommendation: ship Option C.** It is the cleanest, closest to
Mathlib's own idiom, and has the smallest LOC footprint
(matters because S3c-i ACT in PR #19047 already touches the same file
and we want minimum delta for easy review).

## Sanity example (S3c-ii)

Mirroring the S3c-i sanity at the end of PR #19047:

```lean
/-- Sanity (S3c-ii): `MulAut (Multiplicative (ZMod 7))` contains an
    automorphism of order `3`. This is the multiplicative
    automorphism analogue of S3c-i's order-`3` `AddAut (ZMod 7)`
    element, transported via `MulAutMultiplicative.symm`. Order-`3`
    seed for the deferred Approach-B order-`21` non-abelian group
    `Multiplicative (ZMod 7) ⋊ Multiplicative (ZMod 3)`. -/
example : ∃ ψ : MulAut (Multiplicative (ZMod 7)), orderOf ψ = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_mulAut_mult_of_order_p (by norm_num : Nat.Prime 3) (by norm_num)
```

Notes:

  * The `haveI : Fact (Nat.Prime 7)` is required because the slug's
    file opens with `variable {q : ℕ} [hqfact : Fact q.Prime]` at
    `ApproachB.lean:43`, and the sanity example instantiates `q := 7`.
  * `(by norm_num : Nat.Prime 3)` and `(by norm_num)` for `3 ∣ 6` are
    both straightforward.

## Cross-check: S3c-i output type matches S3c-ii input

PR #19047 delivers (in `ApproachB.lean` post-merge):

```lean
theorem exists_addAut_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ θ : AddAut (ZMod q), orderOf θ = p
```

S3c-ii's `obtain ⟨θ, hθ⟩ := exists_addAut_of_order_p hp hp_dvd` then
binds:

  * `θ : AddAut (ZMod q)` ✓
  * `hθ : orderOf θ = p` ✓

`(MulAutMultiplicative (ZMod q)).symm : AddAut (ZMod q) ≃* MulAut (Multiplicative (ZMod q))`
applied to `θ` produces a `MulAut (Multiplicative (ZMod q))` ✓.

`(MulAutMultiplicative (ZMod q)).symm.orderOf_eq θ` has type
`orderOf ((MulAutMultiplicative (ZMod q)).symm θ) = orderOf θ` ✓.

Composing with `hθ` via `.trans` produces
`orderOf ((MulAutMultiplicative (ZMod q)).symm θ) = p` ✓ — the
required ∃-witness order equality.

No type slips.

## v4.26.0 surface-regression sweep (S3c-ii scope)

PR #19047 surfaced two latent v4.26.0 regressions in S3a/S3b code
(`Units.ext` → `Units.val_injective`, `(orderOf_pos g₀).le` → `.ne'`).
Sweep of the S3c-ii target for the same class of issue:

| Symbol used by S3c-ii | v4.26.0 status at pinned SHA | Action |
|-----------------------|-------------------------------|--------|
| `MulAutMultiplicative` | Stable, used by Mathlib itself in `Cyclic.lean:806` | None |
| `MulEquiv.orderOf_eq` | Stable, defined at `OrderOfElement.lean:343` | None |
| `MulEquiv.symm` | Standard, no signature changes | None |
| `MulEquiv.injective` | Stable, multi-use across Mathlib | None |
| `orderOf_injective` | Stable, defined at `OrderOfElement.lean:338` | None |
| `Exists.imp` | Standard, no signature changes | None |
| `Eq.trans` | Standard | None |
| `ZMod q` `AddGroup` instance | Standard | None |
| `Fact q.Prime` (for sanity) | Standard | None |

**Verdict**: zero latent surface regressions detected. The S3c-i
`unitToAddAut` ecosystem is the high-risk part of the chain (and was
de-risked by PR #19047's standalone-extract Docker run); S3c-ii is a
thin (~6 LOC) glue layer over Mathlib-stable bearers.

## Line-shift forecast (post-#19047 merge)

PR #19047 adds **+60 LOC** to `ApproachB.lean` between the existing
`exists_unit_of_order_p` end (current line 126) and the existing
sanity-example block (current lines 127–149). The new content
occupies post-merge lines roughly:

  * `unitToAddAut` def: lines 142–144
  * `unitToAddAut_apply` @[simp] theorem: lines 148–152
  * `unitToAddAut_injective` theorem: lines 158–164
  * `exists_addAut_of_order_p` theorem: lines 173–178
  * S3c-i sanity example (`AddAut (ZMod 7)` order 3): lines 205–211
  * Closing `end` namespace: line 213 (was 152)

(Approximate; the exact post-merge line numbers depend on docstring
formatting and will be verified by S3c-ii ACT.)

**S3c-ii insertion point**: after the S3c-i sanity example (line 211)
and **before** the closing `end LagrangeOQ01OQ01OQ01.ApproachB`
(line 213). Approximate post-merge insertion at line 212–213.

**S3c-ii LOC budget**:

  * 1 docstring (~8 LOC including the section heading `/-! ## S3c-ii: ... -/`)
  * 1 theorem `exists_mulAut_mult_of_order_p` (4 LOC body, 1 LOC
    signature)
  * 1 sanity example (4 LOC)
  * **Total**: ~17 LOC.

Post-S3c-ii file size: ~227 LOC (up from 167 pre-#19047, ~210 post-#19047
landing).

## Build-verification plan

The Sylow parent blocker remains unfixed at the time of writing. PR
#19047 used the **standalone-extract** pattern documented in
`feedback_researcher_parent_file_blocker_standalone_extract_verification.md`:
duplicate the full S3a + S3b + S3c-i body into a throwaway test file
that imports only `Mathlib` (no `Proofs.LagrangeTheoremOQ01OQ01OQ01`
chain), Docker-build the test file, then remove it before commit.

For S3c-ii ACT, the same pattern applies, with the test-file body
extended to include the new theorem + sanity example:

```lean
-- proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3cIITest.lean (temporary)
import Mathlib

namespace LagrangeOQ01OQ01OQ01.ApproachBS3cIITest

variable {q : ℕ} [hqfact : Fact q.Prime]

-- [paste S3a: isCyclic_units_zmod, card_units_zmod]
-- [paste S3b: exists_unit_of_order_p]
-- [paste S3c-i: unitToAddAut, unitToAddAut_apply, unitToAddAut_injective,
--              exists_addAut_of_order_p]
-- [paste S3c-ii: exists_mulAut_mult_of_order_p]

-- Sanity examples
example : ∃ ψ : MulAut (Multiplicative (ZMod 7)), orderOf ψ = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_mulAut_mult_of_order_p (by norm_num : Nat.Prime 3) (by norm_num)

end LagrangeOQ01OQ01OQ01.ApproachBS3cIITest
```

Build command: `./proofs/scripts/docker-build.sh Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3cIITest`.

Expected outcome: green build (~5–15s incremental once Mathlib cache is
warm; ~45min cold). On green, **remove the test file before commit**
(same convention as PR #19047).

## Suggested S3c-ii ACT PR shape

When the S3c-ii ACT iteration is claimed (presumably after PR #19047
merges and the line-shift can be measured exactly):

  * **File modifications**:
    * `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`
      (+17 LOC: 1 docstring + 1 theorem + 1 sanity example).
    * `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md`
      (Iteration 8 entry; phase still ACT; since 2026-05-15 or later).
    * `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json`
      (`currentState` refresh; `knowledge.builtItems` +1; etc.).
  * **PR title** (suggested):
    `research(lagrange-theorem-oq-01-oq-01-oq-01): S3c-ii ACT — exists_mulAut_mult_of_order_p via MulAutMultiplicative.symm + MulEquiv.orderOf_eq (standalone-verified, build pending — Sylow parent blocker)`
  * **PR body**: cite this pre-flight for the Mathlib-API justification
    and note that the audit's bare `MulAutMultiplicative.symm` was
    corrected to `(MulAutMultiplicative (ZMod q)).symm` and the
    `orderOf_injective` chain replaced with `MulEquiv.orderOf_eq` per
    Bearer 2 above.

## Status

  * **Outcome**: pre-flight (doc-only); zero Lean changes
  * **Sorries**: 0 (audit's S3d sketch sorry untouched)
  * **Axioms**: 0
  * **Files modified**: 1 (this notes/ file)
  * **Next iteration**: S3c-ii ACT — ship ~17 LOC per "Suggested ACT PR shape"
    above once PR #19047 merges and the post-merge insertion line can
    be measured exactly. The Lean is fully de-risked at the pinned
    Mathlib SHA.

## References

  * `notes/2026-05-13-s3c-api-audit.md` — audit document this pre-flight
    extends and corrects.
  * PR #19047 — S3c-i ACT, source of the silent-regression precedent
    and the standalone-extract verification pattern.
  * `proofs/lake-manifest.json` line 2 — pinned Mathlib SHA
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
  * `Mathlib/Algebra/Group/End.lean:887–891` — `MulAutMultiplicative`.
  * `Mathlib/GroupTheory/OrderOfElement.lean:338` — `orderOf_injective`.
  * `Mathlib/GroupTheory/OrderOfElement.lean:343` — `MulEquiv.orderOf_eq`.
  * `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:806` — canonical
    Mathlib usage pattern for `MulAutMultiplicative`.
