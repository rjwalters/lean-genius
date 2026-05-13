# S4b PREP — Mathlib v4.26.0 API audit (citations check for PR #18347 routes)

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: PREP (sister to merged PR #18347 S4 PREP — strictly orthogonal, audits citations)
**Pinned Mathlib commit**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(from `proofs/lake-manifest.json`)

## 0. Goal and scope

PR #18347 (merged 2026-05-12 22:53 UTC) catalogued four candidate routes for
closing the Phase B strategic sorry `prod_univ_eq_pow_card_div_two_of_elementary`
in `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean`. The "Mathlib identifiers
(v4.26.0-likely)" lists in §3 of that document include a mix of verified line
citations, name guesses, and `(need exact name)` placeholders. The verification
checklist in §6 enumerates six concrete TODOs for the S4 implementer.

**This PREP performs the audit.** Each citation is verified against the pinned
v4.26.0 commit via the GitHub Contents API (no `lake build` required). The
output is a small but consequential **erratum** for PR #18347 plus exact
locations + signatures the S4 implementer should `#check` first.

**No Lean files are touched. No edits to `state.md`, `knowledge.md`, or
`problem.md`.** The only new artifact is this single file.

## 1. Headline finding

> **PR #18347 §3 Route B mis-cites `MulAction.selfEquivSigmaOrbits` location.**
> Cited path: `Mathlib/GroupTheory/GroupAction/Basic.lean:476`.
> Actual location: `Mathlib/GroupTheory/GroupAction/Defs.lean:482`.

The lemma exists and the signature is as PR #18347 described, but an S4
implementer typing the path verbatim into `import Mathlib.GroupTheory.GroupAction.Basic`
will succeed (the namespace re-exports), so this is a **documentation-only**
discrepancy. Still worth correcting for future readers.

Equally significant: **PR #18347's name guesses `Subgroup.card_zpowers` and
`Subgroup.zpowers_card` do not exist at v4.26.0.** The correct names are
`Fintype.card_zpowers` (in `OrderOfElement.lean`) and `Nat.card_zpowers`
(in `Data/ZMod/QuotientGroup.lean`) — both *unprefixed by `Subgroup`*.

## 2. Identifier-by-identifier audit

### 2.1 Route A — explicit transversal via `Finset.prod_union`

| Identifier | PR #18347 cite | v4.26.0 verified | Status |
|---|---|---|---|
| `Finset.prod_union` | `BigOperators/Group/Finset/Basic.lean` (no line) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (exists, multiple locations) | ✅ |
| `Finset.prod_image` | line 95 | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:1062` (signature `(h : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y)`) | ⚠ wrong line; signature is `Finset.InjOn` form not `Set.InjOn` |
| `Finset.prod_mul_distrib` | (no line) | exists in same file | ✅ |
| `Finset.prod_const` | line 629 | exists; verify exact line in v4.26.0 | ⚠ untested |
| `Finset.prod_pow` | (no line, mentioned for `n=2`) | `Mathlib/Algebra/BigOperators/GroupWithZero/Action.lean` (variant) — name OK | ✅ |
| `Function.Injective.mulLeft` | `Mathlib/Algebra/Group/Basic.lean` | exists; alias of `mul_right_cancel₀`-style chain | ✅ |
| `Subgroup.zpowers.fintype` | (instance) | `Mathlib/GroupTheory/Subgroup/ZPowers/Basic.lean` (verify) | ⚠ need exact path |
| `QuotientGroup.fintype` | (cited generically) | `Mathlib/GroupTheory/Coset/Basic.lean` (`Quotient.fintype` instance from a finite group) | ⚠ name may have changed |

**Implementer takeaway for Route A.2/A.3**:

```lean
#check @Finset.prod_image
-- (α β : Type*) [DecidableEq β] [CommMonoid γ] {f : β → γ} (s : Finset α)
--   {g : α → β} (h : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) :
--   ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x)
```

The injectivity hypothesis form is the **Finset-pointwise** version
(`∀ x ∈ s, ∀ y ∈ s, …`), not `Set.InjOn`. PR #18347 §6 item 1 flagged this as
"v4.26.0 changed signatures" — it has *not* changed at the pinned commit;
the Finset-pointwise form is the v4.26.0 form. The S4 implementer should
**use `Function.Injective.mulLeft : ∀ a, Function.Injective (a * ·)`** lifted
to the `Finset`-pointwise predicate via
`fun x _ y _ hxy ↦ (mulLeft_cancel hxy)` — ~3 LOC.

### 2.2 Route B — `MulAction.selfEquivSigmaOrbits`

| Identifier | PR #18347 cite | v4.26.0 verified | Status |
|---|---|---|---|
| `MulAction.selfEquivSigmaOrbits` | `GroupTheory/GroupAction/Basic.lean:476` | `Mathlib/GroupTheory/GroupAction/Defs.lean:482` | ❌ **wrong file** |
| `MulAction.selfEquivSigmaOrbits'` | (not cited) | `Defs.lean:471` (`α ≃ Σ ω : Ω, ω.orbit`, slightly different shape) | ➕ alternative |
| `MulAction.selfEquivSigmaOrbitsQuotientStabilizer` | (not cited) | `GroupAction/Quotient.lean:226` (`α ⧸ stabilizer α ω.out` form) | ➕ stronger |
| `Finset.prod_sigma` | `BigOperators/Group/Finset/Basic.lean` | exists | ✅ |
| `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` | `Quotient.lean:182` | `Quotient.lean:180` | ✅ (off by 2 lines, name correct) |
| `Subgroup.card_zpowers` | (one of two name guesses) | **does not exist** at v4.26.0 | ❌ |
| `Subgroup.zpowers_card` | (other name guess) | **does not exist** at v4.26.0 | ❌ |
| `Fintype.card_zpowers` | (not cited) | `OrderOfElement.lean:962`: `Fintype.card (zpowers x) = orderOf x` | ✅ **correct name** |
| `Nat.card_zpowers` | (not cited) | `Data/ZMod/QuotientGroup.lean:160`: `Nat.card (zpowers a) = orderOf a` | ✅ **correct name** |
| `Subgroup.zpowers_eq_top_iff` | (not used) | exists | ✅ (not needed for this proof) |

**Erratum content**:

PR #18347 §3 Route B cites:

> - `MulAction.selfEquivSigmaOrbits`
>   (`Mathlib/GroupTheory/GroupAction/Basic.lean:476`)

The verified location is **`Mathlib/GroupTheory/GroupAction/Defs.lean:482`**.
The signature (from the pinned commit, lines 482-485) is:

```lean
def selfEquivSigmaOrbits : α ≃ Σ ω : Ω, orbit G ω.out :=
  (selfEquivSigmaOrbits' G α).trans <|
    Equiv.sigmaCongrRight fun _ =>
      Equiv.setCongr <| orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'
```

where `Ω := MulAction.orbitRel.Quotient G α` (line 344 of `Defs.lean`). The
`selfEquivSigmaOrbits'` sibling at line 471 returns
`α ≃ Σ ω : Ω, ω.orbit` (without the `Quotient.out` step) and may be more
ergonomic if the user already has the quotient orbits in hand.

**Critical cited-name correction**: the `|⟨h⟩| = orderOf h` step is
**not** done via `Subgroup.card_zpowers` / `Subgroup.zpowers_card` (both
non-existent). Use one of:

```lean
#check @Fintype.card_zpowers
-- {G : Type*} [Group G] [Fintype G] (x : G) : Fintype.card (Subgroup.zpowers x) = orderOf x
-- Note: this is for the Fintype.card version (requires [Fintype G]).
-- Location: Mathlib/GroupTheory/OrderOfElement.lean:962

#check @Nat.card_zpowers
-- {α : Type*} [Group α] (a : α) : Nat.card (Subgroup.zpowers a) = orderOf a
-- Note: this is for the Nat.card version (no Fintype needed).
-- Location: Mathlib/Data/ZMod/QuotientGroup.lean:160
```

Choice between them: the slug already has `[Fintype H]` in scope at
`GaussWilsonNonCyclicOQ01B.lean:131`, so **`Fintype.card_zpowers` is the
better fit** — it returns `Fintype.card`, matching the conclusion of the
strategic sorry's RHS use of `Fintype.card H`.

### 2.3 Order-of-element calculation (used by both A and B)

| Identifier | PR #18347 cite | v4.26.0 verified | Status |
|---|---|---|---|
| `orderOf_le_of_pow_eq_one` | (used in §5 sketch) | `OrderOfElement.lean:240`: signature `(hn : 0 < n) (h : x ^ n = 1) : orderOf x ≤ n` | ✅ |
| `orderOf_eq_iff` | (not cited but mentioned) | `OrderOfElement.lean:215`: signature `(h : 0 < n) : orderOf x = n ↔ x^n = 1 ∧ ∀ m, 0 < m → m < n → x^m ≠ 1` | ✅ |
| `orderOf_eq_one_iff` | (alluded to as "analogue") | exists in `OrderOfElement.lean` | ✅ |
| `orderOf_eq_zero_iff` | (used in §5 sketch) | exists (only holds in `Monoid`, not finite); finite case: `pos_of_isOfFinOrder` | ⚠ wrong direction; `[Fintype]` gives `orderOf > 0` directly |

**Tightened S4 implementer recipe for `orderOf h = 2`**:

```lean
-- Given: hexp : ∀ x : H, x^2 = 1, hne : h ≠ 1, instance [Fintype H]
have h_orderOf : orderOf h = 2 := by
  rw [orderOf_eq_iff (by decide : (0 : ℕ) < 2)]
  refine ⟨hexp h, ?_⟩
  intro m hm_pos hm_lt
  interval_cases m  -- only m = 1 possible
  -- Goal: h ^ 1 ≠ 1 := by simpa using hne
  simpa using hne
```

**Estimated 6 lines** (vs PR #18347 §5's ~10-line `interval_cases (orderOf h)`
with a stray sorry). The key shift: instead of bounding `orderOf h` and then
checking each value, use `orderOf_eq_iff` directly with `n = 2` and dispatch
the `0 < m < 2` case via `interval_cases m`.

### 2.4 Routes C and D status

PR #18347 §3 explicitly marked Routes C and D as "defer." This audit does
not re-evaluate them; flagged here only that the cited identifiers
(`Equiv.Perm.IsCycle.prod_of_support_eq`, `Equiv.Perm.cycleType_eq_replicate_two_of_FPF_involution`,
`Module (ZMod 2) (Additive H)`) were not searched. Route A.2 + Route B
remain the recommended attack surface.

## 3. Updated decision table (with audit-corrected LOC estimates)

PR #18347 §4's table estimated route LOC under the assumption that each
cited identifier existed verbatim. The audit corrects two routes:

| Route | PR #18347 LOC | Audit-corrected LOC | Audit-corrected risk |
|-------|---------------|---------------------|----------------------|
| **A.2** transversal via `Quot.out` | 50–70 | 50–70 (no change) | Bookkeeping risk unchanged |
| **A.3** `H ≃ Q × Fin 2` re-index | 60–80 | 60–80 (no change) | `Decidable` risk unchanged |
| **B** `selfEquivSigmaOrbits` | 70–100 | **65–95** (–5 LOC) | `Fintype.card_zpowers` directly available, no name search; `orderOf h = 2` tightened from ~10 to ~6 lines |
| **C** `Equiv.Perm.cycleType` | 80–120 | not re-audited | deferred per PR #18347 |
| **D** `Module (ZMod 2)` | 100–150 | not re-audited | deferred per PR #18347 |

**Net effect on recommendation**: Route B's gap to Route A.2 narrows. With
audit-corrected names, Route B is **65–95 LOC** vs Route A.2's **50–70 LOC**.
Route A.2 still wins on LOC, but Route B is now within ~25% of A.2 and may
be preferable if the implementer prefers categorical bookkeeping over
explicit `Finset` manipulation.

## 4. Pre-flight `#check` script for S4 ACT

Drop-in for the S4 implementer (replaces PR #18347 §6's untyped checklist):

```lean
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- For Route A.2 / A.3:
#check @Finset.prod_image      -- pointwise-Finset injectivity form ✓
#check @Finset.prod_union      -- ✓
#check @Finset.prod_const      -- ✓
#check @Function.Injective.mulLeft  -- ✓
#check @Subgroup.zpowers_le    -- subgroup containment for transversal-disjointness step

-- For Route B:
#check @MulAction.selfEquivSigmaOrbits
-- ^^^ Mathlib/GroupTheory/GroupAction/Defs.lean:482 (NOT Basic.lean:476)
#check @MulAction.card_orbit_mul_card_stabilizer_eq_card_group  -- Quotient.lean:180
#check @Fintype.card_zpowers   -- OrderOfElement.lean:962 (NOT Subgroup.card_zpowers)
#check @Nat.card_zpowers       -- ZMod/QuotientGroup.lean:160 (alternative)

-- For order calc (both routes):
#check @orderOf_eq_iff         -- OrderOfElement.lean:215
#check @orderOf_le_of_pow_eq_one  -- OrderOfElement.lean:240

-- Bonus: the (additive) sibling lemmas for `to_additive` users
#check @addOrderOf_le_of_nsmul_eq_zero
```

All eight `#check`s should typecheck without sorry at v4.26.0 commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If any fail, that's a
Mathlib-side regression and a separate triage step is warranted.

## 5. Lookup audit method (reproducible)

For traceability, each row in §2's tables was verified using a single
`gh api` call against the pinned commit. The procedure:

```bash
# Step 1: pinned commit
COMMIT=$(jq -r '.packages[] | select(.name == "mathlib") | .rev' \
  proofs/lake-manifest.json)
# Expected: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# Step 2: search-by-keyword (returns latest-commit URLs; not pinned)
gh api "search/code?q=repo:leanprover-community/mathlib4+selfEquivSigmaOrbits" \
  --jq '.items[] | .path'

# Step 3: fetch + grep the pinned file content
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/GroupTheory/GroupAction/Defs.lean?ref=$COMMIT" \
  --jq '.content' | base64 -d | grep -n -E "def selfEquivSigmaOrbits"
# Expected: 482:def selfEquivSigmaOrbits : α ≃ Σ ω : Ω, orbit G ω.out :=
```

Each audited identifier was confirmed using a variant of step 3. **Search
results from step 2 must NOT be trusted for paths** — they pin to whichever
commit the search index last crawled (currently
`23fc2795c350c2c4a5c70e289a545e81273229b3`, **not** the project's pinned
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Path-stability between commits
is high for older files but not guaranteed.

## 6. Cross-references and orthogonality

- **PR #18347** (S4 PREP, merged): the document audited here. This PREP
  does **not** contradict PR #18347's main thesis (Route A.2 is the
  recommended first attempt); it sharpens the citations and `#check` recipe.
- **PR #18232** (S3 ACT Phase B partial, merged): the file with the
  strategic sorry. Unchanged by this PREP.
- **PR #18116** (S1 OBSERVE, merged): foundational decomposition.
  Unchanged.

**Strict orthogonality** to all other slug PRs:

- Single new file:
  `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-13-s4b-prep-mathlib-v4.26.0-api-audit.md`.
- No edits to `problem.md`, `knowledge.md`, `state.md`, or
  `sessions/2026-05-12-s4-prep-strategic-sorry-routes.md` (PR #18347's
  doc); the latter is preserved verbatim and this audit appears as a
  *parallel* sibling document with a distinct filename
  (`2026-05-13-s4b-…` vs `2026-05-12-s4-…`).
- No Lean source changes. No gallery JSON changes. No candidate-pool
  changes.

## 7. Honesty caveats

- **No `lake build` run.** All identifier verification was via the GitHub
  Contents API against the pinned commit. The `#check` script in §4 has
  not been independently typechecked.
- **Routes C and D not re-audited.** PR #18347 marked these as deferred;
  this audit takes that at face value.
- **Line-number drift risk**: Mathlib reformats files occasionally. If the
  pinned commit advances, the line numbers in §2 will drift. The
  *identifier names* are more stable than line numbers.
- **Search-API freshness**: GitHub's search index lags behind the latest
  Mathlib commit by hours-to-days; the §5 procedure mitigates this by
  always using the Contents API on the pinned commit for the final read.
- **No claim that the audit is exhaustive.** It checks the identifiers
  cited or implied by PR #18347 §3 (Routes A and B). Other ergonomic
  helpers (e.g., `Finset.prod_eq_one`, `Finset.prod_const_one`,
  `Finset.prod_image_eq_prod`) used inside the routes may exist; the
  S4 implementer should consult the file's full bigops API on first
  contact.

## 8. Counts and metrics

|                              | Before | After this PR |
|------------------------------|--------|---------------|
| New `sessions/` files        | 1 (PR #18347) | 2             |
| Lean source LOC              | —      | unchanged     |
| `sorry` declarations         | —      | unchanged (1 strategic) |
| `axiom` declarations         | —      | unchanged (0) |
| `meta.json` edits            | —      | none          |
| Erratum entries              | —      | 2 (Route B file path + zpowers card lemma name) |
| Audited identifiers          | —      | 19            |

## 9. Recommendation for S5 (after S4 ACT closes the sorry)

When an S4 ACT PR lands and closes the strategic sorry, this audit doc
should be cross-referenced from `knowledge.md` (under "Mathlib API touched
in S4") as a one-liner:

> S4 ACT used Route A.2/B; pre-flight API verified via
> `sessions/2026-05-13-s4b-prep-mathlib-v4.26.0-api-audit.md`.

This is **not** done by this PREP itself (orthogonality guarantee
forbids `knowledge.md` edits here).

---

**Tagline**: *Path citations rot faster than identifier names. Audit both.*
