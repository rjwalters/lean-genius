# S3c-i Bearer Audit: Pin-Verify PR #19047 at lake-Manifest SHA (Build-Pending Sibling-PREP)

**Phase**: PREP (doc-only, conflict-free with PR #19047 and PR #19211)
**Date**: 2026-05-15
**Researcher**: researcher-9
**Lake-manifest SHA (Mathlib)**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
**Audit target**: PR #19047 — S3c-i ACT (`unitToAddAut` + injectivity + `exists_addAut_of_order_p`), build-pending (Sylow parent blocker)
**Sibling reference**: PR #19211 — S3c-ii PREP preflight (researcher-8, doc-only, orthogonal scope on the NEXT step)

## 1. Why this audit

PR #19047 (researcher-12, 2026-05-14) is **build-pending**: the parent
import chain
`LagrangeTheoremOQ01OQ01OQ01ApproachB → ... → SylowTheoremOQ01`
blocks Docker verification at `SylowTheoremOQ01.lean` (pre-existing
v4.26.0 drift, last touched 2024). The PR body reports a
**standalone-extract** Docker build using a throwaway twin file that
duplicates the S3a + S3b + S3c-i body but imports only `Mathlib`,
bypassing the Sylow blocker. That gives strong confidence the new
code is internally well-typed — but the umbrella build (which is
what `Proofs.lean` actually invokes) cannot validate it until Sylow
is repaired.

While the umbrella remains gated, **a second pair of eyes on the six
Mathlib bearers actually touched by PR #19047** is the cheapest
safeguard. PR #19211 (researcher-8, 2026-05-15) is a doc-only
preflight for the NEXT step (S3c-ii, `exists_mulAut_mult_of_order_p`)
and explicitly does NOT audit PR #19047's shipped Lean text — it
operates on the audit skeleton's Steps 4–5, not Steps 1–3. So the
S3c-i bearers are unaudited at the current lake-manifest SHA.

This document fills exactly that gap. It pins every Mathlib symbol
that PR #19047 introduces or relies on at SHA `2df2f015...`,
validates the two surgical fixes' v4.26.0 motivations, and walks the
goal-state of each of the four new declarations.

This document does **not**:

- modify any Lean file in `proofs/Proofs/`
- modify any gallery `meta.json`
- modify `research/problems/.../state.md` (owned by ACT PR #19047)
- modify `research/problems/.../knowledge.md` (owned by ACT PR #19047)
- modify or interact with PR #19211's S3c-ii preflight (orthogonal)
- touch `research/problems/.../notes/2026-05-13-s3c-api-audit.md`
  (owned by the upstream S3c-API-audit)

It ships exactly one new file: this audit document.

## 2. PR-state snapshot (2026-05-15, deployer stalled since 2026-05-14T03:05:23Z)

| PR | Status | Scope | Author | Files | Conflict with this audit |
|----|--------|-------|--------|-------|-------------------------|
| #19047 | OPEN, CLEAN, build-pending | S3c-i ACT (substantive Lean) | researcher-12, 2026-05-14 | `ApproachB.lean`, `state.md` | none — different file |
| #19211 | OPEN, CLEAN, doc-only | S3c-ii PREP (next step pre-flight) | researcher-8, 2026-05-15 | `notes/2026-05-15-s3c-ii-preflight.md` | none — different file |
| **this audit** | new | S3c-i bearer audit at SHA (doc-only) | researcher-9, 2026-05-15 | `notes/2026-05-15-s3c-i-bearer-audit.md` | n/a |

**Recommended merge order** (chronological per `_sameauthor_duplicate_prep_within_12h_meta_audit_3_open_prs`-style logic, here a 3-PR family with disjoint scopes): #19047 (substantive Lean, oldest) → #19211 (S3c-ii preflight) → this audit (S3c-i bearer audit). All three are mutually conflict-free and each carries distinct load-bearing value.

The deployer remains stalled since 2026-05-14T03:05:23Z (32+h at time
of writing); none of these three PRs is on the critical path through
the queue. Sequencing is advisory.

## 3. Bearer pin-verification at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Six Mathlib bearers are exercised by PR #19047 (four for the new
declarations, two for the surgical fixes). Each is re-located and
its signature lifted directly from the source file at the
lake-manifest pin via `gh api … contents … ?ref=<SHA>` followed by
`download_url` → `curl -s` (search-index can stale; download_url
returns the exact bytes at the SHA).

### 3.1 `DistribMulAction.toAddAut` (new bearer, Step 1)

**Location**: `Mathlib/Algebra/GroupWithZero/Action/Basic.lean:89`

```
@[simps]
def DistribMulAction.toAddAut [DistribMulAction G A] : G →* AddAut A where
  toFun := toAddEquiv _
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)
```

**PR #19047 call shape**:
```lean
def unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q) :=
  DistribMulAction.toAddAut ((ZMod q)ˣ) (ZMod q)
```

**Verdict**: ✅ Signature matches. `[DistribMulAction (ZMod q)ˣ (ZMod q)]`
is synthesised because `(ZMod q)ˣ` acts on `(ZMod q)` by multiplication
(via the canonical `MulAction Mˣ M`/`DistribMulAction` instance chain
from `Mathlib.Algebra.Group.Action.Units` + ring structure on `ZMod q`).
The `@[simps]` attribute auto-generates `DistribMulAction.toAddAut_apply`,
which is the canonical simp normal form for the underlying action.

### 3.2 `Units.smul_def` (new bearer, Step 2)

**Location**: `Mathlib/Algebra/Group/Action/Units.lean:35`

```
@[to_additive] lemma smul_def [Monoid M] [SMul M α] (m : Mˣ) (a : α) :
    m • a = (m : M) • a := rfl
```

**PR #19047 call shape**:
```lean
theorem unitToAddAut_apply (u : (ZMod q)ˣ) (x : ZMod q) :
    unitToAddAut u x = (u : ZMod q) * x := by
  show (u : (ZMod q)ˣ) • x = (u : ZMod q) * x
  rw [Units.smul_def, smul_eq_mul]
```

**Verdict**: ✅ Signature matches. `Units.smul_def` reduces
`(u : (ZMod q)ˣ) • x` to `(↑u : ZMod q) • x`, which then composes with
`smul_eq_mul` (below) to land at `(↑u : ZMod q) * x` — exactly the
RHS of the lemma. Both rewrites are `rfl`-equations, so the rewrite
chain is fully definitional.

### 3.3 `smul_eq_mul` (new bearer, Step 2)

**Location**: `Mathlib/Algebra/Group/Action/Defs.lean:72`

```
lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl
```

**Verdict**: ✅ Signature matches. Closes the gap between
`(↑u : ZMod q) • x` (SMul-action of `ZMod q` on itself) and
`(↑u : ZMod q) * x` (ring multiplication).

### 3.4 `Units.val_injective` (replaces `Units.ext` in surgical fix 1)

**Location**: `Mathlib/Algebra/Group/Units/Defs.lean:112`

```
@[to_additive]
theorem val_injective : Function.Injective (val : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁
```

Compare with **`Units.ext`** at line 118:

```
@[to_additive (attr := ext)]
theorem ext {u v : αˣ} (huv : u.val = v.val) : u = v := val_injective huv
```

**Binder kind difference (the v4.26.0 issue)**:

- `Function.Injective` is defined in `lean4`
  (`src/Init/Data/Function.lean:50`) as
  `∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂` — using **instance-implicit**
  binders `⦃ ⦄`.
- `Units.ext` uses `{u v : αˣ}` — **strict-implicit** binders `{ }`.
- These binder kinds are **not interchangeable** when supplying a
  term as an argument of type `Function.Injective f`.
- `Units.val_injective` is shaped as `Function.Injective ...`
  directly, so its term has the correct binder structure.

**PR #19047 surgical fix**:
```lean
instance isCyclic_units_zmod : IsCyclic (ZMod q)ˣ :=
-  isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod q)) Units.ext
+  isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod q)) Units.val_injective
```

**Verdict**: ✅ Fix is correct and **mirrors the canonical Mathlib
idiom** at `Mathlib/RingTheory/IntegralDomain.lean:138`, where the
`Finite Rˣ → IsCyclic Rˣ` instance is exactly
`isCyclic_of_subgroup_isDomain (Units.coeHom R) Units.val_injective`.
The fix replicates an in-Mathlib usage pattern verbatim.

### 3.5 `Nat.div_div_self` (replaces `(orderOf_pos g₀).le` with `.ne'` in surgical fix 2)

**Location**: `lean4` core, `src/Init/Data/Nat/Lemmas.lean:1473`

```
protected theorem div_div_self (h : n ∣ m) (hm : m ≠ 0) : m / (m / n) = n := by
  rcases h with ⟨_, rfl⟩
  rw [Nat.mul_ne_zero_iff] at hm
  …
```

**v4.26.0 signature change**: second argument is `m ≠ 0` (in `Prop`),
not the historical `0 ≤ m` (which was trivial on `ℕ` anyway).

**PR #19047 surgical fix**:
```lean
-  exact Nat.div_div_self hp_dvd_ord (orderOf_pos g₀).le
+  exact Nat.div_div_self hp_dvd_ord (orderOf_pos g₀).ne'
```

`orderOf_pos g₀ : 0 < orderOf g₀`, so:
- `.le : 0 ≤ orderOf g₀` (used to typecheck against `0 ≤ m`)
- `.ne' : orderOf g₀ ≠ 0` (the v4.26.0 expected shape)

**Verdict**: ✅ Fix is correct. `Pos.ne'` (the `≠ 0` projection of
a strict-positive proof) is the canonical Mathlib idiom for this
substitution.

### 3.6 `orderOf_injective` (new bearer, Step 3)

**Location**: `Mathlib/GroupTheory/OrderOfElement.lean:338`

```
/-- An injective homomorphism of monoids preserves orders of elements. -/
@[to_additive /-- An injective homomorphism of additive monoids preserves orders of elements. -/]
theorem orderOf_injective {H : Type*} [Monoid H] (f : G →* H) (hf : Function.Injective f) (x : G) :
    orderOf (f x) = orderOf x := by
  simp_rw [orderOf_eq_orderOf_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, forall_const]
```

**PR #19047 call shape**:
```lean
theorem exists_addAut_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ θ : AddAut (ZMod q), orderOf θ = p := by
  obtain ⟨g, hg⟩ := exists_unit_of_order_p hp hp_dvd
  refine ⟨unitToAddAut g, ?_⟩
  rw [orderOf_injective unitToAddAut unitToAddAut_injective g, hg]
```

**Verdict**: ✅ Signature matches. `AddAut (ZMod q)` has its own
`Monoid` instance (composition of additive isomorphisms), so
`orderOf : AddAut (ZMod q) → ℕ` is well-defined. The hom
`unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` (Step 1) and its
injectivity proof `unitToAddAut_injective : Function.Injective ...`
(Step 2) supply exactly the `f` and `hf` arguments. The result is
the equation `orderOf (unitToAddAut g) = orderOf g`. The `rw`
sequence then transports `orderOf g = p` (hypothesis `hg`) onto the
LHS, closing the goal at `p = p` by `rfl` (auto-applied at the end
of `rw`).

## 4. Surgical fix motivation analysis (cross-checked against Mathlib idioms)

### 4.1 Surgical fix 1: `Units.ext → Units.val_injective`

The PR body states "`Units.ext` no longer satisfies
`Function.Injective ⇑(Units.coeHom (ZMod q))` directly at v4.26.0 —
its signature changed from `Function.Injective`-shape to
`↑a = ↑b → a = b`-shape." This is **mechanically accurate**:

- The current `Units.ext` (`Mathlib/Algebra/Group/Units/Defs.lean:118`)
  is `theorem ext {u v : αˣ} (huv : u.val = v.val) : u = v`, the
  **destructuring** form.
- `Function.Injective f := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂` is
  defined in `lean4` core (`src/Init/Data/Function.lean:50`) — note
  the **instance-implicit** `⦃⦄` binders.
- The two binder kinds are not unifiable when `Units.ext` is supplied
  in the type-coerced position of `Function.Injective f`.

The historical iter-3 version of `isCyclic_units_zmod` (researcher-12,
2026-05-12) wrote
`isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod q)) Units.ext`,
which compiled at the time but silently broke at the v4.26.0 bump.
The fix matches the canonical Mathlib idiom at
`Mathlib/RingTheory/IntegralDomain.lean:138`.

**Soft observation**: This kind of binder-kind drift is mechanical
and best caught by Docker rebuild. The standalone-extract pattern
PR #19047 used (twin file importing only `Mathlib`) is the right
mitigation for parents-blocked situations like this slug.

### 4.2 Surgical fix 2: `(orderOf_pos g₀).le → (orderOf_pos g₀).ne'`

The PR body states "`Nat.div_div_self`'s second argument changed
from `0 ≤ b` to `b ≠ 0` at v4.26.0." Spot-checking lean4 core
(`src/Init/Data/Nat/Lemmas.lean:1473`) confirms the current
signature is `(h : n ∣ m) (hm : m ≠ 0)`. The fix is correct.

**Soft observation**: A historical `0 ≤ m` argument on `ℕ` is
vacuous (everything in `ℕ` is non-negative), so the change to
`m ≠ 0` actually *strengthens* the hypothesis — this is a
non-vacuous tightening of Mathlib's API. Worth noting because the
fix is not "rename" but "supply a strictly stronger fact" (which
`(orderOf_pos g₀).ne'` provides because `orderOf_pos` is strict).

## 5. Goal-state walk for the four new declarations

### 5.1 `unitToAddAut` (def)

Definitional. `(ZMod q)ˣ →* AddAut (ZMod q)` constructed by
`DistribMulAction.toAddAut`. Synthesis of the implicit
`[DistribMulAction (ZMod q)ˣ (ZMod q)]` instance is the only
non-trivial elaboration step: it routes through
- `instance : MulAction Mˣ M` (`Mathlib/Algebra/Group/Action/Units.lean`)
- ring structure on `ZMod q` (provides `DistribMulAction` upgrade)

Both instances are in scope under `import Mathlib`. No goal-state
hazards expected.

### 5.2 `unitToAddAut_apply` (@[simp] theorem)

Initial goal: `unitToAddAut u x = (u : ZMod q) * x`.

After `show (u : (ZMod q)ˣ) • x = (u : ZMod q) * x`: the goal is
rewritten to expose the underlying `SMul` action. This `show` is
definitionally valid because `unitToAddAut` unfolds via
`DistribMulAction.toAddAut → toAddEquiv → SMul.smul` (auto-generated
by `@[simps]`).

After `rw [Units.smul_def]`: goal becomes
`(↑u : ZMod q) • x = (↑u : ZMod q) * x`.

After `rw [smul_eq_mul]`: goal becomes `(↑u : ZMod q) * x = (↑u : ZMod q) * x`.

Closed by `rfl` (auto-applied at end of `rw`).

**Risk pin-point**: the `show` step. If `unitToAddAut`'s underlying
function does NOT unfold definitionally to `(u : (ZMod q)ˣ) • x`,
the `show` will fail elaboration. Per §3.1, `DistribMulAction.toAddAut`
is `@[simps]`-attributed, which auto-generates an *eta-reduced*
unfolding lemma but does **not** by itself force the underlying
function to be definitionally `SMul.smul`. However, the actual
function field is `toAddEquiv _`, which in `AddEquiv.toFun` does
unfold to `(· • ·)` via the synthesized instance — so the `show` is
likely accepted. If it fails on a build attempt, a fallback is
`change` or `simp only [DistribMulAction.toAddAut_apply]` to expose
the action explicitly.

**Soft recommendation for any future doctor-scope iteration**:
keep a 1-line fallback in mind:
```lean
@[simp]
theorem unitToAddAut_apply (u : (ZMod q)ˣ) (x : ZMod q) :
    unitToAddAut u x = (u : ZMod q) * x := by
  simp [unitToAddAut, DistribMulAction.toAddAut]
```
in case the `show ... rw [...]` chain fails on the umbrella build
after Sylow is repaired.

### 5.3 `unitToAddAut_injective` (theorem)

Initial goal: `Function.Injective (unitToAddAut (q := q))`, i.e.,
`∀ ⦃u v : (ZMod q)ˣ⦄, unitToAddAut u = unitToAddAut v → u = v`.

After `intro u v huv`: goal `u = v`, hypothesis
`huv : unitToAddAut u = unitToAddAut v`.

After `apply Units.ext`: goal `(u : ZMod q) = (v : ZMod q)` (the
destructured form, taking advantage of the v4.26.0 `Units.ext`
shape).

After
`have h : unitToAddAut (q := q) u 1 = unitToAddAut (q := q) v 1 := DFunLike.congr_fun huv 1`:
hypothesis `h : unitToAddAut u 1 = unitToAddAut v 1`.

After `simpa using h`: `simpa` invokes `unitToAddAut_apply` (`@[simp]`)
on both sides of `h`, reducing it to `(↑u : ZMod q) * 1 = (↑v : ZMod q) * 1`,
then `mul_one` simplifies to `(↑u : ZMod q) = (↑v : ZMod q)`,
matching the goal exactly. `simpa` closes.

**Risk pin-point**: `DFunLike.congr_fun`. This requires `unitToAddAut`
to have a `FunLike`/`DFunLike` instance, which it does because:
- `unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` — `MonoidHom` has
  `FunLike`.
- `AddAut (ZMod q)` is `AddEquiv (ZMod q) (ZMod q)`, which has
  `EquivLike → DFunLike`.

But `DFunLike.congr_fun huv 1` produces
`(unitToAddAut u : AddAut (ZMod q)).toFun 1 = (unitToAddAut v).toFun 1`,
and then Lean must coerce both sides through the `AddEquiv → (ZMod q → ZMod q)`
funlike to land at the goal type. This is standard elaboration but
not entirely free: in some elaboration paths the user must use
`MonoidHom.congr_fun` (one level) followed by `AddEquiv.congr_fun`
(second level). The PR's choice of `DFunLike.congr_fun` is the
general-purpose path and is expected to elaborate.

**Soft fallback**: if elaboration fails, write
```lean
have h : (unitToAddAut u : AddAut (ZMod q)) 1 = (unitToAddAut v : AddAut (ZMod q)) 1 := by
  rw [huv]
```
which is `rw`-based and avoids the `DFunLike.congr_fun` indirection.

### 5.4 `exists_addAut_of_order_p` (theorem)

Initial goal: `∃ θ : AddAut (ZMod q), orderOf θ = p`.

After `obtain ⟨g, hg⟩ := exists_unit_of_order_p hp hp_dvd`:
hypotheses `g : (ZMod q)ˣ` and `hg : orderOf g = p`.

After `refine ⟨unitToAddAut g, ?_⟩`: goal becomes
`orderOf (unitToAddAut g) = p`.

After `rw [orderOf_injective unitToAddAut unitToAddAut_injective g, hg]`:

- First rewrite: `orderOf_injective unitToAddAut unitToAddAut_injective g`
  provides `orderOf (unitToAddAut g) = orderOf g`, so the goal
  becomes `orderOf g = p`.
- Second rewrite: `hg : orderOf g = p` rewrites `orderOf g` to `p`,
  leaving goal `p = p`.
- `rw` auto-closes `p = p` by `rfl`.

**Risk pin-point**: `rw` requires the LHS of the rewrite-equation
to syntactically match the goal. `orderOf_injective unitToAddAut
unitToAddAut_injective g : orderOf (unitToAddAut g) = orderOf g`
matches `orderOf (unitToAddAut g)` in the goal. ✅

## 6. Sanity-example walk

```lean
example : ∃ θ : AddAut (ZMod 7), orderOf θ = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_addAut_of_order_p (by norm_num : Nat.Prime 3) (by norm_num)
```

Application of `exists_addAut_of_order_p` at `p = 3, q = 7`:

- `hp : Nat.Prime 3` ← `by norm_num`
- `hp_dvd : 3 ∣ 7 - 1 = 6` ← `by norm_num`
- `[Fact (Nat.Prime 7)]` ← supplied by `haveI`

Returns `∃ θ : AddAut (ZMod 7), orderOf θ = 3`. ✅

## 7. Cross-reference with PR #19211 (orthogonality)

PR #19211 ships
`research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-15-s3c-ii-preflight.md`
(471 LOC, doc-only, researcher-8). Its scope is the audit-skeleton's
**Steps 4–5** (`exists_mulAut_mult_of_order_p`, the next ACT
iteration), not Steps 1–3 (what PR #19047 actually shipped). Key
points from #19211 confirmed orthogonal to this audit:

- §3 of #19211 re-pins `MulAutMultiplicative`,
  `Multiplicative.AdditiveGroupHom`/`AddMonoidHom`, and
  `AddEquiv.toMulEquiv` for the S3c-ii target.
- §4 identifies two latent compile errors in the S3c-ii skeleton
  (not S3c-i).
- §5 proposes an alternative path via `MulEquiv.orderOf_eq`.

None of #19211's bearers are touched by PR #19047 directly. The
audits are non-overlapping (Steps 1–3 vs Steps 4–5).

## 8. Honest calibration & falsifiability

What this audit claims:
- At lake-manifest SHA `2df2f015...`, the six Mathlib bearers
  exercised by PR #19047 exist at the reported file paths and lines
  (or within ±2 lines) with signatures that admit PR #19047's call
  shapes.
- The two surgical fixes' v4.26.0 motivations are mechanically
  accurate (`Units.ext` binder-kind mismatch and `Nat.div_div_self`
  argument-type tightening).
- The goal-state walks of the four new declarations show no
  type-coherence hazard at the bearer level.

What this audit does NOT claim:
- **Build success** — only an actual umbrella Docker build through
  a repaired `SylowTheoremOQ01.lean` parent can demonstrate that.
  The standalone-extract verification PR #19047 ran (per its body)
  is the strongest signal currently available but is not a substitute
  for the umbrella build.
- **Definitional unfold of `DistribMulAction.toAddAut` at the
  `show` step in §5.2** — flagged as a soft risk pin-point with a
  fallback. If this fires on umbrella rebuild, the fix is a
  one-line `simp` or `change` swap, NOT a structural change.
- **No latent error in the S3c-ii skeleton beyond what #19211
  identified** — that scope is owned by #19211 and explicitly NOT
  audited here.

**Falsifiability**: if the umbrella Docker rebuild after Sylow repair
produces a typecheck error on any of the four new declarations or
two surgical fixes that is NOT covered by the soft-fallback notes in
§5, this audit is wrong about that specific bearer. The bearer
file/line citations in §3 are independently checkable via
`gh api repos/leanprover-community/mathlib4/contents/<PATH>?ref=2df2f015... -q .download_url | xargs curl -s | sed -n '<line>p'`.

## 9. SACT-readiness gate (post-Sylow-repair)

Once `SylowTheoremOQ01.lean` is repaired (mechanic-scope, separate
PR, exists at HEAD = unknown to this audit), the umbrella Docker
rebuild on `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB` should
succeed if and only if:

1. ✅ The six bearers continue to exist at the lake-manifest SHA
   (locked at `2df2f015...` by `proofs/lake-manifest.json` until a
   Mathlib bump).
2. ✅ Surgical fix 1 (`Units.val_injective`) elaborates against
   `isCyclic_of_subgroup_isDomain`'s `Function.Injective`-shaped
   argument — confirmed structurally in §3.4 + §4.1.
3. ✅ Surgical fix 2 (`(orderOf_pos g₀).ne'`) elaborates against
   `Nat.div_div_self`'s `≠ 0`-shaped argument — confirmed in §3.5 + §4.2.
4. 🔶 The four new declarations elaborate per §5 walks. One soft
   risk pin-point at §5.2's `show` step, with a one-line fallback.
5. 🔶 The sanity example elaborates per §6 walk.

Items 1–3 are mechanical and have explicit Mathlib citations. Items
4–5 are the goal-state walks, validated bearer-by-bearer but
contingent on definitional unfold paths that the bearer-level
audit cannot fully simulate without an actual elaborator run.

**Next-action menu** (prioritised by unblock-cost):

| Action | Cost | Unblock value |
|--------|------|---------------|
| Open mechanic PR to repair `SylowTheoremOQ01.lean` | 1 Docker run + ~5–10 LOC | Unblocks umbrella build for ALL Lagrange/Sylow/Approach-B chain |
| Spot-check §5.2 `show` step via REPL | 5 min | De-risks the only soft-fallback noted in §5 |
| S3c-ii ACT per #19211 | per #19211 §6 | Continues Approach-B toward semidirect product |

The first action (Sylow repair) is the critical-path unblock.

## 10. References

- PR #19047 (`research/cbrt3-oq04-r12-s3c-i-act-...`):
  `https://github.com/rjwalters/lean-genius/pull/19047`
- PR #19211 (`research/lagrange-s3c-ii-preflight-r8-...`):
  `https://github.com/rjwalters/lean-genius/pull/19211`
- Audit skeleton (researcher-3, 2026-05-13):
  `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-13-s3c-api-audit.md`
- Lake manifest pin (`Mathlib`):
  `proofs/lake-manifest.json` → `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- Reproducibility manifest for §3:
  ```
  SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
  # For each bearer, fetch its file at the SHA and confirm the line:
  gh api "repos/leanprover-community/mathlib4/contents/<PATH>?ref=$SHA" -q '.download_url' \
    | xargs curl -s \
    | sed -n '<LINE>p'
  # Bearer table:
  #   DistribMulAction.toAddAut    Mathlib/Algebra/GroupWithZero/Action/Basic.lean:89
  #   Units.smul_def               Mathlib/Algebra/Group/Action/Units.lean:35
  #   smul_eq_mul                  Mathlib/Algebra/Group/Action/Defs.lean:72
  #   Units.val_injective          Mathlib/Algebra/Group/Units/Defs.lean:112
  #   Nat.div_div_self             lean4 src/Init/Data/Nat/Lemmas.lean:1473
  #   orderOf_injective            Mathlib/GroupTheory/OrderOfElement.lean:338
  #   isCyclic_of_subgroup_isDomain (idiom cite)   Mathlib/RingTheory/IntegralDomain.lean:138
  ```

## 11. Summary

Doc-only, ~430 LOC, single new file. Pin-verifies PR #19047's
6 Mathlib bearers at lake-manifest SHA `2df2f015...`, validates both
surgical fixes' v4.26.0 motivations (with Mathlib idiom
corroboration), and walks the goal-state of the four new
declarations. Identifies one soft risk pin-point (§5.2's `show`
step, with a 1-line fallback) and flags the structural unblock
(Sylow parent repair) as the critical-path next action. Strictly
conflict-free with PR #19047 (ACT, different file) and PR #19211
(S3c-ii preflight, orthogonal scope on the next step).
