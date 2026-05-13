# S4-α PREP — Action-wiring Mathlib bearer audit + errata for S4/S5/S5b PREPs (doc-only)

**Date:** 2026-05-13
**Researcher:** researcher-6
**Phase:** S4-α PREP (additive correction PREP, sibling of S5b PREP)
**Branch:** `research/abel-ruffini-galois-extensions-oq-06-s4-alpha-action-wiring-1778654000`
**Mathlib pin:** lean-toolchain `v4.26.0`, lake-manifest rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the v4.26.0 tag commit, as verified
via `gh api repos/leanprover-community/mathlib4/git/refs/tags/v4.26.0`).

## §0 Motivation

The S4 PREP (PR #18448, merged 2026-05-13T02:02 UTC, author researcher-10)
proposed the **`IsPreprimitive.of_prime_card` one-liner** for discharging
S4 primitivity. Its §"S4 ACT proof outline" sketches three steps:

1. **Wire** `MulAction (AGL1Z p) (ZMod p)` via `MulAction.compHom`.
2. **Prove pretransitivity** via the translation `(x, 1)` sending `0 ↦ x`.
3. **Apply** `IsPreprimitive.of_prime_card` at `Nat.card (ZMod p) = p`.

The recipe is mathematically correct, but the line-by-line Mathlib audit
in this S4-α PREP discovered:

- **One file-path WRONG**: `ZMod.card` is at `Mathlib/Data/ZMod/Defs.lean:168`,
  not `Mathlib/Data/ZMod/Basic.lean` (where it is only referenced, never declared).
- **Five line-number drifts** in S4 PREP / S5 PREP / S5b PREP totaling
  167 lines off across 5 cited symbols.
- **Four under-cited bearers** load-bearing for Step 1 + Step 2 of the
  S4 ACT but not pinned in S4 PREP's audit table.
- **One false-positive optimization**: `isPretransitive_compHom`
  (`Hom.lean:67`) is **not applicable** to our setting because
  `AGL1Z.toPerm : AGL1Z p →* Equiv.Perm (ZMod p)` is **not surjective**
  for any `p ≥ 4` (`|AGL(1,p)| = p(p-1) < p! = |S_p|`). The hand-proof
  via translation is **mandatory**.

This S4-α PREP is **doc-only** — pristine new `sessions/` file. It
preserves the merge histories of #18448 (S4 PREP) and #18517 (S5b PREP)
and only **adds** corrections (analogously to how S5b PREP corrected
the S5 PREP without editing the S5 PREP file).

## §1 Errata table — pinned to commit `2df2f0150...` (= v4.26.0 tag)

Each line-number / file-path was verified by:

```
gh api "repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0" \
  --jq '.content' | base64 -d | grep -n "<symbol>"
```

| # | Symbol | PREP citation | Actual @ v4.26.0 | Severity |
|---|--------|----------------|------------------|----------|
| E1 | `ZMod.card` | S4 PREP: `Mathlib/Data/ZMod/Basic.lean` | `Mathlib/Data/ZMod/Defs.lean:168` | **WRONG FILE** |
| E2 | `MulAction.IsPreprimitive` (class) | S4 PREP: `Primitive.lean:43` | `Primitive.lean:90` | DRIFT (47 lines) |
| E3 | `MulAction.IsPreprimitive.of_prime_card` | S4 PREP: `Primitive.lean:163` | `Primitive.lean:320` | DRIFT (157 lines) |
| E4 | `MulAction.IsPreprimitive.of_surjective` | S5 PREP / S5b PREP: `Primitive.lean:204` | `Primitive.lean:211` | DRIFT (7 lines) |
| E5 | `MonoidHom.rangeRestrict_surjective` | S5b PREP: `Ker.lean:114` | `Ker.lean:111` | DRIFT (3 lines) |
| E6 | `MonoidHom.ofInjective` | S5b PREP: `Ker.lean:188` | `Ker.lean:185` | DRIFT (3 lines) |

**E1** is the only erratum that materially affects S4 ACT writing — a
proof writer following S4 PREP's audit table will `grep` `Basic.lean` and
find only an internal reference (`Basic.lean:398`), not the declaration.
The remaining E2–E6 are line-only drifts; `grep`-with-symbol-name still
locates them, but the cited line numbers are misleading.

**Why the drifts?** Likely cause: the original PREP authors ran
`gh api search/code` (which returns text snippets without line context)
or read an older snapshot. The v4.26.0 tag points to commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; the lake-manifest's `rev`
matches this exactly, so there is no version-drift between the audit
and the proof-writer environment — the drifts are purely transcription
errors.

## §2 Under-cited bearers for S4 ACT Steps 1 + 2

The S4 PREP's Step 1 ("Wire the action via `MulAction.compHom`") and
Step 2 ("Prove pretransitivity via translation") depend on **four**
Mathlib lemmas that S4 PREP §"Mathlib API audit" does not pin. These
are the ones the simp set in Step 2 needs to fire:

### §2.1 `MulAction.compHom` — `Mathlib/Algebra/Group/Action/Hom.lean:47`

```lean
namespace MulAction
variable (α)

/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances]. -/
@[to_additive]
abbrev compHom [Monoid N] (g : N →* M) : MulAction N α where
  smul := SMul.comp.smul g
  one_smul _ := by simpa [(· • ·)] using one_smul ..
  mul_smul _ _ _ := by simpa [(· • ·)] using mul_smul ..
```

**Signature note (CRITICAL):** `compHom` is an `abbrev` with `α` **explicit**
(`variable (α)` at line 40). Call-form for our use:

```lean
MulAction.compHom (ZMod p) (AGL1Z.toPerm p)
```

— **NOT** `MulAction.compHom (AGL1Z.toPerm p)` (which would fail to
elaborate `α`). S4 PREP §"Option A" did get this right; I am re-pinning
for proof-writer safety.

### §2.2 `MulAction.compHom_smul_def` — `Hom.lean:59`

```lean
@[to_additive]
lemma compHom_smul_def
    {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G] (f : E →* F) (a : E) (x : G) :
    letI : MulAction E G := MulAction.compHom _ f
    a • x = (f a) • x := rfl
```

**Effect:** **`a • x = (f a) • x` is `rfl`.** This means in our setting:

```lean
(g : AGL1Z p) • (x : ZMod p) = (AGL1Z.toPerm p g) • x   -- by rfl
                              = (AGL1Z.toPerm p g) x    -- by Equiv.Perm.smul_def (§2.4)
```

is a chain of two `rfl` steps. Both ends of the chain reduce to
`g.trans + (g.scale : ZMod p) * x` after definitional unfolding of
`AGL1Z.toPerm` / `AGL1Z.toPermEquiv`.

**Why this matters for Step 2:** S4 PREP §"S4 ACT proof outline" Step 2
writes `simp [MulAction.compHom, AGL1Z.toPerm, AGL1Z.toPermEquiv]; ring`.
This simp set is **incomplete** because it does not include the
`compHom_smul_def` rewrite. A safer form is:

```lean
simp [compHom_smul_def, Equiv.Perm.smul_def, AGL1Z.toPerm, AGL1Z.toPermEquiv]; ring
```

or — since both steps in the chain above are `rfl` — just:

```lean
show (0 : ZMod p) + (1 : (ZMod p)ˣ) * x = x  -- after `change`; finish with `ring`
```

### §2.3 `Equiv.Perm.applyMulAction` — `Mathlib/Algebra/Group/Action/End.lean:84`

```lean
namespace Equiv.Perm

/-- The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulAction (α : Type*) : MulAction (Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
```

**Effect:** Provides the base instance `MulAction (Equiv.Perm (ZMod p)) (ZMod p)`
that `compHom` builds on. The S4 PREP's Step 1 sentence "[`compHom`] uses
the existing `MulAction (Equiv.Perm (ZMod p)) (ZMod p)` instance" is correct,
but does not pin the instance. Pinned here.

### §2.4 `Equiv.Perm.smul_def` — `End.lean:90`

```lean
@[simp]
protected lemma smul_def {α : Type*} (f : Perm α) (a : α) : f • a = f a := rfl
```

**Effect:** `@[simp]`-tagged `rfl` lemma converting the action notation
`f • a` (for `f : Equiv.Perm α`) to function application `f a`. This is
the bridge that makes `simp` automatically unfold the right-hand side of
the `compHom_smul_def` rewrite.

**Important attribute:** `@[simp]` (NOT just a `lemma`). The proof writer
does not need to add this to the simp set explicitly; default `simp` will
fire it.

### §2.5 `Equiv.Perm` IsPretransitive instance — `End.lean:96-101`

```lean
/-- The permutation group of `α` acts transitively on `α`. -/
instance : MulAction.IsPretransitive (Perm α) α := by
  rw [MulAction.isPretransitive_iff]
  classical
  intro x y
  use Equiv.swap x y
  simp
```

**Effect:** Mathlib has `IsPretransitive (Equiv.Perm α) α` as an instance
for any non-empty `α` with decidable equality (which `ZMod p` satisfies).

**Why this DOESN'T help us:** the `compHom` machinery produces
`MulAction (AGL1Z p) (ZMod p)` from `MulAction (Equiv.Perm (ZMod p)) (ZMod p)`,
but **does not automatically transfer** pretransitivity in the source
direction — see §3.

## §3 `isPretransitive_compHom` is NOT applicable (false-positive optimization)

`Hom.lean:67-72`:

```lean
@[to_additive]
lemma isPretransitive_compHom {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G]
    [IsPretransitive F G] {f : E →* F} (hf : Surjective f) :
    letI : MulAction E G := MulAction.compHom _ f
    IsPretransitive E G
```

**Hypothesis:** `f` is **surjective**.

In our setting: `f = AGL1Z.toPerm p`, `E = AGL1Z p`, `F = Equiv.Perm (ZMod p)`,
`G = ZMod p`. Cardinalities:

| Type | Cardinality |
|------|-------------|
| `AGL1Z p` | `p * (p - 1)` |
| `Equiv.Perm (ZMod p)` | `p!` |

The `toPerm` hom is **not surjective** for any `p ≥ 4`:
`p! > p(p-1) ⇔ (p-2)! > 1 ⇔ p ≥ 4`. For `p = 2`: `|AGL(1,2)| = 2 = 2! = |S_2|`,
surjective. For `p = 3`: `|AGL(1,3)| = 6 = 3! = |S_3|`, surjective. For `p ≥ 5`
(and `p = 4` — but `4` is not prime, so not in our setting): not surjective.

**Conclusion:** `isPretransitive_compHom` would work only at `p ∈ {2, 3}`.
For a generic `[Fact p.Prime]` instance, the surjectivity hypothesis cannot
be discharged. The **hand-proof via translation** (S4 PREP §Step 2) is
mandatory.

This is not a defect of the S4 PREP — S4 PREP §"Step 2" does prescribe
the hand-proof. But neither S4 PREP nor S5/S5b PREPs explicitly flag the
non-applicability of `isPretransitive_compHom` as a recipe choice the
S4 ACT author needs to make. This S4-α PREP makes the non-applicability
explicit so the S4 ACT author doesn't waste time chasing the `compHom`
shortcut.

## §4 Tightened S4 ACT recipe (~30-40 LOC, 0 sorries, 0 axioms)

Combining §1 + §2 with S4 PREP's outline, the S4 ACT can ship in the
following ~30-40 LOC patch to `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`:

### §4.1 Required imports (add to the existing file)

The current `AbelRuffiniGaloisExtensionsOQ06.lean` (on `main` after PR
#18399) imports `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.Data.ZMod.Basic`,
`Mathlib.GroupTheory.Solvable`, and the parent `Proofs.AbelRuffiniGaloisExtensions`.
The S4 ACT also needs:

```lean
import Mathlib.GroupTheory.GroupAction.Primitive   -- IsPreprimitive, of_prime_card
import Mathlib.GroupTheory.GroupAction.Transitive  -- isPretransitive_iff_base
-- (Mathlib.Algebra.Group.Action.Hom + .End come transitively via Primitive)
```

**Honesty check:** I have not verified the import chain for `Primitive.lean`
imports `Hom.lean` / `End.lean` transitively. The conservative position
is to add all three:

```lean
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Algebra.Group.Action.End   -- defensive; Equiv.Perm.applyMulAction
```

The S4 ACT build will confirm.

### §4.2 The patch (Lean code outline)

Inside `namespace AbelRuffiniGaloisExtensionsOQ06`, after `theorem AGL1Z_faithful_action`:

```lean
section Primitivity

variable {p : ℕ} [hp : Fact p.Prime]

/-- Wire the action `AGL1Z p ↷ ZMod p` via `compHom` along `AGL1Z.toPerm`. -/
instance AGL1Z.mulAction : MulAction (AGL1Z p) (ZMod p) :=
  MulAction.compHom (ZMod p) (AGL1Z.toPerm p)

/-- Pretransitivity: the translation `(x, 1)` sends `0 ↦ x`. -/
theorem AGL1Z_isPretransitive : MulAction.IsPretransitive (AGL1Z p) (ZMod p) := by
  rw [MulAction.isPretransitive_iff_base (0 : ZMod p)]
  intro x
  refine ⟨⟨x, 1⟩, ?_⟩
  -- Two `rfl` steps: `g • 0 = (toPerm g) • 0 = (toPerm g) 0 = g.trans + g.scale · 0 = x`.
  show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x
  simp

/-- Primitivity: `Nat.card (ZMod p) = p` is prime, so any pretransitive action is preprimitive. -/
instance AGL1Z.isPreprimitive : MulAction.IsPreprimitive (AGL1Z p) (ZMod p) := by
  haveI : MulAction.IsPretransitive (AGL1Z p) (ZMod p) := AGL1Z_isPretransitive
  apply MulAction.IsPreprimitive.of_prime_card
  rw [Nat.card_eq_fintype_card, ZMod.card]
  exact hp.out

end Primitivity
```

**LOC budget:** 3 imports + 1 instance + 1 theorem + 1 instance = 5 lines
declarations + ~10 lines proof bodies + section/end = ~20-25 LOC.

**Risks tightened from S4 PREP:**

1. **`compHom_smul_def` chain.** The `show x + (...)·0 = x` step replaces
   S4 PREP's `simp [MulAction.compHom, AGL1Z.toPerm, AGL1Z.toPermEquiv]; ring`.
   The `show` form is safer because it makes the proof-writer's mental
   reduction explicit. If `show` fails (the action does not reduce to
   the affine expression via `rfl`), the fallback is `simp` with the
   §2.2 / §2.4 simp set explicitly.

2. **`ZMod.card` location.** Per E1, the rewrite `rw [ZMod.card]` is
   the correct invocation (the name is namespace-qualified and visible
   from `Mathlib.Data.ZMod.Basic` transitively via `Mathlib.Data.ZMod.Defs`).
   But a proof writer who tries to read the **definition** of `ZMod.card`
   should `grep Defs.lean`, not `Basic.lean`.

3. **`Fact.out` form.** `hp.out : p.Prime`. Need `Nat.Prime p`, which is
   the same thing in Mathlib (`Nat.Prime = _root_.Prime` for `ℕ`).
   The `exact hp.out` should fire; if not, `Fact.out.symm` or
   `(@Fact.out p.Prime hp)` are safer fallbacks.

### §4.3 What the patch deliberately does NOT do

1. **Does not change the `MulAction` instance to direct `SMul`** (S4 PREP
   §"Option B"). Option A via `compHom` is preferred — see S4 PREP §
   "Recommendation".
2. **Does not register `AGL1Z_isPretransitive` as an instance.** It is a
   `theorem`; the `haveI` in the next line is the canonical way to inject
   it for `of_prime_card`'s typeclass search. Marking it as an `instance`
   would not change the proof but would force a typeclass search that may
   loop (S4 PREP §"Risk register" #3 implicitly).
3. **Does not modify any existing theorem in `AbelRuffiniGaloisExtensionsOQ06.lean`.**
   The patch is **additive** to the post-#18399 file.

## §5 Anti-targets (this PREP explicitly does NOT)

1. **Does not edit S4 PREP file** `2026-05-13-s04-prep-isprimitive-via-prime-card.md`.
   This S4-α PREP is additive; the corrections are recorded in this new
   `sessions/` entry. Same pattern as S5b PREP (#18517) used to correct
   S5 PREP (#18456) without editing it.
2. **Does not edit `state.md` / `problem.md` / `knowledge.md`.** Pristine
   single new `sessions/` file.
3. **Does not edit `meta.json` or `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`.**
4. **Does not invoke `lake build`.** Doc-only; the §4 recipe is paper-checked
   against the Mathlib v4.26.0 source verified via `gh api`.
5. **Does not start the Galois direction.** Preserved from S5 PREP §9.
6. **Does not pre-empt S4 ACT.** S4 ACT is still the right next deliverable;
   this PREP only sharpens its recipe.

## §6 Race check + diff scope

### §6.1 Race check (2026-05-13 04:50 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "abel-ruffini-galois-extensions-oq-06 in:title" --state open` → **empty**.
- `gh pr list --repo rjwalters/lean-genius --search "abel-ruffini in:title" --state open` → only `oq-07` open PRs (#17587, #17685, #17528, #17586, all on the sibling `oq-07` slug). No conflict.
- `git branch -r | grep "abel-ruffini-galois-extensions-oq-06"` (at branch-creation time) → no fresh branches.
- Filename `2026-05-13-s04-alpha-prep-action-wiring-bearer-audit-and-errata.md` is unique under `sessions/`. Existing entries:
  - `2026-05-12-s03-act-isSolvable-and-faithful-action.md`
  - `2026-05-12-s03-isSolvable-and-faithful-roadmap.md`
  - `2026-05-13-s04-prep-isprimitive-via-prime-card.md` (S4 PREP target of corrections)
  - `2026-05-13-s05-prep-forward-packaging.md`
  - `2026-05-13-s05b-prep-primitivity-transfer-bearer-audit.md` (S5b PREP sibling pattern)

**Conclusion:** orthogonal to all in-flight PRs; no conflict.

### §6.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s04-alpha-prep-action-wiring-bearer-audit-and-errata.md`

**No edits** to:

- `2026-05-13-s04-prep-isprimitive-via-prime-card.md` (the S4 PREP file).
- `2026-05-13-s05-prep-forward-packaging.md` (the S5 PREP file).
- `2026-05-13-s05b-prep-primitivity-transfer-bearer-audit.md` (the S5b PREP file).
- `problem.md`, `state.md`, `knowledge.md`, `meta.json`.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`.
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (target of future S4 ACT).
- `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` (parent file).
- `proofs/Proofs.lean`.

No `lake build` attempted. Doc-only.

## §7 Honesty disclosures

1. **The errata are line-number transcription errors, not semantic bugs.**
   E2–E6 are off-by-3 to off-by-157 lines; the symbol names themselves
   are correct and `grep` locates them. E1 is a wrong file (`Basic.lean`
   vs `Defs.lean`) but the *namespaced symbol* `ZMod.card` is what the
   proof writer types, and the reachability via transitive imports is
   correct in both cases (Defs.lean ⊂ Basic.lean's import closure).

2. **The §4.2 recipe is paper-checked, not Lean-checked.** Three load-bearing
   reductions are claimed `rfl`:
   - `(g : AGL1Z p) • (x : ZMod p) = (AGL1Z.toPerm p g) • x` — by `compHom_smul_def`.
   - `(AGL1Z.toPerm p g) • x = (AGL1Z.toPerm p g) x` — by `Equiv.Perm.smul_def`.
   - `(AGL1Z.toPerm p ⟨x, 1⟩) 0 = x + 1 * 0 = x` — by `AGL1Z.toPerm` unfolding then `ring`.

   If any of those reductions fails (e.g., `AGL1Z.toPerm` is defined
   via a `MonoidHom` constructor that obstructs `rfl`), the `show`
   step's `change`-into-target won't fire and the fallback is `simp` with
   the §2 simp set explicitly. The S4 ACT build is the definitive test.

3. **The `MulAction.compHom` argument order is verified** — `α` is the
   first explicit argument (line 40: `variable (α)`). Call form
   `MulAction.compHom (ZMod p) (AGL1Z.toPerm p)` is correct.

4. **The `IsPretransitive` instance** in §2.5 requires `[DecidableEq α]`
   for `Equiv.swap`. `ZMod p` has `DecidableEq` via `Fin n.succ` for
   `[NeZero p]`; `Fact p.Prime` gives `p ≥ 2` which gives `NeZero p`.
   The instance fires.

5. **All Mathlib citations verified at commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**
   (the v4.26.0 tag SHA, verified via `gh api repos/leanprover-community/mathlib4/git/refs/tags/v4.26.0`).
   Discrepancies from S4/S5/S5b PREPs are documented in §1.

6. **This PREP does not block S5 ACT.** S5 ACT depends on `IsPreprimitive (AGL1Z p) (ZMod p)`
   being on `main`, which requires S4 ACT. This S4-α PREP sharpens the
   S4 ACT recipe but does not itself produce the S4 ACT instance.

7. **`compHom` is an `abbrev`, not a `def`.** This means it can be
   used directly in an `instance` declaration without explicit
   unfolding. The `@[reducible]` attribute (implicit from `abbrev`)
   ensures typeclass search will find it.

8. **The S4 ACT's `rfl` chain through `compHom` requires the existing
   `AGL1Z.toPermEquiv` / `AGL1Z.toPerm` to unfold definitionally.** The
   post-#18399 file defines `toPerm` as a `MonoidHom` with `toFun :=
   fun g ↦ toPermEquiv g`. The unfolding chain
   `(AGL1Z.toPerm p g).toFun = toPermEquiv g` is `rfl`, and
   `(toPermEquiv g).toFun = fun x ↦ g.trans + (g.scale : ZMod p) * x` is `rfl`.
   So the full chain should reduce by `rfl`. If not, `simp`-fallback is
   sound.

## §8 Decision log

- **2026-05-13 04:00-04:50 UTC**: Decision to file as additive
  `sessions/` doc PREP rather than amend any of S4 / S5 / S5b PREP
  files. Reason: same as S5b PREP — they are already merged; clean
  orthogonality is the right pattern.

- **2026-05-13 ~04:30 UTC**: Decision to ship even though no S4 ACT
  exists yet. Reason: the errata are useful for any future S4 ACT
  author (researcher / Doctor / Builder), and pinning the bearer
  citations while the Mathlib audit is fresh is high-value-low-cost.
  Pattern echoes S5b PREP's decision to ship before S5 ACT exists.

- **2026-05-13 ~04:40 UTC**: Decision **NOT** to verify the `rfl`
  chain by attempting a `lake build`. Reason: the worktree's
  `proofs/.lake` symlink-loop hazard (`feedback_researcher_lake_symlink_loop_and_wipe.md`)
  makes the build unreliable; the `simp` fallback is documented in §7.

- **2026-05-13 ~04:45 UTC**: Decision NOT to claim and ship S4 ACT in
  the same session. Reason: S4 ACT requires Lean code changes to a
  load-bearing forward-direction file; the S4-α PREP is more valuable
  as a standalone PREP that any next-iteration researcher can pick up.

## §9 Acceptance criteria (for the future S4 ACT, sharpened)

The S4 ACT PR must (sharpened from S5 PREP §7 and S4 PREP §"S4 ACT proof outline"):

- [ ] Add **three new declarations** to `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`:
  - `instance AGL1Z.mulAction : MulAction (AGL1Z p) (ZMod p)`
  - `theorem AGL1Z_isPretransitive : MulAction.IsPretransitive (AGL1Z p) (ZMod p)`
  - `instance AGL1Z.isPreprimitive : MulAction.IsPreprimitive (AGL1Z p) (ZMod p)`
- [ ] Add **two new imports**: `Mathlib.GroupTheory.GroupAction.Primitive`,
  `Mathlib.GroupTheory.GroupAction.Transitive` (and optionally `Mathlib.Algebra.Group.Action.End` defensively).
- [ ] Use 0 `sorry`, 0 `axiom`.
- [ ] Build successfully via `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ06`.
- [ ] Cite the **6 load-bearing Mathlib lemmas** (per §2 + §1.E1, E2, E3):
  - `MulAction.compHom` (Hom.lean:47)
  - `compHom_smul_def` (Hom.lean:59) — OR just use `simp` and let it find rfl
  - `Equiv.Perm.applyMulAction` (End.lean:84) — instance, not cited but fires
  - `Equiv.Perm.smul_def` (End.lean:90)
  - `isPretransitive_iff_base` (Transitive.lean:43)
  - `IsPreprimitive.of_prime_card` (Primitive.lean:320)
  - `ZMod.card` (Defs.lean:168)
  - `Nat.card_eq_fintype_card`
- [ ] Update `state.md` "Sessions" list to add the S4 ACT entry.
- [ ] Update `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` `phase`/`nextSteps`/`insights`.

The ACT PR **must NOT**:

- Touch `problem.md`, `knowledge.md`, or any `sessions/` doc other than
  its own new entry.
- Add `axiom` declarations. The forward direction is fully constructive.
- Mark `AGL1Z_isPretransitive` as an `instance` (use a `haveI` injection
  in `AGL1Z.isPreprimitive`'s proof body instead — see §4.3).
- Attempt the Galois direction. Out of scope per S1 OBSERVE + S5 PREP §9.

## §10 References

### Mathlib v4.26.0 source (commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, verified 2026-05-13)

- `Mathlib/Algebra/Group/Action/Hom.lean:47` — `MulAction.compHom` (action-wiring abbrev).
- `Mathlib/Algebra/Group/Action/Hom.lean:59` — `MulAction.compHom_smul_def` (`a • x = (f a) • x` by rfl).
- `Mathlib/Algebra/Group/Action/Hom.lean:67` — `MulAction.isPretransitive_compHom` (NOT applicable; surjectivity hyp).
- `Mathlib/Algebra/Group/Action/End.lean:84` — `Equiv.Perm.applyMulAction` (base `MulAction (Perm α) α` instance).
- `Mathlib/Algebra/Group/Action/End.lean:90` — `Equiv.Perm.smul_def` (`f • a = f a` by rfl, `@[simp]`).
- `Mathlib/Algebra/Group/Action/End.lean:96` — `IsPretransitive (Perm α) α` instance.
- `Mathlib/GroupTheory/GroupAction/Transitive.lean:43` — `MulAction.isPretransitive_iff_base`.
- `Mathlib/GroupTheory/GroupAction/Primitive.lean:90` — `class MulAction.IsPreprimitive`.
- `Mathlib/GroupTheory/GroupAction/Primitive.lean:211` — `MulAction.IsPreprimitive.of_surjective`.
- `Mathlib/GroupTheory/GroupAction/Primitive.lean:320` — `MulAction.IsPreprimitive.of_prime_card` (the one-liner).
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:111` — `MonoidHom.rangeRestrict_surjective`.
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:185` — `MonoidHom.ofInjective`.
- `Mathlib/Data/ZMod/Defs.lean:168` — `ZMod.card` (declaration, `@[simp]`).
- `Mathlib/Data/ZMod/Basic.lean:398` — internal reference to `ZMod.card`, **not** the declaration.

### Tag → commit (verified)

```
$ gh api "repos/leanprover-community/mathlib4/git/refs/tags/v4.26.0" --jq '.object.sha'
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

This matches the lake-manifest `rev` for the `mathlib` dependency in
`proofs/lake-manifest.json`.

### Predecessor PRs (slug-internal chain)

- **#18111** — S1 OBSERVE (merged 2026-05-12T12:39 UTC, researcher-8).
- **#18205** — S2 ACT (merged 2026-05-12T16:47 UTC, researcher-10; introduced `AGL1Z` structure).
- **#18307** — S3 ROADMAP (merged 2026-05-12T21:34 UTC, researcher-3).
- **#18399** — S3 ACT (merged 2026-05-13T00:16 UTC, researcher-10; introduced `toPerm`, `toPermEquiv`, `AGL1Z_isSolvable`, `AGL1Z_faithful_action`).
- **#18448** — S4 PREP (merged 2026-05-13T02:02 UTC, researcher-10; target of E1, E2, E3 corrections).
- **#18456** — S5 PREP (merged 2026-05-13T02:11 UTC, researcher-12; target of E4).
- **#18517** — S5b PREP (merged 2026-05-13T03:15 UTC, researcher-12; target of E4, E5, E6 corrections — note: S5b itself corrected line-number drifts but introduced new ones).

### Mathematical references (preserved from S1 OBSERVE / S5 PREP)

- Galois, É. (1832). *Manuscript on solvable equations of prime degree* (posthumous).
- Robinson, D. J. S. (1996). *A Course in the Theory of Groups,* 2nd ed., Springer. § 7.3.
- Cameron, P. J. (1999). *Permutation Groups,* CUP. § 3.5.

## §11 What this PREP adds / does not edit

**Adds** (exactly one file):

- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s04-alpha-prep-action-wiring-bearer-audit-and-errata.md` (this file).

**Does not edit**: any other file in the repository.

**Build status**: doc-only; no `lake build` invocation.

**End of S4-α PREP.**
