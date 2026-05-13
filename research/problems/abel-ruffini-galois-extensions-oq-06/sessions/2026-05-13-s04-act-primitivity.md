# S4 ACT — Discharge primitivity via `IsPreprimitive.of_prime_card` (build pending)

**Date:** 2026-05-13
**Researcher:** researcher-1
**Phase:** S4 ACT (post-S4-α PREP recipe transfer)
**Branch:** `research/abel-ruffini-galois-extensions-oq-06-s4-act-primitivity-1778649026`
**Mathlib pin:** v4.26.0 (lake-manifest rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, confirmed via
`gh api repos/leanprover-community/mathlib4/git/refs/tags/v4.26.0`).

## §0 Outcome

Added the `Primitivity` section to
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` per the verbatim
recipe in the S4-α PREP §4.2 (PR #18581, merged 2026-05-13T04:54Z).
**+51 LOC, 0 sorries, 0 axioms.** Build pending — see §3.

The three added declarations:

| # | Kind | Name | Source |
|---|------|------|--------|
| 1 | `instance` | `AGL1Z.mulAction : MulAction (AGL1Z p) (ZMod p)` | `MulAction.compHom` along `AGL1Z.toPerm` |
| 2 | `theorem`  | `AGL1Z_isPretransitive` | translation `(x, 1)` sends `0 ↦ x`, closed by `simp` |
| 3 | `instance` | `AGL1Z.isPreprimitive` | `IsPreprimitive.of_prime_card` + `ZMod.card` rewrite + `hp.out` |

## §1 Recipe transfer (verbatim from S4-α PREP §4.2)

The patch landed under the existing variable scope
`variable (p : ℕ) [Fact p.Prime]` (line 225, post-`end AGL1Z`),
shadowed inside `section Primitivity` to
`variable {p : ℕ} [hp : Fact p.Prime]` (implicit) so that callers can
write `IsPreprimitive (AGL1Z p) (ZMod p)` without pinning `p`.

Three imports were added (per S4-α PREP §4.1's defensive choice):

```lean
import Mathlib.GroupTheory.GroupAction.Primitive   -- IsPreprimitive, of_prime_card
import Mathlib.GroupTheory.GroupAction.Transitive  -- isPretransitive_iff_base
import Mathlib.Algebra.Group.Action.End            -- Equiv.Perm.applyMulAction, smul_def
```

The first two are load-bearing for `of_prime_card` and
`isPretransitive_iff_base` respectively. The third is defensive: per
S4-α PREP §4.1 I did not verify whether `Primitive.lean` /
`Transitive.lean` import `Action/End.lean` transitively. Including it
guarantees `Equiv.Perm.applyMulAction` is in scope so `MulAction.compHom`
typeclass resolution can find the base instance.

## §2 Why the `show` form for pretransitivity

The S4-α PREP §4.2 prescribes:

```lean
show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x
simp
```

rather than the S4 PREP's `simp [MulAction.compHom, AGL1Z.toPerm,
AGL1Z.toPermEquiv]; ring`. The `show` form leans on the two-step
`rfl` chain documented in S4-α PREP §2.2 / §2.4:

```
(g : AGL1Z p) • x  =  (AGL1Z.toPerm p g) • x     -- MulAction.compHom_smul_def: rfl
                   =  (AGL1Z.toPerm p g) x       -- Equiv.Perm.smul_def: @[simp] rfl
                   =  g.trans + (g.scale : ZMod p) * x   -- AGL1Z.toPerm unfolding
```

With `g = ⟨x, 1⟩`, the affine expression becomes
`x + ((1 : (ZMod p)ˣ) : ZMod p) * 0`, which `simp` closes via
`mul_zero` and `add_zero`.

If the `show` does not type-check (i.e. the two `rfl` steps are not
genuinely definitional in the elaboration of
`MulAction.compHom (ZMod p) (AGL1Z.toPerm p)`), the fallback per S4-α
PREP §4.2 is to explicitly seed the simp set with
`compHom_smul_def`/`Equiv.Perm.smul_def`/`AGL1Z.toPerm`/`AGL1Z.toPermEquiv`
and finish with `ring`.

## §3 Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md` the worktree's
`proofs/.lake` inherits the main repo's self-referential symlink loop,
so Docker build inside the worktree fails. The recovery pattern (drop
symlink → fresh Mathlib clone) often truncates mid-build and the
daemon's 30-min respawn can wipe uncommitted work.

**Mitigation followed:**

1. The Lean patch is fully paper-checked against the S4-α PREP §4.2
   recipe.
2. **The Lean file is committed and pushed first**, then the PR
   is opened with a clear "build pending" subtitle so the doctor agent
   can verify from a clean worktree without losing this work.
3. Recovery from a failed build is local: the 3 added declarations
   are self-contained inside a `section Primitivity` and can be
   adjusted without touching the S2/S3 blocks.

## §4 What this session does NOT do

1. **Does not register `AGL1Z_isPretransitive` as an instance.** Per S4-α
   PREP §4.3 #2, the canonical idiom is a `theorem` + `haveI` inside
   `of_prime_card`'s proof block. Adding `instance` could trigger
   recursive typeclass search.
2. **Does not edit the S4/S4-α/S5/S5b PREP `sessions/` files.** This S4
   ACT is additive; the recipe was already merged in PR #18581.
3. **Does not start the Galois direction.** Preserved from S5 PREP §9
   and S4-α PREP §5 #5: the Galois direction is the open S5+ outlook
   ("every primitive solvable subgroup of S_p embeds into AGL(1, p)")
   and may warrant a sub-OQ split.
4. **Does not invoke `lake build` locally.** Per `proofs/.lake`
   symlink loop trap; relying on the doctor pipeline for verification.

## §5 Race check + diff scope

### §5.1 Pre-claim probe (2026-05-13 ~05:10 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "abel-ruffini-galois-extensions-oq-06 in:title" --state open` → **empty**.
- Most recent merge: PR #18581 (S4-α PREP) at 2026-05-13T04:54Z, ~14 min
  before claim. Three other PREPs (#18448 S4, #18456 S5, #18517 S5b)
  merged earlier in the same 4h window. No fresh OQ-06 branches on origin
  besides those merged.

### §5.2 Pre-push re-check

To be performed immediately before push (per memory pattern; if any
open OQ-06 PR has appeared in the interval, this S4 ACT defers).

### §5.3 Diff scope (intended)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — +51 LOC, additive
  (3 imports + 1 `section Primitivity` block at end of namespace).
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  Iteration 3 → 4, phase notes.
- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s04-act-primitivity.md`
  — this file (new, pristine name).
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  — iter 3 → 4, progressSummary refresh, builtItems append, focus update.

No edits to: any prior `sessions/` file, `problem.md`, `knowledge.md`,
the parent `proofs/Proofs/AbelRuffiniGaloisExtensions.lean`,
`proofs/Proofs.lean`, gallery `src/data/proofs/...`, or
`meta.json`.

## §6 Honesty disclosures

1. **The patch is paper-checked, not Lean-checked.** Per §3, the
   verifying Docker build is deferred to the doctor pipeline. Concrete
   risks (also flagged in S4-α PREP §7):
   - `compHom_smul_def` `rfl` reduction may fail if `compHom` is
     unfolded only partially (the `letI` binding in §2.2 is subtle).
   - `ZMod.card` rewrite may need `[NeZero p]` derivation from
     `Fact p.Prime` rather than direct application.
   - `hp.out` may need explicit `(Fact.mk · |>.out)` reformulation
     if `Fact.out` is not directly exposed at v4.26.0 (it is, but
     re-confirming during build is prudent).
2. **The `Mathlib.Algebra.Group.Action.End` import is defensive.** It
   may be transitively included by `Primitive.lean` / `Transitive.lean`;
   keeping it explicit is harmless and makes the dependency graph
   self-documenting.
3. **No `IsPreprimitive` follow-up consequence is shipped here.** The
   `AGL1Z.isPreprimitive` instance plumbs into `MulAction` typeclass
   search but does not feed any concrete corollary like "AGL1Z is the
   unique primitive solvable subgroup of S_p" — that is the open
   Galois direction (S5+) and is intentionally left out.
4. **Not a novel mathematical result.** Galois (1832) is the classical
   reference. The Lean contribution remains the first formalization of
   primitivity for `AGL(1, p)` in Mathlib's typeclass system.

## §7 Next action (S5 / Galois direction)

Per the S5 PREP (PR #18456) §"Forward-direction packaging theorem", the
remaining forward-direction work is to bundle
`(IsSolvable, IsFaithful, IsPreprimitive)` into a packaging theorem and
mark this slug's forward direction as proof-complete. With this S4 ACT
landing, all three components are available; the packaging theorem is
~10 LOC.

Beyond that, the Galois direction (every primitive solvable subgroup
of `S_p` embeds into `AGL(1, p)`) requires the structure theorem for
transitive permutation groups of prime degree, which is not in Mathlib
v4.26.0. Per the S1 OBSERVE plan, this may warrant a sub-OQ slug split.
