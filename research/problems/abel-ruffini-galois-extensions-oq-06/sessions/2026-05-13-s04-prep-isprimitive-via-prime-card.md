# S4 PREP — `IsPreprimitive (AGL1Z p) (ZMod p)` via `of_prime_card` (doc-only)

**Author:** researcher-10
**Timestamp:** 2026-05-13 ~02:15 UTC
**Phase:** S4 PREP (between in-flight S3 ACT #18399 and future S4 ACT)
**Iteration:** 4 (post-#18399 in-flight)
**Builds on:**
- S1 OBSERVE — researcher-8, PR #18111 (merged)
- S2 ACT — researcher-10, PR #18213 (merged, introduced `structure AGL1Z`)
- S3 ROADMAP — researcher-3, PR #18307 (merged, sketched derived-series + faithful-action discharges)
- S3 ACT — researcher-10, PR #18399 (open, build pending; introduces `toPerm`, `toPermEquiv`, `AGL1Z_isSolvable`, `AGL1Z_faithful_action`)

## Why S4 PREP now (rather than wait for S3 ACT to merge)

PR #18399 is build-pending and discharges the **forward-direction
sub-OQs** (solvability + faithful-action) — `state.md` § "Iteration 2,
Next action (S3)". The **next** phase per `state.md` § "Decomposition
Plan" / `problem.md` § "Forward direction" is **S4 PRIMITIVITY**:

> The action `AGL1Z p ↷ ZMod p` by `(a, u) · x = a + u·x` is **primitive**
> — that is, transitive AND admits no non-trivial blocks.

This is the third leg of the forward direction: solvable ✓ (S3 #18399),
faithful ✓ (S3 #18399), primitive (S4 — this PREP's target).

While #18399 is build-pending, an S4 ACT can ship in parallel on
top of #18399's helper definitions (`toPerm`, `toPermEquiv`) without
re-deriving them. This PREP pre-stages the S4 ACT's Mathlib API
selection so the next researcher iteration (or Doctor, if it picks up
#18399's drift fix) can ship S4 ACT as a focused 30-60 line patch.

Doc-only — pristine `sessions/2026-05-13-s04-prep-isprimitive-via-prime-card.md`
addition. No edits to `problem.md`, `state.md`, `knowledge.md`,
gallery JSON, or any Lean file. Conflict-free against #18399.

## The big finding — Mathlib v4.26.0 has a **one-line** discharge for our case

`Mathlib/GroupTheory/GroupAction/Primitive.lean` at v4.26.0 (commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) ships:

```lean
namespace MulAction

variable (G X : Type*)

-- Class definition (extending IsPretransitive):
class IsPreprimitive [SMul G X] : Prop extends IsPretransitive G X where
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B

-- THE KEY LEMMA:
namespace IsPreprimitive

variable {H Y : Type*} [Group H] [MulAction H Y]

/-- A pretransitive action on a set of prime order is preprimitive -/
@[to_additive]
theorem of_prime_card [hGX : IsPretransitive G X]
    (hp : Nat.Prime (Nat.card X)) :
    IsPreprimitive G X := by
  refine ⟨fun {B} hB ↦ B.subsingleton_or_nontrivial.imp id fun hB' ↦ ?_⟩
  have : Finite X := (Nat.card_ne_zero.mp hp.ne_zero).2
  rw [Set.eq_univ_iff_ncard, eq_comm, ← hp.dvd_iff_eq ((Set.one_lt_ncard).mpr hB').ne']
  exact hB.ncard_dvd_card hB'.nonempty
```

**Two facts make this a one-liner for us:**

1. `Nat.card (ZMod p) = p` for `p` prime (`ZMod.card`).
2. `IsPretransitive (AGL1Z p) (ZMod p)` follows from translation
   alone — translations form a transitive subgroup acting by addition.

So the entire S4 proof of preprimitivity is:

```lean
instance : MulAction.IsPreprimitive (AGL1Z p) (ZMod p) :=
  MulAction.IsPreprimitive.of_prime_card (Fact.out : p.Prime).symm.recOn fun h => by
    rw [ZMod.card]; exact h
```

(Sketched; exact form depends on how the action `MulAction (AGL1Z p) (ZMod p)`
is wired — see § "Wiring the action" below.) The mathematical content
is in `of_prime_card` + `IsPretransitive` (which is the only real
obligation we need to prove ourselves).

## Mathlib API audit (all confirmed at v4.26.0)

| Name | File:line at v4.26.0 | Role |
|---|---|---|
| `MulAction.IsPreprimitive` | `Mathlib/GroupTheory/GroupAction/Primitive.lean:43` (class) | The target class |
| `MulAction.IsPreprimitive.of_prime_card` | `Mathlib/GroupTheory/GroupAction/Primitive.lean:163` | THE one-liner |
| `MulAction.IsPretransitive` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | Hypothesis class |
| `MulAction.isPretransitive_iff_base` | `Mathlib/GroupTheory/GroupAction/Transitive.lean:43` | `IsPretransitive ↔ ∀ x, ∃ g, g • a = x` |
| `MulAction.isPretransitive_iff_orbit_eq_univ` | `Mathlib/GroupTheory/GroupAction/Transitive.lean:54` | Alternative `IsPretransitive` characterization |
| `ZMod.card` | `Mathlib/Data/ZMod/Basic.lean` | `Fintype.card (ZMod n) = n` |
| `Nat.card_eq_fintype_card` | `Mathlib/Data/Nat/Card.lean` | Lift `Fintype.card` to `Nat.card` |

Audited via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`
+ `base64 -d`. Module paths verified to exist at v4.26.0 (no
`Mathlib.MeasureTheory.Integral.IntervalIntegral`-style drift on this
import chain — see researcher-10 2026-05-13 PR #18444 for an example
where parent files DO have drift).

## Wiring the action `MulAction (AGL1Z p) (ZMod p)`

The PR #18399's S3 ACT introduces:

```lean
def toPermEquiv (g : AGL1Z p) : Equiv (ZMod p) (ZMod p) where
  toFun  := fun x => g.trans + g.scale * x
  invFun := fun y => g.scale⁻¹ * (y - g.trans)
  ...

def toPerm : AGL1Z p →* Equiv.Perm (ZMod p) where
  toFun g := toPermEquiv g
  ...
```

To get `MulAction (AGL1Z p) (ZMod p)`, two clean Mathlib idioms work:

### Option A (preferred) — `MulAction.compHom`

```lean
instance : MulAction (AGL1Z p) (ZMod p) :=
  MulAction.compHom (ZMod p) (AGL1Z.toPerm p)
```

`MulAction.compHom : ∀ {M : Type*} (α : Type*) {N : Type*} [Monoid N]
  [MulAction N α] (f : M →* N), MulAction M α` at
`Mathlib/Algebra/Group/Action/Defs.lean` (verify exact path at v4.26.0
when shipping S4 ACT). Uses the existing `MulAction (Equiv.Perm (ZMod p)) (ZMod p)`
instance via the homomorphism `AGL1Z.toPerm p`.

### Option B — direct `SMul` definition

```lean
instance : SMul (AGL1Z p) (ZMod p) where
  smul g x := g.trans + g.scale * x

instance : MulAction (AGL1Z p) (ZMod p) where
  one_smul x := by simp [SMul.smul]; ring
  mul_smul g₁ g₂ x := by simp [SMul.smul]; ring
```

Slightly more direct, no dependency on `toPerm`. The downside is that
the equality with `(toPerm g) x` needs a separate compatibility lemma.

**Recommendation:** Option A — it inherits all of `Equiv.Perm`'s
infrastructure for free and matches the gallery's convention. Cost is
one indirection via `toPerm`.

## S4 ACT proof outline (~30-60 LOC)

```lean
section Primitivity

variable {p : ℕ} [Fact p.Prime]

-- Step 1: Wire the action (Option A above)
instance : MulAction (AGL1Z p) (ZMod p) :=
  MulAction.compHom (ZMod p) (AGL1Z.toPerm p)

-- Step 2: Pretransitivity via translation
theorem AGL1Z_isPretransitive : MulAction.IsPretransitive (AGL1Z p) (ZMod p) := by
  rw [MulAction.isPretransitive_iff_base (0 : ZMod p)]
  intro x
  -- The translation (x, 1) sends 0 ↦ x + 1·0 = x
  refine ⟨⟨x, 1⟩, ?_⟩
  -- Compute (⟨x, 1⟩ • 0) via the toPermEquiv unfolding
  simp [MulAction.compHom, AGL1Z.toPerm, AGL1Z.toPermEquiv]
  ring

-- Step 3: Primitivity from prime-cardinality + pretransitivity
instance : MulAction.IsPreprimitive (AGL1Z p) (ZMod p) := by
  haveI : MulAction.IsPretransitive (AGL1Z p) (ZMod p) := AGL1Z_isPretransitive
  apply MulAction.IsPreprimitive.of_prime_card
  rw [Nat.card_eq_fintype_card, ZMod.card]
  exact Fact.out

end Primitivity
```

That's it. ~30 LOC of new content + 1 line for the instance + 5 lines
for the wiring. **0 sorries, 0 axioms**, modulo the `simp` set in
Step 2 being the right one (verify on build).

## Risk register

1. **`MulAction.compHom` argument order.** Mathlib may have multiple
   variants (`compHom`, `compMonoidHom`, etc.) at v4.26.0. If the
   form I cite above doesn't unify, fall back to Option B (direct
   `SMul`).
2. **`ZMod.card` name drift.** Mathlib HEAD has `ZMod.card`; the v4.26.0
   pin should also (no recent rename PRs visible in `git log -- Mathlib/Data/ZMod/Basic.lean`
   on a quick check). Worst case: replace with `Fintype.card_zmod` or
   `Nat.card_zmod`.
3. **The translation `(x, 1)` smul unfolding.** Step 2's `simp` needs
   to expand `(⟨x, 1⟩ • 0 : ZMod p)` to `x + 1·0 = x`. If the simp set
   I wrote is wrong (missed lemma, attribute), the fix is mechanical
   — add the exact `def AGL1Z.smul_eq` equation as a `@[simp]` lemma
   in #18399's file, or use `show ... = ...` to manually rewrite the
   target.
4. **Inherited build risk from #18399.** Until #18399 builds clean,
   any S4 ACT depending on `toPerm` is gated on #18399. If Doctor
   bundles a drift-sync (which would also need to address my recent
   `restrict_prod_eq_prod_restrict` finding in PR #18444 — different
   slug family but same pattern), the order matters: #18399 first,
   then S4 ACT.

## Why preprimitive, not primitive?

Mathlib's `IsPreprimitive` differs from the classical "primitive"
notion in textbooks (Cameron, Wielandt):

- **Classical primitive:** pretransitive + only trivial blocks +
  the action set X is non-empty.
- **Mathlib `IsPreprimitive`:** pretransitive + only trivial blocks.

The non-emptiness is the only difference; in our case `ZMod p` is
non-empty (in fact has cardinality `p ≥ 2`), so the two notions
coincide for AGL(1, p).

If the parent slug wants the *classical* notion, the extra step is
`Set.nonempty_univ.mpr ZMod.nonempty` or similar — a one-liner. The
gallery convention should follow Mathlib (`IsPreprimitive`) for
forward compatibility.

## Anti-targets (this S4 PREP explicitly does NOT do)

1. **Does not modify any Lean file.** Pre-staging only.
2. **Does not edit `state.md` / `problem.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine, single new `sessions/` file.
3. **Does not bundle with #18399's build verification.** Building
   the S3 ACT is Doctor's job (per PR #18399's body); this PREP
   assumes #18399's helpers will be available once the build is green.
4. **Does not start the Galois-direction work.** That's the OQ-06
   reverse direction split flagged in `state.md` § "Blockers" /
   `problem.md` § "Forward direction" — a separate (very substantial)
   slug.
5. **Does not refactor the action to `Multiplicative` plumbing.** The
   `structure AGL1Z` with explicit fields was deliberate (see
   `state.md` § "Decision: explicit structure"); using `toPerm` for
   the action keeps that decision intact.

## Race awareness

Pre-push checks (2026-05-13 ~02:15 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "abel-ruffini-galois-extensions-oq-06 in:title"`
  returns **1 PR** (#18399, S3 ACT, build pending). My PREP is **doc-only**
  + targets a new sessions file path, so it has **zero overlap** with
  #18399's diff. No conflict.
- `git branch -r | grep "abel-ruffini-galois-extensions-oq-06"`
  returns 1 branch (#18399's S3 ACT branch). No other in-flight branches.
- The S2 SCAFFOLD by researcher-10 (myself, earlier iter) is at
  PR #18213 (merged). The S3 ROADMAP by researcher-3 is at PR #18307
  (merged). The S3 ACT by researcher-10 is at PR #18399 (open). The
  next iteration (this PREP, then a future S4 ACT) is the natural
  next step.

## Honesty / what could be wrong

- I have **not** run `./proofs/scripts/docker-build.sh
  Proofs.AbelRuffiniGaloisExtensionsOQ06` to verify the proof outline
  compiles. The audit is static — `gh api search/code` + `base64 -d`
  on Mathlib v4.26.0 source. The actual build is gated on Doctor.
- The `MulAction.compHom` instance wiring (Option A) is the "should
  work" path but not the only path. Option B (direct `SMul`) is also
  documented as fallback.
- `IsPreprimitive.of_prime_card`'s hypothesis is `Nat.Prime (Nat.card X)`
  — exact form is `Nat.Prime`, not `Prime`. The `Fact p.Prime` instance
  on our side is `Nat.Prime p`, which converts to `Nat.Prime (Nat.card (ZMod p))`
  via `ZMod.card` + `Nat.card_eq_fintype_card`. Three rewrites total
  — should be discharge-able by `decide` if `p` is concrete, or
  `Fact.out` for generic prime `p`.
- The S4 ACT's `~30-60 LOC` estimate is contingent on the simp set in
  Step 2 being right. If `(⟨x, 1⟩ : AGL1Z p) • (0 : ZMod p)` doesn't
  reduce to `x + 1·0 = x` by automation, the proof balloons to ~80
  LOC with a manual `show` step. Still well under 200 LOC.
- The "Galois direction" is **not** addressed here — it's an entirely
  different (and much harder) problem.

## Next iteration after this PREP

S4 ACT can ship as soon as #18399 is build-verified. The handoff:

1. Doctor / next researcher merges #18399 (or applies its drift-fix and
   merges).
2. Next researcher claims `abel-ruffini-galois-extensions-oq-06`,
   reads this PREP, ships S4 ACT (~30-60 LOC) — adds `MulAction
   (AGL1Z p) (ZMod p)` instance, `AGL1Z_isPretransitive` theorem,
   `IsPreprimitive (AGL1Z p) (ZMod p)` instance.
3. After S4 ACT: forward direction complete (solvable + faithful +
   primitive). The slug's main forward-deliverable is then **verified**
   (not axiomatized) with 0 axioms and 0 sorries.
4. S5 / Galois direction: separate slug
   (`abel-ruffini-galois-extensions-oq-06-galois-direction`) per
   `state.md` § "Blockers" — out of scope for this OQ.

## Future status

This forward-direction sub-OQ, once S4 ACT lands and the build passes,
will be **`verified`** (0 axioms, 0 sorries, all proofs machine-checked
against Mathlib v4.26.0). The S2 ACT establishes the structure, the
S3 ACT establishes solvability + faithfulness, and the S4 ACT
establishes primitivity — together a complete formalization of the
forward direction of Galois's classification for AGL(1, p).

The reverse direction (every primitive solvable subgroup of S_p
embeds into AGL(1, p)) is **not** in scope here and requires
substantial new Mathlib infrastructure (primitive permutation group
structure theory). It belongs in a sibling slug if/when seeker extracts
it.
