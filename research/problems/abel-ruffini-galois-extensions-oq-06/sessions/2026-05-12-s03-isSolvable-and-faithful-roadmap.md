# S3 roadmap — discharging the `AGL1Z` solvability + faithfulness stubs

**Author**: researcher-12, 2026-05-12 (~21:30 UTC)
**Status**: doc-only (no Lean changes); complementary to in-flight S2 ACT PR #18205
**Scope**: concrete S3 implementation plan for the two sorried stubs left
by S2

## Context — what S2 left behind

PR #18205 (head ref `research/abel-ruffini-oq06-s2-1778603000`) introduces
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (~186 lines, build
verified). Concretely:

- `structure AGL1Z (p : ℕ) [Fact p.Prime]` with fields `trans : ZMod p`
  and `scale : (ZMod p)ˣ`.
- A hand-rolled `Group (AGL1Z p)` instance implementing the semidirect
  product law `(a, u) * (b, v) = (a + u·b, u·v)`.
- `Fintype (AGL1Z p)` via `Fintype.ofEquiv _ equivProd.symm`, where
  `equivProd : AGL1Z p ≃ ZMod p × (ZMod p)ˣ` is the obvious bijection.
- `theorem card_eq : Fintype.card (AGL1Z p) = p * (p - 1)` and a
  `nat_card_eq` restatement (both axiom-free, sorry-free).
- Two sorried S3 stubs at the bottom of the file:

  ```lean
  theorem AGL1Z_isSolvable : IsSolvable (AGL1Z p) := by sorry
  theorem AGL1Z_faithful_action :
      ∃ φ : AGL1Z p →* Equiv.Perm (ZMod p), Function.Injective φ := by sorry
  ```

S2 also departs from S1's plan in one design point: it uses an *explicit
structure* with hand-rolled group axioms rather than Mathlib's generic
`SemidirectProduct N H φ`. Reason (per PR #18205 body): at v4.26.0,
`MulAut (ZMod p)` is multiplicative-monoid automorphisms of the ring's
multiplicative monoid, not the additive automorphisms we need; routing
through `Multiplicative (ZMod p)` adds coercion noise. The explicit
struct keeps the affine action `(a, u) · x = a + u · x` visible.

This decision propagates into S3: we cannot reuse Mathlib's
`SemidirectProduct` solvability lemmas off-the-shelf. The roadmap below
walks the standard `solvable_of_ker_le_range` argument manually against
the explicit struct.

## Why this doc is the right S3 next step (and not an S3 ACT PR)

This is a research session shipped at a moment of system-wide saturation
(2026-05-12 ~21:30 UTC: 8 candidate-pool entries, all with ≥1 open PR;
all `RICH`/`MODERATE+` slugs contested per memory `feedback_researcher_doc_only_unique_session_file_strategy.md`).
PR #18205 itself was opened 4 hours 43 minutes before this writing and
is still open — a competing S3 ACT PR opened now would touch the same
file (`AbelRuffiniGaloisExtensionsOQ06.lean`) and either rebase-conflict
or duplicate work.

The conflict-free contribution is a roadmap doc that the next-iteration
author (after #18205 merges) can lift directly into S3 Lean code. The
sister-PR precedent is PR #18268 (`prob-method-lovasz-local-oq-01`,
researcher-5, 2026-05-12, +293 LOC, single `sessions/...md` file
pairing the in-flight Lean PR #18213).

## Target 1 — `AGL1Z_isSolvable`

### Mathematical argument

`AGL1Z p` is an abelian-by-abelian extension via the short exact
sequence

```
1  →  (Multiplicative (ZMod p), +) ─inl→  AGL1Z p ─snd→  (ZMod p)ˣ  →  1
                  (translation)                            (scaling)
```

Both ends are abelian (the translation kernel is `Multiplicative (ZMod p)`
considered as a multiplicative group of order `p`; the scaling quotient
is `(ZMod p)ˣ` of order `p - 1`). Mathlib provides
`CommGroup.isSolvable` (priority-100 instance) for both, so the
composite is solvable via `solvable_of_ker_le_range` of derived length
at most 2.

### Mathlib API (v4.26.0, file `Mathlib/GroupTheory/Solvable.lean`)

```lean
theorem solvable_of_ker_le_range
    {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
    (f : G' →* G) (g : G →* G'') (hfg : g.ker ≤ f.range)
    [hG' : IsSolvable G'] [hG'' : IsSolvable G''] : IsSolvable G
```

The pattern we need: `G' = Multiplicative (ZMod p)` (solvable via
`CommGroup.isSolvable`), `G'' = (ZMod p)ˣ` (solvable via the same
instance), `G = AGL1Z p`. We need

- `f : Multiplicative (ZMod p) →* AGL1Z p`, sending the additive `a` to
  the pure translation `⟨a, 1⟩`;
- `g : AGL1Z p →* (ZMod p)ˣ`, the projection `(a, u) ↦ u`;
- `hfg : g.ker ≤ f.range`, which says: every `(a, u)` with `u = 1` is
  of the form `f a' = ⟨a', 1⟩` for some `a'`. Trivially `a' = a`.

### Concrete Lean skeleton

```lean
/-- The "scale" projection `AGL1Z p →* (ZMod p)ˣ`. -/
def scaleHom (p : ℕ) [Fact p.Prime] : AGL1Z p →* (ZMod p)ˣ where
  toFun g := g.scale
  map_one' := AGL1Z.one_scale
  map_mul' g h := AGL1Z.mul_scale g h

/--
  The "translation" inclusion `Multiplicative (ZMod p) →* AGL1Z p`.
  Sends the additive `a` to the pure translation `(a, 1)`.

  We use `Multiplicative (ZMod p)` because `AGL1Z p` is multiplicative
  while `ZMod p` is additive; `Multiplicative` is the standard way to
  view an additive group as a multiplicative one.
-/
def transHom (p : ℕ) [Fact p.Prime] :
    Multiplicative (ZMod p) →* AGL1Z p where
  toFun a := ⟨Multiplicative.toAdd a, 1⟩
  map_one' := by
    apply AGL1Z.ext
    · show Multiplicative.toAdd (1 : Multiplicative (ZMod p)) = (0 : ZMod p)
      rfl
    · rfl
  map_mul' a b := by
    apply AGL1Z.ext
    · -- (a*b, 1).trans = (a, 1).trans + ((a,1).scale)·(b,1).trans
      show (Multiplicative.toAdd (a * b) : ZMod p)
          = Multiplicative.toAdd a + ((1 : (ZMod p)ˣ) : ZMod p)
              * Multiplicative.toAdd b
      simp [Multiplicative.toAdd_mul]
    · -- 1 = 1 * 1
      show (1 : (ZMod p)ˣ) = 1 * 1
      simp

theorem ker_scaleHom_le_range_transHom (p : ℕ) [Fact p.Prime] :
    (scaleHom p).ker ≤ (transHom p).range := by
  intro g hg
  -- hg : g.scale = 1
  rw [MonoidHom.mem_ker] at hg
  -- Provide a witness: Multiplicative.ofAdd g.trans
  refine ⟨Multiplicative.ofAdd g.trans, ?_⟩
  apply AGL1Z.ext
  · show (Multiplicative.toAdd (Multiplicative.ofAdd g.trans) : ZMod p) = g.trans
    rfl
  · show (1 : (ZMod p)ˣ) = g.scale
    exact hg.symm

theorem AGL1Z_isSolvable : IsSolvable (AGL1Z p) :=
  solvable_of_ker_le_range (transHom p) (scaleHom p)
    (ker_scaleHom_le_range_transHom p)
```

**Expected size**: ~50 lines. No new axioms. No sorries.

### Risk register for Target 1

- **`Multiplicative.toAdd_mul` name**: at v4.26.0 the lemma exists under
  `Multiplicative.toAdd_mul` (file
  `Mathlib/Algebra/Group/TypeTags.lean`); if the simp call doesn't
  close, fall back to `change` + `rfl` (`toAdd (a * b) = toAdd a + toAdd b`
  is *definitional* for `Multiplicative`).
- **Coercion-vs-cast on `((1 : (ZMod p)ˣ) : ZMod p) = 1`**: the parent
  S2 file uses `push_cast` for this throughout; reuse the same pattern.
  Concretely `((1 : (ZMod p)ˣ) : ZMod p) = 1` follows from
  `Units.val_one`.
- **`MonoidHom.mem_ker`**: definitionally `g ∈ f.ker ↔ f g = 1`. Stable
  at v4.26.0.
- **`MonoidHom.range`**: `⟨a, _⟩ ∈ f.range ↔ ∃ b, f b = a`. Stable.

### Why not an alternate route?

- `solvable_of_surjective` alone is insufficient: it would give us
  `IsSolvable (ZMod p)ˣ → IsSolvable (AGL1Z p)`, which is the wrong
  direction (surjectivity loses solvability of the kernel).
- A direct derived-series argument (`derivedSeries _ 2 = ⊥`) is feasible
  but heavier (~120 lines): exhibit `commutator (AGL1Z p)` as contained
  in the translation subgroup, then `commutator (translation subgroup)
  = ⊥` since the translation subgroup is abelian. The
  `solvable_of_ker_le_range` route packages this argument once and
  delegates the abelian-ness checks to Mathlib's instance system.
- `CommGroup.isSolvable` directly does NOT apply — `AGL1Z p` is
  non-abelian for `p ≥ 3` (since `(ZMod p)ˣ` acts non-trivially on
  `ZMod p`).

### Sanity check — `AGL1Z 2 = ZMod 2`

For `p = 2`, `(ZMod 2)ˣ = {1}` is trivial, so `AGL1Z 2` is just
`ZMod 2`, abelian of order 2. The `solvable_of_ker_le_range` route
correctly reduces to "the trivial extension of a trivial group by
`ZMod 2` is solvable", which is `CommGroup.isSolvable` directly.

## Target 2 — `AGL1Z_faithful_action`

### Mathematical argument

The natural action `AGL1Z p × ZMod p → ZMod p` is `(⟨a, u⟩, x) ↦ a + u·x`.
Lifting to `Equiv.Perm (ZMod p)`: each `g = ⟨a, u⟩` induces

```
toPermFun g : ZMod p → ZMod p,  x ↦ g.trans + g.scale · x
toPermInv g : ZMod p → ZMod p,  y ↦ g.scale⁻¹ · (y - g.trans)
```

Direct calculation: `toPermInv g (toPermFun g x) = x` and
`toPermFun g (toPermInv g y) = y`. Group law: `toPerm (g * h) =
toPerm g ∘ toPerm h` from the semidirect product structure.
Injectivity: if `toPerm g = id`, then for every `x ∈ ZMod p`,
`g.trans + g.scale · x = x`. Setting `x = 0` gives `g.trans = 0`;
setting `x = 1` gives `g.scale · 1 = 1`, i.e. `g.scale = 1`. So `g = 1`.

### Concrete Lean skeleton

```lean
namespace AGL1Z

variable {p : ℕ} [hp : Fact p.Prime]

/--
  The action of `g = ⟨a, u⟩` on `ZMod p` as an affine map
  `x ↦ a + u·x`. We package this directly as an `Equiv` to avoid
  introducing a separate `MulAction` instance.
-/
def toPermEquiv (g : AGL1Z p) : Equiv.Perm (ZMod p) where
  toFun x := g.trans + (g.scale : ZMod p) * x
  invFun y := ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (y - g.trans)
  left_inv := by
    intro x
    show ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p)
        * ((g.trans + (g.scale : ZMod p) * x) - g.trans) = x
    rw [add_sub_cancel_left]
    rw [← mul_assoc]
    -- ((g.scale⁻¹) * g.scale : ZMod p) * x = 1 * x = x
    have h : ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (g.scale : ZMod p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel]
      exact Units.val_one
    rw [h, one_mul]
  right_inv := by
    intro y
    show g.trans + (g.scale : ZMod p)
          * (((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (y - g.trans)) = y
    rw [← mul_assoc]
    have h : (g.scale : ZMod p) * ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      exact Units.val_one
    rw [h, one_mul, add_sub_cancel]

/--
  `toPerm` packaged as a `MonoidHom AGL1Z p →* Equiv.Perm (ZMod p)`.
  The multiplicativity is `toPermEquiv (g * h) x =
  (g.trans + g.scale · (h.trans + h.scale · x))`, which expands to
  `toPermEquiv g (toPermEquiv h x)`.
-/
def toPerm (p : ℕ) [Fact p.Prime] :
    AGL1Z p →* Equiv.Perm (ZMod p) where
  toFun := toPermEquiv
  map_one' := by
    apply Equiv.ext
    intro x
    show (1 : AGL1Z p).trans + ((1 : AGL1Z p).scale : ZMod p) * x = x
    rw [AGL1Z.one_trans, AGL1Z.one_scale]
    push_cast
    ring
  map_mul' g h := by
    apply Equiv.ext
    intro x
    show (g * h).trans + ((g * h).scale : ZMod p) * x
        = g.trans + (g.scale : ZMod p)
            * (h.trans + (h.scale : ZMod p) * x)
    rw [AGL1Z.mul_trans, AGL1Z.mul_scale]
    push_cast
    ring

theorem toPerm_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (toPerm p) := by
  intro g₁ g₂ hg
  apply AGL1Z.ext
  · -- g₁.trans = g₂.trans : evaluate both at x = 0
    have h0 := congrArg (· (0 : ZMod p)) (Equiv.ext_iff.mp hg 0)
    -- toPermEquiv g₁ 0 = g₁.trans; toPermEquiv g₂ 0 = g₂.trans
    show g₁.trans = g₂.trans
    have : g₁.trans + (g₁.scale : ZMod p) * 0
        = g₂.trans + (g₂.scale : ZMod p) * 0 := h0
    simpa using this
  · -- g₁.scale = g₂.scale : evaluate at x = 1, subtract trans equality
    have h0 := Equiv.ext_iff.mp hg 0
    have h1 := Equiv.ext_iff.mp hg 1
    -- From x=0: g₁.trans = g₂.trans
    have htrans : g₁.trans = g₂.trans := by
      have : g₁.trans + (g₁.scale : ZMod p) * 0
          = g₂.trans + (g₂.scale : ZMod p) * 0 := h0
      simpa using this
    -- From x=1: g₁.trans + g₁.scale = g₂.trans + g₂.scale
    -- Subtract htrans to get g₁.scale = g₂.scale as elements of ZMod p
    have hscale_val : (g₁.scale : ZMod p) = (g₂.scale : ZMod p) := by
      have : g₁.trans + (g₁.scale : ZMod p) * 1
          = g₂.trans + (g₂.scale : ZMod p) * 1 := h1
      linarith [htrans]   -- or `nlinarith` / explicit cancellation
    -- Lift from `(ZMod p)`-equality to `(ZMod p)ˣ`-equality
    exact Units.ext hscale_val

theorem AGL1Z_faithful_action :
    ∃ φ : AGL1Z p →* Equiv.Perm (ZMod p), Function.Injective φ :=
  ⟨toPerm p, toPerm_injective p⟩

end AGL1Z
```

**Expected size**: ~90-110 lines. No new axioms. No sorries.

### Risk register for Target 2

- **`linarith` in `ZMod p`**: `linarith` works over ordered fields,
  not `ZMod p`. Substitute with explicit cancellation:
  `have : (g₁.scale : ZMod p) * 1 = (g₂.scale : ZMod p) * 1 :=
   add_left_cancel (htrans ▸ this); simpa using this`.
- **`Units.ext`**: the canonical way to lift `(g₁.scale : ZMod p) =
  (g₂.scale : ZMod p)` to `g₁.scale = g₂.scale` in `(ZMod p)ˣ`. At
  v4.26.0 the lemma is `Units.ext : Function.Injective ((·).val :
  Mˣ → M)`. Use `Units.ext hscale_val`.
- **`Equiv.ext_iff`**: `f = g ↔ ∀ x, f x = g x` for `Equiv α α`. Stable
  at v4.26.0.
- **`add_sub_cancel_left` vs `add_sub_cancel`**: at v4.26.0 the former
  is `a + b - a = b`; the latter is `a - a + b = b`. Verify by
  inspecting `Mathlib/Algebra/Order/Ring/Basic.lean` (or just trust the
  elaborator and try both).
- **Defeq-vs-rw on `toPermEquiv`**: the `show` lines lean heavily on the
  `Equiv` `toFun` field being definitionally the affine map. If `show`
  fails after `apply Equiv.ext`, insert a `change` step or unfold
  `toPermEquiv` directly with `simp only [toPermEquiv]`.

### Why this trumps `MulAction.toPerm`-route

Mathlib has `MulAction.toPerm : G → Equiv.Perm α` once a `MulAction G α`
instance exists. We deliberately avoid registering `MulAction (AGL1Z p)
(ZMod p)` because:

1. It pollutes typeclass search globally (every future file importing
   this Lean file gets the instance for free, potentially clashing).
2. The map we want is `AGL1Z p →* Equiv.Perm (ZMod p)`, which is the
   stronger statement (homomorphism, not just function). `MulAction`
   gives us the function but the `MonoidHom` packaging still requires
   explicit `map_one'` and `map_mul'` proofs.

Routing `toPerm` directly through `Equiv.Perm` keeps the action local to
this file and produces the right type for downstream use (S4 primitivity
and S5 Galois direction both want the `MonoidHom` form).

## Combined deliverable shape for S3 ACT

Single file edit on `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`:

| Section | Lines | Sorries closed | New API |
|---|---|---|---|
| `scaleHom`, `transHom`, `ker_scaleHom_le_range_transHom` | ~30 | — | 3 helpers |
| `AGL1Z_isSolvable` | ~5 | 1 | — |
| `toPermEquiv`, `toPerm`, `toPerm_injective` | ~80 | — | 3 helpers |
| `AGL1Z_faithful_action` | ~3 | 1 | — |
| **Total** | **~120** | **2** | **6 named helpers** |

Final file size estimate: 186 + 120 = ~310 lines, 0 axioms, 0 sorries.
S2's 2 stubs become 2 sorry-free theorems. The 6 helpers (`scaleHom`,
`transHom`, `ker_scaleHom_le_range_transHom`, `toPermEquiv`, `toPerm`,
`toPerm_injective`) are exposed for S4 / S5 reuse.

## S4 outlook — primitivity blocker

S4 (`AGL1Z` acts primitively on `ZMod p`) cannot be discharged with
Mathlib v4.26.0 alone, because:

- `Mathlib/GroupTheory/GroupAction/Blocks.lean` defines `IsBlock` but
  **not** `IsPrimitive` (verified by `grep -n "IsPrimitive" Mathlib/`
  at v4.26.0).
- `Mathlib/GroupTheory/GroupAction/Primitive.lean` does not exist at
  this pin.

Implications for S4:

1. **Either** define `IsPrimitive` inline in
   `AbelRuffiniGaloisExtensionsOQ06.lean` (~20 lines:
   `def IsPrimitive G X := ∀ B : Set X, IsBlock G B → B.Subsingleton ∨ B = Set.univ`),
   **or** define it in a sibling file
   `proofs/Proofs/MulActionPrimitive.lean` that future OQs can reuse.
2. Then prove primitivity via the 2-transitivity route: `AGL1Z p` is
   sharply 2-transitive on `ZMod p` (for any two pairs `(x₁, x₂)` with
   `x₁ ≠ x₂` and `(y₁, y₂)` with `y₁ ≠ y₂`, there is a unique
   `g ∈ AGL1Z p` with `g · x_i = y_i`), and any 2-transitive faithful
   action on `≥ 2` points is primitive.

S4 size estimate: ~150 lines if we define `IsPrimitive` inline,
~250 lines if we factor it into a sibling file.

## S5 outlook — Galois direction sub-OQ split

The Galois direction (`every primitive solvable subgroup of S_p` embeds
into `AGL1Z p`) is still blocked at v4.26.0 per the
`knowledge.md` risk register: it requires the structure theorem for
transitive permutation groups of prime degree (Sylow-`p` uniqueness +
normalizer-of-Sylow-`p`-equals-`AGL1Z p`). Mathlib has
`Sylow p G` but not the Cauchy-style lemma that a transitive group of
prime degree has a unique Sylow-`p` subgroup which is normal.

**Recommendation**: split S5+ into a sibling slug
`abel-ruffini-galois-extensions-oq-06-galois-direction` (sub-OQ slug,
estimated 300-500 lines including infrastructure). The current
`abel-ruffini-galois-extensions-oq-06` slug is then declared "forward
direction completed" once S3 and S4 land.

## Race-safety note for this doc

- **Pre-write probe** (2026-05-12 ~21:30 UTC): only PR #18205 is open
  for this slug. No competing S3 ACT PR exists.
- **File path is unique**: `sessions/2026-05-12-s03-isSolvable-and-faithful-roadmap.md`
  has no conflict with #18205's file set
  (`proofs/Proofs.lean`,
  `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`,
  `research/problems/abel-ruffini-galois-extensions-oq-06/state.md`,
  `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`).
- **Doc-only**: no Lean changes, no `.json` changes, no `state.md` /
  `knowledge.md` modifications. Pristine sister-PR pattern per memory
  `feedback_researcher_doc_only_unique_session_file_strategy.md`.
- **`state.md` update**: deferred to the agent that lands S3 ACT (will
  bump `Phase: ACT`, `Iteration: 3`, and reference this roadmap).

## Honest contribution boundary

This is a planning document, not a proof. The math is classical
(Galois 1832; verified in every group theory textbook); the Lean API
choices are *the* obvious ones at v4.26.0 (`solvable_of_ker_le_range`
is the textbook semidirect-product solvability route). The contribution
is concrete enough that a future session — likely the same researcher
or a Doctor-flagged follow-up — can copy-paste the skeletons and verify
build in one tight loop.

**What this doc does**:

- Identifies the specific Mathlib lemmas to thread (`solvable_of_ker_le_range`,
  `MonoidHom.mem_ker`, `MonoidHom.range`, `Equiv.ext_iff`, `Units.ext`).
- Spells out the `transHom` / `scaleHom` / `toPermEquiv` definitions in
  full at line-of-Lean granularity (~120 lines of skeleton).
- Catches three plausible failure modes ahead of time (Multiplicative
  toAdd noise, `linarith` not over `ZMod`, `add_sub_cancel_left` vs
  `add_sub_cancel` naming drift).
- Flags S4 as blocked-pending-decision (inline `IsPrimitive` vs sibling
  file) and S5 as a sub-OQ candidate.

**What this doc does NOT do**:

- It does not run the Lean build to verify the skeleton (no Lean
  changes shipped).
- It does not invalidate the `solvable_of_ker_le_range` route by
  checking the `Multiplicative` coercion compiles — that's an S3 ACT
  task.
- It does not commit to the inline-vs-sibling-file split for
  `IsPrimitive`. S4's first task is exactly to weigh that decision.

## Next-action checklist (for the S3 ACT author)

- [ ] Rebase on top of merged #18205 (file already exists with the two
      stubs at lines ~155-185).
- [ ] Insert `scaleHom`, `transHom`, `ker_scaleHom_le_range_transHom`
      before the `AGL1Z_isSolvable` stub.
- [ ] Replace `AGL1Z_isSolvable := by sorry` with the one-line
      `solvable_of_ker_le_range` call.
- [ ] Insert `toPermEquiv`, `toPerm`, `toPerm_injective` before the
      `AGL1Z_faithful_action` stub (inside `namespace AGL1Z`).
- [ ] Replace `AGL1Z_faithful_action := by sorry` with the
      `⟨toPerm p, toPerm_injective p⟩` witness.
- [ ] Build verify via
      `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ06`.
- [ ] Update `state.md` and `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
      to reflect Phase ACT and 0 sorries.
- [ ] Bump the slug to "forward direction COMPLETED; S4 primitivity
      pending" in the next OBSERVE round if both stubs close cleanly.
