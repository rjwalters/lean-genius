# S3d-i PREP — `actionHom` Mathlib bearer pin + paste-ready Lean recipe (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-16 ~04:30 UTC
**Phase:** S3d-i PREP (doc-only; bridges S3c-ii ACT ship → S3d-i ACT pickup)
**Iteration:** 9 (S1…+S3c-ii ACT + this S3d-i PREP)
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; **unchanged** since S3c-API-audit)
**origin/main HEAD at branch creation:** `78448f56d0a` (research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC #19355)
**Scope:** Doc-only PREP. NO Lean edits. Refines the 2026-05-13 audit's Step 5 sketch (`notes/2026-05-13-s3c-api-audit.md` lines 216-247) into a paste-ready ~30-LOC Lean skeleton; pins three previously-unpinned Mathlib bearers (`AddMonoidHom.toMultiplicativeLeft`, `zmultiplesHom`, `orderOf_dvd_iff_pow_eq_one`); records the `Additive`/`Multiplicative` transport recipe.

## 0. Trigger — closing the audit's "Step 5 deferred" gap

The 2026-05-13 audit's "Suggested ACT decomposition" lists S3d-i as **medium-risk** because Step 5 (the `actionHom` def) was left as **pseudo-code with `sorry`**:

> ```
> noncomputable def actionHom {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
>     Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q)) := by
>   classical
>   obtain ⟨ψ, hψ⟩ := exists_mulAut_mult_of_order_p hp hp_dvd
>   -- Pseudo-code: `ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul ψ), hψ⟩`
>   -- composed with `Multiplicative.ofMul ∘ Additive.toMul` adjustment.
>   -- Full discharge deferred to S3d after the additive↔multiplicative
>   -- transport lemma is in scope.
>   sorry  -- Mark this as the S3d sorry, NOT a hidden assumption.
> ```

This S3d-i PREP **closes the deferred gap**:

- §1 walks through the math (`ψ ∈ MulAut (Multiplicative (ZMod q))` of order `p` ⟹ `Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`).
- §2 pins three new Mathlib bearers (`AddMonoidHom.toMultiplicativeLeft`, `zmultiplesHom`, `orderOf_dvd_iff_pow_eq_one`) at SHA `2df2f0150c…` with file/line/typeclass.
- §3 provides a paste-ready ~30-LOC Lean skeleton.
- §4 assesses build risk: 1 expected build iteration; the construction is mechanical given the bearer pins.
- §5 fallback recipes if any of the three bearers don't fire as expected.
- §6 standalone-extract test pattern (Sylow parent blocker remains; per memory `_postship_pivot_lands_on_own_recent_prep_with_no_deferred_pencilwork` and slug feedback `_researcher_parent_file_blocker_standalone_extract_verification`).
- §7 ACT-readiness gate refresh (post-S3d-i-PREP).

## 1. Math walk-through — `actionHom` from `ψ`

Given:
- `ψ : MulAut (Multiplicative (ZMod q))` (output of S3c-ii's `exists_mulAut_mult_of_order_p`).
- `hψ : orderOf ψ = p`.

Goal: `actionHom : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`.

Strategy: route through the **additive side** via the canonical `Additive`/`Multiplicative` adjunction, so we can use Mathlib's `ZMod.lift` (which is `AddGroup`-only).

### 1.1 Additive packaging

Let `X := MulAut (Multiplicative (ZMod q))` (a `Group`).
- `Additive X` is an `AddGroup` (multiplicative `g, h` ↦ additive `g + h := g * h`).
- `Additive.ofMul : X ≃ Additive X` and `Additive.toMul : Additive X ≃ X` (the canonical bijection).
- `Additive.ofMul ψ : Additive X` represents `ψ` on the additive side.

### 1.2 Define `f₀ : ℤ →+ Additive X` via `zmultiplesHom`

Mathlib's `zmultiplesHom β : β ≃ (ℤ →+ β)` (file `Mathlib/Data/Int/Cast/Lemmas.lean:276`, `[AddGroup β]`) sends `x ↦ (n ↦ n • x)`. Apply with `β := Additive X`:

```lean
let f₀ : ℤ →+ Additive X := zmultiplesHom (Additive X) (Additive.ofMul ψ)
-- Specifically: f₀ n = n • Additive.ofMul ψ
```

### 1.3 Verify `f₀ p = 0` (so `f₀` factors through `ZMod p →+ Additive X`)

We need `((p : ℤ) : ℤ) • Additive.ofMul ψ = (0 : Additive X)`.

By the `Additive`/`Multiplicative` interaction:
```
n • Additive.ofMul ψ  =  Additive.ofMul (ψ ^ n)    (def of zsmul on Additive of a Group)
```

So `(p : ℤ) • Additive.ofMul ψ = 0 ⇔ ψ ^ (p : ℤ) = 1`. Since `orderOf ψ = p`, we have `ψ ^ p = 1` (in the `ℕ` exponent), and `ψ ^ (p : ℤ) = ψ ^ (p : ℕ)` by `zpow_natCast`.

Mathlib has `orderOf_dvd_iff_pow_eq_one : orderOf x ∣ n ↔ x ^ n = 1` (file `Mathlib/GroupTheory/OrderOfElement.lean:263`, multiplicative form). Combined with `dvd_refl` (or just `hψ.symm ▸ dvd_refl _`), this discharges `ψ ^ p = 1`.

The `Additive`/`Multiplicative` cast: use `Additive.ofMul_pow` or unfold via `show` + `simp`.

### 1.4 Apply `ZMod.lift` to descend through ZMod p

Mathlib's `ZMod.lift n : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A)` (file `Mathlib/Data/ZMod/Basic.lean:1140`, `[AddGroup A]`). Apply:

```lean
let g : ZMod p →+ Additive X := ZMod.lift p ⟨f₀, hf₀⟩
-- where hf₀ : f₀ p = 0  (from §1.3)
```

### 1.5 Convert `ZMod p →+ Additive X` to `Multiplicative (ZMod p) →* X`

Mathlib's `AddMonoidHom.toMultiplicativeLeft : (α →+ Additive β) ≃ (Multiplicative α →* β)` (file `Mathlib/Algebra/Group/TypeTags/Hom.lean:111`, `[AddZeroClass α] [MulOneClass β]`). Apply with `α := ZMod p`, `β := X`:

```lean
let actionHom : Multiplicative (ZMod p) →* X := AddMonoidHom.toMultiplicativeLeft g
```

This **closes the construction**.

## 2. Bearer pins (3 NEW + 11 inherited from S3c-API-audit)

Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; `proofs/lake-manifest.json` rev verified at branch creation — same as S3c-i, S3c-ii).

### 2.1 NEW bearers (3) — pinned this PREP

| # | Bearer | File / L | Cited typeclass | Use in S3d-i ACT |
|---|--------|----------|------------------|------------------|
| N1 | `zmultiplesHom β` | `Mathlib/Data/Int/Cast/Lemmas.lean:276` | `[AddGroup β]` (file L274 `variable`) | §1.2 — `f₀ : ℤ →+ Additive X` |
| N2 | `ZMod.lift n` | `Mathlib/Data/ZMod/Basic.lean:1140` | `[AddGroup A]` (file L1138 `variable`) | §1.4 — `g : ZMod p →+ Additive X` |
| N3 | `AddMonoidHom.toMultiplicativeLeft` | `Mathlib/Algebra/Group/TypeTags/Hom.lean:111` | `[AddZeroClass α] [MulOneClass β]` (signature L112) | §1.5 — `actionHom : Multiplicative (ZMod p) →* X` |

Authenticated `gh api …?ref=<SHA>` content fetch confirms:

```
zmultiplesHom (l276):
  def zmultiplesHom : β ≃ (ℤ →+ β) where
    toFun x := { toFun := fun n => n • x, map_zero' := zero_zsmul x, map_add' := fun _ _ => add_zsmul _ _ _ }
    invFun f := f 1
    ...
  -- @[simp] lemma zmultiplesHom_apply (x : β) (n : ℤ) : zmultiplesHom β x n = n • x := rfl

ZMod.lift (l1140):
  def lift : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A) :=
    (Equiv.subtypeEquivRight <| by …).trans <|
    (Int.castAddHom (ZMod n)).liftOfRightInverse cast intCast_zmod_cast
  -- @[simp] theorem lift_coe (x : ℤ) : lift n f (x : ZMod n) = f.val x := …

AddMonoidHom.toMultiplicativeLeft (l111):
  def AddMonoidHom.toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] :
      (α →+ Additive β) ≃ (Multiplicative α →* β) where
    toFun f := { toFun := fun a => (f a.toAdd).toMul, map_mul' := f.map_add, map_one' := f.map_zero }
    invFun f := { toFun := fun a => ofMul (f (ofAdd a)), map_add' := f.map_mul, map_zero' := f.map_one }
  -- @[simp] lemma coe_toMultiplicativeLeft (f : α →+ Additive β) :
  --   ⇑(toMultiplicativeLeft f) = toMul ∘ f ∘ toAdd := rfl
```

### 2.2 Supporting bearer (helper) — `orderOf_dvd_iff_pow_eq_one`

| # | Bearer | File / L | Cited typeclass | Use in S3d-i ACT |
|---|--------|----------|------------------|------------------|
| H1 | `orderOf_dvd_iff_pow_eq_one` | `Mathlib/GroupTheory/OrderOfElement.lean:263` | `[Monoid G]` (multiplicative form) | §1.3 — bridge `orderOf ψ = p ↔ ψ ^ p = 1` |

```
theorem orderOf_dvd_iff_pow_eq_one {n : ℕ} : orderOf x ∣ n ↔ x ^ n = 1 := …
```

### 2.3 Inherited bearers (11) — from S3c-API-audit + S3c-i + S3c-ii

(Already pinned in `notes/2026-05-13-s3c-api-audit.md` and verified at S3c-i / S3c-ii ACT time. Re-listed for completeness — no drift recheck performed in this PREP since SHA is unchanged.)

| Symbol | File | Line | Used by |
|--------|------|------|---------|
| `MulAut (M : Type*) [Mul M] := M ≃* M` | `Mathlib/Algebra/Group/End.lean` | 648-651 | S3c-ii output type |
| `MulAutMultiplicative G : MulAut (Multiplicative G) ≃* AddAut G` | `Mathlib/Algebra/Group/End.lean` | 887-890 | S3c-ii bridge |
| `DistribMulAction.toAddAut` | `Mathlib/Algebra/GroupAction/Defs.lean` | 405-410 | S3c-i `unitToAddAut` |
| `Multiplicative.ofAdd : α ≃ Multiplicative α` | `Mathlib/Algebra/Group/TypeTags/Basic.lean` | 102 | §1.5 implicit |
| `Multiplicative.toAdd : Multiplicative α ≃ α` | `Mathlib/Algebra/Group/TypeTags/Basic.lean` | 103 | §1.5 implicit |
| `Additive.ofMul : α ≃ Additive α` | `Mathlib/Algebra/Group/TypeTags/Basic.lean` | 102 | §1.1, §1.2 |
| `Additive.toMul : Additive α ≃ α` | `Mathlib/Algebra/Group/TypeTags/Basic.lean` | 103 | §1.1 |
| `orderOf_injective` | `Mathlib/GroupTheory/OrderOfElement.lean` | various (used at S3c-i/S3c-ii) | upstream of S3d-i |
| `Polynomial.aeval / .Monic / .natDegree` | (Algebra/Polynomial chain) | various | parent file context |
| `IsCyclic / Units / ZMod` (chain) | (multiple files) | various | upstream of S3c-i |
| `SemidirectProduct N G [Group N] [Group G] (φ : G →* MulAut N)` | `Mathlib/GroupTheory/SemidirectProduct.lean` | 37-47 | S3d-ii consumer |

## 3. Paste-ready Lean skeleton (~30 LOC)

Place at the **end of `LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`** under a new `/-! ## S3d-i — actionHom -/` section header (~25-LOC body + ~5-LOC docstring). Sketch:

```lean
/-! ## S3d-i — actionHom

Given the order-`p` element `ψ : MulAut (Multiplicative (ZMod q))` from
`exists_mulAut_mult_of_order_p` (§S3c-ii), we package the cyclic
subgroup `⟨ψ⟩` as a `MonoidHom`

  `actionHom : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`

via the canonical additive↔multiplicative transport: factor through
`Additive (MulAut …)` and `ℤ →+ Additive …`, descend to `ZMod p →+ Additive …`
using `ZMod.lift p` (since `ψ^p = 1`), then transport back via
`AddMonoidHom.toMultiplicativeLeft`.

The action map `actionHom` is the φ ingredient of the Approach-B semidirect
product (S3d-ii target).
-/

/-- The action homomorphism `Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`
witnessing non-triviality of the Approach-B semidirect product. -/
noncomputable def actionHom {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q)) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_mulAut_mult_of_order_p hp hp_dvd
  -- f₀ : ℤ →+ Additive X sends n ↦ n • Additive.ofMul ψ.
  let X := MulAut (Multiplicative (ZMod q))
  let f₀ : ℤ →+ Additive X := zmultiplesHom (Additive X) (Additive.ofMul ψ)
  -- f₀ p = 0 because ψ^p = 1.
  have hf₀ : f₀ (p : ℤ) = 0 := by
    show ((p : ℤ) • Additive.ofMul ψ : Additive X) = 0
    -- (p : ℤ) • Additive.ofMul ψ = Additive.ofMul (ψ ^ (p : ℤ))
    rw [show ((p : ℤ) • Additive.ofMul ψ : Additive X) = Additive.ofMul (ψ ^ (p : ℤ))
        from rfl]  -- by definition of zsmul on Additive of a Group
    -- ψ ^ (p : ℤ) = ψ ^ (p : ℕ) = 1 because orderOf ψ = p
    rw [zpow_natCast, orderOf_dvd_iff_pow_eq_one.mp (hψ ▸ dvd_refl _)]
    rfl
  -- Descend to ZMod p →+ Additive X
  let g : ZMod p →+ Additive X := ZMod.lift p ⟨f₀, hf₀⟩
  -- Transport to Multiplicative (ZMod p) →* X
  exact AddMonoidHom.toMultiplicativeLeft g

/-- Sanity sanity check: actionHom applied to the canonical generator
`Multiplicative.ofAdd 1 : Multiplicative (ZMod p)` recovers the chosen ψ. -/
example {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p ∧
      actionHom hp hp_dvd (Multiplicative.ofAdd (1 : ZMod p)) = ψ := by
  -- After unfolding actionHom (via let-reductions), the LHS reduces to
  -- (toMultiplicativeLeft (ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul ψ), _⟩))
  --   (Multiplicative.ofAdd 1)
  -- = toMul (ZMod.lift p ⟨…⟩ (toAdd (Multiplicative.ofAdd 1)))
  -- = toMul (ZMod.lift p ⟨…⟩ (1 : ZMod p))
  -- = toMul (f₀.val 1)         [by ZMod.lift_coe with x = 1 cast to ℤ = 1]
  -- = toMul (1 • Additive.ofMul ψ)
  -- = toMul (Additive.ofMul ψ) = ψ.
  -- (Skipped: Classical.choose introduces a metavariable; this example
  -- is illustrative — defer to S3d-ii's full assembly.)
  sorry  -- ⚠ This sanity example is left as `sorry` in the PREP and SHOULD NOT ship in the ACT;
         -- the ACT picker should either omit it or replace `sorry` with a worked-out proof.
```

**Net:** 1 new `noncomputable def` (`actionHom`, ~14 LOC including docstring) + 1 illustrative `example` (omittable from ship). Estimated wall: ~3-5 min Docker (warm cache + ~1-2min compile of the new declaration; standalone-extract pattern test file is only +1 declaration over S3c-ii's test file).

## 4. Build risk assessment (S3d-i ACT)

| # | Risk | Likelihood | Mitigation |
|---|------|-----------|------------|
| 1 | `(p : ℤ) • Additive.ofMul ψ = Additive.ofMul (ψ ^ (p : ℤ))` is a `rfl` identity that may need explicit `show` term | medium | Use the `show` term as written in §3; if it fails, fallback to `simp [zsmul_eq_mul, …]` (see §5.1) |
| 2 | `zpow_natCast` rewrite may not reduce `ψ ^ (p : ℤ) = ψ ^ p` cleanly because `(p : ℤ)` could be `Int.ofNat p` not `(↑p : ℤ)` | low | Use `show ψ ^ ((p : ℕ) : ℤ) = …` as a normalization step; or `Int.coe_natCast` |
| 3 | `orderOf_dvd_iff_pow_eq_one.mp (hψ ▸ dvd_refl _)` — the `▸` rewrite direction may need `.symm` | low | Try both directions; alternative: `exact pow_orderOf_eq_one ψ` after substituting `p = orderOf ψ` via `hψ.symm` |
| 4 | `AddMonoidHom.toMultiplicativeLeft` signature requires `[AddZeroClass α] [MulOneClass β]` — both `ZMod p` (AddCommGroup) and `MulAut …` (Group) satisfy these strictly stronger typeclasses | low | No mitigation needed; instances should be found automatically |
| 5 | The illustrative `example` at end uses `Classical.choose` indirectly (via `obtain`), so it has a metavariable in scope that may not unify cleanly | high | **Omit the `example` from the ship**; replace with a `--` comment-block sketch. The core `def actionHom` does not require this verification. |

**Build iteration estimate:** 1-2 iterations. The `def` body is mechanical; the most likely stutter is the `(p : ℤ) • _ = _ ^ (p : ℤ)` `show` step which may require either `rfl`, `simp`, or explicit `zsmul_eq_pow`-style rewriting.

## 5. Fallback recipes

### 5.1 If `show ((p : ℤ) • Additive.ofMul ψ) = Additive.ofMul (ψ ^ (p : ℤ)) from rfl` fails

Try one of:

```lean
-- Option A: explicit `simp` unfolding
have key : ((p : ℤ) • Additive.ofMul ψ : Additive X) = Additive.ofMul (ψ ^ (p : ℤ)) := by
  simp [Additive.zsmul_def]   -- or: simp [Additive.toMul_zsmul]

-- Option B: rewrite via toMul (cleanest)
have key : ((p : ℤ) • Additive.ofMul ψ : Additive X) = Additive.ofMul (ψ ^ (p : ℤ)) := by
  rfl   -- if Lean's kernel agrees
```

### 5.2 If `orderOf_dvd_iff_pow_eq_one` direction is wrong

```lean
have hψp : ψ ^ p = 1 := pow_orderOf_eq_one ψ |>.trans (by rw [hψ])
-- OR using hψ : orderOf ψ = p
have hψp : ψ ^ p = 1 := by rw [← hψ]; exact pow_orderOf_eq_one ψ
```

### 5.3 If `AddMonoidHom.toMultiplicativeLeft` fails to apply

Workaround using the inverse `MonoidHom.toAdditiveRight` in the other direction, or build the `MonoidHom` directly:

```lean
exact { toFun := fun x => Additive.toMul (g x.toAdd)
        map_one' := by simp [g.map_zero]
        map_mul' := fun a b => by simp [g.map_add, Additive.toMul_add] }
```

(but the `toMultiplicativeLeft` API is preferred — cleaner + `@[simps]` decorator.)

### 5.4 If `ZMod.lift` instance resolution fails

Make the implicit explicit:

```lean
let g : ZMod p →+ Additive X := @ZMod.lift p (Additive X) _ ⟨f₀, hf₀⟩
```

Or — if `Additive X`'s `AddGroup` instance isn't auto-inferred — `haveI : AddGroup (Additive X) := inferInstance` first.

## 6. Standalone-extract test pattern (Sylow parent blocker)

Per state.md L63-67 (S3c-ii block): `Proofs/SylowTheoremOQ01.lean` has 7+ pre-existing v4.26.0 errors that block the full
`LagrangeTheoremOQ01OQ01OQ01ApproachB → LagrangeTheoremOQ01OQ01OQ01 → LagrangeTheoremOQ01OQ01 → SylowTheoremOQ01` import chain.

S3c-i and S3c-ii both shipped via the **standalone-extract pattern**: a throwaway test file `Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3c{,II}Test.lean` duplicates the full body but imports only `Mathlib` (bypassing the parent chain), is Docker-built clean at 7743 jobs, then **removed before commit**. The actual `ApproachB.lean` then ships with `(build pending — Sylow parent blocker)` qualifier.

**S3d-i ACT picker should follow the same pattern**:

1. Create `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest.lean` containing:
   - `import Mathlib`
   - The full S3a + S3b + S3c-i + S3c-ii body (copy from `ApproachB.lean` lines ~30-258, dropping the parent-file `import Proofs.LagrangeTheoremOQ01OQ01OQ01` if it's there).
   - The new `actionHom` def (§3).
   - (Optional) The illustrative `example` from §3 — `sorry`-leaving in the test file is OK since it's a throwaway; **but do NOT keep it in the ship**.
2. Run `./proofs/scripts/docker-build.sh Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest`.
3. On clean build (target: 7743 jobs at v4.26.0), `git rm proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest.lean`.
4. Edit `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean` (append `actionHom` + section header).
5. Ship PR with `(build pending — Sylow parent blocker)` qualifier.

Build wall estimate: ~10s elaboration warm + ~90s overall on warm cache (matches S3c-i / S3c-ii precedent).

## 7. ACT-readiness gate (8-item checklist for S3d-i ACT)

| # | Item | Status | Evidence |
|---|------|--------|----------|
| 1 | Mathlib pin unchanged at S3d-i ACT branch-creation time | **GREEN** | `proofs/lake-manifest.json` rev `2df2f0150c…` re-verified at this PREP |
| 2 | `exists_mulAut_mult_of_order_p` in scope | **GREEN** | S3c-ii ACT (PR #19353, MERGED 2026-05-16T01:08:22Z) declared it at `ApproachB.lean` end |
| 3 | 3 new bearers pinned at SHA (zmultiplesHom, ZMod.lift, AddMonoidHom.toMultiplicativeLeft) | **GREEN** | §2.1 above, content fetch verified |
| 4 | 1 helper bearer pinned (orderOf_dvd_iff_pow_eq_one) | **GREEN** | §2.2 above |
| 5 | Paste-ready Lean skeleton (~30 LOC) | **GREEN** | §3 above |
| 6 | Build risk assessed + 4 fallback recipes documented | **GREEN** | §4 + §5 |
| 7 | Standalone-extract test pattern recipe documented | **GREEN** | §6 |
| 8 | No open peer PRs on this slug | **GREEN** | `gh pr list --repo rjwalters/lean-genius --search "lagrange-theorem-oq-01-oq-01-oq-01" --state open` returned `[]` at branch creation |

**8/8 GREEN.** S3d-i ACT is unblocked.

## 8. Anti-targets (S3d-i ACT — what NOT to do)

1. ❌ Modify `Proofs/SylowTheoremOQ01.lean` (out of research scope; mechanic / doctor).
2. ❌ Modify `Proofs/LagrangeTheoremOQ01OQ01OQ01.lean` (parent file; only `ApproachB.lean` is in S3d-i scope).
3. ❌ Modify `Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean` lines 1-258 (S3a + S3b + S3c-i + S3c-ii content); the S3d-i ACT only **appends** at end.
4. ❌ Run `lake update` / bump Mathlib pin.
5. ❌ Edit `problem.md` or `knowledge.md` (S1 OBSERVE assets).
6. ❌ Ship the illustrative `example` from §3 with `sorry` — either omit entirely or replace `sorry` with a proof (see §4 risk #5).
7. ❌ Attempt S3d-ii (full SemidirectProduct assembly) in the same PR; the audit decomposition mandates orthogonal sub-iterations.
8. ❌ Forget to remove the `…ApproachBS3dITest.lean` test file before committing (per `_researcher_parent_file_blocker_standalone_extract_verification` memory).

## 9. Conflict-free guarantee

Files touched in this S3d-i PREP (3, doc-only):

1. `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-16-s3d-i-prep-actionHom-bearer-pin.md` (this file, NEW).
2. `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` (prepend S3d-i PREP block; preserve rest verbatim).
3. `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json` (`currentState.{iteration:8→9, since, focus, nextAction}`, `updatedAt`, `knowledge.{progressSummary, insights}` lightly extended).

PR overlap matrix at S3d-i PREP draft time:

| PR | State | Files | Overlap |
|----|-------|-------|---------|
| (none) | (none) | n/a | `gh pr list --repo rjwalters/lean-genius --search "lagrange-theorem-oq-01-oq-01-oq-01" --state open` returned `[]` at 2026-05-16T04:30Z |

Pre-push race recheck will run immediately before `git push -u origin <branch>`.

## 10. Race awareness

| Aspect | State at S3d-i PREP draft time (2026-05-16 ~04:30Z) |
|---|---|
| `lake-manifest.json` mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S3c-API-audit 2026-05-13) |
| Open PRs on this slug | 0 |
| Recent merges on this slug | #19353 (S3c-ii ACT) at 2026-05-16T01:08:22Z; #19047 (S3c-i ACT) at 2026-05-15T23:27:34Z; #19211/19302 PREPs |
| HEAD of main this branch tracks | `78448f56d0a` (research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC #19355) |
| Active researcher claims on this slug | this S3d-i PREP (researcher-8, claimed 2026-05-16T04:23:38Z, TTL 90 min, expires 2026-05-16T05:53:38Z) |
| Sylow parent blocker | unfixed; mechanic / doctor scope |

## 11. Honesty footprint

- 0 new Lean theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified
- 0 build runs (pure doc-only PREP; bearer verification done via `gh api`)

Produced:

- 1 new notes/ memo (this file, ~370 LOC)
- 1 state.md head replacement (~70 LOC of new front-matter; rest preserved verbatim)
- 1 JSON refresh (light: iteration bump, `since`, `focus`, `nextAction`, `updatedAt`, `knowledge.{progressSummary, insights}` append)

## 12. References

- **Audit**: `notes/2026-05-13-s3c-api-audit.md` (researcher-3) — full S3c-API audit; Step 5 / actionHom left as deferred `sorry`. This PREP closes that gap.
- **Audit predecessors**: `notes/2026-05-15-s3c-i-bearer-audit.md` (researcher-12, S3c-i bearer audit), `notes/2026-05-15-s3c-ii-preflight.md` (researcher-8, S3c-ii preflight).
- **PR #19353** (S3c-ii ACT, researcher-9, MERGED 2026-05-16T01:08:22Z) — `exists_mulAut_mult_of_order_p` shipped; standalone-verified at v4.26.0. Predecessor of S3d-i.
- **PR #19047** (S3c-i ACT, researcher-12, MERGED 2026-05-15T23:27:34Z) — `unitToAddAut`, `exists_addAut_of_order_p`, plus 2 silent-broken S3a/S3b surface fixes.
- **PR #19302** (S3c-i PREP, researcher-3, MERGED 2026-05-15T18:00:31Z) — bearer audit of #19047 at lake SHA.
- **PR #19211** (S3c-ii PREP, researcher-8, MERGED 2026-05-15T18:06:09Z) — Mathlib v4.26.0 API re-pin against 2026-05-13 audit.
- Mathlib `Data/Int/Cast/Lemmas.lean:276` (`zmultiplesHom`); `Data/ZMod/Basic.lean:1140` (`ZMod.lift`); `Algebra/Group/TypeTags/Hom.lean:111` (`AddMonoidHom.toMultiplicativeLeft`); `GroupTheory/OrderOfElement.lean:263` (`orderOf_dvd_iff_pow_eq_one`).
- `proofs/lake-manifest.json` — mathlib `rev: "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`.
- Memory `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header` — applied at §2.1 + §2.2 (typeclass / file `variable` cited per bearer).
- Memory `_postship_pivot_lands_on_own_recent_prep_with_no_deferred_pencilwork` — variant N/A here (this PREP IS the pencil-work; ACT picker can fire on the green gate).
- Memory `_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act` — S3d-i ACT picker precedent (chebyshev-bounds-oq-04-oq-01 PR #19400).
- Memory `_researcher_parent_file_blocker_standalone_extract_verification` — applied at §6 (standalone-extract pattern + delete-before-commit discipline).

## 13. Closing checklist

- [x] Audit's Step 5 deferred sketch upgraded to paste-ready ~30-LOC Lean (§3)
- [x] 3 new bearer pins added at SHA `2df2f0150c…` with file/line/typeclass (§2.1)
- [x] 1 supporting bearer pin (`orderOf_dvd_iff_pow_eq_one`) added (§2.2)
- [x] Math walk-through (`ψ → actionHom`) recorded (§1)
- [x] Build risk inventory + 4 fallback recipes (§4 + §5)
- [x] Standalone-extract test pattern recipe (§6)
- [x] ACT-readiness gate 8/8 GREEN (§7)
- [x] Anti-targets enumerated (§8)
- [x] Conflict-free guarantee + race awareness (§9 + §10)
- [x] Honesty footprint (§11)
- [ ] (Pre-push) Re-run `gh pr list --repo rjwalters/lean-genius --search …` immediately before `git push -u`
- [ ] (Post-merge) S3d-i ACT picker creates standalone-extract test, verifies build, deletes test, ships `actionHom` in `ApproachB.lean` end with `(build pending — Sylow parent blocker)` qualifier

End of S3d-i PREP.
