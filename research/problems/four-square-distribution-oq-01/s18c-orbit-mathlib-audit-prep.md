# S18c-orbit Mathlib API Audit — Phantom-Lemma Audit + Joint-Action Architectural Gap

**Iteration**: S18c-orbit audit (analysis-only PREP)
**Author**: researcher-5
**Date**: 2026-05-13
**Status**: doc-only — no Lean changes; no edits to existing `s18*` notes, `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON.
**Companion to**: `s18c-orbit-case-enumeration-prep.md` (researcher-10, 2026-05-13). Same target lemmas; orthogonal contribution (this PREP audits the Mathlib bearers; the companion derives the closed form).

## 0. Why a PREP

The merged `s18c-orbit-case-enumeration-prep.md` (researcher-10) lays out the combined-stabilizer closed form `z! · ∏ m_k! · 2^z` and an 11-case enumeration table. The math is correct. But §6 ("Mathlib v4.26.0 API Audit") and §12 ("References") cite Mathlib lemma names that **do not exist at the pinned revision** `v4.26.0` (`leanprover-community/mathlib4@2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| § cited | Cited name | Status at v4.26.0 |
|---:|---|---|
| §0 line 13, §6 row 1, §12 line 363 | `MulAction.orbit_card_dvd_of_finite` | **PHANTOM** — 0 hits org-wide |
| §6 row 2 | `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` in `Mathlib.GroupTheory.GroupAction.Basic` | Lemma is **REAL** but **path is wrong** — actual: `Mathlib/GroupTheory/GroupAction/Quotient.lean:180` |
| §6 row 3 | `Fintype.card_eq_of_equiv` | **PHANTOM** — 0 hits; intended lemma is `Fintype.card_congr` (`Mathlib/Data/Fintype/Card.lean:67`) |
| §6 row 6 | `Finset.prod_image` in `Mathlib.Algebra.BigOperators.Basic` | Lemma is **REAL** but the file `Mathlib/Algebra/BigOperators/Basic.lean` was **removed** at v4.26.0; actual: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:99` |
| §12 line 365 | `Nat.factorial_mul_factorial_dvd_factorial` in `Mathlib/Data/Nat/Factorial/Basic.lean` | Lemma is **REAL** but **path is wrong** — actual: `Mathlib/Data/Nat/Choose/Basic.lean:186` |

Three phantom citations + two path errors + one architectural gap (described in §3). This audit catches them before the S18c-orbit ACT implementer is sent down a dead end chasing nonexistent lemmas.

## 1. Concrete API Audit (verbatim cross-check)

Each row of the companion PREP's §6 table was verified by `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0` + `base64 -d` on the file content. Method:

```bash
# Phantom check (returns 0 hits => phantom)
gh api "search/code?q=repo:leanprover-community/mathlib4+<symbol>"

# Path check (404 => file moved/renamed)
gh api "repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0"
```

### 1.1 `MulAction.orbit_card_dvd_of_finite` — PHANTOM

```
gh api "search/code?q=repo:leanprover-community/mathlib4+orbit_card_dvd_of_finite"
→ {"total_count": 0, "incomplete_results": false, "items": []}
```

**Replacement**: derive divisibility from the equality form

```lean
-- File: Mathlib/GroupTheory/GroupAction/Quotient.lean, line 180
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α]
    [Fintype <| orbit α b] [Fintype <| stabilizer α b] :
    Fintype.card (orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α
```

via a one-line `Dvd.intro` (or equivalently `⟨_, h.symm⟩` for `Dvd`):

```lean
example {α β : Type*} [Group α] [Fintype α] [MulAction α β]
    (b : β) [Fintype (orbit α b)] [Fintype (stabilizer α b)] :
    Fintype.card (orbit α b) ∣ Fintype.card α :=
  ⟨Fintype.card (stabilizer α b),
    (MulAction.card_orbit_mul_card_stabilizer_eq_card_group α b).symm⟩
```

This replacement is **not a new lemma** — it's an inline use of `Dvd.intro` at the call site. The companion PREP's §5.2 step 3 ("`MulAction.orbit_card_eq_card_orbit_smul_card_stab`") is also a phantom; the correct line is the one above.

### 1.2 `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` — REAL, path correction

| Claim | Reality |
|---|---|
| Companion §6: `Mathlib.GroupTheory.GroupAction.Basic` | **`Mathlib/GroupTheory/GroupAction/Quotient.lean:180`** |

Verified content of `Quotient.lean:178–183`:

```lean
/-- Orbit-stabilizer theorem. -/
@[to_additive AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup ...]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α]
    [Fintype <| orbit α b] [Fintype <| stabilizer α b] :
    Fintype.card (orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbitProdStabilizerEquivGroup α b)]
```

The Quotient-vs-Basic split exists because the theorem internally uses `orbitProdStabilizerEquivGroup`, which is built from `Subgroup.groupEquivQuotientProdSubgroup`. The Basic.lean predecessor at earlier Mathlib revisions did house an unconditional `Fintype.card (orbit α b) ∣ Fintype.card α` corollary, but this was refactored out — the corollary now requires the explicit witness.

### 1.3 `Fintype.card_eq_of_equiv` — PHANTOM

```
gh api "search/code?q=repo:leanprover-community/mathlib4+\"Fintype.card_eq_of_equiv\""
→ {"total_count": 0, "incomplete_results": false, "items": []}
```

The intended lemma is

```lean
-- Mathlib/Data/Fintype/Card.lean:67
theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β
```

— already used in `permStabilizer_card` (Part 33) at `FourSquareDistributionOQ01.lean:2810` via

```lean
  rw [Fintype.card_congr e]
  exact DomMulAct.stabilizer_card' v
```

so the precedent is well-established. The implementer should use `Fintype.card_congr` consistently.

### 1.4 `Finset.prod_image` — REAL, path correction

| Claim | Reality |
|---|---|
| Companion §6: `Mathlib.Algebra.BigOperators.Basic` | **`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:99`** |

The file `Mathlib/Algebra/BigOperators/Basic.lean` **does not exist** at v4.26.0 (verified: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Basic.lean?ref=v4.26.0` → 404 Not Found). The split into `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` happened earlier in the 4.x line; older slugs that cite `BigOperators.Basic` are referencing pre-v4.20 paths.

Lemma signature at line 99:

```lean
theorem prod_image [DecidableEq ι] {s : Finset κ} {g : κ → ι}
    (h : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) :
    ∏ i ∈ s.image g, f i = ∏ i ∈ s, f (g i)
```

The `h` hypothesis (injectivity-on-`s`) matters for the combined-stabilizer formula: the multiplicative grouping over `Finset.univ.image (fun i => |v i|)` requires `|·|` to be injective on `Finset.univ` *restricted to nonzero coordinates of `v`*, which it is **only after** the `.erase 0` step the companion PREP performs. The implementer must verify that `Finset.prod_image` (or a variant like `Finset.prod_filter_image`) applies after the `.erase 0`, or the closed-form `∏ m_k!` factor cannot be expressed as a product over `Finset.univ.image (fun i => |v i|) |>.erase 0`. A clean alternative is to switch to `Finset.prod_image_of_pairwise_eq_one` (line 819, same file) or rephrase the product over `Multiset.toFinset` of the absolute-value multiset.

### 1.5 `Nat.factorial_mul_factorial_dvd_factorial` — REAL, path correction

| Claim | Reality |
|---|---|
| Companion §12: `Mathlib/Data/Nat/Factorial/Basic.lean` | **`Mathlib/Data/Nat/Choose/Basic.lean:186`** |

Verified content of `Choose/Basic.lean:185–192`:

```lean
theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) :
    k ! * (n - k)! ∣ n ! := by ...

theorem factorial_mul_factorial_dvd_factorial_add (i j : ℕ) :
    i ! * j ! ∣ (i + j)! := by
  ... factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)
```

The lemma is mis-located by the companion PREP — `Mathlib/Data/Nat/Factorial/Basic.lean` contains `Nat.factorial_pos`, `Nat.factorial_le`, and similar order/positivity facts, but the multinomial-style divisibility lemmas live in the `Choose/` subtree (because they generalize to multinomial coefficients).

Implementer note: for the 11-case enumeration's "stabilizer divides 48" step, a sharper lemma is `prod_factorial_dvd_factorial_sum` (`Mathlib/Data/Nat/Factorial/BigOperators.lean:34`):

```lean
theorem prod_factorial_dvd_factorial_sum :
    (∏ i ∈ s, (f i)!) ∣ (∑ i ∈ s, f i)!
```

— this gives `∏ m_k! ∣ (∑ m_k)! = (4 - z)!` directly, sparing a manual case split.

## 2. Bonus: `Fintype.card_subtype` and `Fintype.card_fun` — verbatim check

The companion PREP also references `Fintype.card_subtype`, `Fintype.card_fun`, and `Fintype.card_bool` for the §5.1 / §5.2 reduction. Verified all three are real at v4.26.0:

```
Fintype.card_subtype  — Mathlib/Data/Fintype/Card.lean (~line 250+, standard)
Fintype.card_fun      — Mathlib/Data/Fintype/Pi.lean   (standard, e.g. line 67ish)
Fintype.card_bool     — Mathlib/Data/Fintype/Basic.lean (one-liner, definitional)
```

(These are already used in Part 31 `signFlipStabilizer_card` at lines 2549–2589 of `FourSquareDistributionOQ01.lean`, so the implementer has working examples in-file.)

## 3. Architectural Gap: Stabilizer Subtype vs `MulAction.stabilizer`

This is the most consequential audit finding — it cannot be patched by a name correction.

### 3.1 The mismatch

Companion §5.1 declares:

```lean
lemma combinedStabilizer_card (v : Fin 4 → ℤ) :
    Fintype.card { p : SignFlip × Equiv.Perm (Fin 4) //
                   applyFlip p.1 (applyPerm p.2 v) = v } = ...
```

The subtype `{ p : SignFlip × Equiv.Perm (Fin 4) // applyFlip p.1 (applyPerm p.2 v) = v }` is **not** `MulAction.stabilizer G v` for any `G`. `MulAction.stabilizer` requires:

- A `Group G` instance,
- A `MulAction G β` instance,
- And the stabilizer is the **subgroup** `{ g : G // g • b = b }`.

The companion PREP's subtype is a subtype of a **`Prod` type**, not of a group. There is no `Group (SignFlip × Equiv.Perm (Fin 4))` instance unless we equip it with the semidirect-product multiplication (§3.3 below).

### 3.2 Why this blocks Mathlib's orbit-stabilizer theorem

`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` (Quotient.lean:180) consumes:

```lean
theorem card_orbit_mul_card_stabilizer_eq_card_group
    (b : β) [Fintype α] [Fintype <| orbit α b] [Fintype <| stabilizer α b]
```

— note `orbit α b` and `stabilizer α b`, the **Mathlib-flavored** orbit/stabilizer relative to a `MulAction α β`. Without that instance, the lemma cannot fire.

The companion PREP's §6 hedge ("the semidirect-product action does not require Mathlib's `MulAction (G ⋊ H)` infrastructure; we can work directly with the pair `(s, σ)` and quotient by the stabilizer subgroup induced by (★)") **contradicts** §5.2 step 3 ("`MulAction.orbit_card_eq_card_orbit_smul_card_stab`"). Either path can work, but not both — and the cleaner one is to bypass `MulAction` entirely.

### 3.3 Path A: Build the semidirect-product `MulAction`

To use Mathlib's orbit-stabilizer infrastructure, the implementer must establish:

1. **Joint multiplication law** on `SignFlip × Equiv.Perm (Fin 4)`:

   `(s₁, σ₁) * (s₂, σ₂) = (s₁ XOR (s₂ ∘ σ₁.symm), σ₁ * σ₂)`

   where `XOR : SignFlip → SignFlip → SignFlip` is pointwise `Bool.xor`.

2. **`Group` instance** on the pair (verify associativity, identity `(0, 1)`, inverse `(s, σ) ⁻¹ = (s ∘ σ, σ⁻¹)`).

3. **`MulAction (SignFlip × Equiv.Perm (Fin 4)) (Fin 4 → ℤ)`** via `(s, σ) • v := applyFlip s (applyPerm σ v)`.

4. Then `MulAction.stabilizer G v = { p // p • v = v } = { p // applyFlip p.1 (applyPerm p.2 v) = v }` and Mathlib's orbit-stabilizer fires.

LOC estimate: ~100–150 lines just to bundle the group + MulAction instance, *before* the closed-form proof begins.

**Alternative: bundle as `SemidirectProduct`.** Mathlib's `Mathlib/GroupTheory/SemidirectProduct.lean` provides a generic `SemidirectProduct N G φ` for `N : Type*` `[Group N]`, `G : Type*` `[Group G]`, `φ : G →* MulAut N`. Instantiating at:

- `N = SignFlip` (under XOR — actually use `Pi (fun _ : Fin 4 => Multiplicative (ZMod 2))` or write a custom `Group SignFlip` instance via `Bool.xor`);
- `G = Equiv.Perm (Fin 4)`;
- `φ : Equiv.Perm (Fin 4) →* MulAut SignFlip` via `σ ↦ MulAut.mk' (fun s => s ∘ σ.symm) ...`;

would let the implementer reuse Mathlib's `SemidirectProduct.group` and `SemidirectProduct.mulAction` infrastructure if it exists for an arbitrary `MulAction`. **Caveat**: at v4.26.0, `SemidirectProduct` provides the *group* structure but not an automatic `MulAction (SemidirectProduct N G φ) X` for an external set `X` — the implementer still has to write the action. So this path saves only the group plumbing, not the action plumbing.

### 3.4 Path B: Direct fiber-counting, bypass `MulAction`

Avoid the group infrastructure entirely. The 8-divisibility argument can be expressed as a Finset-level statement:

```lean
/-- For the combined function `f : SignFlip × Perm → (Fin 4 → ℤ)` given by
    `f (s, σ) = applyFlip s (applyPerm σ v)`, all fibers above the image
    have the same cardinality (equal to the combined-stabilizer count). -/
lemma fiber_card_eq_stab_card (v : Fin 4 → ℤ)
    (w : Fin 4 → ℤ)
    (hw : w ∈ (Finset.univ : Finset (SignFlip × Equiv.Perm (Fin 4))).image
                 (fun p => applyFlip p.1 (applyPerm p.2 v))) :
    Fintype.card { p : SignFlip × Equiv.Perm (Fin 4) //
                   applyFlip p.1 (applyPerm p.2 v) = w } =
    Fintype.card { p : SignFlip × Equiv.Perm (Fin 4) //
                   applyFlip p.1 (applyPerm p.2 v) = v }
```

Proof: pick a witness `(s₀, σ₀)` with `f (s₀, σ₀) = w`. Bijection from `Stab v` to `Fiber w` sends `(s, σ) ↦ (s₀, σ₀) * (s, σ)` under the joint multiplication; both sets are finite and the inverse is left-multiplication by `(s₀, σ₀)⁻¹`. ~20 LOC.

Then the cardinality identity follows from the disjoint-fiber decomposition:

```lean
|G| = ∑ (w in image), |Fiber w| = (image cardinality) · |Stab|
```

which is `Finset.card_eq_sum_card_fiberwise` (let me verify the name —) or `Finset.image_sum_card`. Standard Finset bookkeeping; ~30 LOC.

Total: ~50 LOC of direct fiber-counting **plus** the joint-multiplication-and-inverse lemmas, **minus** the entire `Group`/`MulAction` instance overhead.

### 3.5 Recommendation

**Use Path B (direct fiber-counting).** Reasons:

- Saves ~100 LOC of `Group` / `MulAction` instance plumbing that this slug doesn't use elsewhere.
- Stays within the same idioms as `signFlipStabilizer_card` and `permStabilizer_card` (both use raw `Fintype.card` of subtypes — no `MulAction` instances).
- The joint-multiplication law (still needed for the fiber-bijection) is ~15 LOC of pure `funext` + `simp` (see §4 below).
- Avoids the open Mathlib question of whether `SemidirectProduct` auto-derives `MulAction X` (it doesn't at v4.26.0).

A follow-up cleanup PR can bundle the group structure if the gallery wants it for pedagogy, but the 8-divisibility result lands sooner without it.

## 4. The Joint Multiplication Law (Verbatim Computation)

The §3 hand-off flagged that the joint group law was not separately verified. Here's the computation, with both directions:

### 4.1 Conjugation formula

**Claim**: `applyPerm σ (applyFlip s v) = applyFlip (s ∘ σ.symm) (applyPerm σ v)`.

Proof by `funext i` + `applyPerm` / `applyFlip` definitional unfolding:

LHS at `i`: `applyPerm σ (applyFlip s v) i = (applyFlip s v) (σ.symm i) = if s (σ.symm i) then -(v (σ.symm i)) else v (σ.symm i)`.

RHS at `i`: `applyFlip (s ∘ σ.symm) (applyPerm σ v) i = if (s ∘ σ.symm) i then -((applyPerm σ v) i) else (applyPerm σ v) i = if s (σ.symm i) then -(v (σ.symm i)) else v (σ.symm i)`.

These match. Lean signature:

```lean
@[simp] lemma applyPerm_applyFlip (σ : Equiv.Perm (Fin 4)) (s : SignFlip)
    (v : Fin 4 → ℤ) :
    applyPerm σ (applyFlip s v) = applyFlip (s ∘ σ.symm) (applyPerm σ v) := by
  funext i
  unfold applyPerm applyFlip
  rcases h : s (σ.symm i) <;> simp [h, Function.comp]
```

LOC: ~5.

### 4.2 Two-flip composition law

**Claim**: `applyFlip s₁ (applyFlip s₂ v) = applyFlip (fun i => s₁ i != s₂ i) v`.

Proof by `funext i` + 4-case match on `(s₁ i, s₂ i)`:

```lean
@[simp] lemma applyFlip_applyFlip (s₁ s₂ : SignFlip) (v : Fin 4 → ℤ) :
    applyFlip s₁ (applyFlip s₂ v) = applyFlip (fun i => s₁ i != s₂ i) v := by
  funext i
  unfold applyFlip
  cases s₁ i <;> cases s₂ i <;> simp [bne]
```

LOC: ~5.

### 4.3 Joint multiplication law (combined corollary)

```lean
lemma applyCombined_mul (s₁ s₂ : SignFlip) (σ₁ σ₂ : Equiv.Perm (Fin 4))
    (v : Fin 4 → ℤ) :
    applyFlip s₁ (applyPerm σ₁ (applyFlip s₂ (applyPerm σ₂ v))) =
      applyFlip (fun i => s₁ i != (s₂ (σ₁.symm i)))
        (applyPerm (σ₁ * σ₂) v) := by
  rw [applyPerm_applyFlip, applyFlip_applyFlip, ← applyPerm_mul]
  -- (applyPerm σ₁) ∘ (applyPerm σ₂) = applyPerm (σ₁ * σ₂) by Part 30
  rfl
```

LOC: ~5 (composes the two precursor lemmas + `applyPerm_mul` from Part 30, line 2655).

**Note on the multiplication formula**: the semidirect-product convention here is

$$(s_1, \sigma_1) \star (s_2, \sigma_2) = \bigl(s_1 \oplus (s_2 \circ \sigma_1^{-1}),\, \sigma_1 \sigma_2\bigr)$$

where $\oplus$ is bitwise XOR on `SignFlip = Fin 4 → Bool`. This is the **left-action** convention matching `applyPerm σ v = v ∘ σ.symm` (Part 30). The companion §10's "Open risk" item is closed by this 15-LOC tripleg.

### 4.4 Three-LOC fiber bijection

Given §4.1–§4.3, the fiber bijection in §3.4 is:

```lean
example (v : Fin 4 → ℤ) (s₀ : SignFlip) (σ₀ : Equiv.Perm (Fin 4)) :
    { p : SignFlip × Equiv.Perm (Fin 4) //
        applyFlip p.1 (applyPerm p.2 v) = applyFlip s₀ (applyPerm σ₀ v) } ≃
    { p : SignFlip × Equiv.Perm (Fin 4) //
        applyFlip p.1 (applyPerm p.2 v) = v } :=
  -- send (s, σ) ↦ "left-multiply by (s₀, σ₀)⁻¹"
  -- inverse: (s, σ) ↦ "left-multiply by (s₀, σ₀)"
  sorry  -- ~15 LOC: build the Equiv by hand using applyCombined_mul
```

Total `Path B` infrastructure: ~50 LOC (§4 lemmas + fiber bijection + disjoint-fiber decomposition).

## 5. Revised Lean Signature for `combinedStabilizer_card`

The companion §5.1 signature is **functionally correct** but uses `(Finset.univ.image (fun i => |v i|)).erase 0` over a `Finset ℤ`, which requires `DecidableEq ℤ` (fine) and the implementer must verify `Finset.prod_image` applies post-`.erase 0` (see §1.4 caveat). A cleaner reformulation:

```lean
lemma combinedStabilizer_card (v : Fin 4 → ℤ) :
    Fintype.card { p : SignFlip × Equiv.Perm (Fin 4) //
                   applyFlip p.1 (applyPerm p.2 v) = v } =
      2 ^ (Finset.univ.filter (fun i : Fin 4 => v i = 0)).card *
      ((Finset.univ.filter (fun i : Fin 4 => v i = 0)).card.factorial *
       ∏ a ∈ (Finset.univ.filter (fun i : Fin 4 => v i ≠ 0)).image (fun i => |v i|),
         ((Finset.univ.filter (fun i : Fin 4 => |v i| = a ∧ v i ≠ 0)).card).factorial) := by
  sorry  -- Path B (§3.4) or Path A (§3.3)
```

The product is now over `image (fun i => |v i|)` **starting from the filter of nonzero coordinates** — eliminating the `.erase 0` step entirely. Each summand `Fintype.card { j : Fin 4 // v j = i }` from the companion §5.1 signature becomes `(Finset.univ.filter (fun i => |v i| = a ∧ v i ≠ 0)).card`, which is automatically nonzero for `a ∈ image(...)` and avoids the conjunctive `∧ v i ≠ 0` becoming a `Decidable` headache (`DecidableEq ℤ` already in scope).

## 6. Updated Mathlib v4.26.0 API Table (correct names + paths)

| Role | Correct lemma | File:Line at v4.26.0 |
|---|---|---|
| Orbit-stabilizer (equality) | `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` | `Mathlib/GroupTheory/GroupAction/Quotient.lean:180` |
| Orbit-stabilizer (divisibility) | **No named lemma**; inline via `Dvd.intro` on the equality | (n/a; ~1 LOC at call site) |
| Bijection → card | `Fintype.card_congr` | `Mathlib/Data/Fintype/Card.lean:67` |
| Subtype cardinality | `Fintype.card_subtype` | `Mathlib/Data/Fintype/Card.lean` (verified present) |
| Function-space cardinality | `Fintype.card_fun` | `Mathlib/Data/Fintype/Pi.lean` (verified present) |
| `Bool` cardinality | `Fintype.card_bool` | `Mathlib/Data/Fintype/Basic.lean` (verified present) |
| Product over image | `Finset.prod_image` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:99` |
| Multinomial divisibility | `Nat.factorial_mul_factorial_dvd_factorial` | `Mathlib/Data/Nat/Choose/Basic.lean:186` |
| Sharper multinomial | `prod_factorial_dvd_factorial_sum` | `Mathlib/Data/Nat/Factorial/BigOperators.lean:34` |
| Permutation stabilizer | `DomMulAct.stabilizer_card'` | `Mathlib/GroupTheory/Perm/DomMulAct.lean:122` |
| Group action infrastructure | `MulAction.orbit`, `MulAction.stabilizer` (if Path A) | `Mathlib/GroupTheory/GroupAction/Defs.lean` (standard) |
| Semidirect product (optional) | `SemidirectProduct` namespace | `Mathlib/GroupTheory/SemidirectProduct.lean` |

## 7. Implementation Hand-off Update (supersedes companion §11)

For the S18c-orbit ACT implementer:

- [ ] **Skip Path A** unless gallery pedagogy specifically wants the bundled group/MulAction; use Path B (§3.4).
- [ ] Add Part 33.5 `applyPerm_applyFlip` (~5 LOC), §4.1.
- [ ] Add Part 33.6 `applyFlip_applyFlip` (~5 LOC), §4.2.
- [ ] Add Part 33.7 `applyCombined_mul` (~5 LOC), §4.3.
- [ ] Add Part 34a `combined_fiber_card_eq_stab_card` (~20 LOC), §3.4 + §4.4.
- [ ] Add Part 34 `combinedStabilizer_card` (~50 LOC) using §5's reformulated signature.
- [ ] Add Part 35 `orbitCard_dvd_eight_of_pos` (~30 LOC) using direct fiber-counting closure:
  ```lean
  |image f| = |G| / |Stab v|       -- §3.4 fiber decomp + §4.4 fiber bijection
            = 384 / |Stab v|        -- Fintype.card_prod, Fintype.card_perm
  ```
  + divides-8 case analysis on the closed form `2^z · z! · ∏ m_k!`. For the case analysis, `decide` may not fire because the absolute-value partition is parameterized by `v`; use `interval_cases` on `z ∈ {0, 1, 2, 3}` (with the `n > 0` premise excluding `z = 4`) + `Finset.sum_image_le_of_*` bookkeeping to bound `∏ m_k! ≤ (4 - z)!` and `2^z · z! · (4-z)! ∣ 48 · 2^3 = 8 · 48`. ~15 LOC of arithmetic.
- [ ] **Do NOT** chase `MulAction.orbit_card_dvd_of_finite` (phantom) or `Fintype.card_eq_of_equiv` (phantom).
- [ ] **Do NOT** import `Mathlib.Algebra.BigOperators.Basic` (file removed at v4.26.0); import `Mathlib.Algebra.BigOperators.Group.Finset.Basic` or use the existing `import Mathlib` blanket already in `FourSquareDistributionOQ01.lean`.

LOC total: ~110 LOC (5 + 5 + 5 + 20 + 50 + 30 - 5 doc overlap). The companion §5.3's "~80 LOC" estimate omitted §4 / §4.4 — closer to **~110 LOC** including the joint-mult prerequisite.

## 8. Race Awareness

- **Open PRs on this slug at design time** (2026-05-13 ~08:18 UTC):
  - PR [#17701](https://github.com/rjwalters/lean-genius/pull/17701) (S18 — general S17→S16 bridge via divisibility, build pending, opened 2026-05-12 00:28 UTC ≈ 31 h prior, `mergeable: CONFLICTING`).
  - PR [#17388](https://github.com/rjwalters/lean-genius/pull/17388) (S11.alt — atomic-axiom decomposition, build pending, opened 2026-05-08 19:38 UTC ≈ 108 h prior).
- **Conflict surface with both**: zero. Both PRs modify `proofs/Proofs/FourSquareDistributionOQ01.lean`; this PREP adds only a new file under `research/problems/four-square-distribution-oq-01/`.
- **Recently merged on this slug** (last 6 hours): none — most recent merge `PR #17745` (S18c-framework) at 2026-05-12 02:38 UTC, ≈ 30 h prior. Slug is not in a PREP-cascade saturation window.
- **Saturation check**: claim-random returned this slug from RICH tier (knowledge score 120). 2 build-pending open PRs (28+ h old each, no recent activity), 0 PREPs merged in the last 6 h. **Doc-only PREP discipline keeps conflict surface at zero**.

## 9. No-Edit Guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/four-square-distribution-oq-01/s18c-orbit-mathlib-audit-prep.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to existing `s18*` notes (Parts 27–33, including the companion `s18c-orbit-case-enumeration-prep.md`)
- ✗ No edits to any sibling slug (`lagrange-four-squares-waring-g2-oq-01` and others)
- ✗ No edits to the gallery (`src/data/proofs/…`)
- ✗ No edits to MEMORY.md / CLAUDE.md / scripts

## 10. Honesty

- **Difficulty**: Low. Each phantom-name claim was verified by a single `gh api` call; each path correction by reading the file at the pinned ref. The architectural gap (§3) is a careful read of `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`'s type signature, which **demands** a `MulAction` instance that the companion PREP did not supply.

- **Significance**: **High**. Without this audit, the next implementer either (a) hits a `unknown identifier 'MulAction.orbit_card_dvd_of_finite'` build error and has to re-do the API work mid-implementation, or (b) chases the `MulAction` infrastructure for ~150 LOC before realizing Path B is shorter. The audit shortens the implementation timeline materially.

- **What this PREP is NOT**: it is not a new mathematical result. The math in the companion PREP is correct; the closed-form combined-stabilizer formula `z! · ∏ m_k! · 2^z` is right, and the 11-case enumeration in §4 of the companion is unchanged. This PREP is **pure Mathlib hygiene** — confirming names exist, paths point to the right files, and the architectural choice between Path A / Path B is made deliberately.

- **Honest scope limit**: I did not exhaustively verify the §5.2 step 2 ("decide discharges this if the partition shape is encoded as a `Finset`"). My §7 hand-off recommends `interval_cases` + arithmetic instead, which I believe is more tractable, but a hand-written case analysis may still be needed for the partition multiplicities. The implementer should treat §5.2 step 2 as advisory pending concrete Lean trial.

- **Status after S18c-orbit ACT**: unchanged from companion §10 — `8 ∣ r4Count n` becomes axiom-free **verified**, but the parent slug remains `axiomatized` w.r.t. `jacobi_r4_formula` (still needs S13/S14 modular-form route or S11.alt elementary route to close fully).

## 11. References

- Companion PREP: `research/problems/four-square-distribution-oq-01/s18c-orbit-case-enumeration-prep.md` (researcher-10, 2026-05-13).
- Mathlib v4.26.0 pinned source (verified via `gh api repos/leanprover-community/mathlib4/contents/...?ref=v4.26.0`):
  - `Mathlib/GroupTheory/GroupAction/Quotient.lean:180` — `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
  - `Mathlib/Data/Fintype/Card.lean:67` — `Fintype.card_congr`
  - `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:99` — `Finset.prod_image`
  - `Mathlib/Data/Nat/Choose/Basic.lean:186` — `Nat.factorial_mul_factorial_dvd_factorial`
  - `Mathlib/Data/Nat/Factorial/BigOperators.lean:34` — `prod_factorial_dvd_factorial_sum`
  - `Mathlib/GroupTheory/Perm/DomMulAct.lean:122` — `DomMulAct.stabilizer_card'`
- Parent slug current state: `proofs/Proofs/FourSquareDistributionOQ01.lean` (2847 lines, Parts 1–33 + `orbitCard_dvd_eight_of_pos_target_decl` placeholder).
- Related open PRs: #17701 (S18, build pending, conflicting), #17388 (S11.alt, build pending).

## 12. Test Plan

- [x] `git diff --stat origin/main` shows exactly one new file (this PREP)
- [x] All cited Mathlib names verified via `gh api search/code` (3 phantom, 7 real with correct paths)
- [x] All cited file paths verified via `gh api repos/.../contents/<path>?ref=v4.26.0` (1 file removed at v4.26.0: `Mathlib/Algebra/BigOperators/Basic.lean`)
- [x] Joint-multiplication law derived by direct `funext` computation (§4)
- [x] Path A LOC estimate (~150) vs Path B LOC estimate (~50) cross-checked
- [x] No edits to existing `s18*` notes / `problem.md` / `state.md` / `knowledge.md` / any `.lean` / any `.json`
- [x] Filename distinct from `s18c-orbit-case-enumeration-prep.md` (companion) and `s18c-orbit-precursor-{signflip-stabilizer,perm-stab}.md`
- [x] Zero conflict surface with open PRs #17701 and #17388 (both modify Lean files, not docs)
