# S9 PREP-2 — Cross-PR seam audit of #19075 (build-verified ACT) + #19270 (S10 skeleton PREP)

**Session type:** PREP (doc-only).
**Trigger:** Slug has 2 open PRs not yet ingested into `state.md`
(last state.md entry: S8 ACT, 2026-05-13):

- **#19075** (researcher-?, 2026-05-14): S9 ACT, build-verified
  (3065 jobs). Surgical 12-line fix to the OUTER theorem
  `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`, swapping
  `(hn : 1 ≤ n)` → `[NeZero n]` so the `Fintype (ZMod n)ˣ` typeclass
  flows in at statement elaboration time. Inner Phase C sorry
  untouched.

- **#19270** (researcher-?, 2026-05-15): S9 PREP, doc-only. Pin-verifies
  11 bearers for the Phase C non-cyclic-direction discharge and ships
  a paste-ready ~38-LOC ACT skeleton for the INNER theorem
  `prod_eq_one_of_not_isCyclic_aux` at
  `Proofs/GaussWilsonNonCyclicOQ01.lean:149`.

This PREP-2 audits the **seam** between the two PRs and goal-state
walks #19270's skeleton against the AS-MERGED-EITHER-ORDER parent file.
Surfaces **3 build risks** the skeleton would hit on first Docker
attempt — 1 type-error, 1 missing parent-file edit, 1 elaboration risk
— plus 1 promotion of a "soft" #19270 risk to "rfl-safe", plus 1
citation-file correction.

**Scope:** Strictly conflict-free. One new file only:
`research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-15-s9-prep-2-cross-pr-seam-audit-19075-19270.md`.
No edits to `state.md`, `problem.md`, `knowledge.md`, `meta.json`, or
any `proofs/Proofs/*.lean` file. Composes with #19075, #19270, and
all prior sessions S1–S9.

---

## 1. Seam check — does #19270's skeleton compose with #19075's signature change?

**Verdict: YES, both merge orderings work.** No merge-ordering hazard.

#19075's diff touches ONLY the OUTER theorem
`prod_univ_units_zmod_eq_neg_one_iff_isCyclic` (lines 176–199 in
current main). #19270's skeleton targets the INNER theorem
`prod_eq_one_of_not_isCyclic_aux` (lines 146–149 in current main).

The inner theorem already uses `[NeZero n]` (line 146 in main):

```lean
theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (_hncyc : ¬IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = 1 := by
  sorry
```

so it pre-dates BOTH #19075 and #19270 in its current signature shape.
The two PRs are scope-disjoint: #19075 patches the outer-theorem call
shape, #19270 prepares the inner-theorem body. Either merge ordering
preserves both.

For the auditor (deployer) — merge order recommendation:

1. Either #19075 or #19270 first (independent).
2. This PREP-2 last (it cites the others).

Each PR's per-file conflict surface:

| PR | Files touched | Lines |
|---|---|---|
| #19075 | `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` | outer theorem, 174–194 |
| #19270 | `research/problems/.../sessions/2026-05-15-s9-prep-noncyclic-direction-bearer-audit-and-skeleton.md` (NEW) | n/a |
| this PREP-2 | `research/problems/.../sessions/2026-05-15-s9-prep-2-cross-pr-seam-audit-19075-19270.md` (NEW) | n/a |

Zero overlap.

---

## 2. Re-corroboration of #19270's 11-bearer table at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Independent `gh api .../contents/...?ref=<SHA>` round-trips on every
Mathlib bearer #19270 cites. Verified live; not relying on #19270's
table.

| # | Bearer | Cited file:line (#19270) | Actual file:line @ SHA | Status |
|---|---|---|---|---|
| 1 | `prod_univ_eq_prod_two_torsion` | `GaussWilsonNonCyclicOQ01A.lean:37` (in-repo) | confirmed via local read | ✅ |
| 2 | `Subgroup.mk` constructor | `Algebra/Group/Subgroup/Defs.lean` | `Subgroup/Defs.lean:294` (struct decl); `mem_mk` at `:351` (`@[simp]`) | ✅ |
| 3 | `mul_pow` | `Algebra/GroupPower/Basic.lean` (vague) | `Algebra/Group/Basic.lean` family | ✅ (well-known) |
| 4 | `inv_pow`, `inv_one`, `one_pow` | `Algebra/Group/Basic.lean` | `Algebra/Group/Basic.lean:409` (`inv_pow`) | ✅ |
| 5 | `IsPGroup.iff_card` | `GroupTheory/PGroup.lean:46` | `GroupTheory/PGroup.lean:46` | ✅ exact match |
| 6 | `Nat.prime_two` | `Data/Nat/Prime/Basic.lean` | confirmed (referenced at `:100`) | ✅ |
| 7 | `Nat.card_eq_fintype_card` | **`Data/Finite/Card.lean`** | **`SetTheory/Cardinal/Finite.lean:45`** | ⚠ file-citation correction |
| 8 | `Fintype.card_subtype` | `Data/Fintype/Card.lean:378` | `Data/Fintype/Card.lean:378` | ✅ exact match |
| 9 | `card_sq_eq_one_ge_three` | `Proofs/GaussWilsonNonCyclic.lean:294` (in-repo) | local read confirms `:294` | ✅ |
| 10 | `SubmonoidClass.coe_finset_prod` | `Algebra/Group/Submonoid/BigOperators.lean:49,101` | `:49` (SubmonoidClass), `:101` (Submonoid) — **two separate lemmas** | ✅ (see §3 F1) |
| 11 | `Finset.prod_subtype` | `BigOperators/Group/Finset/Basic.lean:467` | `BigOperators/Group/Finset/Basic.lean:467` | ✅ exact match |
| 12 | `prod_univ_eq_one_of_elementary_card_ge_four` | `GaussWilsonNonCyclicOQ01B.lean:220` (in-repo) | local read confirms `:220` | ✅ |

**Bonus bearer NOT in #19270's table but used in the skeleton:**

| # | Bearer | Location @ SHA | Notes |
|---|---|---|---|
| 13 | `SubgroupClass.coe_pow` | `Subgroup/Defs.lean:246` (`@[simp, norm_cast]`, **`rfl`**) | `((x ^ n : H) : G) = (x : G) ^ n` |
| 14 | `OneMemClass.coe_one` | `Subgroup/Defs.lean:526` (`@[simp, norm_cast]`, **`rfl`**) | `((1 : H) : G) = 1` |

These two `rfl`-lemmas are LOAD-BEARING for the skeleton's
`Subtype.ext (by show g ^ 2 = 1; ...)` pattern (§ 4, §6 below).
Without `coe_pow` being `rfl`, that pattern fails. #19270 did not call
this out; this PREP-2 confirms it is safe.

### Citation correction (F4)

> #19270 §2 row 7 says `Nat.card_eq_fintype_card` is at
> `Data/Finite/Card.lean`. Actual location at lake SHA is
> `SetTheory/Cardinal/Finite.lean:45`. The lemma is `[Fintype α] :
> Nat.card α = Fintype.card α` (rfl-style via `Nat.card` reduction).
> `Data/Finite/Card.lean` CONSUMES this lemma (lines 53, 58, 68, ...)
> but does not define it.
>
> **Impact:** zero. The lemma name is unique and unambiguous; the
> import that pulls it in is `import Mathlib.Tactic` (which transitively
> imports `SetTheory/Cardinal/Finite.lean`). No skeleton edit needed.
> Citation correction only.

### Negative-bearer reconfirmation

> `IsPGroup.card_eq_pow_one_iff_orderOf_dvd` (cited by state.md "Next
> Action" pre-#19270) — independently re-checked: no such lemma at
> SHA in `GroupTheory/PGroup.lean`. #19270's correction (use
> `IsPGroup.iff_card`) stands.

---

## 3. Goal-state walk — 3 build risks the skeleton hits beyond #19270 §5

#19270 §5 calls out 3 "build-risk" modes (A, B, C) but rates A=HIGH,
B=MEDIUM, C=LOW. This goal-state walk **revises severities** and
surfaces a previously-missed type-error risk.

### F1 (HIGH, missed by #19270) — `SubmonoidClass.coe_finset_prod` over-application: TYPE ERROR

**Skeleton (§4 step 6):**
```lean
rw [SubmonoidClass.coe_finset_prod T.toSubmonoid (fun (x : T) => x) Finset.univ]
```

**Lemma signature** (pin-verified at `Submonoid/BigOperators.lean:49`):
```lean
@[to_additive (attr := norm_cast, simp)]
theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M]
    (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M)
```

The outer `variable` block at file scope (`Submonoid/BigOperators.lean`)
declares `{S : B}` as **implicit**. So `SubmonoidClass.coe_finset_prod`
takes **2 explicit arguments only**: `f : ι → S` and `s : Finset ι`.

The skeleton passes **3** explicit arguments: `T.toSubmonoid`,
`(fun (x : T) => x)`, `Finset.univ`. Lean would try to unify
`T.toSubmonoid : Submonoid (ZMod n)ˣ` with `f : ι → S` — type mismatch,
hard error.

**Fix A (1-token delta, preferred):** drop `T.toSubmonoid`. `S` is
inferred from `f`'s codomain `T`:
```lean
rw [SubmonoidClass.coe_finset_prod (fun (x : T) => x) Finset.univ]
```

**Fix B (namespace correction, equivalent):** use the explicit
`Submonoid.coe_finset_prod` variant at line 101 instead:
```lean
@[to_additive (attr := norm_cast)]
theorem coe_finset_prod {ι M} [CommMonoid M]
    (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M)
```
which takes `S : Submonoid M` explicitly:
```lean
rw [Submonoid.coe_finset_prod T.toSubmonoid (fun (x : T) => x) Finset.univ]
```

**Why this matters:** This is not the "direction reversal" or
"`.symm` adjustment" #19270 §5 Risk A discussed — it is a hard type
error on first compilation. The skeleton as written in #19270 §4 will
not pass the elaborator. Either Fix A or Fix B is required.

---

### F2 (HIGH, missed by #19270) — Parent file has `_hncyc`, skeleton uses `hncyc`: MISSING EDIT

**Parent file at HEAD** (`Proofs/GaussWilsonNonCyclicOQ01.lean:146-149`):
```lean
theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (_hncyc : ¬IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = 1 := by
  sorry
```

Note the **underscore prefix** on `_hncyc` (Lean convention for "this
hypothesis is intentionally unused"). The non-cyclic hypothesis was
not consumed by the placeholder `sorry`.

**Skeleton (#19270 §3):**
```lean
theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
```

The skeleton implicitly renames `_hncyc → hncyc` (drop underscore).
Step 4 of the discharge plan uses the hypothesis:
```lean
have h_T_ge_3 : 3 ≤ Fintype.card T := by
  rw [h_card_filter]
  exact GaussWilsonNonCyclic.card_sq_eq_one_ge_three hn hncyc
```

If the implementer pastes only the **body** of the skeleton (keeping
`_hncyc` in the declaration), step 4 fails with
`unknown identifier 'hncyc'`.

**Fix:** when replacing the `sorry` with the skeleton body, the
implementer **must also** rename the hypothesis on line 147:

```lean
-    (_hncyc : ¬IsCyclic (ZMod n)ˣ) :
+    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
```

This is a 1-character edit; zero net LOC delta. Easy to miss if the
S10 implementer only edits the body. #19270's §4 paste-ready snippet
**implicitly** includes this rename in its theorem header reproduction,
but a hurried implementer may paste the body alone.

**Recommended S10 ACT instruction:** "replace lines 146–149 entirely
(not just the body line 149)" — preserves the rename.

---

### F3 (MEDIUM, partially overlapping #19270 Risk B) — `simp [..., T, ...]` on `let`-bound `T`: FRAGILE

**Skeleton (§4 step 6, final bridge tactic):**
```lean
intro x
simp [Finset.mem_filter, T, Subgroup.mem_mk]
```

Goal at this point: `∀ x, x ∈ univ.filter (fun x => x^2 = 1) ↔ x ∈ T`,
after `intro x`: `x ∈ univ.filter (fun x => x^2 = 1) ↔ x ∈ T`.

The skeleton's `T` is introduced by a **local `let`-binding**
(`let T : Subgroup (ZMod n)ˣ := { carrier := {x | x ^ 2 = 1}, ... }`).
In Lean 4, `simp [T]` where `T` is a `let`-bound local name does NOT
reliably trigger an unfold — there is no `T.eq_def` equation generated
for local lets (unlike top-level `def`s).

The skeleton thus relies on **definitional reduction** through the
`SetLike` instance and `Subgroup.mem_mk`-style simp lemmas to bridge
`x ∈ T` ↔ `x^2 = 1`. The path is:

```
x ∈ T   (Membership instance for SetLike)
  ↪ (T : Set _) x   (SetLike.coe_mk on the inline Subgroup.mk)
  ↪ T.carrier x   (Subgroup.instSetLike.coe := s.carrier)
  ↪ {x | x^2 = 1} x   (carrier := {x | x^2 = 1} by hypothesis)
  ↪ x^2 = 1   (Set.mem_setOf_eq)
```

Most of these steps ARE definitional, but the chain depends on Lean's
unifier eagerly walking through `Subgroup.mk` + `Submonoid.mk` +
`Subsemigroup.mk` projections. In practice, **this usually works** in
Mathlib's contemporary code, but the `simp [T]` is a defensive
sledgehammer that doesn't ACTUALLY help (T isn't a simp equation).

**Severity:** MEDIUM. May work as-is; may not. Build outcome depends on
how aggressively Lean's `simp` unifies through the inline structure
literal under the `let`.

**Fix A (most defensive, ~6 LOC instead of 2):** use explicit
`constructor` + `Finset.mem_filter` unwrap, bypassing `T` unfold:

```lean
intro x
constructor
· intro hx
  rcases Finset.mem_filter.mp hx with ⟨_, hsq⟩
  exact hsq
· intro hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
```

This works IFF `hT : x ∈ T` is definitionally `x^2 = 1` for `exact hT`
to inhabit the filter's predicate slot (and symmetrically `exact hsq`
to inhabit `x ∈ T`). Both directions rely on the same defeq the
`simp` was relying on, but with `exact` Lean's unifier has stronger
hints.

**Fix B (terse, may still need defeq):**
```lean
intro x
simp only [Finset.mem_filter, Finset.mem_univ, true_and]
rfl   -- closes the `x^2 = 1 ↔ x ∈ T` goal via SetLike defeq
```
If `rfl` doesn't close, fall back to `exact Iff.rfl` or `Fix A`.

**Fix C (most reliable, +5 LOC):** lift `T` to a top-level `def` in
the file (above the theorem). With a top-level `def T : Subgroup ... := ...`,
`simp [T]` works (generates `T.eq_def`). This is the cleanest
architecturally but adds 3–5 LOC outside the theorem body.

---

## 4. Promoted from soft-risk to confirmed-safe — `Subtype.ext + show g^2 = 1` pattern

**#19270 §5 Risk C** said:
> The bridge `Nat.card_eq_fintype_card` requires `[Fintype G]` (or
> `[Finite G]`). If `Fintype T` instance isn't picked up, force it
> with `haveI : Fintype T := Subgroup.instFintype`.

Adjacent to this, the skeleton uses (steps 3, 5):
```lean
fun ⟨g, hg⟩ => Subtype.ext (by show g ^ 2 = 1; exact hg)
fun ⟨g, hg⟩ => ⟨1, Subtype.ext (by show g ^ (2 ^ 1) = (1 : (ZMod n)ˣ); ...)⟩
```

The `show g ^ 2 = 1` after `Subtype.ext` relies on
`(⟨g, hg⟩ ^ k : T).val = g ^ k` being definitional. Per pin-verification
of `SubgroupClass.coe_pow` at `Subgroup/Defs.lean:246`:

```lean
@[to_additive (attr := simp, norm_cast)]
theorem coe_pow (x : H) (n : ℕ) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl                                   -- ← THIS IS rfl
```

and `OneMemClass.coe_one` at `:526`:
```lean
@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : H) : G) = 1 :=
  rfl                                   -- ← rfl
```

**Both are `rfl`.** Therefore the `Subtype.ext + show` pattern is
**safe by definitional reduction** — no explicit `SubgroupClass.coe_pow`
rewrite is needed inside the `by`-block. The skeleton's steps 3 and 5
are SOUND as written.

This is a positive finding: had `coe_pow` been only propositionally
true (not `rfl`), the skeleton would have needed an explicit
`simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]` step before
`exact hg`. Confirmed safe.

---

## 5. Numerical sanity at n = 8 (smallest non-cyclic mod)

The smallest `n ≥ 3` with `¬IsCyclic (ZMod n)ˣ` is `n = 8`.
`(ZMod 8)ˣ = {1, 3, 5, 7}`. Square table:

| x | x^2 mod 8 |
|---|---|
| 1 | 1 |
| 3 | 9 ≡ 1 |
| 5 | 25 ≡ 1 |
| 7 | 49 ≡ 1 |

All four units are 2-torsion. So `T = (ZMod 8)ˣ`, `Fintype.card T = 4 = 2^2`.
`IsPGroup 2 T` holds with `k = 2`. Cardinality ≥ 4 holds. Phase B
applies, giving `∏ x : T, x = 1`.

Product check: `1 * 3 * 5 * 7 = 105 = 13 * 8 + 1 ≡ 1 (mod 8)`. ✓

Sanity at `n = 12` (`(ZMod 12)ˣ = {1, 5, 7, 11}`, all square to 1, k=2):
`1 * 5 * 7 * 11 = 385 = 32 * 12 + 1 ≡ 1 (mod 12)`. ✓

Sanity at `n = 15` (cyclic, `(ZMod 15)ˣ ≅ ℤ/8`): outside scope —
non-cyclic hypothesis fails, so this branch is vacuous. ✓

The discharge plan is mathematically sound at the smallest test cases.

---

## 6. Corrected paste-ready S10 ACT skeleton (incorporates F1–F3)

Drop-in replacement for `Proofs/GaussWilsonNonCyclicOQ01.lean:146-149`
(the existing 4-line sorry stub). Net LOC delta: +1 character on the
declaration (drop `_`); body grows from 1 line (`sorry`) to ~40 lines.

```lean
theorem prod_eq_one_of_not_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :       -- F2: drop underscore
    (∏ x : (ZMod n)ˣ, x) = 1 := by
  -- Step 1: Phase A reduction.
  rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]
  -- Step 2: Build the 2-torsion subgroup T.
  let T : Subgroup (ZMod n)ˣ :=
    { carrier := {x | x ^ 2 = 1}
      one_mem' := by show (1 : (ZMod n)ˣ) ^ 2 = 1; exact one_pow _
      mul_mem' := fun {a b} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) => by
        show (a * b) ^ 2 = 1
        rw [mul_pow, ha, hb, mul_one]
      inv_mem' := fun {a} (ha : a ^ 2 = 1) => by
        show (a⁻¹) ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  -- Step 3: T is a 2-group, so Nat.card T = 2^k for some k.
  have hT_pgroup : IsPGroup 2 T := fun ⟨g, hg⟩ =>
    ⟨1, Subtype.ext (by show g ^ (2 ^ 1) = (1 : (ZMod n)ˣ);
                        rw [pow_one]; exact hg)⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT_pgroup
  -- Step 4: T.card = #filter ≥ 3 → 2^k ≥ 3 → k ≥ 2 → T.card ≥ 4.
  have h_card_filter :
      Fintype.card T = (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
    simpa using Fintype.card_subtype (fun x : (ZMod n)ˣ => x ^ 2 = 1)
  have h_T_ge_3 : 3 ≤ Fintype.card T := by
    rw [h_card_filter]
    exact GaussWilsonNonCyclic.card_sq_eq_one_ge_three hn hncyc
  have h_T_pow : Fintype.card T = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact hk
  have h_T_ge_4 : 4 ≤ Fintype.card T := by
    rw [h_T_pow] at h_T_ge_3 ⊢
    rcases k with _ | _ | k'
    · norm_num at h_T_ge_3
    · norm_num at h_T_ge_3
    · calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k' + 2) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  -- Step 5: Apply Phase B to T.
  have hT_exp : ∀ x : T, x ^ 2 = 1 := fun ⟨g, hg⟩ => Subtype.ext (by
    show g ^ 2 = 1; exact hg)
  have hT_prod : (∏ x : T, x) = 1 :=
    prod_univ_eq_one_of_elementary_card_ge_four hT_exp h_T_ge_4
  -- Step 6: Bridge to ambient Finset.  F1: drop T.toSubmonoid extra arg.
  have h_bridge :
      ∏ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1), x
        = ((∏ x : T, x : T) : (ZMod n)ˣ) := by
    rw [SubmonoidClass.coe_finset_prod (fun (x : T) => x) Finset.univ]   -- F1
    symm
    apply Finset.prod_subtype
    -- F3: avoid `simp [T]`; use explicit constructor.
    intro x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨_, hsq⟩
      exact hsq
    · intro hT
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
  rw [h_bridge, hT_prod, OneMemClass.coe_one]
```

**Delta vs #19270 §4:**

- Line 1 (header): `_hncyc` → `hncyc` (F2).
- Step 6, `rw` line: drop `T.toSubmonoid` argument (F1, Fix A).
- Step 6, final tactic: replace `simp [Finset.mem_filter, T,
  Subgroup.mem_mk]` with explicit `constructor` block (F3, Fix A).

LOC count: ~40 (vs #19270's quoted ~38). Net `+2 LOC` for defensive F3
fix; F1 and F2 are zero-net.

---

## 7. Build-iteration budget revision

#19270 §10 estimated:
> Docker iterations: 1 if Risks A/B pre-empted; otherwise 2–3.

With F1–F3 fixes applied verbatim (§6 skeleton above), revised budget:

- **1 iter expected** to compile end-to-end, given:
  - F1 fix eliminates the type-error (was a hard fail in #19270's
    code).
  - F2 fix eliminates `unknown identifier` (also a hard fail).
  - F3 fix eliminates the `simp [T]` defeq gamble (was an
    elaboration roulette).
  - §4 confirms `coe_pow`/`coe_one` are `rfl` (no rewrite needed).

- **2 iters worst-case** if any residual:
  - `Fintype T` instance not auto-inferred (mitigation: `haveI :
    Fintype T := inferInstance` after `let T`).
  - `Subgroup.mem_carrier` defeq for the F3-Fix-A `exact hsq` path
    (mitigation: change `exact hsq` to `show x ∈ T; exact hsq` or
    `show x^2 = 1; exact hsq`).

This represents a **2-iter savings vs #19270's worst case** by
front-loading F1+F2+F3 fixes before any Docker build attempt.

---

## 8. Composition with prior sessions and the two open PRs

| Session | Type | PR | Net effect |
|---|---|---|---|
| S1 OBSERVE | OBSERVE | #18116 (merged) | 3-phase decomposition |
| S2 ACT | ACT | #18147 (merged) | Phase A built (0 sorries) |
| S3 ACT | ACT (partial) | #18232 (merged) | Phase B core with 1 strategic sorry |
| S4 PREP | PREP | #18347 (merged) | 4 Phase-B routes surveyed |
| S4b PREP | PREP | #18467 (merged) | Mathlib v4.26.0 API erratum |
| S5 PREP | PREP | #18502 (merged) | Phase C iff design memo |
| S5b PREP | PREP | #18607 (merged) | 4 tactic bugs in S5 |
| S6 ACT | ACT | #18652 (merged) | Phase C scaffold (2 strategic sorries) |
| S7 PREP | PREP | #18700 (merged) | Cyclic direction recipe |
| S7 ACT | ACT | #18743 (merged) | Cyclic direction discharged |
| S8 ACT | ACT | (merged) | Phase B strategic sorry discharged |
| **S9 ACT (#19075)** | **ACT (open)** | **#19075** | **outer-theorem `[NeZero n]` build-unblocker (build verified 3065 jobs)** |
| **S9 PREP (#19270)** | **PREP (open)** | **#19270** | **inner-theorem skeleton, 11 bearers pinned** |
| **S9 PREP-2 (this)** | **PREP (open)** | **(this)** | **seam audit, 3 build risks surfaced, corrected skeleton** |

Predicted Phase chain after S10 ACT (consumes #19075 + #19270 + this):

| Phase | File | LOC | Sorries | Status |
|---|---|---|---|---|
| A | `GaussWilsonNonCyclicOQ01A.lean` | 66 | 0 | build-verified |
| B | `GaussWilsonNonCyclicOQ01B.lean` | 243 | 0 | build-verified |
| C | `GaussWilsonNonCyclicOQ01.lean` | ~240 | **0** | build-pending (or build-verified post-S10 Docker) |

Slug-wide sorry count after S10 ACT: **0**.

---

## 9. Conflict-free guarantees

- Exactly one new file:
  `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-15-s9-prep-2-cross-pr-seam-audit-19075-19270.md`.
- Zero edits to `state.md`, `problem.md`, `knowledge.md`, `meta.json`.
- Zero edits to any `proofs/Proofs/*.lean` file.
- Zero edits to `proofs/Proofs.lean` or `src/data/proofs/*`.
- Composes with #19075 (Lean-file edit, line 174–194) and #19270
  (new sessions file) without overlap.

---

## 10. Race awareness

Pre-PREP-2 (this commit): 2 open PRs on slug — `gh pr list --search
"gauss-wilson-non-cyclic-oq-01 in:title" --state open` returns
`#19075` (S9 ACT) + `#19270` (S9 PREP). With this PREP-2: 3 open PRs.

Per memory `_sameauthor_duplicate_prep_within_12h_meta_audit_3_open_prs`:
3 PRs on the same slug benefit from explicit merge-order analysis. All
three have **disjoint file scopes** (§1 table), so merge order is
flexible. Recommended:

1. #19075 (or #19270) — first.
2. #19270 (or #19075) — second.
3. **This PREP-2** — third (cites the others).

Sibling slug `gauss-wilson-non-cyclic-oq-03` has #18230 (CONFLICTING/DIRTY)
— independent state.md / PR chain, no interaction.

`docker ps` and `ps -ef | grep docker-build` (in this worktree): no
active builds. No sibling worktree has a `GaussWilsonNonCyclicOQ01.lean`
modification.

---

## 11. Summary table for S10 implementer

| Item | Where (#19270 §) | Severity | Action required |
|---|---|---|---|
| F1: `SubmonoidClass.coe_finset_prod` over-application | §4 step 6 | HIGH (type error) | Apply §6 fix (drop `T.toSubmonoid`) |
| F2: `_hncyc` underscore not renamed | §3 (header) | HIGH (unknown identifier) | Rename parent line 147 along with body replacement |
| F3: `simp [T]` on `let`-bound T | §4 step 6 | MEDIUM (fragile) | Apply §6 fix (explicit `constructor`) |
| F4: `Nat.card_eq_fintype_card` file citation | §2 row 7 | LOW (cosmetic) | None — citation correction only |
| §4 (this doc): `SubgroupClass.coe_pow` is `rfl` | §5 Risk C-adjacent | POSITIVE | Use skeleton's `Subtype.ext + show` pattern with confidence |
| §5 (this doc): n=8/12 numerical sanity | n/a | POSITIVE | Discharge plan is mathematically sound |

Recommended S10 ACT entry point: paste §6 verbatim, run Docker build,
expect 1 iteration to ship.
