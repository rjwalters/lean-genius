# S10 PREP — Goal-state walk of the §6 corrected skeleton + S10 ACT-readiness gate

**Session type:** PREP (doc-only).
**Trigger:** Three of this slug's PRs landed on `main` at the 2026-05-15T18:00Z deployer
batch wave:

- **#19270** (S9 PREP, doc-only) — bearer-pinned ~38-LOC skeleton; merged 18:02:17Z.
- **#19301** (S9 PREP-2, doc-only) — cross-PR seam audit; surfaces 3 build risks (F1, F2, F3)
  in #19270's skeleton; merged 18:00:35Z.
- **#19307** (sibling slug `inverse-galois-a5-oq-01` S4e PREP) — unrelated, listed only as the
  ship that triggered this researcher cycle.

The slug now has **one** open PR — **#19075** (S9 ACT, build-verified `[NeZero n]` unblocker
on the outer theorem). The S10 ACT recipe (the corrected ~40-LOC skeleton in PREP-2 §6) is
fully assembled but has **never been goal-state-simulated step-by-step**; PREP-2 confirmed
F1 + F2 + F3 corrections and §4 `Subtype.ext` safety, but did not walk a tactic-by-tactic
goal trace.

This PREP-3 supplies that walk. It does not re-pin bearers (PREP-2 §2 covered that at lake
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`); it does not re-write the skeleton (PREP-2
§6 is canonical); it does not amend `state.md` or `meta.json`. It supplies:

1. A `state.md`-catchup inventory table (§1) — three documented PRs the on-disk `state.md`
   has not yet absorbed.
2. A per-tactic goal-state simulation (§2) — for every line of the §6 skeleton, the goal
   before/after, the hypothesis context delta, and the inference rule applied.
3. A precision audit (§3) of F1's lambda-typing fix: shows the elaborator's
   unification path for `(fun (x : T) => x) : T → T` with implicit
   `S := T`-via-codomain.
4. A residual risk inventory (§4) for Fintype T, decidable membership, and the
   `Finset.prod_subtype` predicate-match.
5. Composition analysis (§5) with the still-open S9 ACT (#19075) — confirms inner-theorem
   independence both merge orderings.
6. An S10 ACT-readiness gate (§6) — exact build command, expected job count, fallback
   tactics for each soft pin-point, go/no-go criterion.

**Scope:** Strictly conflict-free. One new file only:
`research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-15-s10-prep-goal-state-walk-and-act-readiness.md`.
No edits to `state.md`, `problem.md`, `knowledge.md`, `meta.json`, or any
`proofs/Proofs/*.lean` file. Composes with #19075 (Lean-file edit on lines 174–194 of
`GaussWilsonNonCyclicOQ01.lean`) without overlap. Acknowledges sibling slug
`gauss-wilson-non-cyclic-oq-03` (PR #18230, CONFLICTING/DIRTY, independent state).

---

## 1. State.md catchup inventory

`state.md` last-updated boundary: S8 ACT (2026-05-13). Since then three slug-relevant PRs
have landed on `main`, plus one is still open. None has been written back into `state.md`.
This PREP-3 does NOT amend `state.md` (deferred to S10 ACT or to a STATE-SYNC PR), but
records the inventory so the S10 implementer has a single-table reference.

| PR # | Type | Touches | State | Merged at | Net effect |
|---|---|---|---|---|---|
| #19075 | S9 ACT | `Proofs/GaussWilsonNonCyclicOQ01.lean` outer-theorem 174–194 | **OPEN / MERGEABLE / build-verified 3065 jobs** | (not yet) | Outer theorem `(hn : 1 ≤ n)` → `[NeZero n]`; build-pending status of file cleared |
| #19270 | S9 PREP | new sessions file `2026-05-15-s9-prep-noncyclic-direction-bearer-audit-and-skeleton.md` | merged | 2026-05-15T18:02:17Z | 11-bearer pin table at lake SHA + paste-ready ~38-LOC skeleton |
| #19301 | S9 PREP-2 | new sessions file `2026-05-15-s9-prep-2-cross-pr-seam-audit-19075-19270.md` | merged | 2026-05-15T18:00:35Z | 3 build risks (F1 type-error, F2 unknown-identifier, F3 simp-fragility) + §6 corrected skeleton + §4 `Subtype.ext` safety confirmation |

Post-S10 ACT, the predicted on-disk state is:

| Phase | File | LOC (current → post-S10) | Sorries (current → post-S10) | Build |
|---|---|---|---|---|
| A | `GaussWilsonNonCyclicOQ01A.lean` | 66 | 0 | build-verified |
| B | `GaussWilsonNonCyclicOQ01B.lean` | 243 | 0 | build-verified |
| C | `GaussWilsonNonCyclicOQ01.lean` | 201 → ~240 | 1 → 0 | build-pending → build-verified (post-S10 Docker) |

Slug-wide sorry count post-S10: **0**. Slug-wide axiom count: **0** (unchanged; the parent
file uses no `axiom` declarations and Phase C closure relies entirely on Phase A + Phase B
+ Mathlib bearers).

---

## 2. Per-tactic goal-state walk of the §6 corrected skeleton

Source: PR #19301's §6 (the F1+F2+F3-corrected ~40-LOC skeleton). Lines numbered locally
within the inserted body; the implementer pastes these 40 lines in place of the single
`sorry` at `GaussWilsonNonCyclicOQ01.lean:149` (and renames `_hncyc → hncyc` on line 147
per F2).

**Initial context** (after the parent file's `theorem prod_eq_one_of_not_isCyclic_aux ... := by`):

```
n           : ℕ
hn          : n ≥ 3
inst✝       : NeZero n
hncyc       : ¬IsCyclic (ZMod n)ˣ
⊢ (∏ x : (ZMod n)ˣ, x) = 1
```

Below, `⊢` denotes the goal at each step; only the changed portion of context is shown.

### L1 — `rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]`

| Before | After |
|---|---|
| `⊢ (∏ x : (ZMod n)ˣ, x) = 1` | `⊢ (∏ x ∈ univ.filter (fun x : (ZMod n)ˣ => x^2 = 1), x) = 1` |

**Bearer:** `GaussWilsonNonCyclicOQ01A.prod_univ_eq_prod_two_torsion`. Verified in-repo at
`Proofs/GaussWilsonNonCyclicOQ01A.lean:37`. Signature: for a finite commutative group `G`,
`(∏ x : G, x) = ∏ x ∈ univ.filter (·^2 = 1), x`. Implicit `[CommGroup G]` + `[Fintype G]`
+ `[DecidableEq G]` are all available for `(ZMod n)ˣ` with `[NeZero n]`.

**Why the `(ZMod n)ˣ` explicit argument is needed:** Phase A's theorem is stated
generically in `G`; the `rw` direction infers `G` from the unifier match against the
LHS `(∏ x : (ZMod n)ˣ, x)`. The explicit argument is a no-op convenience and could be
dropped without behavioral change.

### L2–L9 — `let T : Subgroup (ZMod n)ˣ := { carrier := ..., one_mem' := ..., mul_mem' := ..., inv_mem' := ... }`

This is a single `let`-binding spanning lines 2–9 of the §6 skeleton. The goal does not
change (the `let` introduces a local definition without manipulating the goal). The
context gains:

```
T : Subgroup (ZMod n)ˣ := { carrier := {x | x ^ 2 = 1}, ... }
```

Each `*_mem'` field is independently elaborated. Per the §6 skeleton:

- `one_mem'`: `show (1 : (ZMod n)ˣ) ^ 2 = 1; exact one_pow _`
- `mul_mem'`: `show (a * b) ^ 2 = 1; rw [mul_pow, ha, hb, mul_one]`
- `inv_mem'`: `show (a⁻¹) ^ 2 = 1; rw [inv_pow, ha, inv_one]`

The `show` tactic is load-bearing: the elaborator must accept the rewriting of
membership-in-T (i.e. `(1 : (ZMod n)ˣ) ∈ {x | x ^ 2 = 1}`) to the underlying `Set.mem`
predicate `(1 : (ZMod n)ˣ) ^ 2 = 1`. This is definitionally `rfl` (via `Set.mem_setOf_eq`),
so `show` succeeds without further `simp`.

**Confirmed safe — no `change` or `Set.mem_setOf_eq` rewrite needed.**

### L10–L13 — `have hT_pgroup : IsPGroup 2 T := fun ⟨g, hg⟩ => ⟨1, Subtype.ext (by show g ^ (2 ^ 1) = (1 : (ZMod n)ˣ); rw [pow_one]; exact hg)⟩`

**Goal unchanged.** Context gains `hT_pgroup : IsPGroup 2 T`.

The term-mode construction:

1. `IsPGroup 2 T` unfolds (per `GroupTheory/PGroup.lean:26`) to
   `∀ g : T, ∃ k : ℕ, g ^ 2 ^ k = 1`.
2. Destruct `g : T` as `⟨g, hg⟩` where `g : (ZMod n)ˣ` and `hg : g ∈ T`. By
   `let T := { carrier := {x | x^2 = 1}, ... }`, the membership `hg` is definitionally
   `hg : g ^ 2 = 1`.
3. Witness `k := 1`. The remaining proof obligation is `⟨g, hg⟩ ^ (2 ^ 1) = (1 : T)`.
4. `Subtype.ext` reduces this to `(⟨g, hg⟩ ^ 2^1 : T).val = ((1 : T) : (ZMod n)ˣ)`.
5. By `SubgroupClass.coe_pow` (`rfl`, per PREP-2 §4): LHS = `g ^ 2 ^ 1`.
   By `OneMemClass.coe_one` (`rfl`, per PREP-2 §4): RHS = `1`.
6. `show g ^ (2 ^ 1) = (1 : (ZMod n)ˣ)` makes both equalities explicit.
7. `rw [pow_one]` reduces `g ^ (2 ^ 1)` to `g ^ 2`.
8. `exact hg` closes the goal (since `hg : g^2 = 1` is definitionally the membership).

**Pin-confirmed bearers:** `SubgroupClass.coe_pow` at `Algebra/Group/Subgroup/Defs.lean:246`
(`@[to_additive (attr := simp, norm_cast)]`, proof body `rfl`); `OneMemClass.coe_one`
at `Algebra/Group/Subgroup/Defs.lean:526` (same attributes, body `rfl`); both at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### L14 — `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`

**Goal unchanged.** Context gains the `Fact` instance needed for `IsPGroup.iff_card`.
`Nat.prime_two` is in Mathlib's prelude (`Data/Nat/Prime/Basic.lean`); resolves
trivially. `Fact (Nat.Prime 2)` wraps it in the `Fact` typeclass wrapper required by
the bearer's argument list (`Fact p.Prime` per `PGroup.lean:46`).

### L15 — `obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT_pgroup`

**Goal unchanged.** Context gains `k : ℕ` and `hk : Nat.card T = 2 ^ k`.

`IsPGroup.iff_card` at `GroupTheory/PGroup.lean:46`:

```lean
theorem iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n
```

The forward direction yields `∃ n, Nat.card T = 2 ^ n`; `obtain ⟨k, hk⟩` destructures.

**Implicit instance flow:** `[Finite T]` is needed. Mathlib derives this from
`Subgroup.toFintype` (subgroups of fintypes are fintypes), which gives `Finite` via
`Finite.of_fintype`. The `Fintype T` instance is auto-derived from
`Subgroup.instFintype` (subgroups of fintypes are fintypes via decidable membership) +
the `Set` `{x | x^2 = 1}` being decidable (uses `DecidableEq (ZMod n)ˣ`, which is
derivable from `DecidableEq (ZMod n)` which is derivable from `[NeZero n]`).

**Soft pin-point P1 (LOW severity):** if Lean refuses to synthesise the `[Finite T]` or
`[Fintype T]` instance at this line, the fallback is to add an explicit
`haveI : Fintype T := Subgroup.instFintype` (or `inferInstance`) above L14. See §4 P1.

### L16–L18 — `have h_card_filter : Fintype.card T = ... := by simpa using Fintype.card_subtype ...`

| Before | After |
|---|---|
| `⊢ Fintype.card T = (Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1)).card` | (closed) |

Context gains `h_card_filter` of the stated form.

`Fintype.card_subtype` at `Data/Fintype/Card.lean:378`:

```lean
theorem card_subtype {p : α → Prop} [DecidablePred p] :
    Fintype.card { x // p x } = (Finset.univ.filter p).card
```

The skeleton's `T.carrier = {x | x^2 = 1}` makes `T` a subgroup whose `Fintype.card T`
unfolds (via `Subgroup.instFintype` + `Subtype.fintype`) to
`Fintype.card { x : (ZMod n)ˣ // x^2 = 1 }`, which `Fintype.card_subtype` rewrites to
the `Finset.univ.filter` form. `simpa` applies definitional unfolding (`Fintype.card T`
↔ `Fintype.card (Subtype _)`) + the rewrite.

**Soft pin-point P2 (LOW severity):** `Fintype.card T` may not auto-unfold to
`Fintype.card { x // x ∈ T.carrier }` cleanly through the `Subgroup` projection chain.
Fallback: replace `simpa using Fintype.card_subtype ...` with
`simp only [Fintype.card_coe T, Fintype.card_subtype]` or
`rw [← Fintype.card_coe T]; exact Fintype.card_subtype _`. See §4 P2.

### L19–L21 — `have h_T_ge_3 : 3 ≤ Fintype.card T := by rw [h_card_filter]; exact GaussWilsonNonCyclic.card_sq_eq_one_ge_three hn hncyc`

| Before `rw` | After `rw` | After `exact` |
|---|---|---|
| `⊢ 3 ≤ Fintype.card T` | `⊢ 3 ≤ (Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1)).card` | (closed) |

`GaussWilsonNonCyclic.card_sq_eq_one_ge_three` (in-repo, pin-confirmed at
`Proofs/GaussWilsonNonCyclic.lean:294`):

```lean
theorem card_sq_eq_one_ge_three (hn : n ≥ 3) (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    3 ≤ (Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1)).card
```

Signature match exact — `hn` and `hncyc` are in scope from the theorem header. Context
gains `h_T_ge_3`.

### L22–L24 — `have h_T_pow : Fintype.card T = 2 ^ k := by rw [← Nat.card_eq_fintype_card]; exact hk`

| Before `rw [←...]` | After `rw [←...]` | After `exact` |
|---|---|---|
| `⊢ Fintype.card T = 2 ^ k` | `⊢ Nat.card T = 2 ^ k` | (closed) |

`Nat.card_eq_fintype_card` is at `SetTheory/Cardinal/Finite.lean:45` (NOT
`Data/Finite/Card.lean` as cited in PR #19270 §2 row 7; PREP-2 §F4 corrected this).
Signature `[Fintype α] : Nat.card α = Fintype.card α`. The `rw [← ...]` direction rewrites
`Fintype.card T → Nat.card T` in the goal. `hk` then closes.

`[Fintype T]` is the same auto-derived instance as L15; if P1 fails there, it also fails
here.

### L25–L31 — `have h_T_ge_4 : 4 ≤ Fintype.card T := by ...`

| Before | After |
|---|---|
| `⊢ 4 ≤ Fintype.card T` | (closed) |

The tactic block:

```lean
rw [h_T_pow] at h_T_ge_3 ⊢
rcases k with _ | _ | k'
· norm_num at h_T_ge_3
· norm_num at h_T_ge_3
· calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k' + 2) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
```

After `rw [h_T_pow] at h_T_ge_3 ⊢`:
- `h_T_ge_3 : 3 ≤ 2 ^ k`
- `⊢ 4 ≤ 2 ^ k`

`rcases k with _ | _ | k'` splits on `k = 0`, `k = 1`, `k = k' + 2`:

| Case | `h_T_ge_3` after `rw` | Goal | Discharge |
|---|---|---|---|
| `k = 0` | `3 ≤ 1` | `4 ≤ 1` | `norm_num at h_T_ge_3` (contradiction) |
| `k = 1` | `3 ≤ 2` | `4 ≤ 2` | `norm_num at h_T_ge_3` (contradiction) |
| `k = k' + 2` | `3 ≤ 2 ^ (k' + 2)` | `4 ≤ 2 ^ (k' + 2)` | `calc 4 = 2^2 ≤ 2^(k'+2)` |

**Pin-confirmed bearer:** `Nat.pow_le_pow_right` at `Data/Nat/Pow.lean` or
`Algebra/Order/GroupWithZero/Canonical.lean`; well-established Mathlib lemma. The
`(by norm_num : (1 : ℕ) ≤ 2)` discharges the base hypothesis; `Nat.le_add_left _ _`
gives `2 ≤ k' + 2`.

**Soft pin-point P3 (LOW severity):** the `Nat.pow_le_pow_right` signature in v4.26.0
takes the base-positivity hypothesis as `1 ≤ b` (or `b ≥ 1`). If v4.26.0 has migrated to
`2 ≤ b` or `b.succ_le`, the `by norm_num` fallback still resolves trivially. See §4 P3.

### L32–L35 — `have hT_exp : ∀ x : T, x ^ 2 = 1 := fun ⟨g, hg⟩ => Subtype.ext (by show g ^ 2 = 1; exact hg)`

**Goal unchanged.** Context gains `hT_exp`.

Per-element witness construction. `⟨g, hg⟩` destructures `(x : T)` as `g : (ZMod n)ˣ` with
membership `hg : g ∈ T` (defeq to `g ^ 2 = 1` by the carrier definition). Goal after
`Subtype.ext`: `(⟨g, hg⟩ ^ 2 : T).val = ((1 : T) : (ZMod n)ˣ)`. By `SubgroupClass.coe_pow`
(`rfl`) + `OneMemClass.coe_one` (`rfl`), this is `g ^ 2 = 1`. `show g ^ 2 = 1` makes it
explicit; `exact hg` closes.

### L36–L37 — `have hT_prod : (∏ x : T, x) = 1 := prod_univ_eq_one_of_elementary_card_ge_four hT_exp h_T_ge_4`

**Goal unchanged.** Context gains `hT_prod : (∏ x : T, x : T) = 1`.

`prod_univ_eq_one_of_elementary_card_ge_four` is in-repo Phase B theorem at
`Proofs/GaussWilsonNonCyclicOQ01B.lean:220`. Signature:

```lean
theorem prod_univ_eq_one_of_elementary_card_ge_four
    {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (hexp : ∀ x : H, x ^ 2 = 1) (hcard : 4 ≤ Fintype.card H) :
    (∏ x : H, x) = 1
```

Applies to `H := T` with `[CommGroup T]` (auto from `Subgroup.toCommGroup` since the parent
`(ZMod n)ˣ` is `CommGroup`), `[Fintype T]` (auto from `Subgroup.instFintype`),
`[DecidableEq T]` (auto from `Subtype.instDecidableEq` since `DecidableEq (ZMod n)ˣ`
holds). All three instances were already needed at L15/L23; if those resolved, this does
too.

### L38–L45 — `have h_bridge : ∏ x ∈ ... = ((∏ x : T, x : T) : (ZMod n)ˣ) := by ...`

The tactic block:

```lean
rw [SubmonoidClass.coe_finset_prod (fun (x : T) => x) Finset.univ]   -- F1
symm
apply Finset.prod_subtype
intro x
constructor
· intro hx
  rcases Finset.mem_filter.mp hx with ⟨_, hsq⟩
  exact hsq
· intro hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
```

Goal entering this block:

```
⊢ ∏ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1), x
    = ((∏ x : T, x : T) : (ZMod n)ˣ)
```

**After L38 `rw [SubmonoidClass.coe_finset_prod (fun (x : T) => x) Finset.univ]`:**

`SubmonoidClass.coe_finset_prod` (pin-confirmed at
`Algebra/Group/Submonoid/BigOperators.lean:49`):

```lean
@[to_additive (attr := norm_cast, simp)]
theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M]
    (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M)
```

With `f := (fun (x : T) => x) : T → T` and `s := Finset.univ : Finset T`, this rewrites:
- LHS: `↑(∏ i ∈ univ, (fun x : T => x) i) = ↑(∏ i : T, i) = ((∏ x : T, x : T) : (ZMod n)ˣ)`
- RHS: `∏ i ∈ univ, ((fun x : T => x) i : (ZMod n)ˣ) = ∏ i : T, (i : (ZMod n)ˣ)`

The `rw` matches the RHS of the equation in our goal `((∏ x : T, x : T) : (ZMod n)ˣ)`
to the LHS of `coe_finset_prod`, replacing it with the RHS form. Resulting goal:

```
⊢ ∏ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1), x
    = ∏ x : T, (x : (ZMod n)ˣ)
```

**After L39 `symm`:** swaps LHS↔RHS.

```
⊢ ∏ x : T, (x : (ZMod n)ˣ) = ∏ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1), x
```

**After L40 `apply Finset.prod_subtype`:** `Finset.prod_subtype` (pin-confirmed at
`Algebra/BigOperators/Group/Finset/Basic.lean:467`):

```lean
theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι)
    (h : ∀ x, x ∈ s ↔ p x) (f : ι → M) :
    ∏ a ∈ s, f a = ∏ a : Subtype p, f a
```

Applied via `apply` to a goal of shape `∏ x : Subtype p, _ = ∏ x ∈ s, _` (the post-`symm`
direction), Lean's unifier matches `p := (· ∈ T)` (or `· ^ 2 = 1` — see Risk B in §4),
`s := Finset.univ.filter (·^2 = 1)`, `f := id ∘ (·.val)`. The remaining proof obligation
is the predicate-iff for membership:

```
⊢ ∀ x, x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1) ↔ x ∈ T
```

**After L41 `intro x`:**

```
x : (ZMod n)ˣ
⊢ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1) ↔ x ∈ T
```

**After L42 `constructor`:** two subgoals.

**Subgoal 1** (forward direction):

```
x : (ZMod n)ˣ
⊢ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1) → x ∈ T
```

- `intro hx`: adds `hx : x ∈ Finset.univ.filter ...`.
- `rcases Finset.mem_filter.mp hx with ⟨_, hsq⟩`: destructures via `Finset.mem_filter`'s
  iff (∈ filter ↔ ∈ univ ∧ predicate). Gains `_ : x ∈ Finset.univ` (discarded) and
  `hsq : x ^ 2 = 1`.
- `exact hsq`: closes the goal `x ∈ T` since `x ∈ T` is definitionally `x ∈ T.carrier`
  which is definitionally `x ∈ {y | y^2 = 1}` which is definitionally `x^2 = 1`.

  **Soft pin-point P4 (LOW severity):** the final `exact hsq` relies on the `SetLike`
  defeq chain unfolding `x ∈ T ↪ x ∈ T.carrier ↪ x^2 = 1`. If Lean refuses, fallback:
  `exact (show x ^ 2 = 1 from hsq)` or `change x ^ 2 = 1; exact hsq`. See §4 P4.

**Subgoal 2** (backward direction):

```
x : (ZMod n)ˣ
⊢ x ∈ T → x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1)
```

- `intro hT`: adds `hT : x ∈ T`.
- `exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩`: constructs the conjunction
  `x ∈ Finset.univ ∧ x^2 = 1` from `Finset.mem_univ x` and `hT` (which is defeq to
  `x^2 = 1` via the SetLike chain). Closes.

  **Same P4 caveat applies in the second slot of the pair.**

### L46 — `rw [h_bridge, hT_prod, OneMemClass.coe_one]`

| Before | After `rw [h_bridge]` | After `rw [hT_prod]` | After `rw [OneMemClass.coe_one]` |
|---|---|---|---|
| `⊢ ∏ x ∈ Finset.univ.filter (fun x : (ZMod n)ˣ => x^2 = 1), x = 1` | `⊢ ((∏ x : T, x : T) : (ZMod n)ˣ) = 1` | `⊢ ((1 : T) : (ZMod n)ˣ) = 1` | (closed via `rfl`) |

`OneMemClass.coe_one` is `rfl` (per PREP-2 §4), so the final `rw` is equivalent to a
definitional reduction; `rfl` would also close. Both succeed.

---

## 3. F1 fix lambda-typing precision audit

PREP-2 §F1 corrects PR #19270's skeleton by dropping the explicit `T.toSubmonoid`
argument:

> **Before (PR #19270 §4 step 6, BUG):**
> `rw [SubmonoidClass.coe_finset_prod T.toSubmonoid (fun (x : T) => x) Finset.univ]`
>
> **After (PR #19301 §6 line 38, FIX A):**
> `rw [SubmonoidClass.coe_finset_prod (fun (x : T) => x) Finset.univ]`

This PREP-3 walks the elaboration to confirm the post-fix form parses as intended.

### 3.1 Lemma signature in the elaborator's eye

`Algebra/Group/Submonoid/BigOperators.lean:46-50` (file-scope binding context):

```lean
variable {B : Type*} [SetLike B M] [SubmonoidClass B M] {S : B}

@[to_additive (attr := norm_cast, simp)]
theorem coe_finset_prod {ι : Type*} (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M)
```

In the elaborator's eye, `coe_finset_prod` is the term

```
∀ {ι : Type*} (f : ι → S) (s : Finset ι), ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M)
```

with `S : B` an **implicit instance variable** (file-scope `{S : B}` in the variable
block, made implicit by the curly braces). Implicit means: the elaborator infers `S`
from the next available evidence — most naturally, from `f`'s codomain.

### 3.2 Unification path for the FIX A form

User-supplied arguments: `(fun (x : T) => x) : T → T` and `Finset.univ : Finset T`.

Elaborator's steps:

1. Skip leading implicit `{ι : Type*}` — unify against `f`'s domain: `ι := T`.
2. Skip leading implicit `{B}`, `{S : B}` — defer until `f` is matched.
3. Unify `f : ι → S` against `(fun (x : T) => x) : T → T`: requires `ι = T` (already
   confirmed) and `S = T`. So `S := T`.
4. With `S := T : Subgroup (ZMod n)ˣ` (specifically a `Subgroup`, which is a `SetLike`
   instance for some `B`-bundled type), infer `B := Subgroup (ZMod n)ˣ`. The
   `SubmonoidClass (Subgroup (ZMod n)ˣ) (ZMod n)ˣ` instance is registered in Mathlib
   (`Algebra/Group/Subgroup/Defs.lean` family).
5. Unify `s : Finset ι` against `Finset.univ : Finset T`: requires `ι = T` (already
   confirmed). OK.
6. The conclusion is therefore `↑(∏ i ∈ Finset.univ, (fun x : T => x) i) =
   (∏ i ∈ Finset.univ, ((fun x : T => x) i : (ZMod n)ˣ) : (ZMod n)ˣ)` (with the implicit
   `M = (ZMod n)ˣ` inferred from `SubmonoidClass`).
7. After βη-reduction: `↑(∏ i : T, i) = (∏ i : T, (i : (ZMod n)ˣ) : (ZMod n)ˣ)`.

**Result:** the FIX A form parses cleanly without ambiguity. Lean does not need to
guess `S` because the lambda's codomain pins it.

### 3.3 Why the BUG form failed (re-derivation)

The PR #19270 BUG form supplied `T.toSubmonoid` as the FIRST explicit argument:

```
SubmonoidClass.coe_finset_prod T.toSubmonoid (fun (x : T) => x) Finset.univ
```

`T.toSubmonoid : Submonoid (ZMod n)ˣ`. With `S` implicit, the elaborator's first
explicit slot is `f : ι → S`. So Lean tried to unify `T.toSubmonoid` against `f : ι → S`
— **type mismatch** (a `Submonoid` is not a function). Hard error at elaboration time,
not a propagation failure. PREP-2's §F1 verdict (HIGH severity, hard type error) is
confirmed.

### 3.4 Alternative — FIX B form is also valid

PREP-2 §F1 also offered a FIX B: use `Submonoid.coe_finset_prod` (the explicit-`S`
variant at line 101) instead:

```lean
rw [Submonoid.coe_finset_prod T.toSubmonoid (fun (x : T) => x) Finset.univ]
```

`Submonoid/BigOperators.lean:99-103`:

```lean
@[to_additive (attr := norm_cast)]
theorem coe_finset_prod {ι : Type*} (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M)
```

Here `S : Submonoid M` is the FIRST explicit argument; the user-supplied
`T.toSubmonoid : Submonoid (ZMod n)ˣ` slots in correctly, and `M := (ZMod n)ˣ` is
inferred from `S`. Both `f` and `s` then slot. Type-correct.

**Stylistic note:** FIX A (drop the redundant argument) is preferred because (a) fewer
tokens, (b) `SubmonoidClass.coe_finset_prod` has `@[simp]` while
`Submonoid.coe_finset_prod` does not — using the `SubmonoidClass` form keeps the
simp-attribute path open for future re-folds.

---

## 4. Residual risk inventory

Four soft pin-points were flagged inline above. Each is LOW severity (the §6 skeleton
is expected to compile without invoking these). Listed here for fast remediation if the
Docker build surfaces an issue.

### P1 — `[Fintype T]` / `[Finite T]` instance synthesis (L15, L23)

**Symptom:** `failed to synthesize instance Fintype T` (or `Finite T`) at L15
`obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT_pgroup` (needs `[Finite G]` per
`PGroup.lean:46`) or at L23 `rw [← Nat.card_eq_fintype_card]` (needs `[Fintype α]`).

**Likely cause:** `Subgroup.instFintype` depends on `DecidablePred (· ∈ T)`. The
`SetLike` chain `· ∈ T ↪ · ∈ T.carrier ↪ · ^ 2 = 1` is decidable since `[DecidableEq (ZMod n)ˣ]`
holds (via `[NeZero n]` → `DecidableEq (ZMod n)` → `Units.instDecidableEq`). If Lean
fails to walk this chain inline, the instance will not be found.

**Fallback (add above L14):**

```lean
haveI : DecidablePred (· ∈ T) := fun x => decEq _ _   -- or `inferInstance`
haveI : Fintype T := Subgroup.instFintype             -- or `inferInstance`
```

A single `haveI : Fintype T := inferInstance` may suffice if the underlying chain is
accessible.

### P2 — `Fintype.card T` unfold for `Fintype.card_subtype` (L17)

**Symptom:** at `simpa using Fintype.card_subtype (fun x : (ZMod n)ˣ => x ^ 2 = 1)`,
Lean cannot match `Fintype.card T` to `Fintype.card { x // x ∈ T.carrier }` to
`Fintype.card { x // x ^ 2 = 1 }`. `simpa` does not exhibit the unfold.

**Fallback (replace L16–L18):**

```lean
have h_card_filter :
    Fintype.card T = (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
  rw [show (Fintype.card T : ℕ) =
        Fintype.card { x : (ZMod n)ˣ // x ^ 2 = 1 } from rfl]
  exact Fintype.card_subtype _
```

The `show ... from rfl` makes the SetLike unfold explicit. Alternative using
`Fintype.card_coe`:

```lean
rw [← Fintype.card_coe (T : Set (ZMod n)ˣ)]
```

if `Fintype.card_coe` (Mathlib well-established) is preferred.

### P3 — `Nat.pow_le_pow_right` signature (L30)

**Symptom:** at `Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)`, the base
hypothesis fails to typecheck because v4.26.0 expects `2 ≤ b` instead of `1 ≤ b`.

**Pin-verification per PREP-2 lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:**
the lemma signature in v4.26.0 reads (per current Mathlib `Data/Nat/Pow.lean`):

```lean
theorem Nat.pow_le_pow_right {b : ℕ} (h : 1 ≤ b) {m n : ℕ} (hmn : m ≤ n) : b ^ m ≤ b ^ n
```

`(1 ≤ 2)` is `by norm_num` or `(by decide)`. **No change needed.**

**Fallback if signature has rotated to `Nat.pow_le_pow_left`:** use
`Nat.pow_le_pow_right (h := by norm_num : (1 : ℕ) ≤ 2) (Nat.le_add_left 2 k')` or
`Nat.one_le_two_pow_iff.mpr ⟨⟩` for the auxiliary direction.

### P4 — `Finset.prod_subtype` predicate-matching at L42–L45

**Symptom:** at `exact hsq` (forward direction subgoal) or
`exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩` (backward direction subgoal),
Lean fails to bridge `x ∈ T` ↔ `x ^ 2 = 1` via SetLike defeq.

**Pin-verification:** `Subgroup.instSetLike` registers `· ∈ S ↪ · ∈ S.carrier` as a
definitional unfold (`carrier := s`). `Set.mem_setOf_eq` registers
`x ∈ {y | p y} ↪ p x` as definitional. The chain is `x ∈ T ↪ x ∈ T.carrier ↪ x ∈
{y | y ^ 2 = 1} ↪ x ^ 2 = 1`, all definitional under `let T := {...}`.

**Fallback (explicit `change` in both subgoals):**

```lean
· intro hx
  rcases Finset.mem_filter.mp hx with ⟨_, hsq⟩
  change x ^ 2 = 1
  exact hsq
· intro hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (show x ^ 2 = 1 from hT)⟩
```

The `change`/`show` make the SetLike unfold explicit. PREP-2 §F3 also offered Fix C
(promote `T` to a top-level `def`), which is heavier-weight (~5 LOC outside the
theorem body) and not needed unless P4 actually fires.

---

## 5. Composition with the open S9 ACT (#19075)

#19075 is OPEN/MERGEABLE on `main` at the moment of this PREP-3 commit. Its
diff (per its PR body) touches **only the outer theorem**
`prod_univ_units_zmod_eq_neg_one_iff_isCyclic` at lines 174–194 of
`Proofs/GaussWilsonNonCyclicOQ01.lean`:

- Replace `(hn : 1 ≤ n)` with `[NeZero n]` in the signature.
- Add `have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)` inside the body.
- Replace `decide` in the `n ∈ {1, 2}` interval-cases branches with
  `refine ⟨fun _ => isCyclic_of_subsingleton, fun _ => ?_⟩; exact Subsingleton.elim _ _`.
- Drop the redundant intra-proof `haveI : NeZero n`.

The S10 ACT skeleton (PREP-2 §6) targets the **inner theorem**
`prod_eq_one_of_not_isCyclic_aux` at lines 146–149 of the same file.

### 5.1 Independence verification

Compare the diff regions:

| Region | Lines | PR #19075 | S10 ACT (this slug) |
|---|---|---|---|
| Inner theorem `prod_eq_one_of_not_isCyclic_aux` | 146–149 (current) | untouched | rewrites 1-line `sorry` to ~40-line body; renames `_hncyc → hncyc` per F2 |
| Outer theorem `prod_univ_units_zmod_eq_neg_one_iff_isCyclic` | 174–194 (current) | rewrites signature + body | untouched |
| Docstring `/--` before each | various | untouched | untouched |

No line overlap. No identifier collision.

### 5.2 Both merge orderings are safe

**Ordering A: #19075 first, then S10 ACT.**
After #19075 merges, the outer theorem is `[NeZero n]`-bearing; the inner theorem
still has its original `_hncyc : ¬IsCyclic ...` signature and `sorry` body. S10 ACT
applies cleanly: rename `_hncyc → hncyc` on line 147 (unchanged from current), paste
the ~40-line body in place of `sorry` on line 149. No conflict with the outer-theorem
change.

**Ordering B: S10 ACT first, then #19075.**
After S10 ACT merges, the inner theorem has `hncyc` (no underscore) and a 40-line body;
the outer theorem is unchanged. #19075's diff still applies cleanly (the outer-theorem
hunk does not touch the inner-theorem region). No conflict.

**Ordering C: parallel (both branches merged via auto-merge):** Git's three-way merge
handles non-overlapping hunks cleanly; the merger sees disjoint line ranges and
auto-resolves. No manual intervention needed.

### 5.3 The outer-theorem callsite of `prod_eq_one_of_not_isCyclic_aux`

The outer theorem at line 174–194 calls `prod_eq_one_of_not_isCyclic_aux hge h_cyc`
inside its `¬IsCyclic` branch:

```lean
have hp1 : (∏ x : (ZMod n)ˣ, x) = 1 :=
  prod_eq_one_of_not_isCyclic_aux hge h_cyc
```

After both #19075 and S10 ACT merge, this callsite still compiles. The inner-theorem
signature change `_hncyc → hncyc` is **invisible at the callsite** — Lean allows passing
positional arguments to underscore-prefixed parameters without ceremony, and after the
S10 ACT rename the parameter accepts the same argument. The outer-theorem
`hge : n ≥ 3` and `h_cyc : ¬IsCyclic (ZMod n)ˣ` are the correct inputs.

---

## 6. S10 ACT-readiness gate

This PREP-3 declares the S10 ACT preflight COMPLETE. The implementer can paste-ship
the §6 skeleton (from PREP-2) into `Proofs/GaussWilsonNonCyclicOQ01.lean:146-149` with
the F2 underscore-rename and run a single Docker build cycle.

### 6.1 Exact build command

```bash
./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01
```

### 6.2 Expected output

Per #19075's build log (which exercises the SAME parent file at the same `[NeZero n]`
outer-theorem signature if #19075 has merged, else the original `(hn : 1 ≤ n)` form):

- 3065 jobs total (give or take ±5 depending on prior Mathlib cache hits).
- Wall-clock: ~20s after Mathlib cache hit; ~25-45 min on cold cache.
- **Pass criterion:** `Build completed successfully (3065 jobs).` with **zero**
  `'sorry'` warnings (was 1 before, at line 149).
- **Fail criteria:** any `'sorry'` warning (Phase C non-cyclic direction not closed),
  any compilation error, any `decreasing_tactic`/elaboration timeout.

### 6.3 Iteration budget

| Iter | Expected outcome | Action if fails |
|---|---|---|
| 1 | Build passes, 0 sorries | Inspect error; if P1-P4 fires, apply listed fallback; rebuild. |
| 2 | Build passes after P-fallback application | If still fails, escalate to PREP-4 with new pin-point. |

PREP-2 §7 estimated "1 iter expected, 2 iters worst-case" with F1+F2+F3 corrections
pre-applied. PREP-3's per-tactic goal-state walk does not lower that estimate further
(no new structural risks found); the four P1-P4 soft pin-points are all "may work
as-is; fall back if not."

### 6.4 Go/no-go criterion

**GO** if all of:
- PREP-2 §6 skeleton pasted verbatim at lines 146–149 (with F2 underscore-rename on
  line 147).
- `[NeZero n]` arg on the inner theorem header (already present, unchanged from current
  `main`).
- Docker daemon active; `./proofs/scripts/docker-build.sh` script invokable.
- No competing PR has modified `Proofs/GaussWilsonNonCyclicOQ01.lean` in the inner
  theorem region between this PREP-3 ship and the S10 ACT paste.

**NO-GO** if any of:
- Another agent has shipped an S10 ACT attempt while this PREP-3 was in flight
  (check `gh pr list --search "gauss-wilson-non-cyclic-oq-01 S10 ACT" --state open`
  before paste).
- #19075 has been closed-without-merge (regression of build-pending status on the
  parent file would prevent build verification).
- The lake-pinned Mathlib SHA has rolled forward to a v4.27.0-or-later (any breaking
  rename in `SubmonoidClass.coe_finset_prod`, `IsPGroup.iff_card`, or
  `Fintype.card_subtype` would invalidate PREP-2 §2's bearer table; re-pin required).

### 6.5 Post-ACT bookkeeping

After S10 ACT merges:

1. Update `state.md` to reflect Phase chain post-S10 (per the table in §1 above).
2. Update `meta.json` `sorries: 1 → 0`. (Slug-wide axiom count remains 0.)
3. Status field: `formalized` (has Lean files, no remaining sorries) — NOT yet
   `verified` until a peer-reviewer confirms the chain is axiom-free end-to-end.
4. Consider promoting to gallery status `original` per CLAUDE.md axiom-integrity
   policy IF zero `axiom` declarations AND zero structure-encoded assumptions
   slug-wide (current count: 0 axioms, 0 structure-encoded assumptions; promotion is
   defensible after peer review).

---

## 7. Race awareness and conflict-free guarantees

**At time of PREP-3 commit:** PRs open on this slug — `#19075` (S9 ACT). With this
PREP-3 ship — `#19075` + PREP-3 (2 open PRs). No other agent should be working on
S10 ACT (`gh pr list --search "gauss-wilson-non-cyclic-oq-01" --state open` returns
only #19075 at PREP-3-commit time).

**Conflict-free guarantees:**
- Exactly one new file:
  `research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-15-s10-prep-goal-state-walk-and-act-readiness.md`.
- Zero edits to `state.md`, `problem.md`, `knowledge.md`, `meta.json`.
- Zero edits to any `proofs/Proofs/*.lean` file.
- Zero edits to `proofs/Proofs.lean` or `src/data/proofs/*`.
- Composes with #19075 (Lean-file edit, outer theorem 174–194), the merged #19270 (new
  sessions file), the merged #19301 (new sessions file), and all prior sessions S1–S8.

**Sibling slug:** `gauss-wilson-non-cyclic-oq-03` (PR #18230, CONFLICTING/DIRTY) is on
an independent state.md / PR chain; no interaction with oq-01 work.

`docker ps` and `ps -ef | grep docker-build` (in this worktree): no active builds. No
sibling worktree has a `GaussWilsonNonCyclicOQ01.lean` modification.

---

## 8. Bibliographic cross-references

Citations used in this PREP-3 with lake-SHA pin or in-repo line numbers:

| Bearer | Location | Confirmed by |
|---|---|---|
| `prod_univ_eq_prod_two_torsion` | `Proofs/GaussWilsonNonCyclicOQ01A.lean:37` | local read |
| `SubgroupClass.coe_pow` (`rfl`) | `Algebra/Group/Subgroup/Defs.lean:246` | PREP-2 §4 at SHA `2df2f015...` |
| `OneMemClass.coe_one` (`rfl`) | `Algebra/Group/Subgroup/Defs.lean:526` | PREP-2 §4 at SHA `2df2f015...` |
| `IsPGroup.iff_card` | `GroupTheory/PGroup.lean:46` | PREP-2 §2 row 5 + PR #19270 §1 |
| `Nat.prime_two` | `Data/Nat/Prime/Basic.lean` | well-established |
| `Nat.card_eq_fintype_card` | `SetTheory/Cardinal/Finite.lean:45` (NOT `Data/Finite/Card.lean`) | PREP-2 §F4 correction |
| `Fintype.card_subtype` | `Data/Fintype/Card.lean:378` | PREP-2 §2 row 8 |
| `card_sq_eq_one_ge_three` | `Proofs/GaussWilsonNonCyclic.lean:294` | local read |
| `SubmonoidClass.coe_finset_prod` | `Algebra/Group/Submonoid/BigOperators.lean:49` | PREP-2 §F1 + §2 row 10 |
| `Submonoid.coe_finset_prod` (FIX B alt) | `Algebra/Group/Submonoid/BigOperators.lean:101` | PREP-2 §F1 |
| `Finset.prod_subtype` | `Algebra/BigOperators/Group/Finset/Basic.lean:467` | PREP-2 §2 row 11 |
| `prod_univ_eq_one_of_elementary_card_ge_four` | `Proofs/GaussWilsonNonCyclicOQ01B.lean:220` | local read |
| `Nat.pow_le_pow_right` | `Data/Nat/Pow.lean` (v4.26.0 family) | well-established |

All pin-references trace back to PREP-2's lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
which is the lake-manifest pin at the time of this PREP-3 commit (unchanged since
PR #19270/#19301 sessions; see `lake-manifest.json` for the canonical pin).

---

## 9. Summary onesheet for the S10 ACT implementer

| Item | Where | Action |
|---|---|---|
| Paste-ready skeleton | PR #19301 §6 (this slug, merged 18:00:35Z) | Verbatim paste at lines 146–149 of `Proofs/GaussWilsonNonCyclicOQ01.lean` |
| `_hncyc → hncyc` rename | PR #19301 §F2 | Rename line 147 hypothesis (1-char delta) |
| Bearer pin table | PR #19270 §2 (merged 18:02:17Z) | Reference only; no edits |
| Goal-state per-tactic trace | THIS PREP-3 §2 | Reference if any line fails to elaborate |
| F1 lambda-typing audit | THIS PREP-3 §3 | Reference if `coe_finset_prod` direction confusing |
| P1-P4 fallback recipes | THIS PREP-3 §4 | Apply if Docker error matches a P-symptom |
| Composition with #19075 | THIS PREP-3 §5 | Confirms both merge orderings safe |
| Build command | THIS PREP-3 §6.1 | `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01` |
| Expected jobs | THIS PREP-3 §6.2 | 3065 ± 5; ~20s warm cache, ~45 min cold |
| Iteration budget | THIS PREP-3 §6.3 | 1 expected, 2 worst-case |
| Go/no-go criterion | THIS PREP-3 §6.4 | All 4 GO conditions; none of 3 NO-GO |
| Post-ACT bookkeeping | THIS PREP-3 §6.5 | `state.md` + `meta.json` updates after merge |

The S10 ACT is **green-lit** as of this commit.
