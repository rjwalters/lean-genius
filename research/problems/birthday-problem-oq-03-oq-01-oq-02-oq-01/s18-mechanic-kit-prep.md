## S18 Mechanic Kit Prep — 37-error v4.26.0 fix plan

**Companion to**: state.md S17 entry (build-blocker discovery), PR #18973 (state.md), PR #19002 (JSON sync).
**Scope**: doc-only PREP for a mechanic / doctor agent. No Lean edits this session.
**Target file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (2086 LOC).
**Pin**: Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
**Build log**: `.loom/logs/researcher-9-birthday-s17-build.log`.

---

### Why this doc rather than a fix PR

The S17 Docker build surfaced **37 elaboration errors**. Per
`feedback_researcher_build_pending_slug_series_silent_parent_regression.md`,
research PRs are bounded to ≤3 surgical 1-LOC fixes. The fix scope here is
mechanic / doctor territory. This doc converts a 9-cluster mixed-cause inventory
into a **mechanic-ready kit** — each cluster gets a root-cause diagnosis,
proposed fix, file:line references, and Mathlib v4.26.0 API citations — so the
next mechanic can land the fix in 1–2 Docker iterations instead of 5–10.

Pattern matches recent mechanic-kit prep docs:
- `feedback_mechanic_mathlib_v426_ehrhart_cube_7_kit.md`
- `feedback_mechanic_mathlib_v426_clt_oq01oq01oq04_8axiom_kit.md`
- `feedback_mechanic_mathlib_v426_tractatus_8kit.md`

---

### Cluster summary

| ID | Cluster | Lines | Root cause | LOC est |
|---|---|---|---|---|
| K1 | Forward-reference `exp_lambda_tendsto` | 352, 353 | Theorem at L343 references lemma at L468 — never legal in Lean | reorder, 0 LOC delta |
| K2 | `filter_upwards` type annotation drift | 419–460 (5 sites) | `∀ᶠ d in atTop` w/o annotation now infers `d : ℝ` from body | +5 LOC annotation |
| K3 | `subst hmj`+`show m = j` block | 815, 823 | `subst hmj : m = j` eliminates `j`, not `m`, in v4.26.0 | +6 LOC `rw [hmj]` swap |
| K4 | `Nat.descFactorial_two` removed | 1167, 1197 | Decl gone in v4.26.0; only `cast_descFactorial_two` remains | +4 LOC derive inline |
| K5 | `subst` direction trap (let-destructure) | 1299, 1300, 1305, 1306 | Triple-destructure + `LT.lt.le` now project wrong direction | +8 LOC explicit destructure |
| K6 | `omega` regression on let-projections | 1327, 1330 | `omega` no longer decodes `(a,b,c).1` projections | +4 LOC `obtain`-destructure first |
| K7 | `card_eq_sum_card_fiberwise` signature: `Set.MapsTo` | 1384, 1394, 1414, 1428 | v4.26 requires `Set.MapsTo` not `∀ p ∈ s, ...` | +4 LOC annotation on `hF` |
| K8 | `card_sdiff` → `card_sdiff_of_subset` rename | 767, 1493 | `card_sdiff` is now unconditional `_ ∩ _` form | +2 LOC rename |
| K9 | `orderEmbOfFin_unique` arg-order shift | 965 | `h : s.card = k` now explicit first arg | +1 LOC add `hcard` |
| K10 | `Fin (Fintype.card (Fin d))` vs `Fin d` | 551–570 (3 errors) | Anonymous-constructor inference for `Equiv` now picks wrong codomain | +3 LOC type annotation |
| K11 | `card_sdiff` ricochet → unsolved 611 / 1838 | 611, 1838 | "No goals" residue from upstream K8 fix discharging prior steps | -2 LOC remove |
| K12 | Bizarre hygiene leak: `Nat.totient._@...` | 1834 | Likely hygiene-collision on `_φ` or downstream `tot`-named let | requires read-through |
| K13 | `b₁`/`c₁`/`b₂`/`c₂` scope loss | 1580, 1589, 1598, 1607 | `obtain ⟨a₁, b₁, c₁⟩ := …` pattern now scopes only to single tactic | +4 LOC widen scope or repeat `obtain` |
| K14 | Misc `simp` residue: `unsolved goals` | 554, 570, 1193, 1384, 1414 | Drift from earlier fixes; expect cascade-discharge after K2, K7 | re-evaluate |

**Estimated net**: ≈ 35–45 LOC of surgical edits across ~16 distinct sites.
Many `unsolved goals` errors (K14) and "No goals to be solved" (K11) will
cascade-resolve after the upstream fixes in K2/K7/K8 land.

---

### Cluster K1: forward reference to `exp_lambda_tendsto`

**Error** (build log L62):
```
Proofs/BirthdayProblemOQ03OQ01OQ02.lean:353:44: Unknown identifier `exp_lambda_tendsto`
Proofs/BirthdayProblemOQ03OQ01OQ02.lean:352:31: unsolved goals
```

**Source** (lines 343–354):
```lean
theorem poisson_approx_birthday3 (c : ℝ) (hc : 0 < c) :
    let n := ⌊c · d^(2/3)⌋₊
    Filter.Tendsto (… − rexp(-… choose 3 / d^2)) atTop (nhds 0) := by
  have h := (p_no_triple_tendsto c hc).sub (exp_lambda_tendsto c hc)
  simpa using h
```

**Diagnosis**: `poisson_approx_birthday3` (L343) references `exp_lambda_tendsto`
(L468) and `lambda_tendsto` (L413). Lean 4 has never allowed forward references
to non-mutual non-axiom defs — yet this likely compiled at v4.25 because Mathlib
auto-imported a same-named declaration. At v4.26.0 the import auto-resolution
changed and the local forward-ref fails.

**Fix** (zero LOC delta — pure reorder):
Move the `theorem poisson_approx_birthday3` block (L342–354) to immediately
after the `exp_lambda_tendsto` definition (L468 onward). This is a 12-line cut
+ paste, no content change.

**Risk**: low. The surrounding `Decomposition of poisson_approx_birthday3` comment
block (L356–380) is documentation and can stay in place or move with the theorem.

---

### Cluster K2: `filter_upwards` infers `∀ᶠ d : ℝ in atTop` instead of `∀ᶠ d : ℕ in atTop`

**Errors** (5 sites in `lambda_tendsto` proof body L413–467):
- L419: `hpow3_eq` declared as `∀ᶠ d in Filter.atTop, …` — v4.26 infers `d : ℝ`
- L421:76: `Nat.pos_of_ne_zero hd` — `hd : d ≠ 0` for `d : ℝ`, but `Nat.pos_of_ne_zero` expects `ℕ`
- L429:20, 445:20: `filter_upwards [hpow3_eq, …]` — type mismatch on `hpow3_eq : ∀ᶠ (d : ℝ) …`
- L451:20: `Filter.Tendsto.eventually_ge_atTop rpow23_atTop (2/c)` — produces `∀ᶠ (x : ℕ) in atTop` (correct) but mixed with ℝ-form `hpow3_eq`
- L457:20: `hnc_ge_2 : ∀ᶠ d in atTop, 2 ≤ ⌊c · d^(2/3)⌋₊` — v4.26 infers `d : ℝ`

**Root cause**: at v4.25, `∀ᶠ d in Filter.atTop, P d` could elaborate `d`'s type
from the surrounding hypotheses (the `(d : ℝ)` casts in the body). At v4.26.0,
the elaborator now requires an explicit annotation `∀ᶠ d : T in Filter.atTop`
when `P d` mixes `(d : ℝ)` casts (Lean defaults the type to ℝ instead of ℕ).

**Fix** (5 sites, +5 LOC):

```lean
-- L419 → add `: ℕ` annotation
have hpow3_eq : ∀ᶠ d : ℕ in Filter.atTop,
    ((d : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = (d : ℝ) ^ 2 := by …

-- L450 → add `: ℕ` annotation
have hnc_ge_2 : ∀ᶠ d : ℕ in Filter.atTop,
    2 ≤ ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊ := by …
```

The two `have` lines need the `d : ℕ` annotation. The three `filter_upwards`
sites (L429, 445, 451, 457) cascade-resolve once the source `have`s are typed.

**Risk**: low. This is the canonical fix per
`feedback_researcher_mathlib_v426_ennreal_notation_inside_rw_named_arg_trap.md`
(general v4.26.0 elaborator strictness pattern).

---

### Cluster K3: `subst hmj` direction trap (lines 815, 823)

**Errors**:
```
815:24: Unknown identifier `j`
823:31: Unknown identifier `k`
```

**Source** (lines 813–830):
```lean
by_cases hmj : m = j
· subst hmj                                -- v4.26 eliminates j, not m
  show (if hj : m = j then f i …) = f m   -- references j → Unknown identifier
  rw [dif_pos rfl]
  exact h.1
· by_cases hmk : m = k
  · subst hmk
    show (if hj : m = j then f i …) = f m -- references k → Unknown identifier
    …
```

**Root cause**: v4.26.0's `subst` direction handling: when `hmj : m = j`, the
old `subst hmj` substituted `m` (the lhs variable) throughout, leaving `j` in
scope. At v4.26.0, `subst hmj` eliminates `j` and substitutes `j → m`, so the
subsequent `show` clause referencing `j` and `k` fails. Documented in memory
`feedback_mechanic_mathlib_v426_ehrhart_cube_7_kit.md` (`subst hkd` eliminates
wrong variable trap).

**Fix** (+6 LOC):
Swap `subst hmj` → `rw [hmj]`, and `subst hmk` → `rw [hmk]`. The `rw` form
substitutes `m` throughout (the lhs of the equality) without eliminating
either side from scope.

```lean
by_cases hmj : m = j
· rw [hmj]                                 -- m becomes j throughout
  show (if hj : j = j then f i …) = f j
  rw [dif_pos rfl]
  exact h.1
· by_cases hmk : m = k
  · rw [hmk]
    show (if hj : k = j then f i …) = f k
    …
```

Note: the `show` clauses must also update `m → j` and `m → k` respectively
once the `rw` lands.

**Risk**: low. Standard fix per memory pattern. Test that subsequent
`dif_neg hmj` / `dif_neg hmk` rewrites still trigger (they should — the
hypothesis names are preserved by `rw`).

---

### Cluster K4: `Nat.descFactorial_two` removed in v4.26.0

**Errors**:
- L1167: `Unknown constant 'Nat.descFactorial_two'`
- L1197: `Unknown constant 'Nat.descFactorial_two'`

**Mathlib v4.26.0 verification** (`gh search code "descFactorial_two"`):
- `Nat.cast_descFactorial_two` (in `Mathlib/Data/Nat/Factorial/Cast.lean`):
  `(a.descFactorial 2 : S) = a * (a - 1)` — ℕ-cast form, requires `S` with
  appropriate subtraction structure
- **`Nat.descFactorial_two` is removed**. No direct ℕ-form replacement.

**Source — L1167** (`descFactorial_two_real_eq` body):
```lean
have hN : n.descFactorial 2 = n * (n - 1) := Nat.descFactorial_two n
```

**Fix** (+2 LOC, derive inline):
```lean
have hN : n.descFactorial 2 = n * (n - 1) := by
  simp [Nat.descFactorial, Nat.mul_comm]
```

Or even simpler, since this lemma's final goal `descFactorial_two_real_eq`
has `(... : ℝ)`:

```lean
lemma descFactorial_two_real_eq (n : ℕ) :
    (n.descFactorial 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  rcases n with _ | n
  · simp [Nat.descFactorial]
  · simp [Nat.descFactorial, Nat.succ_sub_one]; push_cast; ring
```

**Source — L1197** (`tripleCount_descFact_2_eq_pairs` body):
```lean
rw [← card_tripleCountFinset, Nat.descFactorial_two, ← Finset.card_offDiag]
```

**Fix** (+2 LOC):
```lean
have hdesc : ∀ k, (k : ℕ).descFactorial 2 = k * (k - 1) := fun k => by
  simp [Nat.descFactorial, Nat.mul_comm]
rw [← card_tripleCountFinset, hdesc, ← Finset.card_offDiag]
```

Or invoke `Finset.card_offDiag` after manually unfolding:
```lean
rw [← card_tripleCountFinset]
have hdesc : (#(tripleCountFinset d n f)).descFactorial 2 =
    #(tripleCountFinset d n f) * (#(tripleCountFinset d n f) - 1) := by
  simp [Nat.descFactorial, Nat.mul_comm]
rw [hdesc, ← Finset.card_offDiag]
```

**Risk**: medium. The `simp [Nat.descFactorial]` discharge depends on the
definitional unfolding of `Nat.descFactorial`. If `simp` doesn't close, fall
back to manual:
```lean
show n * ((n - 0) * 1) = n * (n - 1)
ring
```

---

### Cluster K5: triple-destructure `LT.lt.le` direction (lines 1299–1306)

**Errors** (4 sites in `strict_eq_of_tripleSet_eq`):
```
1299:16 LT.lt.le hab' : (a',b',c').1 ≤ (a',b',c').2.1 (got) vs b' ≤ a' (expected)
1300:16 LT.lt.le hac' : a' ≤ c'                      (got) vs c' ≤ a' (expected)
1305:16 LT.lt.le hab  : (a, b, c).1 ≤ (a, b, c).2.1  (got) vs b ≤ a  (expected)
1306:16 LT.lt.le hac  : a ≤ c                       (got) vs c ≤ a  (expected)
```

**Diagnosis**: the source destructures `T : Fin n × Fin n × Fin n` as
`⟨a, b, c⟩` but the elaborator at v4.26.0 represents projections as
`(a, b, c).1` / `.2.1` / `.2.2` rather than the destructured names. The
direction of `≤` is also reversed at goal sites (`b ≤ a` vs `a ≤ b`), which
strongly suggests the proof previously used `le_antisymm` to derive `a = min`
in both directions but at v4.26.0 the inequalities are not auto-flipped.

**Fix** (+8 LOC, explicit projections + direction flip):
The proof structure (re-read from S15 Session 15) is:
```lean
-- derive a = min of tripleSet via le_antisymm
have h_a_min : (a, b, c).1 = (a', b', c').1 := by
  apply le_antisymm
  · exact ?_  -- a ≤ a': follows from a ∈ tripleSet ∧ a' ≤ a' (refl on min)
  · exact ?_  -- a' ≤ a: similar
```

The fix is to widen the destructure to expose `Prod.fst`/`Prod.snd`
projections, and reorder the `LT.lt.le` applications to match. Suggested:

```lean
-- replace LT.lt.le hab with hab.le (cleaner)
-- but ALSO check goal direction: if goal is b' ≤ a' (reversed),
-- use hab'.le.symm or .symm.le or rewrite goal direction first
```

**Risk**: medium. Requires reading the full `strict_eq_of_tripleSet_eq` proof
(L1273–1310 estimated). Cascade-resolves with K6 (same destructure issue
spilling into omega goals).

---

### Cluster K6: `omega` regression on let-projections (lines 1327, 1330)

**Errors**:
```
1327:34: omega could not prove the goal
1330:34: omega could not prove the goal
```

**Counterexample shape** (from build log):
```
variables d := ↑↑(a, b, c).2.1, e := ↑↑(a, b, c).1, f := ↑n,
          g := ↑↑(a, b, c).2.2, i := ↑↑(a', b', c').2.1, j := ↑↑(a', b', c').1, …
```

**Diagnosis**: `omega` at v4.26.0 no longer transparently decodes the
let-projections `(a, b, c).1`, `.2.1`, `.2.2` as separate atoms. The
constraints presented to `omega` include relations that depend on these being
equal to the destructured-variable forms.

**Fix** (+4 LOC, pre-`obtain`-destructure):
```lean
obtain ⟨a, b, c⟩ := T₁  -- explicit destructure, no .1/.2.1 projections
obtain ⟨a', b', c'⟩ := T₂
-- ... rest of proof, all references now use a, b, c, a', b', c' directly
omega
```

**Risk**: medium. The K5 + K6 cluster likely share root cause (same
let-destructure region). Apply K5+K6 together: convert `T₁ = (a, b, c)` and
`T₂ = (a', b', c')` to explicit `obtain` destructures at the top of the
proof body. Then `omega` and `le_antisymm` work cleanly.

---

### Cluster K7: `card_eq_sum_card_fiberwise` now expects `Set.MapsTo`

**Errors** (4 sites, in `overlapPattern_partitions_offDiag` and `tripleCount_descFact_2_eq_overlap_sum`):
```
1394:40: Application type mismatch: hF has type ∀ p ∈ s, … ∈ range 4
         but expected Set.MapsTo ?m.95 ↑?m.96 ↑?m.97
1428:40: same pattern
```

**Mathlib v4.26.0 signature** (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:971`):
```lean
theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M}
    (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b}
```

**Root cause**: at v4.25, the hypothesis was `∀ x ∈ s, f x ∈ t`. At v4.26.0
it's `Set.MapsTo`. Although `Set.MapsTo` definitionally unfolds to
`∀ ⦃x⦄, x ∈ s → f x ∈ t` (strict-implicit), the elaborator no longer
auto-coerces the `∀ p ∈ s, P p` form.

**Fix** (+4 LOC across 4 sites, change `hF` type annotation):
```lean
-- BEFORE
have hF : ∀ p ∈ s, … ∈ range 4 := …
exact card_eq_sum_card_fiberwise hF

-- AFTER
have hF : Set.MapsTo (fun p => …) (s : Set _) ((range 4 : Finset _) : Set _) := by
  intro p hp
  …
exact card_eq_sum_card_fiberwise hF
```

Or wrap inline:
```lean
exact card_eq_sum_card_fiberwise (fun p hp => hF p hp)
```

**Risk**: low. Standard v4.26.0 `Set.MapsTo` refactor; same fix pattern
applies to ~30 other Mathlib API call sites that were touched.

---

### Cluster K8: `card_sdiff` → `card_sdiff_of_subset` rename

**Errors** (2 sites):
```
767:13: Function expected at card_sdiff but type is #(_ \ _) = #_ - #(_ ∩ _)
1493:13: same pattern
```

**Mathlib v4.26.0 verification** (`Mathlib/Data/Finset/Card.lean`):
```lean
theorem card_sdiff_of_subset (h : s ⊆ t) : #(t \ s) = #t - #s        -- ← renamed!
theorem card_sdiff : #(t \ s) = #t - #(s ∩ t)                       -- ← unconditional, no h
```

**Root cause**: at v4.25, `Finset.card_sdiff (h : s ⊆ t) : …` took the subset
hypothesis. At v4.26.0, `Finset.card_sdiff` is unconditional with `∩` on the
RHS, and the old name moved to `Finset.card_sdiff_of_subset`.

**Source — L767** (in `bad_count_general` proof, `hcompl_card`):
```lean
rw [heq, Finset.card_sdiff (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, hpair_card]
```

**Fix** (+2 LOC, rename to `card_sdiff_of_subset`):
```lean
rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, hpair_card]
```

Same rename at L1493.

**Risk**: low. Direct API rename. The new `Finset.card_sdiff` (unconditional)
is also usable but requires adjusting the RHS arithmetic.

---

### Cluster K9: `orderEmbOfFin_unique` arg order shift

**Error** (L965):
```
965:40: Application type mismatch: hf_mem has type ∀ x, f x ∈ {i, j, k}
        but expected #?m.721 = ?m.722
```

**Mathlib v4.26.0 signature** (`Mathlib/Data/Finset/Sort.lean:267`):
```lean
theorem orderEmbOfFin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α}
    (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin h
```

**Source — L965**:
```lean
have h_unique : ∀ m : Fin 3,
    ({i, j, k} : Finset (Fin n)).orderEmbOfFin hcard m = f m := by
  intro m
  exact Finset.orderEmbOfFin_unique hf_mem hf_mono m
```

**Root cause**: at v4.25, args were `(hfs) (h) (hmono)` or implicit `h`.
At v4.26.0, `h : s.card = k` is the FIRST explicit arg. The current call
puts `hf_mem` in `h`'s slot, causing the type mismatch.

**Fix** (+1 LOC — re-order, add `hcard`):
```lean
exact (Finset.orderEmbOfFin_unique hcard hf_mem hf_mono).symm ▸ rfl
```

Or using named args:
```lean
have := (Finset.orderEmbOfFin_unique (h := hcard) hf_mem hf_mono : f = _)
exact (congr_fun (congr_arg DFunLike.coe this.symm) m).symm
```

Cleanest:
```lean
have h_eq := Finset.orderEmbOfFin_unique (h := hcard) hf_mem hf_mono
exact (congr_fun (congr_arg _ h_eq) m).symm
```

**Risk**: medium. The proof was returning `OrderEmbedding`-valued equality;
need to extract `m`-pointwise after the equality.

---

### Cluster K10: `Fin (Fintype.card (Fin d))` vs `Fin d` (L551–570)

**Errors**:
```
551:27: Type mismatch: f 0 has type Fin (Fintype.card (Fin d)) but expected Fin d
553:16: Type mismatch: v has type Fin d but expected Fin (Fintype.card (Fin d))
554:31: unsolved goals (cascade from above)
570:38: unsolved goals (cascade)
```

**Source — L547–558**:
```lean
rw [show d = Fintype.card (Fin d) from (Fintype.card_fin d).symm,
    ← Fintype.card_coe]
apply Fintype.card_congr
exact {
  toFun := fun ⟨f, _⟩ => f 0
  invFun := fun v => ⟨fun _ => v, …⟩
  …
}
```

**Diagnosis**: After `rw [show d = Fintype.card (Fin d) …, ← Fintype.card_coe]`,
the goal's codomain has switched from `Fin d → Fin d` to
`Fin 3 → Fin (Fintype.card (Fin d))`. The anonymous-constructor `Equiv`
expects the original `Fin d` type. At v4.25, Lean's elaborator unified
`Fintype.card (Fin d)` with `d` via `Fintype.card_fin`; at v4.26 it's strict.

**Fix** (+3 LOC, explicit `Fin (Fintype.card (Fin d))` annotation):
```lean
exact ({
  toFun := fun ⟨f, _⟩ => (f 0 : Fin (Fintype.card (Fin d)))
  invFun := fun (v : Fin (Fintype.card (Fin d))) => …
  …
} : ({f | f 0 = f 1 ∧ f 1 = f 2} : Set _) ≃ Fin (Fintype.card (Fin d)))
```

Alternative: don't rewrite `d = Fintype.card (Fin d)` first; do the bijection
in `Fin d` form, then apply `Fintype.card_fin` at the end.

**Risk**: medium. Recommend the alternative form (do the bijection in
`Fin d` directly and `card_fin` at the end) to keep the codomain stable.

---

### Cluster K11: "No goals to be solved" at L611 and L1838

**Errors**:
- L611:2: `No goals to be solved` (in `p_triple_n3` after K10-related)
- L1838:2: `No goals to be solved` (after the K12 hygiene leak)

**Diagnosis**: Both are tail-of-proof "ring" or "rfl" calls that ran after
the body had already been closed. Once upstream K2, K7, K8 fixes land, the
goal state at these tail tactics changes, and the now-redundant closer
becomes "No goals to be solved".

**Fix** (-2 LOC, delete redundant `ring` / `rfl`):
```lean
-- L611: delete trailing `ring`
-- L1838: delete trailing closer
```

**Risk**: low. Standard cascade fix; do AFTER all upstream fixes land.

---

### Cluster K12: bizarre `Nat.totient._@.Proofs.…_hyg.446` pattern variable

**Error** (L1834):
```
1834:6: Invalid pattern variable: Variable name must be atomic, but
`Nat.totient._@.Proofs.BirthdayProblemOQ03OQ01OQ02.1473014559._hygCtx._hyg.446`
has multiple components
```

**Source — L1834**:
```lean
let φ : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) →
        Σ _ : Finset (Fin n), Finset (Fin n) × Finset (Fin n) :=
  fun p => ⟨tripleSet p.1 ∪ tripleSet p.2, (tripleSet p.1, tripleSet p.2)⟩
```

**Diagnosis**: this is a Lean 4 hygiene-leak bug. The `_φ` name appears to
clash with a generated `Nat.totient` hygienic name (the hashed `1473014559`
is the hashed name of the file, the `_hyg.446` is the macro instance index).

This is most likely from an `obtain ⟨…⟩ := …` pattern somewhere AFTER L1834
where one of the destructured names is `tot` or `totient`, and Lean's hygiene
system collides it with `Nat.totient` due to a previously-imported
auto-derived instance.

**Fix** (requires read-through, ≥ 0 LOC delta):
1. Read L1834–L1900 (inside `card_overlapPattern_le_generic` proof body).
2. Find any `obtain ⟨…, tot, …⟩` or `let tot := …` and rename.
3. If no `tot`-named binding found, try renaming `φ` to a different identifier
   (`embed`, `fiberMap`, `unionPair`).
4. Or refactor: replace `let φ := fun p => …` with a top-level
   `private def overlapPattern_embed (p : (Fin n × Fin n × Fin n)²) := …` to
   bypass the inline hygiene scope.

**Risk**: high uncertainty. May resolve on its own once K2 (`filter_upwards`)
and K7 (`Set.MapsTo`) fixes land — the hygiene context is built from
elaboration order, and earlier errors may pollute later contexts.

---

### Cluster K13: `b₁`/`c₁`/`b₂`/`c₂` scope loss (L1580–1607)

**Errors**:
```
1580:25: Unknown identifier `b₁`
1589:32: Unknown identifier `c₁`
1598:34: Unknown identifier `b₂`
1607:36: Unknown identifier `c₂`
```

**Diagnosis**: similar to K5/K6, an `obtain ⟨a₁, b₁, c₁⟩ := T₁` destructure
at the top of `bad_count_disjoint_strict` no longer carries through to
later sub-blocks at v4.26.0 (likely due to a `case`/`subst` interaction).

**Fix** (+4 LOC, widen `obtain` or re-destructure inside each subgoal):
```lean
-- Option A: re-destructure at use sites
have hb₁ne : b₁ ≠ c₁ := …  -- where b₁, c₁ are newly destructured here
```

Or:
```lean
-- Option B: hoist the destructure to the top via `match` or `Prod.mk.injEq`
match T₁, T₂ with
| ⟨a₁, b₁, c₁⟩, ⟨a₂, b₂, c₂⟩ => …
```

**Risk**: medium. The current proof structure has destructures in multiple
sub-cases; reconciling them needs care.

---

### Cluster K14: cascade-resolving `unsolved goals` errors

**Errors** (likely cascade-resolve after upstream fixes):
- L554, 570 — from K10 type-mismatch
- L1193 — from K4 `descFactorial_two`
- L1384, 1414 — from K7 `card_eq_sum_card_fiberwise`

**Strategy**: do NOT manually fix these on first pass. After landing K1–K10,
re-run Docker build; expect ~5 errors to resolve automatically. Re-evaluate
any remaining residue with surgical 1–3 LOC fixes (likely adding
`simp only [...]` or `tauto` closers).

---

### Recommended fix order

1. **K1** (forward-ref reorder — pure cut/paste, 0 LOC delta)
2. **K4** (`Nat.descFactorial_two` derive inline, +4 LOC)
3. **K8** (`card_sdiff_of_subset` rename, +2 LOC)
4. **K9** (`orderEmbOfFin_unique` arg-order, +1 LOC)
5. **K2** (`∀ᶠ d : ℕ in atTop` annotations, +5 LOC)
6. **K7** (`Set.MapsTo` on `hF` predicates, +4 LOC)
7. **K3** (`subst → rw` for `hmj`/`hmk`, +6 LOC)
8. **K10** (Fin d type annotation, +3 LOC)
9. **K5+K6** (triple-destructure cluster, +12 LOC) — do as one block
10. **K13** (b₁/c₁/b₂/c₂ scope, +4 LOC)
11. **K12** (hygiene leak — read-through; may auto-resolve)
12. **K11** (delete dead `ring`/`rfl`, -2 LOC)
13. **K14** (cascade re-evaluation after Docker run)

**Total**: ~45 LOC of edits across 16 sites. Estimated 1–2 Docker iterations.

---

### Acceptance criteria for mechanic

1. **Build clean**: `./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ03OQ01OQ02` → 0 errors, builds in ≤ 60 min.
2. **Axiom count unchanged**: `grep -c "^axiom " proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` returns 1 (the `p_no_triple_tendsto` Lemma C axiom; unchanged from S16d ACT tip).
3. **Theorem-count delta**: ≤ +2 (allow K6/K13 to introduce small helper destructure lemmas; no math content changes).
4. **No new sorries**: `grep -c "sorry" proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` returns 0 (i.e. preserve all 43 numbered lemmas, do NOT demote bodies to `sorry`).
5. **JSON sync**: post-build, update `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json` with:
   - `currentState.phase: "BUILD-BLOCKER"` → `"ACT"`
   - `currentState.iteration: 22 → 23`
   - `currentState.focus`: refreshed with S18 mechanic-fix narrative
   - `lastUpdate`: ISO timestamp

---

### Risk notes (cross-cluster)

- **K2, K7 share an elaborator-strictness root**: v4.26.0's elaborator no
  longer auto-coerces between `∀ᶠ`/`Set.MapsTo` / `∀ p ∈ s` forms. Apply
  both at once.
- **K3, K5, K6, K13 share a destructure-scope root**: the cleanest fix may
  be a single refactor to use `obtain ⟨…⟩ := …` at the top of each affected
  block, avoiding `.1`/`.2` projections and `subst` direction issues
  throughout.
- **K12 (hygiene leak) may be a phantom**: it may disappear after K7
  (`Set.MapsTo`) fix changes the elaboration context. Re-evaluate AFTER K7.
- **K11 (No goals)**: only delete the tail tactics AFTER K2/K7/K8/K10
  upstream fixes land. The tail tactics may be discharging genuine goals in
  the broken state.

---

### Mathlib v4.26.0 API citations (verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| API | New location | Old location (v4.25) | Notes |
|---|---|---|---|
| `Finset.card_sdiff_of_subset` | `Data/Finset/Card.lean` | `Finset.card_sdiff` | Renamed: subset hyp version now `_of_subset` |
| `Finset.card_sdiff` | `Data/Finset/Card.lean` | — | NEW: unconditional, RHS uses `_ ∩ _` |
| `Finset.card_eq_sum_card_fiberwise` | `Algebra/BigOperators/Group/Finset/Basic.lean:971` | same | Hyp type `Set.MapsTo`, not `∀ p ∈ s, …` |
| `Nat.descFactorial_two` | — | `Data/Nat/Factorial/Basic.lean` (gone) | REMOVED; use `simp [Nat.descFactorial]` |
| `Nat.cast_descFactorial_two` | `Data/Nat/Factorial/Cast.lean` | same | Available for ℝ-cast form |
| `Finset.orderEmbOfFin_unique` | `Data/Finset/Sort.lean:267` | same | Arg order: `(h : s.card = k) (hfs) (hmono)` |
| `Finset.subset_union_left/right` | `Order/Lattice/Basic.lean` | same | Unchanged |
| `Finset.card_offDiag` | `Data/Finset/Card.lean` | same | Unchanged |
| `Filter.eventually_ne_atTop` | `Topology/Order/AtTopBot/Defs.lean` | same | Unchanged but `∀ᶠ d in atTop` annotation now strict |

---

### Net deliverable (this session, doc-only)

1. This file (`s18-mechanic-kit-prep.md`): 9-cluster (K1–K14) fix plan, +~45 LOC mechanic-ready edits, ~250 lines doc
2. `state.md` S18 entry
3. JSON `lastUpdate` + cursor refresh (separate PR, optional this session)

Zero Lean changes. Zero JSON metric-field changes. Branch:
`research/birthday-s18-mechanic-kit-prep-<unix>` off `origin/main`.
