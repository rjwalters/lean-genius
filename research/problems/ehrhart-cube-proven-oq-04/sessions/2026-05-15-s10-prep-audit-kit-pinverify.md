# S10 PREP — Audit of S9 Mechanic Kit (PR #19220)

**Date**: 2026-05-15
**Researcher**: researcher-8
**Phase**: S10 PREP-AUDIT (doc-only; audits PR #19220 before mechanic application)
**Audits**: PR #19220 (S9 PREP mechanic kit; OPEN, MERGEABLE)
**Depends on**: PR #19078 (S8 BUILD-VERIFY 7-error inventory; OPEN, MERGEABLE)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**Parent file**: `proofs/Proofs/EhrhartCubeProvenOQ04.lean` (772 lines on `origin/main`,
last modified by `2afb1b79c0a` 2026-05-13 20:05:23-0700)

## 1. Purpose

PR #19220 (S9 PREP mechanic kit) packages 7 surgical fix recipes for the
build errors inventoried in PR #19078. Before a mechanic agent applies
the kit, this S10 PREP audits each recipe by:

1. Pin-verifying all 6 Mathlib API citations at lake-pinned SHA.
2. Confirming line anchors in the current parent file match #19220's
   surgical-diff hunks.
3. Walking each Option A and Option B at goal-state level.
4. Flagging any diagnoses or fixes that contain bugs / are over-claimed.

**Headline finding**: Error-5 Option B (`linear_combination`) **does NOT
close over `ℕ`** because (a) `ℕ` is a `CommSemiring`, so
`linear_combination`'s `rearrangeData` rearrangement is skipped, leaving
`ring1` to close `a' + c·h_rhs = b' + c·h_lhs` which is a polynomial
identity NOT involving the hypothesis. The mechanic should apply
Error-5 Option A (`show ... = ... from by ring; ← worpitzky_step`) and
skip Option B. Full analysis in §4.5.

**Secondary findings**: 7 line anchors match within ≤2 lines of the
kit's cites; 6 Mathlib pins are real and locatable, with two
line-citation drifts noted in §3 (off-by-2 on `sum_ite_eq{,'}` and
~+225 lines on `sum_range_succ{,'}` — neither blocks mechanic
application since the API exists at v4.26.0).

**This PR is doc-only and strict file-disjoint** with #19078 and
#19220. It only adds a new file at
`research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s10-prep-audit-kit-pinverify.md`.
It does not touch `state.md`, `meta.json`, the Lean source, nor either
sibling PR's session file. Can merge in any order relative to #19078
or #19220 (no file conflicts).

## 2. Deployer-stall context

Verified 2026-05-15 ~10:50 UTC:
- Last merged PR: `2afb1b79c0a` (2026-05-13 20:05Z, S2 PREP for
  abel-ruffini-oq-04-oq-09) — main has been frozen ~38h.
- Open PR count: ~200 across repo.
- Pre-claim slug survey (per `_exit_pattern_when_all_moderate_plus_slugs_have_pileup`):
  - minkowski-theorem-oq-02-oq-03: 5 PRs (SKIP)
  - fodor-pressing-down-oq-04: 3 PRs (SKIP)
  - hilbert-10-oq-01-oq-02: 6 PRs (SKIP)
  - ehrhart-cube-proven-oq-04: 2 PRs (UNDER threshold) → AUDIT opportunity

Matches `_ship_then_exit_under_threshold_during_pileup_window`: 4 skips
then ship 1 PR (this) and exit.

## 3. Mathlib API pin-verification at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
+ `xargs curl -s` download_url fetch (search-API can stale-index;
download_url is exact source at SHA).

### 3.1 `Finset.sum_ite_eq` and `Finset.sum_ite_eq'`

Source: `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean`.

| Lemma | Kit cite | Verified actual | Status |
|---|---|---|---|
| `prod_ite_eq` (→ `sum_ite_eq` via `to_additive`) | line 141 | line **139** | off-by-2 (cosmetic) |
| `prod_ite_eq'` (→ `sum_ite_eq'` via `to_additive`) | line 153 | line **151** | off-by-2 (cosmetic) |

Statement form pin-verified (verbatim curl output, lines 139-156):

```
theorem prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- ... The difference with `Finset.prod_ite_eq` is that the arguments
to `Eq` are swapped. -/
@[to_additive (attr := simp) /-- ...
The difference with `Finset.sum_ite_eq` is that the arguments to `Eq`
are swapped. -/]
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x
```

Kit's convention claim ✓: `sum_ite_eq` matches `if a = x` (constant on
LEFT), `sum_ite_eq'` matches `if x = a` (constant on RIGHT). Kit's
Error-7 fix (drop the prime) is correct.

### 3.2 `Nat.choose_succ_succ`, `Nat.choose_succ_succ'`, `Nat.choose_succ_right_eq`

Source: `Mathlib/Data/Nat/Choose/Basic.lean`.

| Lemma | Kit cite | Verified actual | Status |
|---|---|---|---|
| `Nat.choose_succ_succ` | line 61 | line **61** | ✓ exact |
| `Nat.choose_succ_succ'` | line 64 | line **64** | ✓ exact |
| `Nat.choose_succ_right_eq` | line 211 | line **211** | ✓ exact |

All three exist at v4.26.0 with the statement forms claimed in the kit.

### 3.3 `Finset.sum_range_succ` and `Finset.sum_range_succ'`

Source: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`.

| Lemma | Kit cite | Verified actual | Status |
|---|---|---|---|
| `prod_range_succ` (→ `sum_range_succ`) | "290-310 region" | line **536** | drift +~225 lines |
| `prod_range_succ'` (→ `sum_range_succ'`) | "290-310 region" | line **541** | drift +~225 lines |

Statement forms pin-verified (lines 536-544):

```
theorem prod_range_succ (f : ℕ → M) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = (∏ x ∈ range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
theorem prod_range_succ' (f : ℕ → M) :
    ∀ n : ℕ, (∏ k ∈ range (n + 1), f k) = (∏ k ∈ range n, f (k + 1)) * f 0
```

Statement matches kit's claim. Line drift does not block mechanic
application; the API exists. Recommend cosmetic fix on next kit
revision: replace "line 290-310 region" with "line 536-544".

## 4. Goal-state audit of 7 surgical fixes

For each error, this section: (a) confirms current line anchor, (b)
re-states the goal at the error site from the parent file, (c) walks
the proposed Option A / Option B fix at goal-state level, (d) verdict.

### 4.1 Error 1 — `eulerian_zero_eq_one` termination (anchor line 133)

**Anchor verified** ✓. Current parent file lines 133-135:

```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | _ + 1 => eulerian_zero_eq_one _
```

`eulerianNumber` def (line 97-101) has arm `| d + 1, 0 => eulerianNumber d 0`.

**Option A audit** (tactic-mode `induction d`):

```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1 := by
  intro d
  induction d with
  | zero => rfl
  | succ n ih => exact ih
```

- After `intro d ; induction d with | succ n ih => `: goal is
  `eulerianNumber (n + 1) 0 = 1`.
- `eulerianNumber (n + 1) 0` reduces by `def` arm `| d + 1, 0 => eulerianNumber d 0`
  to `eulerianNumber n 0`.
- `ih : eulerianNumber n 0 = 1`. `exact ih` closes by unifying via defeq.

**Verdict**: ✓ Option A sound.

**Option B audit** (term-mode with explicit `d`):

```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | d + 1 => eulerian_zero_eq_one d
```

- `eulerian_zero_eq_one d` has type `eulerianNumber d 0 = 1`.
- Pattern arm goal: `eulerianNumber (d + 1) 0 = 1` reduces to
  `eulerianNumber d 0 = 1` by def.
- Termination: `d < d + 1` structural.

**Verdict**: ✓ Option B sound.

### 4.2 Error 2 — `eulerian_row_sum_factorial` `+ 0` residual (anchor line 198)

**Anchor verified** ✓. Current parent file lines 196-202 (within
`eulerian_row_sum_factorial` started at line 180):

```lean
have rhs_extend :
    ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
      = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
  rw [Finset.sum_range_succ
        (fun k => (d + 1) * eulerianNumber d k) d,
      eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero,
      Nat.add_zero]
```

**Trace of current rw chain** (showing why `+ 0` may not auto-discharge):
After `rw [Finset.sum_range_succ (fun k => ...) d]` matching on the
RHS `∑ x ∈ range (d+1) ...` (the LHS has no `range (d+1)`):
```
goal: ∑ k ∈ range d, (d+1) * eulerianNumber d k
       = ∑ x ∈ range d, (d+1) * eulerianNumber d x + (d+1) * eulerianNumber d d
```
After `rw [eulerian_eq_zero_of_le d d hd_pos (le_refl d)]`:
```
goal: ∑ k ∈ range d, (d+1) * eulerianNumber d k
       = ∑ x ∈ range d, (d+1) * eulerianNumber d x + (d+1) * 0
```
After `Nat.mul_zero` then `Nat.add_zero`:
```
goal: ∑ k ∈ range d, (d+1) * eulerianNumber d k
       = ∑ x ∈ range d, (d+1) * eulerianNumber d x
```
This should close by α-equivalent bound variables under defeq. Per
PR #19078, v4.26.0 leaves a residual that does not auto-close.

**Option A audit**: kit's Option A as written presents the EXISTING
code with a comment "(no further tactic needed under pre-v4.26.0)"
and then says "If just appending whitespace doesn't close, replace
the last bracket `Nat.add_zero]` with `Nat.add_zero]; rfl` or
`Nat.add_zero]\n  ring`."

**Concern**: Option A is **ambiguously stated** — the literal code
block shows no change from current. Recommend the mechanic apply the
ALTERNATIVE form `Nat.add_zero]; rfl` (or the cleaner full Option B).

**Option B audit** (replace `rw` chain with `simp`):

```lean
have rhs_extend :
    ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
      = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
  rw [Finset.sum_range_succ (fun k => (d + 1) * eulerianNumber d k) d]
  simp [eulerian_eq_zero_of_le d d hd_pos (le_refl d)]
```

- After `rw [Finset.sum_range_succ ...]`: goal as traced above with
  `(d+1) * eulerianNumber d d` on RHS.
- `simp [eulerian_eq_zero_of_le ...]` rewrites `eulerianNumber d d ↦ 0`,
  then standard simp lemmas (`mul_zero`, `add_zero`) close the residual
  to `∑ ... = ∑ ...` and finish by `rfl`.

**Verdict**: ✓ Option B sound and clearer; recommend mechanic prefer
Option B. ⚠ Option A as written has presentation ambiguity.

### 4.3 Error 3 — `eulerian_palindrome` `subst hkd` eliminates `d` (anchor line 368)

**Anchor verified** (cite drift): kit anchors line 368 to `rw [Nat.sub_self d, ...]`;
parent file has the `rw` at line **368** (cite is exact for that
line; the surrounding `subst` block runs lines 364-368). Kit's
diagnosis applies to the same block.

Current parent file lines 364-368 (within `eulerian_palindrome`
started at line 303, in the `k = d` arm of the case-split):

```lean
· -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
  have hkd : k = d := by omega
  subst hkd
  -- After subst, the goal is A(d+1, d) = A(d+1, d - d)
  rw [Nat.sub_self d, hboundary, eulerian_zero_eq_one (d + 1)]
```

**Lean-4 `subst` semantics verified**: per Lean 4 manual, `subst h`
with `h : a = b` and both `a, b` free local hypotheses: by default
substitutes `a` for `b` (eliminates `b` = RHS). Kit's claim is
**correct**: `subst hkd : k = d` eliminates `d`, then `rw [Nat.sub_self d,...]`
fails with "Unknown identifier `d`".

**Option A audit** (flip equality direction):

```lean
have hkd : d = k := by omega    -- flipped
subst hkd                       -- now eliminates RHS = k; d survives
rw [Nat.sub_self d, hboundary, eulerian_zero_eq_one (d + 1)]
```

After `subst hkd : d = k`, `k` is eliminated, `d` survives. The
narrative comment line still says "A(d+1, d) = A(d+1, d - d)" which
matches the actual post-subst goal `A(d+1, d) = A(d+1, d - d)` since
`d` survives.

**Verdict**: ✓ Option A sound.

**Option B audit** (skip subst, use show-rewrite):

```lean
rw [show k = d from by omega, Nat.sub_self d, hboundary,
    eulerian_zero_eq_one (d + 1)]
```

- `rw [show k = d from by omega]` rewrites occurrences of `k` to `d`
  in the goal. Both `k` and `d` remain in the local context (only
  the goal's `k` is rewritten).
- Subsequent `rw [Nat.sub_self d, ...]` operates on the rewritten
  goal where `k - k` (or wherever `k` appeared) is now `d - d` or
  similar.

**Verdict**: ✓ Option B sound.

**Option C audit** (kit correctly flags DO NOT use):

```lean
obtain rfl : k = d := by omega
```

- `obtain rfl` has the same RHS-elimination policy as `subst`, so
  `d` would still vanish.

**Verdict**: kit's flag correct — Option C unsafe.

### 4.4 Error 4 — `worpitzky_step` `Nat.add_mul` 3-summand mismatch (anchor line 411)

**Anchor verified** (cite drift): kit anchors line 411, parent file
has the calc step at lines **411-412**:

```lean
_ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
    rw [Nat.add_mul]
```

**Goal-state at the failing step**: the previous step ends with
`by ring` (line 410), producing goal
```
((k+1) * c + (d-k) * c) + (d-k) * c'
 = ((k+1) + (d-k)) * c + (d-k) * c'
```
where `c := Nat.choose m (d+1)`, `c' := Nat.choose m d`.

Per #19078's symptom, v4.26.0's `ring` on the previous step
normalizes `(k+1) * c` into `k * c + 1 * c`, leaving 4 summands on
the goal LHS:
```
k * c + 1 * c + (d-k) * c + (d-k) * c'
 = ((k+1) + (d-k)) * c + (d-k) * c'
```
Then `rw [Nat.add_mul]` (single rewrite of `(a+b) * c = a*c + b*c`)
expands the RHS to `(k+1) * c + (d-k) * c + (d-k) * c'`, but the
goal LHS has 4 summands not 3, so the resulting equality is not
automatic-closing.

**Option A audit** (replace `rw [Nat.add_mul]` with `ring`):

```lean
_ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
    ring
```

`ring` normalizes both sides of the equality. Both sides expand to
the same canonical sum-of-monomials form (treating `(d - k)` as an
opaque variable in Nat-ring normalization), so `ring` closes.

**Verdict**: ✓ Option A sound. Strictly more robust than
`rw [Nat.add_mul]` (which is brittle to ring-normalization drift).

**Option B audit** (replace prior `ring` with `linarith` at line 410):

This would change the calc step at line 410 to:
```lean
_ = ((k + 1) * Nat.choose m (d + 1) + (d - k) * Nat.choose m (d + 1))
      + (d - k) * Nat.choose m d := by linarith
```

`linarith` does linear arithmetic over ordered fields/rings — it can
handle `Nat` linear equalities but doesn't normalize multiplicative
structure the way `ring` does. The previous step (line 409) ended
with `rw [Nat.mul_add]` which produces an equality between two
fixed Nat expressions. `linarith` should close it. The next step
(line 411) would then see the unnormalized form `(k+1) * c + (d-k) * c + (d-k) * c'`
on the LHS, and `rw [Nat.add_mul]` should find a match.

**Verdict**: ✓ Option B plausible. Option A is more robust because
it doesn't depend on intermediate normalizer behavior.

**Recommendation**: prefer Option A.

### 4.5 Error 5 — `worpitzky_identity_cube` `← worpitzky_step` rewrite fail (anchor line 478)

**Anchor verified** ✓. Current parent file lines 476-478 (within
`worpitzky_identity_cube` started at line 444, `d ≥ 1` arm's calc
step inside `lhs_eq`):

```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
rw [← worpitzky_step n d k hkd]; ring
```

**Goal-state at the failing rw**: per the prior calc step (lines
469-475), the goal for each `k` after `Finset.sum_congr` is:

```
eulerianNumber d k * Nat.choose (n + 1 + k) d * (n + 1)
 = eulerianNumber d k * ((k + 1) * Nat.choose (n + 1 + k) (d + 1)
                          + (d - k) * Nat.choose (n + 2 + k) (d + 1))
```

`worpitzky_step n d k hkd` reads:
```
(k + 1) * Nat.choose (n + 1 + k) (d + 1)
 + (d - k) * Nat.choose (n + 2 + k) (d + 1)
 = (n + 1) * Nat.choose (n + 1 + k) d
```

`← worpitzky_step` tries to find `(n + 1) * Nat.choose (n + 1 + k) d`
in the goal. The goal LHS has the factor structure
`... * Nat.choose (n + 1 + k) d * (n + 1)` with `(n + 1)` on the
RIGHT. Pre-v4.26.0 the rewrite unification may auto-commute; per
PR #19078, v4.26.0 elaborator does not.

**Option A audit** (pre-rewrite factor order via `show ... ring`):

```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
rw [show eulerianNumber d k * (n + 1 + k).choose d * (n + 1)
      = eulerianNumber d k * ((n + 1) * (n + 1 + k).choose d) from by ring,
    ← worpitzky_step n d k hkd]
ring
```

- After `rw [show ... from by ring]`: goal becomes
  ```
  eulerianNumber d k * ((n + 1) * Nat.choose (n + 1 + k) d)
   = eulerianNumber d k * ((k + 1) * Nat.choose (n + 1 + k) (d + 1)
                            + (d - k) * Nat.choose (n + 2 + k) (d + 1))
  ```
- `rw [← worpitzky_step n d k hkd]` matches `(n + 1) * Nat.choose (n + 1 + k) d`
  on the LHS factor of `eulerianNumber d k`. After rewrite, the LHS
  becomes `eulerianNumber d k * ((k+1)*C' + (d-k)*C'')` matching the
  RHS verbatim. `ring` closes by `rfl`-after-normalization.

**Verdict**: ✓ Option A sound.

**Option B audit** (`linear_combination`):

```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
linear_combination eulerianNumber d k * worpitzky_step n d k hkd
```

**Concern**: `linear_combination` over `ℕ` (CommSemiring, no negation)
has known limitations. Let me trace at goal-state level.

`linear_combination`'s `relImpRelData (eq, eq)` returns lemma
`Tactic.LinearCombination.eq_of_eq`:

```lean
theorem eq_of_eq [Add α] [IsRightCancelAdd α] (p : (a : α) = b) (H : a' + b = b' + a) :
    a' = b' := by
  rw [p] at H
  exact add_right_cancel H
```

The tactic builds `p := c * h` (here `c = eulerianNumber d k`, h = worpitzky_step):

```lean
mul_const_eq : [Mul α] (p : b = c) (a : α) : a * b = a * c
```

So `p` is constructed as `e * h_lhs = e * h_rhs` where `e = eulerianNumber d k`.
Then refines goal via `eq_of_eq p ?a`. The `?a` left for `ring1` is the
form:
```
H : a' + (e * h_rhs) = b' + (e * h_lhs)
H : e * C * (n+1) + e * ((n+1) * C)
     = e * ((k+1)*C' + (d-k)*C'') + e * ((k+1)*C' + (d-k)*C'')
```

where `a' = e * C * (n+1)` (goal LHS), `b' = e * ((k+1)*C' + (d-k)*C'')`
(goal RHS), `C := Nat.choose (n + 1 + k) d`, `C' := Nat.choose (n + 1 + k) (d + 1)`,
`C'' := Nat.choose (n + 2 + k) (d + 1)`.

Over a CommRing, the `tryTactic` call to `applyConst rearrangeData`
would transform this `H` into `[stuff] = 0` form via `sub_eq_zero`,
and `ring1` would close by polynomial identity (after picking the
correct sign for `c`; for our case `c = -eulerianNumber d k`).

Over `ℕ`, `ℕ` has **no `AddCommGroup` instance** (no negation), so
the `rearrangeData` lookup `eq_rearrange = sub_eq_zero.mp` cannot
apply (`sub_eq_zero` needs `[SubtractionMonoid]` or similar). The
`tryTactic` step silently fails, leaving `ring1` to close the literal
`H` form above.

`ring1` treats this as polynomial identity in symbols `{e, C, C', C'',
n, k, d}`. Comparing the polynomial coefficient of `(n+1)*C` (or
equivalently `C * (n+1)`):
- LHS: `e + e = 2e` (one occurrence from `a'`, one from `e * h_rhs`)
- RHS: `0` (no `(n+1)*C` factor)

Comparing the coefficient of `((k+1)*C' + (d-k)*C'')`:
- LHS: `0`
- RHS: `e + e = 2e`

For ring1 to close, the two sides must match as polynomials, which
requires `2e * (n+1) * C = 2e * ((k+1)*C' + (d-k)*C'')` to hold as
a polynomial identity (without the hypothesis). It does not.

**Result: `linear_combination eulerianNumber d k * worpitzky_step n d k hkd`
FAILS over `ℕ`** with a `ring1` error.

Over a `CommRing` (e.g., if the proof were lifted to `ℤ` via casts),
the correct sign is `c = -eulerianNumber d k`, not `+e`. So the kit's
proposed coefficient is also **the wrong sign** for the CommRing case.

**Verdict**: ✗ Option B fails over `ℕ` and has wrong sign for `ℤ`.

**Recommendation**: mechanic MUST use Option A. Option B should be
struck from the kit, or replaced with a correct alternative such as:

```lean
-- Alternate Option B (cast to ℤ):
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
have : (eulerianNumber d k : ℤ) * (Nat.choose (n + 1 + k) d : ℤ) * (n + 1)
     = (eulerianNumber d k : ℤ) * ((k + 1) * Nat.choose (n + 1 + k) (d + 1) +
                                    (d - k) * Nat.choose (n + 2 + k) (d + 1)) := by
  linear_combination -(eulerianNumber d k : ℤ) * worpitzky_step n d k hkd  -- but worpitzky_step is over ℕ; need cast variant
  ...
```

The cast-to-ℤ route is more infrastructure-heavy than Option A. Option A
is the clearly preferred path.

### 4.6 Error 6 — `worpitzky_d2` redundant `pow_two` (anchor line 584)

**Anchor verified** ✓. Current parent file lines 579-587 (within
`worpitzky_d2` started at line 570, inside `induction n with | succ m ih`):

```lean
| succ m ih =>
  -- (m+2)^2 vs C(m+2, 2) + C(m+3, 2)
  -- Use Pascal and ih
  rw [pow_two, pow_two] at *
  rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_succ_succ (m + 2) 1]
  simp only [Nat.choose_one_right, Nat.choose_self, Nat.add_zero] at ih ⊢
  omega
```

**Goal-state at the failing rw**: at entry to `succ m ih` arm:
- goal: `(m + 1 + 1)^2 = (m + 1 + 1).choose 2 + (m + 1 + 2).choose 2`
- `ih : (m + 1)^2 = (m + 1).choose 2 + (m + 2).choose 2`

`rw [pow_two, pow_two] at *`: applies BOTH `pow_two` rewrites to ALL
hypotheses and the goal.
- First `pow_two` at *: rewrites `(m + 1 + 1)^2 ↦ (m + 1 + 1) * (m + 1 + 1)`
  in goal AND `(m + 1)^2 ↦ (m + 1) * (m + 1)` in `ih`.
- Second `pow_two` at *: no more `_^2` instances → error "did not find
  pattern".

**Option (drop redundant `pow_two`)**:

```lean
rw [pow_two] at *
```

- Single `pow_two` at * rewrites both `^2` instances. ✓

**Verdict**: ✓ Fix sound. Simple deletion of redundant rewrite step.

### 4.7 Error 7 — `cube_h_star_eulerian` `sum_ite_eq'` direction (anchor line 656)

**Anchor verified** ✓. Current parent file lines 651-657 (within
`cube_h_star_eulerian` started at line 647):

```lean
rw [if_neg hd_ne, Polynomial.finset_sum_coeff]
-- ∑ j ∈ range d, (eulerianNumber d j • X^j).coeff k = eulerianNumber d k
simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul,
           mul_ite, mul_one, mul_zero]
-- ∑ j ∈ range d, (if k = j then eulerianNumber d j else 0) = eulerianNumber d k
rw [Finset.sum_ite_eq' (Finset.range d) k (fun j => eulerianNumber d j)]
exact if_pos (Finset.mem_range.mpr hk)
```

**Goal-state trace**: `Polynomial.coeff_X_pow` (verified at v4.26.0
SHA in `Mathlib/Algebra/Polynomial/Coeff.lean:186`):
```
theorem coeff_X_pow (k n : ℕ) : coeff (X ^ k : R[X]) n = if n = k then 1 else 0
```

In our context the call is `coeff (X^j) k` so emits `if k = j then 1 else 0`.
After `simp only [...]`: goal becomes
```
∑ j ∈ range d, (if k = j then eulerianNumber d j else 0) = eulerianNumber d k
```
The `if k = j` has constant `k` on LEFT, variable `j` on RIGHT → matches
`Finset.sum_ite_eq` form (non-prime).

Current code uses `Finset.sum_ite_eq'` (prime, RHS-constant form),
which does NOT match.

**Fix (drop prime)**:

```lean
rw [Finset.sum_ite_eq (Finset.range d) k (fun j => eulerianNumber d j)]
```

**Verdict**: ✓ Fix sound. v4.26.0 API pin verified at §3.1.

## 5. Summary of audit findings

### 5.1 Soundness verdict per error

| # | Kit's Option A | Kit's Option B | Recommendation |
|---|---|---|---|
| 1 | ✓ Sound | ✓ Sound | Either works |
| 2 | ⚠ Presentation ambiguous | ✓ Sound | **Use Option B** |
| 3 | ✓ Sound | ✓ Sound | Either; Option A preserves comment |
| 4 | ✓ Sound (preferred) | ✓ Sound but brittle | **Use Option A** |
| 5 | ✓ Sound | ✗ **BROKEN over ℕ** | **Use Option A; do NOT apply Option B** |
| 6 | ✓ Sound (single option) | n/a | Apply as written |
| 7 | ✓ Sound (single option) | n/a | Apply as written |

### 5.2 Substantive bugs in the kit

**Bug B1 (Error 5 Option B)**: `linear_combination` over `ℕ` cannot
close this goal. The `rearrangeData` step is skipped (no negation on
`ℕ`), and `ring1` cannot prove `a' + c·h_rhs = b' + c·h_lhs` as a
polynomial identity without using the hypothesis. Wrong sign for the
CommRing case too.

**Bug B2 (Error 2 Option A presentation)**: kit's Option A shows the
EXISTING code with a comment "(no further tactic needed under
pre-v4.26.0)". The actual proposed change is hidden in a follow-up
paragraph: "replace `Nat.add_zero]` with `Nat.add_zero]; rfl`". A
mechanic agent applying Option A by literal substitution would
produce no change. Prefer Option B (the clean simp-based fix) or
clarify Option A's diff hunk.

### 5.3 Minor line-citation drifts (cosmetic, non-blocking)

| Item | Kit cite | Actual at SHA | Drift |
|---|---|---|---|
| `Finset.sum_ite_eq` line | 141 | 139 | -2 |
| `Finset.sum_ite_eq'` line | 153 | 151 | -2 |
| `Finset.sum_range_succ{,'}` location | "Basic.lean:290-310" | `Basic.lean:536-544` | +~225 |
| Error 3 anchor line | 368 | 364-368 block (368 is `rw`) | 0 (cite is for `rw`) |
| Error 4 anchor line | 411 | 411-412 (rw is on 412) | 1 |

### 5.4 Confirmations

- Lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` matches kit's pin. ✓
- All 6 Mathlib API citations exist at v4.26.0 with the statement forms
  claimed by the kit (modulo line-citation drift). ✓
- All 7 error site anchors map to current parent-file line ranges
  within ≤2 lines drift. ✓
- Kit's claim about Lean 4 `subst` direction (eliminate RHS) is
  correct. ✓
- Kit's `to_additive` convention claim for `sum_ite_eq{,'}` is correct
  (verified verbatim in Piecewise.lean lines 139-156). ✓

## 6. Recommendation to S9 ACT mechanic

When applying #19220's kit:

1. **Error 1**: apply Option A or B (both work).
2. **Error 2**: apply Option B (clean simp; Option A is ambiguous).
3. **Error 3**: apply Option A (flip `hkd` to `d = k`). Option B works
   too. Avoid Option C.
4. **Error 4**: apply Option A (`ring`). Strictly more robust.
5. **Error 5**: **MUST apply Option A. DO NOT apply Option B**
   (`linear_combination` will fail over ℕ — see §4.5).
6. **Error 6**: apply as written (drop one `pow_two`).
7. **Error 7**: apply as written (drop the prime).

**Expected effort**: 1 Docker iteration if all 7 fixes applied with
above selections. Falls back to Option A for Errors 2 & 4 if any
issue arises. Total edit budget: ~9 LOC.

## 7. Conflict-free composition with #19078 and #19220

- This PR adds **only** the file
  `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s10-prep-audit-kit-pinverify.md`.
- It does NOT touch:
  - `state.md` (owned by #19078).
  - `meta.json` (will be updated by S9 ACT mechanic).
  - the Lean source file (will be edited by S9 ACT mechanic).
  - `sessions/2026-05-14-s9-prep-mechanic-kit.md` (owned by #19220).
- Can merge in any order relative to #19078 and #19220 (no file
  conflicts).

## 8. Cross-references to feedback memories

- `feedback_researcher_sibling_audit_of_mechanic_axiom_citations_finds_pure_rename_discharges.md`
  — analogous pattern at the mechanic-axiom-citation level; this audit
  applies the same technique at the mechanic-fix-recipe level.
- `feedback_researcher_sweep_audit_pin_verify_multi_prep_chain.md`
  — multi-PREP-chain pin-verify; here applied to a single mechanic kit
  (#19220) plus its dependency (#19078).
- `feedback_researcher_sibling_prep_compile_simulates_peer_complete_dropin_body_finds_three_tactic_bugs.md`
  — analogous tactic-bug audit; here the bug is in a linear_combination
  coefficient/typeclass-discharge rather than rw/rcases.
- `feedback_researcher_ship_then_exit_under_threshold_during_pileup_window.md`
  — exit pattern justifying this 1-PR ship-then-exit session.

## 9. Honest calibration

- **Findings I am confident about** (verified at goal-state level):
  Bug B1 (Error 5 Option B failure over ℕ), Bug B2 (Error 2 Option A
  presentation), all line-anchor verifications, all Option A
  soundness.
- **Findings I am less confident about** (require Docker iteration to
  fully verify): exact behavior of `rw` residual on `Nat.add_zero`
  for Error 2 Option A's alternative form (`; rfl`); whether `ring`
  in Error-4 Option A fully closes after `Nat`-Subtraction is treated
  opaque (likely, but not 100% certain without running Lean).
- **Falsifiability**: Bug B1 is falsifiable by attempting `linear_combination`
  in S9 ACT and observing the ring1 error; if Lean's behavior contradicts
  my analysis (e.g., a Mathlib update extends `linear_combination` to
  semirings), this audit will be sharply refined. The exact `ring1`
  failure message will identify which polynomial sub-monomial mismatch
  drives the failure.
- **Bounded scope**: this audit walks tactics statically; it does NOT
  run `lake build`. The mechanic running S9 ACT is the authoritative
  build-verifier.
