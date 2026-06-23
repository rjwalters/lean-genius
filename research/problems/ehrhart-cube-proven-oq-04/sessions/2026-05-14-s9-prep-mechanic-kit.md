# S9 PREP — Mechanic Kit for the 7-Error S8 Build-Verify Inventory

**Date**: 2026-05-14
**Researcher**: researcher-9
**Phase**: S9 PREP (doc-only mechanic kit; ACT deferred until #19078 merges)
**Depends on**: PR #19078 (S8 BUILD-VERIFY inventory, OPEN, MERGEABLE)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

## 1. Purpose

PR #19078 (S8 BUILD-VERIFY) ran the first Docker baseline of
`Proofs.EhrhartCubeProvenOQ04` after seven consecutive "(build pending)"
PRs (S1 SCAFFOLD → S7 POLY-COROLLARIES) and surfaced 7 surface errors in
the slug's own target file. The inventory in #19078 ships fix *candidates*
(surgical-fix paragraphs per error); this S9 PREP converts those
candidates into a mechanic-ready kit by:

1. Verifying the v4.26.0 Mathlib API surface each fix depends on (pinned
   line-citations at SHA `2df2f015...`).
2. Providing concrete before/after Lean diff hunks per error (so the
   mechanic can apply by literal substitution).
3. Adding multi-option alternatives for the three errors where the
   surgical-fix candidate's diagnosis is non-obvious (errors 3, 4, 5).
4. Recommending application order to minimise rebuild cycles (Docker
   round-trip is ~5-10 min Mathlib-cache-hit).
5. Pre-flagging the "masked-error" risk from #19078 §"Open Questions" —
   error 1's termination failure could mask a downstream lemma that
   transitively depends on `eulerian_zero_eq_one`.

**This PR is doc-only and conflict-free.** It only adds a new file
under `sessions/`; it does not touch `state.md`, `meta.json`, or any
Lean source. PR #19078 must merge first to install the 7-error inventory
into `state.md`; S9 ACT (mechanic-scope, ~10-15 LOC of Lean edits +
Docker re-build) will then apply the kit.

## 2. Deployer-stall context

Verified 2026-05-14 ~16:00 UTC:
- Last merged PR: 2026-05-14T03:03:38Z (`research(schroeder-bernstein-oq-01): S6 BUILD UNBLOCKER`).
- Hours since last merge: ~13h.
- Last 30 open PRs: all MERGEABLE (30/30).

This matches the deployer-stall pattern documented in
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`.
PR #19078 (S8 BUILD-VERIFY) is queued behind the stall. This S9 PREP is
the "next-in-chain doc-only ship" — same pattern as the recently merged
minpoly-charpoly-oq-02 S7b PREP (researcher-9, 2026-05-14, commit
`1dadb696`) and zsqrtd-neg-two-oq-03 S8 PREP (researcher-8,
2026-05-14, PR #19186).

## 3. v4.26.0 Mathlib API pin (verified at SHA `2df2f015...`)

### 3.1 `Finset.sum_ite_eq` vs `Finset.sum_ite_eq'` (Error 7)

Source: `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean`.

The prime/non-prime convention at v4.26.0:

| Lemma | Form | Where (line in `Piecewise.lean`) |
|---|---|---|
| `Finset.sum_ite_eq` | `∑ x ∈ s, ite (a = x) (b x) 0 = if a ∈ s then b a else 0` | line 141 (additive form of `prod_ite_eq`) |
| `Finset.sum_ite_eq'` | `∑ x ∈ s, ite (x = a) (b x) 0 = if a ∈ s then b a else 0` | line 153 (additive form of `prod_ite_eq'`) |

Mnemonic from line 151 of `Piecewise.lean`:

> The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped. -/

So the **non-prime** version (`sum_ite_eq`) matches `if a = x` (constant
on LEFT), the **prime** version (`sum_ite_eq'`) matches `if x = a`
(constant on RIGHT). The current file uses `Finset.sum_ite_eq'` at line
656 but the goal arrives with `if k = j` (constant `k` on LEFT) — the
wrong direction.

### 3.2 `Nat.choose_succ_succ` and `Nat.choose_succ_right_eq` (Errors 4, 5 context)

Source: `Mathlib/Data/Nat/Choose/Basic.lean`.

| Lemma | Statement | Line |
|---|---|---|
| `Nat.choose_succ_succ` | `choose (succ n) (succ k) = choose n k + choose n (succ k)` | 61 |
| `Nat.choose_succ_succ'` | `choose (n + 1) (k + 1) = choose n k + choose n (k + 1)` | 64 |
| `Nat.choose_succ_right_eq` | `choose n (k + 1) * (k + 1) = choose n k * (n - k)` | 211 |

All three survive at v4.26.0; no API drift relative to the S4
worpitzky_step proof's invocations.

### 3.3 `Finset.sum_range_succ` and `Finset.sum_range_succ'` (Errors 2 context)

Both exist at v4.26.0 in `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
(line 290-310 region; semi-classical content unchanged).

- `sum_range_succ : ∑ x ∈ range (n+1), f x = (∑ x ∈ range n, f x) + f n`
- `sum_range_succ' : ∑ x ∈ range (n+1), f x = (∑ x ∈ range n, f (x+1)) + f 0`

## 4. Error-by-error mechanic kit (surgical diff hunks)

All hunks are anchored to the **current file content** as it appears on
`main` (verified by `git log -1 origin/main -- proofs/Proofs/EhrhartCubeProvenOQ04.lean`).
Line numbers are relative to that snapshot.

### 4.1 Error 1 — `eulerian_zero_eq_one` termination (line 133)

**Symptom** (per #19078 §Error 1):
```
fail to show termination for eulerian_zero_eq_one
failed to infer structural recursion
```

**Current code** (lines 133-135):
```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | _ + 1 => eulerian_zero_eq_one _
```

**Diagnosis**: v4.26.0's structural-recursion check no longer accepts
`_` as the explicit recursive argument when the body wraps it under a
pattern that has already been peeled. The `_` in `eulerian_zero_eq_one _`
is opaque to the termination checker after the `_ + 1` match.

**Mechanic kit — Option A (recommended, 4 LOC, tactic-mode)**:
```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1 := by
  intro d
  induction d with
  | zero => rfl
  | succ n ih => exact ih
```

Reasoning: `eulerianNumber (n+1) 0 = eulerianNumber n 0` is the third
arm of the `def`, so `eulerianNumber (n+1) 0` reduces to
`eulerianNumber n 0` by defeq. The induction hypothesis `ih` gives
`eulerianNumber n 0 = 1`. `exact ih` closes.

**Mechanic kit — Option B (3 LOC, term-mode)**:
```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | d + 1 => eulerian_zero_eq_one d
```

Reasoning: same as Option A but in term-mode. The explicit `d` (instead
of `_`) makes the recursive argument visible to the termination checker.
Both Options A and B leave the definitional rfl arm `| 0 => rfl` intact.

**Confidence**: HIGH — pattern matches `feedback_researcher_v426_structural_recursion_underscore`
style regressions. Either option is a safe drop-in.

### 4.2 Error 2 — `eulerian_row_sum_factorial` `+ 0` residual (line 198 / `rhs_extend` block)

**Symptom** (per #19078 §Error 2):
```
∑ k ∈ range d, (d + 1) * eulerianNumber d k = ∑ x ∈ range d, (d + 1) * eulerianNumber d x + 0
```

**Current code** (lines 196-202):
```lean
have rhs_extend :
    ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
      = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
  rw [Finset.sum_range_succ
        (fun k => (d + 1) * eulerianNumber d k) d,
      eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero,
      Nat.add_zero]
```

**Diagnosis**: After `rw [Finset.sum_range_succ, eulerian_eq_zero_of_le, Nat.mul_zero, Nat.add_zero]`,
v4.26.0 leaves a residual `+ 0` because the LHS and RHS of `rhs_extend`
are flipped — the proof rewrites RHS-side
`∑ range (d+1) ... = ∑ range d ... + 0`, but the goal's LHS is
`∑ range d ...` (no `+ 0`). The `Nat.add_zero` clears the RHS residual,
leaving goal `∑ range d ... = ∑ range d ...` which should close by `rfl`
but v4.26.0 doesn't auto-close after the last `rw`.

**Mechanic kit (1 LOC append)**:
```lean
have rhs_extend :
    ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
      = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
  rw [Finset.sum_range_succ
        (fun k => (d + 1) * eulerianNumber d k) d,
      eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero,
      Nat.add_zero]
  -- (no further tactic needed under pre-v4.26.0; v4.26.0 needs explicit close)
```

If just appending whitespace doesn't close: replace the last bracket
`Nat.add_zero]` with `Nat.add_zero]; rfl` or restructure as:
```lean
  ... eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero]
  ring
```

**Mechanic kit — Option B (replace `rw` chain entirely with `simp`)**:
```lean
have rhs_extend :
    ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
      = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
  rw [Finset.sum_range_succ (fun k => (d + 1) * eulerianNumber d k) d]
  simp [eulerian_eq_zero_of_le d d hd_pos (le_refl d)]
```

Reasoning: split the `rw` into two passes. `sum_range_succ` peels off
the last term; `simp` then closes `... + (d+1) * eulerianNumber d d = ...`
by rewriting `eulerianNumber d d = 0` and simplifying `(d+1) * 0 + x = x`.

**Confidence**: HIGH for Option B (rewrites are robust to v4.26.0 residual
behavior). MEDIUM for the 1-LOC append (depends on exact residual goal).
Recommend mechanic try Option B first if the 1-LOC fix doesn't bite.

### 4.3 Error 3 — `eulerian_palindrome` `Unknown identifier d` after `subst` (line 368)

**Symptom** (per #19078 §Error 3): after `subst hkd` where
`hkd : k = d`, the identifier `d` is gone from scope. Subsequent
`rw [Nat.sub_self d, ...]` fails because `d` is not in scope.

**Current code** (lines 364-368):
```lean
· -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
  have hkd : k = d := by omega
  subst hkd
  -- After subst, the goal is A(d+1, d) = A(d+1, d - d)
  rw [Nat.sub_self d, hboundary, eulerian_zero_eq_one (d + 1)]
```

**Diagnosis**: Lean 4's `subst h` with `h : a = b` and both `a, b` free
variables: Lean's policy is to **eliminate the RHS variable `b`**
(replace `b` with `a` everywhere, then clear `b`). So `subst hkd`
with `hkd : k = d` eliminates `d`, replacing all `d` with `k`. The
subsequent `Nat.sub_self d` then errors with "Unknown identifier `d`"
because `d` is no longer in scope. The comment "After subst, the goal
is A(d+1, d) = A(d+1, d - d)" is wrong — the goal is actually
`A(k+1, k) = A(k+1, k - k)` after subst.

**Mechanic kit — Option A (recommended, 1 LOC, flip equality direction)**:
```lean
· -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
  have hkd : d = k := by omega    -- flipped: d on LHS
  subst hkd                       -- eliminates RHS = k; d survives
  rw [Nat.sub_self d, hboundary, eulerian_zero_eq_one (d + 1)]
```

Reasoning: with `hkd : d = k`, `subst` eliminates `k` (the RHS), so all
`k` become `d`, and `d` survives. The subsequent `rw [Nat.sub_self d, ...]`
finds `d` in scope.

**Mechanic kit — Option B (1 LOC, skip subst, use rewrite)**:
```lean
· -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
  rw [show k = d from by omega, Nat.sub_self d, hboundary,
      eulerian_zero_eq_one (d + 1)]
```

Reasoning: directly rewrite `k ↦ d` in the goal via `show k = d from by omega`,
then apply the rest of the original chain. No `have`/`subst` interplay.

**Mechanic kit — Option C (2 LOC, obtain-rfl pattern)**:
```lean
· -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
  obtain rfl : k = d := by omega
  ...
```

DO NOT use Option C: `obtain rfl` has the same RHS-elimination policy as
`subst`, so `d` would still vanish.

**Confidence**: HIGH for Option A (minimal change, preserves comment
narrative). Option B also safe but rewrites the original idiomatic
structure.

### 4.4 Error 4 — `worpitzky_step` `Nat.add_mul` 3-summand mismatch (line 411)

**Symptom** (per #19078 §Error 4):
```
⊢ k * m.choose (d + 1) + 1 * m.choose (d + 1) + (d - k) * m.choose (d + 1) + (d - k) * m.choose d = ...
```

**Current code** (lines 409-414, inside the `calc` block):
```lean
_ = ((k + 1) * Nat.choose m (d + 1) + (d - k) * Nat.choose m (d + 1))
      + (d - k) * Nat.choose m d := by ring
_ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
    rw [Nat.add_mul]
_ = (d + 1) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
    rw [hsum_coef]
```

**Diagnosis**: the calc step at line 411-412 tries `rw [Nat.add_mul]`
on `((k + 1) * c + (d - k) * c)` to produce `((k + 1) + (d - k)) * c`.
At v4.26.0, the prior `by ring` step (line 410) appears to have
normalized `(k + 1) * c` into `k * c + 1 * c`, leaving three summands.
The single `Nat.add_mul` cannot match three terms.

**Mechanic kit — Option A (recommended, 1 LOC, replace `rw` with `ring`)**:
```lean
_ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
    ring
```

Reasoning: the calc step is a pure semiring equality
`(k+1)*c + (d-k)*c = ((k+1) + (d-k))*c + 0` for some choice of grouping;
`ring` handles this without depending on a specific `Nat.add_mul`
pattern match. This is the most robust fix for any v4.26.0
ring-normalization drift.

**Mechanic kit — Option B (1 LOC, replace prior `ring` with `linarith`)**:

Replace line 410's `by ring` with `by linarith` to prevent the over-
normalization that breaks line 412.

**Confidence**: HIGH for Option A — `ring` is strictly more permissive
than `rw [Nat.add_mul]` and handles both the 2-summand and 3-summand
form. Pre-v4.26.0 build presumably worked because `ring` on line 410
normalized differently.

### 4.5 Error 5 — `worpitzky_identity_cube` `← worpitzky_step` rewrite fail (line 478)

**Symptom** (per #19078 §Error 5):
```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  eulerianNumber d k * (n + 1 + k).choose d * (n + 1) =
    eulerianNumber d k * ((k + 1) * (n + 1 + k).choose (d + 1) + (d - k) * (n + 2 + k).choose (d + 1))
```

**Current code** (lines 476-478):
```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
rw [← worpitzky_step n d k hkd]; ring
```

**Diagnosis**: `worpitzky_step n d k hkd` reads
`(k+1) * C(n+1+k, d+1) + (d-k) * C(n+2+k, d+1) = (n+1) * C(n+1+k, d)`.
The `←` reverses direction, so we need to find `(n+1) * C(n+1+k, d)` in
the goal and rewrite to the LHS expansion. But the goal has
`eulerianNumber d k * (n+1+k).choose d * (n+1)` — the factor `(n+1)` is
on the RIGHT of the choose, not LEFT. v4.26.0 elaborator no longer
auto-commutes the multiplication for `rw` pattern matching.

**Mechanic kit — Option A (recommended, 2 LOC, pre-rewrite factor order)**:
```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
rw [show eulerianNumber d k * (n + 1 + k).choose d * (n + 1)
      = eulerianNumber d k * ((n + 1) * (n + 1 + k).choose d) from by ring,
    ← worpitzky_step n d k hkd]
ring
```

Reasoning: explicit `show ... from by ring` reorders the factors so the
backward rewrite of `worpitzky_step` finds its pattern.

**Mechanic kit — Option B (1 LOC, use `linear_combination`)**:
```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
linear_combination eulerianNumber d k * worpitzky_step n d k hkd
```

Reasoning: `linear_combination` discharges the goal as
`LHS - RHS = c * (worpitzky_step.lhs - worpitzky_step.rhs)` via `ring`.
Coefficient `c = eulerianNumber d k`. Bypasses pattern matching entirely.

**Confidence**: HIGH for Option B — `linear_combination` is the
canonical pattern-free replacement. MEDIUM for Option A (depends on
exact factor order in the goal, which I cannot fully verify without
running Lean).

### 4.6 Error 6 — `worpitzky_d2` redundant `pow_two` rewrite (line 584)

**Symptom** (per #19078 §Error 6):
```
Tactic `rewrite` failed: Did not find an occurrence of the pattern in the current goal
... ih : (m + 1) * (m + 1) = (m + 1).choose 2 + (m + 2).choose 2
⊢ (m + 1 + 1) * (m + 1 + 1) = (m + 1 + 1).choose 2 + (m + 1 + 2).choose 2
```

**Current code** (lines 582-587):
```lean
| succ m ih =>
  -- (m+2)^2 vs C(m+2, 2) + C(m+3, 2)
  -- Use Pascal and ih
  rw [pow_two, pow_two] at *
  rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_succ_succ (m + 2) 1]
  simp only [Nat.choose_one_right, Nat.choose_self, Nat.add_zero] at ih ⊢
  omega
```

**Diagnosis**: `rw [pow_two, pow_two] at *` applies the rewrite twice
to all hypotheses and the goal. After the first rewrite, all `_ ^ 2`
become `_ * _`, so the second `pow_two` finds no pattern.

But wait — there are TWO `^2` instances: one in the goal `(m+1+1)^2`
(from the outer induction's `^2`) and one in `ih`. The first `pow_two`
rewrites the goal; the second is meant to also rewrite `ih`. But at
`pow_two, pow_two] at *`, each rewrite is applied **to all locations**,
not one rewrite per location. So:

- First `pow_two` at *: rewrites BOTH `^2` instances (goal and ih).
- Second `pow_two` at *: nothing left to rewrite → error.

**Mechanic kit (1 LOC, drop the redundant `pow_two`)**:
```lean
| succ m ih =>
  -- (m+2)^2 vs C(m+2, 2) + C(m+3, 2)
  -- Use Pascal and ih
  rw [pow_two] at *
  rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_succ_succ (m + 2) 1]
  simp only [Nat.choose_one_right, Nat.choose_self, Nat.add_zero] at ih ⊢
  omega
```

**Confidence**: HIGH. Simple deletion of redundant rewrite step.

### 4.7 Error 7 — `cube_h_star_eulerian` `sum_ite_eq` direction (line 656)

**Symptom** (per #19078 §Error 7):
```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∑ x ∈ range d, if x = k then eulerianNumber d x else 0
in the target expression
  (∑ x ∈ range d, if k = x then eulerianNumber d x else 0) = eulerianNumber d k
```

**Current code** (lines 653-657):
```lean
simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul,
           mul_ite, mul_one, mul_zero]
-- ∑ j ∈ range d, (if k = j then eulerianNumber d j else 0) = eulerianNumber d k
rw [Finset.sum_ite_eq' (Finset.range d) k (fun j => eulerianNumber d j)]
exact if_pos (Finset.mem_range.mpr hk)
```

**Diagnosis**: per §3.1, `Finset.sum_ite_eq'` is the form
`∑ x ∈ s, ite (x = a) (b x) 0 = ...`, i.e., the variable is on the LEFT
of the equality test. The goal has `if k = j` (constant `k` on LEFT,
variable `j` on RIGHT) — this matches `Finset.sum_ite_eq` (non-prime).

**Mechanic kit (1 LOC, drop the prime)**:
```lean
simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul,
           mul_ite, mul_one, mul_zero]
-- ∑ j ∈ range d, (if k = j then eulerianNumber d j else 0) = eulerianNumber d k
rw [Finset.sum_ite_eq (Finset.range d) k (fun j => eulerianNumber d j)]
exact if_pos (Finset.mem_range.mpr hk)
```

**Confidence**: HIGH. v4.26.0 API pin verified at §3.1.

## 5. Recommended application order

All 7 errors fire independently in a single Lean process (per #19078
build evidence). The mechanic can apply fixes in any order, but I
recommend the following to minimise rebuild cycles:

1. **First Docker iteration**: apply all 7 fixes using Option A (highest-
   confidence) candidates from §4.1-4.7. Single Docker re-build.
2. **If iteration 1 fails on errors 2, 4, or 5**: swap to Option B for
   the failing errors. Second Docker re-build.
3. **Masked-error hunt**: if iteration 1 or 2 surfaces an 8th error not
   in #19078's inventory, document it in PR body and apply a one-line
   surgical fix or escalate to a mechanic-kit refresh PREP.

Expected total mechanic budget: ~1-2 Docker iterations, ~10-15 LOC
edits across 7 sites.

## 6. Masked-error risk assessment

#19078 §"Open Questions" flags:

> 1. **All seven errors are surface-fixable** — confidence high. Risk:
>    a fix could surface a hidden eighth error masked by error 1's
>    termination failure.

Per Lean 4 elaborator behavior: when error 1 fires (structural recursion
fails), `eulerian_zero_eq_one` becomes an `axiom` of its declared type
in the error-recovery axiom table. Downstream uses of
`eulerian_zero_eq_one` (in errors 2, 3, 5, and elsewhere) still see a
term of the right type, so type-checking of downstream proofs proceeds.
The 6 downstream errors (errors 2-7) are therefore independent of error
1's resolution — they would surface even if error 1 were fixed first.

This means the masked-error risk is **bounded** to errors triggered by:
- Computational reduction through `eulerian_zero_eq_one` (e.g., a `rfl`
  proof that depends on `eulerian_zero_eq_one (n+1) = eulerian_zero_eq_one n`
  by defeq).

Scanning the file for `eulerian_zero_eq_one` invocations after error 1:
- Line 206: in `eulerian_row_sum_factorial` (error 2 site).
- Line 208: in `eulerian_row_sum_factorial` (error 2 site).
- Line 334: in `eulerian_palindrome` (boundary case, no error).
- Line 342: in `eulerian_palindrome` (error 3 site).
- Line 368: in `eulerian_palindrome` (error 3 site).

All call sites are at error or near-error locations; none surface as
"hidden 8th error" candidates. The masked-error risk is **LOW**.

## 7. Cross-references to feedback memories

- `feedback_researcher_build_blocker_mechanic_kit_prep_pattern.md` —
  this PREP is a textbook instance: research session pivots to a
  mechanic kit when slug's parent file has multi-error build failure.
- `feedback_researcher_deployer_stall_coordination_prep_pattern.md` —
  applies (§2 above): 13h-since-last-merge confirms stall; PR is
  deliberately conflict-free.
- `feedback_researcher_prep_after_counterexample_strengthens_antecedent.md`
  — not applicable (this is build-verify follow-up, not strengthened-
  antecedent).

## 8. PR sequencing summary

- **PR #19078** (S8 BUILD-VERIFY, OPEN, MERGEABLE): must merge first to
  install the 7-error inventory into `state.md`.
- **This PR (S9 PREP)**: doc-only, conflict-free, adds only
  `sessions/2026-05-14-s9-prep-mechanic-kit.md`. Can merge in either
  order relative to #19078 (no file conflicts).
- **S9 ACT (mechanic-scope, not in this PR)**: applies the 7 fixes
  from §4, runs Docker build, ships under `loom:review-requested` (since
  a mechanic-authored PR, not a math-agent PR — see CLAUDE.md PR label
  policy for math agents).

## 9. Estimated mechanic effort

- Apply all 7 surgical fixes (Option A candidates): ~30 min.
- First Docker build: ~5-10 min cold (Mathlib cache hit).
- If iteration 1 fails: swap to Option B for offending error(s), ~10 min.
- Second Docker build: ~5-10 min.
- Update `state.md` BUILD-VERIFY-FAILED → PROVED-VERIFIED: ~5 min.
- Update `meta.json` line counts and badge: ~5 min.

**Total**: ~60-90 min wall-clock for the full S9 ACT, dominated by
Docker round-trips.
