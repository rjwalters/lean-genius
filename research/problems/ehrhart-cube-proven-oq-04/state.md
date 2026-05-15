# Current State

**Phase**: BUILD-VERIFY-FAILED (S8 first Docker baseline — 7 surface errors in slug-target file post-v4.26.0 toolchain bump)
**Since**: 2026-05-14T15:30:00Z (S8 STATE-SYNC — build-pending blocker inventory, doc-only)
**Iteration**: 8
**Researcher**: researcher-12

## Current Focus

S8 BUILD-VERIFY (this PR — researcher-12 2026-05-14):
Ran first Docker baseline of `Proofs.EhrhartCubeProvenOQ04` after 7 consecutive
"(build pending)" PRs (S1 SCAFFOLD → S7 POLY-COROLLARIES). All seven
prior research PRs shipped under the convention "Docker cold-build ~45 min,
`.lake` symlink trap" — none Docker-verified. Memory's silent-regression
heuristic (4+ consecutive "(build pending)" PRs = mandatory baseline)
applies; baseline surfaced **7 real proof errors** in the slug's own
target file `proofs/Proofs/EhrhartCubeProvenOQ04.lean`. None of the
errors are in parent files (`Mathlib`, `EhrhartCubeProven`) — they are
all v4.26.0 elaborator-strictness or proof-logic regressions inside
the slug's own theorems.

This PR is **doc-only**: updates `state.md` to reflect the build-pending
blocker status and provides a surgical error inventory for the S9
follow-up (mechanic-scope). No Lean source edits — bundling a 7-error
fix in a research PR violates memory's `> 3 errors = ship inventory,
defer multi-error fix to mechanic` guidance.

## Blockers (S8 BUILD-VERIFY INVENTORY — 7 errors)

Docker build command (from worktree CWD):
```
./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04
```

Toolchain: `leanprover/lean4:v4.26.0`; Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All 7 errors fired
during a single Lean process (Mathlib cache hit, no parent-file errors).

### Error 1 — `eulerian_zero_eq_one` termination (line 133:8)

```
fail to show termination for
  eulerian_zero_eq_one
with errors
failed to infer structural recursion
```

Definition site:

```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | _ + 1 => eulerian_zero_eq_one _
```

v4.26.0 equation compiler is stricter on structural recursion through
the underlying `eulerianNumber` recursion. The `_+1` case recursive
call `eulerian_zero_eq_one _` doesn't reduce the argument under
`sizeOf`-WF (`eulerian_zero_eq_one (n+1) = eulerian_zero_eq_one n` is
syntactic but the compiler treats `n+1` and `_` as opaque after
match-binding).

**Surgical fix candidate** (~3-4 LOC):

```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1 := by
  intro d
  induction d with
  | zero => rfl
  | succ n ih => exact ih
```

The induction tactic exposes the recursive call as `ih : eulerianNumber n 0 = 1`,
and `eulerianNumber (n+1) 0` reduces to `eulerianNumber n 0` by the
def's third arm, so `exact ih` closes by defeq.

### Error 2 — `eulerian_row_sum_factorial` `+ 0` gap (line 198:76)

After `rhs_extend` proves the sum-extension via
`Finset.sum_range_succ` + `eulerian_eq_zero_of_le`, an unsolved goal:

```
∑ k ∈ range d, (d + 1) * eulerianNumber d k = ∑ x ∈ range d, (d + 1) * eulerianNumber d x + 0
```

The `Nat.add_zero` in the `rw` chain at lines 199-202 fires but the
elaborator leaves a residual `+ 0` because `Finset.sum_range_succ`
peels off the last term (which is `0` after `eulerian_eq_zero_of_le`,
`Nat.mul_zero`, `Nat.add_zero`) — but a residual `+ 0` remains.

**Surgical fix candidate** (~1 LOC):

Append `; rfl` or `; ring` after the existing `rw` chain at line 202,
or replace `Nat.add_zero` with `Nat.add_zero, Eq.refl _`.

### Error 3 — `eulerian_palindrome` Unknown identifier `d` (line 368:27)

```lean
· -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
  have hkd : k = d := by omega
  subst hkd
  -- After subst, the goal is A(d+1, d) = A(d+1, d - d)
  rw [Nat.sub_self d, hboundary, eulerian_zero_eq_one (d + 1)]
```

`subst hkd` substitutes the variable that was *introduced last*. With
`hkd : k = d`, `subst` eliminates `k` (the more recent variable) by
replacing it with `d` — so the identifier `k` is gone, but `d` should
remain. The error says `Unknown identifier d` — this means `subst`
eliminated `d` instead (i.e., direction was reversed).

**Surgical fix candidate** (~1 LOC):

Use `subst hkd.symm` to force the direction, or `obtain ⟨rfl⟩ := hkd`
which is unambiguous, or rephrase `hkd : d = k` with `omega` and then
`subst hkd`.

### Error 4 — `worpitzky_step` unsolved arithmetic (line 411:83)

```
⊢ k * m.choose (d + 1) + 1 * m.choose (d + 1) + (d - k) * m.choose (d + 1) + (d - k) * m.choose d =
  …
```

The calc step at line 411-412 applies `Nat.add_mul`:

```lean
_ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
    rw [Nat.add_mul]
```

`Nat.add_mul : (a + b) * c = a*c + b*c` should reverse to combine
`(k+1) * c + (d-k) * c` into `((k+1) + (d-k)) * c`, but the goal
arrives with `k * c + 1 * c + (d-k) * c` (i.e., already distributed
`(k+1) * c = k*c + 1*c` by some earlier `simp`/`ring` normalization).
Pattern doesn't match because the LHS has THREE summands, not two.

**Surgical fix candidate** (~2 LOC):

Replace `rw [Nat.add_mul]` with `ring` (the goal is a pure semiring
equality after constant rearrangement). The previous proof worked when
Lean's normalization left `(k+1) * c` un-distributed; v4.26.0 may now
auto-distribute through `Nat.mul`-style normal form.

### Error 5 — `worpitzky_identity_cube` inductive step rewrite fail (line 478:20)

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
in the target expression
  eulerianNumber d k * (n + 1 + k).choose d * (n + 1) =
    eulerianNumber d k * ((k + 1) * (n + 1 + k).choose (d + 1) + (d - k) * (n + 2 + k).choose (d + 1))
```

The calc step at line 476-478 tries:

```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
rw [← worpitzky_step n d k hkd]; ring
```

`worpitzky_step n d k hkd : (k+1) * C(n+1+k, d+1) + (d-k) * C(n+2+k, d+1) = (n+1) * C(n+1+k, d)`.
Backward rewrite (`←`) requires matching `(n+1) * C(n+1+k, d)` on the
LHS, but the LHS is `eulerianNumber d k * (n+1+k).choose d * (n+1)`
— ordering doesn't match (factor `(n+1)` is on the RIGHT, not LEFT,
of the choose). v4.26.0 elaborator may have tightened pattern matching.

**Surgical fix candidate** (~1-2 LOC):

Pre-rewrite the LHS to put `(n+1)` on the left:
```lean
rw [show eulerianNumber d k * (n+1+k).choose d * (n+1)
      = eulerianNumber d k * ((n+1) * (n+1+k).choose d) from by ring,
    ← worpitzky_step n d k hkd]; ring
```

Or use `linear_combination worpitzky_step n d k hkd` to bypass the
explicit rewrite.

### Error 6 — `worpitzky_d2` redundant `pow_two` rewrite (line 584:17)

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern in the current goal
case succ
e0 : eulerianNumber 2 0 = 1
e1 : eulerianNumber 2 1 = 1
m : ℕ
ih : (m + 1) * (m + 1) = (m + 1).choose 2 + (m + 2).choose 2
⊢ (m + 1 + 1) * (m + 1 + 1) = (m + 1 + 1).choose 2 + (m + 1 + 2).choose 2
```

`rw [pow_two, pow_two] at *` is the offender — the rewrite is applied
TWICE but only ONE `^2` exists per goal/hyp. After the first rewrite
all `_^2` become `_ * _`, and the second `pow_two` finds no pattern.

**Surgical fix candidate** (~1 LOC):

Replace `rw [pow_two, pow_two] at *` with `rw [pow_two] at *` (one
rewrite suffices). Note pre-v4.26.0 may have accepted no-op rewrites;
v4.26.0 errors on them.

### Error 7 — `cube_h_star_eulerian` `sum_ite_eq` direction (line 656:6)

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∑ x ∈ range d, if x = k then eulerianNumber d x else 0
in the target expression
  (∑ x ∈ range d, if k = x then eulerianNumber d x else 0) = eulerianNumber d k
```

`Finset.sum_ite_eq'` expects `if x = k then ... else 0` (`x` on the
LEFT). The goal has `if k = x then ... else 0` (`k` on the left,
flipped equality direction).

**Surgical fix candidate** (~1 LOC):

Two options:
1. Use the non-prime version: `Finset.sum_ite_eq (Finset.range d) k (fun j => eulerianNumber d j)` which expects `if k = x` form. Mathlib has both `sum_ite_eq` (`if k = x`) and `sum_ite_eq'` (`if x = k`).
2. Pre-rewrite with `simp only [eq_comm (a := k)]` to swap the equality direction, then keep `sum_ite_eq'`.

### Cumulative repair budget

7 surgical sites, ~10-15 LOC total edit. Pure surface fixes — no
mathematical content change. All errors are localized and independent
(no inter-error coupling). Mechanic should be able to land all seven
in one Docker iteration after triaging each independently.

## What's Built (cumulative S1–S7, COMPILE-PENDING)

### Definitions (axiom-free, computable)
- `eulerianNumber : ℕ → ℕ → ℕ` — recurrence A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k).
- `cubeHStarPoly : ℕ → Polynomial ℕ` — Eulerian generating polynomial `∑ A(d, k) X^k`.

### Concrete value lemmas (all `rfl`)
- A(0..4, *) — 13 entries plus row-sum and palindrome sanity checks.

### Structural helpers (S3)
- `eulerian_zero_eq_one : ∀ d, A(d, 0) = 1`. **[Error 1 — fails to elaborate]**
- `eulerian_eq_zero_of_le : ∀ d k, 0 < d → d ≤ k → A(d, k) = 0`.

### Recurrence helper (S5)
- `eulerianNumber_recurrence (d k : ℕ) :
    A(d+1, k+1) = (k+2)·A(d, k+1) + (d-k)·A(d, k)` — definitional `rfl`.

### Row-sum theorem (S3)
- `eulerian_row_sum_factorial : ∀ d, 0 < d → ∑ k ∈ range d, A(d, k) = d!`. **[Error 2 — unsolved `+ 0`]**

### Worpitzky step (S4)
- `worpitzky_step (n d k : ℕ) (hk : k ≤ d) :
    (k+1) * C(n+1+k, d+1) + (d-k) * C(n+2+k, d+1) = (n+1) * C(n+1+k, d)`. **[Error 4 — unsolved arithmetic]**

### Worpitzky's identity (S4, main theorem)
- `worpitzky_identity_cube (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d, A(d, k) * C(n + 1 + k, d)`. **[Error 5 — rewrite pattern mismatch]**

### Palindromic symmetry (S5)
- `eulerian_palindrome (d k : ℕ) (hd : 0 < d) (hk : k < d) :
    A(d, k) = A(d, d - 1 - k)`. **[Error 3 — Unknown identifier d after subst]**

### Coefficient extraction (S2)
- `cube_h_star_eulerian : ∀ d k, 0 < d → k < d → (cubeHStarPoly d).coeff k = A(d, k)`. **[Error 7 — sum_ite_eq direction]**
- `cube_lattice_count_eulerian : ∀ d n, 0 < d →
    |Fin d → Fin (n+1)| = ∑ A(d, k) C(n+1+k, d)`.

### Palindrome-reflected Worpitzky form (S6)
- `worpitzky_identity_cube_palindrome : ∀ d n, 0 < d →
    (n+1)^d = ∑ A(d, k) C(n+d-k, d)`.

### Polynomial-evaluation corollaries (S7)
- `cubeHStarPoly_eval_one : ∀ d, 0 < d → (cubeHStarPoly d).eval 1 = d.factorial`.
- `cubeHStarPoly_palindromic : ∀ d k, 0 < d → k < d →
    (cubeHStarPoly d).coeff k = (cubeHStarPoly d).coeff (d - 1 - k)`.

### Concrete cases (S4)
- `worpitzky_d2 (n : ℕ) : (n+1)^2 = C(n+1, 2) + C(n+2, 2)`. **[Error 6 — redundant pow_two]**

## Next Action

**S9 (mechanic/doctor-scope full-file repair)**:
Apply the 7 surgical fixes documented in the inventory above. Expected
LOC: ~10-15 across 7 sites. After repair, re-run
`./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04` from a
worktree CWD; expect ~5-10 min cold-build (Mathlib cache hit). On
success, ship S9 BUILD-VERIFIED PR upgrading badge to `verified` and
status to `proved`.

**S10 (post-build)**:
1. Audit-sync `meta.json` (line counts, theoremCount, axiomCount).
2. Optional: Mathlib upstream contribution path (Combinatorics/Enumerative).

## Attempt Counts

- Total attempts: 8 (S1 SCAFFOLD, S2 STRUCTURAL, S3 ROW-SUM, S4 WORPITZKY, S5 PALINDROME, S6 PALINDROME-COROLLARY, S7 POLY-COROLLARIES, S8 BUILD-VERIFY)
- Current approach attempts: 0 (S9 mechanic-scope)
- Approaches tried: 1 (S8 docker baseline → 7-error inventory)

## Open Questions / Risks

1. **All seven errors are surface-fixable** — confidence high (each error
   has a localized surgical-fix candidate; no proof restructuring needed).
   Risk: a fix could surface a hidden eighth error masked by error 1's
   early termination failure. Mechanic should iterate Docker-build until
   clean.

2. **Pre-v4.26.0 build status unknown** — the 7 PRs (S1-S7) shipped
   under "build pending" convention; impossible to determine if any
   ever Docker-built. Most likely the file was never built cleanly,
   so these are not "regressions" but "latent defects". Confirmation
   would require checking PR CI artifacts or the toolchain bump
   commit timeline.

3. **Mathlib v4.26.0 stricter no-op rewrites** — error 6 reveals
   `pow_two` no-op rewrite now errors; this pattern may affect other
   files in the gallery. Worth a Hermit scan for `rw [_, _] at *`
   chains where the same lemma is repeated. (Out of scope for this slug.)
