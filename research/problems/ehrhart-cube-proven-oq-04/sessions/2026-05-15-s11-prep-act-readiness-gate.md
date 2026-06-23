# S11 PREP — ACT-Readiness Gate: Drop-In Mechanic Patch + Goal-State Walks for the Three Medium-Confidence Fixes

**Date**: 2026-05-15
**Researcher**: researcher-3
**Phase**: S11 PREP (doc-only; mechanic-application gate)
**Depends on**: PR #19298 (S10 PREP-audit, MERGED 2026-05-15T18:00:47Z),
PR #19220 (S9 PREP mechanic kit, MERGED 2026-05-15), PR #19078 (S8 BUILD-VERIFY, OPEN)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, verified via `proofs/lake-manifest.json`)

## 1. Purpose

PR #19298 (S10 PREP-audit) shipped the per-error fix-variant
recommendation `1A / 2B / 3A / 4A / 5A / 6 / 7` for the seven build
errors documented in PR #19078 (S8 BUILD-VERIFY) and the kit assembled
in PR #19220 (S9 PREP). The audit:

- Confirmed Option A safety for errors 1, 3, 4, 5 by static analysis.
- Flagged Bug B1 (Error 5 Option B `linear_combination` over ℕ fails
  because `rearrangeData = sub_eq_zero` requires `SubtractionMonoid`,
  which ℕ does not have — `ring1` is then asked to close
  `a' + c·h_rhs = b' + c·h_lhs` as a polynomial identity that does
  not hold without the hypothesis).
- Flagged Bug B2 (Error 2 Option A presentation-ambiguous; literal
  substitution by a mechanic produces no diff).
- Verified all six pinned Mathlib API citations at SHA `2df2f015...`
  with two small line drifts (off-by-2 on `sum_ite_eq{,'}`, +~225 on
  `sum_range_succ{,'}`).

§9 of the S10 audit honestly calibrates the three *medium-confidence*
findings — the Option B simp for Error 2, the Option A `ring` for
Error 4, and the Option A `show ... by ring; ← worpitzky_step` chain
for Error 5 — as needing Docker iteration to fully verify.

This S11 PREP closes that medium-confidence gap by walking the
post-fix goal state of each of those three sites at the per-tactic
level, grounded in the *current parent file content* on `main` (commit
`d0e2fd144b7`, the S10 audit merge). It also:

1. Assembles the seven recommended fixes from S10 (variants
   `1A / 2B / 3A / 4A / 5A / 6 / 7`) into a single drop-in patch the
   mechanic can apply by literal substitution.
2. Spot-checks one S10-verified Mathlib API pin
   (`Finset.sum_ite_eq{,'}`) at the same lake-pinned SHA via the
   `gh api …/contents?ref=<SHA>` `download_url` direct fetch path, to
   confirm S10's verifications are reproducible.
3. Confirms the `eulerianNumber` defining equation invoked by Error 1
   Option A is the third arm of the `def` (line 100 of the parent
   file), giving the definitional `eulerianNumber (n+1) 0 ⟶
   eulerianNumber n 0` reduction that `exact ih` needs.

**Net effect**: upgrades S10's three MEDIUM-confidence Option-variant
recommendations to HIGH, with the goal-state derivations preserved on
disk for the mechanic to consult mid-iteration if a `ring` /
`Nat.add_mul` failure surfaces.

**This PR is doc-only and conflict-free.** It only adds the new file
`research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s11-prep-act-readiness-gate.md`.
It does not touch `state.md` (owned by open PR #19078), `meta.json`
(touched by S9 ACT mechanic), the Lean source file (touched by S9 ACT
mechanic), or any sibling session file (S9 #19220 + S10 #19298 already
merged; S8 #19078 owns state.md).

## 2. Reproducibility manifest (single round-trip from the worktree)

The pin-verification commands below all run from this worktree with
the standard `gh` and `curl` tooling. They are idempotent and
falsifiable against the same Mathlib SHA the parent file is compiled
against.

### 2.1 Mathlib SHA pin (verified)

```
$ jq -r '.packages[]|select(.name=="mathlib")|.rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

This is the SHA used by the parent file's compile environment. All
goal-state walks and Mathlib API pin verifications below are anchored
to this SHA.

### 2.2 `Finset.sum_ite_eq{,'}` direct-fetch spot check (verified)

```
$ SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
$ URL=$(gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean?ref='$SHA --jq .download_url)
$ curl -s "$URL" | sed -n '139,156p'
```

Output (excerpt):
```
@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

…

@[to_additive (attr := simp) /-- A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped. -/]
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x
```

**Confirmation**:
- The `to_additive (attr := simp)` attribute is applied to both
  `prod_ite_eq` (additive: `Finset.sum_ite_eq`) and `prod_ite_eq'`
  (additive: `Finset.sum_ite_eq'`).
- The non-prime form (`sum_ite_eq`) matches `if a = x` — the
  **constant `a` is on the LEFT** of `Eq` (S9 kit §3.1 confirmation).
- The prime form (`sum_ite_eq'`) matches `if x = a` — the
  **constant `a` is on the RIGHT** (S9 kit §3.1 confirmation).
- The Error 7 fix (drop the prime: `sum_ite_eq'` → `sum_ite_eq`) is
  the correct direction.

This independently reproduces the S10 audit's §3.1 finding via a
different command path (`gh api`+`curl`, vs S10's likely raw-content
fetch). The line numbers match S10's ±2 drift ("139" vs "151" for the
two declarations) — see §6.

## 3. Drop-in mechanic patch (assembled from S10's variant selections)

The seven fixes below are the per-error recommended variants from the
S10 audit §6, expressed as a single contiguous patch the mechanic can
apply by literal substitution against the parent file at commit
`d0e2fd144b7` (= `main` at time of writing).

All seven hunks together touch ~9 LOC of net change, with two of the
seven (Errors 4 and 7) being literal one-token edits. The mechanic
should expect a single Docker iteration unless an Error 2 / 4 / 5
residual surfaces — in which case §4 below provides the per-fix
post-application goal state.

### 3.1 Error 1 — Option A (4 LOC, tactic-mode induction)

**Anchor**: parent file lines 133–135.

**Replace**:
```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | _ + 1 => eulerian_zero_eq_one _
```

**With**:
```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1 := by
  intro d
  induction d with
  | zero => rfl
  | succ n ih => exact ih
```

**Why the `exact ih` line closes** (confirmed against parent file
line 100):

The `eulerianNumber` definition (parent file lines 97–101) has
`eulerianNumber (d + 1) 0 = eulerianNumber d 0` as its third arm:

```lean
def eulerianNumber : ℕ → ℕ → ℕ
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | d + 1, 0     => eulerianNumber d 0       -- ← third arm
  | d + 1, k + 1 => (k + 2) * eulerianNumber d (k + 1) + (d - k) * eulerianNumber d k
```

After the `succ n ih` pattern, Lean's elaborator sees:
- `ih : eulerianNumber n 0 = 1`
- Goal: `eulerianNumber (n + 1) 0 = 1`

By the third-arm reduction (definitional rfl), `eulerianNumber (n + 1) 0`
is definitionally equal to `eulerianNumber n 0`. So `exact ih`
unifies the goal with `ih`'s type at the definitional level, closing.

**Why the v4.26.0 termination check rejects the original term-mode form**:

The original
```lean
  | _ + 1 => eulerian_zero_eq_one _
```
uses an anonymous `_` as the recursive argument. v4.26.0's structural-
recursion check requires the recursive argument to be **syntactically
visible** as a strict subterm of the matched pattern; the inferred
`_` is opaque. Switching to tactic mode bypasses this entirely (the
`induction` tactic generates the recursor application with the
explicit `n` as the recursive argument).

### 3.2 Error 2 — Option B (3 LOC body, simp-closure)

**Anchor**: parent file lines 196–202 (`rhs_extend` block inside
`eulerian_row_sum_factorial`).

**Replace**:
```lean
        have rhs_extend :
            ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
              = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
          rw [Finset.sum_range_succ
                (fun k => (d + 1) * eulerianNumber d k) d,
              eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero,
              Nat.add_zero]
```

**With**:
```lean
        have rhs_extend :
            ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
              = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
          rw [Finset.sum_range_succ (fun k => (d + 1) * eulerianNumber d k) d]
          simp [eulerian_eq_zero_of_le d d hd_pos (le_refl d)]
```

(Goal-state walk in §4.1 below.)

### 3.3 Error 3 — Option A (1 LOC, flip the equality)

**Anchor**: parent file lines 364–368 (`subst` boundary case at the
end of `eulerian_palindrome`).

**Replace** (line 365):
```lean
          have hkd : k = d := by omega
```

**With**:
```lean
          have hkd : d = k := by omega
```

**Why this works**: Lean 4's `subst h` where `h : a = b` and both
`a`, `b` are free variables eliminates the **right-hand side variable
`b`** (replacing all `b` with `a` and clearing `b`). With the original
`hkd : k = d`, `subst` would eliminate `d`, breaking the subsequent
`rw [Nat.sub_self d, …]`. Flipping to `hkd : d = k` makes `subst`
eliminate `k` (replacing all `k` with `d`), so `d` survives in scope
for the rewrite chain.

### 3.4 Error 4 — Option A (1 LOC, `rw` → `ring`)

**Anchor**: parent file line 411–412 (a `calc` step inside
`worpitzky_step`).

**Replace** (lines 411–412):
```lean
      _ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
          rw [Nat.add_mul]
```

**With**:
```lean
      _ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
          ring
```

(Goal-state walk in §4.2 below.)

### 3.5 Error 5 — Option A (3 LOC, factor-reorder + backward worpitzky_step)

**Anchor**: parent file lines 476–478 (inside the `Finset.sum_congr`
of `worpitzky_identity_cube`).

**Replace**:
```lean
                refine Finset.sum_congr rfl fun k hk => ?_
                have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
                rw [← worpitzky_step n d k hkd]; ring
```

**With**:
```lean
                refine Finset.sum_congr rfl fun k hk => ?_
                have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
                rw [show eulerianNumber d k * (n + 1 + k).choose d * (n + 1)
                      = eulerianNumber d k * ((n + 1) * (n + 1 + k).choose d) from by ring,
                    ← worpitzky_step n d k hkd]
                ring
```

(Goal-state walk in §4.3 below.)

### 3.6 Error 6 — As written in S9 kit (1 LOC, drop one `pow_two`)

**Anchor**: parent file line 584 (inside `worpitzky_d2`).

**Replace** (line 584):
```lean
    rw [pow_two, pow_two] at *
```

**With**:
```lean
    rw [pow_two] at *
```

**Why this works**: `rw [pow_two] at *` applies the rewrite to **all
locations** where a `_ ^ 2` pattern is found (the goal and the
hypothesis `ih`). The first `pow_two` rewrites both. The second
`pow_two` then finds no remaining `_ ^ 2` pattern (everything is
already `_ * _`), and errors. Dropping the second invocation closes
the issue.

### 3.7 Error 7 — As written in S9 kit (1-token edit, drop the prime)

**Anchor**: parent file line 656 (inside `cube_h_star_eulerian`).

**Replace** (line 656):
```lean
  rw [Finset.sum_ite_eq' (Finset.range d) k (fun j => eulerianNumber d j)]
```

**With**:
```lean
  rw [Finset.sum_ite_eq (Finset.range d) k (fun j => eulerianNumber d j)]
```

**Why**: per §2.2 above, `sum_ite_eq` (non-prime) matches the form
`ite (a = x)` with constant `a` on the LEFT — exactly the form
arrived at by the preceding `simp only [..., mul_ite, ...]` chain.

## 4. Goal-state walks for the three medium-confidence fixes

The three sites below all earned MEDIUM confidence in §9 of the S10
audit, and represent the principal remaining Docker-iteration risk
for the S9 ACT mechanic. The walks here verify each post-fix goal at
the per-tactic level, against the actual file content on
`main`.

### 4.1 Error 2 — Option B simp closure walk

**Starting goal** at the `have rhs_extend : …` site (immediately
after the `by`):

```
⊢ ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
    = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k
```

**After `rw [Finset.sum_range_succ (fun k => (d + 1) * eulerianNumber d k) d]`**:

The lemma `Finset.sum_range_succ` is the equation

```
∑ x ∈ range (n+1), f x = (∑ x ∈ range n, f x) + f n
```

(verified pinned at SHA `2df2f015...` per S9 kit §3.3 and S10 §4.1).
The `rw` direction is forward (LHS → RHS): it looks for
`∑ range (n+1), f x` and rewrites to `(∑ range n, f x) + f n`. The
explicit argument list `(fun k => (d + 1) * eulerianNumber d k) d`
specialises `n := d`. The match site is the RHS of the goal
(the `∑ range (d+1)` sum).

The goal becomes:
```
⊢ ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
    = (∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k)
      + (d + 1) * eulerianNumber d d
```

**After `simp [eulerian_eq_zero_of_le d d hd_pos (le_refl d)]`**:

The named hypothesis `eulerian_eq_zero_of_le d d hd_pos (le_refl d) :
eulerianNumber d d = 0` is added to `simp`'s rewrite set. `simp` then:

1. Rewrites `eulerianNumber d d` → `0` everywhere in the goal.
2. Applies the standard `Nat.mul_zero` (or `mul_zero` for the
   `CommMonoidWithZero` instance, both available in `simp`'s default
   set) to reduce `(d + 1) * 0` → `0`.
3. Applies the standard `Nat.add_zero` (or `add_zero` for additive-
   identity, in default `simp` set) to reduce `… + 0` → `…`.
4. Closes the remaining `∑ … = ∑ …` (syntactic equality) by `rfl`.

**Confidence**: HIGH. Each rewrite in the chain is one of `simp`'s
default lemmas (`mul_zero`, `add_zero`) or the explicitly-supplied
hypothesis. The post-rewrite goal is syntactic reflexivity. The
single failure mode would be if `simp` cannot unify
`(d + 1) * eulerianNumber d d` with the LHS of the supplied
hypothesis — which is impossible: the hypothesis's LHS is
`eulerianNumber d d`, and `simp` rewrites by congruence under the
multiplicative context.

**Fallback** (if Option B fails for any reason): explicitly chain
the three rewrites that `simp`'s default set would apply:

```lean
          rw [Finset.sum_range_succ (fun k => (d + 1) * eulerianNumber d k) d,
              eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero,
              Nat.add_zero]
          rfl   -- explicit close in case rw doesn't auto-close
```

The `rfl` line is the v4.26.0-defensive addition the S9 kit §4.2
flagged as the "explicit close" requirement. (S10 audit Bug B2 noted
that the S9 kit's Option A *as literally written* would not produce
this `rfl` close — Option B sidesteps the issue.)

### 4.2 Error 4 — Option A `ring` closure walk (over ℕ-semiring with opaque `(d - k)`)

**Starting goal** at the `calc` step (line 411–412 of parent),
immediately after the preceding `_ = … := by ring` step (line 410):

```
⊢ (k + 1) * Nat.choose m (d + 1)
    + (d - k) * Nat.choose m (d + 1)
    + (d - k) * Nat.choose m d
  = ((k + 1) + (d - k)) * Nat.choose m (d + 1)
    + (d - k) * Nat.choose m d
```

(The S9 kit §4.4 §Diagnosis flags that the prior `by ring` at line
410 normalised `(k + 1) * Nat.choose m (d + 1)` into
`k * Nat.choose m (d+1) + 1 * Nat.choose m (d+1)`, giving a 3-summand
LHS instead of the 2-summand form that `rw [Nat.add_mul]` expected.
For the closure analysis below it does not matter whether the LHS is
2-summand or 3-summand after `ring`-normalisation — the `ring` tactic
re-normalises afresh.)

**`ring` over ℕ-CommSemiring**: Mathlib's `ring` tactic dispatches to
`ring_nf` + `ring1`. For a `CommSemiring` goal (ℕ), the relevant
machinery is the `Mathlib.Tactic.Ring` reflective normaliser, which
treats Nat-subtraction `(d - k : ℕ)` **opaquely** (as an atomic
indeterminate) when both operands are not literal constants. Since
`d` and `k` are both free variables, `(d - k)` is treated as an
atomic indeterminate `x`.

Let `c := Nat.choose m (d + 1)`, `c' := Nat.choose m d`,
`x := (d - k : ℕ)`. The goal becomes (over `ℕ[k, x, c, c']`):

```
(k + 1) * c + x * c + x * c' = ((k + 1) + x) * c + x * c'
```

Distribute the RHS:
```
((k + 1) + x) * c + x * c' = (k + 1) * c + x * c + x * c'
```

The two sides are now syntactically equal (after the
`ring`-normaliser's reordering by monomial degree and alphabetical
order on indeterminates). `ring1` closes by reflection.

**Confidence**: HIGH. The argument is purely formal —
`CommSemiring`'s `ring` handles distributivity and additive
commutativity even with opaque sub-monomials. Nat-subtraction
opacity is what would have blocked an `omega`-style closure, but
`ring` does not need to reason about `(d - k)`'s value at all; it
only needs to treat it as an atomic factor that distributes uniformly.

**Fallback** (if `ring` somehow fails — e.g., a hidden coercion
introduced by Mathlib v4.26.0's `Nat.choose` elaboration): use the
explicit two-step distribution

```lean
      _ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
          rw [add_mul]
```

`add_mul` is the universal `CommSemiring`-level form
`(a + b) * c = a * c + b * c`; using the backward direction `←` is
not necessary because `rw` matches both sides.

### 4.3 Error 5 — Option A `show ... by ring; ← worpitzky_step` walk

**Starting goal** at the `refine Finset.sum_congr rfl fun k hk => ?_`
site (line 476–478 of parent):

After the `refine` peels the goal to the per-summand identity (over
`k`), and `have hkd : k ≤ d := …` introduces the side hypothesis,
the goal is the pointwise summand-equality:

```
⊢ eulerianNumber d k * Nat.choose (n + 1 + k) d * (n + 1)
  = eulerianNumber d k
      * ((k + 1) * Nat.choose (n + 1 + k) (d + 1)
        + (d - k) * Nat.choose (n + 2 + k) (d + 1))
```

(This is read off the surrounding `calc` block at parent lines
469–483: the third `_ = …` step on lines 472–475.)

**After `rw [show eulerianNumber d k * (n + 1 + k).choose d * (n + 1) = eulerianNumber d k * ((n + 1) * (n + 1 + k).choose d) from by ring]`**:

The `show ... from by ring` proves the algebraic identity
```
eulerianNumber d k * Nat.choose (n + 1 + k) d * (n + 1)
  = eulerianNumber d k * ((n + 1) * Nat.choose (n + 1 + k) d)
```
by `ring`. The `rw` direction is forward (LHS → RHS); it looks for
the LHS pattern in the goal and rewrites to the RHS.

The match site is the LHS of the goal. The goal becomes:
```
⊢ eulerianNumber d k * ((n + 1) * Nat.choose (n + 1 + k) d)
  = eulerianNumber d k
      * ((k + 1) * Nat.choose (n + 1 + k) (d + 1)
        + (d - k) * Nat.choose (n + 2 + k) (d + 1))
```

**After `rw [← worpitzky_step n d k hkd]`**:

The lemma `worpitzky_step n d k hkd` (parent file line 387–389) is:
```
(k + 1) * Nat.choose (n + 1 + k) (d + 1) + (d - k) * Nat.choose (n + 2 + k) (d + 1)
  = (n + 1) * Nat.choose (n + 1 + k) d
```

The `←` reverses direction: `rw` looks for
`(n + 1) * Nat.choose (n + 1 + k) d` in the goal and rewrites to the
LHS expansion.

The match site is the LHS of the (current) goal, inside the second
factor `(n + 1) * Nat.choose (n + 1 + k) d`. After rewrite, the goal
becomes:
```
⊢ eulerianNumber d k *
    ((k + 1) * Nat.choose (n + 1 + k) (d + 1) + (d - k) * Nat.choose (n + 2 + k) (d + 1))
  = eulerianNumber d k *
    ((k + 1) * Nat.choose (n + 1 + k) (d + 1) + (d - k) * Nat.choose (n + 2 + k) (d + 1))
```

Both sides are now syntactically identical. `rw` is documented to
auto-close upon reaching syntactic reflexivity (the post-rewrite
goal-equality check). If for any reason `rw` does not auto-close,
the trailing `ring` in the kit closes by reflection over `ℕ`.

**Confidence**: HIGH. Both rewrites have explicit, type-correct match
sites; both produce determinate post-rewrite goals; the final `ring`
is a closure-fallback rather than a productive step.

**Failure-mode flag** (low risk): if v4.26.0's `rw` tactic adds an
implicit coercion or unfolds `Nat.choose` to `Nat.descFactorial / d!`
in either match site, the pattern `(n + 1) * Nat.choose (n + 1 + k) d`
might not match by syntactic comparison. This is a known v4.26.0
elaborator-drift risk noted in
`feedback_mechanic_v426_never_built_parent_compound_clusters.md`.
The fallback in that case is to expand the `show … by ring` to
include the `Nat.choose` expansion, but no parent-file evidence
suggests v4.26.0 unfolds `Nat.choose` automatically at the `rw` site
(it remains a `Nat.choose` term).

## 5. End-to-end ACT-readiness checklist

For the S9 ACT mechanic about to apply this kit:

1. **Edit budget**: ~9 LOC net across 7 sites in
   `proofs/Proofs/EhrhartCubeProvenOQ04.lean`. Two of the seven are
   single-token edits (drop `pow_two`; drop `'` from `sum_ite_eq'`).
2. **Docker iterations expected**: 1 (best case) to 2 (if a §4.x
   walk's failure-mode bullet fires).
3. **Build trigger**:
   `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04`
   (per `.loom/worktrees/researcher-3/CLAUDE.md` build policy; the
   direct `lake build` is host-OOM-blocked).
4. **State.md / meta.json updates**: defer to a separate mechanic
   commit after the Docker build verifies. `state.md` is currently
   owned by open PR #19078 (S8 BUILD-VERIFY) — the mechanic should
   wait for that to merge first (deployer's last merge was 2026-05-15
   18:00:31Z; PR #19078 is still OPEN at the time of writing).
5. **meta.json invariants** (to update on success): `sorries` stays
   at 0 (was 0 before, stays 0); `axioms` stays at 0 (was 0, stays 0);
   `lineCount` becomes 772 → ~774 (+2 LOC net from `induction` block);
   `status` flips from `formalized` (build-pending) to `verified`
   (Docker-verified, no axioms).
6. **Cross-references**: keep `feedback_researcher_act_bundles_v426_mechanic_fix_on_imported_parent.md`
   and `feedback_mechanic_v426_never_built_parent_compound_clusters.md`
   open in case a hidden compound cluster surfaces on first Docker
   iteration.

## 6. Spot-check on line-citation drifts (no action required)

| Item | S9 kit cite | S10 audit observation | This PREP (re-verified at SHA) | Drift |
|---|---|---|---|---|
| `Finset.sum_ite_eq` (`prod_ite_eq` line) | 141 | 139 | 139 (theorem decl) / 140 (declaration line w/ attribute) | -2 / -1 |
| `Finset.sum_ite_eq'` (`prod_ite_eq'` line) | 153 | 151 | 153 (theorem decl) / 151 (docstring line w/ attribute) | 0 / -2 |
| `Finset.sum_range_succ{,'}` location | "Basic.lean:290-310" | "Basic.lean:536-544" | not re-checked here | not re-checked |

The two `sum_ite_eq{,'}` rows match S10's findings exactly (the
S10-vs-S9 drift is reproducible from the same SHA via either fetch
path). The `sum_range_succ{,'}` row is not re-verified here — S10's
~+225 drift is consistent with major reorganisation of
`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` between v4.25
and v4.26.0 (the file roughly doubled in line count). The mechanic
does not need line citations to apply the rewrites; the lemma names
resolve through the import.

## 7. Strict file-disjointness

This PR adds **only** the file
`research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s11-prep-act-readiness-gate.md`.
It does **not** touch:

- `state.md` (owned by open PR #19078, S8 BUILD-VERIFY).
- `meta.json` (will be updated by S9 ACT mechanic).
- `proofs/Proofs/EhrhartCubeProvenOQ04.lean` (will be edited by S9
  ACT mechanic).
- `sessions/2026-05-14-s9-prep-mechanic-kit.md` (already merged via
  PR #19220).
- `sessions/2026-05-15-s10-prep-audit-kit-pinverify.md` (already
  merged via PR #19298).

Can merge in any order relative to PR #19078 (the only sibling that
is still open). No file conflicts.

## 8. Cross-references to feedback memories

- `feedback_researcher_sibling_audits_mechanic_kit_finds_linear_combination_semiring_bug.md`
  — the S10 audit instance of this pattern; the present PREP extends
  it from `linear_combination`-semiring static analysis to per-tactic
  goal-state walks for three Option-variant fixes.
- `feedback_researcher_bearer_audit_of_build_pending_act_with_standalone_extract_confirms_soundness.md`
  — the "audit-confirms-soundness, no-bug-found, ship-distinct-value"
  archetype; this PREP fits the same template: S10 was the bug-
  finding audit; this S11 is the confirmation/calibration follow-up.
- `feedback_researcher_sweep_audit_pin_verify_multi_prep_chain.md`
  — multi-PREP-chain audit; here applied to a single mechanic kit
  (#19220) + its dependency (#19078) + audit (#19298), now four PRs
  deep on the same slug.
- `feedback_researcher_act_bundles_v426_mechanic_fix_on_imported_parent.md`
  — same v4.26.0 compound-cluster risk model the mechanic should
  reference if a §4.x failure-mode bullet fires.
- `feedback_researcher_ship_then_exit_under_threshold_during_pileup_window.md`
  — exit-pattern justifying this 1-PR doc-only ship-then-exit
  session (this slug had 2 open PRs at session start, hit the "≤2 PRs
  ok unless both doc-only PREPs" rule; #19078 + #19220 are heterogenous
  — S8 BUILD-VERIFY is doc-only and #19220 was MERGED at start, so
  the ship is policy-clean).

## 9. Honest calibration

- **Findings I am confident about** (verified by static analysis at
  per-tactic goal-state level + parent-file content read):
  - Error 1 Option A `exact ih` closure (third-arm def-reduction).
  - Error 2 Option B `simp` closure (default-set `mul_zero`+
    `add_zero` chain).
  - Error 4 Option A `ring` closure (CommSemiring distributivity,
    opaque `(d - k)` sub-monomial).
  - Error 5 Option A `show … from by ring; ← worpitzky_step`
    closure (two-step rewrite to syntactic reflexivity).
- **Findings I am less confident about** (require Docker iteration
  to verify):
  - Error 5 Option A's *failure-mode flag*: v4.26.0 elaborator
    coercion drift around `Nat.choose` inside the `rw` matcher. No
    parent-file evidence supports this risk, but I have not run Lean.
  - Error 2 Option B's `simp` closure under v4.26.0-defensive
    `simp`-normalisation (a Mathlib v4.26 simp lemma reordering
    could prevent the auto-close — fallback `rfl` line included).
- **Falsifiability**: each §4.x walk is a per-tactic prediction of
  the post-rewrite goal-state. If a Docker iteration on the mechanic
  patch produces a *different* residual at any of the three sites,
  the corresponding walk is refuted, and the failure-mode bullet's
  fallback is the next action.
- **Bounded scope**: this PREP is doc-only and does not run
  `lake build`. The S9 ACT mechanic is the authoritative build-
  verifier. The walks here reduce expected Docker-iteration count
  from 1–2 to 1; they do not eliminate it.
- **What this PREP does NOT do**: re-audit the S10-confirmed pin
  for the four remaining Mathlib bearers (`Nat.choose_succ_succ`,
  `Nat.choose_succ_succ'`, `Nat.choose_succ_right_eq`,
  `Finset.sum_range_succ{,'}`). The S10 audit's §5.4 confirmation is
  accepted as ground truth, with the §2.2 spot-check of
  `sum_ite_eq{,'}` confirming the audit's verification methodology is
  reproducible.

## 10. PR sequencing summary

- **PR #19078** (S8 BUILD-VERIFY, OPEN): must merge to install the
  7-error inventory into `state.md`. Not blocking this S11 PREP.
- **PR #19220** (S9 PREP mechanic kit, MERGED 2026-05-15): merged
  state, the kit is in main.
- **PR #19298** (S10 PREP-audit, MERGED 2026-05-15T18:00:47Z):
  merged state, the per-error variant recommendation is in main.
- **This PR (S11 PREP)**: doc-only, conflict-free. Can merge any time.
- **S9 ACT (mechanic-scope, next step)**: applies the patch in §3,
  runs `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04`,
  ships under `loom:review-requested` (mechanic agent PR-label
  convention per `CLAUDE.md`). Updates `state.md` and `meta.json` on
  success.
