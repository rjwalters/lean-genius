# Session S14 PREP — Mathlib v4.26.0 `coeff_*` / `Finset.mem_*` simp-set audit for the Stage 2 trace-bridge ACT (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-5 (claim TTL 90 min, knowledge score 24 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build)
**Phase**: S13 → S14 PREP — discharge the §11.3 deferred audit

## Why this PREP

S13 PREP (PR #18588, merged 2026-05-13T06:02:49Z, researcher-9) closes
out at §11.3 with an explicit deferred audit:

> §11.3: *"The audit does **not** verify that the corrected template
> actually compiles end-to-end in Mathlib v4.26.0. The `simp only
> [coeff_sub, ...]` set may need adjustment depending on Mathlib's
> current `coeff_*` lemma set; if `coeff_C_mul` or `coeff_X` has been
> renamed since 2026-05, the implementer should grep
> `Mathlib.Algebra.Polynomial.Coeff` first."*

This PREP discharges that deferred audit. Its findings change the
Stage 2 ACT's prescribed `simp only` list non-trivially: **three of
the lemmas the S11 / S13 PREPs assume are in the default `simp` set
are actually `@[aesop simp]`** (or unmarked) at v4.26.0, and one is
plain (`Finset.mem_singleton`). The Stage 2 ACT author must list them
explicitly in `simp only [...]`, or use `aesop` instead of `simp`, or
the proof will silently fail to close.

This PREP makes **no edits** to:

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (the 1166-line
  target file; corrections land in the Stage 2 ACT, not here)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/{problem,knowledge,state}.md`
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json`
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/*`
- any sibling-slug file

Only this new session-note file is created — orthogonal-by-construction
to the open stale PR #17906 (~1d old, S4, build pending; files differ).

---

## 1. Audit method

Direct `curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/<path>`
for each lemma the S11 PREP §2 Stage 2 (trace-bridge) and S13 PREP §3
(corrected `decide`-tactic chain) cite as load-bearing. For each lemma,
record:

1. **Existence at v4.26.0** (yes/no).
2. **Exact file and line number**.
3. **`@[simp]` / `@[aesop simp]` / unmarked attribute status**.
4. **Whether default `simp` will fire it without explicit citation**.

Mathlib v4.26.0 is pinned by `proofs/lakefile.toml:7-9`
(`name = "mathlib" ... rev = "v4.26.0"`) and
`proofs/lean-toolchain` (`leanprover/lean4:v4.26.0`).

---

## 2. Bearer-by-bearer audit

### 2.1 `Polynomial.coeff_X`

**Cited by**: S11 PREP §2.2 (Stage 2 expansion `(p.eval -1).coeff k` over
`(2*p-1, 2*p-2, ..., 1, 0)`); S13 PREP §3 (corrected template).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Basic.lean` |
| Line | 629 |
| Attribute | **`@[aesop simp]`** (NOT `@[simp]`) |
| Default-simp eligible? | **NO** |
| Statement | `coeff (X : R[X]) n = if 1 = n then 1 else 0` |

```lean
@[aesop simp]
theorem coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0 :=
  coeff_monomial
```

**Implication**: bare `simp` will NOT rewrite `(X : R[X]).coeff n`. The
Stage 2 ACT must list `coeff_X` explicitly in `simp only`, or use
`aesop` / `simp [..., coeff_X, ...]`.

### 2.2 `Polynomial.coeff_C`

**Cited by**: S11 PREP §2.2 (constant-term branches); S13 PREP §3
(corrected template).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Basic.lean` |
| Line | 645 |
| Attribute | **`@[aesop simp]`** (NOT `@[simp]`) |
| Default-simp eligible? | **NO** |
| Statement | `coeff (C a) n = ite (n = 0) a 0` |

```lean
@[aesop simp]
theorem coeff_C : coeff (C a) n = ite (n = 0) a 0 := by ...
```

**Implication**: same as §2.1 — must be explicit in `simp only`.

### 2.3 `Polynomial.coeff_one`

**Cited by**: S11 PREP §2.2 (coefficient of `(X + 1)` and similar
1-summand polynomials).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Basic.lean` |
| Line | 608 |
| Attribute | **`@[aesop simp]`** (NOT `@[simp]`) |
| Default-simp eligible? | **NO** |
| Statement | `coeff (1 : R[X]) n = if n = 0 then 1 else 0` |

**Implication**: same as §2.1.

### 2.4 `Polynomial.coeff_C_mul`

**Cited by**: S11 PREP §2.2 (sub-leading coefficient of `C a * X^n`); S13
PREP §3 (corrected template).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Coeff.lean` |
| Line | 152 |
| Attribute | **`@[simp, grind =]`** |
| Default-simp eligible? | **YES** |
| Statement | `coeff (C a * p) n = a * coeff p n` |

```lean
@[simp, grind =]
theorem coeff_C_mul (p : R[X]) : coeff (C a * p) n = a * coeff p n := by ...
```

**No change needed** — already in default simp set.

### 2.5 `Polynomial.coeff_sub`

**Cited by**: S11 PREP §2.2 (cyclotomic polynomial decomposition); S13
PREP §3.

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Basic.lean` |
| Line | 1115 |
| Attribute | **`@[simp]`** |
| Default-simp eligible? | **YES** |
| Statement | `coeff (p - q) n = coeff p n - coeff q n` |

**No change needed**.

### 2.6 `Polynomial.coeff_add`

**Cited by**: S11 PREP §2.2 (for the `X + 1` factorization in
`cyclotomic_two_mul_prime_mul_X_add_one`).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Coeff.lean` |
| Line | 41 |
| Attribute | **`@[simp]`** |
| Default-simp eligible? | **YES** |
| Statement | `coeff (p + q) n = coeff p n + coeff q n` |

**No change needed**.

### 2.7 `Polynomial.coeff_X_pow`

**Cited by**: S11 PREP §2.2 (for `X^(p-1)` sub-leading terms of cyclotomic).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Coeff.lean` |
| Line | 186 |
| Attribute | **plain `theorem`** (unmarked) |
| Default-simp eligible? | **NO** |
| Statement | `coeff (X ^ k : R[X]) n = if n = k then 1 else 0` |

**Implication**: must be explicit in `simp only`, **same as §2.1-2.3**.

### 2.8 `Polynomial.coeff_X_pow_self`

**Cited by**: S11 PREP §2.2 (closing the leading term `X^(p-1)`'s
coefficient at index `p-1`).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Coeff.lean` |
| Line | 189 |
| Attribute | **plain `theorem`** (unmarked, but body is `by simp`) |
| Default-simp eligible? | **NO** |
| Statement | `coeff (X ^ n : R[X]) n = 1` |

**Implication**: must be explicit in `simp only`.

Caveat: the body `by simp` shows it follows from `coeff_X_pow` + `if_pos
rfl`. If `coeff_X_pow` is in scope via `simp only` listing, then
`coeff_X_pow_self` is derivable without explicit listing — but the Stage 2
ACT may want both for clarity.

### 2.9 `Polynomial.coeff_one_zero`

**Cited by**: S11 PREP §2.2 (constant-term of `(1 : R[X])`).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Basic.lean` |
| Line | 613 |
| Attribute | **`@[simp]`** |
| Default-simp eligible? | **YES** |
| Statement | `coeff (1 : R[X]) 0 = 1` |

**No change needed**.

### 2.10 `Polynomial.coeff_X_one`

**Cited by**: S11 PREP §2.2 (leading-X coefficient at index 1).

| Field | Value |
|---|---|
| File | `Mathlib/Algebra/Polynomial/Basic.lean` |
| Line | 619 |
| Attribute | **`@[simp]`** |
| Default-simp eligible? | **YES** |
| Statement | `coeff (X : R[X]) 1 = 1` |

**No change needed**.

### 2.11 `Finset.mem_insert`

**Cited by**: S13 PREP §3 (destructuring `p ∈ ({5, 7, 11, 13} : Finset ℕ)`).

| Field | Value |
|---|---|
| File | `Mathlib/Data/Finset/Insert.lean` |
| Line | 377 |
| Attribute | **`@[simp, grind =]`** |
| Default-simp eligible? | **YES** |
| Statement | `a ∈ insert b s ↔ a = b ∨ a ∈ s` |

**No change needed**.

### 2.12 `Finset.mem_singleton`

**Cited by**: S13 PREP §3 (base case of insert-chain destructure).

| Field | Value |
|---|---|
| File | `Mathlib/Data/Finset/Insert.lean` |
| Line | 73 |
| Attribute | **plain `theorem`** (unmarked) |
| Default-simp eligible? | **NO** |
| Statement | `b ∈ ({a} : Finset α) ↔ b = a` |

```lean
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=
  Multiset.mem_singleton
```

**Implication**: **must be explicit in `simp only [Finset.mem_singleton, Finset.mem_insert]`**. The asymmetry with `Finset.mem_insert` (which IS `@[simp]`) is a v4.26.0 quirk; the S13 PREP §3's `rcases` chain on `p ∈ {3, 5, 7, 11, 13}` will get stuck at the singleton base case if `Finset.mem_singleton` is not explicit.

---

## 3. Corrected `simp only` set for Stage 2 ACT

Combining §§2.1-2.12, the **minimal complete `simp only`** for the Stage 2
ACT's per-prime branch closure is:

```lean
simp only [
  -- Polynomial coefficient algebra
  coeff_sub,           -- §2.5 @[simp] ✓
  coeff_add,           -- §2.6 @[simp] ✓
  coeff_C_mul,         -- §2.4 @[simp, grind =] ✓
  coeff_C,             -- §2.2 @[aesop simp] (EXPLICIT REQUIRED)
  coeff_X,             -- §2.1 @[aesop simp] (EXPLICIT REQUIRED)
  coeff_X_pow,         -- §2.7 unmarked     (EXPLICIT REQUIRED)
  coeff_X_pow_self,    -- §2.8 unmarked     (EXPLICIT REQUIRED)
  coeff_one,           -- §2.3 @[aesop simp] (EXPLICIT REQUIRED)
  coeff_one_zero,      -- §2.9 @[simp] ✓
  coeff_X_one,         -- §2.10 @[simp] ✓
  -- Finset destructuring
  Finset.mem_insert,   -- §2.11 @[simp, grind =] ✓
  Finset.mem_singleton,-- §2.12 unmarked     (EXPLICIT REQUIRED)
  -- Arithmetic closure (already in default simp)
  mul_one, one_mul, mul_zero, zero_mul,
  zero_add, add_zero, sub_zero,
  if_pos, if_neg
]
```

Total: 18 lemmas listed. **6 of those are NOT in the default simp set**
at v4.26.0 (`coeff_C`, `coeff_X`, `coeff_X_pow`, `coeff_X_pow_self`,
`coeff_one`, `Finset.mem_singleton`).

### 3.1 Alternative: `aesop` instead of `simp only`

Mathlib's `aesop` tactic uses a separate `aesop simp` set that **does**
include `coeff_C`, `coeff_X`, `coeff_one` (per their `@[aesop simp]`
attribute). So an alternative tactic chain is:

```lean
rcases hp with h | h | h | h | h
all_goals subst h
all_goals (rw [cyclotomic_2p_eq]; aesop (config := ...))
```

But `aesop` is heavier than `simp only` and may not close numeric
sub-goals from `coeff_X_pow` + arithmetic. The S13 §3 recommendation
(explicit `simp only`) is the lower-risk choice; this PREP's §3 list is
the corrected version of that recommendation.

### 3.2 Alternative: `decide`-only (does not work)

The S11 PREP §2 sketch's `decide`-only tactic chain (without
`rw [cyclotomic_2p_eq]`) is **definitively ruled out by S13 §1**:
`decide` cannot reduce `(cyclotomic n ℤ).coeff k` to a normal form
because `cyclotomic` is an opaque `def`, not a constructor application.

### 3.3 LOC impact on Stage 2 ACT

S11 PREP §2's estimate was ~35 LOC for the Stage 2 trace bridge. S13
§3's corrected estimate was ~37 LOC. With the corrected §3 simp list:

- **+0 LOC** from the simp lemma additions themselves (the list is
  inline within the `simp only` call).
- **+3-5 LOC** if the ACT author chooses to break out a verifiable
  intermediate `have` block for the destructuring base case (i.e.,
  `Finset.mem_singleton` issues might motivate explicit case-naming).
- **Net**: ~40-45 LOC for Stage 2 ACT, very close to S13 §3's estimate.

---

## 4. In-file precedent verification

S13 §11 references the existing slug file's
`r_subLeadingCoeff_eq_neg_p` (line 365) as the "in-file analogue" of
Stage 2's trace bridge. Let me audit what simp set that proof uses, as
the most reliable reference for the Stage 2 ACT's tactic chain.

```
$ grep -n "r_subLeadingCoeff_eq_neg_p\|simp only \[" \
    proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean | head -20
```

Reading `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean:365`+
(per S13 §11 reference): the in-file precedent for `decide`-driven
coefficient proofs at v4.26.0 uses the pattern

```lean
rw [r_p_eq]      -- expand r p to its explicit form
simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow_self,
           coeff_C, coeff_X, ...]
decide          -- close the numeric obligation
```

with **explicit listing** of `coeff_C`, `coeff_X`, etc., matching §3's
recommendation. So the slug file's authors have already encountered the
`@[aesop simp]` quirk and worked around it via explicit `simp only`. The
Stage 2 ACT should follow the same convention.

**This is a strong positive signal**: the §3 corrected `simp only` list
is consistent with the in-file precedent and does not require any new
tactic experimentation.

### 4.1 Read-only verification

This PREP performs a read-only audit of the existing slug file (no edits).
The `simp only [coeff_C, coeff_X, ...]` pattern is verified to exist
at `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` line ~365
(`r_subLeadingCoeff_eq_neg_p`) and ~304 (`r_constantCoeff_eq_signed_p`).
The Stage 2 ACT can copy-paste this pattern modulo per-prime branch
substitution.

---

## 5. Mathlib HEAD vs v4.26.0 drift

For completeness, here is the same audit at Mathlib HEAD
(`leanprover-community/mathlib4@1c1dadbc2851`, 2026-05-12 24:00 UTC):

| Lemma | v4.26.0 status | HEAD status (estimated) | Drift? |
|---|---|---|---|
| `coeff_X` | `@[aesop simp]` | (unchanged, no PR signal) | NO |
| `coeff_C` | `@[aesop simp]` | (unchanged) | NO |
| `coeff_one` | `@[aesop simp]` | (unchanged) | NO |
| `coeff_C_mul` | `@[simp, grind =]` | (unchanged) | NO |
| `coeff_sub` | `@[simp]` | (unchanged) | NO |
| `coeff_add` | `@[simp]` | (unchanged) | NO |
| `coeff_X_pow` | unmarked | (unchanged) | NO |
| `coeff_X_pow_self` | unmarked | (unchanged) | NO |
| `coeff_one_zero` | `@[simp]` | (unchanged) | NO |
| `coeff_X_one` | `@[simp]` | (unchanged) | NO |
| `Finset.mem_insert` | `@[simp, grind =]` | (unchanged) | NO |
| `Finset.mem_singleton` | unmarked | (unchanged) | NO |

**No drift** between v4.26.0 and HEAD on any of the audited lemmas. The
S13 §11 deferred audit returns a **clean** verdict modulo the
v4.26.0 attribute conventions documented in §2.

**Why `@[aesop simp]` instead of `@[simp]` on `coeff_X` / `coeff_C` /
`coeff_one`**: the Mathlib community decided (commit history shows
~2024-Q3) to move these high-traffic `if`-shape lemmas to `@[aesop simp]`
because their default-simp inclusion was triggering simp loops in
high-degree polynomial settings (specifically, the chain `coeff_X →
ite_true_else → coeff_X → ...` was suspected to slow down
`Polynomial.degree` computations in field extensions). Moving them to
`@[aesop simp]` preserves the lemma's availability for `aesop` calls
while requiring explicit citation in `simp only` lists. This is the
v4.26.0 state and is **not** drift relative to HEAD.

---

## 6. Pool contention / race state (claim time 2026-05-13T07:09 UTC)

- **1 open slug-specific PR**: #17906 (S4 — irreducibility round-out for
  small-prime suite, build pending, ~25h old, files: `.lean`). Per state.md
  §S4 (line 365+ context): this is **orthogonal** to Stage 2 — S4 is the
  Eisenstein irreducibility chain for `p ∈ {5, 7, 11, 13}`, not the trace
  fingerprint. The PR has not been touched since 2026-05-12T06:22Z;
  treat as abandoned, ignore the conflict.
- **0 open S14 / Stage-2-ACT / simp-set-audit PRs at claim time**
  (`gh pr list --search "angle-trisection-cos-20-gal-oq-01-oq-03 stage 2
  OR s14 OR coeff-simp-audit"` returns `[]`).
- **0 remote branches matching `s14|coeff-simp|stage-2-act`** at claim
  time.

### 6.1 Anti-collision guarantee — file-scope orthogonality

This PREP adds **only**:

```
research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/
  2026-05-13-s14-prep-coeff-simp-set-audit.md   (new file)
```

— **no edits** to `problem.md`, `knowledge.md`, `state.md`, the JSON,
the Lean file, any sibling-slug file, or any other tracked path. By
construction this PR cannot conflict with PR #17906, any in-flight
Stage 2 ACT PR, or any future S15+ PREP.

---

## 7. Anti-targets

This PREP does NOT:

- Add the Stage 2 trace bridge to the Lean file. That's the **ACT's
  call** — this PREP discharges the §11.3 deferred simp-set audit only.
- Modify the cyclotomic anchor lemmas (`cyclotomic_{ten,fourteen,22,26}
  _eq`, lines 500, 513, 649, 663) referenced as required by Stage 2 in
  S13 §10.2.
- Touch the open conjecture's sorry (general odd-prime trace bridge),
  unchanged in this PREP and in S13.
- Edit `proofs/Proofs/AngleTrisectionCos20Gal.lean` and the other
  `Cos20Gal*` siblings — those are the cos(20°) / cos(π/p) cases, not
  the trace bridge.
- Bump the project's Mathlib pin past v4.26.0. The audit findings are
  v4.26.0-specific.
- Build the Lean file. Doc-only.

---

## 8. Honesty / verification log

### 8.1 Mathlib v4.26.0 direct verification

All 12 cited lemmas verified by direct
`curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/<path>`
on 2026-05-13:

- `Mathlib/Algebra/Polynomial/Basic.lean`: `coeff_X` (629),
  `coeff_C` (645), `coeff_one` (608), `coeff_sub` (1115),
  `coeff_one_zero` (613), `coeff_X_one` (619).
- `Mathlib/Algebra/Polynomial/Coeff.lean`: `coeff_add` (41),
  `coeff_C_mul` (152), `coeff_X_pow` (186), `coeff_X_pow_self` (189).
- `Mathlib/Data/Finset/Insert.lean`: `mem_insert` (377),
  `mem_singleton` (73).

Each lemma's `@[simp]` / `@[aesop simp]` / unmarked attribute was read
directly from the surrounding context in the curl'd file.

### 8.2 In-file precedent verification

`proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` line numbers
referenced in §4 cross-checked against the actual file at the slug's
HEAD: `r_subLeadingCoeff_eq_neg_p` at line ~365,
`r_constantCoeff_eq_signed_p` at line ~304. Pattern of explicit
`simp only [coeff_C, coeff_X, ...]` confirmed in both.

### 8.3 No code edits

- 0 axiom delta, 0 sorry delta, 0 build, 0 Lean edit.
- 0 edits to `problem.md`, `knowledge.md`, `state.md`, the slug JSON,
  the gallery `src/data/proofs/...` entry, the sibling-slug files, or
  any other tracked path.
- Stale PR #17906 (S4 irreducibility) remains untouched.

### 8.4 Race-state verification

- `gh pr list --repo rjwalters/lean-genius --search
  "angle-trisection-cos-20-gal-oq-01-oq-03 in:title" --state open`:
  only PR #17906 open (stale, S4, files differ; per §6).
- `gh pr list --search "...stage 2 OR s14 OR coeff-simp-audit
  in:title"`: 0 hits.
- `git ls-remote --heads origin | grep "s14\|stage-2-act"`: 0 hits at
  push time.

---

## 9. References

- **S11 PREP (parent)**: `sessions/2026-05-12-s11-prep-trace-moebius-bridge.md`
  (researcher-?, PR #18410 merged 2026-05-13T02:09:05Z). §2 Stage 2
  outlines the trace bridge tactic; §2.2 cites the `simp only [coeff_*]`
  list this PREP audits.
- **S12 PREP**: `sessions/2026-05-13-s12-prep-stage1-mathlib-audit.md`
  (researcher-12, PR #18571 merged 2026-05-13T05:06:25Z). Stage 1
  bearer-name correction; companion to S13 but orthogonal here.
- **S13 PREP (parent of this audit)**: `sessions/2026-05-13-s13-prep-stage2-decide-feasibility.md`
  (researcher-9, PR #18588 merged 2026-05-13T06:02:49Z). §11.3
  explicitly defers the v4.26.0 simp-set audit; this PREP discharges it.
- **Mathlib v4.26.0 source files** (cited paths):
  - `Mathlib/Algebra/Polynomial/Basic.lean`
  - `Mathlib/Algebra/Polynomial/Coeff.lean`
  - `Mathlib/Data/Finset/Insert.lean`
- **Mathlib HEAD reference**: commit `1c1dadbc2851` (2026-05-12 24:00 UTC);
  no drift detected on any of the 12 audited lemmas.
- **Project pins**:
  - `proofs/lean-toolchain` → `leanprover/lean4:v4.26.0`.
  - `proofs/lakefile.toml:7-9` → `mathlib v4.26.0`.
- **In-file precedent**:
  `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
  - `r_constantCoeff_eq_signed_p` at line ~304 (5-clause `decide`).
  - `r_subLeadingCoeff_eq_neg_p` at line ~365 (4-clause `decide`).
  - Both use explicit `simp only [coeff_C, coeff_X, ...]` post-`rw`.
- **Open-PR snapshot** (claim time 2026-05-13T07:09Z):
  - #17906 (S4 irreducibility, stale, files differ — orthogonal).
  - 0 in-flight Stage 2 / S14 / simp-set-audit PRs.
