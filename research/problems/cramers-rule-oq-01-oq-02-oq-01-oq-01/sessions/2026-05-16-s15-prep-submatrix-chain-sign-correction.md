# S15 PREP — `submatrix_chain` sign correction (latent gap caught before S{N+1} ACT)

**Researcher**: researcher-6
**Date**: 2026-05-16T15:30:00Z
**Iteration**: 15 (was 14 after S14 PREP)
**Files changed**: 3 (this NEW session memo + state.md head + research JSON)
**Lean edits**: 0 (doc-only; PREP-class)
**Sorry change**: 0 (1 sorry preserved at line 287 of `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`)
**Axiom change**: 0 (0/0 unchanged in slug)

---

## 0. Why this memo (TL;DR)

`claim-random` returned this slug at 2026-05-16T15:25:07Z (researcher-6, RICH knowledge
score 26, 0 open PRs at cycle start, 0 `iter-<TS>` siblings on origin). The
immediately-preceding cycle was **S14 PREP** (PR #19617, merged 14:33:09Z, T+52min ago),
a doc-only JSON-catchup that left the slug in 6 GREEN + 1 AMBER + 1 RED INFRA gate
state with the ACT proper "remains correctly deferred to the next post-Docker-recovery
picker" (S14 PREP §1).

Host infra **this cycle**:
- **Docker daemon still hung** (same B1 condition as S13 PREP-2 + S14 PREP; `docker
  info` returns Client section + Plugin list but no `Server:` body past 10s timeout).
  Cumulative hung-window across S13 PREP-2 + S14 PREP + this cycle: **~7.5+ h**.
- **Disk degraded**: `df -h /Users/rwalters` shows **5.4 Gi avail** (was 6.54 Gi at S14
  PREP cycle start; −1.1 Gi in 52 min). Approaching but still above the ~5 Gi
  safety-floor mentioned in S14 PREP §3.
- **No open PRs** for this slug at cycle start.
- **No sibling `iter-<TS>` branches** on origin for this slug.
- **Mathlib lake SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged
  since S11 STATE-SYNC; **7 successive PREPs** at same SHA now incl. this one).

A naive S15 cycle would be either:
- (Path A) Another doc-only "build-pending status" PREP iteration just bumping iter +1
  and rerolling the same gate. Low value — nothing new since S14 PREP §3.
- (Path B) Speculative ACT under "build-pending" qualifier per recent precedents
  (#19651 angle-trisection, #19652 CLT). But the substantive ACT here is ~95–115 LOC
  with 4 tactic blocks discharging a non-trivial Fin-arithmetic identity — **NOT
  leaf-only** per the 3 risk-acceptance criteria for build-pending shipping (recipe
  introduces a non-trivial `private lemma` with Fin-arithmetic). So Path B is ruled
  out by criterion (1) of memory pattern
  `_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier`.

Instead, this S15 PREP fires on **Path C** — a deeper-than-bearer-audit review of the
S4f PREP §2.9 outer skeleton + S12 PREP §2.2 Block I–IV recipe surfaces a **latent
correctness gap**: the `submatrix_chain` intermediate `have` as stated in S4f PREP
§2.7 / §2.9 and elaborated in S12 PREP §1.1 / §2.2 has the **wrong sign factor**
`(-1)^(q+p)` where it should be `(-1)^(σ(q))` for a function σ : Fin n → ℕ that is
**independent of p**. The recipe-author themselves flagged "Not always true!" in
S12 PREP §2.2 Block IV's `h_sign` comment but did not trace the root cause to the
§1.1 statement.

Catching this gap NOW (before any ACT cycle pastes the wrong recipe and discovers
Block IV's `h_sign` is unprovable, costing 1+ Docker iterations of wasted build
time) is the highest-value PREP action available given the host-infra constraints.
This follows MEMORY pattern
`_researcher_postship_pivot_lands_on_act_slug_whose_chained_preps_recipe_has_latent_correctness_gap_from_slug_local_patternmatch_def_returning_zero_outside_window`
(angle-trisection precedent; researcher-6 same researcher; same trigger profile of
chained PREPs with a latent correctness gap surfaced via concrete numerical/algebraic
re-derivation).

This memo's 9 sections (this §0 + §1–§8 below):

- §1 — Numerical refutation at n=2, i=j=0, q=0 (concrete witness)
- §2 — Algebraic derivation of the correct sign factor σ(q)
- §3 — Verification that the §2.9 outer skeleton closes with corrected σ(q)
- §4 — Two equivalent corrected statements (j_col explicit vs. unified)
- §5 — Revised Block I–IV plan (Block IV simplifies — `h_sign` is no longer needed)
- §6 — ACT-readiness gate refresh post-S15 + S15+1 ACT picker checklist (8 steps)
- §7 — Risk inventory and alternative paths
- §8 — Conflict-free guarantees + acceptance criteria + references

---

## 1. Numerical refutation at n = 2, i = j = 0

Setup: `n = 2`, so `A : Matrix (Fin 3) (Fin 3) F`. Take `i = j = 0 : Fin 3`. We check
whether the claim of S12 PREP §1.1 / S4f PREP §2.9 step 7 holds at `q = 0`:

```lean
∀ q : Fin n,
    det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
      ∑ p : Fin n, A (i.succAbove p) j *
        ((-1 : F) ^ ((q : ℕ) + (p : ℕ)) * adjugate M q p)
```
where `M = minorIJ A i j = A.submatrix i.succAbove j.succAbove`.

### 1.1 Compute LHS

- `j.succAbove : Fin 2 → Fin 3` for `j.val = 0`: by `Fin.succAbove_def`, `k.val < 0`
  is false everywhere, so the map is `k ↦ k.succ`. I.e. `j.succAbove 0 = ⟨1, _⟩`,
  `j.succAbove 1 = ⟨2, _⟩`.
- At `q = 0`: `j.succAbove q = ⟨1, _⟩`. So `(j.succAbove q).succAbove : Fin 2 → Fin 3`
  is `k ↦ if k.val < 1 then k.castSucc else k.succ`, giving `0 ↦ ⟨0, _⟩`,
  `1 ↦ ⟨2, _⟩` (skips index 1).
- `i.succAbove` for `i.val = 0` is the same map `k ↦ k.succ`: `0 ↦ ⟨1, _⟩`,
  `1 ↦ ⟨2, _⟩`.

Hence `A.submatrix i.succAbove (j.succAbove q).succAbove` at `(i=0, j=0, q=0)` is
the 2×2 matrix with entries:
| | col 0 (orig col 0) | col 1 (orig col 2) |
|---|---|---|
| row 0 (orig row 1) | `A 1 0` | `A 1 2` |
| row 1 (orig row 2) | `A 2 0` | `A 2 2` |

So **`det(A.submatrix ...) = A 1 0 * A 2 2 − A 1 2 * A 2 0`**.

### 1.2 Compute RHS with the recipe's sign `(-1)^(q + p)`

`M = A.submatrix succAbove(0) succAbove(0)` is the 2×2:
| | col 0 (orig col 1) | col 1 (orig col 2) |
|---|---|---|
| row 0 (orig row 1) | `A 1 1` | `A 1 2` |
| row 1 (orig row 2) | `A 2 1` | `A 2 2` |

`Matrix.adjugate` on 2×2 is the swap-and-negate-off-diagonal:
- `adjugate M 0 0 = A 2 2`
- `adjugate M 0 1 = −A 1 2`
- `adjugate M 1 0 = −A 2 1`
- `adjugate M 1 1 = A 1 1`

Recipe RHS at `q = 0`:
```
∑ p : Fin 2, A (i.succAbove p) j * (-1)^(0 + p) * adjugate M 0 p
  = A 1 0 * (+1) * adjugate M 0 0
  + A 2 0 * (-1) * adjugate M 0 1
  = A 1 0 * A 2 2 + A 2 0 * A 1 2
```

### 1.3 Comparison

- **LHS** (actual `det`): `A 1 0 * A 2 2 − A 1 2 * A 2 0`
- **Recipe RHS** with `(-1)^(q+p)`: `A 1 0 * A 2 2 + A 2 0 * A 1 2`

These **differ by sign on the second term**. The recipe form is FALSE at
`(n, i, j, q) = (2, 0, 0, 0)`.

(Sanity: the LHS−RHS difference `−2 * A 1 2 * A 2 0` is a non-trivial polynomial
in the matrix entries, so the discrepancy is not "0 = 0 in a corner case" — the
identity simply fails generically.)

### 1.4 Cross-check at (n, i, j, q) = (2, 0, 1, 0)

To rule out "i = j is a degenerate edge", repeat with `i = 0, j = 1, q = 0`.

`j.succAbove` for `j.val = 1`: `k.val < 1` true at `k=0` (castSucc → `⟨0, _⟩`),
false at `k=1` (succ → `⟨2, _⟩`). At `q = 0`: `j.succAbove q = ⟨0, _⟩`.
`(j.succAbove q).succAbove` skips index 0: `0 ↦ ⟨1, _⟩`, `1 ↦ ⟨2, _⟩`.

`A.submatrix` at `(i=0, j=1, q=0)` (rows skipped: 0, cols skipped: 0):
| | col 0 (orig col 1) | col 1 (orig col 2) |
|---|---|---|
| row 0 (orig row 1) | `A 1 1` | `A 1 2` |
| row 1 (orig row 2) | `A 2 1` | `A 2 2` |

`det = A 1 1 * A 2 2 − A 1 2 * A 2 1`.

`M` at `(i=0, j=1)`: rows skipped 0, cols skipped 1 (since `j.succAbove` skips 1).
- M(0, 0) = A 1 0, M(0, 1) = A 1 2, M(1, 0) = A 2 0, M(1, 1) = A 2 2

`adjugate M`:
- (0, 0) = A 2 2, (0, 1) = −A 1 2, (1, 0) = −A 2 0, (1, 1) = A 1 0

Recipe RHS at `q = 0` (using j = 1, but recipe sign is `(-1)^(q+p)` which doesn't
reference j):
```
∑ p : Fin 2, A (i.succAbove p) 1 * (-1)^(0 + p) * adjugate M 0 p
  = A 1 1 * (+1) * A 2 2 + A 2 1 * (-1) * (-A 1 2)
  = A 1 1 * A 2 2 + A 2 1 * A 1 2
```

Again differs from LHS `A 1 1 * A 2 2 − A 1 2 * A 2 1` by sign on second term.
**Confirmed: the recipe form is FALSE generically, not just at the i = j diagonal.**

---

## 2. Algebraic derivation of the correct sign σ(q)

### 2.1 Trace through the four steps

Step (c) of S12 PREP §1.2 applies `Matrix.det_eq_sum_mul_adjugate_col` to the n×n
submatrix `A.sub := A.submatrix i.succAbove (j.succAbove q).succAbove` at the
column `j_col : Fin n` where `j_col` is the preimage of `j` under
`(j.succAbove q).succAbove`. This gives:

```
det(A.sub) = ∑ p : Fin n, A.sub p j_col * adjugate(A.sub) j_col p
           = ∑ p : Fin n, A (i.succAbove p) j * adjugate(A.sub) j_col p
```

(second equality by `Matrix.submatrix_apply` + `j_col` definition.)

Step (d) applies `Matrix.adjugate_fin_succ_eq_det_submatrix` (signature per S12 PREP
§3: `adjugate A i j = (-1) ^ ((j : ℕ) + (i : ℕ)) * det (A.submatrix j.succAbove i.succAbove)`):

```
adjugate(A.sub) j_col p
  = (-1)^(p + j_col) * det((A.sub).submatrix p.succAbove j_col.succAbove)
```

By `Matrix.submatrix_submatrix`:
```
(A.sub).submatrix p.succAbove j_col.succAbove
  = A.submatrix (i.succAbove ∘ p.succAbove) ((j.succAbove q).succAbove ∘ j_col.succAbove)
```

By the §1.2 step (a) Fin-level identity (which IS true — independent of the sign issue):
```
(j.succAbove q).succAbove ∘ j_col.succAbove = j.succAbove ∘ q.succAbove
```

(Both sides are functions `Fin (n−1) → Fin (n+1)` skipping exactly `{j, j.succAbove q}`.
See §3.3 below for the verification.)

So:
```
(A.sub).submatrix p.succAbove j_col.succAbove
  = A.submatrix (i.succAbove ∘ p.succAbove) (j.succAbove ∘ q.succAbove)
  = (A.submatrix i.succAbove j.succAbove).submatrix p.succAbove q.succAbove
  = M.submatrix p.succAbove q.succAbove
```

Applying `Matrix.adjugate_fin_succ_eq_det_submatrix` *backward* to the M side:
```
adjugate M q p = (-1)^(p + q) * det(M.submatrix p.succAbove q.succAbove)
```
hence
```
det(M.submatrix p.succAbove q.succAbove) = (-1)^(p + q) * adjugate M q p
```
(using `(-1)^k * (-1)^k = 1`).

### 2.2 Composing the sign

Combining all the above:
```
adjugate(A.sub) j_col p
  = (-1)^(p + j_col) * det((A.sub).submatrix p.succAbove j_col.succAbove)
  = (-1)^(p + j_col) * det(M.submatrix p.succAbove q.succAbove)
  = (-1)^(p + j_col) * (-1)^(p + q) * adjugate M q p
  = (-1)^(2p + j_col + q) * adjugate M q p
  = (-1)^(j_col + q) * adjugate M q p
```

So:
```
det(A.sub) = ∑ p : Fin n, A (i.succAbove p) j * (-1)^(j_col + q) * adjugate M q p
           = (-1)^(j_col + q) * ∑ p : Fin n, A (i.succAbove p) j * adjugate M q p
```

(`(-1)^(j_col + q)` is independent of p, so factors out of the sum.)

### 2.3 The correct sign is σ(q) := (-1)^(j_col(q) + q), constant in p

**Compare to the recipe's claim**:
- Recipe (S12 PREP §1.1 / S4f PREP §2.7+§2.9): sign factor `(-1)^(q + p)` distributed
  inside the sum (varies with p).
- Correct: sign factor `(-1)^(j_col + q)` constant in p (function of q, j only).

The recipe's `(-1)^(q + p)` and the correct `(-1)^(j_col + q)` agree iff
`j_col ≡ p (mod 2)`, which CANNOT hold for all `p ∈ Fin n` simultaneously (since
`p` varies). Hence the recipe statement is **literally false** for generic
matrices and indices (cf. §1.1 + §1.4 numerical witnesses).

### 2.4 The "Not always true!" comment in Block IV traced

S12 PREP §2.2 Block IV (lines on `h_sign` of `(-1)^(p + j_col) = (-1)^(q + p)`)
admits:
> `Not always true! This step requires the parity argument from §1.2 — and the
> conclusion uses (-1)^(j_col + q) = (-1)^(p + q) * (-1)^(p + q) = 1, not the
> naive parity equality.`

The S12 PREP author noticed `h_sign` is not provable as stated. Their proposed
"resolution" (`(-1)^(j_col + q) = (-1)^(p + q) * (-1)^(p + q) = 1`) is muddled —
`(-1)^(p+q) * (-1)^(p+q) = 1` is correct, but that means
`(-1)^(j_col + q) = 1` is required, i.e., `j_col + q` even. This holds case-by-case
only in the `q < j` AND `q even, j_col even` etc. corners, NOT generically.

**Root cause**: the issue is in the STATEMENT of `submatrix_chain` in §1.1, not
in Block IV. Block IV is trying to reconcile a correct intermediate (-1)^(p + j_col)
times a correct (-1)^(p + q) (from the M-side adjugate inversion) against a
WRONG target form (-1)^(q + p) in §1.1. No sign-collection algebra can fix a
wrong target.

---

## 3. Verification that the §2.9 outer skeleton closes with corrected σ(q)

### 3.1 The outer chain

S4f PREP §2.9 (the ~58-LOC paste-ready skeleton) has the closing block:
```lean
  rw [det_via_pivot]
  simp_rw [inner_unfold, submatrix_chain]
  field_simp [hM_ne]
  ring
```

After `det_via_pivot`:
```
A.det = A i j * ((-1)^(i+j) * M.det)
      + ∑ q : Fin n, A i (j.succAbove q) * adjugate A (j.succAbove q) i
```

After `inner_unfold` (which substitutes
`adjugate A (j.succAbove q) i = (-1)^(i + j.succAbove q) * det(A.submatrix ...)`):
```
A.det = A i j * ((-1)^(i+j) * M.det)
      + ∑ q, A i (j.succAbove q) * (-1)^(i + j.succAbove q) *
          det(A.submatrix i.succAbove (j.succAbove q).succAbove)
```

After substituting the CORRECTED `submatrix_chain` (per §2 above, factor σ(q) outside
sum-over-p):
```
A.det = A i j * ((-1)^(i+j) * M.det)
      + ∑ q, A i (j.succAbove q) * (-1)^(i + j.succAbove q) * σ(q) *
          ∑ p, A (i.succAbove p) j * adjugate M q p
```

### 3.2 Required relation for the outer to close

After Step 8's `field_simp [hM_ne]` + `ring`, the target identity
`qdetN_step A i j M⁻¹ = (-1)^(i+j) * (A.det / M.det)` reduces to

```
A.det / M.det = (-1)^(i+j) * [ A i j - (1/M.det) * ∑ p ∑ q
                                A i (j.succAbove q) * adjugate M q p * A (i.succAbove p) j ]
```

(after carrying through `qdetN_step` and `qdetF` unfolds + `M_inv_apply`). Plug in
the corrected expansion of `A.det / M.det` (from §3.1 divided by M.det):

```
A.det / M.det = A i j * (-1)^(i+j)
              + (1/M.det) * ∑ q, A i (j.succAbove q) * (-1)^(i + j.succAbove q) *
                  σ(q) * ∑ p, A (i.succAbove p) j * adjugate M q p
```

Multiply both sides by `(-1)^(i+j)` (`(-1)^(2(i+j)) = 1`):

```
(-1)^(i+j) * A.det / M.det
  = A i j + (-1)^(i+j) * (1/M.det) * ∑ q ∑ p
      A i (j.succAbove q) * (-1)^(i + j.succAbove q) * σ(q) *
      A (i.succAbove p) j * adjugate M q p
```

Comparing to the target form:
```
A i j - (1/M.det) * ∑ p ∑ q A i (j.succAbove q) * adjugate M q p * A (i.succAbove p) j
```

Match coefficient of `(1/M.det) * A i (j.succAbove q) * adjugate M q p * A (i.succAbove p) j`:
```
-1 = (-1)^(i+j) * (-1)^(i + j.succAbove q) * σ(q)
   = (-1)^(2i + j + j.succAbove q) * σ(q)
   = (-1)^(j + j.succAbove q) * σ(q)
```

Hence:
```
σ(q) = -1 / (-1)^(j + j.succAbove q)
     = (-1)^(j + j.succAbove q + 1)              (since (-1)^k is self-inverse)
```

### 3.3 Closed-form σ(q) (case split on q.val < j.val)

**Case A: q.val < j.val.** By `Fin.succAbove_def`, `j.succAbove q = q.castSucc`,
so `(j.succAbove q).val = q.val`. Plug in:
```
σ(q) = (-1)^(j + q + 1)
```

**Case B: q.val ≥ j.val.** `j.succAbove q = q.succ`, so `(j.succAbove q).val = q.val + 1`:
```
σ(q) = (-1)^(j + q + 1 + 1) = (-1)^(j + q + 2) = (-1)^(j + q)
```

**Equivalently, in `j_col` terms** (per §2.2 derivation):
- Case A: `j_col.val = j.val − 1`, so `(j_col + q).val = j + q − 1`, and
  `(-1)^(j_col + q) = (-1)^(j + q − 1) = (-1)^(j + q + 1)`. ✓
- Case B: `j_col.val = j.val`, so `(j_col + q).val = j + q`, and
  `(-1)^(j_col + q) = (-1)^(j + q)`. ✓

So the two forms agree, modulo the integer-vs-`Nat`-subtraction wrap. **The
algebraically-cleanest closed form is** `σ(q) = (-1)^(j + (j.succAbove q).val + 1)`
or equivalently `σ(q) = −(-1)^(j + (j.succAbove q).val)`.

### 3.4 Sanity-check at (n, i, j, q) = (2, 0, 0, 0) again

`j = 0`, `q = 0`, `q.val = 0 ≥ j.val = 0` so Case B. `σ(0) = (-1)^(0 + 0) = +1`.

LHS det at q=0 (from §1.1): `A 1 0 * A 2 2 − A 1 2 * A 2 0`.

Corrected sum `σ(0) * ∑ p A (i.succAbove p) j * adjugate M 0 p` with `σ(0) = +1`:
```
A 1 0 * A 2 2 + A 2 0 * (−A 1 2)
  = A 1 0 * A 2 2 − A 1 2 * A 2 0   ✓ matches LHS det.
```

(Cross-check at i=0, j=1, q=0: Case A, `σ(0) = (-1)^(1+0+1) = +1`. LHS det
`= A 1 1 * A 2 2 − A 1 2 * A 2 1`. Corrected sum:
`A 1 1 * (+1) * A 2 2 + A 2 1 * (+1) * (−A 1 2) = A 1 1 * A 2 2 − A 1 2 * A 2 1`. ✓)

(Cross-check at i=0, j=0, q=1: Case B (1 ≥ 0), `σ(1) = (-1)^(0+1) = −1`. LHS det
at q=1: rows skipped 0, cols skipped `j.succAbove 1 = 2`, so the submatrix has
entries A(1,0), A(1,1), A(2,0), A(2,1) and `det = A(1,0)*A(2,1) − A(1,1)*A(2,0)`.
adjugate M at (1, _): `(1,0) = −A 2 1`, `(1,1) = A 1 1`. Corrected sum:
`σ(1) * (A 1 0 * (−A 2 1) + A 2 0 * A 1 1) = (−1) * (−A 1 0 * A 2 1 + A 2 0 * A 1 1)
 = A 1 0 * A 2 1 − A 2 0 * A 1 1`. ✓)

The corrected σ(q) closes the outer skeleton on all three witnesses.

### 3.5 The Fin-level identity (`j.succAbove q).succAbove ∘ j_col.succAbove = j.succAbove ∘ q.succAbove`)

This identity (used in Step (d) of the §2 derivation; same as Block IV `h_col_eq`)
is NOT affected by the sign issue. Both compositions are functions
`Fin (n−1) → Fin (n+1)` that skip exactly `{j, j.succAbove q}` as their image,
applied to the same domain in the same order. Verification proceeds by
`funext k` + `Fin.succAbove_def` unfold + a case split on the order of `k.val`,
`j_col.val`, `q.val`. This is the SAME ~5-LOC block that S12 PREP §2.2 Block IV
proposed (modulo the now-redundant `h_sign` deletion); see §5 below for the
revised Block IV.

---

## 4. Two equivalent corrected statements

The corrected `submatrix_chain` can be stated either with σ(q) factored out
(cleaner for the outer `ring` step) or distributed (closer to the original form,
but the constant-in-p factor must still be made explicit):

### 4.1 Form 1 — σ(q) factored out (recommended for Block IV)

```lean
private lemma submatrix_chain {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1)) (q : Fin n)
    (M : Matrix (Fin n) (Fin n) F := A.submatrix i.succAbove j.succAbove) :
    det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
      (-1 : F) ^ ((j : ℕ) + (j.succAbove q : ℕ) + 1) *
        ∑ p : Fin n, A (i.succAbove p) j * adjugate M q p := by
  ...
```

(Use `(-1)^(j + (j.succAbove q : ℕ) + 1)` to avoid the `j_col` case-split appearing
in the statement; the case-split goes inside the body. Notation: the `(j.succAbove q : ℕ)`
is the underlying nat coercion of a `Fin (n+1)`.)

### 4.2 Form 2 — σ(q) distributed (closer to the original recipe shape)

```lean
private lemma submatrix_chain {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1)) (q : Fin n)
    (M : Matrix (Fin n) (Fin n) F := A.submatrix i.succAbove j.succAbove) :
    det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
      ∑ p : Fin n, A (i.succAbove p) j *
        ((-1 : F) ^ ((j : ℕ) + (j.succAbove q : ℕ) + 1) * adjugate M q p) := by
  ...
```

These are propositionally equal by `Finset.sum_const_mul` / `mul_comm`. **Form 1 is
preferred** because:
1. The outer §2.9 skeleton uses `simp_rw [submatrix_chain]` to substitute LHS-by-RHS,
   and Form 1's RHS is structurally `c * ∑ p ...` which composes cleanly with the
   outer `field_simp + ring` pipeline.
2. Block IV's tactic body has one constant factor to track, not n different ones.
3. If we later need a generalisation (S5 mutual recursion, S6 cramer-rule-nxn), the
   factored form makes the σ(q) algebra reusable across calls.

---

## 5. Revised Block I–IV plan (Block IV simplifies)

The revised plan replaces S12 PREP §2.2 Block I–IV. **Total budget remains ~30–45 LOC**
for the `submatrix_chain` private lemma body. The main simplification is that
**Block IV's `h_sign` sub-sorry goes away** — the sign collection becomes a single
`(-1)^(...)` rewrite identity with no parity case-split required.

### 5.1 Block I (unchanged from S12 PREP §2.2) — define j_col, ≈8 LOC

```lean
-- Define j_col : Fin n via a case split on (q : ℕ) < (j : ℕ).
let j_col : Fin n :=
  if hj : (q : ℕ) < (j : ℕ) then
    ⟨(j : ℕ) - 1, by
      have hj_pos : 0 < (j : ℕ) := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
      have hjn : (j : ℕ) - 1 < n := by omega
      exact hjn⟩
  else
    ⟨(j : ℕ), by
      have hjn : (j : ℕ) < n + 1 := j.isLt
      have hjqn : ¬ (q : ℕ) < (j : ℕ) := hj
      have : (j : ℕ) ≤ (q : ℕ) := Nat.le_of_not_lt hjqn
      have hqn : (q : ℕ) < n := q.isLt
      omega⟩
have h_jcol : (j.succAbove q).succAbove j_col = j := by
  rcases Nat.lt_or_ge (q : ℕ) (j : ℕ) with hqj | hqj
  · -- q < j case: j_col = j - 1, (j.succAbove q) = q.castSucc with val = q
    simp only [j_col, dif_pos hqj, Fin.succAbove_def, ...]
    omega  -- or split_ifs + omega
  · -- q ≥ j case: j_col = j, (j.succAbove q) = q.succ with val = q + 1
    simp only [j_col, dif_neg (Nat.not_lt.mpr hqj), Fin.succAbove_def, ...]
    omega  -- or split_ifs + omega
```

### 5.2 Block II (unchanged from S12 PREP §2.2) — det column-expand, ≈8 LOC

```lean
have h_main : det (A.submatrix i.succAbove (j.succAbove q).succAbove) =
    ∑ p : Fin n,
      A (i.succAbove p) j * adjugate (A.submatrix i.succAbove (j.succAbove q).succAbove) j_col p := by
  rw [Matrix.det_eq_sum_mul_adjugate_col _ j_col]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Matrix.submatrix_apply, h_jcol]
rw [h_main]
```

### 5.3 Block III (revised) — adjugate expand + submatrix flatten, ≈10 LOC

```lean
refine Finset.sum_congr rfl (fun p _ => ?_)
-- Goal: A (i.succAbove p) j * adjugate (A.sub) j_col p
--     = A (i.succAbove p) j * ((-1)^σ(q) * adjugate M q p)
-- (where the outer factor σ(q) is the constant outside the sum after factoring)
congr 1
-- Goal: adjugate (A.sub) j_col p = (-1)^σ(q) * adjugate M q p ...

-- NOTE: For Form 1 (σ outside sum), Block II's h_main needs to factor σ outside:
--   det(A.sub) = σ(q) * ∑ p, A (i.succAbove p) j * adjugate M q p
-- Achieve this by deferring the σ extraction to Block IV (after the per-p simplification
-- collapses), then applying Finset.mul_sum.

rw [Matrix.adjugate_fin_succ_eq_det_submatrix _ j_col p]
-- LHS becomes (-1)^(p + j_col) * det(A.sub.submatrix p.succAbove j_col.succAbove)
simp only [Matrix.submatrix_submatrix]
-- LHS now (-1)^(p + j_col) * det(A.submatrix (i.succAbove ∘ p.succAbove)
--                                            ((j.succAbove q).succAbove ∘ j_col.succAbove))
```

### 5.4 Block IV (revised, simpler — h_sign removed) — Fin-comp identity + clean factor, ≈10 LOC

The KEY new observation: after Block III, the LHS sign is `(-1)^(p + j_col)`. After
the `h_col_eq` rewrite (which equates the doubly-skipped A-submatrix with the
once-skipped M-submatrix), the M-side `adjugate_fin_succ_eq_det_submatrix` (applied
backward) introduces a second sign `(-1)^(p + q)`. The two signs **combine** to
`(-1)^(j_col + q)`, which is independent of p — so it factors out via
`Finset.mul_sum`.

```lean
-- Block IV: Fin-comp identity + clean factor
have h_col_eq : (j.succAbove q).succAbove ∘ j_col.succAbove =
                j.succAbove ∘ q.succAbove := by
  funext k
  rcases Nat.lt_or_ge (q : ℕ) (j : ℕ) with hqj | hqj
  · -- q < j case
    simp only [Function.comp_apply, j_col, dif_pos hqj, Fin.succAbove_def, ...]
    -- ~3 LOC of omega + split_ifs
    sorry  -- placeholder: ~3 LOC
  · -- q ≥ j case
    simp only [Function.comp_apply, j_col, dif_neg (Nat.not_lt.mpr hqj), Fin.succAbove_def, ...]
    sorry  -- placeholder: ~3 LOC
rw [show A.submatrix (i.succAbove ∘ p.succAbove)
        ((j.succAbove q).succAbove ∘ j_col.succAbove)
      = A.submatrix (i.succAbove ∘ p.succAbove) (j.succAbove ∘ q.succAbove) from by
    rw [h_col_eq], ← Matrix.submatrix_submatrix]
-- LHS now (-1)^(p + j_col) * det((A.submatrix i.succAbove j.succAbove).submatrix p.succAbove q.succAbove)
--       = (-1)^(p + j_col) * det(M.submatrix p.succAbove q.succAbove)
rw [show det (M.submatrix p.succAbove q.succAbove) = (-1)^((p : ℕ) + (q : ℕ)) * adjugate M q p by
  have := Matrix.adjugate_fin_succ_eq_det_submatrix M q p
  -- this: adjugate M q p = (-1)^(p + q) * det(M.submatrix p.succAbove q.succAbove)
  linarith  -- or `have h := this; linear_combination (-1)^(p+q) * (-this) ...`
  -- actually: simpler is `field_simp; ring` or `rw [this]; ring`
  ]
-- LHS now (-1)^(p + j_col) * (-1)^(p + q) * adjugate M q p
--       = (-1)^(2p + j_col + q) * adjugate M q p
--       = (-1)^(j_col + q) * adjugate M q p
rw [show ((-1 : F)^((p:ℕ) + (j_col:ℕ)) * (-1)^((p:ℕ) + (q:ℕ)) : F)
      = (-1)^((j_col:ℕ) + (q:ℕ)) by
  rw [← pow_add]; ring_nf
  -- Or: use Nat.two_mul_self or Nat.add_self_div_two or sign-identity (-1)^(2k) = 1
  ]
-- Now factor σ(q) := (-1)^(j_col + q) out of the sum:
-- Goal: A (i.succAbove p) j * ((-1)^(j_col + q) * adjugate M q p)
--     = (-1)^(j_col + q) * (A (i.succAbove p) j * adjugate M q p)
ring
```

### 5.5 Wrap (≈5 LOC) — pull σ(q) outside, apply Finset.mul_sum

```lean
-- After Blocks I–IV, the goal of the `private lemma submatrix_chain` is:
--   det(A.sub) = (-1)^(j_col + q) * ∑ p, A (i.succAbove p) j * adjugate M q p
-- Equivalently, with σ in closed form:
--   det(A.sub) = (-1)^(j + j.succAbove q + 1) * ∑ p, A (i.succAbove p) j * adjugate M q p
-- (matching Form 1 of §4.1)
rcases Nat.lt_or_ge (q : ℕ) (j : ℕ) with hqj | hqj
· -- j_col = j - 1, (j.succAbove q).val = q
  simp only [j_col, dif_pos hqj]
  ring  -- (-1)^(j - 1 + q) = (-1)^(j + q - 1) = (-1)^(j + q + 1) [since (-1)^-2 = 1]
· simp only [j_col, dif_neg (Nat.not_lt.mpr hqj)]
  ring  -- (-1)^(j + q) = (-1)^(j + (q+1) + 1) [arithmetic in ℕ]
```

(The case-split at the wrap step handles the `j_col` ↔ `(j + (j.succAbove q : ℕ) + 1)`
conversion. Alternatively, define σ(q) explicitly inside the lemma body and avoid
the wrap.)

**Total revised Block I–IV LOC budget**: ~40 LOC (slightly tighter than S12 PREP §2.2's
~30–45 LOC range, BECAUSE Block IV's `h_sign` sub-sorry goes away).

### 5.6 The outer §2.9 skeleton adjustments

The outer skeleton at S4f PREP §2.9 used `submatrix_chain` as a `simp_rw` target.
With Form 1 (σ outside), the rewrite is:

```lean
simp_rw [inner_unfold, submatrix_chain]  -- as in §2.9; works with Form 1 too
field_simp [hM_ne]
ring
```

Crucial check: does `simp_rw [submatrix_chain]` correctly produce the form
`(-1)^(j + j.succAbove q + 1) * ∑ p, ...` for each `q ∈ Fin n` inside the outer
`∑ q ...`? Yes — `simp_rw` iterates per-binder-occurrence and the new RHS has
no free binder collision. (Verify post-paste by inspecting the goal between
`simp_rw` and `field_simp`.)

The `ring` at the end will close the polynomial identity once the sign collection
`(-1)^(i + j.succAbove q) * (-1)^(j + j.succAbove q + 1) = -(-1)^(i + j)` is applied
(verified §3.2 above; `ring` handles `(-1)^k` algebra via Nat-exponent expansion).

**Potential pitfall (PR #19072 fix-class 1, M risk)**: `ring` may not auto-expand
`(-1)^(a + b)` if the exponent contains a `Fin.val` coercion that isn't normalised.
Mitigation: insert `simp only [Nat.add_comm, Nat.add_assoc, pow_add]` before
`field_simp` to normalise the exponent forms, then `field_simp [hM_ne]; ring`.

---

## 6. ACT-readiness gate refresh post-S15 + S15+1 ACT picker checklist

### 6.1 Updated gate (revised from S14 PREP §5)

| Item | Status (this S15 PREP) | Source | Δ from S14 |
|------|------------------------|--------|------------|
| 5 S12 PREP bearers | ✓ | S12 §3 | unchanged |
| 4 S13 PREP-2 bearers (was ⚠) | ✓ | S13 PREP-2 §2 | unchanged |
| Lake SHA stable | ✓ | 0 drift since S11 (7 PREPs at same SHA incl. this one) | unchanged |
| Slug file builds clean at HEAD | ✓ | S10 build-verify (3060 jobs) | unchanged |
| Sign exponent convention (outer) locked | ✓ | S4 PR #19142 | unchanged |
| **Sub-sorry tactic plan locked** | **✗ → ✓ (THIS S15)** | **S15 PREP §5 (revised Blocks I–IV)** | **S12 PREP §2.2 had wrong σ(q); corrected here** |
| **submatrix_chain statement correct** | **✗ → ✓ (THIS S15)** | **S15 PREP §4 (Form 1)** | **NEW gate row — was implicit-OK before S15 found gap** |
| Docker daemon responsive | **✗** | Still hung this cycle (7.5+ h cumulative) | unchanged |
| Host disk ≥ 5 Gi avail | ⚠ → ⚠ | 5.4 Gi avail (−1.1 Gi since S14 PREP; still above floor) | degrading |

**Gate**: GREEN for documentation prerequisites (7/9 ✓); RED for infra (Docker); AMBER on disk
(degrading but above floor). S15+1 ACT proper (paste the revised Block I–IV + outer
§2.9 skeleton + meta deltas) **remains correctly deferred** to the next
post-Docker-recovery picker.

### 6.2 S15+1 ACT next-picker checklist (8 steps, supersedes S14 PREP §5 7-step)

Note: step count rises 7 → 8 because this S15 PREP introduces a NEW PREP-side item
(Step 5: the explicit `(-1)^(2p + j_col + q) = (-1)^(j_col + q)` algebraic simplification
inside Block IV's wrap). Steps 1–4 carry forward; steps 5–8 are renumbered.

1. **Confirm Docker daemon healthy** (`timeout 10 docker info` returns `Server:` body;
   `docker ps` works).
2. **Adopt Option B (private lemma)** per S12 PREP §5: declare
   `private lemma submatrix_chain` above `qdetN_step_eq_qdetF`.
   **Use the CORRECTED statement (Form 1 per S15 PREP §4.1)** — NOT the S12 PREP §1.1
   or S4f PREP §2.7 form.
3. **Paste the §2.9 outer skeleton** with `submatrix_chain` reference replaced by
   the private-lemma name. **No structural change to the outer skeleton** — the
   substitution form is identical; only the inner `(-1)^(...)` factor changes.
4. **Implement Block I** per S15 PREP §5.1 (`j_col` definition via `Fin.cases`;
   `h_jcol : (j.succAbove q).succAbove j_col = j` via case-split). Budget ~8 LOC.
5. **Implement Block II** per S15 PREP §5.2 (`det_eq_sum_mul_adjugate_col` + entry
   simplification). Budget ~8 LOC.
6. **Implement Block III + IV combined** per S15 PREP §5.3 + §5.4 + §5.5
   (adjugate forward+backward + submatrix_submatrix simp + h_col_eq Fin-comp identity
   + sign collection `(-1)^(j_col + q)` factoring + wrap to closed-form σ(q)).
   Budget ~25 LOC.
7. **Drop S4f PREP §4 sanity-check `example` blocks** at `(i,j) = (0,0)` and `(0,1)`
   (~24 LOC; verified algebraically in S12 PREP §4.2 and re-verified at three witnesses
   in S15 PREP §3.4).
8. **Docker-verify** via `./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01`.
   Forecast: 3060 → 3060 jobs (warm cache, ~60–180s per iter).
   **Sorry count outcome**: 1 → 0 if Blocks I–IV fully discharge; 1 → 1 if Block I
   or h_col_eq partially closes (S15+2 follow-up scope).

Estimated S15+1 ACT wall time (when Docker is healthy): 60–90 min (4–6 Docker iters
at ~60–180s each in warm cache; the `h_col_eq` Fin-arithmetic sub-sorry inside Block
IV may need 1–2 extra iters to settle).

---

## 7. Risk inventory and alternative paths

### 7.1 R1 — `h_col_eq` Fin-arithmetic identity may need more LOC than budgeted

**Risk**: §5.4's `h_col_eq` (the identity
`(j.succAbove q).succAbove ∘ j_col.succAbove = j.succAbove ∘ q.succAbove`) requires
a `funext k` + case-split on `k.val` vs `j_col.val` vs `q.val` ordering. The
~3 LOC estimate per case (6 LOC total) may underestimate.

**Mitigation**: this is a **genuinely true** Fin-identity (verified by hand in §2 +
the §3.4 witnesses). If `omega` + `split_ifs` doesn't close it, manually unfold
`Fin.succAbove_def` at both positions and finish with `omega`. Worst case +10–15 LOC.

**Fallback**: if `h_col_eq` resists tactic-discharge, prove it as a stand-alone
`private lemma succAbove_skip_chain` above `submatrix_chain` — gives a separate
unit-of-work for S15+2 ACT (or for S5 mutual recursion to reuse).

### 7.2 R2 — Sign-collection `(-1)^(2p + j_col + q) = (-1)^(j_col + q)` may not autoclose

**Risk**: §5.4's last `rw [show ... by ring]` block relies on `ring` simplifying
`(-1)^(2p) = 1`. In Lean 4 / Mathlib v4.26.0, `(-1 : F)^k` for `k : ℕ` does not
automatically reduce via `ring` unless an intermediate step exposes `(-1)^(2p) = ((-1)^2)^p = 1^p = 1`.

**Mitigation**: replace `ring` with `rw [show (2 : ℕ) * p = (p : ℕ) + (p : ℕ) by ring, pow_add,
neg_one_pow_mul_self, one_mul]` — but `neg_one_pow_mul_self` may not exist by that
exact name; check `neg_one_pow_two_eq_one` or `Odd.neg_one_pow`.

**Fallback**: extract a lemma `(-1 : F)^(2*p) = 1` at the top of the file (or use
`Even.neg_one_pow ⟨p, two_mul p⟩`). +2-3 LOC.

### 7.3 R3 — `field_simp [hM_ne]; ring` at outer Step 8 may produce residual `(-1)^k`

**Risk**: per PR #19072 fix-class 5 (L), `field_simp` may close more goals than
expected and leave a residue or fail on the `(-1)^(...)` exponent. The new `σ(q)`
factor introduces an additional `(-1)^(j + (j.succAbove q).val + 1)` per q-term.

**Mitigation**: insert `simp only [pow_add, Nat.add_comm]` before `field_simp` to
canonicalise exponents. If `field_simp` leaves residue, try `field_simp; ring_nf`
without the explicit `[hM_ne]` and see if it auto-derives.

**Fallback**: if `field_simp + ring` chokes, fall back to S4f PREP §2.8 Option B
manual multiply-through. +5–8 LOC.

### 7.4 R4 — Drift between S15 sign correction and S5 mutual recursion's expected form

**Risk**: S5 (later iteration) will build `qdetN ↔ qdetN_inv` mutual recursion and
will likely re-use `submatrix_chain` (or a generalisation) for the recursive case.
If S5 expects the original `(-1)^(q+p)` form, S15's correction may surface a
downstream mismatch.

**Mitigation**: S5 will be re-planned from scratch (per knowledge.md S5 = NC-DEFINE
mutual recursion; no current code commits to a sign form). The correct σ(q) factor
should be carried forward in the S5 mutual-recursion `pre-condition` field.

**Action**: leave a note in state.md head pointing future S5 PREP authors at S15
PREP §3 + §4 for the canonical σ(q) factor. (See §8 below.)

### 7.5 R5 — Latent gap discovered in PREP-chain raises confidence in the rest of the recipe by ≤ ε

**Risk**: this S15 finding shows S4f PREP + S12 PREP got a sign wrong (a non-trivial
algebraic detail). Could there be MORE latent gaps in the §2.9 skeleton (Steps 1–6)?

**Mitigation**: re-audited Steps 1–6 of §2.9 quickly during this PREP:
- Step 1 `M_inv_apply`: `(M⁻¹) q p = (M.det)⁻¹ * adjugate M q p` — true by `Matrix.inv_def`
  (S13 PREP-2 §2 bearer 7). No sign issue.
- Step 2 `qdetN_step_expand`: just `unfold qdetN_step qdetF; simp_rw [M_inv_apply]`.
  Pure unfolding.
- Step 3 `det_via_pivot`: column-expansion of A.det along column j via
  `det_eq_sum_mul_adjugate_row` (S12 PREP §3 bearer 2 — note name mismatch vs §2.9
  text "row" but signature `(-1)^(i+j)` matches). Need to verify column-vs-row in
  S15+1 ACT — but the sign exponent `(i + j)` on the pivot term is correct per
  S4 statement-fix PR #19142.
- Step 4 `pivot_unfold`: `adjugate A j i = (-1)^(i+j) * M.det` via
  `adjugate_fin_succ_eq_det_submatrix`. Correct.
- Step 5 `kne_sum_reindex`: combined into Step 3 (per S4f PREP §2.5 Option B).
- Step 6 `inner_unfold`: `adjugate A (j.succAbove q) i = (-1)^(i + j.succAbove q) *
  det(A.submatrix i.succAbove (j.succAbove q).succAbove)` via
  `adjugate_fin_succ_eq_det_submatrix`. Sign exponent matches verbatim.

**Confidence**: Steps 1–6 + Step 8 (`field_simp + ring`) appear correctly stated.
Only Step 7 (`submatrix_chain`) had the latent sign gap that this S15 catches.
Residual risk: low (≤ 10% probability that another sign bug lurks elsewhere in
the outer skeleton, given the §3.4 three-witness numerical confirmation of the
corrected σ(q)).

### 7.6 Alternative path P1: S4d-style direct expansion of M⁻¹ q p as det(M.submatrix)

S4d PREP §2 proposed an ALTERNATIVE that bypasses `submatrix_chain` entirely:
keep `M⁻¹ q p = (M.det)⁻¹ * (-1)^(p+q) * det(M.submatrix p.succAbove q.succAbove)`
expanded throughout, then directly identify the doubly-skipped A-submatrix with
the once-skipped M-submatrix via `submatrix_submatrix` + `h_col_eq` — avoiding the
intermediate `adjugate M q p` notation.

**Pros**: skips the `(-1)^(p + j_col)` sign-from-adjugate step entirely. Fewer
sign-collection rewrites. Cleaner audit trail.

**Cons**: requires keeping `(M.det)⁻¹` distributed through the sum, which couples
the `field_simp` cleanup to the per-term structure. PR #19072 fix-class 4 (H)
specifically warned `field_simp` no longer auto-derives `_ ≠ 0` from compound
hypotheses — the `(M.det)⁻¹` form is harder to discharge.

**Recommendation**: stick with the §2.9 + corrected `submatrix_chain` path
(this S15 PREP). P1 is a fallback if S15+1 ACT's `field_simp + ring` chokes.

### 7.7 Alternative path P2: skip `submatrix_chain` lemma, inline expansion

Per S12 PREP §5 Option A: keep `submatrix_chain` as an inline `have` rather than
a `private lemma`. Saves one top-level name. But: makes the `(-1)^(...)` algebra
nested inside the outer `qdetN_step_eq_qdetF` proof, harder to debug per-step.

**Recommendation**: do NOT switch to P2. The Option B (private lemma) decision in
S12 PREP §5 is correct and the corrected statement of §4.1 is cleaner to isolate.

### 7.8 Alternative path P3: prove `submatrix_chain` via `det_eq_sum_mul_adjugate_row` on A directly

Per S12 PREP §2.4. Avoids the `j_col` reindex by expanding `det(A)` row-wise and
splitting off the `(i.succAbove p, j)` rows. **Not viable** for this LHS — we need
to expand the n×n doubly-skipped submatrix's det, not A's det. P3 is a path for
the OUTER `det_via_pivot` step (Step 3), already adopted.

---

## 8. Conflict-free guarantees + acceptance criteria + references

### 8.1 What this S15 PREP does NOT do

- **NO** Lean edits (0 file changes in `proofs/`).
- **NO** `meta.json` edits (gallery-data stays at HEAD; mechanic territory for line/sorry counts).
- **NO** `problem.md` edits (no problem-definition change).
- **NO** `knowledge.md` edits (insights propagated to JSON `knowledge.insights` only).
- **NO** `lake-manifest.json` edits (Mathlib pin unchanged at `2df2f0150c...`).
- **NO** sibling-slug edits (this is a Cramer-OQ-01-OQ-02-OQ-01-OQ-01-specific finding;
  no `cramers-rule-oq-02-oq-02` / `cramers-rule-oq-03-oq-03` overlap).
- **NO** parent-file edits (`Proofs/CramersRuleOQ01OQ02OQ01.lean` etc. are unaffected
  bearer pins).
- **NO** changes to `leanFiles[i]` array entries (mechanic territory — note that
  `leanFiles[4]` for `CramersRuleOQ01OQ02OQ01OQ01.lean` shows `lineCount: 275` but
  actual file is 293 LOC; this drift is pre-existing per MEMORY pattern guidance to
  not self-edit `leanFiles[]`). Handoff package for this drift: see §8.4 below.

### 8.2 Race-safety

- **0 open PRs** for `cramers-rule-oq-01-oq-02-oq-01-oq-01` at cycle start
  (verified via `gh -R rjwalters/lean-genius pr list --state open --search "cramers-rule-oq-01-oq-02-oq-01-oq-01 in:title"` → empty).
- **0 sibling `iter-<TS>` branches** on origin for this slug.
- **Lake SHA stable** since S11 STATE-SYNC (7 PREPs at same SHA now).
- **No parent-file work-in-progress**: `CramersRuleOQ01OQ02OQ01OQ01.lean` clean at HEAD,
  no recent mechanic PRs in flight on this file.
- This PREP touches 3 files only: NEW session memo + state.md head replace
  (preserves Sessions 1–14) + JSON delta. Conflict-free under concurrent
  branches.

### 8.3 Iteration math

- S14 PREP closed at iter 14.
- This S15 PREP: iter 14 → **15**.
- S15+1 ACT (post-Docker-recovery): iter 15 → 16.
- S15+2 STATE-SYNC (post-ACT consolidation): iter 16 → 17.
- attemptCounts.total: 12 → 13.

### 8.4 LeanFiles drift handoff (informational only — NOT touched in this PREP)

For the mechanic / future picker reviewing this slug: `leanFiles[4]` entry for
`Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` shows `lineCount: 275, theoremCount: 9,
defCount: 2, sorryCount: 1` but the actual file at `origin/main` has 293 LOC.
Difference accounts for the S4 statement-correction landing (PR #19142) +
docstring growth.

Ready-to-paste diff for a future mechanic PR:
```json
    {
      "path": "Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean",
      "filename": "CramersRuleOQ01OQ02OQ01OQ01.lean",
-     "lineCount": 275,
-     "theoremCount": 9,
+     "lineCount": 293,
+     "theoremCount": 9,
      "axiomCount": 0,
      "defCount": 2,
      "sorryCount": 1,
      "isAristotle": false,
      "githubUrl": "..."
    },
```

(MEMORY guidance: do NOT self-edit `leanFiles[]` from a researcher PREP — mechanic
territory + auto-populated by `enrich-research.ts`. Manual edits risk clobber.
This block is for the next mechanic batch that touches Cramer-family JSON drift.)

### 8.5 Acceptance criteria for this S15 PREP PR

- [x] 3 files changed exactly: NEW session memo + state.md head + research JSON
- [x] 0 Lean edits
- [x] 0 axiom / 0 sorry change (preserved)
- [x] Numerical refutation at n=2 documented with explicit witness (§1)
- [x] Algebraic derivation of σ(q) traced through Steps (a)–(d) (§2)
- [x] Outer §2.9 skeleton closure verified at three numerical witnesses (§3.4)
- [x] Two corrected statements presented (Form 1 + Form 2) with recommendation (§4)
- [x] Revised Block I–IV plan with simplification (no h_sign sub-sorry) (§5)
- [x] ACT-readiness gate refreshed (now 7/9 GREEN + 1 RED INFRA + 1 AMBER disk) (§6.1)
- [x] S15+1 ACT picker checklist (8 steps) documented (§6.2)
- [x] Risk inventory R1–R5 + alternative paths P1–P3 (§7)
- [x] Conflict-free guarantees verified (§8.2)
- [x] LeanFiles drift handoff (informational, NOT touched here) (§8.4)

### 8.6 References

- **S4** statement-fix PR #19142 (researcher-12, 2026-05-14) — corrected
  `qdetN_step_eq_qdetF` RHS to carry `(-1)^(i+j)` factor.
- **S4d PREP** session memo (researcher-1, 2026-05-13) — proposed direct-adjugate
  path via `adjugate_fin_succ_eq_det_submatrix` + sign-collection from M⁻¹.
- **S4e PREP** session memo (researcher-9, 2026-05-13) — 8-step skeleton sketch
  (Step 7 = submatrix_chain).
- **S4f PREP** session memo (researcher-12, 2026-05-15) — paste-ready §2.9 outer
  skeleton + Step 7 `submatrix_chain` with `(-1)^(q+p)` sign **(now corrected
  here to `(-1)^(j+(j.succAbove q)+1) = (-1)^(j_col + q)`)**.
- **S11 STATE-SYNC** PR (researcher-X, 2026-05-16T04:35Z) — post-drainwave
  consolidation; locked Mathlib pin at `2df2f0150c...`.
- **S12 PREP** PR (researcher-11, 2026-05-16T04:35Z) — Block I–IV tactic plan,
  S5 Option B (private lemma) recommendation, j_col case-split, **Block IV
  `h_sign` "Not always true!" comment that this S15 traces to a §1.1 root cause**.
- **S13 PREP-2** PR #19579 (researcher-4, 2026-05-16T13:52:16Z) — 4 ⚠-deferred
  bearer live-pinning at unchanged Mathlib SHA.
- **S14 PREP** PR #19617 (researcher-4, 2026-05-16T14:33:09Z) — JSON-catchup
  absorbing S13 PREP-2 + Docker B1 reaffirm + stranded-branch reaffirm.
- **THIS S15 PREP** (researcher-6, 2026-05-16T15:30:00Z) — `submatrix_chain` sign
  correction (latent correctness gap surfaced before S15+1 ACT).
- **Bearer pins at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**:
  `Matrix.adjugate_fin_succ_eq_det_submatrix` (Adjugate.lean:362),
  `Matrix.det_eq_sum_mul_adjugate_row` (Adjugate.lean:401),
  `Matrix.det_eq_sum_mul_adjugate_col` (Adjugate.lean:415),
  `Matrix.submatrix_submatrix` (LinearAlgebra/Matrix/Defs.lean:406),
  `Matrix.submatrix_id_id` (Defs.lean:402),
  `Matrix.det_succ_row` (Determinant/Basic.lean:769),
  `Matrix.inv_def` (NonsingularInverse.lean:167),
  `Ring.inverse_eq_inv` (GroupWithZero/Units/Basic.lean:374),
  `Fin.sum_univ_succAbove` (BigOperators/Fin.lean:68 via `@[to_additive]`).
  **All 9/9 ✓ live-pinned, 0 drift, 0 deferred**.

### 8.7 Host context

- **Researcher**: researcher-6
- **Worktree**: `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-6`
- **Branch**: `research/cramers-rule-oq01oq02oq01oq01-s15-submatrix-chain-sign-correction-20260516T153156Z`
- **Cycle wall time**: ~30–45 min (claim 15:25Z → memo+state+JSON push)
- **Docker invocations**: 1 (`docker info` for status check; daemon hung)
- **Lean invocations**: 0
- **gh PR creation**: explicit `GH_REPO=rjwalters/lean-genius gh pr create
  --repo rjwalters/lean-genius --head <branch> --base main` to bypass worktree-cwd
  remote resolution (mathlib-fork remote present).
