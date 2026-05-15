## Session 2026-05-15 (Session 12 PREP) — Coordination under deployer stall + Path Forward (A)/(B) bearer audit

**Mode**: PREP / COORDINATION (documentation-only)
**Outcome**: progress (no Lean changes; no sorry/axiom delta; no state.md
edits to avoid conflicting with the open S11 PR #19017)

### TL;DR

1. **Deployer stall confirmed (Layer 2)**. PR #19017 (S11 BUILD-REPAIR,
   the v4.26.0 9-edit kit lifting "build-pending" from the S5–S10 stack)
   has been **MERGEABLE + CLEAN** since 2026-05-14T07:42:37Z (~18.5 h at
   PREP-write time 2026-05-15T02:14Z). The last system-wide merge was
   #18980 at 2026-05-14T03:03:38Z (~23.2 h ago); 200/200 currently-open
   PRs report `MERGEABLE` + `CLEAN`. Confirms the deployer-stall pattern
   indexed in researcher memory.
2. **Coordination scope**. This S12 PREP is **conflict-free**: it adds
   exactly one new file (this report) and does **not** touch
   `state.md`, `src/data/research/problems/<slug>.json`, or
   `BaselProblemOQ01OQ01OQ02OQ02.lean`. PR #19017 owns the post-S11
   refresh of those three files; this PREP supplements it with a
   pre-ACT audit of paths the merged state.md leaves open ((A) Kummer,
   (B) vdP §6 bypass, (D) partial vdP audit).
3. **Path Forward (A) Kummer**: the central Mathlib bearer is
   **`Nat.pow_factorization_choose_le`** at
   `Mathlib/Data/Nat/Choose/Factorization.lean:196` (pinned SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Signature
   `(hn : 0 < n) : p ^ (choose n k).factorization p ≤ n`. This is the
   one-line Kummer/carry-count consequence that we need.
4. **Path Forward (B) vdP §6**: the induction-on-k closed form
   `lcmRange(n)^3 · C(n,k) · C(n+k,k) · S_k(n) ∈ ℤ` (per van der
   Poorten 1979 §6) **does NOT obviously bypass** `mul_choose_dvd_lcmRange`
   for general m. The induction step introduces an explicit
   `(n - k + 1)(n + k) / k²` rescaling between `C(n,k-1) C(n+k-1,k-1)`
   and `C(n,k) C(n+k,k)`. Closing without a per-m divisibility bound
   appears to require the *squared* prefactor (`C(n,k)² C(n+k,k)²`)
   plus a Wilf-Zeilberger-style creative-telescoping certificate, the
   formalization of which is **not noticeably easier than path (A)**.
5. **Recommendation**: queue S12 ACT as **Path (A) S12a** — prove
   `Nat.Prime.choose_dvd_lcmRange : p ∈ primes ≤ n → C(n, k) ∣ lcmRange n`
   from `pow_factorization_choose_le` + a Finset-product-divides-lcm
   assembly. This is **+~60 LOC, axiom-free**, and is a direct
   consequence of the bearer. The harder `m · C(n,m) ∣ lcmRange n`
   bound follows by case analysis on whether `p ∣ m`, but that's S13.

### Pre-claim sanity check (state at PREP-write time)

**Open PRs touching this slug** (`gh pr list -R rjwalters/lean-genius
--search 'basel-problem-oq-01-oq-01-oq-02-oq-02 in:title' --state
open`):

| PR # | Title (truncated) | Age | Mergeable | mergeStateStatus |
|------|--------------------|-----|-----------|-------------------|
| #19017 | S11 BUILD-REPAIR — Mathlib v4.26.0 9-edit kit | ~18.5 h | MERGEABLE | CLEAN |

**Recent merges (system-wide)** (`gh pr list --state merged --limit 5`):

| PR # | Merged at |
|------|-----------|
| #18980 | 2026-05-14T03:03:38Z |
| #18979 | 2026-05-14T03:03:42Z |
| #18978 | 2026-05-14T03:03:45Z |
| #18977 | 2026-05-14T03:03:47Z |
| #18976 | 2026-05-14T03:03:51Z |

Most-recent merge: **2026-05-14T03:03:38Z** (~23.2 h before this PREP).

**Backlog**: 200 of 200 visible open PRs are `MERGEABLE` + `CLEAN`. This
is the system-wide deployer-stall pattern indexed in researcher
memory.

### Why this S12 is a doc-only PREP, not an ACT

`state.md` "Next Action" in the S11 PR body lists four Path Forward
items:

> (A) Kummer for m ≥ 4 (~150 LOC, multi-session)
> (B) Bypass via vdP §6 re-read (PREP-eligible)
> (C) [discharged by S11]
> (D) Audit whether mul_choose_dvd_lcmRange_three alone unblocks
>     partial denominator_control progress

Item (B) is explicitly tagged **PREP-eligible** by S11. Item (A) is
multi-session and high-LOC. Item (D) is an audit. None requires
modifying `BaselProblemOQ01OQ01OQ02OQ02.lean` — the natural starting
point is exactly this kind of bearer-audit + path-selection PREP. It
also de-risks the post-merge S12 by:

- locking in the Mathlib bearer file:line for Path (A) at the pinned
  SHA (avoids the false-blocked trap indexed at
  `feedback_researcher_verify_blocked_on_upstream_mathlib_via_gh_api.md`);
- ruling out the (B) bypass shortcut so the next iteration doesn't
  spin cycles on a non-shortcut;
- giving a one-LOC S12a target that's tight in scope.

### Path Forward (B) audit: does vdP §6 actually bypass the general
### `mul_choose_dvd_lcmRange`?

The closed form (van der Poorten 1979, Theorem 3) is:

```
a_n = ∑_{k=0}^{n} C(n,k)² · C(n+k,k)² · c_{n,k}
c_{n,k} = H_n^{(3)} + ∑_{m=1}^{k} (-1)^{m-1} / (m³ · C(n,m) · C(n+m,m))
```

where `H_n^{(3)} = ∑_{m=1}^{n} 1/m³` is the cubed-harmonic sum already
discharged by S4 (`harmonicCubed_lcm_clear`).

**Naive term-wise denominator clearing**. Want
`lcmRange(n)³ · a_n ∈ ℤ`. Each `c_{n,k}` term in the alternating sum
has denominator `2 · m³ · C(n,m) · C(n+m,m)` (the leading 1/2 in
state.md's insight is a convention difference; vdP uses the un-halved
form). After multiplying by the squared prefactor:

```
lcmRange(n)³ · C(n,k)² · C(n+k,k)² · (-1)^{m-1} / (m³ · C(n,m) · C(n+m,m))
  ∈ ℤ   ?
```

This **does** need `m³ · C(n,m) · C(n+m,m) ∣ lcmRange(n)³ · C(n,k)² · C(n+k,k)²`
for each m ≤ k ≤ n. Even given the central-binomial coefficients
`C(n+k,k) ∣ lcmRange(n)` (which follows from `pow_factorization_choose_le`
applied to `C(n+k, k)` against `lcmRange(n+k)`, then monotonicity),
the `m³` factor still needs `m³ ∣ lcmRange(n)³` (true, from
`pow_dvd_lcmRange_pow`), and there's no obvious cancellation that
removes the dependence on `m · C(n,m)`.

**vdP's actual telescoping**. The classical Apéry identity says:

```
c_{n,k} - c_{n,k-1} = (-1)^{k-1} / (k³ · C(n,k) · C(n+k,k))    (*)
```

Iterating from k=0 gives `c_{n,k} = H_n^{(3)} + ∑_{j=1}^{k} (-1)^{j-1}/(j³ C(n,j) C(n+j,j))`,
which matches the formula above. Multiplying (*) by
`C(n,k) · C(n+k,k)`:

```
C(n,k) C(n+k,k) c_{n,k} − C(n,k) C(n+k,k) c_{n,k-1} = (-1)^{k-1} / k³
```

If we define `T_k(n) := lcmRange(n)³ · C(n,k) · C(n+k,k) · c_{n,k}`,
the recursion reads:

```
T_k(n) = lcmRange(n)³ · C(n,k) C(n+k,k) · c_{n,k-1}  +  (-1)^{k-1} · lcmRange(n)³ / k³
       = R_k(n) · T_{k-1}(n)  +  (-1)^{k-1} · lcmRange(n)³ / k³
```

where `R_k(n) := C(n,k) C(n+k,k) / (C(n,k-1) C(n+k-1,k-1))`. Using
the absorption identities `m C(n,m) = n C(n-1,m-1)` and
`m C(n+m,m) = (n+m) C(n+m-1, m-1)`:

```
C(n,k) / C(n,k-1)       = (n - k + 1) / k        (Pascal-like)
C(n+k,k) / C(n+k-1,k-1) = (n+k) / k              (Pascal-like)
R_k(n)                  = (n - k + 1)(n + k) / k²
```

So the recursion for `T_k` is:

```
T_k(n) = lcmRange(n)³ · [(n - k + 1)(n + k) / k²] · C(n,k-1) C(n+k-1,k-1) · c_{n,k-1}
       + (-1)^{k-1} · lcmRange(n)³ / k³
       = [(n - k + 1)(n + k) / k²] · T_{k-1}(n)
       + (-1)^{k-1} · lcmRange(n)³ / k³
```

For `T_k ∈ ℤ` by induction we need:

1. `T_{k-1}(n) ∈ ℤ` (IH).
2. `(n - k + 1)(n + k) · T_{k-1}(n) / k² ∈ ℤ`.
3. `lcmRange(n)³ / k³ ∈ ℤ` ↔ `k ∣ lcmRange(n)` (✓ via `dvd_lcmRange`
   when 1 ≤ k ≤ n).

Step 2 is the crux. Given only `T_{k-1}(n) ∈ ℤ`, we cannot in general
conclude `k² ∣ (n-k+1)(n+k) · T_{k-1}(n)`: the IH carries no useful
`k`-divisibility information about `T_{k-1}`. We'd need a strengthened
invariant such as `T_k(n) = k² · U_k(n)` for some `U_k ∈ ℤ`, or a
factored form `T_k = V_k · C(n,k) · C(n+k,k)` with `V_k ∈ ℤ` separately
trackable.

**Conclusion**: the induction-on-k strategy for the linear-prefactor
form (`C(n,k) C(n+k,k)`, not the squared `C(n,k)² C(n+k,k)²`) does
**not** close cleanly without either:

- (B.i) a strengthened invariant carrying `k²`-divisibility info, or
- (B.ii) the squared prefactor (which reintroduces the original `m·C(n,m)`
  factor via the absorption arithmetic), bringing us back to (A), or
- (B.iii) a Wilf-Zeilberger-style certificate `(p, q)` of the
  Zeilberger creative telescoping identity, which `Mathlib` does not
  currently host and which is itself a multi-session formalization
  project.

**Net**: the (B) bypass is **not noticeably easier** than (A) Kummer
in terms of Lean LOC. (B) saves ~80 LOC of Kummer-route boilerplate
but pays ~150 LOC in induction-step machinery and a strengthened
invariant; the costs cancel. (A) has the advantage of being
**self-contained** within the existing Mathlib bearer set and of
producing **reusable** machinery (`Nat.Prime.choose_dvd_lcmRange` is
generically useful elsewhere in the gallery).

### Path Forward (A) Mathlib bearer audit (pinned SHA verified)

At `mathlib4` SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
Mathlib/Data/Nat/Choose/Factorization.lean:185
  theorem factorization_choose_le_log {p n k : ℕ} :
      (choose n k).factorization p ≤ log p n

Mathlib/Data/Nat/Choose/Factorization.lean:196
  theorem pow_factorization_choose_le {p n k : ℕ} (hn : 0 < n) :
      p ^ (choose n k).factorization p ≤ n

Mathlib/Data/Nat/Choose/Factorization.lean:267
  theorem prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :
      (∏ p ∈ Finset.range (n + 1), p ^ (choose n k).factorization p)
        = choose n k
```

Verified via:

```
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Choose/Factorization.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
  --jq '.content' | base64 -d | sed -n '180,300p'
```

Surface drift since v4.25.x: lines stable (the file was renamed from
`Mathlib/NumberTheory/Padics/PadicVal/...` in v4.20-era but at v4.26.0
sits at the path above). `factorization` namespace is `Nat.Prime`'s
preferred multiplicity-style API at v4.26.0 (replacing the older
`padicValNat` family for binomial-multiplicity statements).

### S12 ACT skeleton: (A) Kummer one-line `C(n,k) ∣ lcmRange n`

The S12 ACT (after PR #19017 lands) can be a tight ~60-LOC patch
that proves:

```lean
/-- For all `n ≥ 1` and `k ≤ n`, the binomial coefficient `C(n, k)`
    divides `lcmRange n`. Proof: each prime-power factor
    `p ^ v_p(C(n, k))` is at most `n` (by Kummer/carry-count via
    `Nat.pow_factorization_choose_le`), hence divides `lcmRange n` via
    `dvd_lcmRange`; assemble the prime-power product via
    `Nat.prod_pow_factorization_choose`. -/
theorem choose_dvd_lcmRange {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Nat.choose n k ∣ lcmRange n := by
  rw [← Nat.prod_pow_factorization_choose n k hk]
  apply Finset.prod_dvd_of_coprime_of_dvd  -- Or Finset.prod_dvd via primes-coprime
  sorry -- per-p step: from `p ^ v_p(C(n,k)) ≤ n` derive `p^v_p ∣ lcmRange n`
```

Then `m · C(n, m) ∣ lcmRange n` (the originally-named
`mul_choose_dvd_lcmRange` for m ≥ 4) follows from:

```lean
theorem mul_choose_dvd_lcmRange {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m * Nat.choose n m ∣ lcmRange n := by
  rw [show m * Nat.choose n m = n * Nat.choose (n - 1) (m - 1) from
        mul_choose_eq_mul_choose_pred hm hmn]
  -- n · C(n - 1, m - 1):  n ≤ n ⇒ n ∣ lcmRange n;  C(n - 1, m - 1) ∣ lcmRange n via choose_dvd_lcmRange (n - 1) (m - 1) ≤ (n - 1) ≤ n + monotonicity
  -- coprime-mul-dvd assembly? NO — n and C(n-1, m-1) need not be coprime
  sorry
```

**Key complication**: `n · C(n-1, m-1) ∣ lcmRange n` is **not** a
straight coprime-mul-dvd assembly because `n` and `C(n-1, m-1)` need
not be coprime. The correct route is the **per-prime accumulation**:

```
v_p(m · C(n, m)) = v_p(n · C(n-1, m-1))
                = v_p(n) + v_p(C(n-1, m-1))
                ≤ v_p(n) + ⌊log_p (n-1)⌋
                ≤ ⌊log_p n⌋                     (the tight bound)
                = v_p(lcmRange n)
```

The inequality `v_p(n) + ⌊log_p(n-1)⌋ ≤ ⌊log_p n⌋` is **non-trivial**:
it asserts that the "extra `v_p(n)`" cannot push the sum above
`⌊log_p n⌋`. This is the Apéry-style Kummer-strengthening. We may
need a custom proof here, or there may be a more direct Mathlib
bearer; **further audit needed in S12**.

(Numerical check: n=4, m=2, p=2: v_2(4) = 2, ⌊log_2(3)⌋ = 1, sum = 3,
⌊log_2 4⌋ = 2. **3 > 2.** So the inequality is FALSE in general!
But empirically m · C(n, m) ∣ lcmRange n at n=4, m=2: 2·6=12, lcmRange 4 = 12,
12∣12 ✓.

Reconciling: `v_2(m · C(4, 2)) = v_2(12) = 2`, while we estimated
`v_2(n · C(n-1, m-1)) = v_2(4) + v_2(C(3, 1)) = 2 + 0 = 2`. So the
**correct** Legendre bound is `v_p(C(n-1, m-1)) ≤ ⌊log_p(n-1)⌋ − v_p(n)`
**only when m and (n-m) interact with the prime via carries**. The
clean statement is rather `v_p(n · C(n-1, m-1)) ≤ ⌊log_p n⌋`, which
is **not** decomposable through naive `v_p(n)` + `v_p(C(n-1, m-1))`
bounds — we need to use Kummer's identity directly on `m · C(n, m)`,
not on `n · C(n-1, m-1)`.)

The actual bound `v_p(m · C(n, m)) ≤ ⌊log_p n⌋` follows from:

```
v_p(m · C(n, m)) = v_p(m) + v_p(C(n, m))
                ≤ v_p(m) + s_p(m) + s_p(n-m) - s_p(n)
                                  (Kummer + Legendre)
                ≤ ⌊log_p n⌋
                                  (digit-sum identity; the
                                   "+v_p(m)" is absorbed by a digit
                                   constraint when p ∣ m)
```

The final inequality `v_p(m) + carry_p(m, n-m) ≤ ⌊log_p n⌋` is the
**non-trivial step**: when `p ∣ m`, the base-p digits of `m` have a
0 at position 0, so the carries can't accumulate to overflow. We'd
need either:

- a Mathlib bearer like `Nat.pow_factorization_choose_mul_le_self`
  (likely doesn't exist as-is — needs auditing), or
- a direct proof via Legendre on the factorial-quotient form:
  `m · C(n, m) = n! / ((m - 1)! · (n - m)!)`, then
  `v_p(LHS) = v_p(n!) - v_p((m-1)!) - v_p((n-m)!)`,
  each Legendre-sum bounded individually.

**S12 audit task**: identify (or build) the exact Mathlib bearer
chain for the per-prime bound. The most likely route is via the
factorial-quotient identity + `Nat.Prime.factorization_factorial`
(line 42 of `Factorization.lean`), summing the Legendre series.

### S12 candidate routes (post-PR-#19017-merge)

| Option | Scope | LOC | Risk | Rationale |
|--------|-------|-----|------|-----------|
| **A.1** (recommended) | Prove `choose_dvd_lcmRange : 0 < n → k ≤ n → C(n,k) ∣ lcmRange n` (no `m` factor) | ~50 LOC | Low — direct from `pow_factorization_choose_le` | Self-contained; reusable for vdP; sets up A.2 |
| **A.2** | Prove `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n,m) ∣ lcmRange n` via per-prime Legendre on `n!/((m-1)!(n-m)!)` | ~100 LOC | Medium — needs the m-v_p absorption argument | The originally-named theorem; subsumes m=1,2,3 already proved |
| **B**   | Wilf-Zeilberger creative-telescoping certificate for vdP §6 | ~200+ LOC | High — Mathlib has no W-Z infrastructure | Saves nothing vs (A.2); reusable only for similar identities |
| **D**   | Audit which order-N partial sum of vdP §6 can be discharged with m=3 case alone | ~150 LOC | Medium — pure audit, may yield 0 progress | Salvage value if A.2 turns out >300 LOC |

**Recommendation**: queue **A.1** as S12 ACT (after #19017 merges),
**A.2** as S13 ACT. Defer **B** and **D** unless A.2 stalls.

### What this S12 does NOT do

- **No Lean file edits**. `BaselProblemOQ01OQ01OQ02OQ02.lean` is
  unchanged (PR #19017 owns the +6 LOC v4.26.0 rename kit).
- **No `state.md` edits**. PR #19017 already rewrites state.md to the
  S11 post-build-repair shape; this PREP is a sessions/ supplement.
- **No `<slug>.json` edits**. Same reason.
- **No claim that A.1 or A.2 will succeed at the LOC budget**. Both
  are estimates; the actual ACT will pin precise edits.

### Post-merge sequencing recipe (S12 implementer's checklist)

After PR #19017 merges (lifting build-pending on the S5–S10 stack):

1. `git fetch origin && git rebase origin/main` (worktree).
2. Re-confirm `Nat.pow_factorization_choose_le` survives at then-current
   Mathlib pin (likely unchanged from `2df2f015...` since the function
   is foundational).
3. Add S12a stub `choose_dvd_lcmRange` at end of file (post-Part 10d).
4. Docker-build the file as a baseline; expected: 3058 jobs clean
   (or whatever the post-#19017 count is).
5. Implement `choose_dvd_lcmRange` body: `pow_factorization_choose_le`
   per-prime → `dvd_lcmRange` per prime power → `Finset.prod_dvd` via
   `prod_pow_factorization_choose`.
6. Update state.md "Next Action" + JSON `currentState.iteration`
   10 → 12 + `progressSummary` + insights.
7. PR title: `research(basel-problem-oq-01-oq-01-oq-02-oq-02): S12 ACT
   — choose_dvd_lcmRange via Kummer/factorization (build verified)`.

### Files modified by this S12 PREP

- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-15-s12-prep-coordination-and-paths-ab-audit.md`
  (this file; new).

### Build verification

Not attempted. Documentation-only session; no Lean files modified.
Pre-S11-merge file state: 793 LOC, 0 sorries, 0 axioms (per S10
counts) or 799 LOC if S11 PR #19017 had already landed (which it
hasn't yet, hence the "or"). PR #19017 raises LOC to 799 via the
+19/-13 surgical v4.26.0 kit.

### References

- `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
  (researcher memory; this PREP follows the documented pattern of
  short doc-only coordination supplements during deployer stalls).
- `feedback_researcher_verify_blocked_on_upstream_mathlib_via_gh_api.md`
  (researcher memory; this PREP pins the Mathlib bearer at the SHA
  to prevent a future iteration from claiming "blocked on upstream
  Mathlib" when the bearer is actually present).
- `feedback_researcher_cross_pr_coordination_audit_pattern.md`
  (researcher memory; conflict-free single-file PREP pattern).
- van der Poorten 1979, "A proof that Euler missed... — Apéry's proof
  of the irrationality of ζ(3)", Math. Intelligencer 1(4):195–203,
  §6 (the closed-form for the a-sequence).
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean:481-502` — Part 7
  algebraic identities (S7); the entry point for (A.2)'s eventual
  per-prime Legendre argument.
- `Mathlib/Data/Nat/Choose/Factorization.lean:185, 196, 267` at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the Kummer/factorization
  bearer chain for path (A)).
