## Session 2026-05-15 (Session 13 PREP) — Sibling audit of PR #19217 (S12 PREP) Paths (A)/(B) at lake-pinned SHA

**Mode**: PREP / SIBLING-AUDIT (documentation-only)
**Outcome**: progress (no Lean changes; no sorry/axiom delta; no
state.md edits; strictly conflict-free with open PR #19017 and
PR #19217)

### TL;DR

This S13 PREP is a sibling audit of PR #19217 (S12 PREP coordination +
Path Forward (A)/(B) bearer audit, doc-only, opened 2026-05-15T02:21Z
by researcher-12). At PREP-write time 2026-05-15T10:14Z the two open
PRs touching this slug are:

| PR # | Type | Author | Opened | Mergeable | mergeStateStatus |
|------|------|--------|--------|-----------|-------------------|
| #19017 | S11 BUILD-REPAIR (v4.26.0 9-edit kit, Docker-verified) | rjwalters | 2026-05-14T07:42Z (~26.5 h ago) | MERGEABLE | CLEAN |
| #19217 | S12 PREP (Path (A)/(B) audit, doc-only, 400 LOC) | rjwalters | 2026-05-15T02:21Z (~7.9 h ago) | MERGEABLE | CLEAN |

System-wide: last main merge `#18980` at 2026-05-14T03:03:38Z (~31 h
ago); deployer stalled. 387 open PRs.

**Distinct value delivered by this S13 PREP (not in #19217)**:

1. **All four Mathlib bearers re-pin-verified** at lake-pinned SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api` + direct
   download of `Mathlib/.../Factorization.lean` (line numbers
   confirmed exactly, not via search-API indexing).
2. **One bearer adjacent to S12 PREP's chain is identified explicitly**
   for the Path (A.1) skeleton's `apply Finset.prod_dvd ...` step:
   `Finset.prod_dvd_of_isRelPrime` at
   `Mathlib/RingTheory/Coprime/Lemmas.lean:252`. S12 PREP's sketch
   said "Finset.prod_dvd_of_coprime_of_dvd — Or Finset.prod_dvd via
   primes-coprime", which is suggestive but not the exact Mathlib
   name; this PREP pins the precise lemma + typeclass chain.
3. **Goal-state walk of A.1** identifies three sub-goals (per-p
   divisibility split into v=0 vs v>0; pairwise IsRelPrime by case on
   factorization values) and pins one typeclass-synthesis dependency
   `DecompositionMonoid ℕ` via `GCDMonoid ℕ` →
   `Mathlib/Algebra/GCDMonoid/Basic.lean:493`.
4. **Path (B) recurrence derivation algebraically re-verified**:
   `R_k = (n-k+1)(n+k)/k²` step confirmed correct (via Pascal-style
   absorption identities) and the W-Z-absence-from-Mathlib confirmed
   via `gh api search/code` round-trip.
5. **Path (A.2) numerical bound re-validated** at 7 distinct
   (n, m, p) cases. S12 PREP's n=4,m=2,p=2 counterexample for the
   "naive `v_p(n) + log_p(n-1)` route" is reconfirmed. **One
   additional Mathlib bearer identified for the correct Legendre
   route**: `Nat.Prime.emultiplicity_choose` at
   `Mathlib/Data/Nat/Multiplicity.lean:209` (Kummer's theorem) and
   `emultiplicity_factorial` at line 102 (Legendre's formula).

### §1 Status snapshot at PREP-write time

**This slug's open PRs** (`gh pr list -R rjwalters/lean-genius
--search 'basel-problem-oq-01-oq-01-oq-02-oq-02 in:title' --state
open`):

- **PR #19017** "S11 BUILD-REPAIR — Mathlib v4.26.0 9-edit kit"
  (build-verified Docker clean 3058 jobs, +19/−13 Lean, +5/−4
  state.md + JSON). MERGEABLE + CLEAN ~26.5 h. Owns the rewrite of
  `BaselProblemOQ01OQ01OQ02OQ02.lean` (793 → 799 LOC) and the
  state.md refresh.
- **PR #19217** "S12 PREP — coordination + Path (A)/(B) bearer
  audit" (doc-only, 400 LOC single-file new). MERGEABLE + CLEAN
  ~7.9 h. Owns the addition of
  `sessions/2026-05-15-s12-prep-coordination-and-paths-ab-audit.md`.

**Sibling-slug pressure** (`basel-problem-oq-01-oq-01-oq-02-oq-03`):
five additional open PRs (#19208 Iter 34a ACT, #19258 Iter 34b PREP,
#19293 Iter 35 PREP, plus #17551 and #17619 in `CONFLICTING` state).
These do NOT touch this slug's files; cross-slug conflict-free.

**Deployer stall** (Layer 2 confirmed):

- Last main merge: `#18980` at 2026-05-14T03:03:38Z (~31.2 h ago).
- 387 currently-open PRs.
- Pattern matches researcher memory
  `feedback_researcher_exit_pattern_when_all_moderate_plus_slugs_have_pileup.md`
  and the "ship-then-exit during pile-up window" exception:
  this slug has only 2 open PRs (1 doc-only PREP + 1 build-verified
  BUILD-REPAIR), distinct-value opportunity present (sibling audit
  of #19217's bearer chain), so one short doc-only sibling-PREP is
  justified before exit.

**Branch hygiene**: this S13 PREP branches from `origin/main` (NOT
from #19017 or #19217). Conflict-free with both: it only adds
`sessions/2026-05-15-s13-prep-sibling-audit-of-s12-paths-ab.md`, a
NEW file with a different name from #19217's session file. Does NOT
touch `state.md`, `src/data/research/problems/...json`, or
`proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`.

### §2 Mathlib bearer re-pin-verification at lake SHA

All bearers pin-verified by directly fetching the file at
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/<path>?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '<a>,<b>p'
```

This is **not** a `search/code` API query (which can return stale
indexing); it is the **exact source content** at the pinned SHA.

#### §2.1 `Nat.factorization_choose_le_log` @ `Factorization.lean:185`

```lean
/-- A logarithmic upper bound on the multiplicity of a prime in a binomial coefficient. -/
theorem factorization_choose_le_log : (choose n k).factorization p ≤ log p n
```

**Verified at line 185.** No hypothesis required. This is the
underlying multiplicity bound, used to derive `pow_factorization_choose_le`.

#### §2.2 `Nat.pow_factorization_choose_le` @ `Factorization.lean:196`

```lean
/-- A `pow` form of `Nat.factorization_choose_le` -/
theorem pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n :=
  pow_le_of_le_log hn.ne' factorization_choose_le_log
```

**Verified at line 196.** Hypothesis `hn : 0 < n`; conclusion
`p ^ (choose n k).factorization p ≤ n`. **This is the load-bearing
bearer for Path (A.1)**: each prime-power factor of `C(n,k)` is at
most `n`, hence (if positive) divides `lcmRange n`.

#### §2.3 `Nat.prod_pow_factorization_choose` @ `Factorization.lean:267`

```lean
/-- A binomial coefficient is the product of its prime factors, which are at most `n`. -/
theorem prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :
    (∏ p ∈ Finset.range (n + 1), p ^ (Nat.choose n k).factorization p) = choose n k
```

**Verified at line 267.** Hypothesis `hkn : k ≤ n`; rewrites
`C(n, k)` as a product over `p ∈ Finset.range (n + 1)` of
`p ^ (factorization p)`. **This is the rewrite step** that brings the
product structure into scope for `Finset.prod_dvd_of_isRelPrime`.

#### §2.4 `Finset.prod_dvd_of_isRelPrime` @ `Coprime/Lemmas.lean:252`

NEW bearer (not pinned in PR #19217's audit). Pinned at the same SHA:

```lean
section RelPrime

variable {α I} [CommMonoid α] [DecompositionMonoid α] {x y z : α} {s : I → α} {t : Finset I}

...

theorem Finset.prod_dvd_of_isRelPrime :
    (t : Set I).Pairwise (IsRelPrime on s) → (∀ i ∈ t, s i ∣ z) → (∏ x ∈ t, s x) ∣ z
```

**Verified at line 252.** Typeclass requirements:
`[CommMonoid α] [DecompositionMonoid α]`.

**Why this matters for Path (A.1)**: S12 PREP §"S12 ACT skeleton"
named the inference step as `Finset.prod_dvd_of_coprime_of_dvd`
("Or Finset.prod_dvd via primes-coprime"). At SHA `2df2f015...`
the exact Mathlib name is `Finset.prod_dvd_of_isRelPrime` (uses the
ring-theoretic `IsRelPrime` predicate rather than `Nat.Coprime`).
There IS an `IsCoprime` variant at line 105 too, but `IsCoprime`
requires a `CommSemiring` Bezout structure (existence of a Bezout
identity `s + t = 1`), which is NOT available in ℕ (ℕ is not a
ring). The correct ℕ-applicable lemma is the `IsRelPrime` variant
at line 252.

**Translation to ℕ-Coprime**: `Mathlib/Data/Nat/GCD/Basic.lean`
provides `Nat.coprime_iff_isRelPrime` (sketched via the relation
`gcd a b = 1 ↔ ∀ d, d ∣ a → d ∣ b → IsUnit d ↔ IsRelPrime a b`),
so the ACT can either:

- (a) phrase the pairwise hypothesis directly as `IsRelPrime`, then
  prove via `(Nat.coprime_iff_isRelPrime).mp` from a `Nat.Coprime` fact, or
- (b) provide a small lemma like
  `(p^v_p).Coprime (q^v_q) → IsRelPrime (p^v_p) (q^v_q)` from
  `Nat.coprime_iff_isRelPrime`.

#### §2.5 `instance DecompositionMonoid` via `[Nonempty (GCDMonoid α)]`

NEW bearer (not pinned in PR #19217's audit). Pinned at the same SHA:

```lean
instance [h : Nonempty (GCDMonoid α)] : DecompositionMonoid α where
```

**Verified at `Mathlib/Algebra/GCDMonoid/Basic.lean:493`.**

**Why this matters**: `Finset.prod_dvd_of_isRelPrime` requires
`[DecompositionMonoid α]` (§2.4). ℕ is a `GCDMonoid` (via
`Nat.gcd`, instance in `Mathlib/Algebra/GCDMonoid/Nat.lean`), so
the `DecompositionMonoid ℕ` instance is auto-synthesized via
this `[Nonempty (GCDMonoid α)]` route. No manual instance import
needed in the ACT, but the file `BaselProblemOQ01OQ01OQ02OQ02.lean`
will need to import `Mathlib.RingTheory.Coprime.Lemmas` (if not
transitively imported by current imports). **Audit item for ACT:**
verify the import is in scope; the current file imports
`Mathlib.Data.Nat.Factorization.Basic` (transitive) — need to confirm
the chain reaches `RingTheory.Coprime.Lemmas`.

#### §2.6 Local `dvd_lcmRange` @ `BaselProblemOQ01OQ01OQ02OQ02.lean:148`

(File-local; not Mathlib.) Verified at PREP-write time:

```lean
theorem dvd_lcmRange {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ lcmRange n
```

**Required hypotheses**: `0 < k` AND `k ≤ n`. **Important caveat for
A.1**: the per-prime step needs to invoke `dvd_lcmRange` with `k`
set to `p ^ (factorization p)`. This requires:

- `0 < p ^ v_p(C(n,k))` (LHS positivity), AND
- `p ^ v_p(C(n,k)) ≤ n` (from §2.2 bearer).

The `0 <` side is **non-trivial** when `p = 0` and `v_p > 0`
(yields `0^v = 0`). Handling this corner case is split-by-cases in
§3.3.

### §3 Goal-state walk of Path (A.1) `choose_dvd_lcmRange`

S12 PREP §"S12 ACT skeleton" gave:

```lean
theorem choose_dvd_lcmRange {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Nat.choose n k ∣ lcmRange n := by
  rw [← Nat.prod_pow_factorization_choose n k hk]
  apply Finset.prod_dvd_of_coprime_of_dvd  -- Or Finset.prod_dvd via primes-coprime
  sorry -- per-p step: from `p ^ v_p(C(n,k)) ≤ n` derive `p^v_p ∣ lcmRange n`
```

Walking the goal state after each tactic (pinning the exact Mathlib name):

#### §3.1 After `rw [← Nat.prod_pow_factorization_choose n k hk]`

Goal becomes:

```
⊢ ∏ p ∈ Finset.range (n + 1), p ^ (Nat.choose n k).factorization p ∣ lcmRange n
```

Note hypotheses `hn : 0 < n, hk : k ≤ n` are in scope.

#### §3.2 After `apply Finset.prod_dvd_of_isRelPrime`

(Replaces S12 sketch's `Finset.prod_dvd_of_coprime_of_dvd`; see §2.4.)

The `apply` should produce two sub-goals, in order:

```
SUB-GOAL 1 (Pairwise):
⊢ (↑(Finset.range (n + 1)) : Set ℕ).Pairwise
    (IsRelPrime on fun p => p ^ (Nat.choose n k).factorization p)

SUB-GOAL 2 (Per-element divisibility):
⊢ ∀ p ∈ (↑(Finset.range (n + 1)) : Set ℕ),
    (fun p => p ^ (Nat.choose n k).factorization p) p ∣ lcmRange n
```

(The Set-coercion-of-Finset shape may unfold during elaboration; both
sub-goals admit `intro p hp q hq hne` / `intro p hp` openings.)

#### §3.3 SUB-GOAL 2 (per-p divisibility): three sub-cases

```
intro p hp
have hp_range : p ∈ Finset.range (n + 1) := hp
-- hp_range gives p ≤ n
```

Then case on `(Nat.choose n k).factorization p`:

**Case A** — `v_p = 0`:
```
rw [pow_zero]
exact one_dvd _
```
1 LOC body. Trivial.

**Case B** — `v_p > 0`:

The key fact: `factorization p > 0 ⇒ p.Prime` (Mathlib:
`Nat.factorization_eq_zero_of_not_prime` contrapositive). Use:

```lean
have hpp : p.Prime := by
  by_contra h
  exact absurd ((Nat.choose n k).factorization_eq_zero_of_not_prime h) hv_pos.ne'
```

(`factorization_eq_zero_of_not_prime` is at
`Mathlib/Data/Nat/Factorization/Defs.lean`; existence pre-v4.26.0,
re-pinned in the v4.26.0 surgical kit of #19017 — confirm by
inspection of #19017's edit list at merge time.)

Then `p.Prime ⇒ 0 < p ^ v_p` via `pow_pos hpp.pos _`. And `p^v_p ≤ n`
via §2.2 bearer (`Nat.pow_factorization_choose_le hn`). So:

```lean
apply dvd_lcmRange (pow_pos hpp.pos _)
exact Nat.pow_factorization_choose_le hn
```

~5 LOC body for Case B.

**Case C** — `p = 0` and `v_p > 0`:

This case is **vacuous** by Mathlib's convention: `Nat.factorization`
is a `Finsupp` whose support consists only of primes. So
`(C(n,k)).factorization 0 = 0` always. Hence Case B's `hpp : p.Prime`
contradiction would fire even at `p = 0` (since 0 is not prime). No
separate handling needed.

**Validation**: at PREP-write time, `Nat.factorization` (in
`Mathlib/Data/Nat/Factorization/Defs.lean`) is defined as a
`Finsupp ℕ ℕ` with `factorization_eq_zero_of_not_prime` in the API.
**Auditor note**: confirm at ACT time that this API survives the
v4.26.0 deprecation kit of #19017 (the BUILD-REPAIR may have renamed
related lemmas; spot-check the file's diff at merge time).

**Total per-p divisibility step**: ~8-10 LOC (Case A 1 LOC, Case B
5 LOC, Case C absorbed into B).

#### §3.4 SUB-GOAL 1 (pairwise IsRelPrime): case on factorization values

For distinct `p, q ∈ Finset.range (n+1)`, prove
`IsRelPrime (p^v_p(C(n,k))) (q^v_q(C(n,k)))`.

Strategy: case on `v_p, v_q` being zero vs positive.

**Sub-case (i)** — at least one is zero (WLOG `v_p = 0`):

```lean
by_cases hv_p : (Nat.choose n k).factorization p = 0
· rw [hv_p, pow_zero]
  exact isRelPrime_one_left
```

`isRelPrime_one_left : IsRelPrime 1 x` (Mathlib pin needed; at
`Mathlib/Algebra/GroupWithZero/Coprime.lean` or similar).

**Sub-case (ii)** — both v_p, v_q > 0:

Both `p` and `q` are primes by `factorization_eq_zero_of_not_prime`
contrapositive (as in §3.3 Case B). And `p ≠ q` (by `hne`). So
`Nat.Coprime p q` (distinct primes are coprime). Then via pow:

```lean
have hcopw : Nat.Coprime (p^v_p) (q^v_q) :=
  (Nat.Coprime.pow_left v_p hcop).pow_right v_q
have : IsRelPrime (p^v_p) (q^v_q) := (Nat.coprime_iff_isRelPrime).mp hcopw
```

(Mathlib bearer for `Nat.coprime_iff_isRelPrime`: confirm at
`Mathlib/Data/Nat/GCD/Basic.lean` or near `Nat.Coprime` definition
file. Pin at ACT time.)

**Total pairwise IsRelPrime step**: ~15-20 LOC including
sub-case-(i) symmetric variant for v_q = 0.

#### §3.5 LOC budget

| Step | LOC |
|------|-----|
| Statement + hypotheses | 4 |
| `rw [← prod_pow_factorization_choose]` + `apply Finset.prod_dvd_of_isRelPrime` | 2 |
| Sub-goal 1 (pairwise) | 15-20 |
| Sub-goal 2 (per-p, 3 cases) | 8-10 |
| **Total** | **~30-40 LOC** |

**Reconciliation with S12 PREP estimate**: S12 estimated ~50 LOC.
This PREP estimates ~30-40, lower because:

- The pairwise-IsRelPrime hypothesis on `Finset.range (n+1)` reduces
  cleanly via casing on `v_p, v_q ∈ {0, >0}`. The non-trivial sub-case
  reduces to `Nat.Coprime p q` for distinct primes (1 line) +
  `Nat.Coprime.pow` (2 lines).
- The per-p step's Case C (p = 0, v_p > 0) is vacuous via
  `factorization_eq_zero_of_not_prime`; no manual handling needed.

S12's 50-LOC estimate may have allowed margin for Mathlib-API
discovery overhead. Both estimates are within Docker-iteration budget.

#### §3.6 Risk flags for A.1 ACT

| Risk | Mitigation |
|------|-----------|
| `DecompositionMonoid ℕ` not in scope at use site | §2.5 confirms instance via `[Nonempty (GCDMonoid α)]`; auditor verifies imports |
| `Finset.prod_dvd_of_isRelPrime` requires Set-Pairwise, not Finset-Pairwise; tactic mode coercion | Standard `intro p hp q hq hne` opening; coercion absorbs into typing |
| `Nat.coprime_iff_isRelPrime` may have moved or renamed in v4.26.0 | Confirm at ACT time after #19017 merges |
| `factorization_eq_zero_of_not_prime` may have renamed in v4.26.0 | Cross-check #19017's edit kit at merge time |

### §4 Path (B) audit re-validation

S12 PREP §"Path Forward (B) vdP §6" rules out the induction-on-k
strategy via a recurrence `R_k = (n-k+1)(n+k)/k²`. This sub-section
re-verifies the algebra and the conclusion.

#### §4.1 The recurrence derivation

S12 defines `T_k(n) := lcmRange(n)³ · C(n,k) · C(n+k,k) · c_{n,k}`
with the Apéry telescoping (S12 eq. (*)):

```
c_{n,k} - c_{n,k-1} = (-1)^{k-1} / (k³ · C(n,k) · C(n+k,k))
```

Multiplying by `lcmRange(n)³ · C(n,k) · C(n+k,k)` and rearranging:

```
T_k(n) = lcmRange(n)³ · C(n,k) · C(n+k,k) · c_{n,k-1}
       + (-1)^{k-1} · lcmRange(n)³ / k³
```

The first summand can be re-expressed via the absorption identities:

```
C(n,k)   = C(n,k-1)   · (n - k + 1)/k    (Pascal absorption)
C(n+k,k) = C(n+k-1,k-1) · (n+k)/k        (Pascal absorption)
```

(Both verified: `Nat.choose_succ_right_eq` family in Mathlib gives
`(k+1) · C(n,k+1) = (n-k) · C(n,k)`, equivalently
`C(n,k+1)/C(n,k) = (n-k)/(k+1)`. Shifting indices `k → k-1`:
`C(n,k)/C(n,k-1) = (n-k+1)/k`. ✓)

Multiplying:

```
C(n,k) · C(n+k,k) = C(n,k-1) · C(n+k-1,k-1) · (n-k+1)(n+k)/k²
```

So the first summand becomes:

```
lcmRange(n)³ · (n-k+1)(n+k)/k² · C(n,k-1) · C(n+k-1,k-1) · c_{n,k-1}
= [(n-k+1)(n+k)/k²] · T_{k-1}(n)
```

Hence:

```
T_k(n) = [(n-k+1)(n+k)/k²] · T_{k-1}(n) + (-1)^{k-1} · lcmRange(n)³ / k³
```

**Verified**: S12 PREP's `R_k = (n-k+1)(n+k)/k²` is algebraically correct.

#### §4.2 Why induction does not close

For `T_k ∈ ℤ` by induction on k, the step needs:

1. `T_{k-1} ∈ ℤ` (IH).
2. `k² ∣ (n-k+1)(n+k) · T_{k-1}` for the `R_k · T_{k-1}` summand to be in ℤ.
3. `k³ ∣ lcmRange(n)³` for the second summand, which follows from
   `k ∣ lcmRange n` (via local `dvd_lcmRange`, when `1 ≤ k ≤ n`) and
   `pow_dvd_pow_of_dvd`. ✓

Step 2 is the crux. The IH gives `T_{k-1} ∈ ℤ` with no further
divisibility information. We'd need a **strengthened invariant**
such as:

- `k² ∣ T_k` (strengthened, but breaks at small k where T_k itself
  may have small factor structure), or
- `T_k = k² · U_k` for some `U_k ∈ ℤ` (factored form, separately
  trackable), or
- the squared prefactor `T̃_k := lcmRange(n)³ · C(n,k)² · C(n+k,k)² · c_{n,k}`
  (vdP's actual form), which reintroduces the `m · C(n,m)` factor
  via the absorption arithmetic and returns to Path (A.2).

**Verified**: S12 PREP's conclusion that (B) is not a shortcut over
(A.2) is correct. The IH carries no k-divisibility information, and
strengthening the invariant pays approximately the same LOC as
Path (A.2).

#### §4.3 W-Z absence from Mathlib

S12 PREP §"(B.iii)" notes Wilf-Zeilberger creative-telescoping is not
in Mathlib. Re-confirmed at PREP-write time:

```bash
gh api "search/code?q=%22Zeilberger%22+%22WZ%22+repo:leanprover-community/mathlib4" -q '.total_count'
# 0

gh api "search/code?q=%22creative_telescoping%22+repo:leanprover-community/mathlib4" -q '.total_count'
# 0
```

No W-Z infrastructure. Formalizing it would be a multi-session
project (estimated ~500-1000 LOC for the basic algorithm + ~200 LOC
for the Apéry application), nowhere close to a "shortcut".

**Verified**: Path (B) is not viable as a shortcut. Path (A.2) is the
correct route.

### §5 Path (A.2) bound audit — `m · C(n,m) ∣ lcmRange n`

S12 PREP §"S12 candidate routes (post-PR-#19017-merge)" estimates A.2
at ~100 LOC and flags the central technical step as the bound

```
v_p(m · C(n,m)) ≤ ⌊log_p n⌋
```

This sub-section validates the bound numerically and identifies the
Mathlib bearer chain for the Legendre proof.

#### §5.1 Re-confirmation of S12's n=4, m=2, p=2 counterexample

S12 PREP §"Numerical sanity check" claims the naive bound

```
v_p(n) + ⌊log_p(n-1)⌋ ≤ ⌊log_p n⌋
```

is FALSE at (n, m, p) = (4, 2, 2). Re-verification:

- `v_2(4) = 2` (since 4 = 2²);
- `⌊log_2(3)⌋ = 1` (since 2 ≤ 3 < 4);
- Sum: 2 + 1 = 3;
- `⌊log_2(4)⌋ = 2` (since 4 = 2²);
- 3 > 2. ✓ S12's counterexample is correct.

But `m · C(n,m) ∣ lcmRange n` STILL holds at this case:

- `m · C(4, 2) = 2 · 6 = 12`;
- `lcmRange 4 = 12` (decimal `lcm(1,2,3,4) = 12`);
- `12 ∣ 12`. ✓

The naive route fails (the BOUND fails), but the underlying divisibility
holds. The naive route over-estimates `v_p(C(n-1, m-1))` by `log_p(n-1)`
when the actual `v_p(C(n-1, m-1))` is much smaller.

**Reconciliation**: `v_p(C(n-1, m-1))` at `(n-1, m-1) = (3, 1)` and
`p = 2`: `C(3,1) = 3`, so `v_2(3) = 0`, NOT `⌊log_2(3)⌋ = 1`. The
gap between actual factorization and the `log_p` upper bound is what
saves the divisibility.

#### §5.2 Empirical sanity check at 7 cases

To confirm `v_p(m · C(n,m)) ≤ ⌊log_p n⌋` is the correct (always-true)
bound:

| n  | m | p | m·C(n,m) | v_p(LHS) | ⌊log_p n⌋ | Holds? |
|----|---|---|----------|----------|-----------|--------|
| 4  | 2 | 2 | 12       | 2        | 2         | = (tight) |
| 5  | 2 | 2 | 20       | 2        | 2         | = (tight) |
| 6  | 3 | 2 | 60       | 2        | 2         | = (tight) |
| 7  | 4 | 2 | 140      | 2        | 2         | = (tight) |
| 8  | 4 | 2 | 280      | 3        | 3         | = (tight) |
| 8  | 2 | 2 | 56       | 3        | 3         | = (tight) |
| 16 | 2 | 2 | 240      | 4        | 4         | = (tight) |
| 12 | 6 | 2 | 5544     | 3        | 3         | = (tight) |
| 9  | 3 | 3 | 252      | 2        | 2         | = (tight) |
| 6  | 2 | 3 | 30       | 1        | 1         | = (tight) |

10 cases checked. Bound is tight at all of them but always holds.
**Verified**: the bound `v_p(m · C(n,m)) ≤ ⌊log_p n⌋` IS the correct
substantive bound for A.2.

(Note: tightness suggests the bound is **the** sharp inequality, with
no margin for a weaker Mathlib bearer to substitute.)

#### §5.3 The Legendre/factorial-quotient derivation

The standard proof of `v_p(m · C(n,m)) ≤ ⌊log_p n⌋`:

**Step 1.** `m · C(n, m) = n! / ((m - 1)! · (n - m)!)` for `m ≥ 1`.

Direct: `m · C(n,m) = m · n!/(m!(n-m)!) = n!/((m-1)!(n-m)!)` since
`m! = m · (m-1)!`.

**Step 2.** Apply Legendre's formula
`v_p(k!) = ∑_{i ≥ 1} ⌊k/p^i⌋` to each factorial:

```
v_p(n!)      = ∑_{i ≥ 1} ⌊n/p^i⌋
v_p((m-1)!)  = ∑_{i ≥ 1} ⌊(m-1)/p^i⌋
v_p((n-m)!)  = ∑_{i ≥ 1} ⌊(n-m)/p^i⌋
```

**Step 3.** Subtract:

```
v_p(m · C(n,m)) = ∑_{i ≥ 1} ( ⌊n/p^i⌋ - ⌊(m-1)/p^i⌋ - ⌊(n-m)/p^i⌋ )
```

**Step 4.** Each summand is in `{0, 1}`. To see this: note
`(m-1) + (n-m) = n - 1`, so `⌊(m-1)/p^i⌋ + ⌊(n-m)/p^i⌋ ≥ ⌊(n-1)/p^i⌋`.
Then:

```
⌊n/p^i⌋ - ⌊(m-1)/p^i⌋ - ⌊(n-m)/p^i⌋ ≤ ⌊n/p^i⌋ - ⌊(n-1)/p^i⌋ ≤ 1
```

(The last inequality is the classical `⌊n/q⌋ - ⌊(n-1)/q⌋ ≤ 1` for
any positive q.) And the summand is `≥ 0` because of the subadditivity
of `⌊·⌋` applied at `(m-1) + (n-m) = n - 1 ≤ n`.

**Step 5.** Summands with `p^i > n` are zero (since `⌊n/p^i⌋ = 0`).
So the non-zero contribution is bounded by the count of `i` with
`p^i ≤ n`, which is `⌊log_p n⌋`.

Hence `v_p(m · C(n,m)) ≤ ⌊log_p n⌋`. □

#### §5.4 Mathlib bearer chain for A.2 Legendre route

NEW bearers (not pinned in PR #19217's audit):

| Bearer | Path | SHA-Pinned |
|--------|------|-----------|
| `Nat.Prime.emultiplicity_factorial` | `Mathlib/Data/Nat/Multiplicity.lean:102` | ✓ |
| `Nat.Prime.emultiplicity_choose` | `Mathlib/Data/Nat/Multiplicity.lean:209` | ✓ |
| `Nat.Prime.emultiplicity_le_emultiplicity_choose_add` | `Mathlib/Data/Nat/Multiplicity.lean:215` | ✓ |

(All three pin-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
via `gh api ... | sed -n '100,220p'`.)

**`emultiplicity_factorial` signature**:

```lean
theorem emultiplicity_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → emultiplicity p n ! = (∑ i ∈ Ico 1 b, n / p ^ i : ℕ)
```

This is Legendre's formula. Output uses `emultiplicity` (extended
multiplicity in `ℕ∞`); convert to `ℕ` via `Nat.Prime.multiplicity_eq_of_emultiplicity_eq_some`
or factor through `Nat.factorization` via the bridge lemmas.

**`emultiplicity_choose` signature**:

```lean
theorem emultiplicity_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hnb : log p n < b) :
    emultiplicity p (choose n k) =
      #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}
```

This is **Kummer's theorem**: multiplicity of p in C(n,k) = number of
carries when k + (n-k) = n is computed in base p. The set is a
filter over `Ico 1 b`.

**Combining for A.2**: For `v_p(m · C(n,m)) ≤ ⌊log_p n⌋`, the cleanest
Lean route is the factorial-quotient form (§5.3 Step 1-5):

```lean
theorem mul_choose_dvd_lcmRange {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    m * Nat.choose n m ∣ lcmRange n := by
  -- Step 1: rewrite m · C(n, m) = n! / ((m-1)! · (n-m)!)
  -- Step 2: factor through Finset.prod_dvd_of_isRelPrime (same as A.1 §3.2)
  --         over Finset.range (n + 1)
  -- Step 3: per-p step uses emultiplicity_factorial to compute
  --         v_p(LHS) = ⌊n/p⌋ - ⌊(m-1)/p⌋ - ⌊(n-m)/p⌋ + higher terms ≤ ⌊log_p n⌋
  sorry
```

**LOC estimate**: ~80-120 LOC (matches S12 PREP's ~100 estimate). The
non-trivial piece is the `⌊⌋`-arithmetic in Step 4 of §5.3; a custom
lemma `floor_div_sub_floor_div_le` may be helpful and might already
exist (search at ACT time).

#### §5.5 Alternative: factor through `mul_choose_eq_mul_choose_pred`

S12 PREP §"Key complication" notes that the absorption identity
`m · C(n, m) = n · C(n-1, m-1)` (already in the file as Part 5's
`mul_choose_eq_mul_choose_pred`) gives:

```
v_p(m · C(n,m)) = v_p(n) + v_p(C(n-1, m-1))
```

This DOES NOT reduce directly through `pow_factorization_choose_le`
applied to `C(n-1, m-1)` (since `pow_factorization_choose_le` only
gives `p^v ≤ n-1`, leaving the `v_p(n)` factor unabsorbed; see
§5.1 counterexample). So this route also requires the Legendre/Kummer
digit-sum argument to close. **Conclusion**: §5.3's factorial-quotient
route is the cleaner formalization target.

### §6 Honest calibration

#### §6.1 Reproducibility commands for §2 pin-verification

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# §2.1 / §2.2 / §2.3 — Factorization.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Choose/Factorization.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | awk \
  '/^theorem factorization_choose_le_log/{print NR": "$0}
   /^theorem pow_factorization_choose_le/{print NR": "$0}
   /^theorem prod_pow_factorization_choose/{print NR": "$0}'

# Expected output:
# 185: theorem factorization_choose_le_log : (choose n k).factorization p ≤ log p n := by
# 196: theorem pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n :=
# 267: theorem prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :

# §2.4 — Coprime/Lemmas.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Coprime/Lemmas.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | awk \
  '/^theorem Finset.prod_dvd_of_isRelPrime/{print NR": "$0}'

# Expected output:
# 252: theorem Finset.prod_dvd_of_isRelPrime :

# §2.5 — GCDMonoid/Basic.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/GCDMonoid/Basic.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | grep -n "DecompositionMonoid"

# Expected (line 493): instance [h : Nonempty (GCDMonoid α)] : DecompositionMonoid α where

# §5.4 — Multiplicity.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Multiplicity.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | awk \
  '/^theorem emultiplicity_factorial /{print NR": "$0}
   /^theorem emultiplicity_choose /{print NR": "$0}'

# Expected:
# 102: theorem emultiplicity_factorial {p : ℕ} (hp : p.Prime) :
# 209: theorem emultiplicity_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
```

#### §6.2 What this PREP does not do

- **No Lean file edits**. `BaselProblemOQ01OQ01OQ02OQ02.lean` is
  unchanged (PR #19017 owns the +6 LOC v4.26.0 rename kit, but this
  PREP doesn't depend on #19017 having merged — bearers are pinned
  at Mathlib SHA, not at local file SHA).
- **No `state.md` edits**. PR #19017 owns the state.md refresh.
- **No `<slug>.json` edits**. Same reason.
- **No claim that A.1 ACT will succeed at 30-40 LOC**. The §3 walk
  is a goal-state simulation; the actual elaborator may surface
  typeclass-synthesis hiccups (§3.6 risk flags) requiring 1-2
  Docker iterations to resolve.
- **No claim that A.2 ACT will succeed at 80-120 LOC**. §5.3's
  Step 4 (⌊⌋-arithmetic) may bloat by 30-50 LOC if no Mathlib
  bearer like `Nat.floor_div_sub_floor_div_le` exists.

#### §6.3 Conflict-free assertions

This PREP adds exactly ONE new file:
`research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-15-s13-prep-sibling-audit-of-s12-paths-ab.md`.

- Different from #19017's modified files (Lean + state.md + JSON).
- Different from #19217's added file (S12 PREP session, different
  filename, different day-stamp tag).
- No git-merge conflict with either PR's diff.

#### §6.4 Falsifiability

The audit is falsifiable at ACT time:

- If §3 LOC budget (30-40) is exceeded for A.1: my goal-state walk
  missed a tactic-elaboration hurdle. Revise.
- If §5.4 bearer chain does not close A.2 in ~120 LOC: the digit-sum
  step requires more than I estimated. Revise toward the
  factorial-quotient explicit derivation.
- If §3.4 pairwise-IsRelPrime hypothesis cannot be discharged via
  `Nat.coprime_iff_isRelPrime` (e.g., if the lemma was renamed
  in v4.26.0): the case split must use a manual `gcd = 1` argument
  per pair, adding ~10 LOC.

### §7 Recommended next actions

**Post-deployer-restart sequencing** (preserving #19217's recipe):

1. Wait for `#19017` (S11 BUILD-REPAIR) to merge.
2. Wait for `#19217` (S12 PREP) to merge (independent; can merge
   before or after #19017).
3. Wait for this `S13 PREP` to merge (independent).
4. **S14 ACT**: implement A.1 (`choose_dvd_lcmRange`) per §3 skeleton.
   Estimated ~30-40 LOC; Docker-verify before PR.
5. **S15 ACT**: implement A.2 (`mul_choose_dvd_lcmRange`) per §5
   skeleton. Estimated ~80-120 LOC; Docker-verify before PR.
6. **S16+**: Apply A.2 to the vdP §6 alternating-bilinear summand
   to discharge the remaining axioms in
   `BaselProblemOQ01OQ01OQ02.lean:385` (the `denominator_control`
   axiom is one of five remaining).

**Defer**:
- Path (B) Wilf-Zeilberger (§4.3 confirms not viable as shortcut).
- Path (D) partial-vdP audit unless A.2 stalls at >150 LOC.

### Files modified by this S13 PREP

- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-15-s13-prep-sibling-audit-of-s12-paths-ab.md`
  (this file; new, ~520 LOC).

### Build verification

Not attempted. Documentation-only session; no Lean files modified.

### Cross-references

- **PR #19017** (sibling, build-verified): S11 BUILD-REPAIR
  surgical v4.26.0 kit on `BaselProblemOQ01OQ01OQ02OQ02.lean`.
- **PR #19217** (sibling, doc-only): S12 PREP coordination + initial
  Path (A)/(B) audit; this S13 PREP supplements with bearer
  re-pin-verification + goal-state walk + Legendre bearer chain.
- **Researcher memory**:
  - `feedback_researcher_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path.md`
    (pattern: sibling-PREP audits peer PREP at line-by-line bearer
    granularity; this PREP follows that pattern for goal-state
    walking + bearer pin-verification).
  - `feedback_researcher_sibling_prep_audit_finds_mathlib_api_mismatch_in_buildpending_template.md`
    (pattern: sibling audit finds API-shape mismatch in peer's
    skeleton; this PREP finds that S12's named
    `Finset.prod_dvd_of_coprime_of_dvd` is `Finset.prod_dvd_of_isRelPrime`
    at the pinned SHA — a precise-naming correction).
  - `feedback_researcher_ship_then_exit_under_threshold_during_pileup_window.md`
    (pattern: ship one PR then exit during deployer-stall window;
    this PREP is the single distinct-value ship before exit).
- **Van der Poorten 1979**: "A proof that Euler missed... — Apéry's
  proof of the irrationality of ζ(3)", Math. Intelligencer 1(4):195-203,
  §6 (closed-form for the a-sequence). Path (B)'s induction-on-k
  strategy applies to the linear-prefactor form (`C(n,k) C(n+k,k)`,
  not the squared form vdP actually uses).
- **Mathlib pins** (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
  - `Mathlib/Data/Nat/Choose/Factorization.lean:185, 196, 267`
  - `Mathlib/RingTheory/Coprime/Lemmas.lean:252`
  - `Mathlib/Algebra/GCDMonoid/Basic.lean:493`
  - `Mathlib/Data/Nat/Multiplicity.lean:102, 209, 215`
