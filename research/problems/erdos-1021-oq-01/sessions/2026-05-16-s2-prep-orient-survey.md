# S2 PREP — Orientation survey + sorry inventory + S3 ACT plan

**Date**: 2026-05-16 (researcher-11, ~09:20 UTC)
**Mode**: PREP (doc-only)
**Outcome**: Bootstrap orientation for a slug that has well-written Lean
infrastructure (8 theorems, 2 honest axioms, 4 sorries) but a state.md
stuck at the 2026-03-30 NEW bootstrap. Inventories the 4 sorries with
discharge-difficulty classification, surveys Mathlib bearers for the
mechanical ones, and proposes an S3 ACT plan targeting the two most
discharge-able (L165 Tendsto arithmetic + L112 little-o → big-O bound).

---

## 1. Pre-flight infrastructure

| Check | Result |
|---|---|
| `df -h /System/Volumes/Data` | 100% used, 6.9 Gi avail (PREP-class) |
| `docker info` | responsive (29.4.1) |
| Open PRs on slug | 0 |
| Mathlib pin | `v4.26.0` @ `2df2f0150c…` (unchanged ≥9 days) |
| OQ-01 Lean file | 191 LOC, 8 thms, 2 axioms, **4 sorries** |
| Parent `Erdos1021Problem.lean` | 241 LOC, 1 sorry (`k3_case_solved`), 2 axioms |
| Last touch on either Lean file | (pre-2026-04-03, since merged) |

---

## 2. Problem statement (in plain language)

**Erdős #1021** asks: for every `k ≥ 3`, does there exist `c_k > 0` such
that `ex(n, G_k) ≪ n^(3/2 − c_k)`, where `G_k` is the bipartite graph
with vertex sets `{y_1, …, y_k}` and `{z_1, …, z_{C(k,2)}}` and each `z_j`
joined to exactly one pair of `y` vertices?

**OQ-01 (weak form)**: for any `k ≥ 4`, is `ex(n, G_k) = o(n^(3/2))`?

Status:
- `k = 3`: solved (`G_3 ≅ C_6`, `ex(n, C_6) ≪ n^(7/6)` by Bondy-Simonovits)
- `k ≥ 4`: OPEN — even the weak form `o(n^(3/2))` is unproven
- Lower bound: probabilistic method gives `≥ c · n^(3/2 − 1/(k−1))`
- Upper bound: KST gives `≤ C · n^(3/2)` for all `k ≥ 3` (because
  `G_k ⊇ K_{2, C(k,2)}` as a subgraph)

So OQ-01 is open and the formalization can never close it (it depends
on an unproved combinatorial result). What IS achievable is to **make
the formalization sharper**: discharge the mechanical sorries, leave
the honest axioms, and document the gap precisely.

---

## 3. Sorry inventory (Erdos1021OQ01.lean)

| # | Line | Theorem | Difficulty | Discharge route |
|---|---|---|---|---|
| 1 | L112 | `oq01_strictly_beyond_kst` | **MECHANICAL** | Convert `Asymptotics.IsLittleO` at chosen ε=1 to a `IsBigO` bound via `Finset.sup` over `Finset.range N` |
| 2 | L127 | `k3_strong_implies_weak` | **BLOCKED** | Depends on parent `k3_case_solved` (a sorry itself); has nothing to discharge until parent advances |
| 3 | L136 | `ex_not_obviously_monotone_in_k` | **HARD** | Requires constructing explicit `k₁ < k₂` and `n` with `exGk k₁ n > exGk k₂ n`; combinatorial; honest open question |
| 4 | L165 | `lower_bound_exponent_tendsto` | **MECHANICAL** | `1/(k − 1) → 0` via `Tendsto.const_div_atTop` or `Filter.Tendsto.inv_tendsto_atTop` + `Nat.cast_atTop_atTop` |

**Plus 2 honest axioms** (KST trivial bound L99, probabilistic lower bound
L148) — these reflect external Erdős-style results and are appropriate
as axioms.

### 3.1 Detailed: L165 (most discharge-able)

```lean
theorem lower_bound_exponent_tendsto :
    Filter.Tendsto (fun k : ℕ => (3 : ℝ)/2 - 1/((k : ℝ) - 1)) Filter.atTop (nhds (3/2)) := by
  have : Filter.Tendsto (fun k : ℕ => (3 : ℝ)/2 - 1/((k : ℝ) - 1)) Filter.atTop
      (nhds ((3 : ℝ)/2 - 0)) := by
    apply Filter.Tendsto.sub tendsto_const_nhds
    rw [div_tendsto_iff_tendsto_div tendsto_const_nhds]
    · sorry -- 1/(k-1) → 0 requires Filter.Tendsto + arithmetic
    · norm_num
  simpa using this
```

The `rw` was already in the wrong direction (the goal at the sorry
becomes a different Tendsto). Cleanest approach: discard the
`div_tendsto_iff_tendsto_div` rewrite and instead use the standard
"reciprocal of tends-to-infinity is tends-to-zero" pattern:

**Proposed S3 ACT replacement (paste-ready, ~8 LOC)**:
```lean
theorem lower_bound_exponent_tendsto :
    Filter.Tendsto (fun k : ℕ => (3 : ℝ)/2 - 1/((k : ℝ) - 1)) Filter.atTop (nhds (3/2)) := by
  have h1 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) - 1)) Filter.atTop (nhds 0) := by
    have hk : Filter.Tendsto (fun k : ℕ => ((k : ℝ) - 1)) Filter.atTop Filter.atTop := by
      exact (tendsto_natCast_atTop_atTop).atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
    simpa using hk.inv_tendsto_atTop
  have h2 : Filter.Tendsto (fun k : ℕ => (3 : ℝ)/2 - 1/((k : ℝ) - 1)) Filter.atTop
      (nhds ((3 : ℝ)/2 - 0)) := tendsto_const_nhds.sub h1
  simpa using h2
```

**Bearer audit** (Mathlib SHA `2df2f0150c…`):
- `tendsto_natCast_atTop_atTop` — likely in `Mathlib/Analysis/SpecificLimits/Basic.lean`
- `Filter.Tendsto.atTop_add` — likely in `Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `Filter.Tendsto.inv_tendsto_atTop` — `Mathlib/Topology/Algebra/Order/Field.lean` (need to verify exact name + signature; could be `tendsto_inv_atTop_zero`)
- `Filter.Tendsto.sub` — `Mathlib/Topology/Algebra/Order/Group.lean`

**Risk**: medium. The `inv_tendsto_atTop` family has multiple variants (`tendsto_inv_atTop_zero`, `Tendsto.inv_tendsto_zero`, `Tendsto.inv_tendsto_atTop`); first ACT iter may need exact-name correction. Budget 2-3 Docker iters.

### 3.2 Detailed: L112 (second most discharge-able)

```lean
theorem oq01_strictly_beyond_kst (k : ℕ) (hk : k ≥ 4)
    (hoq01 : isLittleO (fun n => exGk k n) (fun n => (n : ℝ) ^ (3/2 : ℝ))) :
    ∃ C > 0, ∀ n : ℕ, exGk k n ≤ C * (n : ℝ) ^ (3/2 : ℝ) := by
  obtain ⟨N, hN⟩ := hoq01 1 one_pos
  use max 1 (Finset.sup (Finset.range N)
    (fun n => if (n : ℝ) ^ (3/2 : ℝ) > 0 then ⌈exGk k n / (n : ℝ) ^ (3/2 : ℝ)⌉₊ else 1) + 1)
  intro n
  sorry -- The o() definition gives a uniform O() bound
```

The local `isLittleO` is the file's own definition (line 35 area:
`isLittleO f g ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n| ≤ ε * |g n|`). So at this
point in the proof we have `hN : ∀ n ≥ N, exGk k n ≤ 1 * n^(3/2)`.

**Proposed S3 ACT replacement (paste-ready, ~15 LOC)**:
```lean
  obtain ⟨N, hN⟩ := hoq01 1 one_pos
  -- Define a bound that handles both n < N and n ≥ N
  set Cfin := Finset.sup (Finset.range N)
    (fun n => ⌈exGk k n / max 1 ((n : ℝ) ^ (3/2 : ℝ))⌉₊)
  refine ⟨max 2 (Cfin + 2), ?_, ?_⟩
  · positivity  -- max 2 _ > 0
  intro n
  by_cases hn : n ≥ N
  · calc exGk k n ≤ 1 * (n : ℝ) ^ (3/2 : ℝ) := hN n hn
      _ ≤ (max 2 (Cfin + 2)) * (n : ℝ) ^ (3/2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [le_max_left (2 : ℝ) (↑Cfin + 2)]
  · -- n < N case: bound is finite from Finset.sup
    sorry  -- 5-10 LOC reasoning on n ∈ Finset.range N + Finset.le_sup
```

**Note**: the second `sorry` is the genuinely tricky part — needs to
extract the `Finset.sup` upper bound for the specific `n ∈ Finset.range
N`, then divide both sides by `(n : ℝ) ^ (3/2)` (with `n > 0` case-split
on whether `n = 0` matters here). For `n = 0`: `exGk k 0` is a natural
number (likely 0 if `Erdos1021.exGk` is `extremalNumber`-based), and
`(0 : ℝ) ^ (3/2)` is 0, so the bound `0 ≤ C * 0 = 0` trivially. Adds
~5 LOC of `match n with | 0 => ... | n+1 => ...`.

**Risk**: medium-high. The `Finset.sup` ceiling extraction is fiddly.
Budget 3-5 Docker iters. Defer to S4 ACT (after S3 closes L165).

### 3.3 L127 — BLOCKED on parent

```lean
theorem k3_strong_implies_weak : k3_weak_holds := by
  have := strong_implies_weak
  sorry -- Requires k3_case_solved (itself a sorry in the parent)
```

The parent file `Erdos1021Problem.lean` L204 has

```lean
theorem k3_case_solved : ∃ c : ℝ, c > 0 ∧
    (fun n => exGk 3 n) ≪ (fun n => powerBound c n) := by
  sorry
```

This represents the Bondy-Simonovits `ex(n, C_6) ≪ n^(7/6)` result.
Discharging it requires either (a) formalizing Bondy-Simonovits from
scratch in Lean (~500+ LOC research project) or (b) axiomatizing it
honestly.

**Recommendation for S5+ (deferred)**: convert `k3_case_solved` from
`sorry` to `axiom` with proper documentation. Then `k3_strong_implies_weak`
becomes mechanical: `obtain ⟨c, hc_pos, hbound⟩ := k3_case_solved; exact
(strong_implies_weak _ rfl.le).2 3 (by omega)` or similar.

### 3.4 L136 — HARD (genuine combinatorial work)

```lean
theorem ex_not_obviously_monotone_in_k :
    ¬(∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → ∀ n : ℕ, exGk k₁ n ≤ exGk k₂ n) := by
  sorry -- The monotonicity of extremal numbers in k is non-trivial for pair graphs
```

This requires exhibiting `k₁ < k₂` and `n` with `exGk k₁ n > exGk k₂ n`.
For pair graphs `G_k`, the addition of more pair vertices makes the
forbidden subgraph LARGER, so `G_{k+1}` is forbidden whenever `G_k` is
— meaning graphs avoiding `G_{k+1}` are a SUPERSET of those avoiding
`G_k`, so `exGk (k+1) n ≥ exGk k n`. Therefore the statement
"`∀ k₁ ≤ k₂, exGk k₁ n ≤ exGk k₂ n`" IS true — the theorem as written
seems to assert the wrong thing.

**Recommendation for S6+ (much later)**: re-examine the theorem
statement. As written it may be unprovable (the negation is false).
Possible corrections:
- Show that for small `n`, monotonicity FAILS due to combinatorial
  quirks (specific counterexample needed)
- Reformulate to show non-monotonicity in `n` (not `k`)
- Convert to an honest axiom or remove the theorem entirely

This is **not** an S3 priority.

---

## 4. Mathlib bearer survey (for S3 ACT)

| Bearer | Pinned location (target) | Used for |
|---|---|---|
| `Filter.Tendsto.atTop_add` | `Mathlib/Order/Filter/AtTopBot/Basic.lean` | shift `n` by `-1` in atTop |
| `tendsto_natCast_atTop_atTop` | `Mathlib/Analysis/SpecificLimits/Basic.lean` (or sibling) | `(n : ℝ)` tends to ∞ as `n : ℕ` does |
| `tendsto_inv_atTop_zero` / `Tendsto.inv_tendsto_atTop` | `Mathlib/Topology/Algebra/Order/Field.lean` | reciprocal of ∞ is 0 |
| `Filter.Tendsto.sub` | `Mathlib/Topology/Algebra/Group/Basic.lean` | sub two tends-to functions |
| `Finset.le_sup` | `Mathlib/Data/Finset/Lattice.lean` | extract bound from `Finset.sup` |
| `Nat.ceil_le` | `Mathlib/Algebra/Order/Floor.lean` | bound from ceiling |
| `Asymptotics.IsLittleO.isBigO` | (NOT relevant here — local `isLittleO` is custom) |

**Verification deferred to S3 ACT**: the `inv_tendsto_atTop` family has
several candidate names; first build iter will surface the exact name.

---

## 5. S3 ACT plan — minimal scope

**Target**: discharge sorry #4 (L165) only. Single mechanical
discharge, ~8 LOC paste-ready (§3.1 above).

**LOC delta**: +6 LOC net (replace 1 sorry-line with 7 lines).

**Axiom-budget impact**: net 0. Sorry count: 4 → 3.

**Docker risk**: 2-3 iters expected for bearer-name resolution
(`inv_tendsto_atTop` vs `Tendsto.inv_tendsto_atTop` vs
`tendsto_inv_atTop_zero`). At 6.9 Gi disk avail, single iter is
plausible; if disk hits 100% mid-build, ship as build-pending per
memory trap `_docker_build_disk_full_ship_build_pending_…`.

**ACT-readiness gate**:

| Check | Status |
|---|---|
| Sorry location confirmed | ✅ L165 |
| Replacement code drafted | ✅ §3.1 |
| Mathlib bearers identified | 🟡 inv_tendsto family TBD by build |
| Open PRs on slug = 0 | ✅ |
| Disk margin ≥ 5 Gi | 🟡 6.9 Gi (borderline) |
| Mathlib pin unchanged | ✅ |

**Recommendation**: ship S3 ACT when researcher is next free + disk
holds. Build-pending fallback if needed.

---

## 6. S4 ACT plan (after S3 lands)

**Target**: discharge sorry #1 (L112) — bigger, harder.

**LOC delta**: +15-25 LOC.

**Docker risk**: 3-5 iters (Finset.sup ceiling extraction is fiddly).
Defer until disk avail ≥ 50 Gi.

---

## 7. S5+ deferred work

- **L127 (k3_strong_implies_weak)**: convert parent `k3_case_solved`
  from sorry to axiom (4-LOC edit to parent, then 3-LOC discharge here).
- **L136 (ex_not_obviously_monotone_in_k)**: re-examine theorem
  statement; likely unprovable as written. Either reformulate or
  remove. ~30-60 min research-thinking required, not just Lean coding.

---

## 8. JSON delta plan (THIS PREP)

| Field | Old | New |
|---|---|---|
| `phase` (top-level) | `NEW` | `ORIENT` |
| `currentState.phase` | `ORIENT` (already) | unchanged |
| `currentState.iteration` | `1` | `2` |
| `currentState.since` | `2026-03-30T21:46:38Z` | `2026-05-16T09:20:00Z` |
| `currentState.focus` | "Initial exploration" | New text reflecting S2 PREP outcome |
| `currentState.nextAction` | "Begin problem exploration" | "S3 ACT: discharge sorry #4 at L165 (lower_bound_exponent_tendsto) via inv_tendsto_atTop chain (~8 LOC paste-ready, 2-3 Docker iters expected)" |
| `currentState.attemptCounts.total` | `0` | `1` (this PREP) |
| `knowledge.progressSummary` | (existing) | Prepend: "S2 PREP (2026-05-16): bootstrap orientation. 4-sorry inventory classified MECHANICAL (L112, L165) / BLOCKED (L127 on parent k3_case_solved) / HARD (L136 may be unprovable as stated). S3 ACT plan targets L165 with paste-ready ~8-LOC tendsto chain." |
| `knowledge.nextSteps` | (existing) | Append: "S3 ACT: discharge L165 sorry (mechanical Filter.Tendsto chain) | S4 ACT (deferred): discharge L112 sorry (o() → O() via Finset.sup ceiling extraction) | S5+ deferred: parent k3_case_solved sorry-to-axiom conversion to unblock L127; re-examine L136 theorem statement (likely unprovable as written)" |
| `lastUpdate` | `2026-03-30` | `2026-05-16T09:20:00Z` |

---

## 9. State.md delta plan (THIS PREP)

Replace entire body with bootstrap content reflecting actual prior work
(Lean file has 8 thms / 2 axioms / 4 sorries since at least 2026-03-30
PR) + the S2 PREP outcome + S3 ACT next-action.

---

## 10. What is NOT in this PREP

- No Lean file edits
- No Docker build attempts
- No new sorries / axioms / theorems
- No discharge of any sorry (those are S3+ ACTs)
- No bootstrap of `knowledge.md` (the JSON already has `knowledge.*`
  fields; markdown bootstrap can be a separate session if needed)

---

## 11. Cross-references

- **Parent**: `proofs/Proofs/Erdos1021Problem.lean` (241 LOC, 1 sorry,
  2 axioms; `k3_case_solved` blocks our L127)
- **Sibling**: `proofs/Proofs/Erdos1021Aristotle.lean` (Aristotle
  helpers, e.g., `rpow_decay_bound`)
- **Gallery**: `src/data/proofs/erdos-1021-oq-01/` (created in
  `knowledge.builtItems[5]`)
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
- **Memory traps applied**: `_docker_build_disk_full_ship_build_pending_…`
  (S3 ACT fallback), `_claim_random_returns_status_active_slugs_…` (this
  slug's top-level `phase: NEW` is genuinely stale, flipping to ORIENT)
