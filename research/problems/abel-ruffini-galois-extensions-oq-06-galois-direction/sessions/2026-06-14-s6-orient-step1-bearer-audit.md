# S6 ORIENT — Step 1 route bearer audit (researcher-1, 2026-06-14)

**Phase**: S6 ORIENT (build-free; Docker DOWN — verification blackout).
**Outcome**: ORIENT/knowledge. Re-verified the core bearer ecosystem at
the lake-pinned SHA and bearer-audited the **Step 1 (`sylow_p_unique`)**
proof route for the first time. Two additive findings: (1) the plan's
"`m < p`" Sylow-count framing is **circular**, and (2) the sound
(socle / minimal-normal-subgroup) route has **no Mathlib bearer** at the
pin. No `.lean` change; the 5 sorries are intact.

## 1. Bearer re-verification (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Verified by `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<pin>`
(host `.lake` is a self-referencing symlink — see S3, so direct file
fetch from the pin is the reliable audit channel). All present, no drift
since the 2026-06-01 confirmation:

| Bearer | Path : line | Role |
|--------|-------------|------|
| `IsPreprimitive` *extends* `IsPretransitive` | `Mathlib/GroupTheory/GroupAction/Primitive.lean:90` | Step 1 bootstrap: primitivity ⟹ transitivity via `.toIsPretransitive` (free) |
| `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` | `Mathlib/GroupTheory/GroupAction/Quotient.lean:180` | Step 1 bootstrap: transitive ⟹ `\|orbit\| = p ∣ \|H\|` |
| `Sylow.card_sylow_modEq_one` | `Mathlib/GroupTheory/Sylow.lean:312` | `n_p ≡ 1 [MOD p]` |
| `Sylow.card_dvd_index` | `Mathlib/GroupTheory/Sylow.lean:396` | `n_p ∣ index` |
| `Sylow.normal_of_subsingleton` | `Mathlib/GroupTheory/Sylow.lean:724` | Step 2 (already used) |
| `Sylow.unique_of_normal` | `Mathlib/GroupTheory/Sylow.lean:710` | uniqueness ↔ normal helper |
| `Equiv.Perm.isCycle_of_prime_order''` | `Mathlib/GroupTheory/Perm/Cycle/Type.lean:412` | Step 3 |

`Subgroup.le_normalizer` and the `mem_normalizer` conjugation API live in
`Mathlib/GroupTheory/Subgroup/Normalizer.lean` (file exceeds the GitHub
contents-API 1 MB cap so it returns empty over `gh api`; the lemma is a
standard textbook simp lemma and is present — confirm in a Docker-up
session). These are the bearers for the **corrected** Step 5 (~5–15 LOC).

## 2. Finding A — the plan's "`m < p`" Sylow-count framing is CIRCULAR

`knowledge.md` §"5-step proof plan" item 1 reads "Sylow uniqueness on H
at `\|H\| = p · m, m < p`", and the older state framed Step 1 as a Sylow
count. **This is circular.** The Sylow-count facts available
(`n_p ≡ 1 [MOD p]`, `n_p ∣ \|H\|/p`) force `n_p = 1` *only if* `\|H\|/p < p`.
But `H ≤ S_p` only gives `\|H\| ∣ p!`, so `\|H\|/p` can be as large as
`(p−1)!` — far bigger than `p`. The bound `m = \|H\|/p < p` is equivalent to
`\|H\| ∣ p(p−1)`, i.e. `H ≤ AGL(1,p)` — **the very conclusion** of the
file-level theorem. So Step 1 cannot be closed by a self-contained Sylow
count; it needs genuinely more structure.

What *is* available cheaply and non-circularly: `v_p(\|H\|) = 1` (from
`\|H\| ∣ p!` and Legendre `v_p(p!) = 1`), so the Sylow-p subgroup has
order exactly `p` (cyclic, a single `p`-cycle — this is the honest source
of Step 3, and it does **not** need Step 1). But order-`p` Sylow ⇏
*unique* Sylow without a normality argument.

## 3. Finding B — Step 1's sound route has NO Mathlib bearer

The textbook (Galois 1832 / Rotman 9.11) route to uniqueness is via the
**socle / minimal normal subgroup**: a minimal normal subgroup `N` of a
*solvable* primitive group is elementary abelian and acts *regularly*,
so `\|N\| = degree = p`; `N` is then the order-`p` normal (hence unique)
Sylow-`p`. Searching Mathlib at the pin for the required infrastructure:

- `MinimalNormal` (minimal normal subgroup) — **0 hits**
- group-theoretic `socle` — **0 hits**
- `IsElementaryAbelian` — **0 hits**

(GitHub code search can under-report, but three independent natural names
all returning zero is strong evidence the API is absent/thin.) **Step 1
is blocked on missing Mathlib infrastructure**, not merely on "sustained
multi-session work." Discharging it requires either building a
minimal-normal / regular-action layer from scratch, or finding an
alternative prime-degree-specific route (e.g. directly via the
`MulAction.IsBlock`/block-system API that *is* in `Primitive.lean`, deriving
regularity of the order-`p` Sylow from primitivity). This upgrades Risk
R3 and reshapes the Step-1 estimate.

## 4. Recommended next actions (for a Docker-up ACT session)

1. **Cheapest real progress**: fix Step 5's signature to the corrected
   form (already specified in the `⚠` docstring) and discharge it
   (~5–15 LOC) using `Subgroup.le_normalizer` + the normal-Sylow generator
   hypothesis from Steps 2/3. Step 5 is the only sorry whose *bearers are
   all present and whose math is settled*.
2. **Step 1 scoping spike**: prototype the order-`p` Sylow fact
   (`v_p(\|H\|) = 1` ⟹ `\|Sylow\| = p`) which is bearer-complete and also
   feeds Step 3; defer the uniqueness/normality core until a
   minimal-normal route is located or built.
3. Do **not** attempt Step 1 uniqueness as a Sylow count — it is provably
   insufficient (Finding A).

## Files touched
- this session file (new)
- `state.md` — Iteration 6 block + phase line
- `knowledge.md` — bearer table refresh + R3/Step-1 sharpening, plan item-1 correction
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` — `currentState`
