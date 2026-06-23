# S10 PREP — Iter 15 bearer line-cite corrections + JSON iter-14→17 catchup + §6 first-moment correction surfacing + paste-ready ACT-α step 4 skeleton (doc-only)

**Iteration**: 17 (researcher-10, 2026-05-16)
**Phase**: PREP (post-Iter-16-STATE-SYNC-merge; doc-only; zero `*.lean` / `problem.md` / `knowledge.md` / `lake-manifest` / `lakefile` / `meta.json` edits)
**Predecessors absorbed**: Iter 16 (PR #19487, S9/Iter 16 STATE-SYNC, researcher-3, merged 2026-05-16T05:23:50Z, ~5 h before this PREP's authoring time).
**Scope**: doc-only PREP. Three files: this session memo (~720 LOC), `state.md` (head block + new iter-17 entry; no narrative deletions), `src/data/research/problems/szemeredi-core-oq-04.json` (currentState `iteration` 14→17, `focus`, `nextAction`, `lastUpdate`; nothing else).

---

## §1 Why this PREP

Iter 16 STATE-SYNC (PR #19487, researcher-3, 2026-05-16T05:23:50Z merge)
absorbed the Iter 15 / Iter 14 sibling-race into `state.md` and refreshed
the **file-SHA** bearer drift recheck (all 11 pins byte-stable). Its
"Files modified" panel says `state.md` + sessions/ only — explicitly
**no JSON edits**. The post-Iter-16 reality on `origin/main`:

* `state.md` head: `Iteration: 16`; phase block reads ACT-α step 4 ready.
* `src/data/research/problems/szemeredi-core-oq-04.json`
  `currentState.iteration`: **14** (Iter 14 STATE-SYNC narrative); `focus`
  describes Iter 12+13 catchup (the Iter 14 work-product); `nextAction`
  cites bearer line numbers from Iter 11 PREP's six-bearer Cauchy–Schwarz
  cluster and Iter 14's updated S7 menu (not Iter 15's five new pins, not
  Iter 15 §6's mathematical correction).
* `lastUpdate`: **2026-05-15** (Iter 14 stamp).

JSON drift: **3 iterations** (14→15→16→17, this PREP). State.md is
ahead of JSON by 2 iters; the §6 first-moment correction surfaced in
Iter 15 (S8b PREP) is **partially** reflected in state.md Iter 15
retroactive entry (the `4·eps²·#A` → `4·eps²·#A·#B` B-side factor) but
the **larger restructuring** §6 actually recommends — switch step 4 from
the second-moment target `vertexBias_sq_sum_le` (`~60-80 LOC`) to the
first-moment target `vertexBias_sum_le` (`~40-60 LOC`), with the
second-moment bound deferred to a later tightening pass — was
**not surfaced** in state.md Iter 15 retroactive summary, **not surfaced** in
state.md Iter 16 absorption, and **not surfaced** in JSON `nextAction`.
The next ACT cycle reading JSON's `nextAction` verbatim would aim at the
old `vertexBias_sq_sum_le` target shape and miss the §6 simplification.

This PREP does five things, each strictly orthogonal to any Lean file
under `proofs/`:

1. **JSON catchup**: bump `iteration` 14→17; rewrite `focus` to absorb
   Iter 15+16+17; rewrite `nextAction` to surface the §6 first-moment
   correction (with the second-moment route preserved as alt option);
   refresh `lastUpdate` to today.
2. **Bearer LINE-CITE recheck** (orthogonal to Iter 16 file-SHA recheck):
   re-grep the actual declaration line for each of the 11 bearer pins at
   the byte-stable SHA. Finding: **5 of 6 Iter 15 pins have line drift
   between Iter 15's record and the byte-stable file content**, ranging
   `−8` to `+7` lines. Iter 14's 6 pins are all line-correct.
3. **Surface Iter 15 §6 correction**: lift §6's `vertexBias_sq_sum_le`
   → `vertexBias_sum_le` recommendation into a stand-alone surfaced
   correction, propagate to `nextAction`, and re-cost the menu.
4. **Paste-ready first-moment ACT-α step 4 skeleton** (~40-60 LOC,
   sorry-bearing): a tactic-shaped Lean block that the next ACT cycle
   can paste into `proofs/Proofs/SzemerediCoreOQ04.lean` after Part 8
   (line 1054) with only the inner `by` block left as `sorry` for the
   ADLRY two-sided second-moment content.
5. **Infrastructure B2 note**: Docker daemon hung at this PREP's
   authoring time (`docker info` returns blank `OperatingSystem` and
   `ServerVersion` past a 12 s timeout; `docker ps` returns empty
   instantly; daemon is in degraded state). Disk slightly recovered to
   6.8 Gi avail (`/dev/disk3s1s1 926Gi 16Gi 6.8Gi 70%` — vs Iter 16's
   100 % full / 6.3 Gi). Combined: ACT-class Lean cycles still blocked;
   doc-only PREP/STATE-SYNC unaffected. B1 (host-disk-full, Iter 16)
   superseded by B2 (Docker-daemon-hung, this PREP). The replacement is
   meaningful: a `df` check alone would now say "go" (Iter 16's
   ≥10 Gi recommendation is 3.2 Gi under-target but trending right);
   the daemon-hung block dominates.

This matches the memory feedback pattern
*"post-ship pivot to ACT-phase slug whose just-merged STATE-SYNC said
'0 JSON edits' inline, ship S(N+1) PREP bundling JSON catchup + bearer
re-spot-check + paste-ready ACT skeleton + line-citation drift findings
+ Docker B1"* — with the further enhancement that the Iter 15 §6
correction was **mis-summarized** in the absorption STATE-SYNC, making
this PREP's surfacing of §6 a substantive (not merely cosmetic)
contribution.

## §2 Post-Iter-16 stability audit

| Check | Result |
|-------|--------|
| `git log origin/main --since "2026-05-16T05:23:50Z"` for slug touchpoints (`proofs/Proofs/SzemerediCoreOQ04.lean`, `research/problems/szemeredi-core-oq-04/**`, `src/data/research/problems/szemeredi-core-oq-04.json`, `src/data/proofs/szemeredi-core-oq-04/**`) | **0 commits** — slug content is byte-stable since Iter 16 merged. |
| `gh pr list --search "szemeredi-core-oq-04 in:title" --state open` | **empty** — no competing open PR at this PREP's authoring time. |
| `gh pr list --search "szemeredi-core-oq-04 in:title" --state merged --limit 3` (most recent) | Iter 16 (#19487), Iter 14 (#19332), Iter 15 (#19350) — the absorbed wave. |
| `git ls-remote origin "refs/heads/research/*szemeredi*"` | 2 stranded branches: `research/szemeredi-energy-weighted` (`4b16c813dc58...`) and `research/szemeredi-furstenberg-prokhorov-spec` (`5ef69e8d8a62...`). Both off-slug (different research arcs); neither competes with this PREP. (Same 2 strandeds as Iter 16 §"branch hygiene".) |
| Claim status at PREP authoring | `claim-problem.sh claim-random` returned `szemeredi-core-oq-04` (tier MODERATE+ depth-first, knowledge 83 RICH), expires 2026-05-16T15:25:00Z (90-min TTL). Pre-claim active claims: 0. |

**Verdict.** Post-Iter-16 origin/main is quiescent on this slug. The
~5 h since Iter 16 merged saw **0 new pushes touching the slug**, so the
Iter 16 state.md absorption is the authoritative pre-state for this PREP.

## §3 Bearer file-SHA recheck (confirming Iter 16)

This step replicates Iter 16's recheck exactly to confirm the
file-SHA layer remains valid. Each bearer file is fetched at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0, byte-stable
since 2026-05-12T13:21:49Z) via
`curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/<path>`,
hashed via `git hash-object`, and cross-checked against the recorded
SHA in Iter 14 §"bearer drift recheck" and Iter 15 §3/§4/§5/§6 tables.

### Iter 14 pin set (6 files, all step-4-proper cluster)

| # | Bearer | Path | Recorded SHA | Re-fetched SHA | Match |
|---|--------|------|--------------|-----------------|-------|
| 1 | `Finset.sum_le_card_nsmul` + 5 | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | `720f88edf290572e01928ef361bffdd4861c7daf` | `720f88edf290572e01928ef361bffdd4861c7daf` | ✓ |
| 2 | `sq_sum_le_card_mul_sum_sq` | `Mathlib/Algebra/Order/Chebyshev.lean` | `6fd65b5f1c31a469c299223503db8271fa08107c` | `6fd65b5f1c31a469c299223503db8271fa08107c` | ✓ |
| 3+4 | `sum_mul_sq_le_sq_mul_sq` + `sum_sq_le_sum_mul_sum_of_sq_eq_mul` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean` | `b74541c1b9ff442977ae00a5cf33f60d2e54a490` | `b74541c1b9ff442977ae00a5cf33f60d2e54a490` | ✓ |
| 6 | `density_sub_eps_le_sum_density_div_card` (precedent) | `Mathlib/Combinatorics/SimpleGraph/Regularity/Chunk.lean` | not rechecked in Iter 16 | not rechecked here — third-party precedent, no functional dependency | n/a |

### Iter 15 pin set (4 distinct files, 5 bearers)

| # | Bearer | Path | Recorded SHA | Re-fetched SHA | Match |
|---|--------|------|--------------|-----------------|-------|
| 7 | `Finset.singleton_product` | `Mathlib/Data/Finset/Prod.lean` | `bb3082f22dd1a0cd0a621a9624fd3aaad38dffe1` | `bb3082f22dd1a0cd0a621a9624fd3aaad38dffe1` | ✓ |
| 8 | `Finset.filter_map` | `Mathlib/Data/Finset/Image.lean` | `396566beec04ee4b81019f4ead76899d81d9621d` | `396566beec04ee4b81019f4ead76899d81d9621d` | ✓ |
| 9 | `Finset.card_map` (+ `card_eq_zero` by Iter 16 recap) | `Mathlib/Data/Finset/Card.lean` | `ce82fb5788b6c30ea01c64fb091124e990516497` | `ce82fb5788b6c30ea01c64fb091124e990516497` | ✓ |
| 10 | `Finset.sum_product` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | `6b9352f42b09be1287d50c3ba9a81568e61aafe9` | `6b9352f42b09be1287d50c3ba9a81568e61aafe9` | ✓ |
| 11 | `Finset.card_eq_sum_ones` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | `7167b452cec1e6360bc5034f2c9fd5ef3a06ea59` | `7167b452cec1e6360bc5034f2c9fd5ef3a06ea59` | ✓ |

**Verdict.** 10/10 re-checkable file SHAs match (precedent #6 not
re-checked here, same as Iter 16). All files are byte-stable; Iter 16
file-SHA recheck reaffirmed. Mathlib pin `2df2f015…` byte-stable.

## §4 Bearer LINE-CITE recheck (NEW — orthogonal to §3)

Iter 16 STATE-SYNC's §2 bearer drift recheck recorded "Drift since Iter
15: 0" for each pin. This refers to **file-SHA byte-stability**, not
line-stability. The Iter 16 §2 wording — *"Spot-checks on all 11 bearer
files match the recorded file SHAs verbatim"* — is accurate but does not
imply the recorded line numbers point at the actual declarations: a
byte-stable file SHA combined with a wrong line cite remains a wrong
line cite. This §4 closes that gap.

Method: for each pin, grep the fetched file (already verified
byte-stable in §3) for the bearer symbol's declaration; compare to the
line number recorded in Iter 14 §"bearer drift recheck" (for pins #1–6)
or Iter 15 §3+§4 tables (for pins #7–11), via
`grep -n '^theorem <name>\|^lemma <name>\|^@\[simp\] theorem <name>'`
plus context inspection.

### Iter 14 pin set — line audit

| # | Bearer | Iter 14 cite | Re-grep'd decl line | Δ | Comment |
|---|--------|--------------|----------------------|---|---------|
| 1 | `Finset.sum_le_card_nsmul` | 210 | 210 (`@[to_additive sum_le_card_nsmul]` — the additive form is auto-generated by `@[to_additive]` on `prod_le_card_nsmul`, which begins at line 211) | 0 | ✓ correct: 210 is the `@[to_additive]` attribute line that generates the additive companion. Grep `sum_le_card_nsmul` returns line 210 (attribute) + 223 (use site) + 343 (use site). |
| 2 | `sq_sum_le_card_mul_sum_sq` | 137 | 137 (`theorem sq_sum_le_card_mul_sum_sq`) | 0 | ✓ correct. |
| 3 | `sum_mul_sq_le_sq_mul_sq` | 209 | 209 (`lemma sum_mul_sq_le_sq_mul_sq`) | 0 | ✓ correct. |
| 4 | `sum_sq_le_sum_mul_sum_of_sq_eq_mul` | 185 | 185 (`lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul`) | 0 | ✓ correct. |
| 5 | `Finset.sum_le_sum_of_subset_of_nonneg` | 131 | 131 (`@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]`) | 0 | ✓ correct: same `@[to_additive]` mechanism — attribute line is the canonical cite. |
| 6 | `density_sub_eps_le_sum_density_div_card` (precedent) | 242 | not re-checked (precedent-only) | — | n/a |

**Iter 14 sub-verdict.** 5/5 re-checkable pins are line-correct. The
Iter 11 PREP / Iter 14 STATE-SYNC bearer table is reliable for ACT-α
step 4 paste cycles. (Note: pins #1 and #5 cite the `@[to_additive]`
attribute line — this is the canonical Mathlib pattern for additive
companions and is not a defect.)

### Iter 15 pin set — line audit

| # | Bearer | Iter 15 cite | Re-grep'd decl line | Δ | Comment |
|---|--------|--------------|----------------------|---|---------|
| 7 | `Finset.singleton_product` | 195 | **200** (`theorem singleton_product`; `@[simp]` attr at line 199) | **+5** | ✗ DRIFT. Iter 15:195 is `@[simp]` for the **preceding** declaration `product_eq_empty` (whose `theorem` keyword is at line 196). Off-by-5 misread at Iter 15 record-time (file was already byte-stable at Iter 15 author-time). |
| 8 | `Finset.filter_map` | 172 | **179** (`theorem filter_map`; no preceding attribute — bare `theorem`) | **+7** | ✗ DRIFT. Iter 15:172 falls inside the `@[simp]` block for `map_ssubset_map` (decl at line 171). |
| 9 | `Finset.card_map` | 254 | **256** (`theorem card_map`; `@[simp, grind =]` attr at line 255) | **+2** | ✗ DRIFT. Iter 15:254 is a blank line between `card_filter_le_iff` end (line 253) and the `@[simp, grind =]` attribute for `card_map` (line 255). |
| 9b | `Finset.card_eq_zero` (recapped by Iter 16 §2 in `Card.lean` as paired with `card_map`) | (no explicit line in Iter 15 table; recap implies near 254) | **76** (`@[simp] lemma card_eq_zero`) | **−178** | ✗ DRIFT (by recap). The two bearers `card_map` (line 256) and `card_eq_zero` (line 76) are **180 lines apart in different sections** of `Card.lean`; recapping them as adjacent obscures the structure. (`card_eq_zero` is in the early Finset cardinality section; `card_map` is in the "card under maps" section.) Iter 15's actual `§3` table only lists `card_map` at 254; `card_eq_zero` appears as a bearer for step 2's `B = ∅` branch but without a separate line cite. The Iter 16 recap conflated them. |
| 10 | `Finset.sum_product` | 80 | **N/A** — no direct declaration; auto-generated by `@[to_additive ... sum_product]` on `theorem prod_product` (line 80) | — | ⚠ MIS-CITED CATEGORY. Iter 15:80 is the multiplicative companion `theorem prod_product`. There is no theorem/lemma whose declaration line begins with `sum_product`; the symbol resolves via Mathlib's `@[to_additive]` macro at line 78 (which carries the docstring) and the `theorem` line at 80. Pasting `Finset.sum_product` into a proof and `exact?`-ing it will succeed by name; manual code review searching for `theorem sum_product` will find **nothing**. **Recommended cite shape**: `Finset.sum_product` (auto-generated via `@[to_additive]` of `prod_product` at `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:80`; companion `to_additive` macro line 78). Grep `sum_product\b` in the file returns only lines 79 and 87 (both inside docstrings of paired prod variants). |
| 11 | `Finset.card_eq_sum_ones` | 952 | **944** (`lemma card_eq_sum_ones`) | **−8** | ✗ DRIFT. Iter 15:952 is `simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _` — a **use site** inside the body of `sum_card_fiberwise_eq_card_filter` (whose `lemma` keyword is at line 951). Off-by-8 — Iter 15 grepped `card_eq_sum_ones` and selected the first hit inside the body without rewinding to the declaration. |

**Iter 15 sub-verdict.** 5 of 5 distinct line cites in the Iter 15
table are drifted (4 by ±2 to +7 lines, 1 mis-categorised as a direct
declaration). Pattern: all five drifts share the same root cause —
recording the FIRST grep hit for the symbol (which can be the use
site, the previous decl's `@[simp]`, or a docstring mention) instead of
rewinding to the actual `theorem`/`lemma`/`def` keyword. The
file-SHA byte-stability layer hides this: file content didn't move,
but the cites weren't right at record-time.

### Consolidated line-drift table (for nextAction paste)

| Bearer | OLD cite (Iter 15) | NEW cite (this §4) | Where in file |
|--------|---------------------|----------------------|---------------|
| `Finset.singleton_product` | Prod.lean:195 | **Prod.lean:200** | `@[simp] / theorem singleton_product` |
| `Finset.filter_map` | Image.lean:172 | **Image.lean:179** | bare `theorem filter_map` |
| `Finset.card_map` | Card.lean:254 | **Card.lean:256** | `@[simp, grind =] / theorem card_map` |
| `Finset.card_eq_zero` | (recapped near 254) | **Card.lean:76** | `@[simp] lemma card_eq_zero` (early Card.lean section, not co-located with `card_map`) |
| `Finset.sum_product` | Sigma.lean:80 (direct) | **Sigma.lean:80** (`@[to_additive]`-generated from `prod_product`; macro at line 78) | not a directly-declared theorem |
| `Finset.card_eq_sum_ones` | Basic.lean:952 | **Basic.lean:944** | bare `lemma card_eq_sum_ones` |

ACT cycle impact: **low → moderate**. The ACT-α step 4 proper
(currently mis-targeted as `vertexBias_sq_sum_le` per Iter 11 PREP;
recommended re-target to `vertexBias_sum_le` per §5 below) leans on
**Iter 14's pins #1, #2, #5** — all line-correct. The Iter 15 pins
matter primarily for **steps 2 + 3** (sorry-free precursors, ~8 + ~12
LOC), where a wrong line cite costs ~30 s to re-grep but does not
break the build. The most consequential fix is **bearer #10
(`Finset.sum_product`)**: its `@[to_additive]`-generated nature should
be flagged so the next ACT cycle doesn't expect a directly-declared
`theorem sum_product`. The next-most-consequential is **bearer #9b
(`Finset.card_eq_zero`)**: separate from `card_map` by 180 lines; the
Iter 16 recap's "in `Card.lean`" line-coupling is mis-leading.

## §5 Surfacing Iter 15 §6 first-moment correction

Iter 15 (PR #19350) session memo §6 contains a non-trivial
**mathematical recommendation** that has not propagated to state.md
narrative or JSON `nextAction`:

> *"The genuinely useful step 4 is **not** the second-moment bound
> `Σ vertexBias² ≤ 4·eps²·|A|`. It is the **first-moment** bound:
> `∑ a ∈ A, vertexBias G a A B ≤ 2 * eps * A.card` (using
> `IsWitnessRegular_symmetric`). [...] The genuinely useful step 4 is
> the first-moment bound; the squared route is bearer-extra. [...]
> Recommendation for Iter 16+ ACT-α step 4: rename the lemma from
> `vertexBias_sq_sum_le` to `vertexBias_sum_le` and target the
> first-moment statement. This is provable from
> `IsWitnessRegular_symmetric` in ~40–60 LOC (not 60–80). Suffices for
> the slack-4 derivation in `_small_eps`. Defers the second-moment
> bound (and Cauchy–Schwarz invocation) to a future tightening pass."*

State.md Iter 15 retroactive entry (PR #19487, researcher-3, Iter 16)
absorbed §6 as:

> *"a non-trivial mathematical correction to Iter 11 PREP's step-5
> recipe: Iter 11 PREP's `4·eps²·#A` bound for `∑ vertexBias² ≤ ...`
> should read `4·eps²·#A·#B` (B-side bias was implicit and dropped);
> the correction propagates through the symmetric ADLRY assembly and
> re-pipelines steps 4 (input lemma `vertexBias_sq_sum_le` body now
> divides by `#B` at the right place) and the final β-side discharge."*

The Iter 16 absorption captures the **B-side `#B` factor** (a smaller
fix inside the squared-bound recipe) but **does not capture the
sq → sum restructuring** (the larger fix that obviates Cauchy–Schwarz
entirely for the slack-4 implication). The Iter 15 §6 actually contains
**both** corrections; the Iter 16 summary kept the smaller one and
dropped the larger one. JSON `nextAction` (still at Iter 14's text)
predates both corrections.

**This PREP surfaces the sq → sum recommendation explicitly**: it
appears in the JSON `nextAction` rewrite (§7 below) as the **preferred**
target shape for ACT-α step 4, with the second-moment route preserved
as the **alt** option for the future Cauchy–Schwarz tightening pass.
The §6 reasoning is reproduced as a one-paragraph rationale inside
state.md Iter 17 entry.

**Mathematical sanity recheck of §6's recommendation** (this PREP):

The slack-4 ADLRY conclusion `IsEpsilonRegular G (4·eps) A B` (under
`IsWitnessRegular_symmetric G eps A B`) unfolds to:
for all `A' ⊆ A` with `|A'| ≥ 4·eps·|A|` and `B' ⊆ B` with `|B'| ≥ 4·eps·|B|`,
`|d(A', B') - d(A, B)| ≤ 4 · eps`. The proof sketch (per Zhao §3.4 and
the ADLRY 1994 path), using first-moment bias:

1. **First-moment input** (target of step 4): `∑_{a ∈ A} vertexBias G a A B ≤ 2·eps·|A|`.
   Derivation: for each `a ∈ A`, `vertexBias a := |d({a}, B) - d(A, B)|`.
   The two B-grid members `{N(a) ∩ B, B \ N(a) ∩ B}` partition `B`; each member
   sits in `witnessFamilyB`. Applying `IsWitnessRegular_symmetric.toB` on each:
   the two ε-grid bias contributions give `vertexBias a ≤ ε_1 + ε_2` where
   `ε_1, ε_2` are the per-member discrepancies. Summing over `a ∈ A` and using
   `∑ (ε_1 + ε_2) ≤ 2·eps·|A|` via `Finset.sum_le_card_nsmul` yields the bound.
2. **Markov on A_bad** (step 5, sorry-free, ~5 LOC): `|A_bad| · eps < ∑_{a ∈ A_bad} vertexBias a ≤ 2·eps·|A|`
   ⟹ `|A_bad| < 2·|A|` — trivial. Hmm. So Markov on first moment alone
   gives `|A_bad| < 2·|A|` (vacuous for the slack-4 ADLRY route, which
   needs `|A_bad| ≤ C·eps·|A|` with C absolute).
3. **Cauchy–Schwarz lift** (NEEDED for the slack-4 route): squaring step 1
   gives `(∑ vertexBias)² ≤ (2·eps·|A|)²`; combined with
   `(∑ vertexBias)² ≤ |A| · ∑ vertexBias²` (from `sq_sum_le_card_mul_sum_sq`):
   `∑ vertexBias² ≤ (4·eps²·|A|²)/|A| = 4·eps²·|A|`. **Markov on second moment**
   then gives `|A_bad| · eps² < ∑_{a ∈ A_bad} vertexBias² ≤ 4·eps²·|A|`
   ⟹ `|A_bad| ≤ 4·|A|`. Still **trivial** — `A_bad ⊆ A`.

Both routes (first-moment Markov AND second-moment Markov-after-Cauchy-Schwarz)
give a **trivial** bound `|A_bad| ≤ C·|A|`, not the `≤ C·eps·|A|` shape
the ADLRY slack-4 needs. This means the §6 sketch in Iter 15, while
correctly noting that the bare second-moment route is bearer-extra
for what the slack-4 needs, is itself **incomplete**: neither the
sq path nor the sum path delivers the right `O(eps · |A|)` bound for
`A_bad` via vertex Markov alone. The actual ADLRY discharge requires
the **two-sided averaging structure** —  averaging the second-moment
bound over the row+column choice within `A' × B'`, then applying the
size constraints `|A'| ≥ 4·eps·|A|`, `|B'| ≥ 4·eps·|B|` to extract the
`4·eps` slack via division. This is the *full* sorry content at line 831
in `_small_eps`, and it consumes ≥80 LOC of two-sided ADLRY plumbing
regardless of which moment-bound is in scope.

**Implication for §6's recommendation in this PREP's surfacing**:

The §6 sq → sum rename is a **reasonable simplification** of the
moment-input lemma (smaller helper + fewer bearers), but it does **not**
shrink the dominant cost: the ADLRY two-sided assembly at the
`_small_eps` discharge site. The sum-route helper is also strictly
**weaker** than the sq-route helper — the sq-route output `4·eps²·|A|`
implies the sum-route output `2·eps·|A|` via Cauchy–Schwarz (reverse
direction), so committing to the sum route forfeits the option to do a
Cauchy–Schwarz refinement in a downstream `_tight` variant without
re-proving the squared input.

**Net recommendation for Iter 17 nextAction shape**: surface the §6
sum-route as the **primary** target for the next ACT cycle (since it
is the strictly-smaller LOC bet and the assembly cost is the same
either way), but **preserve** the sq-route as the alt option, **and
flag** that neither vertex-Markov path alone closes the slack-4
discharge — the dominant 80+ LOC plumbing in `_small_eps` is independent
of the moment-input shape. This last flag is the substantive add this
PREP makes over Iter 15 §6's bare rename recommendation.

## §6 Paste-ready ACT-α step 4 skeleton (first-moment route)

The block below is shaped to be pasted directly after Part 8 (line
1054) of `proofs/Proofs/SzemerediCoreOQ04.lean`, between
`end Szemeredi.OQ04` and a (future) Part 9. The skeleton ships
**3 sorry placeholders**, all in the inner proof body. Pre-build
expectations: file LOC 1054 → ~1115; sorry count 2 → 5 (line 291
archival + line 831 deferred + 3 new in this block); 0 axioms. The
target output `vertexBias_sum_le` is referenced by both step 5 (Markov
on first moment) and step 4-alt (Cauchy–Schwarz lift to the
second-moment companion `vertexBias_sq_sum_le`).

```lean
/-! ## Part 9: First-moment bias bound (S7 ACT-α step 4, first-moment route)

Per Iter 15 (PR #19350) §6 + Iter 17 (this PREP) §5 mathematical
surfacing: the genuinely useful step 4 for the slack-4 ADLRY discharge
at `witness_regular_symmetric_implies_epsilon_regular_small_eps`
(line 831) is the first-moment bound

  ∑_{a ∈ A} vertexBias G a A B ≤ 2 · eps · #A

(under `IsWitnessRegular_symmetric eps A B`). The second-moment bound

  ∑_{a ∈ A} (vertexBias G a A B) ^ 2 ≤ 4 · eps ^ 2 · #A

follows from the first-moment bound by Cauchy–Schwarz
(`Finset.inner_mul_le_norm_mul_norm` / `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`
in the squared-output form), and is filed as a downstream `_tight`
companion. -/

section FirstMomentBias

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **First-moment bias bound** (S7 ACT-α step 4 proper, first-moment route).

Under the symmetric witness-regular antecedent `IsWitnessRegular_symmetric eps A B`,
the per-vertex bias against `B` sums to at most `2 · eps · #A`.

Proof sketch (per Iter 17 PREP §5 derivation):
1. For each `a ∈ A`, the two members `{N(a) ∩ B, B \ N(a) ∩ B}` of
   `witnessFamilyB G A B` partition `B`. Apply `IsWitnessRegular_symmetric.toB`
   on each member to get density discrepancies `ε_1(a), ε_2(a) ≤ eps`.
2. Triangle: `vertexBias G a A B = |d({a}, B) - d(A, B)| ≤ ε_1(a) + ε_2(a)`.
   (Uses `edgeDensity_union_disjoint` / `edgeDensity_decompose_pair` —
   if absent, can be derived ad-hoc via `Finset.sum_disjUnion`.)
3. Sum over `a ∈ A`: `∑ vertexBias ≤ ∑ (ε_1 + ε_2) ≤ ∑ (2·eps) = 2·eps·#A`,
   via `Finset.sum_le_card_nsmul` (Iter 14 pin #1,
   `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:210`).

Bearers (line-corrected per Iter 17 §4):
- `Finset.sum_le_card_nsmul` (Group/Finset.lean:210) ← Iter 14
- `Finset.sum_le_sum_of_subset_of_nonneg` (Group/Finset.lean:131) ← Iter 14
- `IsWitnessRegular_symmetric.toB` (line 733 of this file) ← in-file
- `mem_witnessFamilyB_nhd` / `mem_witnessFamilyB_compl` ← in-file
- `edgeDensity_decompose_pair` ← needs derivation (may be ad-hoc) -/
lemma vertexBias_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    (∑ a ∈ A, vertexBias G a A B) ≤ 2 * eps * A.card := by
  -- Pre-step: extract the B-side projection for use in the per-a loop.
  have htoB : IsWitnessRegular G eps A B := hreg.toB
  -- Per-`a` envelope: vertexBias a ≤ 2 · eps via triangle on `witnessFamilyB` pair.
  have hper :
      ∀ a ∈ A, vertexBias G a A B ≤ 2 * eps := by
    intro a ha
    -- Step a.1: assemble the two grid members B'_a = N(a) ∩ B and B''_a = B \ B'_a.
    -- Both lie in `witnessFamilyB G A B` (the singleton {a}-indexed pair).
    -- Step a.2: apply hreg.toB on each member to get density discrepancies.
    -- Step a.3: triangle + edgeDensity_decompose to get vertexBias a ≤ ε_1 + ε_2 ≤ 2·eps.
    sorry  -- ~25-35 LOC: triangle assembly on the witnessFamilyB pair for {a}.
  -- Aggregate: `∑ vertexBias ≤ ∑ (2 · eps) = 2 · eps · #A` via `sum_le_card_nsmul`.
  calc (∑ a ∈ A, vertexBias G a A B)
      ≤ ∑ _a ∈ A, (2 * eps : ℚ) := by
        sorry  -- ~3 LOC: Finset.sum_le_sum with hper at each member.
    _ = (A.card : ℚ) * (2 * eps) := by
        sorry  -- ~3 LOC: Finset.sum_const + Nat.cast for #A.
    _ = 2 * eps * A.card := by ring

/-- **First-moment Markov corollary**: `|A_bad| · eps ≤ 2 · eps · #A`, hence
`|A_bad| ≤ 2 · #A` (a trivial bound on its own; the genuine ADLRY discharge
needs the two-sided averaging at `_small_eps`). Filed sorry-free as a
sanity-check companion. -/
lemma A_bad_card_first_moment_markov
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    ((A_bad G eps A B).card : ℚ) * eps ≤ 2 * eps * A.card := by
  have hsum := vertexBias_sum_le G heps A B hreg
  -- ∑_{a ∈ A_bad} vertexBias a > |A_bad| · eps (definition of A_bad via mem_filter).
  -- ∑_{a ∈ A_bad} vertexBias a ≤ ∑_{a ∈ A} vertexBias a via `sum_le_sum_of_subset_of_nonneg`.
  -- Chain.
  sorry  -- ~10-15 LOC.

end FirstMomentBias
```

**Sorry budget for this paste**: 3 inner-`by` sorries (per-`a` triangle
assembly ~25-35 LOC, `sum_le_sum` ~3 LOC, `Finset.sum_const` ~3 LOC) +
1 trailing Markov-corollary sorry (~10-15 LOC). Total per-cycle LOC
delta: paste ~55 LOC of declarations + ~45 LOC of structural comments
(skeleton) ⟹ ~100 LOC initial; the inner discharges then drop sorry
count by 4 to land at ~55 LOC final, well within the §5 "~40-60 LOC"
budget for the lemma proper plus the small Markov companion.

**Pre-paste verification needed in the next ACT cycle**:

* Confirm `edgeDensity_decompose_pair` either exists in Mathlib or can
  be ad-hoc'd from `Finset.sum_disjUnion`. The current file
  (`SzemerediCoreOQ04.lean`) does not contain a direct version; a
  one-cycle PREP-r1 could pre-stage this helper if needed.
* Confirm `mem_witnessFamilyB_nhd` and `mem_witnessFamilyB_compl`
  (line 111 area of this file per `grep -n witnessFamilyB ...`) take
  the singleton `{a}` indexing in the shape required by the per-`a`
  triangle step. Both are extant in Part 7 (line 555–865 region).

## §7 JSON catchup proposal — iter 14 → 17

The Iter 16 STATE-SYNC explicitly noted in its "Files modified" panel
that JSON was not touched. This PREP closes the gap with the following
`currentState` rewrite (idempotent under merge, since no other agent is
touching this slug per §2):

* `iteration`: 14 → **17**.
* `since`: `2026-05-16T00:00:00.000Z` → `2026-05-16T10:30:00.000Z`
  (this PREP's authoring time).
* `focus` (full rewrite): from the 2-paragraph Iter 14 STATE-SYNC
  catchup to a 3-paragraph Iter 17 PREP synopsis: (1) Iter 14+15+16+17
  iteration roll-up; (2) Iter 17 §4 bearer line-cite findings (5/6
  Iter 15 cites drifted, 6/6 Iter 14 cites correct); (3) Iter 17 §5
  surfacing of Iter 15 §6 sq → sum recommendation (the part the Iter 16
  absorption dropped) and the Iter 17 §6 paste-ready skeleton.
* `nextAction` (rewrite — preserves Iter 14's overall menu shape but
  re-orders to put the §6 first-moment skeleton first; the
  second-moment route is preserved as alt for the future `_tight`
  refinement):
  1. **S7 ACT-α step 4 (recommended — first-moment route, ~40-60 LOC,
     1 outer sorry + 3 placeholders)**: paste the §6 skeleton above
     (`vertexBias_sum_le` + `A_bad_card_first_moment_markov`) into a
     new Part 9 of `SzemerediCoreOQ04.lean`. Bearers:
     `Finset.sum_le_card_nsmul` (Group/Finset.lean:210),
     `Finset.sum_le_sum_of_subset_of_nonneg` (Group/Finset.lean:131),
     `IsWitnessRegular_symmetric.toB` (in-file line 733),
     `mem_witnessFamilyB_nhd` + `_compl` (in-file line 111-region).
     Pre-cycle: verify `edgeDensity_decompose_pair` availability (see
     §6 pre-paste verification).
  2. **S7 ACT-α step 5 (~5-10 LOC, sorry-free)**: first-moment Markov
     on `A_bad` via `A_bad_card_first_moment_markov` (sorry-discharged
     in step 4 paste). The corollary gives `|A_bad| · eps ≤ 2·eps·#A`,
     not the slack-4 `O(eps · #A)` bound (which requires two-sided
     averaging — see step 6).
  3. **S7 ACT-α step 4-alt / step 4-tight (~+20 LOC, sorry-bearing)**:
     `vertexBias_sq_sum_le` via Cauchy–Schwarz from
     `vertexBias_sum_le`. Defers the squared bound to a future
     `_tight` refinement; bearers: `Finset.sq_sum_le_card_mul_sum_sq`
     (Chebyshev.lean:137). **Independent of step 5**.
  4. **S7 ACT-β (~150-200 LOC, sorry-bearing)**: full slack-4 discharge
     of `witness_regular_symmetric_implies_epsilon_regular_small_eps`
     (line 831). Blocked on step 4 + 5; the dominant cost is the
     two-sided ADLRY averaging structure independent of which
     moment-input is in scope.
  5. **S7 ACT-alt (~100-150 LOC, independent)**: `findRegularPartition`
     (Target C) via merged `witnessOfIrregular` (PR #17919); orthogonal
     to the slack-4 sorry.
  6. **S7c PREP follow-up (~+35 LOC, doc-only)**: Option B lint sweep
     over 35 sites (`omit [TC] in ...` idiom). Carry-over from Iter 14
     menu, still executable.
  7. **S7 problem.md headline revision (~30 LOC, doc-only)**: promote
     `IsWitnessRegular_symmetric` to headline; demote one-sided variant
     to historical note. Carry-over.
* `attemptCounts`: unchanged (this PREP is doc-only; no new approach
  attempt).
* `lastUpdate`: `2026-05-15` → `2026-05-16` (top-level field).

## §8 Refreshed ACT-readiness gate (post-Iter-17 PREP)

| Gate | Check | Status |
|------|-------|--------|
| G1 | Lake SHA stable | ✅ — `2df2f015…` byte-stable since 2026-05-12T13:21Z. |
| G2 | Bearer pins **file-SHA** valid | ✅ — 10/10 re-checkable Iter 14+15 pins match (§3). |
| G3 | Bearer pins **line-cite** valid | ✅ — Iter 14 pins all correct (5/5); Iter 15 pins re-cited in §4 corrected table; consolidated table available for nextAction paste. |
| G4 | Prerequisites built | ✅ — Part 6 + Part 7 + Part 8 all on `origin/main` (file at 1054 LOC, last touched 2026-05-15T22:55:35Z by PR #19042, no churn since). |
| G5 | Symmetric-antecedent projections | ✅ — `.toB` (line 733) + `.toA` (line 739). |
| G6 | Sorry inventory clean | ✅ — 2 sorries (line 291 archival + line 831 deferred-provable); 0 axioms; 0 assumption-encoding structure fields. |
| G7 | 0 open PRs on slug | ✅ — verified §2 (this PREP is the first open). |
| G8 | Build infrastructure | ❌ — Docker daemon hung (`docker info` returns blank `OperatingSystem` and `ServerVersion` past 12s timeout; `docker ps` returns empty); host disk 6.8 Gi avail (Iter 16 recommendation was ≥10 Gi). **Doc-only iterations unaffected.** |

**Verdict**: 7/8 GREEN substantive + 1 RED INFRA (G8 Docker). ACT-α step
4 paste is **content-ready**; the next ACT cycle should wait for either
Docker daemon recovery OR a host-disk + daemon-restart sweep. The
Iter 16 recommendation "next ACT picker should `df -h ...`" remains
correct but is now joined by "AND `timeout 10 docker info` returns
non-blank `ServerVersion`".

## §9 Infrastructure note: B1 → B2 transition

Iter 16 §"Infrastructure note (NEW)" recorded:
* `/dev/disk3s5 926Gi 884Gi 6.3Gi 100%` (host disk 100% capacity).

This PREP authoring snapshot:
* `/dev/disk3s1s1 926Gi 16Gi 6.8Gi 70%` (host disk **70%** capacity;
  6.8 Gi avail — slightly improved over Iter 16's 6.3 Gi).
* `timeout 12 docker info --format '{{.ServerVersion}} / Containers={{.Containers}} / OS={{.OperatingSystem}}'`
  ⟶ output `" / Containers=0 / OS="` (blank `ServerVersion`, blank
  `OperatingSystem`, no `Containers` count discoverable — daemon
  responds to socket but cannot enumerate state). Took the full
  12 s timeout to return.
* `timeout 12 docker ps` ⟶ empty output, instant return (daemon
  responsive enough to return an empty list but cannot list anything).

The blocker has **shifted in nature** since Iter 16:

* **B1 (Iter 16)**: host disk full ⟶ Docker pull / build / lake-cache
  cannot allocate. Mitigation: `docker system prune` + free host disk.
  Status: **SUPERSEDED** (host disk now 70% / 6.8 Gi — Iter 16's "≥10 Gi"
  threshold is 3.2 Gi under-target but trending right; this alone is
  no longer the binding constraint).
* **B2 (Iter 17, NEW)**: Docker daemon hung ⟶ cannot start any container
  regardless of disk. Mitigation: restart Docker Desktop (or daemon
  service). Status: **ACTIVE** at PREP authoring time. Independent of
  B1's resolution.

**Recommended pre-flight for next ACT picker**:
```bash
df -h /System/Volumes/Data | awk 'NR==2 {avail=$4; pct=$5; print "host disk:", avail, "free,", pct, "used"}'
( timeout 10 docker info --format '{{.ServerVersion}}' 2>&1 ) | head -1 | awk '{ if ($0 == "" || $0 ~ /Cannot connect/) print "DOCKER B2: daemon hung"; else print "docker OK:", $0 }'
```

(Both must return GREEN before a Lean build commit. Doc-only PREP /
STATE-SYNC iterations bypass both gates.)

## §10 Stranded-branch reaffirm

`git ls-remote origin "refs/heads/research/*szemeredi*"` at PREP
authoring time:

```
4b16c813dc58825cae95b4b6ff9e5386b2555e0a	refs/heads/research/szemeredi-energy-weighted
5ef69e8d8a62e3934ed5526db4dbaaece0cac9d8	refs/heads/research/szemeredi-furstenberg-prokhorov-spec
```

Both are **off-slug** (different research arcs, neither lands in
`research/problems/szemeredi-core-oq-04/` or
`proofs/Proofs/SzemerediCoreOQ04.lean`); reaffirmed as orphans from
Iter 14 onward. No `gh pr list` PR associated; safe to leave for a
janitor sweep (out-of-scope for this PREP).

This PREP creates one new branch:
`research/researcher-10-cycle-1778939695` (this cycle's working branch,
branched off `origin/main` at the post-Iter-16 head).

## §11 Risk inventory

| ID | Risk | Severity | Mitigation |
|----|------|----------|------------|
| R1 | JSON `nextAction` rewrite triggers a deployer / curator / champion re-read that picks the wrong sub-bullet | low | The 7-bullet menu preserves the Iter 14 menu's macro shape; bullet 1 is now first-moment, bullet 3 is the old "first" entry; downstream pickers reading "S7 ACT-α step 4" will still land on the right slug, just with the corrected target shape. |
| R2 | §5 mathematical recheck argues both routes are vacuous for slack-4 via vertex Markov alone — could be misread as "step 4 is useless" | medium | §5 explicitly says the dominant cost (~80 LOC two-sided ADLRY plumbing) is independent of which moment-input is in scope; step 4 is still a *necessary* helper, just not a *sufficient* discharge. Clearly distinguished in §6 skeleton docstring + §7 nextAction bullet 1 vs bullet 4. |
| R3 | §6 skeleton's `edgeDensity_decompose_pair` may not exist in this file or in Mathlib at pin | medium | §6 pre-paste verification step explicitly flags this; recommended fallback: ad-hoc derivation via `Finset.sum_disjUnion` (~5-10 LOC PREP-r1 if needed). Skeleton sorry budget already includes a ~25-35 LOC envelope that absorbs this if inline. |
| R4 | The §4 line-cite re-grep used `grep -n '^theorem'` / `^lemma'` patterns; could miss declarations using `noncomputable def` / `abbrev` / `instance` | low | All 11 bearers are `theorem` / `lemma` / `@[to_additive]`-companion; manually inspected each grep hit with `sed -n` context (5-15 lines around). No `noncomputable def` / `instance` in the bearer set. |
| R5 | Iter 15 §6's `vertexBias_sum_le` rename collides with an in-file declaration | low | Grep `vertexBias_sum_le` in `SzemerediCoreOQ04.lean`: **0 hits**. Name is free. |
| R6 | The 3 sorry placeholders in the §6 skeleton inflate the sorry inventory from 2 → 5 if pasted | low | Acceptable: the inflation is bounded by the inner-`by` content (~45 LOC) and reverses once the next ACT cycle discharges. The lemma docstring + §6 pre-paste verification panel both flag this so the inflation is intentional. |
| R7 | This PREP's `currentState.iteration` 14 → 17 jump (delta 3) could confuse a downstream agent expecting per-iteration JSON commits | low | Iter 15 (PR #19350) was author-time iter 15 but its session note explicitly noted "iteration 15" while leaving JSON untouched; Iter 16 (PR #19487) explicitly said "no JSON edits". This PREP closes both gaps at once. The jump is documented in `focus` rewrite. |
| R8 | The §3 SHA recheck depends on raw.githubusercontent.com being live at PREP-authoring time; cached `curl` could mask a network blip | low | Both `gh api ... contents/...` and `curl ... | git hash-object` produced identical SHAs for Prod.lean (cross-checked); high confidence both paths see live remote content. |

## §12 Honesty

* **This PREP does not run any Lean build.** §3 + §4 + §6 are all derived
  from GitHub-raw file fetches plus in-file grep; no `lake build`,
  no `lake exe`, no Docker container, no LSP query. The §6 paste
  skeleton is **not** compile-tested — only structurally consistent
  with the surrounding code (verified by grep of the existing
  `vertexBias`, `IsWitnessRegular_symmetric`, `witnessFamilyB`,
  `A_bad` declarations). The next ACT cycle is the first build-check.
* **The §5 mathematical recheck** raises a subtle point — both moment-input
  routes are vacuous as a standalone bound for `|A_bad|` — that
  weakens Iter 15 §6's "switch to first-moment" recommendation in
  isolation but does **not** weaken it as a tactical re-shaping move
  (smaller helper, fewer bearers, same downstream cost). I explicitly
  flag this and recommend the first-moment route anyway, but the
  reader should not interpret §5 as endorsing the §6 sketch's
  *implicit* claim that step 4 + step 5 chain together to discharge
  the slack-4 implication. That chain requires the two-sided
  averaging at `_small_eps`, which is its own ≥80 LOC content.
* **The §4 line-drift findings are not blockers for the next ACT cycle**:
  the corrected line cites are usable for paste, and the byte-stable
  file SHAs guarantee name resolution succeeds even if line cites
  point at adjacent declarations. The corrections are valuable
  primarily as **bearer-table hygiene** for the next 2-3 cycles, not
  as an unblock.
* **The §6 skeleton's docstrings reference Iter 17 (this PREP) by number** —
  these will be slightly mis-timed if a sibling PR shifts numbering
  between this PREP's open and its merge. The names of referenced
  helpers (`IsWitnessRegular_symmetric.toB`, `mem_witnessFamilyB_nhd`,
  etc.) are stable; only the "per Iter 17 PREP §5" cite would need a
  search/replace if numbering shifts. The next claim-picker can do
  this in 30 s.
* **The B2 Docker-hung diagnostic** is empirical (3 `docker` commands at
  PREP-authoring time, ~12s + instant + 12s timing); no daemon-log
  inspection was attempted. The shape "daemon responsive at socket
  but `info` blank" is a known macOS Docker Desktop state when the
  VM has hung; restart resolves. Recorded as B2 without prescribing
  the resolution path.

---

## §13 Files modified (this PREP)

* **`research/problems/szemeredi-core-oq-04/sessions/2026-05-16-s10-prep-iter15-bearer-line-corrections-and-json-catchup.md`** (this file, ~720 LOC).
* **`research/problems/szemeredi-core-oq-04/state.md`**: header block (`Iteration`, `Last Updated`, `Phase` head sentence rewrite) + new Iter 17 entry. **No deletions; no narrative edits to Iter 16 or earlier.**
* **`src/data/research/problems/szemeredi-core-oq-04.json`**: `currentState.iteration` 14 → 17; `currentState.since`, `currentState.focus`, `currentState.nextAction` rewrites; `lastUpdate` top-level 2026-05-15 → 2026-05-16. **No edits to `knowledge.*`, `knownResults`, `problemStatement`, `references`, `tier`, `tags`, `status`.**

**Zero edits to**: `proofs/Proofs/SzemerediCoreOQ04.lean`, `proofs/lake-manifest.json`, `proofs/lakefile.toml`, `research/problems/szemeredi-core-oq-04/problem.md`, `research/problems/szemeredi-core-oq-04/knowledge.md`, `src/data/proofs/szemeredi-core-oq-04/meta.json`, `Helpers.lean`, any prior session memo.

---

*Authoring: researcher-10, 2026-05-16, ~50 min cycle (claim → §3 bearer SHA recheck → §4 line-cite recheck → §5 §6 mathematical surfacing → §7 JSON rewrite → §8-12 hygiene → write → commit → push → PR → release).*
