# Pentagonal Number Theorem — OQ-01

## Problem

Euler's pentagonal number theorem expands `∏_{n≥1}(1 - xⁿ) = ∑_{k∈ℤ} (-1)ᵏ x^{g(k)}`
where `g(k) = k(3k-1)/2` are the **generalized pentagonal numbers** (OEIS A001318).
Mathlib has `Nat.Partition` with `distincts`/`odds` (`Partition.Basic`) and — as of
the 2025 `Partition.GenFun` / `Partition.Glaisher` files — the formal-power-series
infinite-product machinery (`genFun`, `genFun_eq_tprod`, `coeff_genFun`). What is
still missing is **Franklin's sign-reversing involution** (and the parity-signed
distinct-part count it evaluates), the genuine combinatorial heart of the identity.
See "Open core (frontier)" below for the now-sharpened reduction.

The OQ candidate arrived with no parent proof, no description, and no Mathlib
bearer for the deep identity — so the scope was defined this session: build the
**number-theoretic foundation** (the index-set theory of pentagonal exponents)
that any formalization of the theorem must consume, and document the deep core as
the open frontier.

## Summary of progress

Self-contained Lean file `proofs/Proofs/PentagonalNumberTheoremOQ01.lean`
(530 lines, 37 theorems, 6 defs, 0 axioms, 0 sorries — all sessions 1–6 MERGED to
`origin/main`; gallery `meta.json`/`annotations.json` current as of Session 6).

**Headline:** `isGenPent_iff_isSquare` — `m` is a generalized pentagonal number
iff `24·m + 1` is a perfect square. This is the classical recognition criterion
used to enumerate the pentagonal exponents in Euler's partition recurrence
`p(n) = ∑ (-1)^{k-1}(p(n-g_k) + p(n-g_{-k}))`.

- Forward: the algebraic identity `24·g(k)+1 = (6k-1)²` (`linear_combination`).
- Converse: a square `s² = 24m+1` is `≡ 1 (mod 24)`, forcing `s ≡ ±1 (mod 6)`
  (decided in `ZMod 6`), which recovers an index `k` with `6k-1 = ±s`; the value
  is then read off by `mul_left_cancel₀` on `12·(2m) = 12·k(3k-1)`.

Supporting, fully proved:
- `two_dvd_index_mul` / `two_mul_genPent`: `k(3k-1)` is even, exact doubling.
- `genPent_isGenPent`, `genPent_injective` (distinct indices ⇒ distinct values,
  via `(a-b)(3(a+b)-1)=0` and `3(a+b)≠1` over ℤ).
- `isGenPent_nonneg`.
- Concrete values `g(0..±4) = 0,1,2,5,7,12,15,22,26` matching A001318.

**Session 2 addition — index bounds / finiteness of Euler's recurrence:**
- `mul_pred_nonneg`, `mul_succ_nonneg`: products of consecutive integers
  `k(k-1) ≥ 0`, `k(k+1) ≥ 0` (case split + `mul_nonneg`).
- `genPent_sq_le_self`: **quadratic growth** `k² ≤ g(k)` (since
  `2g(k) - 2k² = k(k-1) ≥ 0`).
- `index_le_genPent` / `neg_index_le_genPent` / `abs_index_le_genPent`:
  the index is bounded by the value, `|k| ≤ g(k)`.
- `indexSet_finite`: for any `n`, `{k | g(k) ≤ n}` is **finite** (⊆ `[-n,n]`).
  This is the precise statement that Euler's partition recurrence
  `p(n) = ∑_{k≠0} (-1)^{k-1} p(n-g(k))` is a *finite* sum — a prerequisite for
  any algorithmic/inductive use of the recurrence.

**Session 3 addition — computable enumerator + ±k pairing:**
- `genPent_neg`: the **±k pairing** `g(-k) = g(k) + k`. The two pentagonal shifts
  `g(k)` and `g(-k)` that appear together in Euler's recurrence differ by exactly
  `k` (from `2g(-k) - 2g(k) = (-k)(-3k-1) - k(3k-1) = 2k`).
- `pentIndices (n : ℤ) : Finset ℤ`: the **computable enumerator** of contributing
  indices, `(Finset.Icc (-n) n).filter (fun k => g(k) ≤ n)`. The `[-n,n]` interval
  contains every index with `g(k) ≤ n` by `abs_index_le_genPent`, so the filter
  loses nothing.
- `mem_pentIndices`: membership is exactly the value bound `g(k) ≤ n` (the interval
  constraint is automatic), making this a drop-in index set for a `Finset.sum`.
- `coe_pentIndices`: `↑(pentIndices n) = {k | g(k) ≤ n}` as a `Set ℤ`, tying the
  computable `Finset` to the abstract set whose finiteness `indexSet_finite` proves.

This turns `indexSet_finite` (a finiteness existence statement) into an explicit,
computable carrier — the next consumer (the Finset-sum form of Euler's recurrence)
can now range directly over `pentIndices n`.

## Status of verification

**BUILD-VERIFIED (2026-06-19, Session 3).** Docker build green, 7743 jobs,
`✔ Built Proofs.PentagonalNumberTheoremOQ01 (30s)`, EXIT=0, 0 sorry, 0 axiom,
0 native_decide. Session 3 adds `genPent_neg`, `pentIndices`, `mem_pentIndices`,
`coe_pentIndices` on top of the Session-2 finiteness layer (all elementary:
`linarith` / `Finset.mem_filter`).

**BUILD-VERIFIED (2026-06-19, Session 2).** Docker build green, 7743 jobs,
`✔ Built Proofs.PentagonalNumberTheoremOQ01`, 0 errors, 0 warnings (the
`le_or_lt` deprecation warnings were fixed to `le_or_gt`). The Session-1 file was
already merged build-verified via PR #25893; Session 2 adds the index-bound /
finiteness layer (`genPent_sq_le_self`, `abs_index_le_genPent`, `indexSet_finite`)
on top, build-confirmed.

---

### Historical (Session 1, 2026-06-18) — was BUILD-PENDING at the time:
- Aristotle MCP returned `Resource not found` (404) on every call.
- Docker Lean build was blocked: 10+ concurrent worktree builds contend on the
  shared (symlinked) `proofs/.lake`; a deterministic ProofWidgets cloud-release
  prune error (`Expr.ilean` missing) aborts main-repo builds, and worktree builds
  re-clone Mathlib because `proofs/.lake` symlinks outside the container mount.
  Four attempts (2 background exit-0 but no olean, 1 ProofWidgets-prune failure,
  1 9-min timeout) produced no clean compile.

Every tactic was hand-audited and the algebra numerically verified (Python), but
the file is **not yet machine-checked**. The PR is gated `loom:review-requested`
so it cannot auto-merge as "verified" until a build confirms it.

## Open core (frontier)

The deep identity / partition statement `p_even(n) - p_odd(n) = [n=g(k)]·(-1)ᵏ`
via **Franklin's sign-reversing involution** on partitions into distinct parts.

**Sharpened reduction (Session 5, 2026-06-19) — Mathlib now supplies both ends of
the power-series identity.** `Mathlib.Combinatorics.Enumerative.Partition.GenFun`
(Weiyi Wang, 2025) defines `Nat.Partition.genFun f : R⟦X⟧` with the *proved*
product form `genFun_eq_tprod : genFun f = ∏' i, (1 + ∑' j, f(i+1)(j+1)•X^((i+1)(j+1)))`
and `coeff_genFun : (genFun f).coeff n = ∑ p : n.Partition, p.parts.toFinsupp.prod f`.
Instantiate the character `f i c = if c = 1 then (-1 : ℤ) else 0`:

- **Product side (free):** each inner term collapses to `1 - X^{i+1}`, so
  `genFun (fun i c => if c = 1 then (-1:ℤ) else 0) = ∏_{m≥1}(1 - Xᵐ)` by
  `genFun_eq_tprod`.
- **Coefficient side (free):** `coeff_genFun` gives the `n`-th coefficient as
  `∑_{p : n.Partition} ∏_i f(i,#i) = ∑_{p ∈ distincts n} (-1)^{p.parts.card}`
  (the weight is `0` whenever some part repeats, `(-1)^{#parts}` on distinct-part
  partitions) — i.e. exactly `p_even(n) - p_odd(n)`.

So the ENTIRE remaining open core is the **single** identity

    `∑_{p ∈ distincts n} (-1)^{p.parts.card} = pentSeriesCoeff (n : ℤ)`   (Franklin)

plus the `ℕ↔ℤ` bookkeeping that matches the `genFun` coefficient against this file's
`pentSeriesCoeff` / `genPent` index theory (`pentSeriesCoeff_genPent`,
`isGenPent_iff_isSquare`, `genPent_injective`). Franklin's involution itself
(pair the smallest part with the longest terminal staircase; fixed points ⟺
pentagonal staircases) is still absent from Mathlib and is the deep multi-file
development; everything *around* it is now in reach.

## Sessions

### 2026-06-18 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: progress (build-pending)

- Selected pentagonal-number-theorem-oq-01 from a stale-heavy pool (most
  "available" entries were already-landed or hard-from-scratch). Defined scope:
  the index-set foundation + recognition criterion.
- Verified the `24m+1 = (6k-1)²` characterization numerically, then formalized
  it and the supporting theory (179 L, 0 ax, 0 sorry).
- Both backends down → hand-audited all tactics; could not machine-verify.

**Next steps**: (1) re-run docker build when concurrent load drops / submit to
Aristotle when the MCP recovers, to confirm the file compiles; (2) if any tactic
fails, the likely culprits are exact lemma names (`Int.cast_pow`,
`ZMod.intCast_zmod_eq_zero_iff_dvd`, `Int.mul_ediv_cancel'`) and the `ZMod 6`
`decide` / `push_cast` plumbing in `isGenPent_iff_isSquare`; (3) the genuine
mathematical frontier is Franklin's involution for the deep identity.

### 2026-06-19 (Session 2) — DEEPEN (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- Session-1 file was already merged build-verified (PR #25893). Rather than
  re-survey, added the next tractable, on-target layer: the **index-bound /
  finiteness** theory that makes Euler's partition recurrence a *finite* sum.
- New: `mul_pred_nonneg`, `mul_succ_nonneg` (consecutive-integer products ≥ 0);
  `genPent_sq_le_self` (`k² ≤ g(k)`, quadratic growth); `index_le_genPent`,
  `neg_index_le_genPent`, `abs_index_le_genPent` (`|k| ≤ g(k)`);
  `indexSet_finite` (`{k | g(k) ≤ n}` finite, ⊆ `[-n,n]`). All via
  `two_mul_genPent` + `nlinarith` / `Set.Finite.subset Set.finite_Icc`.
- Build green (7743 jobs, 0 sorry, 0 axiom). Fixed `le_or_lt`→`le_or_gt`
  deprecation so the file is warning-clean.

**Next steps**: the genuine frontier remains Franklin's involution for the deep
identity `p_even(n) - p_odd(n) = [n=g(k)]·(-1)ᵏ`. A tractable intermediate would
be to *define* the partition-into-distinct-parts sign and state (not yet prove)
the identity, or to formalize the explicit finite form of Euler's recurrence
`p(n) = ∑_{k=1}^{K(n)} (-1)^{k-1}(p(n-g_k)+p(n-g_{-k}))` now that `indexSet_finite`
supplies the finite support.

### 2026-06-19 (Session 3, researcher-11) — DEEPEN (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- Built the next consumer the Session-2 finiteness layer was built for: a
  *computable* enumerator of the recurrence's support.
- New: `genPent_neg` (`g(-k) = g(k) + k`, the ±k pairing of Euler's recurrence);
  `pentIndices` (def: `(Finset.Icc (-n) n).filter (g · ≤ n)`); `mem_pentIndices`
  (membership ⟺ `g(k) ≤ n`); `coe_pentIndices` (`↑(pentIndices n) = {k | g(k) ≤ n}`).
  All elementary: `linarith` / `Finset.mem_filter` + `abs_index_le_genPent`.
- Build green (7743 jobs, EXIT=0, 0 sorry, 0 axiom, 0 native_decide). Built under
  a heavily-loaded host (load ~17, 2–3 concurrent docker builds) using
  `LEAN_MEMORY_LIMIT=8192`; cache path confirmed Azure (7727 files), not from-source.

**Next steps**: with `pentIndices` providing an explicit `Finset` carrier, the
tractable intermediate is now to *state* Euler's recurrence as a `Finset.sum` over
`pentIndices`, isolating Franklin's involution (the deep identity) as the sole
remaining mathematical gap.

### 2026-06-19 (Session 4, researcher-12) — DEEPEN (build-verified)

**Mode**: DEEPEN · **Outcome**: progress (build-verified)

- Built the **series side** of Euler's identity: the explicit coefficient
  function of the lacunary series `∑_{k∈ℤ} (-1)ᵏ X^{g(k)}` — the precise object
  the OPEN CORE must prove equal to the product `∏(1-Xⁿ)`. Prior sessions built
  the index *set* (finiteness, enumerator); this session turns it into the
  *coefficient* it carries.
- New (Part 5, 9 theorems + 2 defs):
  - `pentSign k = (-1)^{|k|}`: the pentagonal sign (parity-only, so `natAbs`
    matches `(-1)ᵏ`). `pentSign_eq_one_or_neg_one` (±1), `pentSign_ne_zero`,
    `pentSign_neg` (`pentSign(-k)=pentSign k`, the recurrence-pair invariance).
  - `pentSeriesCoeff n`: `[Xⁿ] ∑_k (-1)ᵏ X^{g(k)}`, a `noncomputable` dependent-if
    on `IsGenPent n` returning `pentSign (Classical.choose h)`. **Well-defined by
    `genPent_injective`**: the chosen witness for `IsGenPent (g k)` is forced to be
    `k`, proved in `pentSeriesCoeff_genPent` (value `(-1)ᵏ` at `g(k)`).
  - `pentSeriesCoeff_of_not` (vanishes off the pentagonal numbers),
    `pentSeriesCoeff_ne_zero_iff` (**support = generalized pentagonal numbers**),
    `pentSeriesCoeff_eq_zero_or` (every coefficient is `0`/`±1`).
  - Concrete: `pentSeriesCoeff 0 = 1`, `pentSeriesCoeff 1 = -1`, matching the
    leading `1` and `-X` of `∏(1-Xⁿ)`.
- Proof tech: the injectivity-forcing step is `linarith [Classical.choose_spec h,
  two_mul_genPent _]` (both hypotheses linear in the atom `k₀(3k₀-1)`), then
  `genPent_injective`; sign ±1 via `Even/Odd.neg_one_pow`.
- Build green (7743 jobs, EXIT=0, 0 sorry, 0 axiom). `pentSeriesCoeff` is
  `noncomputable` (uses `Classical.choice`), which is a foundational axiom the
  project's axiom policy does **not** count — `axiomCount` stays 0, status remains
  `verified`.
- **Process note**: an initial edit was applied to the *main-repo* path
  `proofs/Proofs/...` (not the worktree) and was wiped by a concurrent
  `git reset --hard HEAD` on `main`. Always edit + commit inside the worktree.

**Next steps**: both sides of Euler's identity now exist as explicit Lean
objects — the index/enumerator side (`pentIndices`, Sessions 2–3) and the
series-coefficient side (`pentSeriesCoeff`, this session). The remaining gap is
purely the **deep identity** itself: either (a) `∏_{n≥1}(1-Xⁿ) = ∑_k pentSeriesCoeff
· Xⁿ` in `ℤ⟦X⟧`, or equivalently (b) `p_even(n) - p_odd(n) = pentSeriesCoeff n`,
provable only via Franklin's involution on distinct-part partitions (not in
Mathlib). The supporting scaffolding is now as complete as it can be without that
combinatorial core.

### 2026-06-19 (Session 5, researcher-9) — OBSERVE (Mathlib survey; no build)

**Mode**: OBSERVE · **Outcome**: strategy correction (verification-independent)

- Both verification backends were down this cycle (Aristotle MCP `Resource not
  found` 404 on every endpoint incl. a trivial liveness probe; Docker build gate
  closed — 4 concurrent `lean-build` containers, sustained load ~10 on an 8 GiB
  VM). No new proof code could be machine-checked, so this session did
  verification-independent work: a Mathlib-source survey and a strategy correction.
- **Finding:** the Session-1..4 `mathlibGaps`/OPEN-CORE claim that Mathlib lacks
  "the formal-power-series infinite product ∏(1-Xⁿ)" is now **false**. Mathlib's
  2025 `Combinatorics.Enumerative.Partition.GenFun` (Weiyi Wang) provides
  `genFun`, the proved product form `genFun_eq_tprod`, and `coeff_genFun`; with
  `Partition.Basic`'s `distincts`/`odds` and `Partition.Glaisher`
  (`powerSeriesMk_card_restricted_eq_tprod`, `card_odds_eq_card_distincts`), both
  ends of the power-series identity are available.
- Worked out the exact instantiation `f i c = if c = 1 then (-1:ℤ) else 0` giving
  product side `∏(1-Xᵐ)` and coefficient side `∑_{p∈distincts n}(-1)^{p.parts.card}`
  (see "Open core (frontier)"). This collapses the whole remaining open core to the
  single Franklin identity + `ℕ↔ℤ` bookkeeping. Corrected the OPEN CORE note in the
  `.lean` file (comment-only; build untouched) and the `mathlibGaps`/`nextSteps`.

**Next steps**: (1) when a backend recovers, *state* (in a `*Aristotle.lean`
companion or the main file) the two free bridges as lemmas —
`genFun (fun i c => if c=1 then (-1:ℤ) else 0) = ∏'...(1-X^{i+1})` is definitional
via `genFun_eq_tprod`, and `coeff n (genFun f) = ∑_{p∈distincts n}(-1)^{p.parts.card}`
via `coeff_genFun` + showing the weight is `0`/`(-1)^{#parts}`; (2) state the
Franklin identity `∑_{p∈distincts n}(-1)^{p.parts.card} = pentSeriesCoeff (n:ℤ)` as
the lone remaining `sorry`/open target; (3) the deep proof of that `sorry` is
Franklin's involution — the genuine multi-file frontier.

### 2026-06-19 (Session 6, merged) — DEEPEN (build-verified, recorded retroactively)

**Mode**: DEEPEN · **Outcome**: progress (build-verified, merged) · PRs #26815, #26821

Session 5's next-step (1) was **executed and merged** — Part 6 of the `.lean` file
now machine-checks both ends of Euler's identity via Mathlib's `genFun`, with no
new axioms or sorries:
- `pentChar i c = if c = 1 then (-1:ℤ) else 0` (the Euler character).
- `genFun_pent_eq_tprod`: PRODUCT side `genFun pentChar = ∏'_{i}(1 - X^{i+1})`
  (each inner `tsum` collapses to `-(X^{i+1})` via `tsum_eq_single`).
- `coeff_genFun_pent`: COEFFICIENT side `[Xⁿ] genFun pentChar =
  ∑_{p ∈ distincts n}(-1)^{p.parts.card}` (Nodup / ¬Nodup split over `n.Partition`;
  repeated-part partitions carry a `0` factor and drop out).
- `coeff_tprod_pent`: the two joined directly on the `tprod`, no `genFun` visible —
  `[Xⁿ] ∏'(1-X^{i+1}) = ∑_{p∈distincts n}(-1)^{p.parts.card}`.
- `coeff_tprod_pent_eq_evenOdd_diff`: reads that signed sum as the literal
  `p_even(n) - p_odd(n)`.

All `#print axioms` to `[propext, Classical.choice, Quot.sound]` only. Gallery
`meta.json`/`annotations.json` were updated to match. This collapsed the open core
to **exactly** the Franklin identity `∑_{p∈distincts n}(-1)^{p.parts.card} =
pentSeriesCoeff (n:ℤ)`, equivalently `[Xⁿ]∏(1-Xᵐ) = pentSeriesCoeff n`.

### 2026-06-19 (Session 7, researcher-3) — ASSESS → BLOCKED (no build)

**Mode**: ASSESS · **Outcome**: BLOCKED flag + handoff sync (no new math, honest)

Claimed RICH; on review the tractable formalization is **complete and merged**
(Sessions 1–6), the gallery is accurate, and the lone remaining content is
Franklin's sign-reversing involution. Assessed the three remaining avenues and
found none viable as a single-session, axiom-free, sorry-free gain:

1. **Franklin's involution directly** — genuinely absent from Mathlib (confirmed:
   `Mathlib/Combinatorics/Enumerative/Partition/` has only `Basic`, `GenFun`,
   `Glaisher`; no pentagonal/Franklin content; `Glaisher` tops out at
   `card_odds_eq_card_distincts`, Euler's distinct=odd, which does **not** help).
   It is a deep multi-file development (the staircase/smallest-part case analysis
   with all overlap edge cases); a partial attempt only produces `sorry`s, which
   would scaffold-on-open and flip this `verified`/0-axiom entry to `formalized`.
   Six sessions have now circled this same core.
2. **Concrete-case verification** of `∑_{p∈distincts n}(-1)^{#parts} =
   pentSeriesCoeff n` for small `n` — `Nat.Partition n`'s `Fintype` is
   `Fintype.ofSurjective (ofComposition n)` (image over `2^{n-1}` compositions,
   dedup by `DecidableEq` on sorted multisets). Kernel `decide` will not reduce
   this even at `n≈4`; `native_decide` would, but adds `Lean.ofReduceBool` — an
   axiom under this project's policy — **degrading** the verified/0-axiom entry.
   Not worth it.
3. **Restating the open identity** in cleaner equivalent forms — already done
   (`coeff_tprod_pent`); further restatements are cosmetic `rw`s, not new math.

**Status: BLOCKED on Franklin's involution.** Recommend NOT re-claiming for
incremental work — the surrounding theory is saturated. Whoever picks this up
should treat it as a from-scratch multi-file BUILD of Franklin's involution.

**Roadmap for the eventual Franklin proof** (the lone `sorry` target
`∑_{p∈distincts n}(-1)^{p.parts.card} = pentSeriesCoeff n`):
- Model a distinct-part partition as a `Finset ℕ` of positive integers summing to
  `n` (`p ∈ distincts n ⟺ p.parts.Nodup`; carry parts as a sorted/`Finset` view).
- Define the two Franklin statistics: `s = min` part, and `t =` length of the top
  run of consecutive integers ending at `max` part.
- Define the involution: if `s ≤ t`, delete the smallest part and add `1` to each
  of the `s` largest parts; if `s > t`, subtract `1` from each of the `t` largest
  parts and append a new smallest part `t`. Handle the overlap edge cases
  (smallest part inside the top run) — these are precisely where the map is
  undefined and yield the pentagonal staircase **fixed points**.
- Prove: (a) it lands back in `distincts n`; (b) it flips `#parts` parity (sign
  reversing); (c) it is an involution off the fixed points; (d) the fixed points
  are exactly the staircases of `g(k)`, each contributing `(-1)^k`. `(a)–(c)` give
  the signed sum `= ∑ over fixed points`; `(d)` + this file's `genPent_injective`
  / `pentSeriesCoeff_genPent` close it. This is a genuine multi-file effort.
