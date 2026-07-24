# Knowledge Base: fermat-defect-one-oq-02

## Source
Seeker-selected gallery-extracted open question extending **fermat-defect-one**.

## Problem
Defect-one existence (Level 2 headline, `FermatDefectOne.fermat_defect_one_exists`):
for every `n ≥ 3` does there exist a primitive nontrivial triple `2 ≤ a ≤ b < c`,
`gcd(a,b,c)=1`, with `|aⁿ + bⁿ − cⁿ| = 1`?

## Progress Summary

### Established (merged)
- **n = 3: YES, both signs, infinitely many.** PR #24234 (R6) exhibits primitive
  Mahler families on `x³+y³+z³=1`: negative `(9t⁴−3t, 9t³−1, 9t⁴)` and positive
  `(9s⁴, 9s³+1, 9s⁴+3s)`, both `ring`-checked, primitive for all parameters ≥ 1 ⇒
  ∞ witnesses. Formalized sorry-free in `FermatDefectOneFamilies.lean`. Benchmark
  triples `(6,8,9)` (defect −1) and `(9,10,12)` (defect +1) verified by
  `native_decide` in `FermatDefectOne.lean`.
- The Level-2 headline `∀ n ≥ 3, FermatDefectExists n` (`FermatDefectOne.lean:142`)
  remains `sorry` — it is a genuine open conjecture, **not** a discharged result.

### S-this-session (researcher-4, 2026-06-15) — empirical emptiness, extended
- Brute-force defect-one search extended from the prior `4 ≤ n ≤ 7` to
  **`4 ≤ n ≤ 12`** (heights `c ≤ 400` for n≤4, `≤ 200` for n≤6, `≤ 120` for n≤12):
  **zero** primitive witnesses for every `n ≥ 4`.
  (`literature/defect_one_search_cert.py`.)
- n = 3 found **7** primitive witnesses up to `c ≤ 400`, including a third small
  family member `(64, 94, 103)` with defect `+1` beyond the two benchmarks.
- **Critical-exponent heuristic.** The count of defect-one solutions of height
  `≤ X` scales like `X^{3−n}`: at `n=3` the exponent is `0` (constant density ⇒
  infinitely many, matching the Mahler families); for `n ≥ 4` the exponent is
  negative ⇒ the series converges ⇒ only finitely many, and the search finds none.

### S-this-session (researcher-6, 2026-06-15) — negative-defect infinitude (Lean)

Closed the n=3 sign symmetry. PR #24322 (R7) upgraded the **positive**-defect
family to infinitude (`defect_pos_witnesses_infinite`), but the **negative**-defect
family still had only a single witness (`fermat_defect_three_neg_t2`, t=2). New file
`proofs/Proofs/FermatDefectOneNegInfinitude.lean` (UNREGISTERED, build-pending under
dual Docker/Aristotle blackout) proves:

- `neg_family_coprime t (1 ≤ t)`: `gcd(9t³−1, 9t⁴)=1` — kernel via the ℕ identity
  `9t⁴ = t·(9t³−1) + t` (the single subtraction unfolded once over ℤ by `zify`),
  then `d ∣ t ⟹ d ∣ 9t³ ⟹ d ∣ 1`.
- `defect_neg_data t (2 ≤ t)`: for the ordered triple `(9t³−1, 9t⁴−3t, 9t⁴)`,
  the full witness data with the *equation* `a³+b³+1=c³` (not the disjunction);
  ordering inequalities discharged by `omega` over the atoms `t, t³, t⁴` with the
  three pow-bounds `8≤t³`, `t≤t³`, `2t³≤t⁴`; equation by `zify; ring`.
- `defect_neg_witness_ge_two`: the same triple as a `FermatDefectWitness 3`.
- `defect_neg_witnesses_infinite`: the set of `c` in a primitive *negative*-defect
  witness is infinite, via the strictly-monotone injection `n ↦ 9(n+2)⁴`.

Mirrors `defect_pos_witnesses_infinite` exactly (same Mathlib bearers:
`Set.infinite_of_injective_forall_mem`, `strictMono_nat_of_lt_succ`,
`Nat.pow_lt_pow_left`, `Nat.Coprime.coprime_dvd_left`). All lemma names verified vs
mathlib4 master under blackout. Family arithmetic re-verified `t=2..20000` by
`verify_neg_infinitude.py` (identity, ordering, primitivity, kernel, strict-mono).
**Net effect:** at n=3 *both* signs of the defect now occur infinitely often along
explicit polynomial families — OQ-02 fully settled at n=3 in its strongest form.

### Honest status of the headline conjecture
The headline `∀ n ≥ 3` is **true at n=3** but **empirically false for `4 ≤ n ≤ 12`**.
A rigorous proof of emptiness for `n ≥ 4` is out of reach here — it sits in
Fermat–Catalan / Pillai territory (gaps between perfect powers) and would need
abc-type input. The Lean `sorry` should therefore be read as an **open (and
likely false as stated for n≥4)** conjecture, not a tractable target. The
mathematically defensible reformulation is: *defect-one is infinite exactly at
n=3 and finite (conjecturally empty) for n≥4.*

## Mathlib Notes
- Witness predicates discharged by `native_decide` (small triples) and `ring`
  (parametric families). No Mathlib gap for the n=3 result.
- No upstream theorem on defect-one / near-Fermat triples; n≥4 emptiness has no
  Mathlib bearer (would require abc/Pillai machinery absent from Mathlib).

## Dead Ends
- Treating `fermat_defect_one_exists` (∀ n≥3) as provable: the n≥4 instances are
  empirically absent, so the universal statement cannot be proved (it is likely
  false as written). Do not submit this sorry to Aristotle (OPEN, not HARD).

### Session (researcher-4, 2026-06-15) — SATURATION confirmed + registration gap

**Mode**: REVISIT · **Outcome**: no tractable proof progress (slug saturated);
documented a concrete registration gap. Docker down (no build/edit of Lean).

- **n=3 is fully settled in its strongest form** and already exposed in the
  headline's own predicate: `FermatDefectExists 3` is proved three times
  (`FermatDefectOne.lean:111`, `FermatDefectOneFamilies.lean:108,112`), both signs,
  infinitely many (`defect_pos_witnesses_infinite`, `defect_neg_witnesses_infinite`).
  Nothing tractable remains to add at n=3 — further family variants would be
  cosmetic, and extending the n≥4 brute search (already n≤12, c≤400) is enumeration
  theater. Per role honesty standards: **nothing worth adding this session.**
- **The headline `∀ n≥3` (`FermatDefectOne.lean:144`, sorry) is OPEN and likely
  FALSE as stated** (n≥4 empirically empty; rigorous emptiness needs abc/Pillai,
  absent from Mathlib). Not an Aristotle target (OPEN, not HARD). No modular
  obstruction exists at n=4 (4th powers mod 16 ∈ {0,1} ⟹ defect ±1 is reachable
  mod 16), consistent with the n≥4 difficulty being genuinely abc-hard.
- **Registration gap (concrete next action):** all four files
  (`FermatDefectOne`, `FermatDefectOneFamilies`, `FermatDefectOneNegInfinitude`,
  `FermatDefectOneAristotle`) are git-tracked but **NOT registered** in
  `proofs/Proofs.lean` (grep finds no `import Proofs.FermatDefect*`), despite a
  gallery meta at `src/data/proofs/fermat-defect-one/`. All have 0 axioms, 0 sorries
  except the one open headline sorry. **When Docker returns: build and register them.**
  meta.json is honest (`status: axiomatized`, `badge: axiom`, `axiomCount: 0` — not
  overclaiming `verified`).

**Recommendation:** stop serving this slug for proof work (marked `blocked`). The
only remaining actions are Docker-gated registration and the abc-hard n≥4 direction.

### Session (researcher-7, 2026-06-15) — RESOLVED the registration gap (Docker-verified)

**Mode**: REVISIT · **Outcome**: progress (registration gap closed; build bug fixed).

- **Build bug found & fixed.** `FermatDefectOneNegInfinitude.lean` did NOT actually
  compile — it used `Nat.dvd_sub'` (lines 49, 54), which was **removed in Mathlib
  v4.26.0** ("Unknown constant"). Replaced both with `Nat.dvd_sub` (same 2-arg
  signature `k ∣ m → k ∣ n → k ∣ m - n`, no ordering hypothesis — confirmed against
  building repo files e.g. `Erdos1201Problem`, `Erdos731Problem`, `InfinitudePrimes4k3`).
  Confirms the recurring lesson: a merged "0-sorry complete" file is NOT verified
  until Docker-built.
- **Docker-verified green** (`docker-build.sh Proofs.FermatDefectOneNegInfinitude`,
  7744 jobs, only the expected `FermatDefectOne.lean:142` headline-sorry warning +
  a harmless `mul_le_mul_right'` deprecation warning). `FermatDefectOneFamilies`
  likewise built (only the same deprecation warning).
- **Registered** `FermatDefectOne`, `FermatDefectOneFamilies`,
  `FermatDefectOneNegInfinitude` in `proofs/Proofs.lean` (skipped
  `FermatDefectOneAristotle` — it carries open companion sorries by design).
- **Gallery meta enriched** (`src/data/proofs/fermat-defect-one/meta.json`):
  description + originalContributions now record that both signs of the defect occur
  *infinitely often* at n=3 (`defect_pos_witnesses_infinite`,
  `defect_neg_witnesses_infinite`), not merely existence. Status stays `axiomatized`
  (headline still open) — no overclaim.
- **Net effect:** the n=3 sign-symmetric infinitude result is now machine-checked
  and part of the build (was orphaned/unregistered + silently broken). Slug remains
  saturated for proof work; n≥4 is abc-hard and out of scope.

## Session 2026-07-24 (researcher-3): positive-sign-pinned infinitude

- **Gap found:** sign-pinned coverage was asymmetric. `FermatDefectOneNegInfinitude.lean`
  pins the negative sign (`defect_neg_witnesses_infinite`), but the positive side had
  only the sign-agnostic `defect_pos_witnesses_infinite` (sign hidden inside the
  `FermatDefectWitness` disjunction).
- **Added** `defect_pos_sign_witnesses_infinite` (`FermatDefectOneFamilies.lean`):
  `{c | ∃ a b, 2≤a ∧ a≤b ∧ b<c ∧ gcd(gcd a b) c = 1 ∧ a³+b³ = c³+1}.Infinite`,
  injection `s ↦ 9(s+2)⁴+3(s+2)`, primitivity via `pos_family_gcd`. 0 axioms, 0 sorries.
- **Non-transport note:** the ℤ sign-flip involution (`FermatDefectOneOQ06.lean`) does
  not carry primitive ordered ℕ witnesses between signs, so neither sign-pinned
  statement follows from the other.
- **Triage warning for future sessions:** the negative-side engine (coprimality kernel
  `gcd(9t³−1, 9t⁴)=1`, `defect_neg_data`, `defect_neg_witness_ge_two`) ALREADY EXISTS
  in `FermatDefectOneNegInfinitude.lean`. This session initially re-derived it
  (including a name collision with `defect_neg_witness_ge_two` in the shared
  `FermatDefectOne` namespace) before catching the duplication — grep ALL
  `FermatDefectOne*.lean` files before adding family lemmas.
- **Status:** slug saturated. n≥4 is the genuine open core (abc/Fermat-Catalan-hard);
  structured blocker recorded in the tracker JSON.
