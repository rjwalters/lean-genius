# Knowledge Base: e-transcendental-oq-02-oq-06

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-08 (Researcher-8) — Frequency-mismatch criterion

**Mode**: FRESH | **Outcome**: progress (VERIFIED, 0 sorry, 0 new axiom)

### What I did
Generalized the existing *absence* obstruction (`not_normal_of_eventually_missing_ktuple/_digit`,
which handles matching-frequency `0`) to arbitrary frequency anomalies. Added to
`proofs/Proofs/ETranscendentalOQ02.lean` (PART IV.7):

- `not_normal_of_match_freq_tendsto_ne` — if a k-tuple's matching frequency
  converges to `L ≠ b^(-k)`, then not normal. One line via `tendsto_nhds_unique`
  against the definitional limit `hn k s`.
- `not_normal_of_match_freq_eventually_le` / `_eventually_ge` — if the matching
  frequency is *eventually* `≤ c < b^(-k)` (resp. `≥ c > b^(-k)`), then not
  normal. Uses `le_of_tendsto` / `ge_of_tendsto`; **no convergence of the
  frequency is assumed** — strictly stronger than the tendsto form. Captures
  under- and over-representation.
- `not_normal_of_digit_freq_tendsto_ne` — single digit with density `≠ 1/b`
  forbids normality (k=1). Bridged `b^(-(1:ℤ)) = b⁻¹` via `Nat.cast_one` +
  `zpow_neg_one`; collapsed the `∀ i : Fin 1` predicate with `Fin.forall_fin_one`.

### Key findings
- The absence case was the extreme (`L = 0`) instance; the general anomaly needs
  nothing beyond uniqueness of limits (`tendsto_nhds_unique`) or one-sided limit
  comparison (`le_of_tendsto` / `ge_of_tendsto`). The eventual-bound forms are the
  real content: they conclude non-normality from a *single* frequency inequality
  holding eventually, without the frequency converging.
- The necessary-condition theory for normality is now complete: irrational ⇐
  normal, disjunctive ⇐ normal, and full frequency-mismatch ⇐ ¬normal.

### Status
Core axiom `e_absolutely_normal` remains **genuinely open** (no base is proved
normal for e as of 2026) — not eliminable. This session strengthens the sharp
boundary, not the open core.

### Files modified
- `proofs/Proofs/ETranscendentalOQ02.lean` (+4 theorems, PART IV.7)
- `src/data/proofs/e-transcendental-oq-02/meta.json` (lineCount 1021→1114, theoremCount 61→65)
- `src/data/research/problems/e-transcendental-oq-02-oq-06.json` (knowledge)

## Session 2026-07-09 (Researcher-4) — All-zeros k-block has density 1 (base 2)

**Mode**: FRESH | **Outcome**: progress (VERIFIED, 0 sorry, 0 new axiom)

### What I did
Added PART IX to `proofs/Proofs/ETranscendentalOQ02.lean`: the **first k-block
(k ≥ 2) frequency computation** in the development. Prior base-2 work computed a
single digit density (`1` at density `0`, PART VIII). Here the entire all-zeros
length-`k` block of the Liouville constant `liouvilleNumber 2` is shown to occur
with asymptotic density `1`, for every `k`.

- `nthDigit_two_eq_zero_or_one` — every base-2 digit is 0 or 1 (residue mod 2,
  via `Int.emod_two_eq_zero_or_one`).
- `liouvilleNumber_two_zeros_bad_count_le` — windows `[n,n+k) ⊆ [0,N)` that
  contain a `1` number `≤ k·(log₂(N+k)+4)`. Covering argument: each bad window is
  hit by the `1`-position inside it (`< N+k`), and each `1`-position lies in `≤ k`
  windows. Formalized via `Finset.card_biUnion_le` over
  `ones(N+k) = filter (digit = 1)`, each fiber `⊆ (univ : Fin k).image (j - ·)`
  so `card ≤ k`; reuses `liouvilleNumber_two_one_count_le`.
- `liouvilleNumber_two_all_zeros_density_one` — all-zeros k-window density → 1.
  Bad density → 0 by `squeeze_zero` against `k·(log₂(N+k)+4)/N`; the all-zeros
  windows are the complement in `range N`
  (`Finset.filter_card_add_filter_neg_card_eq_card`), so density = `1 - bad → 1`.
- `liouvilleNumber_all_zeros_not_normal_base_two` (k ≥ 1) — non-normality via
  **over-representation**: the general k-tuple criterion
  `not_normal_of_match_freq_tendsto_ne` with `L = 1 ≠ 2^{-k}`. First application
  of the k-tuple (not just single-digit / absence) criterion, and a structurally
  different proof from PART VIII's single under-represented digit.

### Key findings
- `k·(log₂(N+k)+4)/N → 0`: bound `log₂(N+k) ≤ log₂ N + 1` for `N ≥ k` via
  `Nat.log_mono_right` + `Nat.log_mul_base` (`N+k ≤ N·2`), then squeeze against
  `k·(log₂ N + 5)/N = k·((log₂ N + 5)/N) → 0` (reusing the file's
  `tendsto_natLog_two_div_atTop_zero`).
- The covering/biUnion count is the reusable core: a sparse "special" set (here
  the 1-positions) forces a *complementary block* to be over-represented at
  density 1; the same recipe applies to any base-2 real whose 1-digits have
  density 0.
- Gotcha: `gcongr` on `↑A/N ≤ ↑B/N` closes the numerator goal via its assumption
  discharger when the ℕ inequality is in scope — provide the ℝ-cast hypothesis
  explicitly (`have hbR : (↑A:ℝ) ≤ ↑B := by exact_mod_cast …; gcongr`) to keep the
  step deterministic and avoid a stray "No goals to be solved".

### Status
Core axiom `e_absolutely_normal` remains **genuinely open** (no base proved normal
for e as of 2026) — not eliminable. The oq-06 goal (`normal_imp_irrational`) was
discharged long ago (now a theorem, not an axiom). This session extends the
base-2 non-normality theory from single-digit to full k-block distribution.

### Files modified
- `proofs/Proofs/ETranscendentalOQ02.lean` (+4 decls, PART IX; 1608→1809 lines)
- `src/data/proofs/e-transcendental-oq-02/meta.json` (lineCount 1608→1809,
  theoremCount 80→84)

## Session 2026-07-09 (researcher-3) — `e_disjunctive` (VERIFIED, depends on open e_absolutely_normal)

The oq-06 goal (`normal_imp_irrational`) is long-discharged; the sole axiom `e_absolutely_normal`
is genuinely open (no base proved normal for e). Added one recognisable named e-consequence that
the file's `absolutely_normal_imp_disjunctive` corollary made one line away but was missing:

**`e_disjunctive`** (ETranscendentalOQ02.lean, end): for every base b ≥ 2 and every finite digit
string `s : Fin k → Fin b`, e's base-b expansion contains s as a contiguous block
(`∃ n, ∀ i, nthDigit b (n+i) e = s i`). The "every finite pattern occurs in e" richness property,
the disjunctive companion of `e_normal_base_10` / `e_irrational_necessary_for_normality`. Proof =
`absolutely_normal_imp_disjunctive (Real.exp 1) e_absolutely_normal b k hb s`.

No new axiom: depends on exactly the SAME set as e_normal_base_10 —
`[propext, Classical.choice, Quot.sound, ETranscendentalOQ02.e_absolutely_normal]`. File axiomCount
stays 1, entry stays axiomatized (the open e-normality axiom).

VERIFIED green via direct lean-elab vs pinned Mathlib v4.26.0 (docker containerd blob I/O down):
built the dep chain deepest-first into /tmp — `Proofs.HermiteLindemann` (Mathlib-only, ~20s) then
`Proofs.eTranscendental` (imports HermiteLindemann) — then elaborated target, exit 0. Gallery meta
e-transcendental-oq-02: lineCount 2016→2029, theoremCount 89→90.

## Session 2026-07-11 (Researcher-2) — Effective recurrence (bounded-gap occurrences)

**Mode**: REVISIT (RICH) | **Outcome**: progress (VERIFIED, 0 sorry, 0 new axiom)

### What I did
Extended the effective-modulus layer (PART IV.9) of `ETranscendentalOQ02.lean`.
The prior layer bounded only the *first* occurrence (`first_occurrence_lt_of_modulus`)
and the density (`match_count_ge_linear_of_modulus`); nothing bounded the *next*
occurrence after an arbitrary point. Added:

- `exists_match_ge_of_count_gt` (pure `Finset`, no normality hypothesis) — if the
  tuple-`s` match count over `range N` *exceeds* a threshold `P` (with `P ≤ N`),
  then a match exists at a position `P ≤ n < N`. Proof: matches in `[0,P)` number
  `≤ P`, so `A \ B` (matches in `[0,N)` minus matches in `[0,P)`) is nonempty once
  the total exceeds `P`. Uses `Finset.sdiff_nonempty` + `Finset.card_le_card`.
- `next_occurrence_lt_of_modulus` — with a modulus `M`, every `k`-tuple recurs
  after any threshold `P` below the explicit bound
  `max (max (M k (b^{-k}/2)) 1) (2·bᵏ·P + 1)`. This is the effective (bounded-gap)
  form of infinitely-many-occurrences: it upgrades `first_occurrence_lt_of_modulus`
  (its `P = 0` content) to arbitrary `P`, and makes the qualitative
  `normal_ktuple_infinitely_often` quantitative with an explicit inter-occurrence
  gap. Proof: `match_count_ge_linear_of_modulus` gives `≥ (b^{-k}/2)·N₀` matches
  below `N₀`; picking `N₀ > 2·bᵏ·P` makes the count exceed `P`, then
  `exists_match_ge_of_count_gt` extracts the match at position `≥ P`.

### Key findings
- The gap constant is forced by the density rate: to guarantee more than `P`
  matches at density `b^{-k}/2` one needs a window `≳ 2·bᵏ·P`, hence the `2·bᵏ·P`
  term. The `b^{-k}·bᵏ = 1` identity (`zpow_natCast` + `zpow_add₀`) is the crux of
  the arithmetic `(b^{-k}/2)·(2·bᵏ·P + 1) = P + b^{-k}/2 > P`.
- Gotchas (Mathlib v4.26.0): `Finset.range_subset.mpr` did not accept `P ≤ N`
  directly (expects the unfolded `∀ x < P, x ∈ range N`) — build the subset by a
  membership lambda instead. `Finset.card_sdiff hBA` failed (the resolved lemma is
  the unconditional `(s\t).card = s.card - (s∩t).card`); route nonemptiness through
  `Finset.sdiff_nonempty : (s\t).Nonempty ↔ ¬ s ⊆ t` + `card_le_card` + `omega`.

### Status
Core axiom `e_absolutely_normal` remains **genuinely open** (no base proved normal
for `e` as of 2026) — not eliminable. The oq-06 goal (`normal_imp_irrational`) was
long discharged (a theorem, not an axiom). This session sharpens the effective
theory, not the open core.

### Files modified
- `proofs/Proofs/ETranscendentalOQ02.lean` (+2 theorems, PART IV.9; 2062→2160 lines)
- `src/data/proofs/e-transcendental-oq-02/meta.json` (lineCount 2062→2160,
  theoremCount 90→92, +2 originalContributions)
- `src/data/research/problems/e-transcendental-oq-02-oq-06.json` (knowledge)

### Next steps
- Iterate `next_occurrence_lt_of_modulus` (with `P := previous+1`) to build an
  explicit strictly-increasing enumeration of occurrence positions with
  modulus-controlled gaps.

## Session 2026-07-19 (Researcher-1) — Explicit monotone occurrence enumeration

**Mode**: REVISIT (RICH) | **Outcome**: progress (VERIFIED, 0 sorry, 0 new axiom)

### What I did
Executed the standing "Next steps" from the 2026-07-11 session: iterated
`next_occurrence_lt_of_modulus` (with `P := previous + 1`) into an **explicit
strictly-increasing enumeration** of tuple-occurrence positions. Added PART IV.9.a
to `ETranscendentalOQ02.lean`:

- `nextOcc` (noncomputable def) — the next occurrence position at/after threshold
  `P`, extracted from `next_occurrence_lt_of_modulus` via `Classical.choose`; with
  spec projections `nextOcc_ge` / `nextOcc_lt` / `nextOcc_isMatch`.
- `occSeq` (noncomputable def) — the enumeration: `occSeq 0 = nextOcc 0`,
  `occSeq (j+1) = nextOcc (occSeq j + 1)`.
- `occSeq_isMatch` — every term is a genuine occurrence of `s`.
- `occSeq_strictMono` — `StrictMono occSeq` (successor taken at threshold
  `occSeq n + 1 > occSeq n`, so `occSeq n < occSeq (n+1)`).
- `occSeq_succ_lt` — each successor obeys the effective gap bound
  `max (max (M k (b^{-k}/2)) 1) (2·bᵏ·(occSeq n + 1) + 1)`.
- `exists_strictMono_occurrence_enumeration` — headline packaging: a `StrictMono`
  `f : ℕ → ℕ` all of whose terms are occurrences with modulus-controlled gaps.

### Key findings
- Upgrades the qualitative `normal_ktuple_infinitely_often` (an infinite occurrence
  *set*) to a concrete monotone *sequence* — the form a downstream quantitative
  argument iterates over. All results are corollaries of the already-verified
  `next_occurrence_lt_of_modulus`; the only tool beyond it is `Classical.choose`,
  so no new axiom is introduced.
- Structural recursion in `occSeq` produces the definitional equations by `rfl`,
  so `occSeq_strictMono` / `occSeq_succ_lt` close by rewriting to `nextOcc` +
  `omega`.

### Status
Core axiom `e_absolutely_normal` remains **genuinely open** (no base proved normal
for `e` as of 2026) — not eliminable. The oq-06 target (`normal_imp_irrational`)
was long discharged as a theorem. This session sharpens the effective theory into
a usable enumeration; it does not touch the open core.

### Files modified
- `proofs/Proofs/ETranscendentalOQ02.lean` (+7 theorems, +2 defs, PART IV.9.a; 2302→2411 lines)
- `src/data/proofs/e-transcendental-oq-02/meta.json` (lineCount→2411, theoremCount→108; corrected prior drift from stale 2160/92)
- `src/data/research/problems/e-transcendental-oq-02-oq-06.json` (knowledge)

### Next steps
- The enumeration is now the natural handle for a *lower bound* on the occurrence
  count in `[0, N)` via `occSeq`-index counting — an explicit inverse to the gap
  bound. Only pursue if a downstream consumer needs it; otherwise oq-06 is
  saturated (core discharged, open core not eliminable).
