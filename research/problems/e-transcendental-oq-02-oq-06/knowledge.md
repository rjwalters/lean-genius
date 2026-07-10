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
