# Knowledge Base: nth-root-irrational-oq-03

Insights accumulated during research on this problem (Hermite-Lindemann / Lindemann-Weierstrass).

---

## Problem Understanding (Iteration 1, researcher-10, 2026-05-12)

This slug was placed under the `nth-root-irrational` parent during seeker batch initialization (2026-05-12 13:06 UTC, PR #18263), but the Lindemann–Weierstrass / Hermite–Lindemann content it covers is **transcendence theory**, which is orthogonal to the parent's *algebraic irrationality of irreducible polynomial roots* material. The slug's effective home is the existing `e-transcendental-oq-*` family (`oq-01`, `oq-02`, `oq-03`) and `hermite-lindemann` (no slug yet, but `HermiteLindemann.lean` exists).

## Insights

### Insight 1 — The "open question" is mostly already infrastructure

The problem statement (transcendence of $e^\alpha$ for nonzero algebraic $\alpha$, and the algebraic-independence form for $\Q$-linearly-independent $\alpha_1, \dots, \alpha_n$) is **already stated and axiomatized** in `proofs/Proofs/HermiteLindemann.lean:147` via:

```lean
axiom hermite_lindemann :
    ∀ α : ℂ, α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℤ (Complex.exp α)
```

with 390 lines of supporting pedagogical exposition, statement of the LW theorem, and corollary derivations for $e$ (Wiedijk #67) and $\pi$ (Wiedijk #53). The "open question" framing is misleading: the *statement* is closed; what remains is *proof* of the axiomatized statement, plus surrounding bridge work.

### Insight 2 — Two tractable adjacent axioms (in OQ03 sibling)

> **STATUS UPDATE (S11 source audit, 2026-06-14):** Axiom (1) below, `irrational_liouvilleWith_two`, is **no longer an axiom** — it was discharged into a full `theorem` at S5c (2026-05-16, see Iteration insight chain) and is verified in source at `ETranscendentalOQ03.lean:180`. The file now carries **exactly one** `axiom`: `e_not_liouvilleWith_gt_two` (item 2). This Iteration-1 narrative is preserved for history; treat item (1) as **DONE**.

`ETranscendentalOQ03.lean` contains two axioms feeding the $\mu(e) = 2$ irrationality-measure result:

1. `irrational_liouvilleWith_two : ∀ x, Irrational x → LiouvilleWith 2 x` (Dirichlet's approximation theorem lower bound)
2. `e_not_liouvilleWith_gt_two : ∀ p > 2, ¬LiouvilleWith p (exp 1)` (sharp upper bound from regular CF expansion of $e$)

Axiom (1) is a standard Mathlib-provable result (Dirichlet's theorem on rational approximations: every irrational has at least one infinite sequence of approximants $|x - p/q| < 1/q^2$). It should reduce to existing `Mathlib.NumberTheory.DiophantineApproximation` API.

Axiom (2) is harder but uses the *known* regular continued fraction $e = [2; 1, 2k, 1]_{k=1}^\infty$ (Euler 1737). The proof requires:

- Linking the partial quotients $a_n$ to the convergents $p_n/q_n$
- Bounding $q_{n+1} \leq (2k+1) q_n + q_{n-1}$, hence $q_n$ grows polynomially-in-$\sqrt{n}$ in the relevant subsequence
- Concluding that the approximation quality is at most $1/q^{2+o(1)}$

Mathlib has `Mathlib.NumberTheory.ContinuedFractions.*` API that may cover most of this; the bottleneck is matching the project's `LiouvilleWith` formulation.

### Insight 3 — The full HL axiom is 800-1500 lines of work

`hermite_lindemann` is the deep result. A complete formal proof requires:

1. **Auxiliary polynomial machinery**: $f_p(x) = x^{p-1}(x-\alpha)^p (x - 2\alpha)^p \cdots (x - n\alpha)^p / (p-1)!$ for large prime $p$.
2. **Integral analysis**: Define $F(x) = \sum_{j \geq 0} f^{(j)}(x)$; key identity $\int_0^{k\alpha} f(t) e^t dt = e^{k\alpha} F(0) - F(k\alpha)$.
3. **Prime-selection contradiction**: Show $S = \sum_k \beta_k I_k$ is simultaneously a nonzero integer divisible by $p$ (lower-bound $\geq 1$) and bounded by $C^p / (p-1)!$ in absolute value (upper-bound $\to 0$). Take $p$ larger than $\max(|\alpha|, |\beta_0|)$ to derive a contradiction.

Estimating proof length:

- Polynomial setup + derivatives + factorial accounting: ~200 lines
- Integral identity (integration by parts $p$-many times): ~150 lines
- Integer-and-divisibility argument: ~250 lines
- Bound argument (Stirling + max-modulus): ~150 lines
- Coercion between $\mathbb{Z}[\alpha]$ and $\mathbb{C}$: ~100 lines
- Glue + main theorem statement: ~50 lines

Total: roughly 900 lines, conservatively. Mathlib has had an active Lindemann–Weierstrass formalization PR (search: `mathlib4 lindemann`) — the right move long-term is to **wait for Mathlib upstream** and then bridge, rather than re-formalize.

### Insight 4 — Project status is "axiomatized", not "verified"

For meta.json on this slug's gallery entry (if/when created), the appropriate badge is `axiom` and status is `axiomatized`. The full proof depends on:

- `axiom hermite_lindemann` (HermiteLindemann.lean) — the marquee assumption (still open; gated on Mathlib PR #28013)
- ~~2 axioms~~ **1 axiom** in `ETranscendentalOQ03.lean` — `e_not_liouvilleWith_gt_two` only (the lower-bound axiom was discharged at S5c, 2026-05-16; source-verified 2026-06-14)
- ~~4 sorries across siblings~~ **0 sorries** — the S1 "4 sibling sorries" claim was already corrected at S7 (2026-06-05): actual sorry count across all 5 sibling files is **0**

Per the Axiom Integrity Policy in CLAUDE.md, this slug must NEVER be marked `verified` while these assumptions remain.

## Dead Ends

None recorded for this slug yet — Iteration 1 is the first session.

## Promising Next-Iteration Targets

### Target A (S2): Discharge `irrational_liouvilleWith_two` — ✅ DONE (S5c, 2026-05-16)

> **RESOLVED.** This target was completed at S5c: `axiom irrational_liouvilleWith_two` was replaced by a full `theorem` (now `ETranscendentalOQ03.lean:180`) using `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` plus the slice-finiteness helper `rat_approx_bounded_den_finite`, after adding `import Mathlib.NumberTheory.DiophantineApproximation.Basic`. `meta.json` axiomCount went 2→1. The strategy sketch below is retained only as the historical record of how it was approached. **The sole remaining axiom in this file is `e_not_liouvilleWith_gt_two` (Target C / S5d.A), which is Docker-gated 280–480 LOC CF work.**

**Statement to prove:**

```lean
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x
```

**Proof strategy (Mathlib API):**

The Mathlib definition of `LiouvilleWith` (in `Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith`) requires a constant $C > 0$ and infinitely many rationals $p/q$ with $|x - p/q| < C/q^p$. For $p = 2$, this is exactly Dirichlet's approximation theorem.

Mathlib has (or should have, depending on pin):

- `Irrational.exists_int_nat_lt` or similar
- `Real.exists_rat_btwn` — interval density
- `Nat.exists_pos_of_lt` — bound construction

Candidate sketch:

```lean
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x := by
  -- LiouvilleWith p x ↔ ∃ C, ∀ᶠ q in atTop, ∃ p, |x - p/q| < C/q^p
  -- Dirichlet: ∀ N, ∃ q ∈ [1, N], ∃ p, |x - p/q| < 1/(qN) ≤ 1/q^2
  -- Use C = 1, take q large
  sorry
```

**Risk:** Mathlib v4.26.0 (the pin used here) may have slightly different API names; ~1-2 hours to chase the right lemmas.

### Target B (S3): Lindemann–Weierstrass bridge to Mathlib

**Goal:** Survey current Mathlib state of `Mathlib.NumberTheory.Transcendental` (or wherever the LW formalisation is landing). If a `transcendental_exp_of_isAlgebraic_ne_zero` or similar is upstream, write a bridge lemma; otherwise document the upstream PR status and add a comment to `HermiteLindemann.lean` referencing the upstream effort.

### Target C (S4 or beyond): `e_not_liouvilleWith_gt_two`

Harder — but isolated. The continued-fraction route is the right strategy. If `Mathlib.NumberTheory.ContinuedFractions` has the regular CF of $e$ pre-computed (unlikely on v4.26.0), bridge directly; otherwise this requires standalone CF infrastructure and is multi-session.

## Open Questions for Future Iterations

- What is the current state of `mathlib4` Lindemann–Weierstrass PRs as of 2026-05-12? (Web check needed in S2.)
- Should this slug be **renamed/aliased** to align with the existing `e-transcendental-*` or `hermite-lindemann` family? Or should `nth-root-irrational-oq-03` remain as a curated cross-reference entry pointing to the real work in those slugs?
- Are there any *new* mathematical content gaps (i.e., theorems not in any existing file) that this slug could fill? (Initial scan suggests no — the territory is well-covered.)

## Cross-References

- **Sibling slugs**: `e-transcendental-oq-01`, `e-transcendental-oq-02`, `e-transcendental-oq-03` — directly related
- **Lean files**: `proofs/Proofs/HermiteLindemann.lean`, `eTranscendental.lean`, `ETranscendentalOQ0{1,2,3}.lean`, `PiTranscendental.lean`
- **Parent**: `nth-root-irrational` (algebraic irrationality of irreducible-polynomial roots) — orthogonal in technique despite shared "expanding $\Q$" theme
- **Adjacent transcendence work**: `angle-trisection-cos-20-gal-oq-01-oq-03` (cyclotomic $\Phi_{2p}(-1) = p$, requires algebraic-not-transcendental machinery), `algebraic-numbers-countable-oq-02-oq-04` (countability bounds)

---

## Session 2026-06-05 (Session 7) — S7 ACT — `e_transcendental` axiom discharged via Hermite-Lindemann bridge

**Mode**: REVISIT (knowledge tier RICH at 19 items)
**Outcome**: progress — local axiom reduction + 5 pre-existing Mathlib v4.26.0 build regressions repaired

### What I Did
- Discovered `HermiteLindemann.lean:208` already contained `hermite_lindemann 1 one_ne_zero (isAlgebraic_int 1)` — an aspirational derivation of `e_transcendental` that never compiled
- Audited dependency chain: `eTranscendental.lean` had its own `axiom e_transcendental` (line 147) but the same statement was derivable from `axiom hermite_lindemann`
- Wrote the bridge `e_transcendental_int : Transcendental ℤ (Real.exp 1)` in `HermiteLindemann.lean` using `IsAlgebraic.algebraMap` (3 lines)
- Replaced `axiom e_transcendental` with `theorem e_transcendental := HermiteLindemann.e_transcendental_int`
- Repaired 3 broken theorems in `HermiteLindemann.lean` (Mathlib v4.26.0 API regressions): `e_transcendental_rationals`, `pi_transcendental`, `pi_transcendental_real`
- Cleaned up 7 dangling `/-- ... -/` aspirational-axiom docstrings → `/-! ... -/` blocks

### Key Findings
- `IsAlgebraic.algebraMap` (Mathlib/RingTheory/Algebraic/Basic.lean:174) is the right primitive for ℝ→ℂ transcendence transfer — replaces the broken `Polynomial.aeval_algHom_apply (Complex.ofRealHom.toAlgHom)` pattern in 1 line
- S5b's "flip `.mp` to `.mpr`" applies consistently: `IsFractionRing.isAlgebraic_iff A K x : IsAlgebraic A x ↔ IsAlgebraic K x` so `.mpr` goes ℚ→ℤ
- The "4 sibling sorries" claim from S1 (Insight 1) is stale — actual sorry count across all 5 sibling files is **0**
- `HermiteLindemann.lean` was broken on origin/main but unnoticed because `Proofs.lean` builds Mathlib targets lazily; `ETranscendentalOQ03` doesn't import HermiteLindemann so S5c/S5d/S6 all missed the issue
- `pi_transcendental` and `pi_transcendental_real` (Wiedijk #53) now provide working bridges in addition to the e bridge — orthogonal axiom-reduction targets opened up

### Files Modified
- `proofs/Proofs/HermiteLindemann.lean` (3 theorems repaired, 1 new theorem, 7 docstring cleanups; 390→373 lines)
- `proofs/Proofs/eTranscendental.lean` (axiom → theorem, +1 import; 305→304 lines)
- `src/data/proofs/e-transcendental/meta.json` (leanFile.axiomCount 1→0, theoremCount 12→13)
- `src/data/proofs/hermite-lindemann/meta.json` (leanFile.theoremCount 4→5, lineCount 390→373)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (phase OBSERVE→ACT, iteration 7→8, knowledge updates)

### Build verification
`Proofs.eTranscendental` 3079/3079 jobs ✓; `Proofs.ETranscendentalOQ03` 3085/3085 jobs ✓.

### Next Steps
- S8 watch tick on PR #28013 (current 169.8h stale, S6 grace period ends ~2026-06-26)
- S5d.A/B/C continued-fraction-of-e arc remains deferred per S6 grace-period logic
- S7 follow-up: use repaired `pi_transcendental_real` to discharge `axiom lindemann_theorem` in `PiTranscendental.lean` (requires first fixing PT's pre-existing v4.26.0 build errors — mechanic-class)

See `sessions/2026-06-05-s7-act-e-transcendental-axiom-discharge-via-hermite-lindemann-bridge.md` for full details.

---

## Session 2026-06-05 (Session 9, S8 ACT) — lindemann_theorem axiom discharge in PiTranscendental.lean

**Researcher**: researcher-11
**Mode**: REVISIT (extending S7 ACT pattern to sibling file)
**Outcome**: progress — local axiom reduction in `PiTranscendental.lean` (1→0)

### What I did
- Recognized `axiom lindemann_theorem` (PT:125) and `axiom hermite_lindemann` (HL:147) differ only in base ring (`IsAlgebraic ℤ` vs `IsAlgebraic ℚ`).
- Replaced PT's `axiom` with a 3-line `theorem` derived from `HermiteLindemann.hermite_lindemann` via `(IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp` bridge.
- Repaired 2 pre-existing v4.26.0 regressions flagged in S7 nextSteps:
  - Line 228: added `import Mathlib.Analysis.Real.Pi.Irrational` for `irrational_pi`.
  - Line 285: replaced `isAlgebraic_algebraMap (1 : ℚ)` with `isAlgebraic_one` (S5b Fix #2 pattern).
- Added imports `Mathlib.Analysis.Real.Pi.Irrational` and `Proofs.HermiteLindemann` (no circular dep: HL.lean has no `import Proofs.*`).

### Key Findings
- The `IsFractionRing.isAlgebraic_iff` bridge is the canonical ℤ ↔ ℚ algebraicity translator in this codebase (used 10+ times, including the identical `.mp ℤ ℚ ℂ` call at HermiteLindemann.lean:228).
- S5b/S7 fix patterns generalize cleanly: same diagnoses, same one-line fixes, applied to a different file.
- The two "pre-existing build errors" flagged by S7 as mechanic-class were not actually deep — both have known 1-line fixes from sibling files. The researcher applied them as part of the axiom-reduction since they were on the critical path.

### Files Modified
- `proofs/Proofs/PiTranscendental.lean` (+2 imports, axiom→theorem, `isAlgebraic_one` fix; 457→463 lines)
- `src/data/proofs/pi-transcendental/meta.json` (leanFile.axiomCount 1→0, theoremCount 18→19, lineCount 457→463; assumptions reworded)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (iteration 8→9, +1 insight, +1 builtItem)

### Build verification
Initial attempts blocked by host disk pressure (cache I/O `os error 5/30`, daemon crash). `docker system prune -f` reclaimed 8.155 GB; re-run surfaced a long-standing forward-reference bug in `pi_transcendental` (refs `I_algebraic`/`neg_one_algebraic` defined later in the file — invalid in Lean 4). Replaced `pi_transcendental` body with a one-line alias to `HermiteLindemann.pi_transcendental_real`. **Final build: 3092/3092 jobs ✓ (81s)**.

### Next Steps
- S9 watch tick on PR #28013 (head SHA `5abb7c68488` unchanged since 2026-05-29; 7 days).
- Mechanic: ETranscendentalOQ02.lean line 708 build error remains out of researcher scope.
- ETranscendentalOQ01.lean transitively depends on PT; S8 fix should unblock it.

See `sessions/2026-06-05-s8-act-lindemann-theorem-axiom-discharge-via-hermite-lindemann-bridge.md` for full details.

---

## Session 2026-06-14 (Session 11) — S11 Source Audit + Iteration-1 narrative de-stale

**Mode**: REVISIT (RICH; Docker DOWN — verification blackout)
**Outcome**: progress (knowledge integrity) — no proof advance possible (sole open item is Docker-gated)

### What I Did
- Read `ETranscendentalOQ03.lean` directly from source: confirmed **1** `^axiom ` (`e_not_liouvilleWith_gt_two`, line 247), **0** sorries, 312 LOC. `irrational_liouvilleWith_two` is a full `theorem` at line 180 (proved S5c).
- Confirmed `src/data/proofs/e-transcendental-oq-03/meta.json` is already accurate (axiomCount 1, sorries 0, lineCount 312, assumptions note the lower-bound discharge) — no gallery edit needed.
- De-staled this file's **Iteration-1 narrative** (the only stale content): Insight 2, Insight 4, and the "Target A" section all still presented `irrational_liouvilleWith_two` as an open axiom. Marked Target A ✅ DONE and corrected the axiom/sorry tallies, with superseded banners (history preserved).
- Verified no open PR and no concurrent claim on the slug; S10 watch tick (#23728) is the latest commit on the problem dir.

### Key Findings
- The research JSON (`progressSummary`, insights #9/#11) and the gallery meta were already correct; only the human-readable Iteration-1 prose at the top of `knowledge.md` lagged. Future researchers reading top-down would otherwise re-attempt a solved target.
- **Sole remaining axiom**: `e_not_liouvilleWith_gt_two` (μ(e) ≤ 2 upper bound). Its only discharge route is the Euler CF expansion of e (`[2;1,2k,1]`), absent from Mathlib (confirmed S5d), scoped 280–480 LOC — **Docker-gated**, so blocked this session.
- The marquee `axiom hermite_lindemann` (HermiteLindemann.lean) remains gated on Mathlib PR #28013 (passive watch, grace period to ~2026-06-26).

### Files Modified
- `research/problems/nth-root-irrational-oq-03/knowledge.md` (de-stale Insight 2/4 + Target A; this entry)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (S11 insight; iteration bump)

### Next Steps
- Unchanged: when Docker returns and/or grace period (~2026-06-26) passes with PR #28013 still stale, begin S5d.A (CF expansion of e). No build-free forward step remains.

---

## Session 2026-06-15 (Session 12) — S12 ACT — CF-independent reduction for `μ(e) ≤ 2`

**Mode**: REVISIT (RICH, 25 items; dual blackout: Docker `docker info` hangs, Aristotle `prove` → 404 "Resource not found" — both verified live this session)
**Outcome**: progress (architecture) — isolated the analytic heart of the sole open axiom; no axiom-count reduction yet (build-pending, unregistered)

### What I Did
- Re-confirmed the sole open item is `axiom e_not_liouvilleWith_gt_two (p) (hp : p > 2) : ¬LiouvilleWith p (exp 1)` (ETranscendentalOQ03.lean:247), 0 sorries elsewhere.
- Web scout: no new Mathlib4 CF-of-e or irrationality-measure infrastructure (confirms S5d/S6); regular continued fraction of `e` still absent.
- **Key observation**: the monolithic axiom bundles two independent ingredients — (1) `LiouvilleWith` filter/Diophantine bookkeeping (general, not e-specific) and (2) the deep CF-of-e bad-approximability bound. Every prior session treated it as one indivisible CF axiom.
- Wrote `proofs/Proofs/ETranscendentalOQ03Reduction.lean` (UNREGISTERED, build-pending) discharging ingredient (1) once and for all:
  - `not_liouvilleWith_of_diophantine_bound (x p) (hp : 2 < p) (c) (hc : 0 < c) (hlb : ∀ n≥1 ∀ m, c/n^((p+2)/2) ≤ |x − m/n|) : ¬ LiouvilleWith p x`
  - `e_not_liouvilleWith_gt_two_of_bound` — the e-specialization, the precise remaining obligation.
- Proof engine: write `a := (p+2)/2`, `d := (p−2)/2`; then `a+d=p`, `d>0`, `2<a<p`. From `LiouvilleWith` extract `C` and `∃ᶠ n, |e−m/n| < C/n^p`; since `c·n^d → ∞` (`Real.tendsto_rpow_atTop`), eventually `C ≤ c·n^d`; `Frequently.and_eventually` + `.exists` picks one such `n`; chaining `c/n^a ≤ |e−m/n| < C/n^p`, splitting `n^p=n^a·n^d` and cancelling `n^a` gives `c·n^d < C`, contradiction.
- Verified non-vacuity numerically: `min_{n≤4000,m} |e−m/n|·n^2.5 = 0.282 > 0` (Python, exact-`round`), so the reduced hypothesis is genuinely satisfiable for e at p=3.

### Key Findings
- The reduction converts the open axiom from an analysis-AND-number-theory statement into a **pure Diophantine lower bound** — the future Docker/CF session needs zero `LiouvilleWith` manipulation.
- Lemma names cross-checked against building sibling files (no Docker): `div_lt_div_iff_of_pos_right` (4.26 rename of `div_lt_div_right`, used identically in LiouvilleTheoremOQ04.lean:1123), `(Real.tendsto_rpow_atTop _).comp tendsto_natCast_atTop_atTop` (Erdos1155OQ02.lean:138), `lt_div_iff₀`, `Tendsto.const_mul_atTop`, `Frequently.and_eventually`, `Tendsto.eventually_ge_atTop`.
- Per Axiom Integrity Policy: this does NOT reduce the assumption count (the CF bound remains axiomatic when wired in). It is a proof-architecture refactor that makes the remaining obligation self-contained.

### Files Modified
- `proofs/Proofs/ETranscendentalOQ03Reduction.lean` (NEW, unregistered, build-pending)
- `research/problems/nth-root-irrational-oq-03/knowledge.md` (this entry)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (S12 knowledge updates, iteration bump)

### Next Steps
- When a build host returns: compile `ETranscendentalOQ03Reduction.lean`; repair any rpow-rewrite step if needed (the `hCsplit`/cancel chain is the only moderate-risk part).
- Then the e-axiom discharge reduces to proving the single Diophantine bound `∃ c>0, ∀ n≥1 ∀ m, c/n^((p+2)/2) ≤ |e−m/n|` — i.e. begin S5d.A (Euler CF expansion of e, `[2;1,2k,1]`), still the dominant 280–480 LOC cost.
- Marquee `axiom hermite_lindemann` remains gated on Mathlib PR #28013 (passive watch, grace ~2026-06-26).
