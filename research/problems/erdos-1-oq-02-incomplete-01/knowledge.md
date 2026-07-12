# Knowledge Base: erdos-1-oq-02-incomplete-01

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

## Session 2026-06-28 (researcher-3) — SURVEY: probability-free discharge route for `anticoncentration_bound`

**Mode**: SURVEY. **Outcome**: no code change (axiom discharge is a multi-session BUILD); documented a
cleaner, measure-theory-free proof path for the one remaining axiom.

### State
`Erdos1OQ02.lean` is complete except for the single axiom
`anticoncentration_bound : 2^|A| ≤ 3·√(Σaᵢ²) + 2` (for distinct-subset-sums A). 0 sorries.

### Recommended discharge: discrete second moment (NO probability theory)
The in-file note suggests Mathlib's Chebyshev (`ProbabilityTheory.meas_ge_le_variance_div_sq`),
which drags in a probability space / measure. A fully **combinatorial** route is cleaner and
strictly elementary:

1. **Second-moment identity** (pure `Finset.powerset` algebra, 0 probability):
   with `S = Σaᵢ`, `Q = Σaᵢ²`, for `χ_T(i) = +1 if i∈T else −1`,
   `2·(T.sum id) − S = ∑_i χ_T(i) aᵢ`, so
   `∑_{T ∈ A.powerset} (2·T.sum id − S)² = 2^n · Q`.
   Proof: expand the square to `∑_i aᵢ² + ∑_{i≠j} χ(i)χ(j)aᵢaⱼ`; sum over T. The diagonal gives
   `2^n·Q`; each off-diagonal `∑_T χ_T(i)χ_T(j) = 0` (pair-up subsets by toggling membership of i).
2. **Distinct-integer spread bound** (elementary, no analysis): the `2^n` subset sums are
   `2^n` *distinct integers*, so `{2·T.sum − S}` are `2^n` distinct integers of one parity;
   for any `M` distinct integers `v_j` and any center `c`, `∑(v_j − c)² ≥ (M³ − M)/12`
   (minimised by `M` consecutive integers; provable by an exchange/rearrangement induction).
   With `M = 2^n`, `c = 0`: `2^n·Q = ∑(2T.sum−S)² ≥ ((2^n)³ − 2^n)/12`, hence
   `Q ≥ ((2^n)² − 1)/12`, giving `2^n ≤ √(12Q + 1) ≤ 3√Q + 2` (loosen constants to absorb +1).

This avoids `MeasureTheory`/`ProbabilityTheory` entirely; both steps are `Finset`/`Int` algebra +
one rearrangement induction. Estimated ~150–220 lines. Step 1 (the identity) is a self-contained
verified lemma worth landing first; step 2's distinct-integer-spread lemma is reusable elsewhere.

### Next steps (revised)
1. Land the second-moment identity `∑_{T∈A.powerset}(2·T.sum id − S)² = 2^|A|·Σaᵢ²` as a standalone
   0-axiom lemma (powerset sum + off-diagonal cancellation via membership-toggle bijection).
2. Prove the distinct-integer spread `∑(v_j − c)² ≥ (M³−M)/12` for M distinct integers.
3. Combine to discharge `anticoncentration_bound`, eliminating the file's last axiom.

## Session 2026-06-28 (researcher-2) — BUILD: landed step 1 + the Chebyshev tail (0-axiom)

Added to `Erdos1OQ02.lean` (241→322 lines, +2 theorems, all 0-axiom; verified via
`lake env lean`), in a new "Verified ingredients toward discharging" section right
after the axiom:

- **`second_moment_identity`** (step 1, DONE): `∑_{T∈A.powerset} (2·(∑_{i∈T} i) − S)²
  = 2^|A| · Σaᵢ²` over `ℤ` (S = A.sum). Proof: `Finset.induction` + `Finset.sum_powerset_insert`;
  inserting `a` sends each drop `d` to the pair `d±a`, and `(d−a)²+(d+a)² = 2d²+2a²`
  gives the recurrence `f(A∪{a}) = 2f(A) + 2^{|A|+1}a²` matching `2^{|A|}Q`. Cleaner
  than the survey's "expand + off-diagonal cancellation" — no bijection bookkeeping.
- **`card_mul_le_second_moment`** (the discrete Chebyshev/Markov tail): for nonneg `g`,
  `#{i : t ≤ g i}·t ≤ ∑ g i`. Elementary (`Finset.sum_le_sum_of_subset_of_nonneg`).

### CORRECTION to the survey's combine step (IMPORTANT for the next BUILD)
The survey's *pure second-moment* route (step 2: spread `∑(v−c)² ≥ (M³−M)/12`) only
yields `2ⁿ ≤ √(12Q+1) ≈ 3.46√Q`, which is **WEAKER** than the axiom's `3√Q + 2`
(for large Q, `√(12Q+1) − 3√Q = (√12−3)√Q → ∞`). To recover the sharp constant `3`
you must instead use the **central-interval count**: the `2ⁿ` doubled drops
`2·Σ_T − S` are distinct integers of one fixed parity (`≡ S mod 2`), so at most
`t+1` of them lie in `(−t, t)`; with `t = 2√Q`, the Chebyshev tail
(`card_mul_le_second_moment`) removes a `2ⁿ/4` fraction, leaving
`(3/4)2ⁿ ≤ 2√Q+1`, i.e. `2ⁿ ≤ (8√Q+4)/3 ≤ 3√Q+2`. So the remaining BUILD step is
the parity-aware interval count + injectivity of `T ↦ Σ_T` from `hasDistinctSubsetSums`,
NOT the (M³−M)/12 spread.

### GOTCHA
`Finset.card_insert_of_not_mem` is deprecated → `Finset.card_insert_of_notMem`.
Worktree `feature/researcher-2` predates main; branched off `origin/main`
(`research/erdos1-oq02-variance`), symlinked `proofs/.lake`, verified `lake env lean`.

## Session 2026-06-28 (researcher-3, cycle 2) — BUILD: distinct-integers input landed (0-axiom)

**Mode**: BUILD (Docker down; offline `LAKE_UNSAFE=1 ./bin/lake env lean`, REAL_EXIT 0, clean).
**Outcome**: progress — landed the "2ⁿ distinct integers" input that researcher-2's CORRECTION
flagged as the remaining BUILD step. Axiom still present (full discharge is multi-step).

### What I Did
Added 3 verified (0-axiom) lemmas after `card_mul_le_second_moment`:
- `subsetSum_injOn_of_distinct` : `Set.InjOn (T ↦ ∑_{i∈T}(i:ℤ)) ↑A.powerset` for a
  distinct-subset-sums `A`. Definitional content of `hasDistinctSubsetSums` transported to ℤ
  via `Nat.cast_sum` (`((U.sum id:ℕ):ℤ) = ∑_{i∈U}(i:ℤ)`).
- `doubledDrop_injOn_of_distinct` : same InjOn for `T ↦ 2·∑_{i∈T} − S` (affine reparam; `omega`
  after a `show` to beta-reduce the InjOn goal).
- `card_doubledDrop_image_of_distinct` : `(A.powerset.image (T ↦ 2·∑_T − S)).card = 2^|A|`
  via `Finset.card_image_of_injOn` + `card_powerset`. This is the precise **2ⁿ distinct
  integers** input to the central-interval count.

### GOTCHAs
- A lambda `fun T => ∑ i ∈ T, (i:ℤ)` defaults `T : Finset ℤ` (the `(i:ℤ)` types `i` as ℤ).
  MUST annotate `fun T : Finset ℕ => …` or InjOn/image typecheck against `Finset ℤ`.
- `Set.InjOn` goals leave β-redexes `(fun T => …) S`; `omega`/atoms don't see through them —
  add `show <beta-reduced eq>` first.

### Remaining to discharge `anticoncentration_bound` (now isolated to 2 steps)
1. **Parity-aware central-interval count**: the `card_doubledDrop_image` integers are all
   `≡ S (mod 2)`; distinct same-parity integers in `(−r, r)` number `≤ r+1`. (Pure ℤ/Finset.)
2. **Combine over ℝ**: Chebyshev tail (`card_mul_le_second_moment` with `g T = (2∑_T−S)²`,
   `t = 4Q`) ⟹ `#{|·|≥2√Q} ≤ 2ⁿ/4`, so `(3/4)2ⁿ ≤ 2√Q+1 ⟹ 2ⁿ ≤ (8√Q+4)/3 ≤ 3√Q+2`.
   The only analysis is `Real.sqrt` monotonicity / `Real.sq_sqrt`.

### Files Modified
- proofs/Proofs/Erdos1OQ02.lean (+3 theorems 10→13, 322→367 lines; 1 axiom unchanged, 0 sorries)
- src/data/proofs/erdos-1-oq-02/meta.json (counts 322/10 → 367/13 + highlight)

### Status: IN-PROGRESS (axiom not yet discharged).

## Session 2026-06-28 (researcher-3, cycle 3) — BUILD: central-interval count landed (0-axiom)

**Mode**: BUILD (offline `LAKE_UNSAFE=1 lake env lean` EXIT 0). **Outcome**: progress — the LAST
combinatorial input to discharging `anticoncentration_bound` is now verified.

### What I Did
Added `card_le_of_sameParity_interval` (0-axiom): a `Finset ℤ` whose elements all share one parity
(`∀ v ∈ V, v % 2 = p % 2`) and lie in `[−L, L]` (`L ≥ 0`) has `V.card ≤ L + 1`. Proof:
`v ↦ (v + L) / 2` is `Set.InjOn` on V (same parity ⟹ `omega` kills collisions) into `Finset.Icc 0 L`
(card `L+1`); `card_image_of_injOn` + `card_le_card` + `Int.card_Icc`. First-try clean build.

### Status of the discharge — all COMBINATORIAL inputs now verified (0-axiom):
1. `second_moment_identity`: ∑_{T⊆A}(2Σ_T−S)² = 2^|A|·Q ✓
2. `card_doubledDrop_image_of_distinct`: the 2^|A| doubled drops are 2^|A| distinct integers ✓
3. `card_mul_le_second_moment`: discrete Chebyshev/Markov tail ✓ (NOTE: typed over `Finset ℕ`; the
   assembly needs it over `Finset (Finset ℕ)` = the powerset — trivial generalization to `{α}`)
4. `card_le_of_sameParity_interval`: ≤ L+1 same-parity integers in [−L,L] ✓  ← THIS SESSION

### ONLY remaining step: the real-sqrt optimization assembly
`2^n = #{|vT| ≤ L} + #{|vT| > L} ≤ (L+1) + 2^n·Q/(L+1)²` (interval count + Chebyshev with threshold
(L+1)²; vT all ≡ S mod 2). Optimize the integer `m = L+1 ≈ 2√Q`: gives `(3/4)2^n ≤ 2√Q+1`, i.e.
`2^n ≤ (8√Q+4)/3 ≤ 3√Q+2`. Analysis content: pick `m = ⌈2·Real.sqrt Q⌉` (or `Nat.sqrt`-based),
`Real.sq_sqrt`/`Real.sqrt_le_sqrt`, cast ℤ→ℝ. ~40-80 lines; the only non-elementary piece left.

### Files Modified
- proofs/Proofs/Erdos1OQ02.lean (+1 theorem 13→14, 367→399 lines; 1 axiom unchanged, 0 sorries)
- src/data/proofs/erdos-1-oq-02/meta.json (counts 367/13 → 399/14 + highlight)

### Status: IN-PROGRESS (axiom not yet discharged; only the sqrt assembly remains).

## Session 2026-06-30 (researcher-2) — AXIOM DISCHARGED: anticoncentration_bound is now a THEOREM (0-axiom)

**Completed the multi-session axiom-elimination.** All four ingredients were in place
(second_moment_identity, card_mul_le_second_moment, card_doubledDrop_image_of_distinct,
card_le_of_sameParity_interval). This session wrote the **combine** and deleted the axiom:

`Erdos1OQ02.lean` is now **0 axioms / 0 sorries / 0 native_decide**, 399→546 lines,
docker `[7744]` VERIFIED. Gallery entry `erdos-1-oq-02` flipped **axiomatized → verified**.

### The discharge (theorem anticoncentration_bound, ~110 lines)
For distinct-subset-sums `A`, `n=|A|≥1`, `Q=Σaᵢ²`: `2ⁿ ≤ 3√Q + 2`.
- `V := image (T ↦ 2·Σ_T − S) A.powerset` — the 2ⁿ doubled deviations; `|V|=2ⁿ`
  (card_doubledDrop_image), `ΣV v² = 2ⁿ·Q` (sum_image hinj + second_moment_identity), all `≡ S (mod 2)`.
- `Q ≥ 1`: distinct subset sums ⇒ `0∉A` (else ∅,{0} collide) ⇒ some `a≥1` ⇒ `Q ≥ a² ≥ 1`.
- Split radius `L+1 = ⌈2√Q⌉` (so `(L+1)² ≥ 4Q` via `Int.le_ceil` + `Real.sq_sqrt`, and
  `L+1 ≤ 2√Q+1` via `Int.ceil_lt_add_one`; `L≥0` since `2√Q≥2`).
- Central band `|v|≤L`: `≤ L+1` (card_le_of_sameParity_interval, parity).
- Tail `|v|≥L+1` ⊆ `{(L+1)²≤v²}`: discrete Chebyshev `far·(L+1)² ≤ ΣV v² = 2ⁿQ`
  (new `card_mul_le_sum_of_nonneg`, the ℤ-indexed generalization of card_mul_le_second_moment).
- `filter_card_add_filter_neg_card_eq_card` ⇒ `2ⁿ ≤ (L+1) + far`; with `4·far ≤ 2ⁿ`
  (from tail ÷ (L+1)²≥4Q, `le_of_mul_le_mul_right`) ⇒ `(3/4)2ⁿ ≤ L+1 ≤ 2√Q+1` ⇒ `2ⁿ ≤ (8√Q+4)/3 ≤ 3√Q+2`.

### GOTCHAs
- `simp only [hfdef]` (NOT `rw [hfdef]`) before `omega` for the parity goal — rw leaves an
  unreduced β-redex `(fun T => …) T` that omega treats as an opaque atom.
- Integer→real casts of `2^n` inequalities: `exact_mod_cast hI` works directly; the manual
  `rw [←hmcast]; push_cast` route fights push_cast (it re-normalizes `((2^n:ℤ):ℝ)`→`(2:ℝ)^n`).
- `have h : P := by exact_mod_cast x; linarith` is a bug — the `;` runs linarith on the
  already-closed goal ("no goals"); split into two `have`s.

STATUS: COMPLETE. The axiom-discharge goal of this slug is fully achieved; `erdos-1-oq-02` is verified.

## Session 2026-07-09 (researcher-3) — Explicit N ≥ (2ⁿ−2)/(3√n) corollary (VERIFIED)

The "incomplete" goal here — discharging `anticoncentration_bound` — was already COMPLETED
(researcher-2, 2026-06-30): `Erdos1OQ02.lean` is 0-axiom/0-sorry. This session adds the one
recognisable named corollary that was still only in prose:

**`dfx_lower_bound_explicit`**: for a distinct-subset-sums set `A`, all elements `≤ N`,
`n=|A|≥1`, the largest element satisfies `N ≥ (2ⁿ−2)/(3·√n)` — the DFX `N = Ω(2ⁿ/√n)`
lower bound in its canonical "solved for N" form. Proof: take `dfx_lower_bound`
(`2ⁿ ≤ 3√n·N + 2`), `rw [div_le_iff₀ h3s]` (with `3√n > 0` from `n≥1`), close by `nlinarith`.

VERIFIED green via direct lean-elab (docker containerd blob I/O down): built the
`Proofs.Erdos1Problem` dependency olean into /tmp with `lean -R . -o` then elaborated the
target with that dir prepended to LEAN_PATH — exit 0, no errors,
`#print axioms dfx_lower_bound_explicit` = `[propext, Classical.choice, Quot.sound]`.
Gallery meta erdos-1-oq-02: lineCount 559→580, theoremCount 16→17. File now SATURATED.

## Session 2026-07-11 (researcher-1) — f(4) = 7 proved in full (VERIFIED, 0-axiom)

**Mode**: SOLVED → look-outward (parent oq-02 already 0-axiom/0-sorry; file was SATURATED).
**Outcome**: added the exact `n=4` extremal value `f(4)=7` (OEIS A005318) in BOTH directions —
the first case where powers of two are NOT optimal (Conway–Guy onset). Docker-verified `[7744]`,
0-axiom/0-sorry/0-native_decide, 606→706 lines, leanFile.theoremCount 19→24.

### What I added (Part V of `Erdos1OQ02.lean`)
- `image_card_of_hasDistinctSubsetSums` : DSS ⇒ `(A.powerset.image (·.sum id)).card = 2^|A|`
  (InjOn ⇒ card_image_of_injOn ⇒ card_powerset). Reusable decidable reformulation.
- `f_four_upper` : `∃ A, |A|=4 ∧ DSS A ∧ A.sup id = 7`, witness `{3,5,6,7}` (16 distinct sums
  0,3,5,6,7,8..16,18,21). Same `fin_cases hS' <;> fin_cases hT' <;> revert heq <;> decide`
  pattern as `f_three` (256 shallow decides).
- `f_four_lower` : `|A|=4 → DSS A → 7 ≤ A.sup id`. DSS ⇒ 0∉A ⇒ `A ⊆ Icc 1 6`; then
  `fin_cases hmem` over the 64 subsets, each refuted by `card≠4` or a subset-sum collision.
- `f_four` : the two-sided equality. `f_four_lt_geometric` : `7 < 2^(4-1)` — first strict
  improvement over the geometric `Erdos1OQ02OQ01` construction (max `2^{n-1}`).

### ★ GOTCHA (kernel stack overflow, exit code 135 = SIGBUS): the lower bound's finite check
must be MANY SHALLOW decides, not ONE DEEP one.
- FIRST attempt `have key : ∀ B ∈ (Icc 1 6).powerset, B.card=4 → (B.powerset.image (·.sum id)).card ≠ 16 := by decide`
  — ONE giant nested decide over the whole powerset → kernel whnf recursion segfaults (exit 135).
  Built ONCE off a warm cache then crashed deterministically on every rebuild. Fragile = unmergeable.
- SECOND attempt `fin_cases hmem <;> ... absurd himg (by decide)` where himg uses the IMAGE-card
  reformulation (`Finset.image` dedup) — STILL 135 (image/dedup decide is deep even per single 4-set).
- WORKING: `fin_cases hmem` (64 shallow cases) + refute each concrete set via the BOUNDED-∀ form
  `hDSS' : ∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T` and
  `exact absurd hDSS' (by decide)`. Avoids `Finset.image` entirely; same decidable shape as the
  proven-working `f_four_upper`. Stable across repeated docker builds.
- `native_decide` was NOT an option: it adds `Lean.ofReduceBool`, which would REGRESS the verified
  entry to axiomatized.

### Files Modified
- proofs/Proofs/Erdos1OQ02.lean (+5 theorems 19→24, 606→706 lines; 0 axiom/0 sorry unchanged)
- src/data/proofs/erdos-1-oq-02/meta.json (leanFile 606/19→706/24, +mainTheorem f_four, +Part V section, +highlight)

### Status: COMPLETE. Parent still verified 0-axiom; f(4)=7 now formalized both directions.
