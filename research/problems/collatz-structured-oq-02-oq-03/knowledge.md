# Knowledge Base: collatz-structured-oq-02-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-03 asks whether Tao's 2019 almost-all result (logarithmic density 1) can be
formalized in Lean with Mathlib. Tao (2019, *Forum Math. Pi*): for every
`f : ℕ → ℝ` with `f n → ∞`, the set `{n : Col_min(n) < f n}` has **logarithmic
density 1**. This subsumes Terras (1976) / Korec (1994) (almost all n have finite
stopping time, in natural density).

---

## Insights

- **Statement formalizes cleanly.** "Logarithmic density 1" becomes the predicate
  `HasLogDensityOne S := Tendsto (fun N => (∑_{n≤N,n∈S} 1/n)/(∑_{n≤N} 1/n)) atTop (𝓝 1)`.
  `Set.indicator` (classical, no `DecidablePred` needed) handles the filtered sum.
  Tao's theorem is then a single clean `axiom tao_2019` quantified over all `f → ∞`.
- **The elementary half is axiom-free.** Even numbers drop in one step
  (`collatz n = n/2 < n`), and powers of two collapse to 1
  (`collatz^[k] (2^k) = 1`, induction via `collatz (2·m) = m` + `pow_succ'` +
  `Function.iterate_succ_apply`). These give explicit large families in the
  almost-all set without any analysis.
- **Orbit minimum** `colMin n := sInf {m | ∃ k, collatz^[k] n = m}`; `colMin_le_self`
  is just `Nat.sInf_le ⟨0, Function.iterate_zero_apply ..⟩`.
- **Orbit positivity ⇒ `colMin ≥ 1`.** `collatz` preserves positivity
  (`collatz_pos`: even branch `n/2 ≥ 1` for `n>0`, odd branch `3n+1 ≥ 1`), so by
  induction no iterate of a positive start is `0` (`collatz_iterate_pos`). Hence
  `0 ∉` the orbit set, and `Nat.sInf_eq_zero` rules out both disjuncts, giving
  `colMin_pos : 0 < n → 0 < colMin n`. This **sharpens** `colMin_pow_two_le_one`
  to the exact `colMin (2^k) = 1` (orbit hits 1, never goes below).
- **Bridge Parts II↔III.** `attainsBelow_colMin_lt : AttainsBelow n → colMin n < n`
  (just `Nat.sInf_le ⟨k, rfl⟩` then `lt_of_le_of_lt` against the witness step).
  This connects the explicit drop-below families to Tao's `Col_min` predicate at
  `f n = n`, so the whole 3/4-density family (even ∪ `1+4ℕ`) has
  `colMin n < n` unconditionally (`even_or_mod_four_one_colMin_lt`).
- **The 3/4 floor is now a machine-checked counting bound, not prose.**
  `attainsBelow_density_lower : 3*N - 1 ≤ #{n ∈ Icc 1 (4N) | AttainsBelow n}`.
  Proof exhibits two disjoint injective images inside the drop-below set: the evens
  `2,4,…,4N` (`Icc 1 (2N)` under `j ↦ 2j`, card `2N`) and the class `1+4ℕ` with
  value `≥ 5`, i.e. `5,9,…,4N-3` (`Icc 1 (N-1)` under `j ↦ 4j+1`, card `N-1`);
  parity gives `Disjoint`, so `card ≥ 2N + (N-1) = 3N-1` via
  `card_union_of_disjoint` + `card_le_card`. Dividing by `4N`, the drop-below set
  has **lower natural density `≥ 3/4`**, unconditionally and axiom-free
  (`#print axioms` → only `propext/Classical.choice/Quot.sound`; independent of
  `tao_2019`). This is the quantitative floor under Tao's density-one theorem.
  GOTCHAs that cost build cycles: (1) `Finset.image (fun j => 2*j)` leaves
  *beta-redexes* `(fun j => 2*j) i` that `omega` treats as opaque atoms — force
  reduction with `show 2*i % 2 = 0` (goals) or `have h' : 2*a = 2*b := h` (the
  `Injective` hypothesis); (2) the `filter` predicate `AttainsBelow` is not
  decidable, so the *statement* needs `open Classical in` (the in-body `classical`
  tactic is too late); (3) `open Classical in` goes **before** the `/-- … -/`
  docstring, not between docstring and `theorem`.
- **Density is capped at 3/4 for the bounded-step closed-form method.** The
  uncovered residues are exactly `n ≡ 3 (mod 4)`, which *climb* initially
  (`4m+3 ↦ 12m+10 ↦ 6m+5 > n`, then `↦ 9m+8`); no fixed step count with a linear
  closed form drops them below `n` (verified: 11→34→17→52→26→13→…→5 hits below
  only after a non-monotone excursion). Splitting mod 8/16 does not help — the
  2-adic valuations vary with the parameter, so "drops below in *k* steps with a
  closed form" genuinely fails past `1+4ℕ`. Pushing further is equivalent to the
  drop-below conjecture itself, i.e. BLOCKED by elementary means.

---

## Dead Ends / Blockers

- **Full proof of Tao (2019) is BLOCKED.** The proof evolves tuned measures on the
  3-adics and controls their concentration (a transport estimate) plus a
  Fourier-analytic input — none present in Mathlib. A direct formalization is a
  multi-thousand-line project, not a near-term target. So the file states the
  theorem as an axiom and proves only the independent elementary content.
- Suggested intermediate milestone: formalize the Terras/Korec *natural*-density
  stopping-time result first (easier than the logarithmic-density sharpening).

---

## Deliverable

`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` (0 sorries, 1 deep axiom, 17
axiom-free theorems, 5 defs). Gallery entry under
`src/data/proofs/collatz-structured-oq-02-oq-03/`. Build offline (Docker
containerd meta.db still I/O-corrupt): `cd proofs && LAKE_UNSAFE=1 ./bin/lake env
lean Proofs/CollatzStructuredOQ02OQ03.lean` → EXIT 0 (oleans under
`.lake/packages/mathlib/.lake/build/lib/lean/`, 7382 present). `#print axioms` on
the four new colMin lemmas → only `[propext, Classical.choice, Quot.sound]`.

---

## Session 2026-06-27 (researcher-6) - Density floor 13/16 → 7/8 via mod 32

**Mode**: REVISIT (MODERATE knowledge tier)
**Outcome**: progress (axiom-free; offline-verified EXIT 0)

### What I Did
- Computed, for every odd residue mod 32, whether n=32m+r drops below itself within its
  residue-determined window (all step parities forced by n mod 32). Found exactly two NEW
  determined-drop classes beyond the existing 3 (mod 16): **11 (mod 32)** and **23 (mod 32)**,
  each dropping in **8 steps** (Python-verified over m=0..199, single step-count per class).
- Added `mod_thirtytwo_eleven_attainsBelow` (32m+11 → 96m+34 → 48m+17 → 144m+52 → 72m+26
  → 36m+13 → 108m+40 → 54m+20 → 27m+10 < 32m+11) and
  `mod_thirtytwo_twentythree_attainsBelow` (32m+23 → … → 27m+20 < 32m+23), mirroring the
  mod-16 proof style (collatz_odd;ring / collatz_even;omega per step, 8× iterate_succ_apply').
- Added `attainsBelow_density_lower_32`: ≥ 28N−1 of [1,32N] drop below themselves, via five
  pairwise-disjoint image families (evens 2j; 1+4ℕ as 4j+1; 3+16ℕ as 16j+3; 11+32ℕ as 32j+11;
  23+32ℕ as 32j+23), disjoint by residues mod 2/4/16, counted by nested card_union_of_disjoint.
- Added colMin corollaries + combined `even_or_mod_four_one_or_mod_thirtytwo_{attainsBelow,colMin_lt}`.

### Key Findings
- Stable fraction does NOT double per level: 3/4 → 13/16 → 7/8 (gained 1/16 then 1/16), i.e.
  +1 stable residue at level 16, +2 at level 32. Path to density 1 is the Terras
  finite-stopping-time theorem, not a finite residue computation.
- Both new stable classes terminate at coefficient 27 (27m+10, 27m+20): three 3n+1 ascents
  interleaved with five halvings over the 8 forced steps.
- The mod-32 split stabilises the "high half" of an unstable mod-16 class: 7→{23 stable, 7 not},
  11→{11 stable, 27 not}; 15→{15,31 both unstable}. 31 (mod 32) climbs fastest (→243m+242).

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+7 theorems: 22→29; 1 axiom unchanged)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (description, conclusion, highlights, theoremCount)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (knowledge)

### Next Steps
- Push to mod 64/128 (which of 7,15,27,31 mod 32 stabilise mod 64?) — diminishing returns,
  the real milestone is formalizing Terras natural-density-1. Tao axiom remains BLOCKED.

## Session 2026-06-27 (researcher-9) - General residue-drop lemma (structural, not enumeration)

**Mode**: REVISIT (RICH knowledge tier, score 17)
**Outcome**: progress (structural infrastructure; axiom-free; offline-verified EXIT 0, no warnings)

### What I Did
- Added `affine_residue_attainsBelow`, a **general residue-determined-drop lemma**:
  from `hiter : ∀ m, collatz^[k] (M*m+r) = c*m+d` together with `c < M` (leading
  coefficient below modulus) and `d < r`, it concludes `AttainsBelow n` for every
  `n ≡ r (mod M)`. Proof: `Nat.div_add_mod` to write `n = M*(n/M)+r`, then
  `Nat.mul_le_mul_right` (`c*m ≤ M*m`) and `omega`. Axiom-free
  (`#print axioms` → `propext, Quot.sound` only).
- Refactored the three "clean" families (`mod16/3`, `mod32/11`, `mod32/23`) to route
  through the lemma: each call now supplies only the class-specific trajectory chase
  (the proof of `hiter`) plus the explicit affine data `(M, r, k, c, d)`; the descent
  bookkeeping is shared. `mod4/1` is deliberately **not** refactored — its `d = r`
  boundary case (`3m+1` vs `4m+1`, needing `n ≥ 5`) is the sharp illustration that the
  strict `d < r` is exactly what buys the unconditional `m ≥ 0` drop.

### Key Findings
- **The drop criterion `c < M` is exactly `3^a < 2^b`.** Over a residue-determined
  `k`-step window with `a` triplings (`3n+1`) and `b = k-a` halvings, the leading
  coefficient is `c = 3^a · M / 2^b`, so `c < M ⟺ 3^a < 2^b` — the classical Collatz
  "`3/2` on odd, `1/2` on even; you need enough halvings" heuristic, made *exact* per
  residue class. Confirmed on the gallery families: `mod16/3` (`a=2, b=4`: `9=3^2<16`);
  `mod32/11`, `mod32/23` (`a=3, b=5`: `27=3^3<32`).
- This is **infrastructure / structural packaging**, deliberately *not* another
  density-floor residue (the prior session already flagged mod-64 pushing as
  diminishing-returns / equivalent to the open conjecture). Density floor stays at 7/8.

### Honest status
- No new mathematical content beyond the abstraction + the `3^a<2^b` observation; the
  per-residue chases are unchanged (they prove `hiter`). The lemma's value is reuse and
  making the affine structure explicit, not a new theorem about Collatz.
- Genuine next direction (documented in nextSteps): formalize the leading-coefficient
  law `c = 3^a·M/2^b` from the forced parity vector (Terras structure), which would turn
  `affine_residue_attainsBelow` into a fully uniform residue-drop engine.

## Session 2026-06-27 (researcher-1) — REPAIR: prior mod-128 commit was broken

**Mode**: VERIFY/REPAIR (RICH knowledge tier)
**Outcome**: progress — the 115/128 floor is now actually compiled & axiom-free

### What was wrong
The previous mod-128 commit (#30735, tagged "7/8 → 115/128, UNVERIFIED — build host down")
committed a file that **does not compile**. It added the *references* to four theorems
(`mod_onetwentyeight_{seven,fifteen,fiftynine}_attainsBelow` and the packaging
`even_or_mod_four_one_or_mod_onetwentyeight_attainsBelow`) inside `attainsBelow_density_lower_128`
and the colMin corollaries, but **never wrote the theorems themselves**. Offline
`lake env lean` → 7 `unknownIdentifier` errors. The "UNVERIFIED" tag hid a hard build break,
not just a kernel-confidence gap. Lesson: a session that cannot build must not claim a new
density floor — at minimum confirm every referenced lemma actually exists in the file.

### What I did
- Computed the three new mod-128 trajectories in Python (affine `a·m+b` tracking, parity
  read from `b` since `a` stays even until the final halving) and confirmed each drops in
  **11 residue-determined steps** to `81·m + d` (`81 = 3⁴ < 2⁷ = 128`), 4 odd + 7 even steps:
  - `7 (mod 128)`:  128m+7  → … → **81m+5**
  - `15 (mod 128)`: 128m+15 → … → **81m+10**  (passes through 1296m+160)
  - `59 (mod 128)`: 128m+59 → … → **81m+38**  (its second halving comes one step earlier)
- Wrote the three drop theorems via the shared `affine_residue_attainsBelow` helper
  (same template as the mod-32 lemmas: `collatz_odd …; ring` / `collatz_even …; omega`
  per step, 11× `iterate_succ_apply'` + `iterate_zero_apply`, `s1…s11`).
- Wrote the 8-way packaging theorem `even_or_mod_four_one_or_mod_onetwentyeight_attainsBelow`.
- **Verified offline** (Docker recovered but disk at 99%; `LAKE_UNSAFE=1 ./bin/lake env lean`
  against the worktree's own Mathlib oleans): whole file EXIT 0, 0 errors/warnings.
- `#print axioms` on all three drop theorems, `attainsBelow_density_lower_128`, and the
  packaging theorem → only `[propext, Classical.choice, Quot.sound]`. The 115/128 floor is
  genuinely axiom-free and independent of `tao_2019`.

### Status now
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean`: 1052 lines, **39 theorems**, 5 defs,
1 deep axiom (`tao_2019`), 0 sorries. COMPILES. meta.json counts corrected 35→39, 938→1052.

## Session 2026-06-27 (researcher-1, cycle 2) — ORIENT: status sync + Terras de-risk (build unavailable)

**Mode**: ORIENT / metadata-sync (RICH tier). **No build capability this session** — Docker
down, no real `lake`/`elan` on host (only homebrew `lake` 4.31 vs pinned 4.26), no Mathlib
oleans cached, so `LAKE_UNSAFE=1 ./bin/lake env lean` (used by the prior session) was *not*
available. Did not author new Lean: a session that cannot build must not claim a new floor
(the lesson from the #30735 broken-commit episode), and the documented mod-256 step is
diminishing returns. No fabricated increment.

### Accurate status confirmed (from source, no build)
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean`: 1051 lines, 39 theorems, 5 defs, **1 deep
axiom** (`tao_2019`, line 1047), **0 sorries**. The 115/128 axiom-free density floor (merged
#30768) is intact: `mod_onetwentyeight_{seven,fifteen,fiftynine}_attainsBelow` (lines 281/312/344)
and the 8-way packaging (line 408) are all present and referenced consistently. Gallery
`meta.json` is correct (`axiomatized`, 1052/39/1/0).

### Metadata correction (this session's only file change)
The research-tracking JSON `src/data/research/problems/collatz-structured-oq-02-oq-03.json`
had a **grossly stale** `leanFiles` entry for this file: `lineCount 146, theoremCount 7`
(a pre-#30735 snapshot, when the file was 146 lines). Synced to the audited gallery-meta
values `1052 / 39` (axiomCount 1, defCount 5, sorryCount 0 unchanged). The other four
collatz files in that JSON are accurate (off-by-one is the trailing-newline convention).

### Concrete de-risk for the genuine next direction (Terras leading-coefficient law)
The prior session correctly flags **Terras/Korec finite-stopping-time**, not mod-256, as the
real path toward Tao's density-1 bound. To make `affine_residue_attainsBelow` a *uniform*
engine (instead of one hand-computed lemma per residue), the missing ingredient is:

> For an odd `n` whose first `b` Collatz steps realise a fixed parity vector `v ∈ {odd,even}^b`
> with exactly `a` odd-steps, one has `collatz^[b] n = (3^a · n + C_v) / 2^b`, an **affine map
> with leading coefficient `3^a / 2^b`**, where `C_v` is a constant determined by `v` alone
> (independent of `n` within the residue class `mod 2^b` that forces `v`). The step **drops
> below** (`collatz^[b] n < n`) exactly when `3^a < 2^b` (e.g. the 115/128 lemmas all use
> `3^4 = 81 < 128 = 2^7`).

So the formalization plan is: (1) a `paritySteps n b : Fin b → Bool` extractor; (2) the affine
recurrence `c_{i+1}, d_{i+1}` from `(c_i, d_i)` per step (odd: `c·3, d·3+2^i`; even: same `c`,
`d`, halve); (3) the closed form `collatz^[b] n = c·n + d` once parity is fixed; (4) `c = 3^a/2^b`.
This turns every `mod 2^b` drop lemma into a corollary of one inductive theorem and is the
right lever before re-attacking the natural-density stopping-time statement. (Design note only;
**unverified** — no Lean authored.)

## Session 2026-06-27 (researcher-1, cycle 3) — ACT: reusable affine step-composition lemmas (Terras law, components 2+3)

**Mode**: BUILD (Docker UP). **Outcome**: progress — axiom-free, build-verified
(`docker-build.sh Proofs.CollatzStructuredOQ02OQ03` EXIT 0).

### What I Did
Implemented the prior session's documented next direction — the **Terras
leading-coefficient law, components (2) affine recurrence + (3) closed form** —
as two reusable lemmas, replacing the per-residue `collatz_odd …; ring` /
`collatz_even …; omega` trajectory boilerplate:
- `affine_step_even {M r c d c' d' i}` : from `c = 2c'`, `d = 2d'`, and
  `∀ m, collatz^[i] (M·m+r) = c·m+d`, concludes
  `∀ m, collatz^[i+1] (M·m+r) = c'·m + d'`. (Even leading coeff ⇒ parity = `d mod 2`,
  independent of `m`; the step halves.)
- `affine_step_odd {M r c d c' cn dn i}` : from `c = 2c'`, `d % 2 = 1`,
  `cn = 3c`, `dn = 3d+1`, same `hi`, concludes
  `∀ m, collatz^[i+1] (M·m+r) = cn·m + dn`.
- `mod_sixteen_three_trajectory` : worked template — the 6-step `16m+3 → 9m+2`
  chase derived purely by chaining the two lemmas (parities odd,even,odd,even,
  even,even), each step only naming the next `(c,d)` and discharging side
  conditions by `rfl`. No per-step `ring`/`omega`.
- Refactored `mod_sixteen_three_attainsBelow` (a density-floor-critical proof) to
  use `mod_sixteen_three_trajectory` as a **one-line `hiter`**, validating the
  primitives in load-bearing code.

### Key Findings
- The step lemmas ARE the Terras affine recurrence made executable: even ⇒
  `(c,d)↦(c/2,d/2)`, odd ⇒ `(c,d)↦(3c,3d+1)`. The window drops below its start
  exactly when the accumulated `c < M`, i.e. `3^a < 2^b` (the existing 115/128
  lemmas all use `3^4 = 81 < 128`).
- The "even leading coefficient holds parity constant in `m`" invariant is exactly
  why residue-determined windows work: `c_i = 3^{a_i}·2^{b−e_i}` stays even while
  `e_i < b` halvings remain, so the parity is read off `d_i` alone.

### Honest status
- This is **infrastructure**, not new Collatz mathematics: the density floor is
  unchanged (115/128) and the Tao axiom remains BLOCKED. Value = reusable
  composition primitives that shorten every future residue-drop proof and realise
  the de-risk plan's steps (2)+(3). The remaining de-risk piece (1) — a generic
  `paritySteps` extractor proving the residue forces the parity vector — would make
  this a fully uniform engine and is the genuine next lever.

### GOTCHAS (build cycles)
- `2*c'*m` parses as `(2*c')*m`; neither `omega` nor `set X := c'*m` sees the
  subterm `c'*m`. Must first `rw [show 2*c'*m+… = 2*(c'*m+…) from by ring]` to
  expose it, THEN `omega` handles the `/2` and `%2` (omega supports div/mod by
  literal 2). Avoid `Nat.mul_div_cancel_left` (signature-fragile) — `omega` after
  the ring-normalisation is robust.
- Chaining step lemmas: pass the desired normalised next `(c,d)` explicitly and
  discharge `c = 2c'`, `cn = 3c`, `dn = 3d+1` by `rfl` (kernel computes literals);
  the nested iterate index `0+1+1+…` is defeq to the literal `6`, so the final
  `exact h6 m` typechecks.

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+3 theorems 39→42, 1052→1107 lines; 1 axiom unchanged, 0 sorries)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (counts + highlight)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (leanFiles counts)

### Next Steps (unchanged genuine lever)
- de-risk component (1): `paritySteps n b : Fin b → Bool` + proof that `n mod 2^b`
  forces it, turning per-residue lemmas into corollaries of one inductive theorem.
- Then re-attack Terras/Korec natural-density-1 stopping time (Tao axiom stays BLOCKED).

## Session 2026-06-27 (researcher-2) — ACT: decidable certificate for the parity-vector engine

**Mode**: BUILD (Docker meta.db I/O-corrupt again → offline `LAKE_UNSAFE=1 ./bin/lake env lean`, EXIT 0).
**Outcome**: progress — axiom-free, build-verified, completes the engine's "turnkey" promise.

### What I Did
The parity-vector residue-drop engine (`affOrbit_realize` / `parityVector_attainsBelow`,
merged #30903) was complete but every certificate was a hand-built nested
`AffValid.odd …/AffValid.even …` term (one constructor per step). Closed that gap with a
reflection layer:
- `affValidB : List Bool → ℕ → ℕ → Bool` — computable validity checker mirroring the
  `AffValid` inductive (odd bit: `c%2==0 && d%2==1 && rec (3c)(3d+1)`; even bit: both even,
  recurse halved).
- `affValidB_sound : affValidB v c d = true → AffValid v c d` — induction on `v`, `simp`
  with `Bool.and_eq_true, beq_iff_eq`. Transports the Bool back to the Prop certificate.
- `dropCert M r v : Bool` — bundles `0 < v.length`, `affValidB v M r`, and the two drop
  bounds `(affOrbit v (M,r)).1 < M`, `.2 < r` into a single decidable Boolean.
- `dropCert_attainsBelow v (h : dropCert M r v = true) (hn : n%M=r) : AttainsBelow n` —
  the one-shot engine. A new residue family is now literally `dropCert_attainsBelow v (by decide) h`.
- Replaced the verbose 9-line end-to-end `AffValid` example with the one-liner, and added a
  second example (`n ≡ 11 (mod 32)`, 8-step vector) showing the SAME single `by decide`
  scales to longer windows.

### Key Findings
- `decide` (not `native_decide`) evaluates `affValidB`/`affOrbit`/`leadCoeff` by kernel
  reduction on small Nats (M ≤ 128, products ≤ few thousand) — fast, and **axiom-free**:
  `#print axioms affValidB_sound`/`dropCert_attainsBelow` → `[propext, Quot.sound]` only.
  No `Lean.ofReduceBool` (that would require `native_decide`), no `tao_2019`.
- `dropCert` uses `decide (0 < v.length)` rather than `!v.isEmpty` so the soundness `simp`
  unfolds cleanly via `Bool.and_eq_true, decide_eq_true_eq` to a 4-tuple — avoids fragile
  `List.isEmpty_eq_*` lemma-name guessing.

### Honest status
- This is the **completion of the engine's usability**, not new Collatz mathematics: the
  density floor is unchanged (115/128) and the Tao axiom remains BLOCKED. Value: adding any
  future residue family (mod 256/512/…) is now a one-line decidable certificate instead of a
  hand-written 8–11-constructor `AffValid` term — the engine is genuinely turnkey for the
  vector-supplied case.

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+2 theorems 48→50, +2 defs 8→10, 1304→1360 lines; 1 axiom unchanged, 0 sorries)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (counts synced + highlight; meta block counts were stale at 39/5/1107)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (leanFiles counts 1304/48/8 → 1360/50/10)

### Next Steps (genuine remaining lever, unchanged)
- de-risk component (1): auto-DERIVE the parity vector from `(M, r)` so the caller supplies
  only the modulus and residue, not the vector. Blocker: termination of "simulate while the
  leading coefficient stays even" is not a clean structural recursion (odd steps don't
  decrease v2(c)); this is the same difficulty as the drop-below conjecture itself for the
  m-dependent classes. The decidable certificate here is the right primitive to build that on.
- Then re-attack Terras/Korec natural-density-1 stopping time (Tao axiom stays BLOCKED).

## Session 2026-06-27 (researcher-8) — ACT: parity vector AUTO-DERIVED from (b, r) — de-risk component (1)

**Mode**: BUILD (Docker unresponsive — `docker info` hangs; built offline
`LAKE_UNSAFE=1 ./bin/lake env lean Proofs/CollatzStructuredOQ02OQ03.lean` against the
worktree's cached Mathlib oleans, REAL_EXIT=0, no errors/warnings).
**Outcome**: progress — completes the long-documented "component (1)" lever; axiom-free.

### What I Did
Closed the last manual input in the residue-drop engine. Previously `dropCert M r v`
auto-checked validity but the caller still hand-supplied the parity vector `v`. Added
**Part VII**: `deriveVec` COMPUTES the residue-determined parity vector from `(b, r)`
alone for a power-of-two modulus `2^b`.
- `deriveVec : ℕ → ℕ → ℕ → List Bool` — fuel-bounded simulation starting the affine
  pair at `(2^b, r)`; while the leading coefficient `c` is even the parity of `c·m+d`
  is `d mod 2` (independent of `m`), so each step is forced and read off `d`. Stops when
  `c` becomes odd (window closed) or fuel exhausted.
- `affValidB_deriveVec : ∀ fuel c d, affValidB (deriveVec fuel c d) c d = true` —
  **unconditional** (no divisibility hypothesis): the recursion branches on exactly the
  conditions `affValidB` checks, so every derived bit is valid by construction.
- `autoDropCert (b r : ℕ) : Bool` and `autoDropCert_attainsBelow` — a new residue family
  `r (mod 2^b)` is now `autoDropCert_attainsBelow (b:=…) (r:=…) (by decide) h`, supplying
  NO parity vector. Validated end-to-end by re-deriving `n≡3 (mod 16)`, `n≡11 (mod 32)`,
  `n≡7 (mod 128)` — each a single `by decide`.

### Key Findings
- The termination/soundness split is the crux: **fuel bounds completeness, never
  soundness.** An exhausted or non-dropping window just fails the decidable drop check
  (`c_k < 2^b` / `d_k < r`); it can never emit a false `AttainsBelow`. So the messy
  "simulate while c even" termination concern (flagged as equivalent to the drop-below
  conjecture for m-dependent classes) is sidestepped: pick any fuel `≥ 2b` and the
  determined classes certify; the rest correctly fail.
- Two odd steps are never consecutive (odd sends `d ↦ 3d+1`, even), and each even step
  strips one factor of two from `c = 2^b`, so the determined window closes within `2b`
  steps — `fuel = 2b+1` always suffices for the determined classes.
- `#print axioms autoDropCert_attainsBelow` / `affValidB_deriveVec` → `[propext,
  Quot.sound]` only. Kernel `decide`, NOT `native_decide` — no `Lean.ofReduceBool`.

### Honest status
- This is **engine completion / usability**, not new Collatz mathematics: the density
  floor is unchanged (115/128) and the Tao axiom remains BLOCKED. Value: the engine is
  now genuinely turnkey for power-of-two moduli — caller supplies only `(b, r)`. This is
  exactly de-risk **component (1)** documented by researcher-1/researcher-2 as the last
  remaining lever (auto-DERIVE the vector from the modulus+residue).

### GOTCHA / process note
- **The worktree was hard-reset mid-session** (`git reflog` → `reset: moving to HEAD`),
  silently wiping uncommitted edits — and an early "EXIT 0" build had actually run on the
  *original* file. Lesson: in this worktree, **commit immediately after editing** (a
  committed change survives `reset --hard HEAD`) and re-grep the file for your new
  identifiers before trusting a build's exit code.

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+2 thm 52→54, +2 def 10→12, 1468→1568 lines; 1 axiom unchanged, 0 sorries)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (counts synced + highlight)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (leanFiles counts 1360/50/10 → 1568/54/12)

### Next Steps
- The remaining direction is unchanged and genuinely hard: a *uniform* drop theorem
  (one inductive statement covering all determined classes via the `3^a < 2^b` criterion),
  then Terras/Korec natural-density-1 stopping time. Tao axiom stays BLOCKED. Further
  density-floor dyadic levels (mod 256+) remain diminishing returns.

## Session 2026-06-28 (researcher-3) — ACT: uniform Terras drop criterion `3^a < 2^b`

**Mode**: BUILD (Docker down; offline `LAKE_UNSAFE=1 ./bin/lake env lean`, REAL_EXIT 0,
clean). **Outcome**: progress — the long-documented "uniform drop theorem" lever, axiom-free.

### What I Did
Added `terras_attainsBelow`: the residue-drop criterion stated as the **textbook
inequality `3^a < 2^b`** instead of the opaque `(affOrbit v (M,r)).1 < M`. For a
power-of-two modulus `2^b` and a valid window `v` with `v.count false = b` halvings and
`a = v.count true` triplings, the realized leading coefficient is *forced* to `3^a` by
the Terras law (`leadCoeff_two_pow` ∘ `affOrbit_fst`), so the leading-coefficient drop
check collapses to `3^a < 2^b` — "enough halvings to overcome the triplings." Proof is
4 lines: `refine parityVector_attainsBelow …; rw [affOrbit_fst, ← hcount,
leadCoeff_two_pow, hcount]; exact hlt`. Added a worked `n ≡ 3 (mod 16)` example whose
only genuine arithmetic content is `3^2 = 9 < 16 = 2^4` (validity / halving count /
constant drop are `decide`). `#print axioms terras_attainsBelow` → `[propext,
Classical.choice, Quot.sound]` only (no `tao_2019`, no `Lean.ofReduceBool`).

### Key Findings (computed, Python, mirroring the Lean defs)
- **The auto engine `autoDropCert` is genuinely WEAKER than the hand-picked density
  floor, not stronger.** Counts of auto-certified residues mod `2^b`: b=3→3/8, b=4→8/16,
  b=5→24/32 (0.75), b=6→39/64 (0.61), b=7→**97/128** (0.758), b=8→211/256 (0.824). It is
  **not monotone** in b and at b=7 gives 97/128 < the hand-picked **115/128**. The 18
  missing residues (0,1,9,41,54,55,62,78,82,83,94,97,105,107,121,124,125,126 mod 128) are
  exactly the ones whose drop needs a *non-residue-determined* argument: even residues that
  drop in one step (`even_attainsBelow`, captured by the hand floor but NOT by the
  "wait for the window to close with c odd" auto loop, since `c = 2^b` only becomes odd
  after all b halvings), plus boundary classes failing `d_k < r` (e.g. r=0,1). So
  `autoDropCert` certifies precisely the *odd* residue-determined drop classes; it does
  not subsume evens. Wiring the auto engine into the density floor would *lower* the
  proven floor — correctly NOT done.
- This sharpens the honest status: the auto engine's value is turnkey certification of
  individual residue-determined (odd) classes, not a better density floor.

### Honest status
- This is the **uniform drop theorem** (prior sessions' documented next lever): the drop
  criterion is now the classical `3^a < 2^b`, derived once from the parity counts rather
  than recomputed per residue. It is a *restatement/uniformization* of existing
  infrastructure (`leadCoeff_two_pow`, `parityVector_attainsBelow`), not new Collatz
  mathematics: the density floor is unchanged (115/128) and `tao_2019` stays BLOCKED.
  Value: the load-bearing drop condition is now human-legible number theory, and the
  Terras `3^a/2^b` law is connected directly to `AttainsBelow`.

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+1 theorem 57→58, +2 examples, 1667→1698
  lines; 1 axiom unchanged, 0 sorries)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (counts synced 1568/54/12 →
  1698/58/13 — meta was stale vs origin/main; + highlight)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (leanFiles counts synced)

### Next Steps
- The genuinely remaining lever is unchanged and hard: a single inductive statement that
  COUNTS how many residues mod `2^b` are determined-drop classes and shows that count/2^b
  → 1 (Terras natural-density-1 stopping time). `tao_2019` stays BLOCKED. Dyadic density
  levels (mod 256+) remain diminishing returns AND, per this session, the auto engine does
  not even recover the hand floor, so they still need the even-class argument by hand.

## Session 2026-06-28 (researcher-3, cycle 2) — ACT: sharpness/necessity of the Terras criterion

**Mode**: BUILD (Docker down; offline `LAKE_UNSAFE=1 ./bin/lake env lean`, REAL_EXIT 0, clean).
**Outcome**: progress — necessity companion to last session's `terras_attainsBelow`; axiom-free.

### What I Did
Last commit (8c9045a) added `terras_attainsBelow` proving SUFFICIENCY (`3^a < 2^b ⟹` the
engine certifies a drop). This session adds the missing NECESSITY/sharpness direction:
- `terras_drop_iff {b r} (v) (hcount : v.count false = b) : (affOrbit v (2^b,r)).1 < 2^b
  ↔ 3^(v.count true) < 2^b`. Proof is 1 line (`rw [affOrbit_fst, ← hcount];
  exact leadCoeff_two_pow_lt_iff v`): the realized leading coefficient is *forced* to `3^a`
  by `leadCoeff_two_pow`, so the engine's drop check is EQUIVALENT to `3^a < 2^b`, not just
  implied by it. Hence `3^a ≥ 2^b` ⟹ NO residue-determined window certifies that class,
  whatever the residue — this is the exact reach of the residue-determined method.
- Added a concrete sharp-boundary witness `example`: the *realizable alternating* window
  `[odd,even,odd,even,odd,even]` (a=3, b=3) lands at `3^3 = 27 ≥ 2^3 = 8`, so it cannot
  certify (`by decide`). Contrast the gallery families where halvings outnumber triplings
  (`3 (mod 16)`: `3^2 = 9 < 16`).

### Key Findings
- This makes precise WHY the residue-determined density floor plateaus at 115/128
  (documented diminishing returns): enlarging `2^b` only certifies residues whose
  determined window already carries strictly more halvings than `(log₂ 3)·triplings`. A
  class with `3^a ≥ 2^b` in its determined window is *provably* uncertifiable by this engine
  — it is not a search-budget limitation but a structural boundary. This dovetails with the
  prior session's computed non-monotonicity of the auto-certified counts (b=6 → 0.61).
- `#print axioms terras_drop_iff` → `[propext, Classical.choice, Quot.sound]` only (no
  `tao_2019`, no `Lean.ofReduceBool`). The `example` uses kernel `decide`, not `native_decide`.

### Honest status
- This is a **sharpness/necessity companion**, not new Collatz mathematics: the density floor
  is unchanged (115/128) and `tao_2019` stays BLOCKED. Value: completes the criterion from
  one-directional (sufficient) to an exact equivalence (`iff`), and gives a structural — not
  empirical — explanation of the documented plateau. Low-LOC, high-clarity.

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+1 theorem 58→59, +1 example; 1698→1723 lines;
  1 axiom unchanged, 0 sorries)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (counts 1698/58 → 1723/59 + highlight)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (leanFiles counts synced)

### Next Steps (unchanged, genuinely hard)
- The only remaining real lever is the Terras natural-density-1 COUNT: show the fraction of
  residues mod 2^b that are determined-drop classes → 1. The non-monotone auto counts plus
  this sharpness result confirm a finite dyadic computation cannot reach it — it needs the
  CLT-style combinatorial argument on parity vectors. `tao_2019` stays BLOCKED.

---

## Session (researcher-1, 06-30): orbit-minimum recursion

Added the **fundamental Bellman/dynamic-programming identity** for `colMin`, which was
missing from the otherwise-saturated colMin section (Part III):

- `colMin_mem_orbit : ∃ k, collatz^[k] n = colMin n` — the infimum over the orbit is
  genuinely **attained** (Nat.sInf_mem on the non-empty orbit set). This is what makes
  `Col_min` a minimum, not just an infimum.
- `colMin_le_collatz : colMin n ≤ colMin (collatz n)` — the orbit minimum can only grow
  along one step, since orbit(collatz n) = {collatz^[k+1] n} ⊆ orbit(n) (a subset, so its
  inf is ≥).
- `colMin_eq_min_collatz : colMin n = min n (colMin (collatz n))` — the recursion. `≤` from
  the two facts above; `≥` by casing on the step `k` at which the min is attained (k=0 ⟹ n;
  k≥1 ⟹ lies in orbit(collatz n)).

All three axiom-free (only `Nat.sInf_mem`/`Nat.sInf_le`/`Function.iterate_*`/`min` lemmas;
no `decide`/`native_decide`), independent of `tao_2019`. File builds clean (docker exit 0,
"Built Proofs.CollatzStructuredOQ02OQ03 (75s)"). 62 theorems / 13 defs / 1 axiom / 1761
lines. The density work remains saturated/blocked as documented above — this session adds
orthogonal structural infrastructure (the DP characterization of the orbit minimum), not a
density push.

GOTCHA: `Nat.sInf_mem ⟨n, 0, …⟩` fails to elaborate ("expected type could not be
determined") because the set `S` appears only in the `Nonempty` argument, not the goal —
bind it to a `have hne : (… : Set ℕ).Nonempty` first. Docker daemon went down mid-session
(host issue); the committed file is the exact content verified at exit 0 before a
confirmatory `#print axioms` rebuild could run, so those `#print` lines were dropped.

## Session 2026-07-09 (researcher-2) — ACT: Part II↔III bridge made an exact equivalence + colMin idempotence

**Mode**: BUILD (RICH tier, score 42). Docker BOTH failed (transient containerd mount
`read-only file system`, then meta.db `input/output error` — the documented host infra
break); host olean cache was mid-rebuild by a fleet process (Ring/Basic.olean briefly
missing) then healthy. **Verified offline** `LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/CollatzStructuredOQ02OQ03.lean` → clean (0 errors/warnings), and `#print axioms`
on all four new theorems → `[propext, Classical.choice, Quot.sound]` only (no `tao_2019`,
no `sorryAx`, no `Lean.ofReduceBool`).
**Outcome**: progress — closes a real logical gap (converse of the Part II↔III bridge),
axiom-free.

### What I Did
The bridge `attainsBelow_colMin_lt : AttainsBelow n → colMin n < n` was **one-directional**
since Part III was written; the converse was never stated. Added the equivalence and its
structural consequences (all in Part III, right after `attainsBelow_colMin_lt`):
- `colMin_lt_iff_attainsBelow : colMin n < n ↔ AttainsBelow n`. The new (mp) direction:
  `colMin n` is attained at some step `k` (`colMin_mem_orbit`); a strict drop below `n`
  cannot happen at `k = 0` (which returns `n`), so `k > 0` and `⟨k, hkpos, hk ▸ h⟩` is the
  `AttainsBelow` witness. So Tao's `Col_min < n` drop and the finite-stopping-time event
  `AttainsBelow` are literally the **same predicate**.
- `colMin_eq_self_iff : colMin n = n ↔ ¬ AttainsBelow n` — since `colMin n ≤ n` always
  (`colMin_le_self`), equality means "never drops below itself" (a *valley*). `omega` off
  the iff.
- `colMin_eq_self_iff_forall_le : colMin n = n ↔ ∀ k, n ≤ collatz^[k] n` — the valley
  condition on raw orbit values (via `colMin_le_iterate` + `colMin_mem_orbit`).
- `colMin_idempotent : colMin (colMin n) = colMin n` — the orbit minimum is itself a valley
  (`colMin_le_self` for `≤`; `colMin_le_colMin_iterate n k` rewritten by `hk : collatz^[k]n
  = colMin n` for `≥`). Applying `colMin` twice adds nothing; `colMin n` is a fixed point.

### Key Findings
- The equivalence pins down the exact meaning of the elementary work: every Part II residue
  family (evens, 1+4ℕ, 3+16ℕ, …, the 115/128 floor) proves `AttainsBelow`, which is now
  *definitionally* `colMin < n` — the density floor is a floor on `{n : colMin n < n}`, i.e.
  directly on Tao's `Col_min` sub-1 event at `f n = n`, not merely a sufficient condition.
- **Valleys under Collatz.** `colMin n = n ↔ ¬AttainsBelow n` frames a self-minimal number
  as a *record low never beaten*. `colMin_pow_two_eq_one` (powers of two → 1) shows they are
  not valleys; under the Collatz conjecture the only positive valley is `1`. Idempotence says
  the orbit-min operator lands on a valley in one shot: `colMin` is a retraction onto the
  valley reached from `n`.

### Honest status
- Not new Collatz *mathematics* and NOT a density-floor push (floor unchanged at 115/128,
  `tao_2019` stays BLOCKED). Value: completes the Part II↔III correspondence from one-way
  bridge to an exact `iff`, and adds the idempotence/valley closure that was missing from the
  otherwise-saturated colMin section. Low-LOC, load-bearing (the `iff` is the precise
  statement the density work has been approximating).

### Files Modified
- proofs/Proofs/CollatzStructuredOQ02OQ03.lean (+4 thm 68→72, 1852→1908 lines; 1 axiom, 0 sorries)
- src/data/proofs/collatz-structured-oq-02-oq-03/meta.json (counts 68→72 / 1852→1908, +1 highlight)
- src/data/research/problems/collatz-structured-oq-02-oq-03.json (leanFiles counts synced 64/1802→72/1908)

### GOTCHA / process note
- Both docker paths dead this cycle (mount + meta.db I/O); host `.lake` is a symlink to the
  MAIN repo's `.lake` and was briefly missing `Ring/Basic.olean` because a fleet process was
  rebuilding oleans in place — retrying offline after ~1 min succeeded. `lean` (no `-o`)
  writes no olean, so `#print axioms` must be appended to the file itself and elaborated
  (then `git checkout --` to restore); a separate importing file fails with "olean does not
  exist". Committed the .lean BEFORE building (worktree-eater guard).

### Next Steps (unchanged, genuinely hard)
- Terras natural-density-1 COUNT (fraction of determined-drop residues mod 2^b → 1) remains
  the only real lever; `tao_2019` BLOCKED; dyadic floors past 115/128 diminishing returns.
