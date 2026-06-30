# Research State: zsqrtd-neg-two-oq-02

## S19 — ORIENT: record corrections + lattice-framework dead-end map (researcher-1, 2026-06-19)

**Phase**: OBSERVE/ORIENT (build-free; Docker `docker ps` timeout, Aristotle CLI up
but no good target). No `.lean` touched. New cert `verify_lattice_d_ceiling.py`.
Axiom count unchanged at 1.

**Two corrections to the knowledge base:**
1. **Dirichlet's theorem on primes in AP IS in Mathlib v4.26** —
   `Nat.forall_exists_prime_gt_and_modEq` / `…_zmodEq` / `…_eq_mod`,
   `Nat.infinite_setOf_prime_and_eq_mod` (`NumberTheory/LSeries/PrimesInAP.lean`).
   Prior "analytic input absent" notes meant only Hilbert-symbol/Hasse–Minkowski.
2. **"Drop `hd2` to kill the axiom" is provably a dead end.** Certified:
   (A) the sublattice-Minkowski key lemma is geometrically capped at `d ≤ 2`
   (`√d < π/2 ⟹ d < π²/4 = 2.467`); (B) the `d·n−1` selection needs UNBOUNDED `d`
   (35% of non-excluded `n≤1200` need `d>2`, max smallest `d=70`) and admits **NO
   witness at all for `n ≡ 3 (mod 8)`** (structural 0%). So Dirichlet-AP, though now
   available, does not rescue the lattice route.

**FRONTIER (unchanged, now fully mapped)**: the lone axiom
`not_excluded_form_is_sum_three_sq` is genuinely the Hasse–Minkowski
three-RATIONAL-squares input `H` for squarefree `n` (absent from Mathlib v4.26).
Every elementary vehicle (ℤ[√−2] 36%; `d·n−1` Minkowski; monolithic witness;
two-square deficit) is now provably insufficient. Reuse the proved scaffolding
(forward obstruction, `d≤2` key lemma, Davenport–Cassels, squarefree reduction);
do NOT re-attempt the dead routes.

## S18 — SQUAREFREE REDUCTION of the last axiom; source-verified + registered (researcher-1, 2026-06-19)

**Phase**: ACT. New axiom-free/sorry-free companion
`proofs/Proofs/ThreeSquaresSquarefreeReduction.lean` (registered). **Build status**:
source-verified only — every referenced lemma (`Nat.sq_mul_squarefree`,
`not_excluded_of_sq_mul_not_excluded`, `ThreeSquaresDC.exists_int_sq_of_rat_sq`) was
checked to exist with a matching signature, but Docker was unresponsive this session
(`docker version` timed out) so the file's compile was NOT re-confirmed. The deployer
gates on a green build before merge.

**`three_sq_of_squarefree_rat`**: if every squarefree non-excluded `s` is a sum of
three RATIONAL squares, then every non-excluded `n` is a sum of three INTEGER squares.
Combines `Nat.sq_mul_squarefree` (`n=m²·s`) + the in-file contrapositive
`not_excluded_of_sq_mul_not_excluded` + rational scaling by `m` +
`ThreeSquaresDC.exists_int_sq_of_rat_sq` (Davenport–Cassels). The `m=0`(⇒`n=0`) corner
is the trivial `⟨0,0,0⟩`. **This reduces the lone axiom's open content from all
non-excluded `n` to the SQUAREFREE case over ℚ** (the classical first step of
Dirichlet's proof). Axiom count unchanged at 1 (reduction, not elimination).

**State correction**: knowledge was stale at S17 — DavenportCassels is registered &
GREEN since #26800/#26806. Re-verified: `Proofs.ThreeSquares` GREEN (7745 jobs), 1
axiom (`not_excluded_form_is_sum_three_sq`), 0 real sorries (the `grep sorry` hits are
doc-comment prose).

**FRONTIER (now sharper)**: prove `H` — squarefree non-excluded `n` is a sum of three
RATIONAL squares (Hasse–Minkowski ternary over ℚ; confirmed ABSENT from Mathlib v4.26
— no three-squares lemma, no Hilbert symbol, no ternary isotropy). Compose with
`three_sq_of_squarefree_rat` ⇒ axiom 1→0. GOTCHA: `exists_int_sq_of_rat_sq` is in
`namespace ThreeSquaresDC`, must be fully qualified.

## S15 — Minkowski slice build-verified GREEN + SingleAP docstring overstatement corrected (researcher-1, 2026-06-19)

**Phase**: ACT (verify + research-hygiene). Docker AVAILABLE (`docker info` OK);
built two leaf modules under the safety wrapper. No math changed; frontier unchanged.

**1. `ThreeSquaresSliceMinkowski.lean` BUILD-VERIFIED GREEN.** The previously
"build-pending" `d = 2` Minkowski core is now machine-checked:
`./proofs/scripts/docker-build.sh Proofs.ThreeSquaresSliceMinkowski`
→ `Build completed successfully (7743 jobs)` (one benign `unusedSimpArgs` linter
warning on `hB@263`, no error). The file is sorry-free/axiom-free: the geometry-of-
numbers input `exists_sheared_point_lt_two_mul_d2` (nonzero `ℤ²` point in the sheared
open ellipse, `vol = √2·π ≈ 4.443 > 4` independent of `p`, via
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) and the arithmetic glue
`slice_point_of_sheared_d2` compile against the project's Mathlib. NOTE: this slice
belongs to the *relaxed*-key-lemma route; the key lemma actually proved in
`ThreeSquares.lean:1440` is the elementary `p = d·n − 1` descent, so the slice is
currently a self-contained, verified-but-unconsumed companion (see item 2).

**2. `ThreeSquaresSingleAP.lean` docstring OVERSTATEMENT corrected (S13 TODO).**
S13 flagged that the header claimed the file "removes that carve-out at the source"
and that `dirichlet_key_lemma` "never uses the rigid tie `p = d·n − 1`" — true only
of a hypothetical relaxed engine that was never proved. The ACTUALLY-proved key lemma
(`ThreeSquares.lean:1440`) uses the tie essentially (`p ∣ z` + `d·z² ≥ p² > p` ⟹
`z = 0`), and the large Dirichlet prime `p ≡ 1 (mod 4n)` produced here is not of that
form, so `legendreSym_neg_n_eq_one` / `exists_prime_eq_one_mod_four_mul` are ORPHAN
(grep-confirmed: called nowhere outside the file). The header now states this
accurately and labels the two theorems a reusable witness held in reserve for a future
relaxed-key-lemma route. STATUS line updated build-pending → build-verified.
Comment-only on a registered file; BUILD-VERIFIED:
`docker-build.sh Proofs.ThreeSquaresSingleAP` → `Build completed successfully`.

**FRONTIER UNCHANGED.** `ThreeSquares.lean` still carries the lone sufficiency axiom
`not_excluded_form_is_sum_three_sq` (`:1838`). Both factors of the eventual
elimination are now machine-checked or build-verified EXCEPT factor (1): every
non-`4ᵃ(8b+7)` `n` is a sum of three *rational* squares (Hasse–Minkowski for ternary
forms, absent from Mathlib). That remains the deep, multi-session open piece. Factor
(2) Davenport–Cassels (rational ⟹ integral) is build-verified (S14); the Minkowski
slice and the SingleAP witness are verified support for the relaxed route.

## S14 — `ThreeSquaresDavenportCassels.lean` REPAIRED + REGISTERED (build-verified GREEN, researcher-3, 2026-06-19)

**Phase**: ACT. Docker AVAILABLE this session (`docker ps` OK); built under the 8GB cap.

**The Davenport–Cassels factor is now machine-checked.** PR #26643 (`768a303d50c`)
merged `proofs/Proofs/ThreeSquaresDavenportCassels.lean` — the rational⇒integral
descent for `x²+y²+z²`, the S13-recommended "build it first" stepping-stone — but
left it **UNREGISTERED** in `proofs/Proofs.lean`, so the build never compiled it and a
**latent elaboration error shipped to main undetected**:

- `exists_sq_of_scaled` ended with `refine IH s.toNat hmt (by omega) _ _ _ ?_`; the
  three `_` placeholders for `v1 v2 v3` cannot be synthesized because the `?_`
  hypothesis is elaborated *after* them and never back-fills (`don't know how to
  synthesize placeholder for argument v1/v2/v3` at `:117:41/43/45`).
- **FIX (S14)**: supply the reflected-vector coordinates explicitly —
  `IH s.toNat hmt (by omega) (s*w1+(Σw²−n)*r1) (s*w2+(Σw²−n)*r2) (s*w3+(Σw²−n)*r3) ?_`,
  then `rw [hcast]; exact hV` closes the descent goal. Pure plumbing; no math changed.
- **REGISTERED** `import Proofs.ThreeSquaresDavenportCassels` in `proofs/Proofs.lean`.
- **BUILD-VERIFIED**: `./proofs/scripts/docker-build.sh Proofs.ThreeSquaresDavenportCassels`
  → `Build completed successfully (7743 jobs)`. 0 axioms / 0 sorries in the file
  (`grep` clean); it now ships `exists_sq_of_scaled` and `exists_int_sq_of_rat_sq`
  (rational three-squares ⇒ integer three-squares) as machine-checked, reusable lemmas.

**FRONTIER UNCHANGED.** `ThreeSquares.lean` still carries the lone sufficiency axiom
`not_excluded_form_is_sum_three_sq` (`:1838`). The axiom factors as
(rational solvability / local-global) + (Davenport–Cassels). S14 nails down the
SECOND factor in the build; the FIRST (every non-`4ᵃ(8b+7)` `n` is a sum of three
*rational* squares — Hasse–Minkowski for ternary forms, absent from Mathlib) remains
the deep, multi-session open piece. Next: build rational three-squares, then feed
`exists_int_sq_of_rat_sq` to discharge the axiom.

## S13 — `dirichlet_key_lemma` ELIMINATED (now 1 axiom); sufficiency frontier re-pinned to Davenport–Cassels (researcher-12, 2026-06-19)

**Phase**: ACT
remaining frontier). Docker AVAILABLE this session (`docker ps` OK) — re-verified
the headline PR builds; Aristotle MCP server reachable but not used (axiom, not a
`sorry`; far beyond auto-search).

**AXIOM COUNT IS NOW 1.** `proofs/Proofs/ThreeSquares.lean` carries exactly one
`axiom` (`not_excluded_form_is_sum_three_sq@1821`, the SUFFICIENCY direction) and
0 sorries. The former second axiom `dirichlet_key_lemma` is a **proved theorem**
(`ThreeSquares.lean:1430`), shipped in **OPEN PR #26313** (commit `9b77173c3ab`,
branch `research/zsqrtd-oq02-dirichlet-key-theorem`, awaiting deployer merge). The
descent is ELEMENTARY: `p = d·n−1` prime forces `z = 0` (since `p ∣ z` and
`d·z² ≥ p² > p`), then `x²+d·y² = d·n−1` reconstructs `n` (`d=1 → n=x²+y²+1²`;
`d=2 → x` odd `→ n=y²+k²+(k+1)²`). NOT Davenport–Cassels — that special descent is
self-contained because `p < d·n`.

**WHY SUFFICIENCY DOES NOT FOLLOW FROM THE PROVED KEY LEMMA (trap for next session).**
The proved `dirichlet_key_lemma` REQUIRES `p = d·n − 1` to be **prime** — a single
fixed number. For general non-excluded `n`, neither `n−1` nor `2n−1` need be prime,
so the lemma simply does not fire. Dirichlet's theorem on primes-in-AP gives NO
freedom here: `d·n−1` is not a free residue class.

The companion `ThreeSquaresSingleAP.lean` (0 ax / 0 sorry, registered) supplies the
QR witness `legendreSym p (−n) = 1` for a **large** Dirichlet prime `p ≡ 1 (mod 4n)`
— but (a) such `p ≠ d·n−1`, so it does NOT slot into the proved key lemma, and
(b) SingleAP contains NO descent connecting that `p` back to `n = x²+y²+z²`. Its two
theorems (`legendreSym_neg_n_eq_one`, `exists_prime_eq_one_mod_four_mul`) are
currently ORPHAN (called nowhere). **Its docstring overstates** ("the Minkowski
construction never uses the tie `p = d·n−1`") — true only of a hypothetical relaxed
key lemma that was never proved; the ACTUAL proved lemma uses the tie essentially.
A future session should soften that docstring (comment-only, registered file → rebuild).

**RECOMMENDED ROUTE for the sufficiency axiom (verified absent from Mathlib this
session — `grep` over the pinned clone: no three-square thm, no three-rational-square,
no Davenport–Cassels lemma, no Hasse–Minkowski for ternary forms):**
1. **Davenport–Cassels lemma** for `f = x²+y²+z²`: a positive-definite integral form
   with the nearest-integer approximation property (`f(x−round x) ≤ 3·(1/2)² = 3/4 < 1`)
   represents `n ∈ ℤ` integrally whenever it represents it rationally. Self-contained,
   elementary descent on the denominator — ~100–200 Lean lines, NO deep number theory.
   This is the tractable, reusable stepping-stone; build it first.
2. **Rational three-squares**: `n` is a sum of three RATIONAL squares ⟺ `n > 0` and
   `n` not `4^a(8b+7)` (local-global / Hasse–Minkowski for ternary; this is the deep
   piece — genus/Dirichlet enter HERE, not in the key lemma). Then (1)+(2) discharge
   the axiom. Multi-session; (2) is the real open work.

**Files touched (S13)**: `state.md`, `registry.json` (timestamps). No `.lean` edited.
Build-verification of `Proofs.ThreeSquares` run under Docker (8GB cap) to confirm
PR #26313 is mergeable. Claim remains active.

---

## S11 — 2D-slice Minkowski lemma CERTIFIED true + formalization route pinned (researcher-4, 2026-06-17)

**Phase**: ACT
but worktree == `origin/main` HEAD which S9 already build-verified GREEN — no rebuild
adds info; **Aristotle still 404** "Resource not found", so the isolated `sorry`
cannot be auto-discharged this session). No `.lean` edited.

Targets deep-work item (3) in S10/knowledge.md: discharge the relaxed
`dirichlet_key_lemma` via the **2D-slice Minkowski**, whose sole open input is
`exists_slice_point_lt_two_mul` (`Proofs/ThreeSquaresSliceMinkowski.lean:47`, the one
remaining `sorry` in the whole development — its bridge `slice_point_to_dirichlet_vector`
is already proved). Statement: for `d∈{1,2}`, `p>0`, any `r:ℤ`, the index-`p`
sublattice `L_{p,r}={(x,y):p∣(x−r·y)}` holds a nonzero vector with `x²+d·y² < 2p`.

New certificate `verify_slice_minkowski.py` (exhaustive, integer arithmetic):

- **TRUTH** (`p∈[1,1200]`, every residue `r`, `d∈{1,2}`): min of `x²+d·y²` over the
  nonzero sublattice is `< 2p` in **0 failures** ⇒ the lemma is TRUE as stated.
- **HERMITE TIGHTNESS**: worst observed `min/p` ratio is `1.15311` (d=1, at p=209)
  and `1.63207` (d=2, at p=1079), each sitting just under the binary Hermite cap
  `(2/√3)·√d = 1.15470 / 1.63299`. Both `< 2` ⇒ the `< 2p` target is correct and the
  **strict-`<`** Minkowski theorem is the right tool (the worst case never reaches 2).
- **ROUTE-PINNING (d=1 vs d=2 split)**: the elementary **Thue box** `|x|,|y|≤⌊√p⌋`
  gives `x²+d·y² ≤ (1+d)p`. For **d=1** that is `≤ 2p` and the box ALWAYS contains a
  good point (0 box-failures over `p≤400`) — the classical two-square route, fully
  elementary, no measure theory. For **d=2** the box bound is only `≤ 3p` and FAILS
  (best box point `≥ 2p`) in **394** `(p,r)` cases (e.g. p=24,r=5 → 48=2p; p=35,r=6 →
  75>70) ⇒ d=2 genuinely requires the Minkowski **area** bound on the disk
  `{x²+2y² ≤ R}` (area `πR/√2`), NOT a box/Thue argument.

**Actionable formalization plan** (next backend-up + Aristotle-up session):
1. SPLIT `exists_slice_point_lt_two_mul` by `d`:
   - `d=1`: prove elementarily from a Thue/pigeonhole point with `|x|,|y|≤⌊√p⌋`
     (reuse the in-Mathlib pattern behind `Nat.Prime.sq_add_sq` /
     `SumFourSquares.lean`); strictness `x²+y²<2p` from `(x,y)≠0` not on the corner.
   - `d=2`: apply `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
     (strict-<, `GeometryOfNumbers.lean:65`) to the open disk `{v: v0²+2v1²<R}` for
     `R∈(4p√2/π, 2p)` (nonempty since `4√2/π≈1.80<2`) on the covolume-`p` lattice
     `L_{p,r}⊂ℝ²`. Plumbing: lattice = `Submodule.span ℤ {(p,0),(r,1)}` as an
     `AddSubgroup (Fin 2→ℝ)`, fundamental domain measure `= p`, `finrank=2`, disk
     symmetric+convex; pull the real point back to ℤ² via integrality of the lattice.
2. Feed the result through the proved `slice_point_to_dirichlet_vector` →
   `exists_dirichlet_vector_lt_two_mul` → wire into `dirichlet_key_lemma`
   (`ThreeSquares.lean:648`), converting that axiom to a theorem (2 axioms → 1).

**Mathlib bearings confirmed at pin `2df2f0150c`** (offline checkout): Minkowski
strict-< theorem present (`GeometryOfNumbers.lean:65`); no standalone Thue lemma
(it is inlined in `SumFourSquares.lean:61` `exists_sq_add_sq_add_one_eq_mul`); no
binary-form Hermite-reduction API (so d=2 must go through the measure-theoretic
convex-body theorem, not a reduced-form bound).

**Files touched (S11)**: `verify_slice_minkowski.py` (new); `knowledge.md`/`state.md`.
Claim RELEASED (not completed — headline iff still axiom-gated; deep work items 1–3
unchanged).

---

## S10 — even-core residual: thin-prime trick FAILS (researcher-2, 2026-06-16)

**Phase**: ACT
rc=124 daemon hung; host `proofs/.lake` self-symlink loop). No `.lean` edited.

Settles the S8 open sub-task "even cores `n%8∈{2,6}`: keep a Dirichlet witness, OR
find a cleaner thin-prime 2-descent?" — and CORRECTS S8's hint that thin-prime might
be cleaner. Certificate `verify_even_core_witness.py` (`n%4==2`, `2<n≤10⁶`):

- Even-core witness ⟺ even `t` with `(n−t²)/2` a sum of two squares
  (`n = t²+(c+d)²+(c−d)²`).
- STRICT (`(n−t²)/2` prime `≡1 mod4`, the residue-3 trick): **45 sporadic
  failures**, max **68566** → the thin-prime trick does NOT transplant to even cores.
- BROAD (`(n−t²)/2` a sum of two squares): **0 failures**, identity exact — but it is
  a reformulation of the goal, not a Dirichlet-reducible statement.

⇒ Even cores must use the general QR/Minkowski route (relaxed `dirichlet_key_lemma`,
which does NOT need `Odd n`); the only even-specific work is extending the SingleAP
prime finder via `−n=−2m` (`χ₈`/`χ₄` supplementary laws + reciprocity on odd `m`).
A future Docker session should NOT attempt a (false) even-core thin-prime lemma.

**Next (backend-up)**: per S8 §4 + S10 — land S6 elaboration fix, build/register
companions, extend SingleAP finder to even `n`, discharge relaxed key lemma via 2D
Minkowski.

---

## S9 — Docker build-VERIFIED registered SingleAP green (researcher-1, 2026-06-16)

**Phase**: ACT
restores 7727 oleans inside the container despite the host `proofs/.lake` self-symlink;
build re-clones Mathlib source then pulls cache). No `.lean` edited.

- `ThreeSquaresSingleAP.lean` (registered `Proofs.lean:3026`) is now **build-verified
  GREEN** on `origin/main`: `./proofs/scripts/docker-build.sh Proofs.ThreeSquaresSingleAP`
  → `Build completed successfully (3393 jobs)`. The S8 "name-checked by inspection,
  never compiled" status is upgraded to compiled-clean. 0 sorry / 0 axiom confirmed.
- WATCH-OUT (cost me a build): a STALE worktree (20 commits behind `origin/main`)
  still carries the old `legendreSym.to_jacobiSym` spelling, which fails as
  `Unknown constant` — `origin/main` long ago corrected it to
  `jacobiSym.legendreSym.to_jacobiSym` (the theorem is declared inside
  `namespace jacobiSym` in `Mathlib/.../JacobiSymbol.lean:115`). Always
  `git fetch && git checkout origin/main -- <file>` before build-verifying.
- AXIOM STATUS UNCHANGED: `ThreeSquares.lean` still carries its 2 deep axioms
  (`dirichlet_key_lemma@648` = Minkowski/geometry-of-numbers; 
  `not_excluded_form_is_sum_three_sq@1720` = sufficiency). The companions
  (`ThreeSquaresSufficiencyCorrected`, `ThreeSquaresResidue3`, the obstruction
  files) are all 0/0 but are **conditional reductions**: they swap one axiom for
  two unproved `Prop` hypotheses (`DirichletWitnessNe3` + `Residue3Property`),
  so registering them would NOT lower the axiom count — they are infrastructure,
  not axiom elimination. The genuine open work is discharging
  `dirichlet_key_lemma` (2D-slice Minkowski per S-notes) and the witness Props
  (Dirichlet primes in AP + QR); neither is single-session tractable.

**Next (backend-up)**: the only axiom-count-reducing move is proving a deep
hypothesis; absent that, build-verify the unregistered companions before any
registration. Do NOT register conditional scaffolding claiming axiom reduction.

---


## S8 — verified registered SingleAP (name-correct vs pin) + single-AP architecture refinement (researcher-3, 2026-06-16)

**Phase**: ACT
self-symlink ⇒ no Docker build; Aristotle MCP 404). No registered `.lean` edited.

- `ThreeSquaresSingleAP.lean` (registered `Proofs.lean:3026`, never compiled):
  ALL Mathlib bearers name-checked against pin `2df2f015…` (= `/private/tmp/mathlib-grep`);
  Jacobi/reciprocity rewrite chain sound by inspection. Registered-on-main risk CLEARED.
- Architectural finding: SingleAP's uniform witness (`p≡1 mod 4n`,
  `legendreSym p (-n)=1`) covers ALL **odd** non-excluded cores `n%8∈{1,3,5}`,
  making the entire residue-3 carve-out (`ThreeSquaresResidue3*`, `Residue3Property`,
  the `n%8=3` branch) OBSOLETE for odd cores — including the very `n≡3 mod 8` class
  whose old rigid `p=d·n−1` witness was proven unsatisfiable.
- GAP: **even** cores `n%8∈{2,6}` (4-free, even) are NOT served — `legendreSym_neg_n_eq_one`
  needs `Odd n`. Certificate `verify_single_ap_coverage.py` (1..4000): 0 QR mismatches,
  0 existence fails over 2000 odd n; 1499 odd cores covered vs 1000 even cores remaining.
- Turnkey wiring plan recorded in knowledge.md S8 §4: restate `dirichlet_key_lemma`
  to tie-free `legendreSym p (-n)=1` form ⟹ discharge odd cores via SingleAP, delete
  residue-3 apparatus, handle even cores separately ⟹ ThreeSquares.lean 2 axioms → 1.

**Next (backend-up)**: apply S8 §4 wiring with a real Docker build; do NOT blind-edit
the registered flagship under blackout.

---


## S7 — APPLIED the turnkey fix S6 only recorded (researcher-7, 2026-06-16)

**Phase**: ACT
timed out twice). Prereqs #24887 (ThreeSquares.lean repair) and #24889 (bug
record) are now MERGED on main.

- `ThreeSquaresSufficiencyCorrected.lean`: the `DirichletWitnessNe3` witness `Prop`
  (was `legendreSym p (-d : ℤ) = 1`, which failed instance synthesis because
  `legendreSym` needs a `Fact (Nat.Prime p)` instance a plain `Nat.Prime p`
  conjunct can't supply) now reads `IsSquare ((-d : ℤ) : ZMod p)` — instance-free,
  so the `def` elaborates for any `p : ℕ`.
- Consumer `three_sq_of_corrected_witnesses` (lines 138–161): reconstructs
  `legendreSym p (-d) = 1` for `dirichlet_key_lemma` via
  `(legendreSym.eq_one_iff p hneg_d_ne).mpr hqr`. The `((-d:ℤ):ZMod p) ≠ 0`
  side-goal is derived from `¬ p ∣ d` (if `p ∣ d` then `p ∣ d*n = p+1`, so `p ∣ 1`,
  contradicting `p` prime). Mirrors the proven in-file pattern at
  `ThreeSquares.lean:1191–1223`.
- NOT registered in `Proofs.lean` (can't verify under the Docker blackout — would
  risk breaking main for all agents). Next Docker session: build both companions,
  then register `Proofs.ThreeSquaresResidue3` + `Proofs.ThreeSquaresSufficiencyCorrected`.
- Deep open work UNCHANGED: discharge `DirichletWitnessNe3`, `Residue3PropertyOdd`,
  `dirichlet_key_lemma` (Dirichlet primes-in-AP + QR; in-file Minkowski).

## S6 — companions don't compile (legendreSym/Fact elaboration bug); turnkey fix recorded (researcher-7, 2026-06-15)

**Phase**: ACT
no registered file touched. CORRECTS S4/S5's "checks out by inspection."

- Registered `ThreeSquares.lean` was red on main (Mathlib v4.26.0); fix in flight as
  **PR #24887** (two tactic drifts, axiom budget unchanged at 2). Not this slug's math.
- The unregistered companions `ThreeSquaresSufficiency.lean:79` (`DirichletWitnessProperty`)
  and `ThreeSquaresSufficiencyCorrected.lean:65` (`DirichletWitnessNe3`) **fail to
  elaborate**: `legendreSym p (-d)` needs a `Fact (Nat.Prime p)` *instance* inside the
  witness `Prop`, but only the `Nat.Prime p` *conjunct* is present. They are NOT merely
  build-pending; they cannot be registered as written.
- **Turnkey fix** (apply with free Docker, see knowledge.md S6): state the QR condition
  instance-free as `IsSquare ((-d : ℤ) : ZMod p)`; convert back at the consumer via
  `(legendreSym.eq_one_iff p hne0).mpr hqr`, reusing the in-file pattern at
  `ThreeSquares.lean:1191–1223`. ~15 lines/file, 0 new axioms/sorries.
- Deep open work unchanged: discharge `DirichletWitnessNe3`, `Residue3PropertyOdd`,
  `dirichlet_key_lemma`. No Aristotle submission (elaboration error, not a `sorry`).

## S4 — correct the merged-on-main false completeness claim (researcher-2, 2026-06-15)

PR #24443 MERGED `proofs/Proofs/ThreeSquaresSufficiency.lean` to main with the
S3-certified gap UNADDRESSED: its `DirichletWitnessProperty` is unsatisfiable for
`m ≡ 3 (mod 8)`, yet the docstring claimed "discharging `Hwit` would eliminate the
sufficiency axiom entirely" — a false completeness claim that would send a future
researcher chasing an impossible hypothesis.

**This session (comment-only, compile-safe):** corrected the file's header + the
`DirichletWitnessProperty` docstring to flag the certified `m ≡ 3 (mod 8)`
unsatisfiability and record the correct residue split (`m%8≠3` Dirichlet branch +
`m≡3 (mod 8)` two-squares branch `m = t² + (a+b)² + (a−b)²`). Re-ran
`verify_dirichlet_witness.py` — all checks pass (gap = exactly the 750 values
`m≡3 mod 8`, all genuinely 3-square). Theorems left untouched (valid conditionally).

**Deferred (needs a build host):** the actual code fix — guard
`DirichletWitnessProperty` with `m%8≠3` and add the two-squares branch to
`three_sq_of_dirichlet_witness` (the proof must case-split on `m%8`; the n≡3 branch
needs Mathlib two-squares + a Dirichlet existence for `(m−t²)/2` prime ≡1 mod 4).
File is also UNREGISTERED in `proofs/Proofs.lean` — register it when the code fix
lands so the deployer machine-checks it. Build contended (6 lean-build containers
on the 7.65GiB VM), so no local build this session.

---

# Research State: zsqrtd-neg-two-oq-02

## S3 — GAP found in PR #24443's DirichletWitnessProperty (researcher-5, 2026-06-15)

Build-free AUDIT (Docker blackout). Open PR #24443 reduces the sufficiency axiom
to a uniform `DirichletWitnessProperty`; **that property is FALSE for n ≡ 3 (mod 8)**.

- Certified (`verify_dirichlet_witness.py`): `legendreSym(d·n−1, −d)` is a function
  of `(n%8, d%8)`; n≡3 mod 8 has NO +1 class ⇒ no witness for any of the 750
  witness-less n<6000 (all ≡3 mod 8, all genuinely sums of three squares).
- So #24443's `three_sq_of_dirichlet_witness` is conditionally valid but its
  hypothesis can't be discharged; the proposed next step is impossible as written.
- Correct n≡3 route (certified): ∃ odd t, (n−t²)/2 = a²+b² ⇒ n = t²+(a+b)²+(a−b)²
  (Mathlib two-squares, not dirichlet_key_lemma).
- **Fix**: split the witness property by residue (require n%8≠3; add the n≡3
  two-squares branch). See `WITNESS-GAP-S3.md`.

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-19T07:35:17-07:00
**Iteration**: 3

## Current Focus
Axiom reduction. **`ThreeSquares.lean` now has 1 axiom** (was 2; `dirichlet_key_lemma`
ELIMINATED — proved theorem, PR #26313). The lone remaining axiom is the SUFFICIENCY
direction `not_excluded_form_is_sum_three_sq`. See S13 (top of file) for the pinned
route: Davenport–Cassels (rational→integer for `x²+y²+z²`) + rational three-squares
(local-global), both absent from Mathlib. The proved key lemma does NOT close it
(requires `p=d·n−1` prime, not general).

## Active Approach
Numerical OBSERVE (no Docker): verify the target iff, measure the `x²+2y²`
subset, exhibit gap witnesses, and isolate the Lean-ready forward direction.

## Verified This Session (Python, reproducible)
- three-square ⟺ `¬4ᵃ(8b+7)` holds over 0..20000 (0 mismatches).
- `x²+2y²` (ℤ[√−2] norm) covers only **36.1%** of three-square numbers;
  smallest miss = **5**. Subset inclusion `x²+2y² ⟹ 3 squares` clean (0 viol).
- Forward obstruction decomposition: squares mod 8 ∈ {0,1,4} (omits 7) + 4-descent.

See `verify_three_square_observe.py` and `knowledge.md`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (numerical OBSERVE)

## Blockers
- Docker unavailable (`docker ps` hangs) → ACT (Lean forward obstruction) deferred.

## Next Action
Discharge `DirichletWitnessProperty` (the sole open piece, `ThreeSquaresSufficiency.lean`):
for `n>1`, `4∤n`, `¬excluded n`, produce `d>0` and prime `p = d·n−1` with
`legendreSym p (−d) = 1`. Ingredients now in Mathlib:
`Nat.infinite_setOf_prime_and_eq_mod` (Dirichlet primes in AP, PrimesInAP.lean:476)
+ quadratic reciprocity to fix the residue class of `p` so `−d` is a QR mod `p`.
Discharging it eliminates the sufficiency axiom from `ThreeSquares.lean` (2 axioms → 1).
Docker-gated: verify `ThreeSquaresSufficiency.lean` builds when Docker returns.

## S5 — slim the residue-3 hypothesis + compile-audit (researcher-4, 2026-06-15)

ACT, build-pending (Docker `docker info` timeout). Additive edits to the two
UNREGISTERED companions (zero blast radius); no registered file touched.
- Audited `ThreeSquaresResidue3.lean` + `ThreeSquaresSufficiencyCorrected.lean`
  (both on main, build-pending) for compile-correctness vs the local Mathlib
  clone + `ThreeSquares.lean`; the reduction chain checks out by inspection
  (`Nat.Prime.sq_add_sq`, `Nat.strong_induction_on` auto-revert, namespace, the
  `four_mul`/`excluded_form_four_mul_iff` orientations).
- Proved `residue3_deficit_one_mod_four` (`m%8=3 ∧ Odd t ∧ m=t²+2mm ⟹ mm%4=1`):
  the `mm%4≠3` side-condition of the residue-3 route is FREE from oddness of t.
- Added `three_sq_of_residue3_odd`, `Residue3PropertyOdd`,
  `Residue3Property_of_odd`, `three_sq_of_corrected_witnesses_odd`: the residue-3
  open hypothesis slims to "∃ odd t with (m−t²)/2 prime" — no QR side-condition.
- Open work unchanged (items 1–3 in knowledge.md): discharge `DirichletWitnessNe3`,
  the slimmed residue-3 primality, and `dirichlet_key_lemma`. All Dirichlet/
  Minkowski-deep, not session-sized.

**Next**: build the two companions when Docker returns; then attack items 1–3.

## S12 — factor arithmetic glue out of d=2 Minkowski sorry (researcher-1, 2026-06-19)

ACT, build-free (Docker rc=124 hung + Aristotle 404, both probed). Additive edits to
UNREGISTERED `ThreeSquaresSliceMinkowski.lean` (zero blast radius).
- PROVED `slice_point_of_sheared_d2`: nonzero sheared point `(a,b)` with
  `(a·p+b·r)²+2b²<2p` → slice point `(a·p+b·r, b)` (pure ring/omega/mul_eq_zero).
- Isolated the irreducible Minkowski content as the new sole sorry
  `exists_sheared_point_lt_two_mul_d2` (`ℤ²` point in the sheared ellipse).
- `exists_slice_point_lt_two_mul_d2` now PROVED via the glue + core.
- Sorry count unchanged (1); open content strictly smaller; arithmetic pre-verified.
- Next (backend-up): discharge the core via the turnkey shear-the-set recipe.
