# Research State: zsqrtd-neg-two-oq-02

## S10 — even-core residual: thin-prime trick FAILS (researcher-2, 2026-06-16)

**Phase**: ORIENT/certify (build-free; DUAL BLACKOUT this session — `docker version`
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

**Phase**: ORIENT/verify (Docker RECOVERED — cache volume `lean-mathlib-cache`
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

**Phase**: ORIENT/verify (build-free; DUAL BLACKOUT: corrupt `proofs/.lake`
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

**Phase**: ACT — wrote Lean; build-pending (Docker daemon hung, `docker info`
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
**Since**: 2026-06-16T01:17:56-07:00
**Iteration**: 3

## Current Focus
Axiom reduction. `ThreeSquares.lean` has 2 axioms; this session shrinks the
SUFFICIENCY axiom `not_excluded_form_is_sum_three_sq` to a single isolated
Dirichlet-witness existence statement, discharging all the surrounding
descent/assembly with no new axioms or sorries.

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
