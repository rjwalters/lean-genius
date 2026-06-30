# Knowledge Base: nth-root-irrational-oq-01-oq-01

**Title**: Algebraic irrationality of roots of cyclotomic polynomials and their subfields
**Phase**: COMPLETED
**Status**: VERIFIED (2026-06-15, S2/researcher-5 — all 5 files Docker-GREEN)

---

## Problem Understanding

The parent `nth-root-irrational-oq-01` (`NthRootIrrationalOQ01.lean`) proved the
structural principle: *a root of an irreducible polynomial of degree ≥ 2 over ℚ
is irrational*, and applied it to `X^n − p` via Eisenstein. This OQ asks to
extend that principle to **cyclotomic polynomials** Φ_n and their roots (the
primitive n-th roots of unity), and to their subfields.

---

## Result (this session, 2026-06-15, Session 1, FRESH → ACT)

New file `proofs/Proofs/NthRootIrrationalOQ01OQ01.lean` (0 sorries, 0 axioms,
build-pending — both backends down at authoring time). Reuses the parent's
already-proven "irreducible deg ≥ 2 ⇒ no rational root" core (re-proved inline,
verbatim, to keep the file independent of cross-file build state).

1. `totient_ge_two` — `3 ≤ n → 2 ≤ Nat.totient n`. Proof: `Nat.totient_pos`
   (positivity) + `Nat.totient_eq_one_iff` (`φ n = 1 ↔ n = 1 ∨ n = 2`) ⇒ omega.
2. `cyclotomic_no_rational_root` — for `n ≥ 3`, `Φ_n` (over ℚ) has **no rational
   root**. Proof: `cyclotomic.irreducible_rat` + `natDegree_cyclotomic` (= φ(n))
   + `totient_ge_two` feed the inline core.
3. `rational_root_of_unity_le_two` — if `r : ℚ` is a primitive `n`-th root of
   unity (`0 < n`) then `n ≤ 2`. **The only rational roots of unity are ±1.**
   Proof: `IsPrimitiveRoot.isRoot_cyclotomic` gives `r` a root of `Φ_n`,
   contradicting (2) when `n ≥ 3`.
4. `primitiveRoot_not_rational` — a **complex** primitive `n`-th root of unity
   (`n ≥ 3`) is not in `Set.range (algebraMap ℚ ℂ)`; i.e. it is irrational.
   Proof: descend `ζ = algebraMap r` to `r : ℚ` via
   `IsPrimitiveRoot.of_map_of_injective` + `(algebraMap ℚ ℂ).injective`, then (3).
5. `primitiveCubeRoot_not_rational` — concrete instance `e^{2πi/3}` via
   `Complex.isPrimitiveRoot_exp 3`.

Numerically pre-verified (sympy): φ(n) ≥ 2 for all 3 ≤ n ≤ 200; deg Φ_n = φ(n);
Φ_n has no rational roots for n = 3,4,5,6.

---

## Insights

- The whole extension is "swap `X^n − p` (Eisenstein) for `Φ_n`
  (`cyclotomic.irreducible_rat`)" in the parent's irreducibility-⇒-irrational
  pipeline. The only genuinely new lemma is the degree lower bound
  `φ(n) ≥ 2 ⇔ n ≥ 3`.
- `Φ_n` has **no real roots** for n ≥ 3 (Φ_3 = X²+X+1, Φ_4 = X²+1, …), so the
  honest content lives in ℂ (not-rational) and in the rational-roots-of-unity =
  ±1 corollary — not in any "irrational real root" statement (which is vacuous).

## Mathlib gaps

- None for the rational/complex statements. The real **subfield** story
  (degree of `2cos(2π/n)` = φ(n)/2, irrational for n ≥ 5 except 6) was NOT
  formalized this session — `minpoly` of `2cos` is the missing piece; deferred
  as a follow-up OQ (would need the maximal-real-subfield minimal polynomial).

## Next steps / fragile points if CI fails

- `Nat.totient_eq_one_iff` (name) — fallback: prove φ(n) ≥ 2 via the two
  distinct coprime witnesses `1` and `n−1` in `Finset.range n`.
- `Nat.totient_pos.mpr` assumes the iff form (current Mathlib v4.26). If the
  one-directional form is in scope, drop `.mpr`.
- `IsPrimitiveRoot.of_map_of_injective` (Part IV) — assumes the bundled
  `MonoidHomClass` form so `algebraMap ℚ ℂ` unifies directly. Fallback: descend
  via `map_cyclotomic n (algebraMap ℚ ℂ)` + `eval_map`/`aeval` + `map_eq_zero_iff`
  injective, landing on `cyclotomic_no_rational_root` directly.
- `Complex.isPrimitiveRoot_exp` arg form `2 * ↑Real.pi * Complex.I / (n : ℕ)` —
  the concrete instance matches the `↑(3:ℕ)` denominator exactly.
- Register in `proofs/Proofs.lean` and `docker-build.sh Proofs.NthRootIrrationalOQ01OQ01`
  once a backend is available (left UNREGISTERED to protect auto-merge).

## Follow-up OQ (after SOLVED)

- Maximal real subfield: is `2cos(2π/n)` irrational for n ≥ 5 (n ≠ 6), via its
  degree-`φ(n)/2` minimal polynomial? (Genuinely distinct: needs the real
  cyclotomic subfield minpoly, absent above.)

## Dead ends

- "Irrational real root of Φ_n" — vacuous; Φ_n has no real roots for n ≥ 3.

---

## Result (Session 2, 2026-06-15, REVISIT → ACT) — real subfield SOLVED

New file `proofs/Proofs/NthRootIrrationalOQ01OQ01Real.lean` (0 sorries, 0 axioms,
build-pending — Docker/Aristotle blackout at authoring). Separate file to avoid
colliding with the still-open S1 PR #24349 (`NthRootIrrationalOQ01OQ01.lean`).

Closes the "maximal real subfield" follow-up the S1 notes flagged as a Mathlib
gap. **The gap was illusory.** S1 thought we'd need the minimal polynomial *of*
`2cos(2π/n)` (absent in Mathlib). Instead the degree argument runs the other way
and needs nothing new:

1. `trace_not_rational` — for `ζ : ℂ` a primitive `n`-th root of unity with
   `φ(n) ≥ 3`, `ζ + ζ⁻¹ = 2·cos(2π/n) ∉ Set.range (algebraMap ℚ ℂ)`
   (i.e. irrational). **Proof:** if `ζ + ζ⁻¹ = r ∈ ℚ`, clear by `ζ` to get
   `ζ² − r·ζ + 1 = 0`, so `ζ` is a root of the *rational* quadratic
   `q = X² − C r·X + 1`. Then `minpoly ℚ ζ ∣ q` (`minpoly.dvd`), so
   `deg(minpoly ℚ ζ) ≤ deg q = 2` (`natDegree_le_of_dvd`). But
   `minpoly ℚ ζ = Φ_n` (`Polynomial.cyclotomic_eq_minpoly_rat`), of degree
   `φ(n) ≥ 3` (`natDegree_cyclotomic`) — contradiction by `omega`.
2. `fifthRoot_trace_not_rational` — concrete `n = 5`: `2·cos(2π/5) = (√5−1)/2`
   is irrational (`φ(5) = 4`), via `Complex.isPrimitiveRoot_exp 5`.

### Key insight

The honest content of the real subfield is captured WITHOUT building any
"minpoly of cos" machinery: the *trace* `ζ + ζ⁻¹` being rational forces `ζ` to
satisfy a degree-2 rational polynomial, contradicting `deg Φ_n = φ(n) ≥ 3`. The
sharp bound is `φ(n) ≥ 3` (⇔ `n ∉ {1,2,3,4,6}`), matching Niven's theorem: the
only rational values of `2·cos(2π/n)` are `{2, −2, −1, 0, 1}`.

### Mathlib lemmas used (all name-checked vs leanprover-community/mathlib4 master)

- `Polynomial.cyclotomic_eq_minpoly_rat` (RingTheory/Polynomial/Cyclotomic/Roots.lean:178)
- `Polynomial.natDegree_cyclotomic`, `minpoly.dvd` (FieldTheory/Minpoly/Field.lean:72;
  args `(A) (x)` explicit), `Polynomial.natDegree_le_of_dvd`
  (Algebra/Polynomial/Degree/Domain.lean:61), `Nat.totient_pos` (iff form).

### Fragile points if CI fails

- `by decide` for `3 ≤ Nat.totient 5` — fallback `rw [Nat.totient_prime (by norm_num)]`.
- `compute_degree!` for `q.natDegree = 2` — fallback: prove `q.Monic` (`monicity!`)
  for `q ≠ 0` and use `≤ 2` from `compute_degree`.
- `rw [hr]` where `hr : algebraMap ℚ ℂ r = ζ + ζ⁻¹` after `simp` emits
  `aeval_C` — if the coercion forms diverge, replace `rw [hr]; linear_combination -hmul`
  with `linear_combination (-ζ) * hr - hmul` (no rewrite).
- Register `Proofs.NthRootIrrationalOQ01OQ01Real` in `proofs/Proofs.lean` once a
  backend is available (left UNREGISTERED to protect auto-merge).

### Next follow-up (still genuinely open)

- The *exact degree* `[ℚ(ζ+ζ⁻¹):ℚ] = φ(n)/2` (not just `> 1`) — would need the
  minimal polynomial of the real generator, still absent in Mathlib.

---

## Result (Session 4, 2026-06-15, researcher-4, REVISIT → ACT) — rational half of Niven (classification completed)

New file `proofs/Proofs/NthRootIrrationalOQ01OQ01CosRational.lean` (0 sorries, 0
axioms, build-pending — Docker `docker info` times out, Aristotle 404; both re-probed).
Branch built from origin/main so the sibling Cos/Real files are present.

The S2/S3 work (merged: #24403 real subfield, #24427 `cos_two_pi_div_n_irrational`)
proved the **irrational** direction `φ(n) ≥ 3 ⟹ Irrational(cos(2π/n))`, sharp at
`φ(n) ≤ 2 ⇔ n ∈ {1,2,3,4,6}`. This session adds the **complementary rational
direction**, so the two files together give the full Niven classification:

> `cos(2π/n)` is rational  ⟺  `n ∈ {1, 2, 3, 4, 6}`,  values `1, −1, −1/2, 0, 1/2`.

Theorems (each an elementary special-angle evaluation):
- `cos_two_pi_div_one_rational` — `cos(2π) = 1` (`Real.cos_two_pi`).
- `cos_two_pi_div_two_rational` — `cos π = −1` (`Real.cos_pi`).
- `cos_two_pi_div_three_rational` — `cos(π−π/3) = −cos(π/3) = −1/2`
  (`Real.cos_pi_sub` + `Real.cos_pi_div_three`).
- `cos_two_pi_div_four_rational` — `cos(π/2) = 0` (`Real.cos_pi_div_two`).
- `cos_two_pi_div_six_rational` — `cos(π/3) = 1/2` (`Real.cos_pi_div_three`).
- `cos_two_pi_div_rational_of_mem` — bundled over `n ∈ {1,2,3,4,6}` via `rcases … rfl`.

Reusable pattern: `not_irrational_of_eq_rat (q : ℚ) (h : x = (q:ℝ)) : ¬Irrational x`
(`rw [h]; exact q.not_irrational`); angle identity `2π/k = <std angle>` by
`push_cast; ring`; final rational-cast equality by `norm_num`.

### Mathlib lemmas name-checked vs sibling v4.26 (`/Users/rwalters/GitHub/mathlib4`)
`Real.cos_two_pi` (Trig/Basic.lean:224), `Real.cos_pi` (:216), `Real.cos_pi_sub`
(:331), `Real.cos_pi_div_two` (:133), `Real.cos_pi_div_three` (:775),
`Rat.not_irrational` (NumberTheory/Real/Irrational.lean:197), `not_irrational_one`
(:99), `not_irrational_zero` (:98).

### Still genuinely open (unchanged)
- The *exact degree* `[ℚ(ζ+ζ⁻¹):ℚ] = φ(n)/2` (not just `> 1`): IntermediateField
  tower `φ(n) = [ℚ(ζ):ℚ] = [ℚ(ζ):ℚ(ζ+ζ⁻¹)]·[ℚ(ζ+ζ⁻¹):ℚ] = 2·(φ(n)/2)`. Needs the
  real-subfield minpoly / adjoin-tower machinery; Docker-gated, ~150 LOC.

---

## Session 5 (2026-06-15, researcher-5) — REGISTER the four completed files

**Mode:** ACT (registration-only, build-free). Docker + Aristotle blackout
(`docker info` timed out). All four S1–S4 files were merged to `main` but left
UNREGISTERED in `proofs/Proofs.lean` (no open PR was registering them):
`NthRootIrrationalOQ01OQ01` (#24349), `...Real` (#24403), `...Cos` (#24427),
`...CosRational` (#24466). Each is 0 sorry / 0 axiom.

Added the four `import Proofs.NthRootIrrationalOQ01OQ01{,Cos,CosRational,Real}`
lines after the existing NthRoot imports (Proofs.lean:2633). Personally
name-checked each file before registering (per the blackout rule "grep-clean ≠
build-safe"): identifiers are standard v4.26 (`cyclotomic.irreducible_rat`,
`natDegree_cyclotomic`, `cyclotomic_eq_minpoly_rat`, `minpoly.dvd`,
`IsPrimitiveRoot.of_map_of_injective`, `Complex.exp_mul_I`, the special-angle
`Real.cos_*` lemmas, `Rat.not_irrational`). One-line-per-file change;
deployer-build-gated (a failing build blocks the merge, not main), so safe under
blackout. The genuinely-open exact-degree φ(n)/2 item above remains untouched.

---

## Session 6 (2026-06-15, researcher-1, REVISIT → ACT) — EXACT DEGREE φ(n)/2 SOLVED

**The sole remaining open item is closed.** New file
`proofs/Proofs/NthRootIrrationalOQ01OQ01Degree.lean` (0 sorries, 0 axioms,
build-pending — Docker `docker info` timed out; Aristotle blackout). Branch from
origin/main. Every Mathlib lemma name-checked against the pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (local clone HEAD matches exactly).

Every prior session (S1–S5) flagged the **exact degree**
`[ℚ(ζ+ζ⁻¹):ℚ] = φ(n)/2` as the lone open item, deferred as "needs
IntermediateField tower machinery, ~150 LOC, Docker-gated". This session proves
it (division-free to avoid `φ(n)/2` integrality fuss):

> **`finrank_adjoin_trace_eq`**: `3 ≤ n → 2 · [ℚ(ζ+ζ⁻¹):ℚ] = φ(n)`.

### Proof architecture (the machinery that finally worked)

1. `[ℚ(ζ):ℚ] = φ(n)` — `IntermediateField.adjoin.finrank hζint`
   (= `(minpoly ℚ ζ).natDegree`) + `cyclotomic_eq_minpoly_rat` +
   `natDegree_cyclotomic`. (Same as S2/Real.lean.)
2. Tower `ℚ ⊆ ℚ(ζ+ζ⁻¹) ⊆ ℚ(ζ)` via **`IntermediateField.finrank_bot_mul_relfinrank`**
   `(h : A ≤ B) : finrank F A * relfinrank A B = finrank F B`. This is THE clean
   tower lemma that stays inside `IntermediateField ℚ ℂ` (no scalar-tower
   instance hassle from nesting `IntermediateField (↥K) ℂ`).
3. `relfinrank ℚ(α) ℚ(ζ) = 2`:
   - `relfinrank_eq_finrank_of_le h` → `finrank ↥ℚ(α) (extendScalars h)`;
   - **`extendScalars_adjoin h : extendScalars h = adjoin K S`** (the KEY lemma,
     `IntermediateField/Adjoin/Defs.lean:433`) identifies `extendScalars h` with
     the *simple adjoin* `ℚ(α)⟮ζ⟯` because `ℚ(ζ) = adjoin ℚ {ζ}` definitionally;
   - `adjoin.finrank hζint` → `(minpoly ℚ(α) ζ).natDegree`;
   - `= 2` by `≤ 2` (ζ root of `X²−C αK·X+1` over ℚ(α), `minpoly.dvd` +
     `natDegree_le_of_dvd`) and `≠ 0,1` (`minpoly.natDegree_pos`; degree-1 ⇒
     `finrank_eq_one_iff` ⇒ `ℚ(α)⟮ζ⟯ = ⊥` ⇒ `mem_bot` ⇒ ζ ∈ ℚ(α), but ζ
     non-real).

### Reusable insights / fragile points

- **The relfinrank/extendScalars route beats `Module.finrank_mul_finrank`** for
  intermediate-field towers: `finrank_bot_mul_relfinrank` + `extendScalars_adjoin`
  + `adjoin.finrank` keeps everything over the *base* ℚ and over ↥K, dodging the
  `Algebra ℚ (↥(IntermediateField (↥K) ℂ))` transitive-instance minefield.
- **Real subfield**, manually built as `realField : IntermediateField ℚ ℂ` with
  carrier `{z | z.im = 0}`. Field-closure proofs: `Complex.mul_im`/`add_im`
  (im=0 preserved), `Complex.inv_im` (`z⁻¹.im = -z.im/normSq z`),
  `algebraMap_mem'` via `eq_ratCast` (`f q = ↑q` for any ℚ-ring-hom) +
  `Complex.ratCast_im` (`(↑q:ℂ).im = 0`, rfl). `mem_realField := Iff.rfl`.
- `ζ+ζ⁻¹` is real: `‖ζ‖=1` (`Complex.norm_eq_one_of_pow_eq_one`) ⇒
  `normSq ζ = 1` (`Complex.normSq_eq_norm_sq`, decl in `Analysis/Complex/Norm.lean:146`)
  ⇒ `(ζ+ζ⁻¹).im = ζ.im + (-ζ.im/1) = 0`.
- ζ **non-real** for n≥3: `ζ.im=0` ⇒ `ζ⁻¹=ζ` (via `Complex.inv_re/inv_im` +
  normSq=1) ⇒ `ζ²=1` ⇒ `n ∣ 2` (`IsPrimitiveRoot.dvd_of_pow_eq_one`) ⇒ n≤2 ⊥.
- ζ integral over ℚ: `(hζ.isIntegral hn0).tower_top` (`IsPrimitiveRoot.isIntegral`
  gives ℤ; `IsIntegral.tower_top` lifts ℤ→ℚ).
- `aeval ζ (X²−C αK·X+1) = 0` closes by `linear_combination -hmul`
  (`hmul : ζ⁻¹*ζ = 1`); `compute_degree!` for `natDegree = 2`.
- αK := `⟨α, mem_adjoin_simple_self ℚ α⟩`; `algebraMap ↥ℚ(α) ℂ αK = α := rfl`.

### Status / next
- Left UNREGISTERED in `proofs/Proofs.lean` (build unverifiable under blackout;
  register + `docker-build.sh Proofs.NthRootIrrationalOQ01OQ01Degree` once Docker
  returns). With this, the Niven cosine story for this OQ is COMPLETE: rational
  classification (n∈{1,2,3,4,6}), irrationality (φ(n)≥3), and now the **exact
  degree** φ(n)/2. No genuinely-open sub-item remains.

---

## Session 6 (2026-06-15, researcher-8) — exact real-subfield degree φ(n)/2 certified

**Mode:** REVISIT → ACT (verify-before-assert, build-free; Docker down,
`docker info` times out; no Aristotle). The slug is otherwise saturated: the four
S1–S4 files are merged and now registered in `proofs/Proofs.lean:2651–2656`. The
lone genuinely-open direction was the **exact** degree of the real-subfield
generator (the Real file proved only the degree-≤2 *bound* used for the
irrational direction, not the exact value). This session certifies the exact
degree symbolically and pins the Lean tower plan for the build-up session.

New artifact `verify_real_subfield_degree.py` (sympy; deterministic; all asserts
pass for `n = 1..30`):

- **(A) Quadratic relation.** `z² − (z + 1/z)·z + 1 = 0` as an algebraic identity
  (`z ≠ 0`), and concretely for `ζ = e^{2πi/n}`. This is the upper half of the
  tower: `ζ` is a root of `X² − α·X + 1 ∈ K[X]` with `K = ℚ(α)`, `α = ζ+ζ⁻¹`, so
  `[ℚ(ζ):K] ≤ 2`.
- **(B) Degree tower.** `φ(n) = 2·deg(minpoly_ℚ α_n)` for every `n ≥ 3`
  (since `deg(minpoly_ℚ ζ) = φ(n)` and `[ℚ(ζ):K] = 2` exactly — the lower bound
  `≥ 2` holds because `ζ` is non-real for `n ≥ 3` while `K = ℚ(α) ⊆ ℝ`).
- **(C) Exact degree.** `deg(minpoly_ℚ(2cos(2π/n))) = φ(n)/2` for `n ≥ 3`, and
  `= 1` (rational) exactly for `n ∈ {1,2,3,4,6}` — consistent with the Niven
  classification proved in the Cos/CosRational files.
- **(D) Niven values.** `α_n ∈ {2,−2,−1,0,1}` for `n ∈ {1,2,3,4,6}`.

This does **not** add a Lean proof — the exact-degree theorem is Docker-gated
(IntermediateField tower + a real-subfield minpoly that is absent from Mathlib,
~150 LOC). The script de-risks the eventual proof (the three load-bearing facts
are now certified, not just claimed).

### Lean tower plan (pinned for the Docker-up session)

Target: `[ℚ⟮ζ+ζ⁻¹⟯ : ℚ] = φ(n)/2` for `n ≥ 3`, `ζ` a primitive `n`-th root of unity.

1. `[ℚ⟮ζ⟯ : ℚ] = φ(n)` — via `cyclotomic_eq_minpoly_rat` + `natDegree_cyclotomic`
   (already used in `NthRootIrrationalOQ01OQ01Real.lean`), or
   `IsCyclotomicExtension.finrank`.
2. `[ℚ⟮ζ⟯ : ℚ⟮ζ+ζ⁻¹⟯] = 2`:
   - `≤ 2` from relation (A): `ζ` is a root of `X² − C α · X + 1` over `K`,
     so `minpoly K ζ ∣` that quadratic ⇒ `natDegree ≤ 2`
     (`minpoly.dvd` + `Polynomial.natDegree_le_of_dvd`).
   - `≥ 2` because `ζ ∉ K`: `K = ℚ⟮α⟯ ⊆ ℝ` (α real) but `ζ ∉ ℝ` for `n ≥ 3`
     (`Complex.ofReal_im`/primitive-root non-realness). Hence degree `≠ 1`.
3. Tower: `Module.finrank_mul_finrank` (or `FiniteDimensional.finrank_mul_finrank`)
   on `ℚ ⊆ ℚ⟮α⟯ ⊆ ℚ⟮ζ⟯` ⇒ `φ(n) = 2 · [ℚ⟮α⟯:ℚ]` ⇒ `[ℚ⟮α⟯:ℚ] = φ(n)/2`.

Fragile points to watch under v4.26: realizing `ℚ⟮α⟯ ⊆ ℝ` as a subfield (work in
`ℝ` via `Complex.ofReal` and the real embedding, or use `IsIntegrallyClosed`/
`adjoin` over the real subfield), and the `finrank` vs `Module.rank` coercions in
the tower law. The real-subfield minpoly itself (degree `φ(n)/2` explicitly) is
still not in Mathlib — the tower route above sidesteps constructing it.

---

## Session 2026-06-15 (S2, researcher-5) — Docker-VERIFIED all 5 files (fixed Degree synthInstance timeout)

**Mode**: REVISIT (build-gate). **Outcome**: VERIFIED → slug COMPLETED.

Docker recovered (worktree `proofs/.lake` is a healthy symlink to the main repo's warm
olean cache). Built all five registered files:
- `NthRootIrrationalOQ01OQ01` (primary), `…Cos`, `…CosRational`, `…Real` — **green, no edits**.
- `…Degree` — initially **failed**: `Proofs/NthRootIrrationalOQ01OQ01Degree.lean:177:4` typeclass
  timeout `failed to synthesize Module (↥ℚ⟮α⟯) (↥ℚ⟮α⟯)[X]` at the default 20000
  `synthInstance` heartbeat budget (separate from the file's `maxHeartbeats 1600000`). The
  instance IS synthesizable, just slow over the IntermediateField subtype. **Fix**: added
  `set_option synthInstance.maxHeartbeats 400000`. Rebuilt → **green**.

All five now kernel-check at the v4.26.0 pin. Promoted gallery meta `formalized/wip →
verified/original`; cleared the CosRational build-pending banner and the meta build-pending note.

**Files Modified (S2)**
- `proofs/Proofs/NthRootIrrationalOQ01OQ01Degree.lean` (+synthInstance.maxHeartbeats option)
- `proofs/Proofs/NthRootIrrationalOQ01OQ01CosRational.lean` (banner)
- `src/data/proofs/nth-root-irrational-oq-01-oq-01/meta.json` (status/badge/assumptions)

**Lesson**: a file carrying `maxHeartbeats N` can still die on `synthInstance.maxHeartbeats`
(default 20000) — they are independent budgets. IntermediateField-subtype instance searches
(`Module (↥K) (↥K)[X]`, field/commring derivations) are the usual culprits.

**Next**: only open vein is concrete small-`n` instantiations beyond the existing `fifthRoot`
example; the slug's core (Niven + irrationality + exact real-subfield degree) is complete and verified.
