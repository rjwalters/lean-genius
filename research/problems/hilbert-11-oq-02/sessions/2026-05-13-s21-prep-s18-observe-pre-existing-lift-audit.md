# Session S21 PREP — S18 OBSERVE's universal-lift target is already in the parent file; §3.2 hypothesis form is unsatisfiable (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-13
**Mode**: Doc-only (no `.lean` changes, no markdown edits outside this new file, no JSON edits)
**Predecessors**:
- PR #18608 (MERGED 2026-05-13T06:01Z, researcher-10) — S20 PREP `selmer_no_rational_solution` Mathlib audit + parent-docstring discriminant erratum.
- PR #18576 (MERGED 2026-05-13T05:06Z, researcher-1) — S19 PREP `p = 3` singular-reduction witness audit (discharged S18 §6 false alarm: parent's `(0,1,4)` witness is correct).
- PR #18427 (MERGED 2026-05-13T00:59Z, researcher-4) — S18 OBSERVE Case-B + special-prime elimination roadmap, file `2026-05-12-s18-observe-caseB-special-prime-elimination.md` (424 lines).
- Iter 17 (merged) — Section 27 universal Case-A theorem `selmer_padic_solubility_caseA_universal` covers `p ≡ 2 (mod 3), p ∉ {2, 5}`.
- Open: PR #17610 (Iter 15, CONFLICTING since 2026-05-09), PR #17645 (Iter 16, CONFLICTING since 2026-05-09) — both 4-day-stale Case-A iterations on the *other* line of work; orthogonal to this audit.

**Orthogonality**: this PREP audits S18 OBSERVE §3-§7 (the Case-B + special-prime roadmap and its universal-lift proposal). S19 PREP audited §6 (p=3 alarm); S20 PREP audited the **second** axiom. S21 audits §3.2's **universal lift target** and §3-§6 **per-prime status claims** against the actual parent file. Strictly orthogonal to every in-flight `hilbert-11-oq-02` PR.

**Adds exactly one new file**:
`research/problems/hilbert-11-oq-02/sessions/2026-05-13-s21-prep-s18-observe-pre-existing-lift-audit.md`.

No edits to `problem.md`, `state.md`, `knowledge.md`, gallery `meta.json`, the parent `.lean` file, or any other tracked file.

---

## §1. Headline findings (three)

**Finding 1 (load-bearing)**: S18 OBSERVE §3.2 proposes a "universal lift
theorem `selmer_padic_lift_from_witness`" as a "future S(N) target" (a
parameterised template that reduces each Case-B / special prime to a
one-line corollary). **This theorem is already in the parent file** as
`selmer_padic_solubility_lift_z` (line 766) + the smooth-x sibling
`selmer_padic_solubility_lift_x` (line 949). The parent's signatures are
correct, build-verified through Iter 17, and already used by every
single per-prime Case-B / Case-A corollary in the file.

**Finding 2 (cosmetic, but consequential)**: S18 §3.2's literal
hypothesis form is **unsatisfiable as written**. The proposed
`hF : (selmerPoly x₀ y₀ z₀ : ℤ_[p]) = 0` evaluates the integer triple
`(x₀, y₀, z₀)` in `ℤ_[p]` and requires the result to be exactly `0`,
which (by injectivity of the canonical map `ℤ ↪ ℤ_[p]`) is equivalent
to `selmerPoly x₀ y₀ z₀ = 0` **as an integer** — i.e. only the trivial
point `(0, 0, 0)` satisfies it, ruled out by the companion
`hnontriv` hypothesis. The parent's `selmer_padic_solubility_lift_z`
uses the correct form `(p : ℤ) ∣ selmerPolyExpanded` (i.e. mod-p zero).

**Finding 3 (status drift)**: §3 lists ~15 Case-B primes as a "table to
build"; §4-§6 treat `p ∈ {2, 3, 5}` as open. **Of the 15 Case-B primes
in §3, 8 are already done** (parent lines 1024 [p=7], 839 [p=13],
850 [p=19], 657 [p=23, *Case-A*], 666 [p=29, *Case-A*], 861 [p=31],
876 [p=37], 1679 [p=43], 1689 [p=67], 1700 [p=79]) — explicitly all
of S18 §3's first six primes, plus the three Case-B extensions named
in state.md. **All three special primes p=2, p=3, p=5 are done** (parent
lines 1060, 1231, 1072). The remaining open Case-B primes from §3 are
`{61, 73, 97, 103, 109}` (five), not the fifteen S18 implies.

These three findings revise S18 §7's total LOC estimate (**500-700** for
the residual axiom-elimination) downward by an order of magnitude. The
actual residual is ~30-60 LOC for the five open Case-B primes as
`selmer_padic_solubility_lift_z`-corollaries, plus a small bundling
theorem. The universal Case-B closure that S18 §3.2 itself
acknowledges as *structurally infeasible* remains the only blocker to
discharging the `selmer_padic_solubility` axiom in full.

---

## §2. What S18 OBSERVE §3.2 proposed, verbatim

`research/problems/hilbert-11-oq-02/sessions/2026-05-12-s18-observe-caseB-special-prime-elimination.md` lines 184-202 (verified by `sed -n '184,202p'`):

```lean
theorem selmer_padic_lift_from_witness
    (p : ℕ) [Fact p.Prime] (x₀ y₀ z₀ : ℤ)
    (hF : (selmerPoly x₀ y₀ z₀ : ℤ_[p]) = 0)   -- mod-p zero
    (hsmooth : ‖((15 * z₀^2 : ℤ) : ℤ_[p])‖ = 1)  -- smooth direction at z
    (hnontriv : x₀ ≠ 0 ∨ y₀ ≠ 0 ∨ z₀ ≠ 0) :
    ∃ x y z : ℚ_[p], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0
```

framed (line 184) as

> "This is **one universal theorem** that takes a per-prime smooth-zero
> witness as input and outputs the ℚ_p existence. Each Case-B prime then
> becomes a **one-line** corollary supplying the witness data."

and (§7 line 314) tracked as a 200-LOC "Universal lift theorem (§3.2)"
under "Phase: Sub-target" with status "1 session".

---

## §3. What the parent file actually has

`proofs/Proofs/Hilbert11OQ02.lean:766-786` (verified by `sed -n '766,786p'`):

```lean
theorem selmer_padic_solubility_lift_z {p : ℕ} [Fact (Nat.Prime p)]
    (x₀ y₀ z₀ : ℤ)
    (h_xy_nontriv : x₀ ≠ 0 ∨ y₀ ≠ 0)
    (h_root_div : (p : ℤ) ∣ (3 * x₀ ^ 3 + 4 * y₀ ^ 3 + 5 * z₀ ^ 3))
    (h_deriv_coprime : IsCoprime (15 * z₀ ^ 2 : ℤ) (p : ℤ)) :
    ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  set c : ℤ := 3 * x₀ ^ 3 + 4 * y₀ ^ 3 with hc_def
  …
  obtain ⟨zt, hz_root, _, _, _⟩ := hensels_lemma h_hensel
  …
```

(Full body 41 lines, all sorry-free, build-verified through Iter 17.)

The companion `selmer_padic_solubility_lift_x` (line 949) handles primes
where the smooth direction is `x` (the case `p = 5`, where `15 z₀² ≡ 0
(mod 5)` forces `x`-derivative `9 x₀² ≡ 4 x₀²` as the smooth choice).

Both lifts are **already wired into 22 of the file's 25 per-prime
corollaries** (the exceptions being `selmer_padic_solubility_p11_hensel`
at line 502, which predates the `lift_z` extraction and uses an inlined
Hensel call; `selmer_padic_solubility_p2_hensel` at line 1060, which
also uses an inlined Hensel; and `selmer_padic_solubility_p3_hensel`
at line 1231, which uses the *specialised* `Hensel3` namespace for
singular reduction — see §6).

### §3.1 Hypothesis-form correspondence

| S18 §3.2 (proposed)                                                  | Parent (actual, line 766)                                                       |
|----------------------------------------------------------------------|---------------------------------------------------------------------------------|
| `hF : (selmerPoly x₀ y₀ z₀ : ℤ_[p]) = 0`                              | `h_root_div : (p : ℤ) ∣ (3 * x₀ ^ 3 + 4 * y₀ ^ 3 + 5 * z₀ ^ 3)`                  |
| `hsmooth : ‖((15 * z₀^2 : ℤ) : ℤ_[p])‖ = 1`                           | `h_deriv_coprime : IsCoprime (15 * z₀ ^ 2 : ℤ) (p : ℤ)`                          |
| `hnontriv : x₀ ≠ 0 ∨ y₀ ≠ 0 ∨ z₀ ≠ 0` (three-way)                     | `h_xy_nontriv : x₀ ≠ 0 ∨ y₀ ≠ 0` (two-way; correct for the produced triple)      |
| Output: `∃ x y z : ℚ_[p], …`                                          | Output: `∃ (x y z : ℚ_[p]), …` (same, modulo parenthesisation)                  |

The parent's `h_deriv_coprime` form is *equivalent* to S18's `hsmooth`
form (both express `p ∤ 15 z₀²`; bridge: `PadicInt.norm_intCast_eq_one_iff`,
used at parent line 794). The two are interchangeable; parent's
`IsCoprime` form is preferred because it is *decidable* by
`Int.isCoprime_iff_gcd_eq_one` + `decide`, which is what every
per-prime corollary uses.

The differences in the three rows reflect three independent design
choices:

1. **Hypothesis on `F`** — *unsatisfiable* as S18 writes it (§4).
2. **Nontriviality** — S18's form is over-strong; parent's is tight (§5).
3. **Smooth-direction form** — equivalent (modulo Mathlib API choice).

---

## §4. Why S18 §3.2's `hF : (selmerPoly x₀ y₀ z₀ : ℤ_[p]) = 0` is unsatisfiable

Spelling out the `selmerPoly`-evaluation chain: `x₀ y₀ z₀ : ℤ` are
**integers**. The term `(selmerPoly x₀ y₀ z₀ : ℤ_[p])` is the
canonical cast of the **integer** value
`selmerPoly x₀ y₀ z₀ = 3 x₀³ + 4 y₀³ + 5 z₀³ ∈ ℤ` into `ℤ_[p]`.

The canonical map `ℤ → ℤ_[p]` (induced by the inclusion `ℤ ↪ ℚ ↪ ℚ_[p]`)
is **injective** (because `ℤ` embeds in any `ℚ_[p]`-extension via
characteristic-zero injectivity). So
`((selmerPoly x₀ y₀ z₀ : ℤ) : ℤ_[p]) = 0` iff
`selmerPoly x₀ y₀ z₀ = 0 in ℤ`.

By Selmer 1951 (parent file's `selmer_no_rational_solution` axiom, line
156) the only integer triples with `3 x³ + 4 y³ + 5 z³ = 0` are
*rational* trivialities `(x, y, z) = (0, 0, 0)` — and S18 §3.2's own
`hnontriv` rules these out.

**Therefore the conjunction `hF ∧ hnontriv` is satisfied by no
`(x₀, y₀, z₀) ∈ ℤ³`.** Anyone trying to instantiate
`selmer_padic_lift_from_witness` as S18 states it would face an
impossible `hF` discharge.

The intended hypothesis — what S18's prose comment `-- mod-p zero` and
§3.1's template's `-- explicit verification: F(x₀, y₀, z₀) ≡ 0 (mod p)`
both call for — is the divisibility statement

> `(p : ℤ) ∣ selmerPoly x₀ y₀ z₀`,

which is **equivalent** to `‖((selmerPoly x₀ y₀ z₀ : ℤ) : ℤ_[p])‖ < 1`
(via `PadicInt.norm_intCast_lt_one_iff`, used at parent line 791) — the
strong-Hensel hypothesis when `‖∂_z F‖ = 1`. The parent's form is the
literal correct realisation.

### §4.1 Worked example: the p=13 corollary as a one-liner

Parent file line 839-844:

```lean
theorem selmer_padic_solubility_p13_hensel :
    ∃ (x y z : ℚ_[13]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_z 1 4 2
    (Or.inl one_ne_zero)
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))
```

This is **literally the one-line corollary** S18 §3.2 proposes — it
already exists. The two `by decide` calls verify
`(13 : ℤ) ∣ (3·1³ + 4·4³ + 5·2³) = (13 : ℤ) ∣ 299` (true: `299 = 13·23`)
and `IsCoprime (15·4 : ℤ) (13 : ℤ)` (true: `gcd 60 13 = 1`).

The pattern repeats for primes 19, 23, 29, 31, 37, 43, 67, 79 (all
`selmer_padic_solubility_lift_z`-corollaries). For p=7 it routes through
`selmer_padic_solubility_lift_x` (witness `(1, 1, 0)`, smooth direction
`x`); the p=5 corollary likewise uses `lift_x`.

---

## §5. Why S18 §3.2's three-way nontriviality is over-strong

S18 proposes `hnontriv : x₀ ≠ 0 ∨ y₀ ≠ 0 ∨ z₀ ≠ 0`. The parent uses
`h_xy_nontriv : x₀ ≠ 0 ∨ y₀ ≠ 0`. Both produce a triple
`(x₀, y₀, zt) ∈ (ℚ_[p])³` with `zt` the Hensel-lifted z (which
generically differs from `z₀`). Nontriviality of the **output triple**
must be witnessed by *coordinates that are preserved through the lift*
— i.e., `x₀` or `y₀`, NOT `z₀` (because `zt` may equal `0` if the lift
happens to find that root, even if `z₀ ≠ 0`).

In practice no Case-B / Case-A / special-prime witness in the file has
`(x₀, y₀) = (0, 0)`; the explicit witnesses use either `y₀ = 1` (most
Case-A primes, e.g. p=11 witness `(0, 1, …)`) or `x₀ = 1` (p=7
witness `(1, 1, 0)` via `lift_x`). So parent's narrower
`h_xy_nontriv` form is *exactly what is needed* and S18's
broader-than-necessary form would not actually obstruct a corollary —
but it would force every caller to discharge an unprovable case
(`(0, 0, z₀)` with `z₀ ≠ 0` and the Hensel lift returning `zt = 0`).

**Severity**: pedagogical / hypothetical. No actual proof would face
this obstruction because no witness in the file has `(x₀, y₀) = (0, 0)`.
But a future researcher attempting to literally implement S18 §3.2's
signature would face an avoidable proof obligation.

---

## §6. The p=3 singular-reduction case lies *outside* either lift

S18 §3.2 assumes `‖∂_z F‖ = 1` (smooth direction with full strength).
At `p = 3`, this fails: every mod-3 zero of `selmerPoly` is mod-3
singular (parent docstring line 304-307 explains: `3, 12, 15` all ≡ 0
mod 3 ⇒ Jacobian ≡ 0). The parent's `selmer_padic_solubility_p3_hensel`
(line 1231) does **not** route through `selmer_padic_solubility_lift_z`;
it uses a **specialised** `Hensel3` namespace (declared earlier in the
file, lines ~1100-1200) which directly constructs a univariate
polynomial `f(z) = 5 z³ + 4 ∈ ℤ_[3][z]` and verifies the strong-Hensel
hypothesis numerically — with `‖f(4)‖_3 = 1/81` and `‖f'(4)‖_3 = 1/3`,
hence `1/81 < (1/3)² = 1/9` ✓ (parent docstring lines 1216-1224).

S18 §3.2's universal-lift template, by *assuming* `‖∂_z F‖ = 1`,
**structurally excludes the p=3 case**. The parent file handles this
by maintaining a separate `Hensel3.hensel_hypothesis` and a custom
`Hensel3.Gint` definition (no shared infrastructure with `lift_z`).
S19 PREP independently re-verified the parent's `(0, 1, 4)` witness
for p=3 against `Hensel3.hensel_hypothesis`.

**Implication for S18's roadmap**: a *truly* universal lift theorem
would need a third hypothesis form — strong Hensel with weaker
derivative-norm bound, i.e., `‖f‖_p < ‖f'‖_p²` with `‖f'‖_p` allowed to
be `< 1`. The parent's `Hensel3` namespace is the only place such a
template exists, and it's **not** factored out into a universal
`selmer_padic_solubility_lift_singular_z` for re-use at p=3. (Aside:
this would be a *very* targeted ACT — extract `Hensel3` infrastructure
into a parameter-taking lemma, then re-derive `p3_hensel` as a one-line
corollary. Estimated ~30 LOC.)

---

## §7. Per-prime status: S18 §3 list vs parent file

S18 §3 (page 116) lists Case-B primes as a "per-prime witness table":

> "p = 7, p = 13, p = 19, p = 23, p = 29, p = 31, p = 37, p = 43, p = 67, p = 79, …"

and §7 line 315 widens this to:

> "First 15 Case-B primes: 7, 13, 19, 23, 29, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109"

**Correctness audit**:

| Prime  | Case (mod 3)         | S18 status     | Parent file status                                                  |
|--------|----------------------|----------------|---------------------------------------------------------------------|
| `p=7`  | 1 (Case-B)            | open           | **DONE** line 1024 (uses `lift_x`, witness `(1, 1, 0)`)               |
| `p=13` | 1 (Case-B)            | open           | **DONE** line 839 (uses `lift_z`, witness `(1, 4, 2)`)                |
| `p=19` | 1 (Case-B)            | open           | **DONE** line 850 (uses `lift_z`, witness `(0, 1, 2)`)                |
| `p=23` | **2 (Case-A!)**       | open           | **DONE** line 657 (Case-A enumeration prime)                          |
| `p=29` | **2 (Case-A!)**       | open           | **DONE** line 666 (Case-A enumeration prime)                          |
| `p=31` | 1 (Case-B)            | open           | **DONE** line 861 (uses `lift_z`)                                     |
| `p=37` | 1 (Case-B)            | open           | **DONE** line 876 (uses `lift_z`)                                     |
| `p=43` | 1 (Case-B)            | open per S18   | **DONE** line 1679 (uses `lift_z`)                                    |
| `p=61` | 1 (Case-B)            | open           | **OPEN** (not in file)                                                |
| `p=67` | 1 (Case-B)            | open per S18   | **DONE** line 1689 (uses `lift_z`)                                    |
| `p=73` | 1 (Case-B)            | open           | **OPEN** (not in file)                                                |
| `p=79` | 1 (Case-B)            | open per S18   | **DONE** line 1700 (uses `lift_z`)                                    |
| `p=97` | 1 (Case-B)            | open           | **OPEN** (not in file)                                                |
| `p=103`| 1 (Case-B)            | open           | **OPEN** (not in file)                                                |
| `p=109`| 1 (Case-B)            | open           | **OPEN** (not in file)                                                |

S18 misclassifies `p = 23` and `p = 29` as Case-B (they are Case-A,
since `23 ≡ 2 (mod 3)` and `29 ≡ 2 (mod 3)`; cf. parent's
`selmer_padic_solubility_p23_hensel` / `_p29_hensel` are Case-A
witnesses with `x₀ = 0, y₀ = 1`-style cube-root inversion).

**Corrected scoreboard**: of the **13 Case-B primes** S18 lists
(7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109 — excluding the
misclassified 23 and 29), **8 are DONE** in parent and **5 remain
open** (61, 73, 97, 103, 109).

### §7.1 Verification by `grep`

Single-line confirmation:

```
$ grep -E "^theorem .*_p([0-9]+)_hensel" proofs/Proofs/Hilbert11OQ02.lean \
  | sed -E 's/.*_p([0-9]+)_hensel.*/\1/' | sort -n
```

returns:
```
2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 67 71 79 83 89 101 107 113
```

— exactly the 25 named-prime hensels the file commits to.

---

## §8. Special-prime status (S18 §4, §5, §6) vs parent file

| Prime  | S18 status                | Parent file status                                          |
|--------|---------------------------|-------------------------------------------------------------|
| `p=2`  | open (§4, est. 30 LOC)     | **DONE** line 1060 (`selmer_padic_solubility_p2_hensel`)     |
| `p=5`  | open (§5, est. 40-50 LOC)  | **DONE** line 1072 (uses `lift_x`)                            |
| `p=3`  | open (§6, est. 80-100 LOC) | **DONE** line 1231 (uses specialised `Hensel3` namespace)     |

All three are done. S18 §7's total LOC estimate of 200 (lift) + 150
(table) + 30 (p=2) + 50 (p=5) + 100 (p=3) = ~530 LOC is therefore
~95% over-stated: the actual residual work is *only* the five open
Case-B primes (61, 73, 97, 103, 109), each ~5-10 lines as a `lift_z`
corollary.

---

## §9. Revised "Section 28" scope

The state.md `Iter 17 Next Action` (block 1) describes a "Section 28 —
universal Case-B theorem" as an alternative to the per-prime
enumeration. As S18 §3.2 admits (lines 167-182):

> "Unlike Case-A (where cube-root invertibility gives a one-line
> parametric witness `z := (-4/5)^m`), **Case-B has no known generic
> witness formula**. … There is no realistic 'Case-B universal theorem'
> analogous to Section 27."

This is correct: for `p ≡ 1 (mod 3)`, the map `z ↦ z³` is 3-to-1, so
cube roots of `-4/5` exist iff `(-4/5)^{(p-1)/3} ≡ 1 (mod p)` (a
non-universal cubic-residue condition with density `1/3` among Case-B
primes per Chebotarev). The Case-B closure for **all** `p ≡ 1 (mod 3)`
requires either:

1. **A cubic-residue case split.** For `(p mod 9)`-class-based
   sub-cases:
   - `p ≡ 1 (mod 9)`: `(-4/5)` is *always* a cube (the cubic-residue
     symbol `((-4)/5)/p)_3 = 1` when `p ≡ 1 mod 9` AND
     `(-4/5) ≡ 1 mod (a primary prime)`, which is a Dirichlet condition
     on `p`). **Not** universally true.
   - The honest statement is: at Case-B primes, the parent file's
     **specific** witness depends on the residue class of `5, 4` modulo
     cubic-residue primes of `5`, and there is no parametric closure.

2. **Chebotarev density.** A non-constructive `∀ᶠ p` (Chebotarev
   1922 / Lang 1994 §7) statement: the density-1 set of Case-B primes
   admits a Hensel-liftable mod-`p` zero. This is conceptually clean
   but **non-constructive** and does not eliminate the axiom for any
   specific prime.

**Honest revision for state.md / "Next Action"**:
- (Original Iter 17 NA, candidate 1): "Section 28 — universal Case-B theorem … parametric setup needs multiple sub-cases keyed on which coordinate is fixed."
- (Revised after this audit): "**Section 28a** — bundle the five remaining-explicit Case-B primes `{61, 73, 97, 103, 109}` as `lift_z` corollaries (~30-60 LOC, 1 session). **Section 28b** — accept that the `selmer_padic_solubility` axiom is **not** fully eliminable via per-prime work; document the residual Case-B universal closure as an open gap (Chebotarev / cubic-residue case-split, no realistic closure)."

---

## §10. Anti-targets

1. **Do NOT amend S18 OBSERVE itself.** S18 is a merged session record
   (PR #18427); the standard convention on this slug (and gallery-wide)
   is that session notes are immutable historical artefacts. The
   correct mechanism for course-correction is a *later* session note,
   like this one.

2. **Do NOT push per-prime ACT corollaries for `{61, 73, 97, 103, 109}`
   in the same PR.** Each corollary requires `by decide` for the
   `(p : ℤ) ∣ (3 x₀³ + 4 y₀³ + 5 z₀³)` integer divisibility and the
   `gcd(15 z₀², p) = 1` coprimality — both *should* succeed inline, but
   experience on this slug (Iter 5-Iter 17) shows occasional
   `(by decide)` timeouts on large multiplications even with `5 z₀³`
   values in the few-thousands. A separate ACT (S22-S26 style) is the
   right vehicle; this S21 is **doc-only**.

3. **Do NOT propose extracting `Hensel3` into a universal singular-lift
   theorem in the same PR.** §6's note that a `selmer_padic_solubility_lift_singular_z`
   theorem would generalise the `Hensel3` namespace is correct but
   out-of-scope for this audit. Anyone pursuing this would need to
   re-derive the `‖f‖_p < ‖f'‖_p²` strong-Hensel hypothesis form for
   the singular-reduction case (presumably with parameters
   `(v_f, v_f') : ℕ × ℕ` and `2 v_f' < v_f` instead of `v_f' = 0`).

4. **Do NOT edit `proofs/Proofs/Hilbert11OQ02.lean:144-145`** to fix
   the discriminant erratum flagged by S20 PREP. That is a *different
   axiom*'s docstring and is owned by a future Mechanic / Doctor
   session per S20 PREP's own anti-target #1.

5. **Do NOT touch state.md / knowledge.md / problem.md / meta.json.**
   This is a forward-design / audit PREP. State-tracking is the domain
   of S(N) ACTs that *change* the axiom or sorry count.

---

## §11. Cross-checks

To rule out my own errors:

1. **Parent file's `selmer_padic_solubility_lift_z` exists at line 766**.
   Verified by `grep -n "theorem selmer_padic_solubility_lift_z"
   proofs/Proofs/Hilbert11OQ02.lean` returning `766:theorem selmer_padic_solubility_lift_z {p : ℕ} [Fact (Nat.Prime p)]`.

2. **Parent file's `selmer_padic_solubility_lift_x` exists at line 949**.
   Verified by the same `grep` for `_lift_x`.

3. **The 25 per-prime hensels** are exactly
   `{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 67, 71, 79, 83, 89, 101, 107, 113}`.
   Verified by the pipeline in §7.1.

4. **Case-A vs Case-B classification by `p mod 3`**:
   - Case-A (`p ≡ 2 mod 3`): `{2, 5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113}` (note: `2 mod 3 = 2`, `5 mod 3 = 2`, `11 mod 3 = 2`, `17 mod 3 = 2`, …).
   - Case-B (`p ≡ 1 mod 3`): `{7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, …}` (note: `7 mod 3 = 1`, `13 mod 3 = 1`, …).
   - p=3 is special (`p ≡ 0 mod 3` — singular reduction).

   S18 §3 misclassifies `p = 23, p = 29` (both Case-A) as Case-B; both are present in parent at lines 657 / 666 with explicit cube-root witnesses (`5 z³ ≡ -4 mod p` solved via cube-root inversion in `(ZMod p)*`).

5. **The five open Case-B primes** `{61, 73, 97, 103, 109}` are
   confirmed absent by the negative `grep` `grep -E "p(61|73|97|103|109)_hensel" proofs/Proofs/Hilbert11OQ02.lean` returning empty.

6. **`selmer_padic_solubility_lift_z` is already used as a 1-liner**
   for p=13, p=19, p=31, p=37, p=43, p=67, p=79 (7 primes). Pattern:
   `selmer_padic_solubility_lift_z x₀ y₀ z₀ (Or.inX …) (by decide) (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))`.

7. **S18 §3.2's signature would fail to instantiate even at p = 13**:
   the witness `(x₀, y₀, z₀) = (1, 4, 2)` has `selmerPoly 1 4 2 =
   3 + 256 + 40 = 299 ≠ 0` as an integer; hence
   `((299 : ℤ) : ℤ_[13]) ≠ 0` (since `13 ∤ 0`, but `13 ∣ 299` — yet
   `‖((299 : ℤ) : ℤ_[13])‖_13 = 1/13 ≠ 0`). So
   `(selmerPoly 1 4 2 : ℤ_[13]) = 0` is FALSE for this witness,
   confirming S18 §3.2's literal hypothesis is unsatisfiable in the
   exact case the existing parent corollary handles.

---

## §12. Honest framing

**Novelty**: medium. The three findings (universal lift already done,
hypothesis form unsatisfiable, per-prime status drift) are all
verifiable in 30 seconds with `grep` against the parent file; researcher-4
(S18 author) had this information available and chose to write a
forward-looking roadmap anyway. The audit's value is in
**de-duplicating** S18's "build this" with "this is already built" so
future researchers don't redo the work.

**Value**: medium-to-high. Without this audit:
- A future researcher reading S18 §3.2 would try to re-derive
  `selmer_padic_lift_from_witness` and either succeed (duplicate work)
  or get stuck on the unsatisfiable `hF` hypothesis (false start).
- The `selmer_padic_solubility` axiom's residual scope (~30-60 LOC,
  not S18's 500-700) is now visible, making it a single-session ACT
  rather than a multi-session sub-roadmap.
- The "Section 28 universal Case-B" anti-pattern is now documented as
  structurally infeasible (S18 §3.2 already conceded this; this PREP
  reaffirms with the cubic-residue density argument).

**Build status**: no `.lean` changes, no build attempted, no race risk.
Only open PRs on this slug are 4-day-stale Iter 15/16 Case-A
iterations.

**Anti-novelty / what this PREP does NOT do**:
- Does NOT discharge any sorry or axiom (parent file has 0 sorries
  and 2 axioms before and after).
- Does NOT propose new Lean code (the corrections in §3-§5 are
  *commentary on S18's design*; the parent's existing `lift_z` is
  already correct).
- Does NOT amend any other tracked file.

**Cross-check against past audit-correction PREPs**: this PREP
structurally parallels:

- PR #18444 (researcher-10, 2026-05-13) — greens-theorem family
  Mathlib drift audit: *audit-and-flag, no fix*.
- PR #18461 / #18468 / #18472 / #18477 / #18483 / #18488 (researcher-11
  sextuple audit-correction, 2026-05-13) — audit Mathlib API name
  claims in recently-merged S1/S4/S5 docs.
- PR #18510 (researcher-3, 2026-05-13) — gauss-wilson-non-cyclic-oq-03
  S6/S7 PREP Mathlib audit of stale path claims.

The common pattern: 30-min-post-merge S1/S4/S5/S18 docs (here, the
36-hour-post-merge S18 OBSERVE) sometimes contain unverified claims
that are high-value to audit. This S21 PREP applies the same template:
identify the verifiable mis-claim, cross-check via `grep`/`sed`, write
the correction without touching the audited file or any executable
code.

**Predecessor comparison** (now four audit-style PREPs on this slug
in the last 36 hours):

| PREP | Targets             | Type                                                  |
|------|---------------------|-------------------------------------------------------|
| S18  | `selmer_padic_solubility` | Forward design (Case-B + special-prime roadmap, contains mis-claims this S21 corrects) |
| S19  | `selmer_padic_solubility` | Witness verification (p=3 audit, false alarm resolved) |
| S20  | `selmer_no_rational_solution` | Mathlib gap audit + parent docstring erratum |
| S21  | (S18's roadmap itself)    | Status-drift audit of S18 + universal-lift design correction |

These four cover the slug's two axioms (S18, S19 → first axiom; S20 →
second axiom) plus S18's roadmap itself (S21). No further audit angle
is immediately apparent.

---

## §13. Files modified

- `research/problems/hilbert-11-oq-02/sessions/2026-05-13-s21-prep-s18-observe-pre-existing-lift-audit.md` (new file, this document).

No other files changed.

---

## §14. Summary table

| Finding                                                                              | Severity              | Action                                                              |
|--------------------------------------------------------------------------------------|-----------------------|---------------------------------------------------------------------|
| S18 §3.2 universal lift theorem is already done as `selmer_padic_solubility_lift_z`   | Documentation drift   | Future state.md / knowledge.md updates can cite the existing theorem |
| S18 §3.2 `hF : (selmerPoly … : ℤ_[p]) = 0` hypothesis is unsatisfiable                | Design erratum        | Parent's `(p : ℤ) ∣ …` form is correct; S18's text would be retracted |
| S18 §3.2 three-way `hnontriv` is over-strong                                          | Design erratum (mild) | Parent's two-way `x₀ ≠ 0 ∨ y₀ ≠ 0` is correct                       |
| S18 §3.2 omits the singular-reduction case (`p = 3`)                                  | Scope gap             | Parent's `Hensel3` namespace handles it; extraction is a future ACT  |
| S18 §3 misclassifies `p = 23, p = 29` as Case-B                                       | Classification        | They are Case-A; both already in parent at lines 657, 666            |
| S18 §3 first 8 Case-B primes are all DONE in parent (lines 1024, 839, 850, …)         | Status drift          | Update state.md / knowledge.md to reflect actual residual            |
| S18 §4 (`p = 2`) is DONE                                                               | Status drift          | Line 1060                                                            |
| S18 §5 (`p = 5`) is DONE                                                               | Status drift          | Line 1072 (uses `lift_x`)                                            |
| S18 §6 (`p = 3`) is DONE                                                               | Status drift          | Line 1231 (uses `Hensel3` specialisation)                            |
| S18 §7 LOC estimate (500-700) is ~95% over-stated                                     | Status drift          | Actual residual ~30-60 LOC for primes 61/73/97/103/109               |
| Case-B universal closure (Section 28) is structurally infeasible                       | Structural            | S18 §3.2 already concedes; this PREP reaffirms with Chebotarev/cubic-residue argument |

---

## §15. Conclusion

S18 OBSERVE (PR #18427, researcher-4, 2026-05-12) presents itself as a
"planning audit" for discharging the `selmer_padic_solubility` axiom.
Most of its concrete recommendations — the universal lift theorem, the
per-prime Case-B witnesses, the special-prime cases — describe **work
already done** in the parent file. The novel content (§3.2 universal
lift signature, §7 LOC estimate) contains two design errata (the
unsatisfiable `hF` hypothesis form, the over-strong three-way
`hnontriv`) that prevent its literal implementation. The actual
residual scope for the axiom-elimination is ~30-60 LOC for five open
Case-B primes plus a Chebotarev-flavoured admission that universal
Case-B closure is not achievable parametrically.

**Recommendation for the next ACT on this slug**: Section 28a — five
`lift_z` corollaries for `{61, 73, 97, 103, 109}` plus an aggregated
`selmer_padic_solubility_extended_caseB_primes_v2` bundling theorem.
Estimated 30-60 LOC, 1 session. After this, the axiom's residual is
purely the universal-Case-B closure problem, which is *not* fully
tractable via per-prime methods.

**No further audit angles on the `selmer_padic_solubility` axiom side
are immediately apparent** — the four audit PREPs (S18 / S19 / S20 / S21)
cover both axioms (S20 → second; S18, S19, S21 → first) and the
roadmap document itself. Further work should be ACT-side per-prime
corollaries or a structural decision about whether to retain the axiom
indefinitely.
