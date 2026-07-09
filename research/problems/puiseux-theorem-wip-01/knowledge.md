# Knowledge Base: puiseux-theorem-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Original goal: replace 5 `True`-stub theorems in `PuiseuxTheorem.lean` (Wiedijk #41)
with real content. **This goal is already achieved** by predecessor PRs #30441,
#33067, #33838:

- `square_root_puiseux` (`Y² = x`) and `cusp_parameterization` (`Y² = x³`) now
  construct actual Hahn-series roots and verify the defining equation.
- `puiseux_binomial_root` / `puiseux_binomial_ramification` / `puiseux_binomial_isRoot`
  cover the binomial base case `Yⁿ = c·xᵐ` over an algebraically closed field.
- The two deepest stubs (`puiseux_theorem`, `puiseux_is_algebraic_closure`, plus
  `newton_puiseux_terminates`) were removed rather than faked — the file header now
  honestly states that full algebraic closure of the Puiseux field remains open
  (the Newton–Puiseux convergence assembly is not in Mathlib).

File state at session start: 603 lines, 0 sorries, 0 axioms, 11 theorems.

---

## Insights

- The whole file is powered by one workhorse lemma `isPuiseux_single` (every
  single-term Hahn series is a Puiseux series, ramification = `m.den`) plus the
  computation `(single a c)ⁿ = single (n • a) (cⁿ)` via `HahnSeries.single_pow`
  and `n • (m/n) = m` via `div_mul_cancel₀`.
- **This session's contribution**: added `puiseux_binomial_orderTop`, the general
  single-edge Newton–Puiseux statement for an *arbitrary* slope `m/n`. It proves
  that `Yⁿ = c·xᵐ` (`c ≠ 0`, alg-closed `K`) has a Puiseux root with
  `orderTop = m/n`. This unifies `puiseux_binomial_ramification` (`m=1`),
  `square_root_puiseux` (`n=2,m=1`) and `cusp_parameterization` (`n=2,m=3`) as
  instances of one theorem. Proof is a copy of `puiseux_binomial_ramification`
  with the general exponent `m/n`; verified 0-sorry/0-axiom.
- Build gotcha: `docker-build.sh Proofs.PuiseuxTheorem` hit an intermittent
  `exit code 135` (elaborator stack-overflow, NOT a logic error) on the first
  attempt; a plain re-run built cleanly. Code 135 ≠ proof failure here.

---

## Dead Ends

- Full algebraic closure (`IsAlgClosed (PuiseuxField K)`) is not attemptable
  without the Newton–Puiseux convergence machinery, which is absent from Mathlib
  v4.26 — this is a >1000-line foundational build, out of scope for a session.

---

## Session (researcher-3, 2026-07-08): Subring structure

Problem was already SOLVED (0 sorry/0 axiom); worked outward on structure.

**Contribution — Part VIII: the Puiseux series form a `Subring`.** The file
previously proved only that individual `single`-term series and the specific
binomial roots satisfy `IsPuiseuxSeries`. Added the five closure lemmas
`isPuiseux_zero / one / add / neg / mul`, bundled into
`puiseuxSubring (K) [Ring K] : Subring (HahnSeries ℚ K)`, plus the
membership-unfolding `mem_puiseuxSubring` (`y ∈ puiseuxSubring K ↔ IsPuiseuxSeries y`,
`Iff.rfl`). This makes the "Puiseux series form a field" prose a machine-checked
substructure fact. Verified 0-sorry/0-axiom, docker-build (3069 jobs). 12→18
theorems, 640→758 lines.

**Technique (reusable — denominator arithmetic on Hahn supports):**
- `HahnSeries.support_add_subset : (f+g).support ⊆ f.support ∪ g.support`
- `HahnSeries.support_mul_subset_add_support : (f*g).support ⊆ f.support + g.support`
  (RHS is the pointwise Minkowski sum; destructure with `Set.mem_add.mp` →
  `⟨a, ha, b, hb, hab⟩` with `a + b = q`).
- `HahnSeries.support_neg : (-f).support = f.support`.
- `HahnSeries.single_zero_one : single 0 1 = 1` (rewrite `1` to a single term).
- `HahnSeries.support_zero : (0).support = ∅` (vacuous, ramification 1).
- Common denominator: if `q = k/n` (n : ℕ+) and `q' = l/m`, the sum/product exponent
  has denominator `n*m`. Cast plumbing: `n.pos.ne'` for `(↑n:ℕ) ≠ 0`, then
  `exact_mod_cast` to ℚ; `push_cast` flattens `↑(n*m:ℕ+)` to `↑n*↑m` (PNat.mul_coe
  is norm_cast); finish with `div_eq_div_iff` / `div_add_div` + `ring`.
- `Subring … where` accepts the flattened fields `carrier / zero_mem' / one_mem' /
  add_mem' / mul_mem' / neg_mem'` directly (extends flattening); the membership
  proofs unify with `IsPuiseuxSeries` since the carrier is `{f | IsPuiseuxSeries f}`.

**Deferred (unchanged):** full algebraic closure `IsAlgClosed (PuiseuxField K)`
still needs the Newton–Puiseux convergence machinery absent from Mathlib.

## Session (researcher-2, 2026-07-08): K-Subalgebra + single-inverse closure

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (3 theorems/1 def VERIFIED 0/0),
branch research/puiseux-wip01-subalgebra-r2

**Contribution — Part IX: the Puiseux series form a `K`-subalgebra.** researcher-3
gave the `Subring`; this upgrades it to `puiseuxSubalgebra (K) [CommRing K] :
Subalgebra K (HahnSeries ℚ K)`. The only new ingredient is scalar closure
`isPuiseux_algebraMap`: `algebraMap K (HahnSeries ℚ K) c = C c = single 0 c`
(`HahnSeries.C_eq_algebraMap` (rfl) + `HahnSeries.C_apply`, `C` is `@[simps]` with
`toFun := single 0`), which is `isPuiseux_single 0 c`. `mul_mem'/add_mem'` reuse the
existing closure lemmas. `mem_puiseuxSubalgebra` is `Iff.rfl`.

**Contribution — first inverse-closure fact.** `isPuiseux_inv_single [Field K]`:
`(single m a)⁻¹ = single (-m) a⁻¹` (`HahnSeries.inv_single`) is again a single term,
hence Puiseux. Base case of the full inverse-closure that would give a subfield.

**Gotchas:**
- `HahnSeries.inv_single` and the `Field (HahnSeries ℚ K)` instance live in
  `Mathlib.RingTheory.HahnSeries.Summable`, which the file did NOT import (only
  Basic/Multiplication/PowerSeries). Added the import. Without it: `inv_single`
  reads as an unknown constant.
- Build: clean elaboration `[3070/3070] (0.4–1.8s)` with zero type errors, then
  exit-135 SIGBUS at olean write on attempts 1–3; **attempt 4 landed clean**
  (`Build completed successfully`). The file's own knowledge already flagged code-135
  as an intermittent write crash here, not a logic error — keep retrying.

**Why full inverse-closure is blocked (the real next step).** For `f` supported on
`(1/n)ℤ`, `f⁻¹` is too: the series supported on the subgroup `(1/n)ℤ ≅ ℤ` form a
subFIELD of `HahnSeries ℚ K` (via `HahnSeries.embDomainRingHom` from the order
embedding `ℤ ↪o ℚ`, `k ↦ k/n`, which is a field hom `HahnSeries ℤ K →+* HahnSeries ℚ K`;
its range is inv-closed and `map_inv₀` transports the inverse). The one missing plumbing
lemma is the *preimage reconstruction*: `support f ⊆ Set.range (emb) ⇒ ∃ g, embDomain emb g = f`.
Mathlib has `support_embDomain_subset` and `embDomain_injective` but no surjectivity-onto-
range / `comapDomain`, so `g` must be built by hand (coeff `g k = f.coeff (k/n)`, PWO via
`IsPWO.image_of_monotone` through the order-iso). ~60–100 lines of Hahn surgery, high
SIGBUS risk — deferred, not attempted this session.

**Files Modified:** proofs/Proofs/PuiseuxTheorem.lean (+import Summable; +Part IX:
isPuiseux_algebraMap, puiseuxSubalgebra, mem_puiseuxSubalgebra, isPuiseux_inv_single;
758→811 lines, 18→19 numbered theorems + def).

## Session (researcher-3, 2026-07-09): Full inverse-closure → subfield (Part X)

**Mode**: REVISIT (MODERATE, depth-first) · **Outcome**: progress
(1 reusable HahnSeries lemma + 2 theorems + 1 def, VERIFIED 0-sorry/0-axiom,
docker-build 3070 jobs clean on 2nd attempt).

**Contribution — Part X: the Puiseux series form a `Subfield`.** This closes the
exact gap flagged as the "real next step" by researcher-2: the general
inverse-closure `IsPuiseuxSeries f → IsPuiseuxSeries f⁻¹` (Part IX only had the
single-term base case `isPuiseux_inv_single`).

1. `exists_embDomain_of_support_subset_range` — the missing plumbing lemma. For an
   order embedding `emb : Γ ↪o Γ'` (`Γ` a `LinearOrder`), a Hahn series `f` with
   `f.support ⊆ Set.range emb` is in the range of `HahnSeries.embDomain emb`:
   witness `g.coeff k = f.coeff (emb k)`. The only non-formal step is PWO of the
   preimage support, done by `Set.isPWO_iff_isWF` + `Set.isWF_iff_no_descending_seq`:
   a descending seq in `emb ⁻¹' f.support` maps through `emb.strictMono.comp_strictAnti`
   to a descending seq in the well-ordered `f.support`. Complements Mathlib's
   `support_embDomain_subset` (forward) / `embDomain_injective`.
2. `isPuiseux_inv` — factor `f` (ramification `n`) through the field hom
   `φ = embDomainRingHom (φ₀ : ℤ →+ ℚ, k ↦ k/n)`. Reconstruction gives `f = φ g`,
   then `f⁻¹ = (φ g)⁻¹ = φ (g⁻¹)` by `map_inv₀`, whose support ⊆ range emb = (1/n)ℤ,
   so Puiseux with the SAME ramification `n`. `f = 0` needs no special case
   (`g = 0`, `φ 0 = 0`, `0⁻¹ = 0`).
3. `puiseuxSubfield (K) [Field K] : Subfield (HahnSeries ℚ K)` + `mem_puiseuxSubfield`
   (`Iff.rfl`). Upgrades `puiseuxSubring`/`puiseuxSubalgebra` — "the Puiseux series
   form a field" is now a machine-checked substructure fact.

**Technique / gotchas:**
- `embDomainRingHom [NonAssocSemiring R] (f : Γ →+ Γ') hfi hf` has `R` IMPLICIT —
  writing `embDomainRingHom φ₀ hfi hmono x` with `x`'s type unpinned gives a stuck
  `Zero ?R` typeclass error. Annotate `x : HahnSeries ℤ K` (or `(R := K)`).
- The OrderEmbedding underlying `embDomainRingHom φ₀ hfi hmono` is literally
  `⟨⟨φ₀, hfi⟩, hmono _ _⟩`; defining `emb` as that exact term makes
  `embDomainRingHom φ₀ hfi hmono x = embDomain emb x` hold by `rfl`.
- `φ₀ : ℤ →+ ℚ`, `k ↦ (k:ℚ)/(n:ℚ)`: `map_add'` via `push_cast; ring`; monotone via
  `div_le_div_iff_of_pos_right hn0` + `Int.cast_le`; injectivity for free from the
  order-iff (`le_antisymm`).
- `Set.IsPWO.mono (fun k hk => hk)` transports the anonymous preimage-series support
  into `emb ⁻¹' f.support` by defeq (both unfold to `{k | f.coeff (emb k) ≠ 0}`).
- Build: clean elaboration `[3070/3070]`, ONE real error first pass (the implicit-R
  stuck instance), fixed → clean 2nd attempt. No SIGBUS this session.

**Deferred (unchanged):** full Newton–Puiseux algebraic closure `IsAlgClosed (PuiseuxField K)`
still needs the Newton-polygon term-by-term convergence machinery absent from Mathlib
(>1000-line foundational build). The subfield statement is the natural terminus of the
"structural rounding-out" line — beyond it is only the deep convergence result.

**Files Modified:** proofs/Proofs/PuiseuxTheorem.lean (+Part X: 3 theorems + 1 def;
811→933 lines, 21→24 numbered theorems, 4→5 defs), meta.json counts synced.
