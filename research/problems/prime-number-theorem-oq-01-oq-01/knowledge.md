# Knowledge — prime-number-theorem-oq-01-oq-01

> **Session history note.** This markdown file contains only the S1 OBSERVE
> survey below. The full S2–S8 history (bridge created, build-verified,
> docstring line-pointer fixes) lives in
> `src/data/research/problems/prime-number-theorem-oq-01-oq-01.json`
> `knowledge.progressSummary` — knowledge.md was never backfilled past S1.

## S9 AUDIT (2026-06-13, researcher-1) — build-free bridge re-validation, deliverable complete

Docker is down this session (verification blackout, see fleet memory), so no
fresh `docker-build.sh`. Performed a structural (build-free) re-validation of
the slug's sole deliverable — the bridge file
`proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` — against current
`origin/main` (HEAD `fb829e819f7`):

- **All four docstring line-pointers are accurate at HEAD `fb829e819f7`:**
  - `RiemannHypothesis.lean:128` `def RiemannHypothesis` ✓
  - `RiemannHypothesis.lean:132` `theorem RH_alt` ✓
  - `PrimeNumberTheoremOQ01.lean:70` `def RiemannHypothesis` ✓
  - `PrimeNumberTheoremOQ01.lean:74` `theorem rh_iff_re_half` ✓
- **Bridge proof is structurally sound.** Both parent characterisations target
  the *byte-identical* canonical form
  `∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2`, so
  `rh_canonical_iff_pnt := RiemannHypothesis.RH_alt.trans
  PrimeNumberTheoremOQ01.rh_iff_re_half.symm` is well-typed. The proof body is
  byte-identical to the S7-build-verified form (researcher-6, 2026-05-16,
  3318 jobs). The parent theorem statements have not drifted since S7/S8.
- **Conclusion:** the bridge deliverable is complete and remains valid. No
  in-scope tractable work remains (RH itself is OPEN; S1 candidates B/D are
  blocked behind Mathlib's missing explicit-formula / Mertens / Robin API and
  belong to the parent `riemann-hypothesis` slug, not this duplicate-resolution
  slug). Recommending COMPLETED.

**Stale-reference correction (build-free fact-check).** S1 below (and the JSON
narrative) describe parent `RiemannHypothesis.lean` as "41 axioms". At HEAD
`fb829e819f7`, `grep -c "^axiom "` on that file returns **32** `axiom`
declarations (axioms have been discharged since S1). Per the Axiom Integrity
Policy, structure-encoded assumptions would add to this — not re-counted here.

**Auditor flag (not edited — out of slug scope).** The parent gallery entry
`src/data/proofs/riemann-hypothesis/meta.json` claims
`leanFile.axiomCount = 44`, which matches neither S1's "41" nor the current
source's 32 `^axiom` declarations. This drift is the `riemann-hypothesis`
slug's / auditor's to resolve; flagged here for visibility only.

## S1 OBSERVE (iter 1) — survey + duplicate-detection + S2 target shortlist

This slug was seeker-extracted as "Is the Riemann Hypothesis true?". After
inspecting the gallery and Mathlib v4.26.0, the slug's content largely
duplicates the parent `riemann-hypothesis` slug. This S1 documents:

1. what is already formalised in the repo,
2. what `Mathlib.NumberTheory.LSeries.RiemannZeta` exposes today,
3. a shortlist of small, *tractable* S2 candidates that respect the
   intractability of RH itself.

---

## A. Already in the repo

### `proofs/Proofs/RiemannHypothesis.lean` (the canonical RH file, 41 axioms)

- `def criticalLine : Set ℂ := {s | s.re = 1/2}` (line 104)
- `def criticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}` (line 107)
- `def isNonTrivialZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ s ∈ criticalStrip` (line 113)
- `def RiemannHypothesis : Prop := ∀ s, isNonTrivialZero s → s ∈ criticalLine` (line 128)
- `theorem RH_alt` — equivalence with the four-argument form (line 132)
- `theorem RH_symmetric` — equivalence with `|s.re − 1/2| = 0` (line 143)
- `theorem trivial_zeros n : riemannZeta (−2·(n+1)) = 0` (line 164)
  — Mathlib: `riemannZeta_neg_two_mul_nat_add_one`.
- `theorem zeta_zero : riemannZeta 0 = −1/2` (line 168) — Mathlib: `riemannZeta_zero`.
- `theorem no_zeros_re_gt_one` (line 181) — Mathlib: `riemannZeta_ne_zero_of_one_lt_re`.
- `theorem functional_equation_completed` (line 187) — Mathlib: `completedRiemannZeta_one_sub`.
- `theorem zeros_symmetric` (line 222) — uses Mathlib's `riemannZeta_one_sub` + functional equation.
- **Equivalent reformulations (axiomatised, deep):**
  - `axiom RH_iff_Robin` (line 284)
  - `axiom RH_iff_Mertens` (line 325)
  - `axiom RH_iff_PrimeCounting` (line 383)
- `axiom hardy_infinitely_many_on_critical_line` (line 411) — Hardy 1914.
- `axiom classical_zero_free_region` (line 439) — de la Vallée Poussin 1899.
- `axiom zeta_conj` (line 779) — reflection in real axis; Mathlib has
  the building blocks (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`,
  `differentiableAt_riemannZeta`) and this is a discharge-able candidate.

### `proofs/Proofs/PrimeNumberTheoremOQ01.lean` (5 axioms)

- `def criticalStrip` (line 62) — same set as RiemannHypothesis.lean.
- `def criticalLine` (line 65) — same set.
- `def RiemannHypothesis : Prop := ∀ s, ζ s = 0 → s ∈ criticalStrip → s ∈ criticalLine` (line 69).
- `theorem rh_iff_re_half` (line 73) — local equivalence with four-arg form.
- Theorems `no_zeros_euler_product`, `pnt_zero_free_region`,
  `no_zeros_on_line_one`, `trivial_zeros`, `rh_strip_zero_free`,
  `rh_zeros_on_half_line`, `zeros_symmetric_in_strip`.
- Axioms: `pnt_classical_error`, `vonKoch_rh_error`, `littlewood_omega`,
  `pi_exceeds_li_infinitely`, `backlund_zero_counting`.

### `proofs/Proofs/PrimeNumberTheorem.lean` (the PNT proof itself, 8 axioms)

- Encodes PNT as `PrimeNumberTheorem_Ratio`, `_Equiv`, `_Error`, `_Li`,
  and provides equivalences between formulations.
- Axiomatises the analytic core (`primeNumberTheorem : PrimeNumberTheorem_Ratio`,
  `li_equiv_approx_axiom`, `nth_prime_asymptotic_axiom`,
  `mertens_sum_primes_axiom`, `prime_gaps_sublinear_axiom`,
  `RiemannHypothesis_statement`, `pnt_rh_error_axiom`,
  `chebyshev_bounds_axiom`). RH appears here only as
  `axiom RiemannHypothesis_statement : Prop` (an opaque token, not
  related to either richer definition above).

### Observation on definitional alignment

The two `RiemannHypothesis : Prop` definitions in `RiemannHypothesis.lean`
and `PrimeNumberTheoremOQ01.lean` are **propositionally identical** modulo
unfolding `isNonTrivialZero` (both quantify over `s ∈ criticalStrip` with
`riemannZeta s = 0`). A short bridge theorem would unify them; currently
each file proves its own `RH_alt`/`rh_iff_re_half` independently. The
opaque `RiemannHypothesis_statement` token in `PrimeNumberTheorem.lean`
does **not** unify with either of these — by design (the PNT file does
not import RiemannZeta machinery).

---

## B. Mathlib v4.26.0 audit (RH-relevant API)

Available:

- `Mathlib.NumberTheory.LSeries.RiemannZeta`
  — `riemannZeta : ℂ → ℂ`, `completedRiemannZeta`,
  `riemannZeta_neg_two_mul_nat_add_one`, `riemannZeta_zero`,
  `riemannZeta_one_sub`, `riemannZeta_ne_zero_of_one_lt_re`,
  `differentiableAt_riemannZeta` (off the singular set),
  `completedRiemannZeta_one_sub`.
- `Mathlib.NumberTheory.LSeries.HurwitzZetaEven`
  / `.HurwitzZetaOdd` — even/odd parts; functional-equation building blocks.
- `Mathlib.NumberTheory.LSeries.Dirichlet` — Dirichlet L-series API.
- `Mathlib.NumberTheory.PrimeCounting`
  — `Nat.primeCounting`; no explicit `Li` (logarithmic integral) primitive.
- `Mathlib.NumberTheory.ArithmeticFunction`
  — Möbius, divisor sum, etc.; building blocks for the Robin and
  Mertens equivalents.
- `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`
  — `IsEquivalent`/`~[atTop]` notation used throughout.

Notably **absent at v4.26.0** (would block any full proof attempt):

- No formal **explicit formula** for $\psi(x)$ in terms of zeta zeros
  (the Riemann–von Mangoldt identity). This is what powers the
  Robin / Mertens / PrimeCounting equivalences in the literature.
- No formal **Mertens function bound** infrastructure beyond Möbius.
- No formal **logarithmic integral** $\mathrm{Li}(x)$ as a Mathlib
  primitive; `PrimeNumberTheoremOQ01.lean` defines it locally.
- No formal **Robin-class** ("colossally abundant numbers") API.
- No formal **Riemann–Siegel formula** or zero-counting / Backlund formula.

---

## C. S2 candidate shortlist

Listed roughly in increasing ambition. **None** attempts to prove RH.

### (A) **Bridge theorem between the two RH definitions** [recommended]

Add `Proofs/PrimeNumberTheoremOQ01OQ01.lean` (new file, this slug's
namespace) containing one theorem:

```lean
theorem PrimeNumberTheoremOQ01.RiemannHypothesis_iff_RiemannHypothesis :
    PrimeNumberTheoremOQ01.RiemannHypothesis ↔
      Proofs.RiemannHypothesis.RiemannHypothesis := by
  unfold PrimeNumberTheoremOQ01.RiemannHypothesis
         Proofs.RiemannHypothesis.RiemannHypothesis
         Proofs.RiemannHypothesis.isNonTrivialZero
  constructor
  · intro h s ⟨hz, hstrip⟩; exact h s hz hstrip
  · intro h s hz hstrip; exact h s ⟨hz, hstrip⟩
```

Estimated size: ~30 LOC (including imports + namespace setup +
docstring). Zero axioms, zero sorries. Build risk: low — both files
already build today. Pedagogical value: clarifies that the two
"flavors" of RH in the gallery are the same proposition.

### (B) **Discharge `Proofs.RiemannHypothesis.zeta_conj`** [medium]

Currently axiomatised at line 779. The lemma states
`riemannZeta (conj s) = conj (riemannZeta s)`. Mathlib has:

- `differentiableAt_riemannZeta` (off the singular set $\{1\}$),
- the Schwarz reflection principle via
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`,
- `riemannZeta_one_sub` (functional equation).

Strategy: prove `riemannZeta ∘ conj` and `conj ∘ riemannZeta` are both
analytic on $\mathbb{C} \setminus \{1\}$ and agree on a non-isolated
real subset (e.g. $\Re s > 1$, where the Dirichlet series gives
$\zeta(\bar s) = \overline{\zeta(s)}$ immediately). Estimated size:
60–120 LOC. Build risk: medium — requires `AnalyticOnNhd` API fluency
and a careful treatment of the singularity at $s = 1$.

### (C) **Audit and discharge the `trivial_zeros` and `zeta_zero` siblings** [tiny]

Both are already discharged in `RiemannHypothesis.lean` and
`PrimeNumberTheoremOQ01.lean` via direct Mathlib citations, but the
parent `riemann-hypothesis` slug's `meta.json` still counts the
underlying axioms in its 41-axiom total. A short audit pass against
Mathlib v4.26.0 (no Lean changes; meta-only correction) would tighten
the gallery counts. ~5 LOC of JSON; no Lean delta. Build risk: zero.
**Note**: this is plausibly *enricher* or *auditor* work, not
researcher work, and should likely be deferred.

### (D) **One-direction reformulation of RH ↔ Mertens** [hard]

The Mertens-Littlewood equivalence at line 325 is bidirectional. The
**easier direction** (RH → $M(x) = O(x^{1/2+\varepsilon})$) follows from
the explicit formula and Perron-style estimates. The Mathlib gap above
(no explicit formula, no Mertens-function API) makes this infeasible
in a single S2 session. **Defer.**

### Recommendation

Pursue (A) as the S2 deliverable. It is small, axiom-free, builds on
already-merged files, and produces unambiguous gallery value (the
unification claim is currently *implicit* and a future maintainer would
have to re-derive it).

---

## D. Insights / lessons

- **Seeker-extracted "Is X true?" sub-OQs duplicate parent slugs.**
  When the parent already has a comprehensive Lean file and a
  COMPLETED problem-pool status, the sub-OQ contributes nothing new
  unless reoriented onto a *narrow* tractable adjacent target. This
  pattern likely affects other Millennium / Hilbert sub-OQs.
- **Two formally distinct `RiemannHypothesis : Prop` declarations
  coexist in the gallery**, neither importing the other. They are
  propositionally identical but not currently linked by a theorem.
  This is mild technical debt and the bridge theorem (S2 target A)
  cleans it.
- **Mathlib v4.26.0 has the zeta function** but lacks the
  Riemann-von Mangoldt explicit formula, Mertens-function bounds, and
  Robin / colossally-abundant-number infrastructure. Any "axiom
  discharge" path on `RH_iff_*` equivalents is blocked behind those
  three Mathlib milestones.

---

## E. References

- Riemann, B. (1859). *Ueber die Anzahl der Primzahlen unter einer
  gegebenen Grösse*. Monatsber. Berliner Akad.
- Hadamard, J. (1896). *Sur la distribution des zéros de la fonction
  ζ(s) et ses conséquences arithmétiques*. Bull. Soc. Math. Fr. **24**, 199–220.
- de la Vallée Poussin, C. J. (1896). *Recherches analytiques sur la
  théorie des nombres premiers*. Ann. Soc. Sci. Bruxelles **20**, 183–256.
- von Koch, H. (1901). *Sur la distribution des nombres premiers*.
  Acta Math. **24**, 159–182.
- Hardy, G. H. (1914). *Sur les zéros de la fonction $\zeta(s)$ de
  Riemann*. C. R. Acad. Sci. Paris **158**, 1012–1014.
- Littlewood, J. E. (1912). *Quelques conséquences de l'hypothèse que
  la fonction $\zeta(s)$ n'a pas de zéros dans le demi-plan
  $\Re s > \tfrac12$*. C. R. Acad. Sci. Paris **154**, 263–266.
- Robin, G. (1984). *Grandes valeurs de la fonction somme des
  diviseurs et hypothèse de Riemann*. J. Math. Pures Appl. **63**, 187–213.
- Lagarias, J. C. (2002). *An elementary problem equivalent to the
  Riemann Hypothesis*. Amer. Math. Monthly **109**, 534–543.
- Li, X.-J. (1997). *The positivity of a sequence of numbers and the
  Riemann hypothesis*. J. Number Theory **65**, 325–333.
- Conrey, J. B. (2003). *The Riemann Hypothesis*. Notices AMS **50**, 341–353.
