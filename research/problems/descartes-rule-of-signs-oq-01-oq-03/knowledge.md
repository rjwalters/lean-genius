# Knowledge Base: descartes-rule-of-signs-oq-01-oq-03

## Session 2026-07-09 (researcher-2) — AXIOM ELIMINATION on base file (8→7)

**Mode**: AXIOM HUNT (RICH family, score 20). My slug's on-target file
`DescartesRuleOfSignsOQ01OQ03.lean` (871 lines, 30 thm) is saturated (r6 §7 invariances).
Pivoted to the family's base `DescartesRuleOfSigns.lean`, which carried 8 axioms including
three CONCRETE `example_*` "axioms" that are not deep results at all.

**Discharged `x_cubed_minus_x_positive_roots_axiom` → theorem** (`countPositiveRoots (X³-X)=1`):
factor `X³−X = X(X−1)(X+1)`, compute `.roots` via Mathlib `roots_mul`/`roots_X`/`roots_X_sub_C`
= `{0,1,−1}`, filter `(· > 0)` leaves `{1}`, card 1. **Self-contained (pure Mathlib root API, no
downstream helper) so it discharges IN the base file** — base axiomCount 8 → 7. `#print axioms`
= `[propext, Classical.choice, Quot.sound]` only. Kept the `_axiom` name (now a theorem) so the
wrapper `x_cubed_minus_x_positive_roots` still resolves.

Recipe: `hpe : X + C 1 = X - C (-1) := by rw [map_neg, sub_neg_eq_add]` to reuse `roots_X_sub_C`
for the `(X+1)` factor; nonzero side-conditions via `X_ne_zero` / `X_sub_C_ne_zero` /
`mul_ne_zero`; finish `simp only [Multiset.filter_add, Multiset.filter_singleton]; norm_num`.

**The other two concrete axioms** `example_x2_minus_1_sign_changes` (=1) and
`example_x2_plus_1_sign_changes` (=0) are ALSO not deep — they are already PROVED axiom-free
downstream in `DescartesRuleOfSignsOQ01OQ03.lean` (~lines 481/502) using its
`countSignChanges_three_mid_zero_pos/zero` helpers. They persist in the base ONLY because
`signChangesInCoeffs` is noncomputable (classical `Fin n × Fin n` filter) and the base file
cannot import the downstream helpers (circular). Eliminating them at the base needs the Fin-3
enumeration helpers copied in, or the base `axiom`+local `example` simply deleted (nothing outside
depends on them). ACTIONABLE next: either inline the two helpers to prove them in the base, or
delete the redundant base axioms — base would then reach 5 axioms (the remaining 5 —
`descartes_upper_bound`, `descartes_parity`, `descartes_negative_roots`,
`alternating_signs_max_roots`, `derivative_reduces_sign_changes` — are the genuinely deep
Descartes-proof content).

**Verification (docker DOWN — containerd meta.db/blob I/O, NOT disk).** Direct `lean` elab vs
pinned Mathlib v4.26.0 (see [[reference-docker-down-lean-elab-verification-path]]): exit 0, only
2 pre-existing `unused variable hp` warnings. Meta `descartes-rule-of-signs` synced 8→7 axioms.

## Session 2026-07-11 (researcher-1) — §9 reflection complementarity (Descartes for negative roots)

**Mode**: ACT (SOLVED-side; frontier extension). The invariance family §7/§8 covered
scaling, negation, reversal, positive-dilation `p(cX)` (c>0) — all of which FIX V — but
the **reflection `p(-X)`** (which sends positive↔negative roots, the transformation
behind Descartes for negative roots) was absent. It does NOT preserve V; instead there
is a sharp complementarity.

**Added to `DescartesRuleOfSignsOQ01OQ03.lean` (4 theorems, VERIFIED 0-axiom
`{propext, Classical.choice, Quot.sound}`, host `lake env lean` EXIT 0):**
- `countSignChanges_nowhere_zero` : for nowhere-zero f, the sign-change set = adjacent
  pairs (i,i+1) with f i·f(i+1)<0 (no zeros to skip over → SignChangeBetween ⟺ adjacent+opp).
- `card_adjacent` : `#{(i,j) : j=i+1}` in Fin n × Fin n = n-1 (card_bij' to range(n-1)).
- `countSignChanges_alternate_add` : **V(f) + V(alt f) = n-1** for nowhere-zero f, where
  alt f i = (-1)^i f i. Core: on an adjacent pair, (alt f)i·(alt f)(i+1) = -(f i·f(i+1)),
  so opp-sign test holds for EXACTLY one of f, alt f → the two sign-change sets partition
  the n-1 adjacent gaps (`Finset.filter_card_add_filter_neg_card_eq_card`).
- `signChangesInCoeffs_comp_neg_X_add` : **V(p) + V(p(-X)) = deg p** for gap-free p (all
  coeff 0..deg nonzero). Bridge: (p(-X)).coeff k = (-1)^k coeff k via `comp_C_mul_X_coeff`
  at c=-1 (`-X = C(-1)*X`); reflected coeffSequence = (-1)^d · alt(coeffSequence p), global
  (-1)^d factor killed by `countSignChanges_const_smul`, then alternate_add (n=d+1, n-1=d).

**Key API / GOTCHAs**:
- `comp_C_mul_X_coeff` : (p.comp(C c*X)).coeff k = c^k·p.coeff k (reused from §7's dilation).
- Exponent identity `(-1)^(d-i) = (-1)^d·(-1)^i` (i≤d): via (-1)^i squared = 1
  (`Even.neg_one_pow`) + pow_add on (d-i)+i=d.
- ★`fun i => ... cp i` where cp:Fin(d+1)→ℝ and `(i:ℕ)` coercion present: MUST annotate
  binder `fun (i : Fin (d+1)) => ...` else Lean infers i:ℕ from the coercion and `cp i` fails.
- ★card_bij' mapsTo: prove `i.val < n-1` as a SEPARATE `have hlt := by omega` then
  `mem_range.mpr hlt` — `mem_range.mpr (by omega)` fails (omega can't see hyps through the
  dependent bij-function goal).

### Terminus (unchanged)
Transformation family now complete. Remaining open work is the deep (B1)-(B3) Sturm/Descartes
comparison (structure-encoded assumptions in SturmReduction), genuinely multi-week.

## Session (researcher-1, 2026-07-11): general quadratic sign-change count (§12)

**Mode**: REVISIT (RICH, already SOLVED 0/0) · **Outcome**: progress (6 theorems VERIFIED
0-sorry/0-axiom), branch research/descartes-oq0103-quadratic-family, PR #38202.

**Contribution.** Closed the standing next-step "full Fin 3 sign-change count for
quadratics aX²+bX+c with nonzero middle term". §4 only handled three HARDCODED
polynomials; §12 generalises to the whole 3-parameter family:
- `coeffSequence_quadratic (ha:a≠0)`: coeffSequence (C a*X^2+C b*X+C c) 2 = ![a,b,c].
  Proof: `funext i; fin_cases i <;> simp [coeffSequence, coeff_add, coeff_C_mul_X_pow,
  coeff_C_mul_X, coeff_C]`.
- `signChangesInCoeffs_quadratic (ha)`: = countSignChanges ![a,b,c]. Uses Mathlib
  `natDegree_quadratic ha` (poly form C a*X^2+C b*X+C c is EXACTLY Mathlib's
  Degree/SmallDegree form) + dif_neg + coeffSequence_quadratic.
- Four sign-pattern corollaries reusing the §2¾ Fin 3 lemmas via `by simpa using h`
  (simp rewrites ![a,b,c] 0/1/2 to a/b/c): alternating→2, one_left→1, one_right→1,
  no_change→0 (needs b≠0). Complete classification for nonzero middle.

The nextStep "replace example_x2_*_sign_changes axioms in base file" is STALE/DONE — the
base DescartesRuleOfSigns.lean already has them as theorems (line 312/332, "Formerly an
axiom; now discharged"). Base file's remaining 5 axioms are the DEEP Descartes facts
(upper_bound/parity/negative_roots/alternating_max/derivative_reduces) — not routine.

**Build**: docker-build GREEN first try (3064 jobs). 51→57 theorems.

**Reusable technique**: to lift a hardcoded coefficient computation to a parametric
polynomial family, prove the `coeffSequence p natDegree = ![...]` identity once (funext +
fin_cases + coeff_* simp set), then every downstream count is `rw [signChanges_quadratic];
apply <Fin n lemma> (by simpa using hyp)`.
