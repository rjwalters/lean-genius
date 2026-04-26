# Knowledge Base: binomial-theorem-oq-02-oq-01-oq-01-oq-01

**Problem**: Can the Fintype instance for Composition be proved efficiently using piAntidiag?

**Status**: COMPLETE — 0 sorries, 0 axioms.

---

## Session 2026-04-26 (Session 1) — Fintype Instance via piAntidiag

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Claimed the problem as a FRESH pick (score 0, first session)
- Identified the sorry in `BinomialTheoremOQ02OQ01OQ01.lean` line 51
- Discovered `Finset.mem_piAntidiag` uses `∀ i, f i ≠ 0 → i ∈ s` (not `∀ i ∉ s, f i = 0`)
- Wrote `BinomialTheoremOQ02OQ01OQ01OQ01.lean` with 7 theorems, 0 sorries
- First build had 2 errors (API mismatch + pipe syntax), fixed in one round
- Second build: succeeded cleanly

### Key Findings
- `Finset.mem_piAntidiag` characterizes membership as: `f ∈ s.piAntidiag n ↔ ∑ i ∈ s, f i = n ∧ ∀ i, f i ≠ 0 → i ∈ s`
- `Composition.counts_outside : ∀ a ∉ s, f a = 0` is logically equivalent but syntactically different — requires `by_contra` conversion
- Lean 4 has definitional proof irrelevance: `rfl` closes `⟨f, ha1, ha2⟩ = ⟨f, hb1, hb2⟩` after `subst`
- `Fintype.ofEquiv` takes 2 lines after the bijection; actual proof far shorter than ~50 line estimate
- `|>.card` pipe syntax doesn't work; use `((s.piAntidiag n)).card` directly

### Files Modified
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01.lean` (new, 185 lines, 0 sorries)
- `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-01/meta.json` (new)

### Results
- `compositionEquiv`: bijection `Composition α s n ≃ ↥(s.piAntidiag n)`
- `instFintypeComposition`: Fintype instance in 2 lines
- `card_composition_zero`: unique composition of 0
- `dice_six_rolls_all_different`: multinomial({0..5},1) * 1 = 6! (native_decide)
- `sum_composition_eq_piAntidiag_sum`: sum transfer via bijection

### Next Steps
The remaining sorries in `BinomialTheoremOQ02OQ01OQ01.lean` are:
- `multinomialPMF_sum_eq_one`: ENNReal normalization — now feasible via `sum_composition_eq_piAntidiag_sum` + `Finset.sum_pow_eq_sum_piAntidiag`
- `multinomial_marginal_binomial`: more complex, involves piAntidiag fiber arguments
- `multinomial_mean`, `multinomial_covariance`: statistical theory
