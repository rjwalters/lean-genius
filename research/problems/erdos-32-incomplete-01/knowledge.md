# erdos-32-incomplete-01
## Erdős #32: Additive Complements of Primes — Fixed and proved no_suboptimal_log_density

**Status: SURVEYED/PARTIAL** — Fixed syntax errors, proved the one `sorry` theorem. Axioms remain for known results.

---

## Summary

`Erdos32Problem.lean` formalizes Erdős Problem #32: Is there a set A with |A ∩ [1,N]| = o((log N)²)
such that every large n = p + a with p prime, a ∈ A?

**Known results (axiomatized)**:
- Erdős (1954): ∃ A additive complement with O((log N)²) density
- Kolountzakis (1996): O((log N)(log log N)) achievable
- Ruzsa (1998): Lower bound liminf |A ∩ [1,N]|/log N ≥ e^γ ≈ 1.781

**Proved this session**:
- `no_suboptimal_log_density`: if C < e^γ, no additive complement has uniform density ≤ C·log N
- `goldbach_gives_partial_complement`: reformulation of Goldbach (already proved)
- `erdos_32_summary`: combines known results (proved via axioms)

**Open**: Erdős's $50 question — can O(log N) be achieved?

---

## Session Log

### Session 2026-04-03 (Session 1)
**Mode**: FRESH
**Outcome**: progress

**What Was Done**:
1. Fixed 4 syntax errors: floating docstrings `/--` with no following declaration → changed to `/-`
2. Proved `no_suboptimal_log_density`:
   - Set ε = (e^γ - C)/2 > 0
   - Use `Filter.frequently_atTop.mp` to extract N ≥ 2 from Ruzsa's `∃ᶠ` statement
   - `Real.log_pos` gives log N > 0 since N ≥ 2
   - `mul_lt_mul_of_pos_right` converts the contradiction to a numeric linarith goal

**Key Lean technique**:
- `rw [Filter.frequently_atTop] at hFreq; obtain ⟨N, hN_ge, hN_lower⟩ := hFreq 2`
  converts `∃ᶠ N in atTop, P N` to `∃ N ≥ 2, P N`
- `mul_lt_mul_of_pos_right (h : a < b) (hc : 0 < c) : a * c < b * c`
  (NOT `mul_le_mul_right` which is not an iff in current Mathlib)

---

## Key Mathematical Insights

1. **Proof structure of density lower bounds**: Extract specific N from `∃ᶠ` via
   `Filter.frequently_atTop`, then derive numerical contradiction via log N > 0.

2. **Open problem status**: The gap between O(log N · ω(N)) upper bound (Ruzsa) and
   Ω(e^γ · log N) lower bound (Ruzsa) remains unresolved. The optimal constant is
   unknown — is it e^γ or strictly larger?

3. **Floating docstrings**: `/-- ... -/` followed by another `/-- ... -/` or `/-`
   causes parse errors. The first `/--` expects a declaration to follow.
