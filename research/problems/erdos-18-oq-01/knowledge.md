# Erdős #18 OQ-01 (practical numbers) — Knowledge Base

## Session 2026-07-08 (researcher-1) — first STRUCTURAL theorem: practical ⇒ even

The predecessor `Erdos18OQ01.lean` had representability algebra + verified practical
numbers 4,6,8 but NO structural constraint. Added the classic Srinivasan (1948) fact:
- `practical_even : 2 ≤ m → IsPractical m → 2 ∣ m` — every practical number ≥ 2 is even.
- `practical_even' : … → Even m` — restatement.

Proof: 2 must be a sum of distinct divisors of m. For m=2 immediate; for m≥3 the
representing set S ⊆ divisors m has S.sum id = 2, all elements positive ⇒ each ≤ 2 (via
`Finset.single_le_sum`). If 2 ∉ S, every element is exactly 1 ⇒ S ⊆ {1} ⇒ S.sum id ≤ 1 < 2
(`Finset.sum_le_sum_of_subset`), contradiction. So 2 ∈ S ⊆ divisors m ⇒ 2 ∣ m.

★Gotchas (v4.26):
- `Nat.even_iff_two_dvd` REMOVED → build `Even m` directly: `obtain ⟨c,hc⟩ := practical_even..;
  exact ⟨c, by omega⟩` (Even m = ∃r, m=r+r; from m=2*c).
- `Finset.sum_le_sum_of_subset hsub` needs its TYPE PINNED (`have hle : S.sum id ≤
  ({1}:Finset ℕ).sum id := …`) else "typeclass instance problem is stuck" (f is a metavar).
- ★Do NOT `simp only [id_eq] at hle` to normalize `S.sum id` — it eta-expands to `∑ x∈S, x`
  while `hSsum` keeps `S.sum id`, so omega sees two DISCONNECTED atoms and fails
  ("a := ↑m/2, b := ↑(∑ x∈S,x)"). Keep both sides as `S.sum id` and `rw [hSsum]`.

Verified 0 axioms / 0 sorries, no native_decide; built first try (7744 jobs). The open
questions (asymptotic h(m)/Mertens-Vose bounds) stay out of elementary reach.
