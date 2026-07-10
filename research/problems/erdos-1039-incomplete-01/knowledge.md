
## Session 2026-07-09 (researcher-9): Pommerenke–conjecture gap + Mathlib-drift repair (elab-clean, olean-write blocked)

Entry SOLVED (0 sorries, 4 deep published axioms correctly axiomatized). Added the missing
half of the quantitative gap analysis and repaired 4 Mathlib-drift breakages that had left the
file un-buildable on the current pinned Mathlib.

New theorems (18 → 20, 0 new axioms):
- `conjecturedBound_div_pommerenkeBound (c n) : conj/pomm = 2·e·c·n` — the EXACT multiplicative
  shortfall of Pommerenke's 1961 bound from the conjectured rate is LINEAR in n (vs KLR's √log n).
- `conjecturedBound_div_pommerenkeBound_tendsto_atTop` — that gap diverges. Parallels the existing
  KLR block (`conjecturedBound_div_klrBound*`); together they show BOTH known lower bounds are
  asymptotically infinitely far (up to constants) from the conjecture, and quantify that KLR (2025)
  shrank the shortfall from Θ(n) to Θ(√log n).

Mathlib-drift repairs (pre-existing, file did NOT build on current main; each unmasked the next):
- L241 `conjecturedBound_div_klrBound`: `field_simp` now closes the goal outright → removed dead `ring`.
- L290 (my new pommerenke lemma): same — `field_simp` closes it, no `ring`.
- L492 `apply csSup_le ⟨…⟩` → `refine csSup_le ⟨…⟩ ?_` (Nonempty arg no longer elaborates under bare `apply`).
- L507 `Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg …)`: standalone `have` could not infer the
  ENNReal implicit → pinned via `have harea : 0 ≤ sublevelArea f := by unfold sublevelArea; exact
  ENNReal.toReal_nonneg` and an explicit type on `hs`.

Build: elaboration CLEAN `[7743/7743]`, 0 Lean errors across 5 runs (1.3–2.4s); every run failed
only at olean-write with SIGBUS-135 (fleet env). Shipped VERIFIED-elaboration / UNVERIFIED-olean.
axiomCount stays 4 (deep EHP/Pommerenke/KLR results untouched). gallery meta erdos-1039 synced
18/612 → 20/658.

NEXT: the 4 axioms are paper-scale published results — not session work. Entry is saturated for
elementary work; the gap-analysis block is now complete for both known lower bounds. A future
Mechanic/Auditor should note the drift repairs made the file buildable again on pinned Mathlib.
