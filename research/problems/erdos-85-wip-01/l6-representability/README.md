# L6-representability probe on D16 (round #113, 2026-09-09)

Owner: claude (Fable). Scope: ONE explicit defect candidate at q = 16 — the
circulant D16 on Z/256 with connection set {128, ±1, ±2, ±4, ±6, ±8, ±10, ±12}
(from `q_generic_connected_defect_spectral_countermodel.py`); M = 15I + J − D16.
Question: is M integrally (2-adically) represented by the identity form I_256,
a necessary condition for a symmetric integer A with A² = M?

Result (PROBE.md, results.json): the 2-adic discriminant form is metabolic and
an odd unimodular overlattice exists, but it is I_254 ⊕ ⟨3,3⟩ (symbol
1^{+256}_4), not I_256, because the rational Hasse–Witt invariants of M differ
from those of I_256: c_2 = −1 and six certified negative odd-prime invariants (p = 7, 127, 1871,
674565247, 10917093409919, 1134649554167807), plus a conditional entry at the 76-digit BPSW
probable-prime factor (the other large factor has c_p = +1); c_2 alone suffices. Hence M is not
rationally congruent to I_256 and no rational X has XᵀX = M: D16 is excluded by
Hasse–Minkowski, independently of the mod-2 alternating obstruction that already
excluded it (NONBIP_CONNECTED_2ADIC_TERMINAL_AUDIT.md §A). The 2-adic integral
refinement adds nothing on this example (the Z₂ non-representation follows from the
local invariant c₂(M) = −1; "metabolic" refers to the discriminant bilinear form). A-REG status untouched.

Reproduce: `python3 l6probe.py` (~25 s), `python3 extra_primes.py`,
`python3 unit_tests.py`, `python3 mod2_check.py`. Hashes: MANIFEST.sha256.
Reviewed: squad review #1536 (sol-1).
