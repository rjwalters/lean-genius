# Knowledge Base: erdos-131-oq-01-oq-01

OQ: determine the exact growth rate of F(N) (Erdős #131, non-dividing sets) — is it
`N^{1/5+o(1)}` or some other power?

---

## Session 2026-06-15 (S1) — FRESH OBSERVE (build-free; Docker + Aristotle blackout)

**Mode**: FRESH · **Outcome**: OBSERVE — pinned the exact object, computed verified
exact values `F(1..54)`, laid out the rigorous bound landscape, and gave an HONEST
negative meta-finding: the exponent is empirically inaccessible at computable N. No
growth-exponent claim is made (that would be unsupportable from small N). No Lean file
written (build-gated; the OQ is a hard open asymptotic, not a wiring task).

### The exact object (matches the Lean parent)

`IsNonDividing A` (Erdos131Problem.lean:47): `∀ a ∈ A, ∀ S ⊆ A.erase a, |S| ≥ 2 →
¬(a ∣ S.sum)`. `F N` (line 109) = max card of a non-dividing `A ⊆ Icc 1 N`. Note the
condition is over EVERY ≥2-element subset of the others (not just the sum of all
others), so it is the *strong* non-dividing notion. Consequences pinned:
- `1 ∈ A` forces `|A| ≤ 2` (1 divides every sum, so no ≥2-subset may coexist).
- Witnesses: `{2,4,5}` is non-dividing; `{2,3,4}` is not (3 ∣ 2+4).

### Verified exact values (certificate `verify_Fn.py`, two independent methods agree)

Computed two ways — brute force over all ≥2-subsets, and a residue-class DP tracking
size-1 vs size-≥2 reachability mod `a` — which **agree on F(1..30)** (internal
cross-validation, guards the predicate against off-by-one). DP extends to N=54:

    F(1..54) = 1 2 2 2 3 3 3 3 3 4 4 4 4 4 4 5 5 5 5 5 5 5 5 5 5 5 5 5 5 6
               6 6 6 6 6 6 6 6 6 6 6 6 7 7 7 7 7 7 7 7 7 7 7 7

    smallest N with F(N)=k:  F=1→N=1, 2→2, 3→5, 4→10, 5→16, 6→30, 7→43

(NOTE: an OEIS A068063 cross-check — referenced by the parent meta — is PENDING;
oeis.org returned HTTP 403 to the fetcher this session. The two-method internal
agreement is the integrity anchor instead. A future session with OEIS access should
confirm whether A068063 uses this exact ≥2-subset variant or the "sum of all others"
variant; the values above are unambiguous for the Lean `IsNonDividing` definition.)

### Rigorous bound landscape (NOT closed by this session)

    exp(c·√log N)   ≤   F(N)   ≤   N^{1/4 + o(1)}

- Lower: Straus, `exp(c√log N)` (sub-polynomial). Improving it to polynomial would
  need fundamentally new large-non-dividing-set constructions (open).
- Upper: Pham–Zakharov (2024), `N^{1/4+o(1)}`, via the non-averaging connection
  (`IsNonDividing ⟹ IsNonAveraging`, proven in the parent at line 95). This refuted
  the original Erdős guess `F(N) > N^{1/2-o(1)}` (answer: NO).
- The OQ's `N^{1/5}` is one guess inside the wide `[exp(c√log N), N^{1/4}]` window;
  whether `F` is even a clean power (`N^{θ+o(1)}`) vs genuinely intermediate growth
  is itself open.

### Honest negative meta-finding (why small N can't help)

The finite-N effective exponent `log F(N)/log N` at the thresholds:

    F=3 @N=5: 0.683   F=4 @10: 0.602   F=5 @16: 0.580
    F=6 @30: 0.527    F=7 @43: 0.517   (and ≈0.49 at N=54)

It decreases only glacially and at N=54 is still ≈0.49 — about **double** the proven
asymptotic ceiling 1/4, and nowhere near the conjectured 1/5 = 0.20. So the lower-order
terms dominate completely at every computable N: brute small-N computation provably
cannot distinguish `N^{1/5}` from `N^{1/4}` from `exp(c√log N)`. Any "empirical exponent
fit" here would be misleading — the OQ is not attackable by enumeration.

### Decision / where the real progress is

This OQ is a genuine open asymptotic; build-free computation does not move it. The only
honest formalization targets (for a Docker-up session) are *infrastructure*, not the OQ:
1. A decidable instance / `native_decide`-friendly reformulation of `IsNonDividing` and
   small `F(N)` values as certified gallery facts (the values above).
2. Formalizing the `IsNonDividing ⟹ IsNonAveraging` bridge is already done (parent:95);
   the Pham–Zakharov upper bound itself is far out of formalization reach.
Recommend: keep this OQ as a documented hard-open with the verified `F(1..54)` table;
do NOT spawn enumeration-theater sessions chasing the exponent.

---

## Dead Ends

- **Empirical exponent fitting**: ruled out as dishonest — effective exponent at N=54 is
  ~0.49, dominated by lower-order terms; cannot resolve 1/5 vs 1/4 vs sub-polynomial.
- **OEIS fetch** (oeis.org/A068063): blocked by HTTP 403 this session; use an
  authenticated/MCP fetch or local OEIS mirror next time.
