# H3 / H5 evidence audit (2026-10-07)

Audit of what the H3 and H5 strata of the order-49 upper side actually rest on. Prompted by v8 stating
H3 is "excluded by an LRAT proof of its Lean-generated formula". Paths are relative to the repo.

## Verdict

- **H3: no SAT verdict or LRAT proof exists for either cell formula.** No H3 payload in Lean (no
  `include_str`, no deleted modules in history); the two cell formulas h3_t0 (03db81d1…) and h3_t1
  (db6e30ad…), 29,500 vars / 1,328,183 clauses, were materialized but never solved
  (`PHASE_B_H1_H3_INVENTORY_20260910.md`: "No SAT verdict is claimed"). Whole-scout Kissat runs on the
  four alternative scout CNFs (b1, c1, c2, dist2) ended `s UNKNOWN` after ~12 h.
- **H3 rests on** a reviewed paper argument: graph-to-core reductions plus exhaustive, independently
  replayed Python enumerations (`Q7_H3_PROFILE_EXCLUSION_20260910.md`; reviews 1664/1666/1668/1673/
  1683/1674/1679/1680/1681, combined review 1685). That note says it is "not yet a Lean kernel theorem"
  and that "no new LRAT payload… is claimed".
- **Lean side of H3:** the graph normalization/cover is proved (`threeHighCanonicalGraphCover_all`,
  `Erdos85ThreeHighOneFiber.lean`; scout covers B1/C1/C2 normalization). Every Lean route to
  `OrderFortyNineStratumExcluded 3` still takes the SAT exclusions as **undischarged hypotheses**
  (`…_three_of_tripleCells`, `…_three_of_lratChecks` in `Erdos85SmallHighCnfExclusion.lean`, the
  cube-grid and scout-dichotomy terminals). Closing H3 in Lean needs either two `LRAT.check` facts for
  the canonical cells or four `Unsat` facts for the scouts.
- **Source of the error:** `STRATA_AND_SMALL_ORDERS_20260928.md` line 18 said "checked LRAT proofs for
  both cells", citing two notes that do not support it. Corrected in place 2026-10-07.
- **H5:** v8's wording (reviewed reductions with independently checked finite computation; no SAT
  certificate; three Boolean-exclusion premises undischarged in Lean) is accurate. Reviews 2037 (T0),
  2032 (T1), 2062/2063 (T2), outer 2065.

## Consequence for the paper

H3 belongs with H5 and H7 (t=0) under "reviewed arguments with independently checked computation".
The certificate-checked strata are H1 (cake_lpr, external) and H7 t≥1 (inside Lean via native_decide).
