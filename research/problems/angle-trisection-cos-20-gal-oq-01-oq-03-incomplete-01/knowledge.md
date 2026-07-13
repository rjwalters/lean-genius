# Knowledge Base: angle-trisection-cos-20-gal-oq-01-oq-03-incomplete-01

**Title:** Eisenstein Conjecture for cos(π/p), general odd prime p (tier B, sig 7, tract 4).

---

## Session 2026-06-25 (S1, researcher-2) — STATEMENT-INTEGRITY FINDING

**Mode**: FRESH. **Outcome**: peer-review finding (no Lean shipped — see "Build" below).

### The finding: the parent's open `sorry` is a trivially-true weak existential

`proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` records ONE open `sorry`,
`eisenstein_conjecture_cos_pi_p` (line ~1374). Its gallery annotations
(`src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/annotations.json:221`,
`meta.json:40`) describe it as the **deep** uniform conjecture, "requiring cyclotomic
ramification theory and the local-field uniformizer theorem (Neukirch ANT II.6, the
main gap, ~200–400 lines)".

But the **actual Lean statement** is

```lean
∀ p, p.Prime → 3 ≤ p → Odd p →
  ∃ q : ℤ[X], q.natDegree = (p-1)/2 ∧ q.Monic ∧ q.IsEisensteinAt (Ideal.span {(p:ℤ)})
```

— a bare existential that says **nothing about cos(π/p)**. It is **trivially true**:
the witness `q = X^((p-1)/2) − p` is monic of degree `(p-1)/2 ≥ 1` and Eisenstein at
`p` for *every* prime `p ≥ 3` (leading coeff `1 ∉ (p)`; all sub-leading coeffs are
`0` or `−p ∈ (p)`; constant `−p ∉ (p²)`). None of the ramification machinery is
needed. **The file's headline "open conjecture" does not match the mathematics its
own documentation claims for it.**

### Recommended fix (mechanic / peer-review)

Replace the weak existential with the genuine conjecture — the minimal polynomial of
`2 + 2cos(π/p)` over ℤ is Eisenstein at `p` — so the `sorry` actually is the deep
problem the annotations advertise:

```lean
theorem eisenstein_minpoly_two_add_two_cos_pi_div_p
    (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) (hodd : Odd p) :
    (minpoly ℤ (2 + 2 * Real.cos (Real.pi / p))).IsEisensteinAt
      (Ideal.span {(p : ℤ)}) := by
  sorry
```

and (optionally) keep the now-honestly-named weak fact as a separate proved lemma.

### Ready-to-verify patch (UNVERIFIED — see Build note)

Proposed new file `Proofs/AngleTrisectionCos20GalOQ01OQ03Incomplete01.lean`
(namespace `EisensteinCosPiP`, `open Polynomial`). The weak lemma proof below uses
only confirmed Mathlib API: `natDegree_X_pow_sub_C`, `monic_X_pow_sub_C`,
`Monic.isEisensteinAt_of_mem_of_notMem`, `Ideal.span_singleton_eq_top`,
`Int.isUnit_iff`, `Ideal.mem_span_singleton`, `coeff_X_pow`, `coeff_C`,
`Ideal.span_singleton_pow`, `Int.le_of_dvd`.

```lean
theorem exists_monic_eisenstein_of_degree
    (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) (_hodd : Odd p) :
    ∃ q : ℤ[X], q.natDegree = (p - 1) / 2 ∧ q.Monic ∧
      q.IsEisensteinAt (Ideal.span {(p : ℤ)}) := by
  set d : ℕ := (p - 1) / 2 with hd_def
  have hd : d ≠ 0 := by rw [hd_def]; omega
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h3
  refine ⟨X ^ d - C (p : ℤ), ?_, ?_, ?_⟩
  · simpa using (natDegree_X_pow_sub_C (n := d) (r := (p : ℤ)))
  · exact monic_X_pow_sub_C (p : ℤ) hd
  · have hmonic : (X ^ d - C (p : ℤ)).Monic := monic_X_pow_sub_C (p : ℤ) hd
    have hne_top : Ideal.span {(p : ℤ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]; intro hu
      rw [Int.isUnit_iff] at hu; omega
    have hdeg : (X ^ d - C (p : ℤ)).natDegree = d :=
      natDegree_X_pow_sub_C (n := d) (r := (p : ℤ))
    refine hmonic.isEisensteinAt_of_mem_of_notMem hne_top ?_ ?_
    · intro n hn
      rw [hdeg] at hn
      rw [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, coeff_C,
        if_neg (by omega : n ≠ d)]
      rcases eq_or_ne n 0 with hn0 | hn0
      · simp [hn0, dvd_neg]
      · simp [hn0]
    · rw [coeff_sub, coeff_X_pow, coeff_C,
        if_neg (by omega : (0 : ℕ) ≠ d), if_pos rfl, zero_sub,
        Ideal.span_singleton_pow]
      intro hmem
      rw [Ideal.mem_span_singleton] at hmem
      have hdvd : (p : ℤ) ^ 2 ∣ (p : ℤ) := (dvd_neg).mp hmem
      have hp0 : (0 : ℤ) < (p : ℤ) := by omega
      have hle := Int.le_of_dvd hp0 hdvd
      nlinarith [hpZ]
```

### Build note (why no Lean was committed)

This file (`import Mathlib`) could not be verified this session:
- Docker down.
- Local olean cache (`proofs/.lake`) is **statically corrupt**: a failed/partial
  `lake exe cache get` left several **0-byte** artifacts
  (`Mathlib/MeasureTheory/Integral/Pi.ir`, plus rotating `invalid header` on
  `aesop/.../Substitution.olean`, `Mathlib/Tactic/NormNum/Result.olean`). No olean
  changed in the last 3 min, so the cache is not self-repairing; every `import
  Mathlib` build aborts at olean *load* time. (Agents importing narrow Mathlib
  slices still build.)
- Aristotle MCP returned `Resource not found` (service unavailable).

Rather than commit an unverifiable proof that could fail the deployer's Docker build,
the proof is recorded here for a build-capable session to drop in and verify. The
*finding itself* (the weak-existential mismatch) is verification-independent and is
the real deliverable.

**Next steps**
- Build-capable session: verify the patch above, ship the new file, and strengthen
  the parent's `eisenstein_conjecture_cos_pi_p` (rename to weak form + add the
  `minpoly` conjecture) so the gallery's documentation matches the Lean.
