# Knowledge: cauchy-schwarz-oq-02-oq-03 (Complex Polarization Identity)

## Session 1 (researcher-10, 2026-05-08)

### What we did

Drafted full Lean proof of the complex polarization identity at `proofs/Proofs/CauchySchwarzOQ02OQ03.lean` (218 lines, 12 theorems, 0 sorries, 0 axioms). Created gallery entry at `src/data/proofs/cauchy-schwarz-oq-02-oq-03/`. Submitted as draft PR (build pending due to `proofs/.lake` self-symlink trap).

### Key technical observation: Convention mismatch

The slug's stated formula is in PHYSICS convention (linear in first argument):

$$\langle f, g \rangle = \frac{1}{4}(\|f+g\|^2 - \|f-g\|^2 + i\|f+ig\|^2 - i\|f-ig\|^2).$$

Mathlib uses MATH convention (sesquilinear in first argument: $\langle c \cdot x, y \rangle = \overline{c}\,\langle x,y \rangle$, linear in second). With this convention:

- $\langle x, iy \rangle = i \langle x, y \rangle$ (linear in second arg)
- $\mathrm{re}(i \cdot z) = -\mathrm{im}(z)$
- so $\|x + iy\|^2 = \|x\|^2 + 2\mathrm{re}\langle x, iy \rangle + \|y\|^2 = \|x\|^2 - 2\mathrm{im}\langle x,y \rangle + \|y\|^2$
- and $\|x + iy\|^2 - \|x - iy\|^2 = -4\,\mathrm{im}\langle x,y \rangle$ — SIGN FLIPPED from physics.

Therefore the slug's formula computes:

$$\frac{4\,\mathrm{re}\langle x,y \rangle - 4i\,\mathrm{im}\langle x,y \rangle}{4} = \mathrm{re}\langle x,y \rangle - i\,\mathrm{im}\langle x,y \rangle = \overline{\langle x,y \rangle} = \langle y, x \rangle.$$

In Mathlib convention the correct identity is:

$$\langle x, y \rangle_{\mathbb{C}} = \frac{1}{4}\left( \|x+y\|^2 - \|x-y\|^2 + i(\|x-iy\|^2 - \|x+iy\|^2) \right).$$

### Proof structure

12 theorems organized into 7 sections:

1. **Squared-norm expansion**: `norm_add_sq_complex` (cite Mathlib's `norm_add_sq`), `norm_sub_sq_complex` (derive via $y \to -y$ + `inner_neg_right` + `norm_neg`).
2. **Real-part recovery**: `norm_add_sq_sub_norm_sub_sq_eq_four_re` ($= 4\,\mathrm{re}\langle x,y \rangle$).
3. **Imaginary-part recovery**: helper lemmas `norm_smul_I_sq` (= $\|y\|^2$ via `norm_smul`+`Complex.norm_I`) and `re_I_mul` (= $-\mathrm{im}$); main lemma `norm_add_smul_I_sq_sub_eq_neg_four_im` substitutes $I \cdot y$ for $y$ in the squared-norm expansion.
4. **Per-component**: `re_inner_eq_quarter_norm_diff`, `im_inner_eq_quarter_norm_diff` (with sign flip).
5. **Main Mathlib-convention theorem**: `complex_polarization_mathlib`. Proof uses `Complex.re_add_im` to decompose, substitutes per-component formulas, finishes with `push_cast; ring`.
6. **Physics-convention bridge**: `physics_polarization_eq_inner_swap` (= $\langle y, x \rangle$), `physics_polarization_eq_conj` (= $\overline{\langle x, y \rangle}$). Key step: `inner_conj_symm` says $\langle y, x \rangle = \overline{\langle x, y \rangle}$.
7. **Corollary**: `mathlib_minus_physics`: $\langle x,y \rangle - \langle y, x \rangle = 2i \cdot \mathrm{im}\langle x, y \rangle$.

### Mathlib API used

- `norm_add_sq (𝕜 := ℂ)` : the squared-norm expansion (verified in sibling files `CauchySchwarzOQ01OQ02.lean` line 145, `CauchySchwarzOQ01.lean` line 121, `CauchySchwarzOQ01OQ01OQ01.lean` line 154).
- `inner_smul_right` : $\langle x, c \cdot y \rangle = c \cdot \langle x, y \rangle$.
- `inner_neg_right` : $\langle x, -y \rangle = -\langle x, y \rangle$.
- `inner_conj_symm` : $\langle y, x \rangle = \overline{\langle x, y \rangle}$.
- `Complex.re_add_im` : $\uparrow z.\mathrm{re} + \uparrow z.\mathrm{im} \cdot I = z$ (decomposition lemma).
- `Complex.norm_I = 1`.
- `Complex.mul_re`, `Complex.I_re`, `Complex.I_im` — for $\mathrm{re}(I \cdot z)$ computation.

### Build status

**Pending.** The worktree's `proofs/.lake` is a recursive self-symlink (per memory `feedback_researcher_lake_symlink_broken.md`), forcing every Docker build to fresh-clone Mathlib (~10–15 min) + cache get (~10 min) — total ~45 min. PR submitted as draft following PR #16936's pattern.

### Risks identified for build

1. `linarith` in `norm_sub_sq_complex` after `sub_eq_add_neg` rewrite — may need explicit `omega` or manual rewriting.
2. `simp` sets in `Complex.ext` proofs (only used as a small helper inside `physics_polarization_eq_inner_swap` for the `conj` decomposition) — should be robust given the standard Mathlib `Complex.conj_re`/`Complex.conj_im` lemmas.
3. `Complex.re_add_im` exact name in Mathlib 4.26 — well-established API name, low risk.
4. Coercion-cast handling in `complex_polarization_mathlib` — `push_cast` should normalize, then `ring` finishes.

### Next steps

- Re-run Docker build with warm Mathlib cache to verify all 12 theorems compile.
- If any tactic fails, the proof structure stays the same — only the specific `linarith`/`simp` invocations need patching.
- Future session: unify with parent OQ-02 via `RCLike` quantification; investigate operator polarization (Session 3).
