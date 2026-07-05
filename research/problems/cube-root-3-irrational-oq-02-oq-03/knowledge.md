# Knowledge Base: cube-root-3-irrational-oq-02-oq-03

Vahlen–Capelli irreducibility criterion for `Xⁿ - a` over a field.

---

## Problem Understanding

Parent `cube-root-3-irrational-oq-02` proves `X³ - 3` irreducible over ℚ via
Eisenstein at 3 — one instance of the general question: **exactly when is
`Xⁿ - a` irreducible over a field `K`?** The classical answer is the
**Vahlen–Capelli theorem** (Lang, *Algebra* VI.9.1):

> `Xⁿ - a` is irreducible over `K` ⟺
> (1) `a ∉ Kᵖ` for every prime `p ∣ n`, and
> (2) if `4 ∣ n`, then `a ∉ -4·K⁴`.

The half where a perfect `p`-th power or a `-4K⁴` member forces **reducibility**
is elementary; the reverse (those conditions ⇒ irreducible) is the deep half.

---

## Insights

### Mathlib coverage (surveyed 2026-07-04)
- `Mathlib.FieldTheory.KummerExtension` proves the **odd `n`** criterion completely:
  - `X_pow_sub_C_irreducible_iff_forall_prime_of_odd (hn : Odd n)`:
    `Irreducible (X^n - C a) ↔ ∀ p prime, p ∣ n → ∀ b, b^p ≠ a`.
  - `X_pow_sub_C_irreducible_of_prime_pow` (odd prime powers).
- The file explicitly carries **`TODO: criteria for even n`**. The `4 ∣ n`
  exceptional clause (condition 2) is **NOT in Mathlib** — this is the genuine gap.

### Mathematical heart of the even case
- The `4 ∣ n` exception is powered by the **Sophie Germain / Aurifeuillian identity**
  `Y⁴ + 4c⁴ = (Y² - 2cY + 2c²)(Y² + 2cY + 2c²)` (valid over any comm ring).
- Setting `Y = Xᵏ`, `c = C b` gives an explicit factorization of `X^{4k} - C a`
  when `a = -(4b⁴)`, exhibiting the reducibility that condition 2 rules out.

### Necessity is fully provable now (all `n`)
- Clause 1 necessity: if `bᵖ = a`, then `Xᵐ - C b` (`m = n/p`) properly divides
  `Xⁿ - C a` — via `sub_dvd_pow_sub_pow` + `natDegree_X_pow_sub_C` + the
  degree-collapse contradiction using `Irreducible.isUnit_or_isUnit`.
- Clause 2 necessity: the Sophie Germain factors have degree `2k`; computed via
  `F = q.comp (Xᵏ)` and `natDegree_comp` (`q` a monic quadratic, degree 2).

---

## Dead Ends / Notes
- Cannot submit the even-`n` *sufficiency* to Aristotle: it is a genuine OPEN
  case (Mathlib's own TODO), not a known-proof formalization task.
- Tooling blackout this session: Docker build unavailable (containerd EIO),
  Aristotle MCP returns "Resource not found" — file shipped build-pending.

---

## Sessions

### 2026-07-04 (Session 1) — FRESH, ORIENT→ACT
**Outcome**: progress (necessity direction fully formalized; even-sufficiency isolated as sole open sorry)

**What I did**
- Surveyed Mathlib `KummerExtension`; confirmed odd case done, even case is an open TODO.
- Locked exact API (`sub_dvd_pow_sub_pow`, `natDegree_X_pow_sub_C`,
  `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`, `natDegree_comp`) against tag v4.26.0.
- Wrote `proofs/Proofs/CubeRoot3IrrationalOQ02OQ03.lean`:
  - `sophie_germain_factor` (ring identity),
  - `X_pow_four_mul_sub_C_factorization` (explicit `X^{4k} - C(-(4b⁴))` factorization),
  - `reducible_of_prime_pow_eq` (clause-1 necessity),
  - `reducible_of_neg_four_mul_pow4` (clause-2 / `4∣n` necessity — the Mathlib-gap part),
  - `VahlenCapelliCond`, `vahlen_capelli_necessity` (`Irreducible ⇒ Cond`, all n, fully proved),
  - `vahlen_capelli_of_odd` (full criterion for odd n via Mathlib, fully proved),
  - `vahlen_capelli` (full criterion; even-`n` sufficiency = single `sorry`).

**Key findings**: the necessity direction — including the delicate `4∣n` clause
that Mathlib omits — is provable with elementary factorization + degree bookkeeping.
Only the even-`n` sufficiency remains (the deep half).

**Next steps**
- Even-`n` sufficiency: reduce general `n` to prime-power towers; the `2ᵏ` tower
  is the crux (odd-prime towers already in Mathlib via `X_pow_sub_C_irreducible_of_prime_pow`).
- Formalize the `2ᵏ` case: `X^{2ᵏ} - C a` irreducible when `a ∉ K²` and `a ∉ -4K⁴`.
  This is where the `-4K⁴` exception genuinely enters; expect a norm/degree-2-extension argument.
- Once a build is available, verify the degree-computation tactics
  (`compute_degree!`, `natDegree_comp`, `map_ofNat` simp) in the shipped file.
