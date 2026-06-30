/-
  Property B — the asymmetric first moment cannot beat Erdős's 2^(k-1).

  Open question (property-b-first-moment-oq-03): sharpen Erdős's 1963 bound
  m(k) ≥ 2^(k-1) to the Radhakrishnan–Srinivasan m(k) = Ω(2^k·√(k/log k))
  via the "asymmetric / recoloring" refinement of the first moment argument.

  The OQ names two ingredients — *asymmetry* of the random coloring and a
  *recoloring* repair step. This file isolates the first and settles it
  *negatively*: asymmetry alone yields no improvement whatsoever.

  Setup. Color each vertex of a k-uniform hypergraph independently Red with
  probability `p` and Blue with probability `1 - p`. A fixed edge of size
  `k` is monochromatic (all-Red or all-Blue) with probability
      monoProb k p = p^k + (1-p)^k.
  The first-moment threshold — the largest edge count `m` for which the
  expected number of monochromatic edges `m · monoProb k p` stays below 1,
  forcing a proper coloring to exist — is `1 / monoProb k p`.

  Results (all over the finite/real first-moment model, 0 axioms):

    • `monoProb_ge`     : monoProb k p ≥ 2·(1/2)^k = 2^(1-k) for every bias
                          p ∈ [0,1], k ≥ 1.
    • `monoProb_half_le`: the symmetric coloring p = 1/2 MINIMIZES the
                          monochromatic probability.
    • `monoProb_half_lt`: for k ≥ 2 it is the UNIQUE minimizer — any bias
                          p ≠ 1/2 strictly increases monoProb, hence strictly
                          LOWERS the threshold 1 / monoProb k p.
    • `threshold_half`  : the symmetric threshold is exactly Erdős's 2^(k-1),
                          so no bias raises the threshold above 2^(k-1).
    • `expected_mono_half_le` : for an m-edge hypergraph, the expected number
                          of monochromatic edges is minimized at p = 1/2.

  Conclusion. Biasing the colors never improves Erdős's 2^(k-1); the
  Radhakrishnan–Srinivasan gain of order √(k/log k) must come entirely from
  the *recoloring* step, not from asymmetry. This is a structural ORIENT
  result for oq-03, not the RS bound itself, and it sharply scopes the
  remaining work (the recoloring analysis) for future sessions.

  Companion to `PropertyBFirstMoment.lean`, which formalizes Erdős's
  original symmetric bound `m(k) ≥ 2^(k-1)`.

  Status: 0 sorries, 0 axioms. No `native_decide`.
-/
import Mathlib

namespace ProbMethod.PropertyB.Asymmetric

open Set

/-- Probability that a fixed edge of size `k` is monochromatic when each
    vertex is colored Red independently with probability `p` (and Blue with
    probability `1 - p`): one of the two colors must hit every one of the
    `k` vertices, giving `p^k + (1-p)^k`. -/
def monoProb (k : ℕ) (p : ℝ) : ℝ := p ^ k + (1 - p) ^ k

@[simp] lemma monoProb_half (k : ℕ) : monoProb k (1 / 2) = 2 * (1 / 2) ^ k := by
  unfold monoProb; norm_num; ring

/-- **Asymmetry never helps (first moment).**
    For `k ≥ 1` and any bias `p ∈ [0,1]`, the monochromatic probability is
    at least the symmetric value `2·(1/2)^k = 2^(1-k)`. This is convexity of
    `x ↦ x^k` applied to the midpoint of `p` and `1 - p`. -/
theorem monoProb_ge (k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * (1 / 2) ^ k ≤ monoProb k p := by
  have hmem_p : p ∈ Ici (0 : ℝ) := hp0
  have hmem_q : (1 - p) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have h := (convexOn_pow (𝕜 := ℝ) k).2 hmem_p hmem_q
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  have hmid : (1 / 2) * p + (1 / 2) * (1 - p) = (1 / 2 : ℝ) := by ring
  rw [hmid] at h
  unfold monoProb
  linarith [h]

/-- The symmetric coloring `p = 1/2` minimizes the monochromatic
    probability over all biases in `[0,1]`. -/
theorem monoProb_half_le (k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    monoProb k (1 / 2) ≤ monoProb k p := by
  rw [monoProb_half]; exact monoProb_ge k hp0 hp1

/-- **Symmetry is the unique optimum for `k ≥ 2`.**
    Any bias `p ≠ 1/2` strictly increases the monochromatic probability, by
    strict convexity of `x ↦ x^k` for `k ≥ 2`. Consequently a biased
    coloring strictly lowers the first-moment threshold `1 / monoProb k p`. -/
theorem monoProb_half_lt (k : ℕ) (hk : 2 ≤ k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hne : p ≠ 1 / 2) :
    monoProb k (1 / 2) < monoProb k p := by
  have hmem_p : p ∈ Ici (0 : ℝ) := hp0
  have hmem_q : (1 - p) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have hxy : p ≠ 1 - p := by intro h; apply hne; linarith
  have h := (strictConvexOn_pow hk).2 hmem_p hmem_q hxy
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  have hmid : (1 / 2) * p + (1 / 2) * (1 - p) = (1 / 2 : ℝ) := by ring
  rw [hmid] at h
  rw [monoProb_half, monoProb]
  linarith [h]

/-- The symmetric first-moment threshold equals Erdős's `2^(k-1)`:
    `1 / monoProb k (1/2) = 2^(k-1)`. Combined with `monoProb_half_le`, no
    bias `p` raises the threshold `1 / monoProb k p` above `2^(k-1)` — the
    asymmetric first moment cannot beat the Erdős bound. -/
theorem threshold_half (k : ℕ) (hk : 1 ≤ k) :
    1 / monoProb k (1 / 2) = 2 ^ (k - 1) := by
  have hk2 : (2 : ℝ) ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ]; congr 1; omega
  rw [monoProb_half]
  have hpk : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [one_div_pow]
  rw [hpk]
  have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  linarith [hk2]

/-- For a `k`-uniform hypergraph with `m` edges, the expected number of
    monochromatic edges under a `p`-biased random coloring, `m · monoProb k p`,
    is minimized at the symmetric `p = 1/2`. -/
theorem expected_mono_half_le (k : ℕ) (m : ℝ) (hm : 0 ≤ m)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    m * monoProb k (1 / 2) ≤ m * monoProb k p :=
  mul_le_mul_of_nonneg_left (monoProb_half_le k hp0 hp1) hm

end ProbMethod.PropertyB.Asymmetric
