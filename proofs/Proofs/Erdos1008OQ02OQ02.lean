/-
Erdős Problem #1008 — Explicit Kővári–Sós–Turán bound for K_{2,t}-free graphs
(the algebraic quadratic core)

The sibling file `Proofs.Erdos1008OQ02` solves the *C₄-case* Kővári–Sós–Turán
quadratic (`reiman_quadratic_solve`): from the cherry-counting inequality
`4 m² ≤ n²(n-1) + 2 n m` — valid because in a C₄-free (= K_{2,2}-free) graph any
two vertices share at most **one** common neighbour — it extracts Reiman's
explicit bound `4 m ≤ n(1 + √(4n-3))`.

This file generalises that algebraic core to the full **K_{2,t}** family.  A
K_{2,t}-free graph is one in which any two vertices share at most `t-1` common
neighbours.  Double-counting cherries `a — v — b` then gives

      ∑_v C(d_v, 2) ≤ (t-1) · C(n, 2),

and with `∑ d_v = 2m` and convexity `∑ d_v² ≥ (2m)²/n` this rearranges to the
generalised Kővári–Sós–Turán quadratic

      4 m² ≤ (t-1) · n²(n-1) + 2 n m.

`kst_quadratic_solve` solves this quadratic in `m`, extracting the upper root

      4 m ≤ n · (1 + s),   where   s = √(1 + 4(t-1)(n-1)),

i.e. the classical closed form

      ex(n ; K_{2,t}) ≤ ¼ · (1 + √(1 + 4(t-1)(n-1))) · n
                      = ½ · (√(t-1) · n^{3/2} + n)   (leading order).

The C₄ result is the special case `t = 2` (`reiman_quadratic_solve_of_kst`,
where `1 + 4(t-1)(n-1) = 4n-3`), and `kst_root_exact` certifies that the extracted
root is *exact* — it makes the generalised quadratic vanish — so the algebra loses
nothing (sharpness is a matter of an extremal graph construction, not of the bound).

Everything here is a self-contained real-number identity/inequality (pure
quadratic-formula manipulation, `Real.sqrt` avoided via the defining identity
`s² = 1 + 4(t-1)(n-1)`); no graph theory and no axioms are used.  The remaining
gap toward a graph-level `ex(n ; K_{2,t})` theorem is the general cherry-count
`∑_v C(d_v,2) ≤ (t-1)·C(n,2)`, which would replay the parent's `kovari_sos_turan`
double-count with `t-1` in place of `1`; that graph corollary is the natural next
step.

Reference: T. Kővári, V. T. Sós, P. Turán, "On a problem of K. Zarankiewicz",
Colloq. Math. 3 (1954), 50–57.

Status: 0 sorries, 0 axioms.  The algebraic core (`kst_quadratic_solve`,
`reiman_quadratic_solve_of_kst`, `kst_root_exact`) is docker-VERIFIED
(PR #36875).  The graph-level section (`kst_cherry_count_nat`,
`kst_graph_quadratic`, `kst_edge_bound`, `kst_edge_bound_of_free`) and the
leading-order closed form added in this session (`kst_radical_envelope`,
`kst_edge_bound_leading_order`, giving the recognisable
`ex(n ; K_{2,t}) ≤ ½(√(t-1)·n^{3/2}+n)`) are elaboration-checked but UNVERIFIED
in docker — the containerd build backend was down (meta.db / content-store I/O
errors) at authoring time.  They should be re-verified once the build infra is
repaired.
-/

import Mathlib

namespace Erdos1008

/-- **Solving the general Kővári–Sós–Turán quadratic (K_{2,t}).**

Given nonnegative reals `m, n, s` with `n ≥ 1`, `s = √(1 + 4(t-1)(n-1))` (encoded
as `s² = 1 + 4(t-1)(n-1)`, `s ≥ 0`), and the generalised KST inequality
`4 m² ≤ (t-1)·n²(n-1) + 2 n m`, the edge count satisfies `4 m ≤ n (1 + s)`.

`n(1 ± s)/4` are exactly the two roots of the quadratic
`4 x² - 2 n x - (t-1) n²(n-1)`; here we extract the upper root.  Setting `t = 2`
recovers `reiman_quadratic_solve` (the C₄ case, `s = √(4n-3)`).  The proof avoids
`Real.sqrt`, using only the defining identity for `s²`. -/
theorem kst_quadratic_solve (t m n s : ℝ)
    (hn : 1 ≤ n) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1))
    (hkst : 4 * m ^ 2 ≤ (t - 1) * n ^ 2 * (n - 1) + 2 * n * m) :
    4 * m ≤ n * (1 + s) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hns : 0 ≤ n * s := mul_nonneg hn0 hs
  -- (n·s)² = n²·s² = n²(1 + 4(t-1)(n-1)), and the KST bound forces (4m - n)² ≤ (n·s)².
  have hnssq : (n * s) ^ 2 = n ^ 2 * (1 + 4 * (t - 1) * (n - 1)) := by rw [mul_pow, hs2]
  have hsq : (4 * m - n) ^ 2 ≤ (n * s) ^ 2 := by nlinarith [hkst, hnssq]
  rcases le_or_gt (4 * m) n with h | h
  · -- Trivial side: 4m ≤ n ≤ n(1+s).
    nlinarith [hns]
  · -- Main side: 4m > n, so 4m - n ≥ 0; with (4m-n)² ≤ (n·s)² this gives
    -- 4m - n ≤ n·s, hence 4m ≤ n + n·s = n(1+s).
    have hpos : 0 < 4 * m - n := by linarith
    have h4mn : 4 * m - n ≤ n * s := by nlinarith [hsq, hns, hpos]
    nlinarith [h4mn]

/-- **The C₄ case is `t = 2`.**  Specialising `kst_quadratic_solve` to `t = 2`
(where `1 + 4(t-1)(n-1) = 4n - 3` and `(t-1) = 1`) reproduces the sibling file's
`reiman_quadratic_solve` verbatim, certifying that the K_{2,t} generalisation is a
faithful extension of the C₄ result. -/
theorem reiman_quadratic_solve_of_kst (m n s : ℝ)
    (hn : 1 ≤ n) (hs : 0 ≤ s)
    (hs2 : s ^ 2 = 4 * n - 3)
    (hkst : 4 * m ^ 2 ≤ n ^ 2 * (n - 1) + 2 * n * m) :
    4 * m ≤ n * (1 + s) := by
  refine kst_quadratic_solve 2 m n s hn hs ?_ ?_
  · rw [hs2]; ring
  · nlinarith [hkst]

/-- **Exactness of the extracted root.**  The upper root `R = n(1 + s)/4`, with
`s² = 1 + 4(t-1)(n-1)`, makes the generalised Kővári–Sós–Turán quadratic vanish:

      4 R² = (t-1) n²(n-1) + 2 n R.

So `kst_quadratic_solve` extracts a *genuine* root of the quadratic — the algebraic
bound is tight; any slack in `ex(n ; K_{2,t})` comes from the (in)existence of an
extremal graph attaining it, not from the quadratic-formula step.  Setting `t = 2`
recovers `reiman_root_exact`. -/
theorem kst_root_exact (t n s : ℝ) (hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1)) :
    let R := n * (1 + s) / 4
    4 * R ^ 2 = (t - 1) * n ^ 2 * (n - 1) + 2 * n * R := by
  intro R
  simp only [R]
  nlinarith [hs2]

/-- **Classical Kővári–Sós–Turán closed form.**  From the generalised KST quadratic
`4 m² ≤ (t-1)·n²(n-1) + 2 n m` (for `t ≥ 2`, `n ≥ 1`, `m ≥ 0`) the edge count obeys the
textbook bound

      m ≤ ½ · (√(t-1) · n^{3/2} + n).

This is the recognizable form `ex(n ; K_{2,t}) ≤ ½(√(t-1)·n^{3/2} + n)` of Kővári, Sós
and Turán (1954), obtained from the exact upper root `n(1+s)/4` of
`kst_quadratic_solve` by the elementary discriminant estimate
`s = √(1 + 4(t-1)(n-1)) ≤ 1 + 2√(t-1)·√n` (squaring reduces it to
`0 ≤ 4√(t-1)·√n + 4(t-1)`).  Here `n^{3/2}` is written `n · √n`. -/
theorem kst_bound_classical (t m n : ℝ) (ht : 2 ≤ t) (hn : 1 ≤ n) (_hm : 0 ≤ m)
    (hkst : 4 * m ^ 2 ≤ (t - 1) * n ^ 2 * (n - 1) + 2 * n * m) :
    m ≤ (Real.sqrt (t - 1) * (n * Real.sqrt n) + n) / 2 := by
  have ht1 : (0 : ℝ) ≤ t - 1 := by linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  set a := Real.sqrt (t - 1) with ha_def
  set b := Real.sqrt n with hb_def
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = t - 1 := Real.sq_sqrt ht1
  have hb2 : b ^ 2 = n := Real.sq_sqrt hn0
  have hdisc : (0 : ℝ) ≤ 1 + 4 * (t - 1) * (n - 1) := by nlinarith
  set s := Real.sqrt (1 + 4 * (t - 1) * (n - 1)) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + 4 * (t - 1) * (n - 1) := Real.sq_sqrt hdisc
  have hsolve : 4 * m ≤ n * (1 + s) := kst_quadratic_solve t m n s hn hs0 hs2 hkst
  have hYnn : (0 : ℝ) ≤ 1 + 2 * a * b := by nlinarith [mul_nonneg ha hb]
  have hsle : s ≤ 1 + 2 * a * b := by
    have hXY : 1 + 4 * (t - 1) * (n - 1) ≤ (1 + 2 * a * b) ^ 2 := by
      nlinarith [mul_nonneg ha hb, ha2, hb2, sq_nonneg a]
    calc s = Real.sqrt (1 + 4 * (t - 1) * (n - 1)) := hs_def
      _ ≤ Real.sqrt ((1 + 2 * a * b) ^ 2) := Real.sqrt_le_sqrt hXY
      _ = 1 + 2 * a * b := Real.sqrt_sq hYnn
  have hcomb : 4 * m ≤ n * (1 + (1 + 2 * a * b)) := by
    nlinarith [hsolve, mul_le_mul_of_nonneg_left hsle hn0]
  nlinarith [hcomb]

/-! ### Graph-level Kővári–Sós–Turán bound for K_{2,t}

The algebraic core above (`kst_quadratic_solve`) is fed by a genuinely
graph-theoretic input: the **cherry-count** inequality

      ∑_v C(d_v, 2) ≤ (t-1) · C(n, 2)

for K_{2,t}-free graphs.  We formalise it here directly from the defining property
of K_{2,t}-freeness — *any two distinct vertices have at most `t-1` common
neighbours* — via a double count of cherries `a — v — b`.  Combined with the
handshaking lemma `∑ d_v = 2m`, Cauchy–Schwarz `(∑ d_v)² ≤ n·∑ d_v²`, and the
algebraic solver `kst_quadratic_solve`, this yields the graph-level closed form

      ex(n ; K_{2,t}) ≤ ¼ · (1 + √(1 + 4(t-1)(n-1))) · n.

This closes the gap flagged in the sibling algebraic file: the parent
`Erdos1008Problem.lean` only proved the `t = 2` (C₄) graph-level bound
(`kovari_sos_turan`); here we obtain the full K_{2,t} family. -/

section GraphLevel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Common neighbours of two vertices `a`, `b`, as a `Finset`. -/
def commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : Finset V :=
  G.neighborFinset a ∩ G.neighborFinset b

/-- `s.offDiag.card = s.card·(s.card-1)` (self-contained port). -/
private theorem finset_card_offDiag {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  have hdiag : s.diag.card = s.card := by
    have heq : s.diag = s.image (fun a => (a, a)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_diag, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨ha, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨hc, rfl⟩
    rw [heq]
    exact Finset.card_image_of_injective _ (fun _ _ h => congr_arg Prod.fst h)
  have hdisj : Disjoint s.diag s.offDiag := Finset.disjoint_diag_offDiag s
  have hunion : s.diag ∪ s.offDiag = s ×ˢ s := Finset.diag_union_offDiag s
  have hprod : s.card + s.offDiag.card = s.card * s.card := by
    have hcu := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_product, hdiag] at hcu
    omega
  have hfact : s.card * (s.card - 1) + s.card = s.card * s.card := by
    cases s.card with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring
  omega

/-- Cast helper `↑(d·(d-1)) = ↑d·(↑d-1)` for `d : ℕ` (self-contained port). -/
private theorem nat_cast_mul_pred (d : ℕ) :
    (↑(d * (d - 1)) : ℝ) = (↑d : ℝ) * ((↑d : ℝ) - 1) := by
  cases d with
  | zero => simp
  | succ n => push_cast [Nat.succ_sub_one]; ring

/-- Cauchy–Schwarz for finite sums: `(∑ f)² ≤ |V|·∑ f²` (self-contained port). -/
private theorem sq_sum_le_card (f : V → ℝ) :
    (∑ v : V, f v) ^ 2 ≤ (Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 := by
  suffices h : (0 : ℝ) ≤ ∑ i : V, ∑ j : V, (f i - f j) ^ 2 by
    have hexp : ∑ i : V, ∑ j : V, (f i - f j) ^ 2 =
        (2 : ℝ) * ((Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 - (∑ v : V, f v) ^ 2) := by
      trans ∑ i : V, ((Fintype.card V : ℝ) * f i ^ 2 -
            2 * f i * ∑ j : V, f j + ∑ j : V, f j ^ 2)
      · congr 1; ext i
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      · have h1 : ∑ i : V, (Fintype.card V : ℝ) * f i ^ 2 =
            (Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 := by
          rw [← Finset.mul_sum]
        have h2 : ∑ i : V, 2 * f i * ∑ j : V, f j = 2 * (∑ v : V, f v) ^ 2 := by
          have hrearrange : ∀ i : V, 2 * f i * ∑ j : V, f j = (2 * ∑ j : V, f j) * f i :=
            fun i => by ring
          simp_rw [hrearrange, ← Finset.mul_sum]; ring
        have h3 : ∑ i : V, ∑ j : V, f j ^ 2 = (Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        linarith
    linarith
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Graph-level cherry count for K_{2,t} (ℕ form).**  If any two *distinct*
vertices of `G` have at most `κ` common neighbours (this is K_{2,κ+1}-freeness),
then `∑_v d_v(d_v-1) ≤ κ · n(n-1)`.

The proof double-counts ordered cherries `(a,b)` with `a, b ∈ N(v)`, `a ≠ b`:
summed over `v` this equals `∑_{a≠b} |N(a) ∩ N(b)|`, and each common-neighbour
count is bounded by `κ`. -/
theorem kst_cherry_count_nat (G : SimpleGraph V) [DecidableRel G.Adj] (κ : ℕ)
    (hfree : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ κ) :
    ∑ v : V, G.degree v * (G.degree v - 1) ≤
      κ * (Fintype.card V * (Fintype.card V - 1)) := by
  -- Each degree cherry count is the offDiag cardinality of the neighbourhood.
  have hoff : ∀ v : V, (G.neighborFinset v).offDiag.card = G.degree v * (G.degree v - 1) := by
    intro v; rw [finset_card_offDiag, SimpleGraph.card_neighborFinset_eq_degree]
  have hoffU : (Finset.univ : Finset V).offDiag.card =
      Fintype.card V * (Fintype.card V - 1) := by
    rw [finset_card_offDiag, Finset.card_univ]
  -- offDiag of each neighbourhood embeds into offDiag of the whole vertex set.
  have hsub : ∀ v : V, (G.neighborFinset v).offDiag ⊆ (Finset.univ : Finset V).offDiag := by
    intro v p hp
    rw [Finset.mem_offDiag] at hp ⊢
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, hp.2.2⟩
  -- The core double count.
  have key : ∑ v : V, (G.neighborFinset v).offDiag.card ≤
      (Finset.univ : Finset V).offDiag.card * κ := by
    -- Rewrite each cherry card as a sum of indicators over all ordered pairs.
    have expand : ∀ v : V, (G.neighborFinset v).offDiag.card =
        ∑ p ∈ (Finset.univ : Finset V).offDiag,
          (if p ∈ (G.neighborFinset v).offDiag then 1 else 0) := by
      intro v
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (hsub v)]
    calc ∑ v : V, (G.neighborFinset v).offDiag.card
        = ∑ v : V, ∑ p ∈ (Finset.univ : Finset V).offDiag,
            (if p ∈ (G.neighborFinset v).offDiag then 1 else 0) :=
          Finset.sum_congr rfl (fun v _ => expand v)
      _ = ∑ p ∈ (Finset.univ : Finset V).offDiag, ∑ v : V,
            (if p ∈ (G.neighborFinset v).offDiag then 1 else 0) := Finset.sum_comm
      _ ≤ ∑ _p ∈ (Finset.univ : Finset V).offDiag, κ := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_offDiag] at hp
          rw [← Finset.card_filter]
          -- the fibre over pair p is exactly the common-neighbour set of p.1, p.2
          have hset : (Finset.univ.filter
              (fun v => p ∈ (G.neighborFinset v).offDiag)) = commonNbrs G p.1 p.2 := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag,
              SimpleGraph.mem_neighborFinset, commonNbrs, Finset.mem_inter]
            constructor
            · rintro ⟨hv1, hv2, _⟩; exact ⟨hv1.symm, hv2.symm⟩
            · rintro ⟨hv1, hv2⟩; exact ⟨hv1.symm, hv2.symm, hp.2.2⟩
          rw [hset]; exact hfree p.1 p.2 hp.2.2
      _ = (Finset.univ : Finset V).offDiag.card * κ := by
          rw [Finset.sum_const, smul_eq_mul]
  -- Convert offDiag cardinalities back to degree cherry counts.
  calc ∑ v : V, G.degree v * (G.degree v - 1)
      = ∑ v : V, (G.neighborFinset v).offDiag.card :=
        Finset.sum_congr rfl (fun v _ => (hoff v).symm)
    _ ≤ (Finset.univ : Finset V).offDiag.card * κ := key
    _ = κ * (Fintype.card V * (Fintype.card V - 1)) := by rw [hoffU]; ring

/-- **Graph-level Kővári–Sós–Turán quadratic for K_{2,t}.**  For a graph `G` on
`n` vertices with `m` edges in which any two distinct vertices share at most `κ`
common neighbours (K_{2,κ+1}-freeness),

      4 m² ≤ κ · n²(n-1) + 2 n m.

This is the graph-theoretic input to `kst_quadratic_solve`; the `κ = 1` case is
the parent file's `kovari_sos_turan`. -/
theorem kst_graph_quadratic (G : SimpleGraph V) [DecidableRel G.Adj] (κ : ℕ)
    (hfree : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ κ) :
    (4 : ℝ) * (G.edgeFinset.card : ℝ) ^ 2 ≤
      (κ : ℝ) * (Fintype.card V : ℝ) ^ 2 * ((Fintype.card V : ℝ) - 1)
      + 2 * (Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ) := by
  -- Step 1: cherry count in ℝ.
  have hcherry_real : ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) ≤
      (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
    have hnat := kst_cherry_count_nat G κ hfree
    calc ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1)
        = ((∑ v : V, G.degree v * (G.degree v - 1) : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl (fun v _ => (nat_cast_mul_pred (G.degree v)).symm)
      _ ≤ ((κ * (Fintype.card V * (Fintype.card V - 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
          rw [Nat.cast_mul, nat_cast_mul_pred]
  -- Step 2: handshaking ∑ d_v = 2m.
  have hhand : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  -- Step 3: ∑ d_v² ≤ κ·n(n-1) + 2m via d² = d(d-1) + d.
  have hsum_sq : ∑ v : V, (G.degree v : ℝ) ^ 2 ≤
      (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))
      + 2 * (G.edgeFinset.card : ℝ) := by
    have hid : ∀ v : V, (G.degree v : ℝ) ^ 2 =
        (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + (G.degree v : ℝ) := fun v => by ring
    calc ∑ v : V, (G.degree v : ℝ) ^ 2
        = ∑ v, ((G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + (G.degree v : ℝ)) :=
          Finset.sum_congr rfl (fun v _ => hid v)
      _ = ∑ v, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + ∑ v, (G.degree v : ℝ) :=
          Finset.sum_add_distrib
      _ ≤ (κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))
          + 2 * (G.edgeFinset.card : ℝ) := by linarith [hcherry_real, hhand]
  -- Step 4: Cauchy–Schwarz and combination.
  have hcs := sq_sum_le_card (fun v : V => (G.degree v : ℝ))
  rw [hhand] at hcs
  have hn0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  calc (4 : ℝ) * (G.edgeFinset.card : ℝ) ^ 2
      = (2 * (G.edgeFinset.card : ℝ)) ^ 2 := by ring
    _ ≤ (Fintype.card V : ℝ) * ∑ v : V, (G.degree v : ℝ) ^ 2 := hcs
    _ ≤ (Fintype.card V : ℝ) *
          ((κ : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))
            + 2 * (G.edgeFinset.card : ℝ)) := mul_le_mul_of_nonneg_left hsum_sq hn0
    _ = (κ : ℝ) * (Fintype.card V : ℝ) ^ 2 * ((Fintype.card V : ℝ) - 1)
          + 2 * (Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ) := by ring

/-- **Graph-level closed-form edge bound for K_{2,t}.**  For a nonempty graph `G`
on `n ≥ 1` vertices with `m` edges in which any two distinct vertices share at
most `κ` common neighbours,

      4 m ≤ n · (1 + √(1 + 4κ(n-1))).

Combining `kst_graph_quadratic` with the algebraic root extraction
`kst_quadratic_solve` (taking `t = κ + 1`). -/
theorem kst_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (κ : ℕ)
    (hfree : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ κ) :
    4 * (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) *
        (1 + Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1))) := by
  have hn1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    have : 1 ≤ Fintype.card V := Fintype.card_pos
    exact_mod_cast this
  have harg : (0 : ℝ) ≤ 1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    have : (0 : ℝ) ≤ (κ : ℝ) * ((Fintype.card V : ℝ) - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  have hs0 : 0 ≤ Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1)) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1)) ^ 2 =
      1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1) := Real.sq_sqrt harg
  have hquad := kst_graph_quadratic G κ hfree
  refine kst_quadratic_solve ((κ : ℝ) + 1) (G.edgeFinset.card : ℝ) (Fintype.card V : ℝ)
    (Real.sqrt (1 + 4 * (κ : ℝ) * ((Fintype.card V : ℝ) - 1))) hn1 hs0 ?_ ?_
  · rw [hs2]; ring
  · have e : ((κ : ℝ) + 1 - 1) = (κ : ℝ) := by ring
    rw [e]; linarith [hquad]

/-- A graph *contains* K_{2,t}: two distinct vertices with at least `t` common
neighbours (the common neighbours are automatically distinct from `a`, `b`). -/
def HasK2t (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ (a b : V) (T : Finset V), a ≠ b ∧ t ≤ T.card ∧ (∀ y ∈ T, G.Adj a y ∧ G.Adj b y)

/-- In a K_{2,t}-free graph, any two distinct vertices share fewer than `t`
common neighbours (else those neighbours witness a K_{2,t}). -/
theorem commonNbrs_card_lt_of_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (hfree : ¬ HasK2t G t) (a b : V) (hab : a ≠ b) :
    (commonNbrs G a b).card < t := by
  by_contra h
  push_neg at h
  exact hfree ⟨a, b, commonNbrs G a b, hab, h, fun y hy => by
    simp only [commonNbrs, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
    exact hy⟩

/-- **K_{2,t}-free edge bound.**  A genuinely K_{2,t}-free nonempty graph
(`t ≥ 1`) satisfies the classical Kővári–Sós–Turán bound

      4 m ≤ n · (1 + √(1 + 4(t-1)(n-1))).

This packages `kst_edge_bound` with `commonNbrs_card_lt_of_free`, using the
forbidden-subgraph definition of K_{2,t}-freeness directly. -/
theorem kst_edge_bound_of_free (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (t : ℕ) (ht : 1 ≤ t) (hfree : ¬ HasK2t G t) :
    4 * (G.edgeFinset.card : ℝ) ≤
      (Fintype.card V : ℝ) *
        (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * ((Fintype.card V : ℝ) - 1))) := by
  have hbound : ∀ a b : V, a ≠ b → (commonNbrs G a b).card ≤ t - 1 := fun a b hab => by
    have := commonNbrs_card_lt_of_free G t hfree a b hab; omega
  have h := kst_edge_bound G (t - 1) hbound
  have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht, Nat.cast_one]
  rwa [hcast] at h

/-- **Nested-radical envelope.**  For `t ≥ 1` and any `n ≥ 0` the Reiman/KST radical
is dominated by a sum of *separated* radicals:

      √(1 + 4(t-1)(n-1)) ≤ 1 + 2·√(t-1)·√n.

This is the algebraic step that turns the exact nested-radical closed form into the
recognisable leading-order bound; it uses only `A² = t-1`, `B² = n`
(`A = √(t-1)`, `B = √n`) and `AB ≥ 0`, the squared comparison reducing to
`-4(t-1) ≤ 4·AB`. -/
theorem kst_radical_envelope (t : ℕ) (ht : 1 ≤ t) (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt (1 + 4 * ((t : ℝ) - 1) * (n - 1)) ≤
      1 + 2 * Real.sqrt ((t : ℝ) - 1) * Real.sqrt n := by
  have htm1 : (0 : ℝ) ≤ (t : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hA0 : 0 ≤ Real.sqrt ((t : ℝ) - 1) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hAB : 0 ≤ Real.sqrt ((t : ℝ) - 1) * Real.sqrt n := mul_nonneg hA0 hB0
  -- (A·B)² = (t-1)·n, obtained from A² = t-1, B² = n.
  have hab2 : (Real.sqrt ((t : ℝ) - 1) * Real.sqrt n) ^ 2 = ((t : ℝ) - 1) * n := by
    rw [mul_pow, Real.sq_sqrt htm1, Real.sq_sqrt hn]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [hab2, hAB, htm1]

/-- **Leading-order Kővári–Sós–Turán bound for K_{2,t}.**  The recognisable textbook
closed form: a K_{2,t}-free nonempty graph (`t ≥ 1`) on `n` vertices with `m` edges
satisfies

      m ≤ ½ · (√(t-1) · n^{3/2} + n),

with `n^{3/2}` written as `n · √n`.  This is the classical
`ex(n ; K_{2,t}) = O(√(t-1) · n^{3/2})` bound of Kővári–Sós–Turán, obtained from the
exact nested-radical form `kst_edge_bound_of_free` by dominating the radical via
`kst_radical_envelope`.  Setting `t = 2` gives the Reiman leading term
`ex(n ; C₄) ≤ ½(n^{3/2} + n)`. -/
theorem kst_edge_bound_leading_order (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (t : ℕ) (ht : 1 ≤ t) (hfree : ¬ HasK2t G t) :
    (G.edgeFinset.card : ℝ) ≤
      (Real.sqrt ((t : ℝ) - 1) * (Fintype.card V : ℝ) * Real.sqrt (Fintype.card V)
        + (Fintype.card V : ℝ)) / 2 := by
  have hn0 : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hbound := kst_edge_bound_of_free G t ht hfree
  have henv := kst_radical_envelope t ht (Fintype.card V : ℝ) hn0
  -- n·(1 + radical) ≤ n·(2 + 2·√(t-1)·√n), monotonicity in the nonnegative factor n.
  have hstep : (Fintype.card V : ℝ) *
      (1 + Real.sqrt (1 + 4 * ((t : ℝ) - 1) * ((Fintype.card V : ℝ) - 1))) ≤
      (Fintype.card V : ℝ) *
        (2 + 2 * Real.sqrt ((t : ℝ) - 1) * Real.sqrt (Fintype.card V)) :=
    mul_le_mul_of_nonneg_left (by nlinarith [henv]) hn0
  -- Chain: 4m ≤ n(1+rad) ≤ n(2 + 2√(t-1)√n) = 2n + 2·√(t-1)·n·√n.
  nlinarith [hbound, hstep, hn0]

/-- **Reiman's C₄ leading-order bound (graph-level `t = 2` specialisation).**
A `C₄`-free (`K_{2,2}`-free) graph on `n` vertices with `m` edges satisfies the
recognisable Reiman (1958) leading-order estimate

      m ≤ ½ · (n^{3/2} + n),

with `n^{3/2}` written as `n · √n`.  This is the `t = 2` case of
`kst_edge_bound_leading_order`, where the coefficient `√(t-1)` collapses to
`√1 = 1`, recovering `ex(n ; C₄) = O(n^{3/2})` and tying the `K_{2,t}` family back
to the parent `C₄` entry. -/
theorem reiman_edge_bound_leading_order (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hfree : ¬ HasK2t G 2) :
    (G.edgeFinset.card : ℝ) ≤
      ((Fintype.card V : ℝ) * Real.sqrt (Fintype.card V) + (Fintype.card V : ℝ)) / 2 := by
  have h := kst_edge_bound_leading_order G 2 (by norm_num) hfree
  have hsqrt : Real.sqrt (((2 : ℕ) : ℝ) - 1) = 1 := by
    rw [show (((2 : ℕ) : ℝ) - 1) = 1 by norm_num, Real.sqrt_one]
  rw [hsqrt, one_mul] at h
  exact h

end GraphLevel

end Erdos1008
