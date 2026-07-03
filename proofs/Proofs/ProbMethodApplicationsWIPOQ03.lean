/-
  Probabilistic Method Applications — WIP OQ-03

  Open question (prob-method-applications-wip-01-oq-03):
    "Tournament domination bound via the first-moment method."

  The companion file `ProbMethodApplicationsWIP.lean` proves the abstract
  first-moment / union-bound existence engine

      ProbMethod.Core.exists_good_of_card_bound :
        (s : Finset ι) (A : ι → Finset Ω) (B : ℕ)
        (∀ i ∈ s, (A i).card ≤ B) (s.card * B < |Ω|)
        ⟹ ∃ ω, ∀ i ∈ s, ω ∉ A i,

  over an arbitrary finite sample space `Ω`.  Its docstring lists *tournament
  domination* among the headline consequences of the probabilistic method that
  the vacuous companion `ProbMethodApplications.lean` only gestured at.  This
  file supplies the genuine instantiation.

  **Setup.**  Fix a finite linearly ordered vertex set `V`.  A *tournament* is an
  orientation of every edge, encoded as `T : Edge V → Bool`, where
  `Edge V = {p : V × V // p.1 < p.2}` is the set of `C(|V|,2)` unordered pairs
  (represented by their increasing ordering) and `beats T u v` reads off, from
  the orientation of the edge `{u,v}`, whether `u` beats `v`.  The sample space
  is thus `Ω = Edge V → Bool`, of size `2^{|Edge V|} = 2^{C(|V|,2)}`.

  A vertex set `K` **dominates** `T` when every vertex outside `K` is beaten by
  some member of `K`.  For a fixed `k`-set `K`, the number of tournaments in
  which `K` dominates is
      `(2^k - 1)^{|V|-k} · 2^{|Edge V| - k(|V|-k)}`
  (each of the `|V|-k` outside vertices must avoid the single orientation in
  which it beats every member of `K`; the remaining edges are free), so the
  fraction of dominating tournaments is `(1 - 2^{-k})^{|V|-k}`.

  **First-moment bound.**  Summing over all `C(|V|,k)` vertex `k`-sets, if
      `C(|V|,k) · (2^k - 1)^{|V|-k} < 2^{k(|V|-k)}`
  — equivalently the classical `C(n,k)(1 - 2^{-k})^{n-k} < 1` — then the total
  number of "`K` dominates" tournaments is below `|Ω|`, so `exists_good_of_card_bound`
  produces a tournament in which **no** `k`-set dominates, i.e. a tournament whose
  domination number exceeds `k`.  The smallest instance (`k = 1`, `n = 3`,
  `3 · 1 < 4`) is the cyclic triangle: a `3`-tournament with no dominating vertex.

  Status: fully proved (0 sorry, 0 axiom).  The engine instantiation
  (`exists_no_dominating_kset`), the finite count `card_dominates_le`, and the
  concrete cyclic-triangle witness are all discharged.  The cross-edge count is
  moreover exact (`card_cross_eq`: there are precisely `k(n-k)` cross edges),
  which pins the dominating fraction to the classical `(1 - 2^{-k})^{n-k}`.
-/
import Mathlib
import Proofs.ProbMethodApplicationsWIP

open Finset

namespace ProbMethod.Tournament

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The edge set of the complete graph on `V`: unordered pairs represented by
their increasing ordered pair. `|Edge V| = C(|V|, 2)`. -/
abbrev Edge (V : Type*) [LinearOrder V] : Type _ := {p : V × V // p.1 < p.2}

/-- Given an orientation `T` of the edges, does `u` beat `v`?  The edge `{u,v}`
is stored as the increasing pair; `T` is `true` there iff the smaller endpoint
beats the larger. -/
def beats (T : Edge V → Bool) (u v : V) : Bool :=
  if h : u < v then T ⟨(u, v), h⟩
  else if h : v < u then ! T ⟨(v, u), h⟩
  else false

/-- `K` **dominates** the tournament `T` when every vertex outside `K` is beaten
by some member of `K`. -/
def Dominates (K : Finset V) (T : Edge V → Bool) : Prop :=
  ∀ v ∈ Kᶜ, ∃ u ∈ K, beats T u v = true

instance (K : Finset V) (T : Edge V → Bool) : Decidable (Dominates K T) := by
  unfold Dominates; infer_instance

/-- The "bad event": the set of tournaments in which the vertex set `K`
dominates. -/
def dominatingSet (K : Finset V) : Finset (Edge V → Bool) :=
  (univ : Finset (Edge V → Bool)).filter (fun T => Dominates K T)

/-! ## The counting lemma -/

/-- An edge is a *cross* edge for `K` when exactly one endpoint lies in `K`. -/
def IsCross (K : Finset V) (e : Edge V) : Prop :=
  (e.1.1 ∈ K ∧ e.1.2 ∉ K) ∨ (e.1.1 ∉ K ∧ e.1.2 ∈ K)

instance (K : Finset V) (e : Edge V) : Decidable (IsCross K e) := by
  unfold IsCross; infer_instance

/-- The "good block" configurations at one outside vertex `v`: assignments of a
Boolean to each of the `k` edges from `v` to `K` in which *some* member of `K`
wins.  There are `2^k - 1` of them (all but the all-lose configuration). -/
theorem card_block (K : Finset V) :
    Fintype.card {c : {x // x ∈ K} → Bool // ∃ u, c u = true} = 2 ^ K.card - 1 := by
  classical
  have hcompl : Fintype.card {c : {x // x ∈ K} → Bool // ¬ ∃ u, c u = true} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨fun _ => false, by simp⟩, ?_⟩
    rintro ⟨c, hc⟩
    apply Subtype.ext
    funext u
    by_contra h
    exact hc ⟨u, by simpa using h⟩
  have htot : Fintype.card ({x // x ∈ K} → Bool) = 2 ^ K.card := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have h := Fintype.card_subtype_compl (fun c : {x // x ∈ K} → Bool => ∃ u, c u = true)
  rw [hcompl, htot] at h
  have hle : Fintype.card {c : {x // x ∈ K} → Bool // ∃ u, c u = true} ≤ 2 ^ K.card := by
    rw [← htot]; exact Fintype.card_subtype_le _
  omega

/-- The cross edge `{u, v}` associated to a pair `(u, v) ∈ K × Kᶜ`. -/
def crossEdge (K : Finset V) (p : {x // x ∈ K} × {x // x ∈ Kᶜ}) :
    {e : Edge V // IsCross K e} :=
  if h : p.1.1 < p.2.1 then
    ⟨⟨(p.1.1, p.2.1), h⟩, Or.inl ⟨p.1.2, Finset.mem_compl.mp p.2.2⟩⟩
  else
    ⟨⟨(p.2.1, p.1.1),
        lt_of_le_of_ne (not_lt.mp h)
          (by
            intro heq
            have hmem : p.2.1 ∈ K :=
              Eq.subst (motive := fun x => x ∈ K) heq.symm p.1.2
            exact Finset.mem_compl.mp p.2.2 hmem)⟩,
      Or.inr ⟨Finset.mem_compl.mp p.2.2, p.1.2⟩⟩

/-- The underlying ordered pair of `crossEdge K p` is `(u, v)` or `(v, u)`
according to the order of the endpoints. -/
theorem crossEdge_fst (K : Finset V) (p : {x // x ∈ K} × {x // x ∈ Kᶜ}) :
    (crossEdge K p).1.1
      = if p.1.1 < p.2.1 then (p.1.1, p.2.1) else (p.2.1, p.1.1) := by
  unfold crossEdge
  by_cases h : p.1.1 < p.2.1
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

theorem crossEdge_injective (K : Finset V) : Function.Injective (crossEdge K) := by
  intro p q hpq
  have hpK : p.1.1 ∈ K := p.1.2
  have hqK : q.1.1 ∈ K := q.1.2
  have hpKc : p.2.1 ∉ K := Finset.mem_compl.mp p.2.2
  have hqKc : q.2.1 ∉ K := Finset.mem_compl.mp q.2.2
  have hpair :
      (if p.1.1 < p.2.1 then (p.1.1, p.2.1) else (p.2.1, p.1.1))
        = (if q.1.1 < q.2.1 then (q.1.1, q.2.1) else (q.2.1, q.1.1)) := by
    rw [← crossEdge_fst, ← crossEdge_fst, hpq]
  by_cases hp : p.1.1 < p.2.1 <;> by_cases hq : q.1.1 < q.2.1
  · rw [if_pos hp, if_pos hq, Prod.mk.injEq] at hpair
    exact Prod.ext (Subtype.ext hpair.1) (Subtype.ext hpair.2)
  · rw [if_pos hp, if_neg hq, Prod.mk.injEq] at hpair
    exact absurd (hpair.1 ▸ hpK) hqKc
  · rw [if_neg hp, if_pos hq, Prod.mk.injEq] at hpair
    exact absurd (hpair.2 ▸ hpK) hqKc
  · rw [if_neg hp, if_neg hq, Prod.mk.injEq] at hpair
    exact Prod.ext (Subtype.ext hpair.2) (Subtype.ext hpair.1)

/-- `crossEdge` hits every cross edge: given a cross edge `{a, b}` (say `a < b`)
with exactly one endpoint in `K`, the pair `(u, v) ∈ K × Kᶜ` obtained by putting
the in-`K` endpoint first maps back onto it. Together with injectivity this makes
`crossEdge` a bijection `K × Kᶜ ≃ {cross edges}`. -/
theorem crossEdge_surjective (K : Finset V) : Function.Surjective (crossEdge K) := by
  rintro ⟨⟨⟨a, b⟩, hab⟩, hcross⟩
  rcases hcross with ⟨haK, hbK⟩ | ⟨haK, hbK⟩
  · -- `a ∈ K`, `b ∉ K`, and `a < b`: the pair `(a, b)` maps to this edge.
    refine ⟨(⟨a, haK⟩, ⟨b, Finset.mem_compl.mpr hbK⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [crossEdge_fst, if_pos hab]
  · -- `a ∉ K`, `b ∈ K`, and `a < b` so `¬ b < a`: the pair `(b, a)` maps to it.
    refine ⟨(⟨b, hbK⟩, ⟨a, Finset.mem_compl.mpr haK⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [crossEdge_fst, if_neg (not_lt.mpr hab.le)]

/-- **Exact cross-edge count.** `crossEdge` is a bijection from `K × Kᶜ` onto the
cross edges, so there are *exactly* `k · (n - k)` cross edges for a `k`-set `K`.
This sharpens `card_cross_ge` and pins the dominating-tournament fraction to the
exact `(1 - 2^{-k})^{n-k}` (equality in the free-edge exponent of the count). -/
theorem card_cross_eq (K : Finset V) :
    Fintype.card {e : Edge V // IsCross K e}
      = K.card * (Fintype.card V - K.card) := by
  classical
  have hbij : Function.Bijective (crossEdge K) :=
    ⟨crossEdge_injective K, crossEdge_surjective K⟩
  rw [← Fintype.card_of_bijective hbij, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_coe, Finset.card_compl]

/-- There are at least `k · (n - k)` cross edges. Immediate from the exact count
`card_cross_eq`; retained under this name for the union-bound call site. -/
theorem card_cross_ge (K : Finset V) :
    K.card * (Fintype.card V - K.card)
      ≤ Fintype.card {e : Edge V // IsCross K e} :=
  (card_cross_eq K).ge

/-- **Count of dominating tournaments.**
For a fixed `k`-set `K` in an `n`-vertex tournament, the number of orientations
in which `K` dominates is at most `(2^k - 1)^{n-k} · 2^{|Edge V| - k(n-k)}`:
each of the `n - k` vertices outside `K` must avoid the single orientation of its
`k` edges to `K` in which it beats all of `K` (leaving `2^k - 1` choices for that
block), and the remaining `|Edge V| - k(n-k)` edges are unconstrained. -/
theorem card_dominates_le (K : Finset V) (hK : K.card = k) :
    (dominatingSet K).card
      ≤ (2 ^ k - 1) ^ (Fintype.card V - k)
        * 2 ^ (Fintype.card (Edge V) - k * (Fintype.card V - k)) := by
  classical
  rw [dominatingSet, ← Fintype.card_subtype]
  have hinj : Function.Injective
      (fun TT : {T : Edge V → Bool // Dominates K T} =>
        ((fun v : {x // x ∈ Kᶜ} =>
            (⟨fun u : {x // x ∈ K} => beats TT.1 u.1 v.1,
              by
                obtain ⟨u, huK, hu⟩ := TT.2 v.1 v.2
                exact ⟨⟨u, huK⟩, hu⟩⟩ :
              {c : {x // x ∈ K} → Bool // ∃ u, c u = true})),
          (fun e : {e : Edge V // ¬ IsCross K e} => TT.1 e.1))) := by
    rintro ⟨T₁, h₁⟩ ⟨T₂, h₂⟩ hEq
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨hcr, hnc⟩ := hEq
    apply Subtype.ext
    funext e
    obtain ⟨⟨a, b⟩, hab⟩ := e
    by_cases hcross : IsCross K ⟨(a, b), hab⟩
    · rcases hcross with ⟨haK, hbK⟩ | ⟨haK, hbK⟩
      · have hbKc : b ∈ Kᶜ := Finset.mem_compl.mpr hbK
        have hval := congrFun hcr ⟨b, hbKc⟩
        rw [Subtype.ext_iff] at hval
        have hval2 := congrFun hval ⟨a, haK⟩
        have e1 : beats T₁ a b = T₁ ⟨(a, b), hab⟩ := by
          simp only [beats]; rw [dif_pos hab]
        have e2 : beats T₂ a b = T₂ ⟨(a, b), hab⟩ := by
          simp only [beats]; rw [dif_pos hab]
        change beats T₁ a b = beats T₂ a b at hval2
        rw [e1, e2] at hval2; exact hval2
      · have haKc : a ∈ Kᶜ := Finset.mem_compl.mpr haK
        have hval := congrFun hcr ⟨a, haKc⟩
        rw [Subtype.ext_iff] at hval
        have hval2 := congrFun hval ⟨b, hbK⟩
        have hnba : ¬ b < a := not_lt.mpr hab.le
        have e1 : beats T₁ b a = ! T₁ ⟨(a, b), hab⟩ := by
          simp only [beats]; rw [dif_neg hnba, dif_pos hab]
        have e2 : beats T₂ b a = ! T₂ ⟨(a, b), hab⟩ := by
          simp only [beats]; rw [dif_neg hnba, dif_pos hab]
        change beats T₁ b a = beats T₂ b a at hval2
        rw [e1, e2] at hval2
        exact Bool.not_inj hval2
    · exact congrFun hnc ⟨⟨(a, b), hab⟩, hcross⟩
  refine le_trans (Fintype.card_le_of_injective _ hinj) ?_
  have hcardBlock :
      Fintype.card {c : {x // x ∈ K} → Bool // ∃ u, c u = true} = 2 ^ k - 1 := by
    rw [card_block K, hK]
  have hcardKc : Fintype.card {x // x ∈ Kᶜ} = Fintype.card V - k := by
    rw [Fintype.card_coe, Finset.card_compl, hK]
  have hcardNon : Fintype.card {e : Edge V // ¬ IsCross K e}
      ≤ Fintype.card (Edge V) - k * (Fintype.card V - k) := by
    rw [Fintype.card_subtype_compl]
    have hcr := card_cross_ge K
    rw [hK] at hcr
    exact Nat.sub_le_sub_left hcr _
  calc
    Fintype.card (({x // x ∈ Kᶜ} → {c : {x // x ∈ K} → Bool // ∃ u, c u = true})
        × ({e : Edge V // ¬ IsCross K e} → Bool))
        = (Fintype.card {c : {x // x ∈ K} → Bool // ∃ u, c u = true})
            ^ (Fintype.card {x // x ∈ Kᶜ})
          * 2 ^ (Fintype.card {e : Edge V // ¬ IsCross K e}) := by
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool]
      _ = (2 ^ k - 1) ^ (Fintype.card V - k)
            * 2 ^ (Fintype.card {e : Edge V // ¬ IsCross K e}) := by
          rw [hcardBlock, hcardKc]
      _ ≤ (2 ^ k - 1) ^ (Fintype.card V - k)
            * 2 ^ (Fintype.card (Edge V) - k * (Fintype.card V - k)) := by
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hcardNon)

/-! ## First-moment instantiation -/

/-- **Tournament domination lower bound (first-moment method).**
If `C(n,k) · (2^k - 1)^{n-k} < 2^{k(n-k)}` (the classical
`C(n,k)(1 - 2^{-k})^{n-k} < 1`), then there is a tournament on `V` in which no
`k`-set dominates — i.e. a tournament with domination number `> k`.  Proved by
instantiating the abstract engine `ProbMethod.Core.exists_good_of_card_bound`
over the sample space of orientations, with the per-set count `card_dominates_le`
as the uniform union bound. -/
theorem exists_no_dominating_kset (k : ℕ)
    (hcross : k * (Fintype.card V - k) ≤ Fintype.card (Edge V))
    (hclassical : (Fintype.card V).choose k * (2 ^ k - 1) ^ (Fintype.card V - k)
        < 2 ^ (k * (Fintype.card V - k))) :
    ∃ T : Edge V → Bool, ∀ K : Finset V, K.card = k → ¬ Dominates K T := by
  classical
  set n := Fintype.card V with hn
  set cE := Fintype.card (Edge V) with hcE
  set B := (2 ^ k - 1) ^ (n - k) * 2 ^ (cE - k * (n - k)) with hB
  set s := (univ : Finset V).powersetCard k with hs
  -- Uniform union bound: every "K dominates" event has size ≤ B.
  have hbound : ∀ K ∈ s, (dominatingSet K).card ≤ B := by
    intro K hKmem
    rw [hs, mem_powersetCard] at hKmem
    exact card_dominates_le K hKmem.2
  -- Size of the sample space and of the index family.
  have hΩ : Fintype.card (Edge V → Bool) = 2 ^ cE := by
    rw [hcE]; simp
  have hscard : s.card = n.choose k := by
    rw [hs, card_powersetCard, card_univ, hn]
  -- The total mass is below |Ω|.
  have hlt : s.card * B < Fintype.card (Edge V → Bool) := by
    rw [hΩ, hscard, hB]
    have hsplit : (2 : ℕ) ^ cE = 2 ^ (k * (n - k)) * 2 ^ (cE - k * (n - k)) := by
      rw [← pow_add, Nat.add_sub_cancel' hcross]
    rw [hsplit]
    have hpos : 0 < 2 ^ (cE - k * (n - k)) := pow_pos (by norm_num) _
    calc n.choose k * ((2 ^ k - 1) ^ (n - k) * 2 ^ (cE - k * (n - k)))
        = (n.choose k * (2 ^ k - 1) ^ (n - k)) * 2 ^ (cE - k * (n - k)) := by ring
      _ < 2 ^ (k * (n - k)) * 2 ^ (cE - k * (n - k)) :=
          (Nat.mul_lt_mul_right hpos).mpr hclassical
  -- Apply the abstract first-moment engine.
  obtain ⟨T, hT⟩ :=
    ProbMethod.Core.exists_good_of_card_bound (Ω := Edge V → Bool) s dominatingSet B hbound hlt
  refine ⟨T, fun K hKcard => ?_⟩
  have hKmem : K ∈ s := by
    rw [hs, mem_powersetCard]; exact ⟨subset_univ K, hKcard⟩
  have hnot := hT K hKmem
  rw [dominatingSet, mem_filter] at hnot
  push_neg at hnot
  exact hnot (mem_univ T)

/-! ## Concrete witness: the cyclic triangle -/

/-- **Smallest instance.** With `k = 1`, `n = 3` the criterion reads
`3 · 1 = 3 < 4 = 2^{1·2}`, so there is a `3`-vertex tournament with no dominating
*single* vertex — the cyclic triangle `0 → 1 → 2 → 0`.  No vertex beats both
others, so the domination number is `> 1`. -/
theorem exists_no_dominating_vertex_Fin3 :
    ∃ T : Edge (Fin 3) → Bool, ∀ K : Finset (Fin 3), K.card = 1 → ¬ Dominates K T := by
  apply exists_no_dominating_kset (V := Fin 3) 1
  · decide
  · decide

end ProbMethod.Tournament
