/-
  Erdős Problem #44: Sidon Set Lower Bound Construction

  Proves: For any N ≥ 1, there exists a Sidon set A ⊆ {1,...,N} with |A| ≥ ⌊√N⌋/2.

  Construction: The "modular parabola" — for prime p, the set
    S_p = {2ap + (a² mod p) : a = 0, 1, ..., p-1}
  is a Sidon set with p elements in [0, 2p²-p-1].

  The factor of 2 is essential: it ensures that in the equation
    f(a)+f(b) = f(c)+f(d)
  the integer quotient forces a+b = c+d exactly (no carry), after which
  the standard quadratic root argument over ℤ/pℤ finishes the proof.

  Key references:
  - Erdős-Turán (1941): Original construction
  - Lindström (1969): Simplified presentation
-/
import Mathlib
import Proofs.Erdos340GreedySidon

open Finset BigOperators

namespace Erdos44

open Erdos340

/- ## The Modular Parabola Construction -/

/-- The modular parabola function: f(a) = 2*a*p + (a² mod p). -/
def modParabolaFn (p : ℕ) (a : ℕ) : ℕ := 2 * a * p + a ^ 2 % p

/-- The modular parabola Sidon set: first k elements, shifted to start at 1. -/
def modParabola (p : ℕ) (k : ℕ) : Finset ℕ :=
  (range k).image (fun a => modParabolaFn p a + 1)

/- ## Basic Properties -/

/-- The modular parabola function is strictly monotone for p ≥ 1. -/
lemma modParabolaFn_strictMono {p : ℕ} (hp : 1 ≤ p) : StrictMono (modParabolaFn p) := by
  intro a b hab
  unfold modParabolaFn
  have ha_rem : a ^ 2 % p < p := Nat.mod_lt _ (by omega)
  have hb_rem : b ^ 2 % p < p := Nat.mod_lt _ (by omega)
  -- f(b) ≥ 2bp > 2ap + (p-1) ≥ f(a)
  calc 2 * a * p + a ^ 2 % p
      < 2 * a * p + p := by omega
    _ ≤ 2 * b * p := by nlinarith
    _ ≤ 2 * b * p + b ^ 2 % p := by omega

/-- The modular parabola has exactly k elements when k ≤ p and p ≥ 1. -/
lemma modParabola_card {p k : ℕ} (hp : 1 ≤ p) (hk : k ≤ p) :
    (modParabola p k).card = k := by
  unfold modParabola
  rw [card_image_of_injective]
  · exact card_range k
  · intro a b hab
    simp only at hab
    have : modParabolaFn p a = modParabolaFn p b := by omega
    exact (modParabolaFn_strictMono hp).injective this

/-- Elements of the modular parabola are in [1, 2kp]. -/
lemma modParabola_subset_Icc {p k : ℕ} (hp : 1 ≤ p) (hk : k ≤ p) :
    modParabola p k ⊆ Icc 1 (2 * k * p) := by
  intro x hx
  simp only [modParabola, mem_image, mem_range] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [mem_Icc]
  constructor
  · omega
  · unfold modParabolaFn
    have : a ^ 2 % p < p := Nat.mod_lt _ (by omega)
    nlinarith

/- ## The Sidon Property -/

/-- **The modular parabola is Sidon** (for prime p).

    Proof: From f(a)+f(b)=f(c)+f(d) where f(x) = 2xp + x²%p:
    1. The 2p factor forces a+b=c+d (no carry: remainders < 2p)
    2. Remainders match: a²%p+b²%p = c²%p+d²%p, giving a²+b² ≡ c²+d² (mod p)
    3. Algebraic identity: when x+y=u+v, x²+y²-u²-v² = 2(x-u)(x-v)
    4. So 2(a-c)(a-d) ≡ 0 (mod p); for odd prime p, (a-c)(a-d) ≡ 0
    5. Since p is prime (ZMod p is a field): p | (a-c) or p | (a-d)
    6. Since 0 ≤ a,c,d < p: a=c (then b=d) or a=d (then a=b=c=d) -/
theorem modParabola_isSidon (p : ℕ) (hp : Nat.Prime p) :
    IsSidon ((range p).image (modParabolaFn p)) := by
  intro x y u v hx hy hu hv hxy huv heq
  rw [mem_image] at hx hy hu hv
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, rfl⟩ := hu
  obtain ⟨d, hd, rfl⟩ := hv
  rw [mem_range] at ha hb hc hd
  have hab : a ≤ b := by
    by_contra h; push_neg at h
    exact absurd ((modParabolaFn_strictMono hp.one_le).lt_iff_lt.mpr h) (by omega)
  have hcd : c ≤ d := by
    by_contra h; push_neg at h
    exact absurd ((modParabolaFn_strictMono hp.one_le).lt_iff_lt.mpr h) (by omega)
  suffices h : a = c ∧ b = d by
    exact ⟨congr_arg (modParabolaFn p) h.1, congr_arg (modParabolaFn p) h.2⟩
  -- Step 1: "No carry" — extract sum and remainder equalities
  unfold modParabolaFn at heq
  set ra := a ^ 2 % p with hra_def
  set rb := b ^ 2 % p with hrb_def
  set rc := c ^ 2 % p with hrc_def
  set rd := d ^ 2 % p with hrd_def
  have hra : ra < p := Nat.mod_lt _ hp.pos
  have hrb : rb < p := Nat.mod_lt _ hp.pos
  have hrc : rc < p := Nat.mod_lt _ hp.pos
  have hrd : rd < p := Nat.mod_lt _ hp.pos
  -- Rewrite heq in Euclidean division form: q*(2p) + r with r < 2p
  have heq_ed : (a + b) * (2 * p) + (ra + rb) = (c + d) * (2 * p) + (rc + rd) := by
    have h1 : (a + b) * (2 * p) = 2 * a * p + 2 * b * p := by ring
    have h2 : (c + d) * (2 * p) = 2 * c * p + 2 * d * p := by ring
    linarith
  have h_ra_rb_lt : ra + rb < 2 * p := by omega
  have h_rc_rd_lt : rc + rd < 2 * p := by omega
  -- Uniqueness of Euclidean division: quotients and remainders must match
  have h_sum : a + b = c + d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : (a + b) * (2 * p) + 2 * p ≤ (c + d) * (2 * p) := by
        have := mul_le_mul_of_nonneg_right (Nat.succ_le_of_lt h) (Nat.zero_le (2 * p))
        have : (a + b + 1) * (2 * p) = (a + b) * (2 * p) + 2 * p := by ring
        linarith
      linarith
    · have h1 : (c + d) * (2 * p) + 2 * p ≤ (a + b) * (2 * p) := by
        have := mul_le_mul_of_nonneg_right (Nat.succ_le_of_lt h) (Nat.zero_le (2 * p))
        have : (c + d + 1) * (2 * p) = (c + d) * (2 * p) + 2 * p := by ring
        linarith
      linarith
  have h_rem : ra + rb = rc + rd := by
    have := congrArg (· * (2 * p)) h_sum
    linarith [heq_ed]
  -- Handle p = 2 directly (a,b,c,d ∈ {0,1})
  by_cases hp2 : p = 2
  · subst hp2; exact ⟨by omega, by omega⟩
  · -- p is an odd prime (p ≥ 3)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    haveI : Fact p.Prime := ⟨hp⟩
    -- Step 2: Lift to ZMod p
    have h_sum_zmod : (a : ZMod p) + (b : ZMod p) = (c : ZMod p) + (d : ZMod p) := by
      have := congrArg (Nat.cast (R := ZMod p)) h_sum
      push_cast at this; exact this
    -- Bridge: (n²%p : ZMod p) = (n : ZMod p)² since they differ by a multiple of p
    have mod_sq (n : ℕ) : ((n ^ 2 % p : ℕ) : ZMod p) = (n : ZMod p) ^ 2 := by
      rw [← Nat.cast_pow]
      conv_rhs => rw [show (n ^ 2 : ℕ) = p * (n ^ 2 / p) + n ^ 2 % p
                       from (Nat.div_add_mod _ _).symm]
      push_cast
      simp only [CharP.cast_eq_zero (ZMod p) p, zero_mul, zero_add]
    have h_sq_zmod : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 =
                     (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
      have h_cast := congrArg (Nat.cast (R := ZMod p)) h_rem
      push_cast at h_cast
      -- Unfold set variables so mod_sq can match
      rw [hra_def, hrb_def, hrc_def, hrd_def] at h_cast
      rwa [mod_sq a, mod_sq b, mod_sq c, mod_sq d] at h_cast
    -- Step 3: Derive (a-c)(a-d) = 0 in ZMod p via algebraic identity
    have h_prod_zero : ((a : ZMod p) - c) * ((a : ZMod p) - d) = 0 := by
      -- Identity: x²+y²-u²-v² = 2(x-u)(x-v) when x+y=u+v
      have h_identity : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 -
                        (c : ZMod p) ^ 2 - (d : ZMod p) ^ 2 =
                        2 * ((a : ZMod p) - c) * ((a : ZMod p) - d) := by
        have hb_eq : (b : ZMod p) = (c : ZMod p) + (d : ZMod p) - (a : ZMod p) := by
          linear_combination h_sum_zmod
        rw [hb_eq]; ring
      have h_zero : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 -
                    (c : ZMod p) ^ 2 - (d : ZMod p) ^ 2 = 0 := by
        linear_combination h_sq_zmod
      -- 2*(a-c)*(a-d) = 0
      rw [h_identity] at h_zero
      -- (2 : ZMod p) ≠ 0 since p ≥ 3
      have h2_ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have : p ∣ 2 := by
          rwa [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
               ZMod.natCast_eq_zero_iff] at h
        exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
      rw [mul_assoc] at h_zero
      exact (mul_eq_zero.mp h_zero).resolve_left h2_ne
    -- Step 4: Factor in the field ZMod p
    rcases mul_eq_zero.mp h_prod_zero with hac | had
    · -- Case: a ≡ c (mod p), so a = c since a,c < p
      have hac_eq : (a : ZMod p) = (c : ZMod p) := sub_eq_zero.mp hac
      have : a % p = c % p := by
        have := congrArg ZMod.val hac_eq
        rwa [ZMod.val_natCast, ZMod.val_natCast] at this
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this
      exact ⟨this, by omega⟩
    · -- Case: a ≡ d (mod p), so a = d, then b = c, and a ≤ b = c ≤ d = a
      have had_eq : (a : ZMod p) = (d : ZMod p) := sub_eq_zero.mp had
      have : a % p = d % p := by
        have := congrArg ZMod.val had_eq
        rwa [ZMod.val_natCast, ZMod.val_natCast] at this
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd] at this
      -- a = d and b = c (from h_sum), but a ≤ b and c ≤ d, so a = b = c = d
      exact ⟨by omega, by omega⟩

/- ## Subset Sidon -/

/-- The first k elements of a Sidon set form a Sidon set. -/
theorem modParabola_k_isSidon (p k : ℕ) (hp : Nat.Prime p) (hk : k ≤ p) :
    IsSidon ((range k).image (modParabolaFn p)) := by
  apply Erdos340.IsSidon.subset (modParabola_isSidon p hp)
  apply image_subset_image
  intro x hx
  rw [mem_range] at hx ⊢
  omega

/-- Shifting all elements by a constant preserves the Sidon property. -/
lemma isSidon_map_add_const (A : Finset ℕ) (c : ℕ) (hA : IsSidon A) :
    IsSidon (A.image (· + c)) := by
  intro x y u v hx hy hu hv hxy huv heq
  rw [mem_image] at hx hy hu hv
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  have ⟨h1, h2⟩ := hA x' y' u' v' hx' hy' hu' hv' (by omega) (by omega) (by omega)
  exact ⟨by omega, by omega⟩

/-- modParabola is the shifted image of the unshifted construction. -/
lemma modParabola_eq_image_add {p k : ℕ} :
    modParabola p k = ((range k).image (modParabolaFn p)).image (· + 1) := by
  unfold modParabola
  ext x
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨modParabolaFn p a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- The shifted modular parabola is Sidon. -/
theorem modParabola_shifted_isSidon (p k : ℕ) (hp : Nat.Prime p) (hk : k ≤ p) :
    IsSidon (modParabola p k) := by
  rw [modParabola_eq_image_add]
  exact isSidon_map_add_const _ 1 (modParabola_k_isSidon p k hp hk)

/- ## The Main Lower Bound Theorem -/

/-- **Theorem**: For any N ≥ 1, there exists a Sidon set A ⊆ {1,...,N}
    with |A| ≥ ⌊√N⌋/2.

    Construction:
    1. Let s = ⌊√N⌋, k = s/2
    2. By Bertrand's postulate, find prime p with k < p ≤ 2k ≤ s
    3. The first k elements of the modular parabola {2ap + a²%p + 1}
       form a Sidon set in [1, 2kp] ⊆ [1, s²] ⊆ [1, N]
    4. This set has k = ⌊√N⌋/2 elements -/
theorem sidon_set_lower_bound_exists (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ IsSidon A ∧ Nat.sqrt N / 2 ≤ A.card := by
  set s := Nat.sqrt N with hs_def
  set k := s / 2 with hk_def
  by_cases hk0 : k = 0
  · -- k = 0: empty set works (need |A| ≥ 0)
    exact ⟨∅, empty_subset _, isSidon_empty, by simp [hk0]⟩
  · -- k ≥ 1: use Bertrand's postulate
    -- Find prime p with k < p ≤ 2k
    obtain ⟨p, hp_prime, hk_lt_p, hp_le_2k⟩ :=
      Nat.exists_prime_lt_and_le_two_mul k hk0
    -- p ≤ 2k = 2*(s/2) ≤ s
    have hp_le_s : p ≤ s := by
      have : 2 * (s / 2) ≤ s := by omega
      omega
    have hk_le_p : k ≤ p := le_of_lt hk_lt_p
    -- The Sidon set: first k elements of the shifted modular parabola
    refine ⟨modParabola p k, ?_, ?_, ?_⟩
    · -- Subset: A ⊆ Icc 1 N
      intro x hx
      have hx_bound := modParabola_subset_Icc hp_prime.one_le hk_le_p hx
      simp only [mem_Icc] at hx_bound ⊢
      refine ⟨hx_bound.1, le_trans hx_bound.2 ?_⟩
      -- 2kp ≤ 2k·s ≤ s·s ≤ N
      -- s² ≤ N is the defining property of Nat.sqrt
      have hsq : s * s ≤ N := by
        -- (Nat.sqrt N)² ≤ N is the fundamental floor-sqrt property
        rw [hs_def]; exact Nat.sqrt_le N
      have : 2 * k * p ≤ s * s := by
        have : 2 * (s / 2) ≤ s := by omega
        nlinarith
      linarith
    · -- Sidon: first k elements of the shifted modular parabola
      exact modParabola_shifted_isSidon p k hp_prime hk_le_p
    · -- Size: |A| = k = s/2
      rw [modParabola_card hp_prime.one_le hk_le_p]

end Erdos44
