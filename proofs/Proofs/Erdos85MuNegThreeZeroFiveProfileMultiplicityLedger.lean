import Mathlib

/-! # Arithmetic ledger for the h305 service-profile multiplicities -/

namespace Erdos85

/-- Multiplicities of the three same-shore profiles on each shore and the
four cross-shore profiles, together with the three type-transition handshake
equations. -/
structure H305ProfileMultiplicityLedger where
  u0 : ℕ
  u1 : ℕ
  u2 : ℕ
  y0 : ℕ
  y1 : ℕ
  y2 : ℕ
  y3 : ℕ
  v0 : ℕ
  v1 : ℕ
  v2 : ℕ
  u_total : u0 + u1 + u2 = 12
  y_total : y0 + y1 + y2 + y3 = 24
  v_total : v0 + v1 + v2 = 12
  handshake_u_y : 4 * u0 + 2 * u1 = y1 + 2 * y2 + 3 * y3
  handshake_y_v : y1 + 2 * y2 + 3 * y3 = 4 * v0 + 2 * v1
  handshake_u_v : 2 * u0 + 3 * u1 + 4 * u2 =
    2 * v0 + 3 * v1 + 4 * v2
  u1_even : Even (u1 : ℕ)
  v1_even : Even (v1 : ℕ)

/-- The two shore handshake equations give the same halved balance. -/
theorem H305ProfileMultiplicityLedger.shore_half_balance
    (L : H305ProfileMultiplicityLedger) :
    2 * L.u0 + L.u1 = 2 * L.v0 + L.v1 := by
  have h := L.handshake_u_y.trans L.handshake_y_v
  omega

/-- After using the twelve-edge populations, the imbalance between the two
extreme same-shore profiles is identical on both shores. -/
theorem H305ProfileMultiplicityLedger.shore_extreme_balance
    (L : H305ProfileMultiplicityLedger) :
    L.u0 + L.v2 = L.v0 + L.u2 := by
  have hhalf := L.shore_half_balance
  have hu := L.u_total
  have hv := L.v_total
  omega

/-- Cross profiles with an odd same-shore count occur with even total
multiplicity. -/
theorem H305ProfileMultiplicityLedger.cross_odd_profiles_even
    (L : H305ProfileMultiplicityLedger) : Even (L.y1 + L.y3) := by
  obtain ⟨k, hk⟩ := L.u1_even
  have h := L.handshake_u_y
  refine ⟨2 * L.u0 + 2 * k - L.y2 - L.y3, ?_⟩
  omega

/-- Consequently the complementary pair of cross profiles also has even
total multiplicity. -/
theorem H305ProfileMultiplicityLedger.cross_even_profiles_even
    (L : H305ProfileMultiplicityLedger) : Even (L.y0 + L.y2) := by
  obtain ⟨k, hk⟩ := L.cross_odd_profiles_even
  have h := L.y_total
  refine ⟨12 - k, ?_⟩
  omega

/-- The weighted cross-to-shore transition count is even. -/
theorem H305ProfileMultiplicityLedger.cross_transition_even
    (L : H305ProfileMultiplicityLedger) :
    Even (L.y1 + 2 * L.y2 + 3 * L.y3) := by
  have h := L.handshake_u_y
  refine ⟨2 * L.u0 + L.u1, ?_⟩
  omega

/-- The middle-profile parity on one shore is equivalent to that on the
other once the handshake equations hold. -/
theorem H305ProfileMultiplicityLedger.middle_parity_agrees
    (L : H305ProfileMultiplicityLedger) :
    L.u1 % 2 = L.v1 % 2 := by
  obtain ⟨ku, hku⟩ := L.u1_even
  obtain ⟨kv, hkv⟩ := L.v1_even
  omega

end Erdos85

#print axioms Erdos85.H305ProfileMultiplicityLedger.shore_half_balance
#print axioms Erdos85.H305ProfileMultiplicityLedger.cross_odd_profiles_even
