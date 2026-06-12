/-
Copyright (c) 2026 Field Effect Institute. All rights reserved.

# Hexad Order-6 Cyclic Forcing

Companion files in this repository:
- `BennettPeriodicTableZ9Z.lean` (positive backbone: supplies the explicit S₃ group and the doubling cycle)
- `EnneagramHexadDerivability.lean` (negative companion: the commutativity obstruction)

## Claim

For any 6-element set H with a 6-cycle s ∈ Sym(H):

- (T1) Any order-6 subgroup of Sym(H) containing s equals ⟨s⟩.
- (T2) Such a subgroup is isomorphic to ℤ/6ℤ.
- (T3) No copy of S₃ ≤ Sym(H) contains s (since |s| = 6 and S₃ has element
       orders only in {1, 2, 3}).

These three pin the hexad's Z/6Z vs S3 disjunction at the level of Sym(H)
permutations: Z/6Z is forced by the successor data alone, while S3 cannot
be realized as a subgroup containing the 6-cycle. The two order-6 structures
on a 6-element carrier are thus witnessed by disjoint subgroups of Sym(H),
not by a single ambient group. This is the elementary finite-group kernel
under the fence-irreducibility results in `SubstrateFenceIrreducibility.lean`.
-/

import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace HexadOrderSixForcing

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- T1: An order-6 subgroup of Sym(H) containing a 6-cycle equals ⟨s⟩. -/
theorem order_six_subgroup_containing_six_cycle_is_cyclic
    (s : Equiv.Perm α) (hs : orderOf s = 6)
    (G : Subgroup (Equiv.Perm α))
    (hG : Nat.card G = 6) (hsG : s ∈ G) :
    G = Subgroup.zpowers s := by
  have h_zpow_card : Nat.card (Subgroup.zpowers s) = 6 := by
    rw [Nat.card_zpowers, hs]
  have h_le : Subgroup.zpowers s ≤ G := Subgroup.zpowers_le.mpr hsG
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; decide)
  exact (Subgroup.eq_of_le_of_card_ge h_le (by rw [hG, h_zpow_card])).symm

omit [Fintype α] [DecidableEq α] in
/-- T2: Such a G is cyclic of order 6, hence ≃* Multiplicative (ZMod 6). -/
theorem order_six_subgroup_containing_six_cycle_is_Z6
    (s : Equiv.Perm α) (hs : orderOf s = 6)
    (G : Subgroup (Equiv.Perm α))
    (hG : Nat.card G = 6) (hsG : s ∈ G) :
    Nonempty (G ≃* Multiplicative (ZMod 6)) := by
  rw [order_six_subgroup_containing_six_cycle_is_cyclic s hs G hG hsG]
  -- Goal: Nonempty (Subgroup.zpowers s ≃* Multiplicative (ZMod 6))
  -- `Subgroup.zpowers s` is `IsCyclic` by instance; both groups have card 6,
  -- so `mulEquivOfCyclicCardEq` gives the iso.
  have h_zpow_card : Nat.card (Subgroup.zpowers s) = 6 := by
    rw [Nat.card_zpowers, hs]
  have h_zmod_card : Nat.card (Multiplicative (ZMod 6)) = 6 := by
    simp [Nat.card_eq_fintype_card]
  exact ⟨mulEquivOfCyclicCardEq (h_zpow_card.trans h_zmod_card.symm)⟩

/-- Helper: no element of `Equiv.Perm (Fin 3)` has order 6.
(|S₃| = 6, but S₃ is non-abelian, so it is not cyclic.) -/
lemma perm_fin3_orderOf_ne_six (x : Equiv.Perm (Fin 3)) : orderOf x ≠ 6 := by
  fin_cases x <;> simp +decide [orderOf_eq_iff]

omit [Fintype α] [DecidableEq α] in
/-- T3: No S3 ≤ Sym(H) contains a 6-cycle. -/
theorem no_S3_contains_six_cycle
    (s : Equiv.Perm α) (hs : orderOf s = 6)
    (G : Subgroup (Equiv.Perm α))
    (hiso : Nonempty (G ≃* Equiv.Perm (Fin 3))) (hsG : s ∈ G) : False := by
  rcases hiso with ⟨φ⟩
  have h_order_s : (orderOf (⟨s, hsG⟩ : G)) = 6 := by
    convert hs using 1
    simp +decide
  have h_order_phi_s : orderOf (φ ⟨s, hsG⟩) = 6 := by
    simp +decide [← h_order_s]
  exact absurd h_order_phi_s (perm_fin3_orderOf_ne_six (φ ⟨s, hsG⟩))

end HexadOrderSixForcing
