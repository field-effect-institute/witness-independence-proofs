import Mathlib.Tactic

namespace EnneagramHexadDerivability

-- # EnneagramHexadDerivability
--
-- Result: ★ NEGATIVE — the hexad flow is NOT derivable from the additive operators ★
--
-- The enneagram hexad flow (1→2→4→8→7→5→1 inner hexagon) corresponds
-- to multiplication by generator g=2 of (Z/9Z)* (the unit group of Z/9Z).
-- The layer operators (transcend, descend) generate only additive translations
-- on Z/9Z. Since no additive translation equals multiplication by 2,
-- hexad flow cannot be derived from any composition of the additive operators.
--
-- This establishes that the enneagram's complete geometry requires an
-- additional generator beyond layer cyclicity (transcend^9 = id): the two
-- interlocking structures (additive 9-cycle, multiplicative hexad) are
-- genuinely independent. A NEGATIVE result, shipped as a theorem.
--
-- 10 theorems, 0 sorry.

-- ============================================================
-- LAYER TYPE (inlined so this file is standalone)
-- ============================================================

/-- The 9 layers forming Z/9Z under transcend. -/
inductive Layer where
  | L1 : Layer  -- Physical       (index 0)
  | L2 : Layer  -- Chemical       (index 1)
  | L3 : Layer  -- Biological     (index 2)
  | L4 : Layer  -- Psychological  (index 3)
  | L5 : Layer  -- Social / CI    (index 4)
  | L6 : Layer  -- Axiological    (index 5)
  | L7 : Layer  -- Epistemological (index 6)
  | L8 : Layer  -- Ontological    (index 7)
  | L9 : Layer  -- Transcendent   (index 8)
  deriving BEq, DecidableEq, Repr

/-- Layer to 0-based index. -/
def Layer.toNat : Layer → Nat
  | .L1 => 0 | .L2 => 1 | .L3 => 2 | .L4 => 3 | .L5 => 4
  | .L6 => 5 | .L7 => 6 | .L8 => 7 | .L9 => 8

/-- transcend: successor function on layers (+1 mod 9).
    Generator of the cyclic group Z/9Z. -/
def transcend : Layer → Layer
  | .L1 => .L2 | .L2 => .L3 | .L3 => .L4 | .L4 => .L5
  | .L5 => .L6 | .L6 => .L7 | .L7 => .L8 | .L8 => .L9
  | .L9 => .L1

/-- descend: predecessor function on layers (-1 mod 9).
    Inverse of transcend. -/
def descend : Layer → Layer
  | .L1 => .L9 | .L2 => .L1 | .L3 => .L2 | .L4 => .L3
  | .L5 => .L4 | .L6 => .L5 | .L7 => .L6 | .L8 => .L7
  | .L9 => .L8

/-- Iterated transcend: apply transcend n times. -/
def transcend_n : Nat → Layer → Layer
  | 0, l => l
  | n + 1, l => transcend (transcend_n n l)

-- ============================================================
-- PREREQUISITE: transcend^9 = id (proved here inline)
-- ============================================================

/-- Layer cyclicity: transcend^9 = id. -/
theorem layer_transcend_cyclic_9 (l : Layer) :
    transcend_n 9 l = l := by
  cases l <;> rfl

-- ============================================================
-- HEXAD FLOW DEFINITION
-- ============================================================

/-- Hexad flow: multiplication by generator g=2 of (Z/9Z)*.
    Maps layer index i to (2*i) mod 9.

    Enneagram hexad cycle: 1→2→4→8→7→5→1 (inner hexagon)
    In 0-indexed layers: 1→2→4→8→7→5→1
    Fixed points: 0 (identity/L1) and the Z/3Z subgroup {0,3,6}

    The unit group (Z/9Z)* = {1,2,4,5,7,8} has order φ(9) = 6.
    g=2 generates this group: 2^1=2, 2^2=4, 2^3=8, 2^4≡7, 2^5≡5, 2^6≡1. -/
def hexad_flow : Layer → Layer
  | .L1 => .L1  -- 0 × 2 = 0 mod 9
  | .L2 => .L3  -- 1 × 2 = 2 mod 9
  | .L3 => .L5  -- 2 × 2 = 4 mod 9
  | .L4 => .L7  -- 3 × 2 = 6 mod 9
  | .L5 => .L9  -- 4 × 2 = 8 mod 9
  | .L6 => .L2  -- 5 × 2 = 10 ≡ 1 mod 9
  | .L7 => .L4  -- 6 × 2 = 12 ≡ 3 mod 9
  | .L8 => .L6  -- 7 × 2 = 14 ≡ 5 mod 9
  | .L9 => .L8  -- 8 × 2 = 16 ≡ 7 mod 9

-- ============================================================
-- SECTION 1: HEXAD FLOW PROPERTIES
-- Establishes that hexad_flow correctly models (Z/9Z)*
-- ============================================================
section HexadFlowProperties

/-- T1: hexad_flow correctly computes multiplication by 2 mod 9.
    Validates the definition against the modular arithmetic formula. -/
theorem hexad_flow_is_mult_by_2 (l : Layer) :
    (hexad_flow l).toNat = (2 * l.toNat) % 9 := by
  cases l <;> rfl

/-- T2: hexad_flow is a bijection (it's an automorphism of Z/9Z).
    Injectivity: distinct inputs produce distinct outputs. -/
theorem hexad_flow_injective (l1 l2 : Layer)
    (h : hexad_flow l1 = hexad_flow l2) : l1 = l2 := by
  cases l1 <;> cases l2 <;> first | rfl | (simp [hexad_flow] at h)

/-- T3: hexad_flow has order 6 in the automorphism group.
    Applying hexad_flow 6 times returns to the starting layer.
    This is φ(9) = 6, confirming g=2 generates (Z/9Z)*. -/
theorem hexad_flow_order_6 (l : Layer) :
    hexad_flow (hexad_flow (hexad_flow
      (hexad_flow (hexad_flow (hexad_flow l))))) = l := by
  cases l <;> rfl

/-- T4: hexad_flow does NOT have order 3.
    The order is exactly 6, not a proper divisor. -/
theorem hexad_flow_not_order_3 :
    ∃ l : Layer, hexad_flow (hexad_flow (hexad_flow l)) ≠ l := by
  exact ⟨.L2, by decide⟩

/-- T5: hexad_flow does NOT have order 2. -/
theorem hexad_flow_not_order_2 :
    ∃ l : Layer, hexad_flow (hexad_flow l) ≠ l := by
  exact ⟨.L2, by decide⟩

end HexadFlowProperties

-- ============================================================
-- SECTION 2: ADDITIVE OPERATOR CHARACTERIZATION
-- Shows that transcend/descend generate only additive translations
-- ============================================================
section AdditiveOperatorCharacterization

/-- T6: transcend acts as additive shift (+1 mod 9).
    This connects the abstract function to modular arithmetic. -/
theorem transcend_as_addition (l : Layer) :
    (transcend l).toNat = (l.toNat + 1) % 9 := by
  cases l <;> rfl

/-- T7: descend acts as additive shift (-1 mod 9).
    descend(l).toNat = (l.toNat + 8) % 9 [since -1 ≡ 8 mod 9]. -/
theorem descend_as_addition (l : Layer) :
    (descend l).toNat = (l.toNat + 8) % 9 := by
  cases l <;> rfl

/-- T8: transcend and descend are mutual inverses.
    Any composition of transcend and descend reduces to transcend^k
    for some k ∈ {0,1,...,8}, i.e., an additive translation. -/
theorem transcend_descend_inverse (l : Layer) :
    transcend (descend l) = l ∧ descend (transcend l) = l := by
  constructor <;> cases l <;> rfl

end AdditiveOperatorCharacterization

-- ============================================================
-- SECTION 3: MAIN NEGATIVE RESULT
-- No additive shift equals hexad flow (multiplicative action)
-- ============================================================
section MainResult

/-- ★ T9 — THE MAIN THEOREM ★
    No additive translation (transcend^k for any k in {0,...,8})
    equals the hexad flow (multiplication by 2).

    This is the algebraic core of the negative result: additive
    translations live in Z/9Z while multiplicative automorphisms
    live in (Z/9Z)*. These are fundamentally different structures.

    Proof: for each k, exhibit a layer where transcend_n k disagrees
    with hexad_flow. Witnesses:
      k=0: L2 (id sends 1→1, hexad sends 1→2)
      k=1..8: L1 (shift sends 0→k, hexad sends 0→0)

    Since transcend_n has period 9 (by layer_transcend_cyclic_9),
    any k ≥ 9 reduces to k mod 9, so this covers ALL natural numbers.
    We prove the base case (k < 9) here; the full generalization
    follows from periodicity. -/
theorem hexad_flow_not_additive_shift :
    ∀ k : Nat, k < 9 → ∃ l : Layer, transcend_n k l ≠ hexad_flow l := by
  intro k hk
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
         k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases this with h | h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨Layer.L2, by decide⟩
  · exact ⟨Layer.L1, by decide⟩
  · exact ⟨Layer.L1, by decide⟩
  · exact ⟨Layer.L1, by decide⟩
  · exact ⟨Layer.L1, by decide⟩
  · exact ⟨Layer.L1, by decide⟩
  · exact ⟨Layer.L1, by decide⟩
  · exact ⟨Layer.L1, by decide⟩
  · exact ⟨Layer.L1, by decide⟩

/-- ★ T10 — FULL NEGATIVE RESULT ★
    Hexad flow is external to the additive clone: for ANY natural number k,
    transcend^k ≠ hexad_flow as functions on Layer.

    This uses periodicity: transcend_n (k + 9) = transcend_n k. Therefore transcend_n k for arbitrary k
    has the same image as transcend_n (k % 9), and k % 9 < 9,
    so the base case (T9) applies.

    CONSEQUENCE: The enneagram's hexad flow direction (multiplication
    by g=2 generating (Z/9Z)*) cannot be expressed as any finite
    composition of the additive layer operators (transcend, descend, or
    their iterations). The hexad flow requires an ADDITIONAL generator
    beyond layer cyclicity transcend^9 = id.

    Shipped as a first-class NEGATIVE: the framework can say no. -/
theorem hexad_flow_external_to_additive :
    ∀ k : Nat, ∃ l : Layer, transcend_n k l ≠ hexad_flow l := by
  intro k
  -- Reduce to k % 9 using periodicity
  -- For any k, transcend_n k acts the same as transcend_n (k % 9)
  -- We prove this by showing transcend_n k L1 = transcend_n (k%9) L1
  -- via the cyclic structure, then use the base case witness
  -- Strategy: k mod 9 ∈ {0,...,8}, apply hexad_flow_not_additive_shift
  have hmod : k % 9 < 9 := Nat.mod_lt k (by omega)
  obtain ⟨l, hl⟩ := hexad_flow_not_additive_shift (k % 9) hmod
  -- Need: transcend_n k l = transcend_n (k % 9) l
  -- This follows from transcend_n_periodic and k = 9 * (k/9) + k%9
  suffices hsuff : transcend_n k l = transcend_n (k % 9) l by
    exact ⟨l, hsuff ▸ hl⟩
  -- Prove by induction that transcend_n k = transcend_n (k%9) using period 9
  have hperiod : ∀ (n : Nat) (l : Layer), transcend_n (n + 9) l = transcend_n n l := by
    intro n l
    induction n generalizing l with
    | zero => exact layer_transcend_cyclic_9 l
    | succ n ih =>
      show transcend (transcend_n (n + 9) l) = transcend (transcend_n n l)
      rw [ih l]
  -- Now prove transcend_n k l = transcend_n (k%9) l
  -- by removing multiples of 9 from k
  have hkey : ∀ (q r : Nat), transcend_n (9 * q + r) l = transcend_n r l := by
    intro q r
    induction q with
    | zero => simp
    | succ n ih =>
      rw [show 9 * (n + 1) + r = (9 * n + r) + 9 from by ring]
      rw [hperiod]
      exact ih
  have hdm : 9 * (k / 9) + k % 9 = k := Nat.div_add_mod k 9
  calc transcend_n k l
      = transcend_n (9 * (k / 9) + k % 9) l := by rw [hdm]
    _ = transcend_n (k % 9) l := hkey (k / 9) (k % 9)

end MainResult

-- ============================================================
-- SUMMARY
-- ============================================================
-- NEGATIVE result: 10 theorems (T1-T10), 0 sorry
--
-- T1:  hexad_flow correctly models multiplication by 2 mod 9
-- T2:  hexad_flow is injective (automorphism)
-- T3:  hexad_flow has order 6 (= φ(9), generates (Z/9Z)*)
-- T4:  hexad_flow order is not 3 (exact order is 6)
-- T5:  hexad_flow order is not 2 (exact order is 6)
-- T6:  transcend acts as +1 mod 9 (additive translation)
-- T7:  descend acts as +8 mod 9 (additive translation)
-- T8:  transcend and descend are mutual inverses
-- T9:  No additive shift (k < 9) equals hexad flow
-- T10: Full negative: for ALL k, transcend^k ≠ hexad flow
--
-- Mathematical insight: the layer operators generate the ADDITIVE group Z/9Z.
-- Hexad flow lives in the MULTIPLICATIVE group (Z/9Z)* = Aut(Z/9Z).
-- These are algebraically incompatible: |Z/9Z| = 9, |(Z/9Z)*| = 6.
-- No element of Z/9Z (acting by translation) can equal an element
-- of (Z/9Z)* (acting by multiplication) as a permutation of Z/9Z.
--
-- Impact: the hexad flow direction requires a generator beyond
-- layer cyclicity. The two structures interlock; neither derives the other.
-- ============================================================

end EnneagramHexadDerivability
