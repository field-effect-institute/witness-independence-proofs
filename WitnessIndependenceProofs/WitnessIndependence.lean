import Mathlib.Tactic

/-!
  ## WitnessIndependence — Two-axis decomposability of witness independence

  The *witness-independence* relation between two attestors decomposes into two
  structurally distinct axes:
  - **model-independence**  — a different computational system produced the attestation
    (e.g. a different LLM family running the same Lean kernel);
  - **facet-independence**  — a different *kind* of attestation (e.g. algebraic certification
    vs. interpretive judgement of fit).

  An attestor is modelled as a point `⟨model, facet⟩ : Attestor`; `SameModel`/`SameFacet`
  are the two coordinate kernels (genuine equivalence relations), and `IndepM`/`IndepF`
  are their negations.

  | Target | Theorem(s) | Content |
  |---|---|---|
  | **T1** non-collinearity | `axes_not_collinear`, `indepM_ne_indepF` | the two axes are not the same relation — each can hold while the other fails |
  | **T2** non-aggregation  | `shared_axis_strictly_weaker`, `nonaggregation_witness`, `axesIndep_le_two`, `axesIndep_shared_le_one` | co-attestation evidence is *capped* by axis-independence; two witnesses that share an axis are strictly weaker than two independent on both axes (witness count does not simply aggregate) |
  | **T3** coupling-pricing | `coupling_self`, `coupling_le_one`, `coupling_eq_one_iff`, `vcoupling_fst`, `vcoupling_snd`, `priceIndep_eq_zero_iff`, `priceIndep_pos_witness` | a scalar coupling `1 − |a−b|/R` (a form taken from a separate result outside this repository; every theorem about it is proved here, self-contained) lifts to a per-axis vector; each component is the *unchanged* scalar coupling (reduction), so the scalar theorems transfer; the aggregate independence *price* is `0` iff both axes coincide |

  **Non-vacuity gate.** `nonaggregation_witness` (the evidence observable provably takes a
  strictly smaller value on a shared-axis pair) and `priceIndep_pos_witness` (the price
  observable provably takes a strictly positive value) jointly witness that the structures
  are non-degenerate: the inequalities and the iff are not vacuously true.

  **Honest scope.** These theorems are about the encoded two-coordinate structure defined
  below. Whether two real attestors are "model-independent" or "facet-independent" is a
  judgement about the world; the theorems govern what follows *once that judgement is made*.

  15 theorems, 0 sorry. Mathlib-only.
-/

namespace WitnessIndependence

/-- An attestor carries two coordinates: which computational `model` produced it, and
    which `facet` (kind of property) it certifies. -/
structure Attestor where
  model : ℕ
  facet : ℕ
deriving DecidableEq, Repr

/-- Same computational substrate. -/
def SameModel (a b : Attestor) : Prop := a.model = b.model
/-- Same kind of attestation. -/
def SameFacet (a b : Attestor) : Prop := a.facet = b.facet

/-- Model-independence: distinct computational substrate. -/
def IndepM (a b : Attestor) : Prop := a.model ≠ b.model
/-- Facet-independence: distinct kind of attestation. -/
def IndepF (a b : Attestor) : Prop := a.facet ≠ b.facet

/-! ### Both axes are genuine equivalence relations (so negating them is meaningful) -/

theorem sameModel_equiv : Equivalence SameModel :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

theorem sameFacet_equiv : Equivalence SameFacet :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-! ### T1 — Non-collinearity of the two axes -/

/-- The two independence axes are not collinear: there is a pair independent on the model
    axis but *not* the facet axis, and a pair independent on the facet axis but *not* the
    model axis. (The concrete witness form.) -/
theorem axes_not_collinear :
    (∃ a b : Attestor, IndepM a b ∧ ¬ IndepF a b) ∧
    (∃ c d : Attestor, IndepF c d ∧ ¬ IndepM c d) := by
  refine ⟨⟨⟨0, 0⟩, ⟨1, 0⟩, ?_, ?_⟩, ⟨⟨0, 0⟩, ⟨0, 1⟩, ?_, ?_⟩⟩ <;>
    simp only [IndepM, IndepF] <;> decide

/-- The abstract form: model-independence and facet-independence are *different relations*. -/
theorem indepM_ne_indepF : (IndepM : Attestor → Attestor → Prop) ≠ IndepF := by
  intro h
  have h2 := congrFun (congrFun h ⟨0, 0⟩) ⟨1, 0⟩
  simp only [IndepM, IndepF] at h2
  rw [eq_iff_iff] at h2
  exact (h2.mp (by decide)) rfl

/-! ### T2 — Witness-count non-aggregation -/

/-- The number of independent axes a co-attestation pair spans (`0`, `1`, or `2`).
    This is the evidence weight a pair contributes: aligned on both axes ⇒ `0`, fully
    independent ⇒ `2`. Witness *count* (always two attestors) is decoupled from witness
    *weight* (axis-independence), which is the content of "witnesses do not aggregate". -/
def axesIndep (a b : Attestor) : ℕ :=
  (if a.model = b.model then 0 else 1) + (if a.facet = b.facet then 0 else 1)

/-- Evidence weight is bounded by `2`: two attestors can span at most two axes. -/
theorem axesIndep_le_two (a b : Attestor) : axesIndep a b ≤ 2 := by
  unfold axesIndep; split_ifs <;> decide

/-- A pair that *shares* an axis spans at most one independent axis. -/
theorem axesIndep_shared_le_one (a b : Attestor)
    (hshare : SameModel a b ∨ SameFacet a b) : axesIndep a b ≤ 1 := by
  rcases hshare with h | h
  · simp only [axesIndep, SameModel] at *
    rw [if_pos h]; split_ifs <;> omega
  · simp only [axesIndep, SameFacet] at *
    rw [if_pos h]; split_ifs <;> omega

/-- **Non-aggregation (main).** Two attestors that share *any* axis constitute strictly
    weaker evidence than two attestors independent on *both* axes — co-attestation evidence
    is capped by axis-independence, not by witness count. -/
theorem shared_axis_strictly_weaker
    (a b a' b' : Attestor)
    (hshare : SameModel a b ∨ SameFacet a b)
    (hindep : IndepM a' b' ∧ IndepF a' b') :
    axesIndep a b < axesIndep a' b' := by
  obtain ⟨h1, h2⟩ := hindep
  have hr : axesIndep a' b' = 2 := by
    simp only [axesIndep, IndepM, IndepF] at h1 h2 ⊢
    rw [if_neg h1, if_neg h2]
  have hl : axesIndep a b ≤ 1 := axesIndep_shared_le_one a b hshare
  omega

/-- Concrete non-vacuity witness for T2: a facet-sharing pair (weight `1`) carries strictly
    less evidence than a both-axes-independent pair (weight `2`). -/
theorem nonaggregation_witness :
    axesIndep ⟨0, 0⟩ ⟨1, 0⟩ < axesIndep ⟨0, 0⟩ ⟨1, 1⟩ := by decide

/-! ### T3 — Coupling-pricing: the vectorial extension of the scalar coupling -/

/-- The abstract scalar coupling: `1 − |a−b|/R`. (The form originates in a separate
    result outside this repository; the theorems below are self-contained.) -/
noncomputable def coupling (a b R : ℝ) : ℝ := 1 - |a - b| / R

theorem coupling_self (a R : ℝ) : coupling a a R = 1 := by
  simp [coupling]

theorem coupling_le_one (a b R : ℝ) (hR : 0 < R) : coupling a b R ≤ 1 := by
  have h : 0 ≤ |a - b| / R := div_nonneg (abs_nonneg _) hR.le
  unfold coupling; linarith

theorem coupling_eq_one_iff (a b R : ℝ) (hR : 0 < R) :
    coupling a b R = 1 ↔ a = b := by
  unfold coupling
  constructor
  · intro h
    have h0 : |a - b| / R = 0 := by linarith
    have habs : |a - b| = 0 := by
      rcases div_eq_zero_iff.mp h0 with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt hR)
    have : a - b = 0 := abs_eq_zero.mp habs
    linarith
  · intro h; subst h; simp

/-- Per-axis coupling vector: model-axis coupling paired with facet-axis coupling. -/
noncomputable def vcoupling (aM bM aF bF R : ℝ) : ℝ × ℝ :=
  (coupling aM bM R, coupling aF bF R)

/-- **Reduction (model component).** The model component of the vectorial coupling is the
    *unchanged* scalar coupling — so every closed scalar theorem transfers verbatim. -/
theorem vcoupling_fst (aM bM aF bF R : ℝ) :
    (vcoupling aM bM aF bF R).1 = coupling aM bM R := rfl

/-- **Reduction (facet component).** Likewise for the facet component. -/
theorem vcoupling_snd (aM bM aF bF R : ℝ) :
    (vcoupling aM bM aF bF R).2 = coupling aF bF R := rfl

/-- Per-axis independence *price*: total departure from full coupling across both axes. -/
noncomputable def priceIndep (aM bM aF bF R : ℝ) : ℝ :=
  (1 - coupling aM bM R) + (1 - coupling aF bF R)

/-- The independence price is `0` iff both axes coincide — i.e. you pay strictly more for
    any genuinely independent axis. -/
theorem priceIndep_eq_zero_iff (aM bM aF bF R : ℝ) (hR : 0 < R) :
    priceIndep aM bM aF bF R = 0 ↔ aM = bM ∧ aF = bF := by
  unfold priceIndep
  have h1 := coupling_le_one aM bM R hR
  have h2 := coupling_le_one aF bF R hR
  constructor
  · intro h
    have e1 : coupling aM bM R = 1 := by linarith
    have e2 : coupling aF bF R = 1 := by linarith
    exact ⟨(coupling_eq_one_iff aM bM R hR).mp e1, (coupling_eq_one_iff aF bF R hR).mp e2⟩
  · rintro ⟨hm, hf⟩
    subst hm; subst hf
    simp [coupling_self]

/-- Concrete non-vacuity witness for T3: a pair maximally independent on both axes at
    `R = 2` pays a strictly positive price of `1`. -/
theorem priceIndep_pos_witness : priceIndep 0 1 0 1 2 = 1 := by
  unfold priceIndep coupling
  simp only [zero_sub, abs_neg, abs_one]
  norm_num

end WitnessIndependence
