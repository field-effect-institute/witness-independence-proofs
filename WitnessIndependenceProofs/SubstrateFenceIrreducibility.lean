import Mathlib.Tactic
import WitnessIndependenceProofs.EnneagramHexadDerivability

/-!
  ## SubstrateFenceIrreducibility — substrate-fence operator irreducibility

  **The pinned definition.**
  *Internal expansion* of a substrate `S` := membership in the **composition closure**
  (the unary fragment of the clone) `⟨O_S⟩` of `S`'s declared primitive operators `O_S`.
  Anything reachable from `O_S` by composition is internal; any operator or base **not** in
  `O_S` is, by definition, an *external axiom* — not an internal expansion. This closes the
  hard-coding loophole (a hard-coded fenced attestation needs a new primitive ⇒ external) and,
  guarded by a non-vacuity gate, dodges the `complement-of-the-closure` circularity.

  **Arity note (load-bearing).** The closure is taken over the declared operators
  *with their declared arities*. For the `human_cognition` exemplar this is the **additive**
  successor `transcend` (= +1 mod 9) only — NOT the ring's multiplication. That arity choice is
  exactly where the result lives: the fenced hexad flow `×2` is outside the additive clone, but
  would be *inside* a clone that declared binary `+` (since `2x = x + x`). Hence extending the result to
  OTHER substrates requires, in each case, that substrate's own declared operator set `O_S`.

  | Target | Theorem(s) | Content |
  |---|---|---|
  | **B.T1** fence-blindness | `fence_blind` | a named fence inventory disciplined into the algebra's silent zone has no base attestation (near-definitional; the discipline hypothesis carries it) |
  | **B.T2** operator irreducibility | `operator_irreducible` | if the operator required to attest a fenced claim is not internally derivable, no internally-derivable operator equals it — the fenced attestor is irreducibly external |
  | non-vacuity gate | `nonvacuity_gate` | a fenced op outside + an admissible op inside ⇒ the internal expansion is a PROPER, non-vacuous sub-structure (neither ⊤ nor ⊥) |
  | **exemplar** (human_cognition) | `hexad_not_derivable`, `human_operator_irreducible`, `human_nonvacuous` | `O_S = {transcend}`; the fenced `hexad_flow` (×2) is provably outside `⟨transcend⟩` — a DIRECT corollary of `EnneagramHexadDerivability.hexad_flow_external_to_additive`; `transcend` is admissible (inside). The negative-control gate is discharged. |

  The exemplar's hard half is the already-proved NEGATIVE result in
  `EnneagramHexadDerivability.lean`; this file is the bridge that wires it to the pinned
  clone-closure definition.

  **Second exemplar — `llm_cognition`**: a second instantiation of the same abstract structure over the
  same `Layer`/`transcend` carrier. Reading (a) is an assumption-free cross-system-dependency
  gate; reading (b) is the finite-group mirror (with the `w_cross|_scope = ×2` identification
  recorded as a declared modelling choice, not proved).

  **Honest scope.** The abstract theorems (B.T1/B.T2/non-vacuity) are unconditional for any
  `InternalExpansion`. Each exemplar is an *encoding* of a cognitive system as a 9-element
  layered cycle with one declared additive primitive — whether that encoding captures the
  real system is a modelling judgement stated where it is made, never proved here.

  18 theorems, 0 sorry. Mathlib + EnneagramHexadDerivability only.
-/

namespace SubstrateFenceIrreducibility

/-! ### Abstract layer — substrate-portable -/

/-- An internal-expansion structure on a carrier `α`: the operators reachable from a substrate's
    declared primitives. To be a genuine internal expansion (a sub-structure of the
    composition monoid `(α → α, ∘, id)`, i.e. the unary fragment of the clone `⟨O_S⟩`), the
    derivability predicate must contain the identity (empty composition) and be closed under
    composition. -/
structure InternalExpansion (α : Type*) where
  Derivable : (α → α) → Prop
  id_mem : Derivable id
  comp_mem : ∀ f g, Derivable f → Derivable g → Derivable (f ∘ g)

/-- **B.T2 (operator irreducibility), abstract.** If the operator `req` required to attest a
    fenced claim is NOT internally derivable, then no internally-derivable operator equals it:
    the fenced-zone attestor is irreducibly external to `S`. (The content is entirely in the
    separation hypothesis `hsep`; given it, irreducibility is immediate — this is the honest
    shape MATH flagged.) -/
theorem operator_irreducible {α : Type*} (E : InternalExpansion α) (req : α → α)
    (hsep : ¬ E.Derivable req) : ∀ f, E.Derivable f → f ≠ req := by
  intro f hf hfe
  exact hsep (hfe ▸ hf)

/-- **Non-vacuity gate (negative control).** A fenced operator outside the expansion and an
    admissible operator inside it together witness that the internal expansion is a PROPER,
    non-vacuous sub-structure: `Derivable` is neither universally true (it excludes `req`) nor
    universally false (it includes `adm`). Guards against the `Fences := complement-of-closure`
    vacuity trap. -/
theorem nonvacuity_gate {α : Type*} (E : InternalExpansion α) (req adm : α → α)
    (hfenced : ¬ E.Derivable req) (hadm : E.Derivable adm) :
    (∃ f, ¬ E.Derivable f) ∧ (∃ f, E.Derivable f) :=
  ⟨⟨req, hfenced⟩, ⟨adm, hadm⟩⟩

/-- **B.T1 (fence-blindness), abstract.** A named fence inventory disciplined to lie within the
    base algebra's silent zone is silent: no fenced claim carries any base attestation. The
    discipline hypothesis (`Fences` characterized independently AND landing in the `none`-zone)
    carries the weight — B.T1 is near-definitional, as MATH flagged. -/
theorem fence_blind {Claim Attestation : Type*} (Algebra : Claim → Option Attestation)
    (Fences : Set Claim) (hdisc : ∀ c ∈ Fences, Algebra c = none) :
    ∀ c ∈ Fences, ∀ a, Algebra c ≠ some a := by
  intro c hc a
  rw [hdisc c hc]
  simp

/-! ### Exemplar — `human_cognition`, `O_S = {transcend}` (additive successor +1 mod 9) -/

namespace HumanCognition

open EnneagramHexadDerivability

/-- `transcend` commutes with its own iterate (it generates an abelian/cyclic action). -/
theorem transcend_iterate_comm (a : ℕ) (l : Layer) :
    transcend (transcend_n a l) = transcend_n a (transcend l) := by
  induction a generalizing l with
  | zero => rfl
  | succ a ih => simp only [transcend_n]; rw [ih]

/-- Iterates of the additive primitive compose additively: `transcend^(a+b) = transcend^a ∘ transcend^b`.
    This is what makes the iterate set a composition-closed monoid (the clone of `{transcend}`). -/
theorem transcend_n_add (a b : ℕ) (l : Layer) :
    transcend_n (a + b) l = transcend_n a (transcend_n b l) := by
  induction b generalizing l with
  | zero => rfl
  | succ b ih =>
    show transcend (transcend_n (a + b) l) = transcend_n a (transcend (transcend_n b l))
    rw [ih, transcend_iterate_comm]

/-- The internal expansion of `human_cognition`: a function is internally derivable iff it is an
    iterate of the single additive primitive `transcend`. This set IS the composition closure
    `⟨{transcend}⟩` — the clone of the lone declared primitive. -/
def Derivable (f : Layer → Layer) : Prop := ∃ k : ℕ, ∀ l, f l = transcend_n k l

theorem derivable_id : Derivable id := ⟨0, fun _ => rfl⟩

theorem derivable_transcend : Derivable transcend := ⟨1, fun _ => rfl⟩

theorem derivable_comp (f g : Layer → Layer) (hf : Derivable f) (hg : Derivable g) :
    Derivable (f ∘ g) := by
  obtain ⟨kf, hkf⟩ := hf
  obtain ⟨kg, hkg⟩ := hg
  refine ⟨kf + kg, fun l => ?_⟩
  simp only [Function.comp_apply, hkf, hkg]
  exact (transcend_n_add kf kg l).symm

/-- The `human_cognition` internal expansion as a genuine `InternalExpansion` (id + comp closed):
    the additive successor clone is a real sub-structure of `(Layer → Layer, ∘, id)`. -/
def humanExpansion : InternalExpansion Layer where
  Derivable := Derivable
  id_mem := derivable_id
  comp_mem := derivable_comp

/-- **B.T2 exemplar separation.** The fenced hexad flow (`×2`, the multiplicative automorphism
    generating `(ℤ/9ℤ)*`) is NOT internally derivable from the additive primitive — a DIRECT
    corollary of `EnneagramHexadDerivability.hexad_flow_external_to_additive`. This is the substantive
    half of B.T2, and it was already closed: the bridge is one `rintro`. -/
theorem hexad_not_derivable : ¬ Derivable hexad_flow := by
  rintro ⟨k, hk⟩
  obtain ⟨l, hl⟩ := hexad_flow_external_to_additive k
  exact hl (hk l).symm

/-- **B.T2 exemplar (operator irreducibility).** No internally-derivable operator attests the
    fenced hexad claim — the fenced-zone attestor is irreducibly external to `human_cognition`.
    "Human-at-the-loop is required, not merely useful," formalized for the exemplar. -/
theorem human_operator_irreducible : ∀ f, Derivable f → f ≠ hexad_flow :=
  operator_irreducible humanExpansion hexad_flow hexad_not_derivable

/-- **Non-vacuity discharged (negative control).** The additive successor `transcend` is
    admissible (inside the expansion); the fenced hexad flow is external (outside). The
    expansion is a proper, non-vacuous sub-structure — the gate is satisfied. -/
theorem human_nonvacuous : (∃ f, ¬ Derivable f) ∧ (∃ f, Derivable f) :=
  nonvacuity_gate humanExpansion hexad_flow transcend hexad_not_derivable derivable_transcend

end HumanCognition

/-! ### Second exemplar — `llm_cognition`

  A second instantiation over the same 9-element layered cycle (`Layer`) and additive successor
  `transcend` (+1 mod 9) as the `human_cognition` exemplar.
  Declared operator set: every layer-projection primitive is **unary** (an endomap of a
  single system `M`'s carriers); `compose` is binary but type-restricted to `M`-endo × `M`-endo,
  so `⟨O_S⟩` is the wholly-internal additive clone `⟨transcend⟩`. The fenced operator is
  `w_cross` (a cross-system audit witness). Admitting a binary cross-system primitive would
  pull `w_cross` inside and collapse the fence — the exact twin of "binary `+` puts `×2` inside."

  Two readings close it; this file proves BOTH, at honestly different strengths:
  - **(a) `w_cross_not_internally_realizable`** — assumption-free: a verdict that genuinely depends
    on an external substrate's data cannot be realized by any function of `M` alone (hence by no
    composite of unary `M`-endomaps). Independent of any scope-axis modelling.
  - **(b) `wCrossScope` / `llm_operator_irreducible`** — the finite-group mirror: `w_cross`
    RESTRICTED to the 9-layer scope axis is *modelled* as the `×2` automorphism (a declared
    MODELLING CHOICE — **not** proved here), under which it is outside the additive
    clone verbatim by `hexad_flow_external_to_additive`, giving proof-shape parity with the human twin.
-/

namespace LlmCognition

open EnneagramHexadDerivability

/-- The `llm_cognition` internal expansion: the additive clone `⟨transcend⟩`, identical in shape to
    the human exemplar (the two substrates share `Layer` + `transcend`). -/
def Derivable (f : Layer → Layer) : Prop := ∃ k : ℕ, ∀ l, f l = transcend_n k l

theorem derivable_id : Derivable id := ⟨0, fun _ => rfl⟩

theorem derivable_transcend : Derivable transcend := ⟨1, fun _ => rfl⟩

theorem derivable_comp (f g : Layer → Layer) (hf : Derivable f) (hg : Derivable g) :
    Derivable (f ∘ g) := by
  obtain ⟨kf, hkf⟩ := hf
  obtain ⟨kg, hkg⟩ := hg
  refine ⟨kf + kg, fun l => ?_⟩
  simp only [Function.comp_apply, hkf, hkg]
  exact (HumanCognition.transcend_n_add kf kg l).symm

/-- The `llm_cognition` internal expansion as a genuine `InternalExpansion` (id + comp closed). -/
def llmExpansion : InternalExpansion Layer where
  Derivable := Derivable
  id_mem := derivable_id
  comp_mem := derivable_comp

/-! #### Reading (a) — assumption-free backstop (cross-substrate dependency) -/

/-- **Reading (a).** A cross-substrate witness whose verdict genuinely depends on an EXTERNAL
    substrate's data (`hdep`: two external inputs agreeing nowhere on `M` yet judged differently)
    cannot be realized by ANY function `g` of `M`'s own carrier alone — hence by no composite of
    unary `M`-endomaps. This holds independently of the scope-axis `×2` modelling, and is the
    categorical (size-unconditional) gate, parity with the negative result in `EnneagramHexadDerivability.lean`. -/
theorem w_cross_not_internally_realizable
    {CM CMext : Type*} (w_cross : CM → CMext → Bool)
    (hdep : ∃ x : CM, ∃ m1 m2 : CMext, w_cross x m1 ≠ w_cross x m2) :
    ¬ ∃ g : CM → Bool, ∀ x mext, g x = w_cross x mext := by
  rintro ⟨g, hg⟩
  obtain ⟨x, m1, m2, hne⟩ := hdep
  exact hne ((hg x m1).symm.trans (hg x m2))

/-! #### Reading (b) — finite-group mirror -/

/-- The scope-axis MODEL of `w_cross`: its restriction to the 9-layer scope axis, *modelled* as the
    `×2` multiplicative automorphism `hexad_flow`. The identification `w_cross|_scope = ×2` is a
    declared MODELLING CHOICE, recorded here as a definition — it is not derived. -/
def wCrossScope : Layer → Layer := hexad_flow

/-- Under reading (b), the scope-axis model of `w_cross` is not internally derivable — verbatim from
    the ENNEAGRAM negative (`×2 ≠ transcend^k` for all `k`). -/
theorem wCrossScope_not_derivable : ¬ Derivable wCrossScope := by
  rintro ⟨k, hk⟩
  obtain ⟨l, hl⟩ := hexad_flow_external_to_additive k
  exact hl (hk l).symm

/-- **B.T2 for the llm_cognition exemplar (reading b).** No internally-derivable operator equals the
    scope-axis model of `w_cross` — instantiates the abstract `operator_irreducible` on the concrete
    `llmExpansion`, mirroring `HumanCognition.human_operator_irreducible`. -/
theorem llm_operator_irreducible : ∀ f, Derivable f → f ≠ wCrossScope :=
  operator_irreducible llmExpansion wCrossScope wCrossScope_not_derivable

/-- Non-vacuity gate discharged for the llm_cognition exemplar: `transcend` admissible (inside),
    `wCrossScope` fenced (outside). -/
theorem llm_nonvacuous : (∃ f, ¬ Derivable f) ∧ (∃ f, Derivable f) :=
  nonvacuity_gate llmExpansion wCrossScope transcend wCrossScope_not_derivable derivable_transcend

end LlmCognition

end SubstrateFenceIrreducibility
