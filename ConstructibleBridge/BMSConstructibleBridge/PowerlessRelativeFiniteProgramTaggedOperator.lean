import BMSConstructibleBridge.PowerlessRelativeFiniteProgramGraphOperator

/-! # 有限实际函数族的纯 Δ₀ 标签算子

外部有限列表只索引实际图和标签，不模拟内部自然数归纳。输入是
Kuratowski 对 (标签,源输入)，输出读取该标签对应的实际图。图都映射
W→W，且相同标签对应相同图时，组合仍单值并保层；无需任一图属于 W。
标签一致性必须显式证明，不能用无约束关系析取代替有限见证族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramTaggedOperator

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev Entry (Δ : SortContext ℒ) := Term ℒ [] Δ .set × Term ℒ [] Δ .set

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

private def forall_m {α : Type} {Γ Δ : SortContext ℒ}
    (F : List α) (f : α → Formula ℒ Γ Δ) : Formula ℒ Γ Δ :=
  match F with
  | [] => .truth
  | p :: F => .conj (f p) (forall_m F f)

private theorem forall_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {α : Type} {Γ Δ : SortContext ℒ} (F : List α) (f : α → Formula ℒ Γ Δ)
    (η : Env 𝒱 Γ Δ) : (forall_m F f).satisfies η ↔ ∀ p ∈ F, (f p).satisfies η := by
  induction F with
  | nil => simp [forall_m, Formula.satisfies]
  | cons p F ih => simp [forall_m, Formula.satisfies, ih]

def clause_m {Δ : SortContext ℒ} (W t J : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  membershipLevyBound.boundedExists (free₂ W) <|
    .conj (PowerlessPairBounded.ordered_m (up (free₂ t)) (.bvar .here)
      (up (.fvar (.there .here))))
      (PowerlessValueBounded.formula_m (up (free₂ J)) (.bvar .here) (up (.fvar .here)))

def relation_m {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  match F with
  | [] => .falsum
  | p :: F => .disj (clause_m W p.1 p.2) (relation_m W F)

theorem delta_l {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ)) :
    Formula.IsDelta0 membershipLevyBound (relation_m W F) := by
  induction F with
  | nil => exact .falsum
  | cons p F ih =>
    exact .disj (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
      (PowerlessValueBounded.delta_l _ _ _))) ih

theorem clause_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (W t J : Term ℒ [] Δ .set) (η : Env 𝒱 [] Δ)
    (x y : carrier_l 𝒱) :
    (clause_m W t J).satisfies ((η.pushFree x).pushFree y) ↔
      ∃ a, member_l 𝒱 a (W.eval η) ∧ ordered_l (ℳ := 𝒱) (t.eval η) a x ∧
        value_l (ℳ := 𝒱) (J.eval η) a y := by
  simp only [clause_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, Arguments.eval,
    PowerlessPairBounded.ordered_formula_l, PowerlessValueBounded.formula_l,
    up, free₂, Term.eval_weakenBound, Term.eval_weakenFree, Term.eval,
    Env.pushFree_here, Env.pushFree_there]
  rfl

theorem relation_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ))
    (η : Env 𝒱 [] Δ) (x y : carrier_l 𝒱) :
    (relation_m W F).satisfies ((η.pushFree x).pushFree y) ↔
      ∃ p ∈ F, ∃ a, member_l 𝒱 a (W.eval η) ∧ ordered_l (ℳ := 𝒱) (p.1.eval η) a x ∧
        value_l (ℳ := 𝒱) (p.2.eval η) a y := by
  induction F with
  | nil => simp [relation_m, Formula.satisfies]
  | cons p F ih => simp [relation_m, Formula.satisfies, clause_formula_l, ih]

def maps_m {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ)) : Formula ℒ [] Δ :=
  forall_m F (fun p => SecondOrderObjectSyntax.map_m p.2 W W)

def coherent_m {Δ : SortContext ℒ} (F : List (Entry Δ)) : Formula ℒ [] Δ :=
  forall_m F (fun p => forall_m F (fun q => .imp (.equal p.1 q.1) (.equal p.2 q.2)))

theorem maps_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ)) (η : Env 𝒱 [] Δ) :
    (maps_m W F).satisfies η ↔ ∀ p ∈ F, map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η) := by
  simp only [maps_m, forall_formula_l, map_formula_l]

theorem coherent_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (F : List (Entry Δ)) (η : Env 𝒱 [] Δ) :
    (coherent_m F).satisfies η ↔
      ∀ p ∈ F, ∀ q ∈ F, p.1.eval η = q.1.eval η → p.2.eval η = q.2.eval η := by
  simp only [coherent_m, forall_formula_l, Formula.satisfies]

/-- 每个有效标签和源输入都确实有输出；不要求任意 raw 输入有标签。 -/
def total_m {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ)) : Formula ℒ [] Δ :=
  forall_m F (fun p => membershipLevyBound.boundedForall W <| .forallE .set <|
    .imp (PowerlessPairBounded.ordered_m (up (up p.1)) (.bvar (.there .here)) (.bvar .here)) <|
      membershipLevyBound.boundedExists (up (up W)) <|
        at_m (relation_m W F) (.bvar (.there .here)) (.bvar .here))

theorem total_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ)) (η : Env 𝒱 [] Δ) :
    (total_m W F).satisfies η ↔
      ∀ p ∈ F, ∀ a, member_l 𝒱 a (W.eval η) → ∀ x, ordered_l (ℳ := 𝒱) (p.1.eval η) a x →
        ∃ y, member_l 𝒱 y (W.eval η) ∧ (relation_m W F).satisfies ((η.pushFree x).pushFree y) := by
  simp only [total_m, forall_formula_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, Arguments.eval, PowerlessPairBounded.ordered_formula_l, at_formula_l,
    parameters_pushBound_l, parameters_empty_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem functional_l {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ))
    (η : Env 𝒱 [] Δ) (B : SecondOrderQuotient.type_l hℳ)
    (hMaps : ∀ p ∈ F, map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η))
    (hCoherent : ∀ p ∈ F, ∀ q ∈ F, p.1.eval η = q.1.eval η → p.2.eval η = q.2.eval η) :
    PowerlessRelativeFiniteProgramInstruction.functional_l (relation_m W F) η B := by
  intro x y z _ _ _ hy hz
  obtain ⟨p, hp, a, _, hpa, hpy⟩ := (relation_formula_l W F η x y).mp hy
  obtain ⟨q, hq, b, _, hqb, hqz⟩ := (relation_formula_l W F η x z).mp hz
  have hPair := (SecondOrderPairObjects.ordered_eq_l hℳ hpa hqb).mp rfl
  have hGraph := hCoherent p hp q hq hPair.1
  rw [← hGraph, ← hPair.2] at hqz
  exact SecondOrderFunctionProperties.value_unique_l hℳ (hMaps p hp) hpy hqz

theorem closed_l {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ))
    (η : Env 𝒱 [] Δ) (B : SecondOrderQuotient.type_l hℳ)
    (hMaps : ∀ p ∈ F, map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η)) :
    PowerlessRelativeFiniteProgramLimitStep.closed_l (relation_m W F) η B (W.eval η) := by
  intro x y _ _ hy
  obtain ⟨p, hp, a, _, _, hpy⟩ := (relation_formula_l W F η x y).mp hy
  exact (SecondOrderFunctionProperties.value_mem_l hℳ (hMaps p hp) hpy).2

theorem total_l {Δ : SortContext ℒ} (W : Term ℒ [] Δ .set) (F : List (Entry Δ))
    (η : Env 𝒱 [] Δ)
    (hMaps : ∀ p ∈ F, map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η)) :
    ∀ p ∈ F, ∀ a, mem_l hℳ a (W.eval η) → ∀ x, ordered_l (ℳ := 𝒱) (p.1.eval η) a x →
      ∃ y, mem_l hℳ y (W.eval η) ∧ (relation_m W F).satisfies ((η.pushFree x).pushFree y) := by
  intro p hp a ha x hx
  obtain ⟨y, hy, _⟩ := (hMaps p hp).2 a ha
  exact ⟨y, hy.1, (relation_formula_l W F η x y).mpr ⟨p, hp, a, ha, hx, hy.2⟩⟩

def schema_m {Δ : SortContext ℒ} (B W : Term ℒ [] Δ .set) (F : List (Entry Δ)) : Formula ℒ [] Δ :=
  .imp (maps_m W F) <| .imp (coherent_m F) <|
    .conj (PowerlessRelativeFiniteProgramInstruction.functional_m (relation_m W F) B)
      (.conj (PowerlessRelativeFiniteProgramLimitStep.closed_m (relation_m W F) B W) (total_m W F))

def sentence_m {Δ : SortContext ℒ} (B W : Term ℒ [] Δ .set) (F : List (Entry Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B W F)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (B W : Term ℒ [] Δ .set) (F : List (Entry Δ)) :
    (sentence_m B W F).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, maps_formula_l, coherent_formula_l, total_formula_l,
    PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, parameters_empty_l]
  intro η hMaps hCoherent
  exact ⟨functional_l W F η (B.eval η) hMaps hCoherent,
    closed_l W F η (B.eval η) hMaps, total_l W F η hMaps⟩

theorem derives_m {Δ : SortContext ℒ} (B W : Term ℒ [] Δ .set) (F : List (Entry Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B W F)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B W F)

#print axioms delta_l
#print axioms relation_formula_l
#print axioms functional_l
#print axioms closed_l
#print axioms total_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramTaggedOperator
