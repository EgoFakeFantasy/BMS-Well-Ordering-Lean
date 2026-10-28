import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLimitStep
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 实际集合函数图的纯 Δ₀ 程序算子

最小见证等函数图先由原对象模式构造，再将实际图 J 作为参数读取。
不能因此称原规范选择公式本身为 Δ₀；图存在性和有限公式族的组合仍须证明。
干净映射给全部原对象上的单值性。J∈W 与实际层传递性可给输出留层；
更弱的输出母域 D⊆W 已经足够，不要求最小见证图 J 属于原见证层。
不需要在 Type 中抽取选择函数，也不要求非法输入有图读数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramGraphOperator

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

def relation_m {Δ : SortContext ℒ} (J : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessValueBounded.formula_m (free₂ J) (.fvar (.there .here)) (.fvar .here)

theorem delta_l {Δ : SortContext ℒ} (J : Term ℒ [] Δ .set) :
    Formula.IsDelta0 membershipLevyBound (relation_m J) :=
  PowerlessValueBounded.delta_l _ _ _

theorem relation_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (J : Term ℒ [] Δ .set) (η : Env 𝒱 [] Δ) (x y : carrier_l 𝒱) :
    (relation_m J).satisfies ((η.pushFree x).pushFree y) ↔ value_l (J.eval η) x y := by
  simp only [relation_m, PowerlessValueBounded.formula_l, free₂, Term.eval_weakenFree,
    Term.eval, Env.pushFree_here, Env.pushFree_there]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem functional_l {Δ : SortContext ℒ} (J : Term ℒ [] Δ .set) (η : Env 𝒱 [] Δ)
    {A D B : type_l hℳ} (hJ : map_l (ℳ := 𝒱) (J.eval η) A D) :
    PowerlessRelativeFiniteProgramInstruction.functional_l (relation_m J) η B := by
  intro x y z _ _ _ hy hz
  exact SecondOrderFunctionProperties.value_unique_l hℳ hJ
    ((relation_formula_l J η x y).mp hy) ((relation_formula_l J η x z).mp hz)

theorem closed_l {Δ : SortContext ℒ} (J : Term ℒ [] Δ .set) (η : Env 𝒱 [] Δ)
    {B W : type_l hℳ}
    (hW : ∀ x, mem_l hℳ x W → ∀ y, mem_l hℳ y x → mem_l hℳ y W)
    (hJ : mem_l hℳ (J.eval η) W) :
    PowerlessRelativeFiniteProgramLimitStep.closed_l (relation_m J) η B W := by
  intro x y _ _ hy
  exact PowerlessRelativeFiniteProgramLimitStep.reading_l hW hJ
    ((relation_formula_l J η x y).mp hy)

/-- 以图的实际输出母域保层；图本身可以位于严格更高的层。 -/
theorem range_closed_l {Δ : SortContext ℒ} (J : Term ℒ [] Δ .set) (η : Env 𝒱 [] Δ)
    {A D B W : type_l hℳ} (hJ : map_l (ℳ := 𝒱) (J.eval η) A D)
    (hD : ∀ y, mem_l hℳ y D → mem_l hℳ y W) :
    PowerlessRelativeFiniteProgramLimitStep.closed_l (relation_m J) η B W := by
  intro x y _ _ hy
  exact hD y (SecondOrderFunctionProperties.value_mem_l hℳ hJ
    ((relation_formula_l J η x y).mp hy)).2

def range_schema_m {Δ : SortContext ℒ} (B W J A D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderObjectSyntax.map_m J A D) <|
    .imp (ThirdOrderTheory.subset_m D W) <|
      .conj (PowerlessRelativeFiniteProgramInstruction.functional_m (relation_m J) B)
        (PowerlessRelativeFiniteProgramLimitStep.closed_m (relation_m J) B W)

def range_sentence_m {Δ : SortContext ℒ} (B W J A D : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (range_schema_m B W J A D)

theorem range_models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B W J A D : Term ℒ [] Δ .set) :
    (range_sentence_m B W J A D).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [range_schema_m, Formula.satisfies, map_formula_l,
    subset_formula_l,
    PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, parameters_empty_l]
  intro η hJ hD
  exact ⟨functional_l J η hJ, range_closed_l J η hJ hD⟩

theorem range_derives_m {Δ : SortContext ℒ} (B W J A D : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (range_sentence_m B W J A D)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => range_models_l h𝒩 B W J A D)

def schema_m {Δ : SortContext ℒ} (B β W J A D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
      .imp (SecondOrderObjectSyntax.member_m J W) <|
        .imp (SecondOrderObjectSyntax.map_m J A D) <|
          .conj (PowerlessRelativeFiniteProgramInstruction.functional_m (relation_m J) B)
            (PowerlessRelativeFiniteProgramLimitStep.closed_m (relation_m J) B W)

def sentence_m {Δ : SortContext ℒ} (B β W J A D : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β W J A D)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β W J A D : Term ℒ [] Δ .set) :
    (sentence_m B β W J A D).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.level_formula_l K, SecondOrderObjectSyntax.member_m,
    Arguments.eval, map_formula_l, PowerlessRelativeFiniteProgramInstruction.functional_formula_l K,
    PowerlessRelativeFiniteProgramLimitStep.closed_formula_l K, parameters_empty_l]
  intro η hB hW hJ hMap
  exact ⟨functional_l J η hMap,
    closed_l J η (PowerlessRelativeLevelClosure.transitive_l h𝒩 hB hW) hJ⟩

theorem derives_m {Δ : SortContext ℒ} (B β W J A D : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B β W J A D)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B β W J A D)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramGraphOperator
