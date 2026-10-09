import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBudgetInduction

/-! # 同一实际成员坍缩图的相对 Class 身份

I 和 T 的真实 Class 见证给出一个包含源母层及 T 的实际共同层。预算图
由原 Z₂ 的内部序数构造取得，局部域和图的界由原公式集合归纳证明。
在覆盖 I 的源层读回同一个原全图 H，得到 ClassH，而不预供局部解覆盖。
正式出口为原 SecondOrderArithmetic.theory_m 的图翻译 Derives；本文件
不声称已经完成 Collection、逐候选完整源模型或最终固定高度 BMS 闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseClass

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 共同预算及全部局部解的成员界在证明内构造，不保留 hWitness 或 ClassH 守卫。 -/
theorem class_l (K : source_coding_l hℳ) {B I T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hT : PowerlessRelativeClassCorrespondence.member_l hℳ B T)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  obtain ⟨a, U, hU, hIU⟩ := hI
  let B₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let T₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨T, hT⟩
  let U₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨U, PowerlessRelativeLevelClosure.class_l hℳ hBase hU⟩
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set] :=
    Env.empty |>.pushFree T₀ |>.pushFree U₀
  obtain ⟨Ω, W, _hLimit, hW, _hBW, hParams⟩ :=
    PowerlessRelativeClassLimitParameterBounds.exists_l η B₀
  have hTW : mem_l hℳ T W := hParams .set (.there .here)
  have hUW : mem_l hℳ U W := hParams .set .here
  have hDomain : PowerlessRelativeMembershipCollapseRestriction.domain_l I U I := by
    intro x
    exact ⟨fun hx => ⟨hx, PowerlessRelativeLevelClosure.transitive_l hℳ hBase hU I hIU x hx⟩,
      fun h => h.1⟩
  have hPartial : PowerlessRelativeMembershipCollapsePartial.partial_l I I T H := by
    refine ⟨fun _ hx => hx, fun _ _ _ hy _ => hy, hH.2.1, ?_⟩
    exact fun x hx y _hy hxy z _hz => hH.2.2.2.1 x y hx hxy z
  obtain ⟨A, f, r, hA, haA, hHist, hfa⟩ := hU
  have hU : PowerlessRelativeHierarchySemantics.level_l hℳ B a U :=
    ⟨A, f, r, hA, haA, hHist, hfa⟩
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨I, ⟨a, U, hU, hIU⟩⟩
  obtain ⟨Q, hBudget⟩ := PowerlessHierarchyLightHistoryBudgetExists.exists_l hℳ K hBase I₀ hW hA
  obtain ⟨δ, hQ⟩ := hBudget.total a haA
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
    (hBudget.output_ordinal a δ hQ)
  have hBound := PowerlessRelativeMembershipCollapseBudgetInduction.bounded_l K
    hBase hBI hW hTW hH hBudget a δ C U I H hQ hC hU hUW hDomain hPartial
  exact ⟨δ, C, hC, hBound.2⟩

def schema_m {Δ : SortContext ℒ} (B I T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (ThirdOrderTheory.subset_m B I) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B T) <|
          .imp (PowerlessRelativeMembershipCollapse.spec_m I T H)
            (PowerlessRelativeHierarchySyntax.class_m B H)

def sentence_m {Δ : SortContext ℒ} (B I T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B I T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (B I T H : Term ℒ [] Δ .set) : (sentence_m B I T H).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeMembershipCollapse.spec_formula_l]
  exact fun hBase hBI hI hT hH => class_l K hBase hBI hI hT hH

theorem derives_m {Δ : SortContext ℒ} (B I T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B I T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B I T H)

#print axioms class_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseClass
