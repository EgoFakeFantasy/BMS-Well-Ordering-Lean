import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetExists
import BMSConstructibleBridge.PowerlessHierarchyLightHistoryCodomain
import BMSConstructibleBridge.PowerlessRelativeCutoffDefFunction

/-! # 截断分支的实际 Class 长历史及原 Z₂ 对象出口

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。
统一原 Def 图由截断分支实际构造，预算图及层包也在证明内构造；
最终存在句只保留原四项截断守卫，不增加预算、前缀覆盖或 Collection。

原历史的域仍为 α；预算域取 α 的实际后继，使终点 α 也有预算。
同一 raw 历史图的 Class 身份来自原内部预算归纳，不抽取 Type 选择。
特别在 α=Ω 得到实际 Class 前史 Ω→W；这不是前史属于 W，也不是
统一枚举族、完整截断源公理或最终固定高度 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffClassHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct RawModel)

/-- 严格初段内的实际原历史进入 Class；预算证书不是公共前提。 -/
theorem class_exists_l (K : source_coding_l hℳ) {B α Ω W : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (D : type_l hℳ B)
    (hRead : ∀ X Y : SecondOrderQuotient.type_l hℳ, value_l (ℳ := RawModel) D.val X Y ↔
      mem_l hℳ X W ∧ SecondOrderMemberDef.spec_l hℳ X Y)
    (hα : Ordinal α) (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBelow : ∀ a, mem_l hℳ a α → mem_l hℳ a Ω) :
    ∃ f : type_l hℳ B, PowerlessRelativeHierarchySemantics.history_l hℳ B α f.val W := by
  obtain ⟨A, hA⟩ := SecondOrderQuotient.surj_l hℳ α
  obtain ⟨U, hU, hαU, _hSucc⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ A (hA ▸ hα)
  have hαU' : mem_l hℳ α (mk_l hℳ U) := by
    change mem_l hℳ (mk_l hℳ A) (mk_l hℳ U) at hαU
    exact hA ▸ hαU
  obtain ⟨Q, hBudget⟩ := PowerlessHierarchyLightHistoryBudgetExists.exists_l hℳ K hBase D hW hU
  obtain ⟨f, hf⟩ := PowerlessHierarchyLightHistoryCodomain.exists_l hℳ hBase hRead hα hW hBelow
  obtain ⟨δ, hQ⟩ := hBudget.total α hαU'
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
    (hBudget.output_ordinal α δ hQ)
  have hClass := PowerlessHierarchyLightHistoryBudgetInduction.class_l hℳ K hBase hRead
    hBudget hQ hC hf
  exact ⟨⟨f, hClass⟩, PowerlessHierarchyLightHistoryUnique.to_original_l hℳ hRead hf⟩

/-- 首不可数截断的统一原 Def 图和实际预算全部在证明内取得。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω W : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) :
    ∃ f : type_l hℳ B, PowerlessRelativeHierarchySemantics.history_l hℳ B Ω f.val W := by
  obtain ⟨D, _hMap, hRead⟩ := PowerlessRelativeCutoffDefFunction.exists_l K hBase hω hΩ hW
  exact class_exists_l hℳ K hBase D hRead (PowerlessRelativeLevelClosure.ordinal_l hℳ hW)
    hW (fun _ hx => hx)

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let W : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let B := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
            (PowerlessRelativeHierarchySyntax.history_m (up B) (up Ω) (.bvar .here) (up W))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hΩ hW
  obtain ⟨f, hf⟩ := exists_l h𝒩 K hBase hω hΩ hW
  exact ⟨f.val, f.property, hf⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffClassHistory
