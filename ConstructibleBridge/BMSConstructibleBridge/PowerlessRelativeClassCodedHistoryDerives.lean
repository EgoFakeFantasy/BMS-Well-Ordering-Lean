import BMSConstructibleBridge.PowerlessRelativeClassCodedHistoryReading
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances

/-! # 同一完整 Class 编码包读回原历史的 Z₂ 对象句

保留原二十槽点矩阵及其原结果 AST。Class 参数资格和实际内部 ω
显式留作守卫；类内完整包推出同一 raw 包、原 Def 图、原历史及
原层资格。正式出口为原 num/set 理论中的 Derives，不是模型语义
或 AST 的替代交付，也不宣称全局内部枚举或 BMS 终局已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedHistoryDerives

open Logic FirstOrder PowerlessBMSQuotientCoding
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev context_m : SortContext ℒ :=
  [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private abbrev B_m : Term ℒ [] context_m .set := .fvar .here
private abbrev ω_m : Term ℒ [] context_m .set := .fvar (.there (.here))
private abbrev x_m : Term ℒ [] context_m .set := .fvar (.there (.there (.here)))
private abbrev a_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.here))))
private abbrev y_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.here)))))
private abbrev A_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.here))))))
private abbrev U_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.here)))))))
private abbrev D_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.here))))))))
private abbrev f_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
private abbrev e_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
private abbrev t₁_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
private abbrev t₂_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
private abbrev t₃_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
private abbrev t₄_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))
private abbrev P_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))
private abbrev N_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))
private abbrev F_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))
private abbrev V_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))
private abbrev Q_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))
private abbrev G_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))))

private def parameters_m (v : Variable context_m .set) : Term ℒ [] context_m .set := .fvar v

private def point_m : Formula ℒ [] context_m :=
  PowerlessCodedHistoryCoverageSyntax.point_m B_m ω_m x_m a_m y_m A_m U_m D_m f_m e_m t₁_m t₂_m t₃_m t₄_m P_m N_m F_m V_m Q_m G_m

def schema_m : Formula ℒ [] context_m :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B_m) <|
    .imp (PowerlessRelativeClassFormulaInstances.members_m context_m B_m parameters_m) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω_m) <|
        .imp (instance_m point_m B_m parameters_m) <| .conj point_m
          (PowerlessRawCodedHistoryReading.result_m B_m x_m a_m y_m A_m U_m D_m f_m)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeClassFormulaInstances.members_l K, SecondOrderOmegaSyntax.omega_l]
  intro hBase hMembers hω hPoint
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B_m.eval η) hBase) [] context_m := {
    boundVal := fun v => nomatch v
    freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMembers v⟩ }
  have hν : ∀ v, (parameters_m v).eval η = (ξ.freeVal v).val := fun _ => rfl
  have hClass := (instance_l K point_m η B_m parameters_m ξ rfl hν).mp hPoint
  have hPointClass := (PowerlessCodedHistoryCoverageSyntax.point_formula_l
    (PowerlessRelativeClassStructure.ext_l hℳ (B_m.eval η) hBase) ξ
    B_m ω_m x_m a_m y_m A_m U_m D_m f_m e_m t₁_m t₂_m t₃_m t₄_m P_m N_m F_m V_m Q_m G_m).mp hClass
  have hωEq : (ω_m.eval ξ).val = K.omega := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hRaw := PowerlessRelativeClassCodedHistoryReading.point_l
    K (B_m.eval ξ) (ω_m.eval ξ) (x_m.eval ξ) (a_m.eval ξ) (y_m.eval ξ) (A_m.eval ξ) (U_m.eval ξ) (D_m.eval ξ) (f_m.eval ξ) (e_m.eval ξ) (t₁_m.eval ξ) (t₂_m.eval ξ) (t₃_m.eval ξ) (t₄_m.eval ξ) (P_m.eval ξ) (N_m.eval ξ) (F_m.eval ξ) (V_m.eval ξ) (Q_m.eval ξ) (G_m.eval ξ) hωEq hPointClass
  have hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (SecondOrderQuotient.structure_l hℳ)) := ⟨SecondOrderQuotient.ext_l hℳ⟩
  refine ⟨(PowerlessCodedHistoryCoverageSyntax.point_formula_l hExt η
    B_m ω_m x_m a_m y_m A_m U_m D_m f_m e_m t₁_m t₂_m t₃_m t₄_m P_m N_m F_m V_m Q_m G_m).mpr hRaw, ?_⟩
  simp only [PowerlessRawCodedHistoryReading.result_m, Formula.satisfies,
    PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K]
  have hLevel := PowerlessRawCodedHistoryReading.level_l K hωEq hRaw
  exact ⟨PowerlessRawCodedHistoryReading.graph_l K hωEq hRaw,
    PowerlessRawCodedHistoryReading.history_l K hωEq hRaw, hLevel.1, hLevel.2⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCodedHistoryDerives
