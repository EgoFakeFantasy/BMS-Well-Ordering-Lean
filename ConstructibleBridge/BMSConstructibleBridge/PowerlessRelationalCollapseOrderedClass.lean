import BMSConstructibleBridge.PowerlessRelationalCollapseBudgetInduction
import BMSConstructibleBridge.PowerlessRelationalCollapseRange

/-! # 前驱优先良序下的实际坍缩类闭包

纯隶属 ℒ，原 Z₂。先真正构造 α 后继上的预算 Q，再由原内部
集合归纳给完整初段 I 和同一 H 一个实际层界，精确满射值域认同 T。
调用端不预供预算、局部覆盖、ClassH/ClassT 或 ClassP。
仍明确要求已有前驱优先类内良序 J 及其原坍缩 P；这些索引的无条件
构造与最终固定高度 BMS 良序句不是本模块完成的结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrderedClass

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem class_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {B A I J T H α P : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hJClass : PowerlessRelativeClassCorrespondence.member_l hℳ B J)
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hExtends : PowerlessRelationalCollapseOrderedCut.extends_l I A J)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B T := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ α
  obtain ⟨Y, hY, _hXY, hSucc⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ X
    (PowerlessRelationalCollapseOrderReading.ordinal_l hJ hP)
  have hγ : PowerlessRelativeHierarchySemantics.successor_l hℳ (mk_l hℳ X) (mk_l hℳ Y) := by
    intro z
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
    exact (hSucc Z).trans (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ Z X).symm)
  let A₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨A, hA⟩
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨I, hI⟩
  let J₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨J, hJClass⟩
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set] :=
    Env.empty |>.pushFree A₀ |>.pushFree J₀
  obtain ⟨_Ω, W, _hLimit, hW, _hIW, hParams⟩ :=
    PowerlessRelativeClassLimitParameterBounds.exists_l η I₀
  obtain ⟨Q, hBudget⟩ := PowerlessHierarchyLightHistoryBudgetExists.exists_l hℳ K hBase I₀ hW hY
  have hAll := PowerlessRelationalCollapseBudgetInduction.bounded_l K hBase
    (hParams .set (.there .here)) (hParams .set .here) hJ hP hExtends hH hγ hBudget
  have hCut : PowerlessRelationalCollapseOrdinalCut.cut_l I P (mk_l hℳ X) I := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha, _⟩ := hP.2.1.2 x hx
      exact ⟨hx, a, ha⟩
    · exact fun hx => hx.1
  have hPartial : PowerlessRelationalCollapsePartial.partial_l A I I T H := by
    refine ⟨fun _ hx => hx, fun _ _ _ hy _ => hy, hH.2.1, ?_⟩
    intro x hx y _hy hxy z _hz
    exact hH.2.2.2 x y hx hxy z
  obtain ⟨δ, hQ⟩ := hBudget.total (mk_l hℳ X) ((hγ (mk_l hℳ X)).mpr (Or.inr rfl))
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
    (hBudget.output_ordinal (mk_l hℳ X) δ hQ)
  have hHC := (hAll (mk_l hℳ X) δ C I H hQ hC hCut hPartial).2
  have hHClass : PowerlessRelativeClassCorrespondence.member_l hℳ B H := ⟨δ, C, hC, hHC⟩
  exact ⟨hHClass, PowerlessRelationalCollapseRange.range_l hBase hI hHClass hH⟩

def schema_m {Δ : SortContext ℒ} (B A I J T H α P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B J) <|
          .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
            .imp (PowerlessRelationalCollapseOrderedCut.extends_m I A J) <|
              .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
                .imp (SecondOrderCollapseSyntax.formula_m J I α P) <|
                  .conj (PowerlessRelativeHierarchySyntax.class_m B H)
                    (PowerlessRelativeHierarchySyntax.class_m B T)

def sentence_m {Δ : SortContext ℒ} (B A I J T H α P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B A I J T H α P)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B A I J T H α P : Term ℒ [] Δ .set) : (sentence_m B A I J T H α P).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelationalCollapseOrderedCut.extends_formula_l, SecondOrderCollapseSyntax.formula_l]
  exact fun hBase hA hI hJClass hJ hExtends hH hP =>
    class_l (hℳ := hℳ) K hBase hA hI hJClass hJ hExtends hH hP

theorem derives_m {Δ : SortContext ℒ} (B A I J T H α P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B A I J T H α P)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B A I J T H α P)

#print axioms class_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrderedClass
