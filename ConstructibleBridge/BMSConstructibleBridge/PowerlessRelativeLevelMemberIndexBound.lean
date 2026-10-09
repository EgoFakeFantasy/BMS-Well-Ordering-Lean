import BMSConstructibleBridge.PowerlessRelativeLevelClosure
import BMSConstructibleBridge.SecondOrderOrdinalComparison
import BMSConstructibleBridge.SecondOrderFoundation

/-! # 实际层对象成员关系的严格阶段界

纯隶属语言下，从同一传递基集的 Lα[B]∈Lβ[B] 推出 α∈β。
仅使用原层唯一性、单调性、内部序数三歧性及正则公理；不要求首 Ω、
可数性、坍缩图类资格或 Collection。闭句回接原 Z₂ 图翻译推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelMemberIndexBound

open Logic FirstOrder
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 层对象的隶属严格反映阶段大小，不能用基集的序数成员替代阶段。 -/
theorem below_l {B α β C D : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : level_l hℳ B α C) (hD : level_l hℳ B β D)
    (hCD : mem_l hℳ C D) : mem_l hℳ α β := by
  have hCC : ¬mem_l hℳ C C := by
    obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ C
    exact SecondOrderFoundation.irrefl_l hℳ A
  rcases SecondOrderOrdinalComparison.compare_l hℳ
      (PowerlessRelativeLevelClosure.ordinal_l hℳ hC)
      (PowerlessRelativeLevelClosure.ordinal_l hℳ hD) with h | h | h
  · subst β
    have hEq := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hC hD
    rw [← hEq] at hCD
    exact False.elim (hCC hCD)
  · exact h
  · exact False.elim (hCC (PowerlessRelativeLevelClosure.subset_l hℳ hB h hD hC C hCD))

def schema_m {Δ : SortContext ℒ} (B α β C D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B α C) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β D) <|
        .imp (SecondOrderObjectSyntax.member_m C D) (SecondOrderObjectSyntax.member_m α β)

def sentence_m {Δ : SortContext ℒ} (B α β C D : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B α β C D)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (B α β C D : Term ℒ [] Δ .set) :
    (sentence_m B α β C D).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  exact fun hB hC hD hCD => below_l hB hC hD hCD

theorem derives_m {Δ : SortContext ℒ} (B α β C D : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B α β C D)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B α β C D)

#print axioms below_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLevelMemberIndexBound
