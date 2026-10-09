import BMSConstructibleBridge.PowerlessRelativeMemberCodedCoverage
import BMSConstructibleBridge.PowerlessRelativeParameters

/-! # 完整局部覆盖矩阵在原 Z₂ 核中的首 Ω 守卫推导

相对化域 W 只出现在外层来源句中；被共同族捕获的原矩阵只有
B、ω、x 三个自由参数。十七个见证的全部图规格、数字资格和
有限赋值覆盖由实际 MemberW 构造证明，再用原图解释接入 Derives。
这里不假定 MemberW 满足完整 PowerlessTheory，也不宣称已在 I
中捕获或完成无首 Ω 分支；最终 hSources 仍待消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedCoverageDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m)
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set]

/-- 捕获正文不带 W／Ω；三槽依次为 B、ω、x。 -/
def body_m : Formula ℒ [] parameters_m :=
  PowerlessCodedHistoryCoverageSyntax.result_m
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

private def assignment_m {Γ Δ : SortContext ℒ} (B ω x : Term ℒ Γ Δ .set) :
    Variable parameters_m SetTheory.SetSort.set → Term ℒ Γ Δ .set
  | .here => B
  | .there .here => ω
  | .there (.there .here) => x

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 域是环境外部参数，不要求 W∈W。 -/
def relative_m {Γ Δ : SortContext ℒ} (W B ω x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativeParameters.instance_m body_m W (assignment_m B ω x)

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  let W := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
  .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
  .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
  .imp (member_m B W) <| .forallE .set <| .imp (member_m (.bvar .here) (up W))
    (relative_m (up W) (up B) (up ω) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω hΩ hW hBW x hx
  let B := η.freeVal .here
  let ω := η.freeVal (.there .here)
  let Ω := η.freeVal (.there (.there .here))
  let W := η.freeVal (.there (.there (.there .here)))
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η
    (.fvar .here)).mp hBase
  have hω' := (SecondOrderOmegaSyntax.omega_l hℳ η (.fvar (.there .here))).mp hω
  have hΩ' := (PowerlessRelativeOrdinalCutoff.first_formula_l K η
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hΩ
  have hW' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar .here) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))).mp hW
  change mem_l hℳ B W at hBW
  change mem_l hℳ x W at hx
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase' Ω W hW' ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase') K hω' hΩ')
  let B₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨B, hBW⟩
  let ω₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨ω, hωW⟩
  let x₀ : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W := ⟨x, hx⟩
  let ξ : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨B, hBW⟩) [] parameters_m :=
    Env.empty |>.pushFree x₀ |>.pushFree ω₀ |>.pushFree B₀
  have hTrans : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W :=
    fun z t hz ht => PowerlessRelativeLevelClosure.transitive_l hℳ hBase' hW' z hz t ht
  have hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (PowerlessMemberStructure.structure_l
        (ℳ := SecondOrderQuotient.structure_l hℳ) W ⟨B, hBW⟩)) := by
    refine ⟨?_⟩
    intro a b h
    apply Subtype.ext
    apply SecondOrderQuotient.ext_l hℳ
    intro z
    constructor
    · intro hz
      exact (h ⟨z, hTrans a.val z a.property hz⟩).mp hz
    · intro hz
      exact (h ⟨z, hTrans b.val z b.property hz⟩).mpr hz
  have hStatement := PowerlessRelativeMemberCodedCoverage.exists_l
    (hW₀ := ⟨B, hBW⟩) K B₀ ω₀ x₀ hBase' hω' hΩ' hW'
  have hTruth : body_m.satisfies ξ :=
    (PowerlessCodedHistoryCoverageSyntax.result_formula_l hExt ξ
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mpr hStatement
  have hRelative := PowerlessRelativeParameters.instance_l body_m (η.pushBound x)
    (up (.fvar (.there (.there (.there .here)))))
    (assignment_m (up (.fvar .here)) (up (.fvar (.there .here))) (.bvar .here)) ξ rfl
      (fun v => by
        cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => nomatch v)
  exact hRelative.mpr hTruth

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCodedCoverageDerives
