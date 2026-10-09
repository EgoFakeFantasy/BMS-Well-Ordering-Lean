import BMSConstructibleBridge.PowerlessMemberOmegaExtensional
import BMSConstructibleBridge.PowerlessRelativeParameters
import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives
import BMSConstructibleBridge.SecondOrderOmegaSyntax

/-! # 不假定完整源模型的成员域 ω 识别

原 Z₂ 图商本身的外延性已足够。传递域含实际 ω 时，原 ω 公式在
实际成员结构中精确识别同一对象；不要求源 Separation / Collection。
相对公式守卫和任意域内候选均进入原 Z₂ 的正式对象闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberOmegaAbsolute

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem omega_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C ω : SecondOrderQuotient.type_l hℳ} {hC : ∃ c, mem_l hℳ c C}
    (hCT : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) C)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hωC : mem_l hℳ ω C)
    (a : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) C) :
    ThirdOrderSemantics.omega_l
      (ℳ := PowerlessMemberStructure.structure_l (ℳ := SecondOrderQuotient.structure_l hℳ) C hC) a ↔
        a.val = ω := by
  have hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (SecondOrderQuotient.structure_l hℳ)) := ⟨fun x y h => SecondOrderQuotient.ext_l hℳ x y h⟩
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set] := Env.empty.pushFree ω
  have hωPure := (ThirdOrderSemantics.omega_formula_l η (.fvar .here)).mp
    ((SecondOrderOmegaSyntax.omega_l hℳ η (.fvar .here)).mpr hω)
  exact PowerlessMemberOmegaExtensional.omega_l hExt hCT hωPure hωC a

private def assignment_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Variable [.set] SetTheory.SetSort.set → Term ℒ Γ Δ .set
  | .here => a

def relative_m {Γ Δ : SortContext ℒ} (C a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  PowerlessRelativeParameters.instance_m (SecondOrderOmegaSyntax.omega_m (.fvar .here)) C (assignment_m a)

def schema_m : Formula ℒ [] [.set, .set] :=
  let C : Term ℒ [] [.set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.member_m ω C) <|
      .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (C.weakenBound SetTheory.SetSort.set))
        (.iff (relative_m (C.weakenBound SetTheory.SetSort.set) (.bvar .here))
          (.equal (.bvar .here) (ω.weakenBound SetTheory.SetSort.set)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hCT hω hωC a ha
  have hTrans := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hCT
  have hCT' : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (η.freeVal .here) :=
    fun x y hx hy => hTrans x hx y hy
  have hω' := (SecondOrderOmegaSyntax.omega_l hℳ η (.fvar (.there .here))).mp hω
  let hC : ∃ c, mem_l hℳ c (η.freeVal .here) := ⟨η.freeVal (.there .here), hωC⟩
  let x : PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) (η.freeVal .here) := ⟨a, ha⟩
  let ξ : Env (PowerlessMemberStructure.structure_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) (η.freeVal .here) hC) [] [.set] :=
    Env.empty.pushFree x
  have hR := PowerlessRelativeParameters.instance_l (SecondOrderOmegaSyntax.omega_m (.fvar .here))
    (η.pushBound a) (.fvar .here) (assignment_m (.bvar .here)) ξ rfl (fun v => by
      cases v with
      | here => rfl
      | there v => nomatch v)
  have hOmega := (ThirdOrderSemantics.omega_formula_l ξ (.fvar .here)).trans
    (omega_l hℳ hCT' hω' hωC x)
  exact hR.trans hOmega

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms omega_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberOmegaAbsolute
