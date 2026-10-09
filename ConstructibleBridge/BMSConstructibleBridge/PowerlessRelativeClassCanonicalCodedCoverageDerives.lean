import BMSConstructibleBridge.PowerlessRelativeClassCanonicalCodedCoverage
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances
import BMSConstructibleBridge.SecondOrderCanonicalLevelDerives

/-! # 原 Z₂ 中实际 Class 规范覆盖的存在推导

原纯隶属二十见证矩阵相对化到真实 Class。背景只有原 Z₂，
出口使用原 GraphTranslation 与 Derives；种子良序及实际参数资格
守卫保留，不预供前史、比较图、原编码包或参考历史。
这不是固定行高 BMS 的终局句，也没有取得 Class 内部可数性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalCodedCoverageDerives

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev context_m : SortContext ℒ := [.set, .set, .set, .set]
private abbrev B_m : Term ℒ [] context_m .set := .fvar .here
private abbrev ω_m : Term ℒ [] context_m .set := .fvar (.there .here)
private abbrev x_m : Term ℒ [] context_m .set := .fvar (.there (.there .here))
private abbrev P₀_m : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))

private def parameters_m (v : Variable context_m .set) : Term ℒ [] context_m .set := .fvar v

private def formula_m : Formula ℒ [] context_m :=
  PowerlessCanonicalCodedCoverageSyntax.result_m B_m ω_m x_m P₀_m

def result_m : Formula ℒ [] context_m := instance_m formula_m B_m parameters_m

def schema_m : Formula ℒ [] context_m :=
  .imp (guard_m B_m P₀_m) <| .imp (SecondOrderOmegaSyntax.omega_m ω_m) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B_m x_m) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B_m P₀_m) result_m

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, guard_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, B_m, ω_m, x_m, P₀_m, Term.eval]
  intro hGuard hω hx hP₀
  let B := η.freeVal .here
  have hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B :=
    fun z hz t ht => hGuard.2.1 z t hz ht
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (hωEq.symm ▸ SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  have hMember (v : Variable context_m .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B (η.freeVal v) := by
    cases v with
    | here => exact PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase
    | there v => cases v with
      | here => exact hωClass
      | there v => cases v with
        | here => exact hx
        | there v => cases v with
          | here => exact hP₀
          | there v => nomatch v
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] context_m :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMember v⟩ }
  apply (instance_l K formula_m η B_m parameters_m ξ rfl (fun _ => rfl)).mpr
  apply (PowerlessCanonicalCodedCoverageSyntax.result_formula_l
    (PowerlessRelativeClassStructure.ext_l hℳ B hBase) ξ B_m ω_m x_m P₀_m).mpr
  exact PowerlessRelativeClassCanonicalCodedCoverage.exists_l (hBase := hBase) K
    (ξ.freeVal (.there .here)) (ξ.freeVal (.there (.there .here)))
    (ξ.freeVal (.there (.there (.there .here)))) hω
    hGuard.1 hGuard.2.2.1 hGuard.2.2.2

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalCodedCoverageDerives
