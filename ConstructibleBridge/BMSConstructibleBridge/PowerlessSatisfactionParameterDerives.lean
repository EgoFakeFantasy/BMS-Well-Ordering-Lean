import BMSConstructibleBridge.PowerlessSatisfactionParameterSchema
import BMSConstructibleBridge.PowerlessSatisfactionCompilation

/-! # 公共 Sat 参数读数模式的原 Z₂ 推导

逐项保留共同静态规格、合法编译输出和同一张 R 的全参数读数。数学见证
直接复用同编码编译定理，再将实际对象模式接入原推导核；不是最终 BMS 句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionParameterDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessSatisfactionParameterSchema

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    statement_l (𝒩 := structure_l hℳ B hBase) φ ω :=
  PowerlessSatisfactionCompilation.parameters_l φ hω

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ [] Θ .set) :
    (sentence_m φ ω).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ
  simp only [schema_m, Formula.satisfies, omega_formula_l, existence_formula_l]
  exact fun hω => exists_l φ hω

theorem derives_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m (sentence_m φ ω))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase => models_l hℳ B hBase φ ω)

#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionParameterDerives
