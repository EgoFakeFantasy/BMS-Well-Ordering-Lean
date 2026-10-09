import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionSyntax

/-! # 指定层完整 Sat 存在模式的原 Z₂ 推导

层关系、先后关系及参数成员守卫在原商结构中解释，仅静态规格和 Sat
正文作类相对化。公开对象前提不包含编码 K、原算术 V 或未证递归方程。
本模式保留先前非零极限层和序列集成员条件，不宣称最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitSatisfactionSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    (sentence_m ω e N T A S t₁ t₂ t₃).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ hBase hD hInner hC hOuter hEarlier hParams hω hS
  let B := base_m.eval ρ
  let γ := innerStage_m.eval ρ
  let D := inner_m.eval ρ
  let β := outerStage_m.eval ρ
  let C := outer_m.eval ρ
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ρ base_m).mp hBase
  have hD' := (PowerlessRelativeHierarchySemantics.level_formula_l K ρ base_m innerStage_m inner_m).mp hD
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K ρ base_m outerStage_m outer_m).mp hC
  have hInner' := (PowerlessRelativeHierarchySemantics.limit_formula_l ρ innerStage_m).mp hInner
  have hOuter' := (PowerlessRelativeHierarchySemantics.limit_formula_l ρ outerStage_m).mp hOuter
  have hEarlier' : mem_l hℳ γ β := hEarlier
  have hParams' := (PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l Δ ρ inner_m tail_m).mp hParams
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase') [] Δ :=
    ⟨(fun v => nomatch v), fun {s} v => match s with
      | .set => ⟨(tail_m v).eval ρ, ⟨γ, D, hD', hParams' _ v⟩⟩⟩
  have hη : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val D := by
    intro s v
    cases s
    exact hParams' _ v
  have hω' := (PowerlessRelativeClassInstantiation.formula_l K (SecondOrderOmegaSyntax.omega_m ω)
    η ρ base_m tail_m rfl (fun _ => rfl)).mp hω
  have hωClass := (omega_formula_l η ω).mp hω'
  have hS' := (PowerlessRelativeClassInstantiation.formula_l K (PowerlessFiniteSequencesSyntax.spec_m ω A S)
    η ρ base_m tail_m rfl (fun _ => rfl)).mp hS
  have hSClass := (PowerlessFiniteSequencesSyntax.spec_formula_l η ω A S).mp hS'
  intro F hFC hStatic
  let F' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨F, ⟨β, C, hC', hFC⟩⟩
  have hStatic' := (PowerlessRelativeClassInstantiation.formula_l K
    (sourceStatic_m ω e N T t₁ t₂ t₃) (η.pushFree F') (ρ.pushBound F) base_m one_m rfl
    (by intro v; cases v <;> rfl)).mp hStatic
  have hStaticClass := (sourceStatic_formula_l η ω e N T t₁ t₂ t₃ F').mp hStatic'
  obtain ⟨R, hRC, hSat⟩ := PowerlessRelativeLimitSatisfactionStatic.exists_l (F := F')
    hD' hInner' hC' hOuter' hEarlier' η ω e N T A S t₁ t₂ t₃ hη hωClass hSClass hFC hStaticClass
  refine ⟨R.val, hRC, ?_⟩
  apply (PowerlessRelativeClassInstantiation.formula_l K (sourceSat_m ω e T A t₁ t₂ t₃)
    ((η.pushFree F').pushFree R) ((ρ.pushBound F).pushBound R.val) base_m two_m rfl ?_).mpr
  · exact (sourceSat_formula_l η ω e T A t₁ t₂ t₃ F' R).mpr hSat
  · intro v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem derives_m {Δ : SortContext ℒ} (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m ω e N T A S t₁ t₂ t₃)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω e N T A S t₁ t₂ t₃)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfactionDerives
