import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseSatisfaction
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBase
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

/-! # 完整传递域覆盖后的原公式反射

消费同一实际 I、T、H 与 D⊆I：传递 D 的全部成员被原坍缩逐点固定，
故原有限元素性在这些绑定值与自由参数上给出 W 与 T 的真值对应。
不把域对象 W 放入 D，不要求枚举图属于 W，也不选择坍缩求值函数。

原 Z₂ 对象模式保留实际元素性及坍缩规格。本规则服务于真实种子、
壳和坍缩构造的装配，不将这些中间规格作为最终源存在性的假设。
本结论只比较 D 中的参数，不能据此断言任意 T 参数都与 W 同值，
尤其不能把坍缩后的见证自动当作原 W 中同一公式的见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCoveredCondensation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessRelativeMembershipCollapseSatisfaction (instance_m instance_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 全部原赋值落在同一个完整传递覆盖域时，坍缩不改变这些赋值。 -/
theorem formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (I W : Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set)
    {D T H : type_l hℳ}
    (hD : ∀ x, mem_l hℳ x D → ∀ y, mem_l hℳ y x → mem_l hℳ y D)
    (hDI : ∀ x, mem_l hℳ x D → mem_l hℳ x (I.eval ζ))
    (hH : PowerlessRelativeMembershipCollapse.spec_l (hℳ := hℳ) (I.eval ζ) T H)
    (hφ : (PowerlessRelativeFiniteElementarity.entry_m φ I W τ).satisfies ζ)
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (hτ : ∀ v, (τ v).eval ζ = η.freeVal v)
    (hBound : ∀ v : Variable Γ .set, mem_l hℳ (η.boundVal v) D)
    (hFree : ∀ v : Variable Δ .set, mem_l hℳ (η.freeVal v) D) :
    (PowerlessRelativization.formula_m φ).satisfies (η.pushFree (W.eval ζ)) ↔
      (PowerlessRelativization.formula_m φ).satisfies (η.pushFree T) := by
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := η.freeVal }
  have hFixed := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ D (I.eval ζ) T H
    hD hDI hH.2.1 hH.2.2.2.1
  have h : PowerlessRelativeMembershipCollapseSatisfaction.env_l hℳ (I.eval ζ) H η η :=
    ⟨fun v => ⟨hDI _ (hBound v), hFixed _ (hBound v)⟩,
      fun v => ⟨hDI _ (hFree v), hFixed _ (hFree v)⟩⟩
  have hElem := (PowerlessRelativeFiniteElementarity.entry_formula_l φ ζ I W τ ν hτ).mp
    hφ η (fun _ _ => rfl) (fun v => hDI _ (hBound v))
  exact hElem.trans (PowerlessRelativeMembershipCollapseSatisfaction.formula_l hℳ φ hH η η h)

def schema_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (D I W T H : Term ℒ [] Θ .set)
    (ρ : Variable Γ .set → Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m D) <|
    .imp (ThirdOrderTheory.subset_m D I) <|
      .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
        .imp (PowerlessRelativeFiniteElementarity.entry_m φ I W τ) <|
          .imp (parameters_m Γ D (fun {s} v => match s with | .set => ρ v)) <|
            .imp (parameters_m Δ D (fun {s} v => match s with | .set => τ v)) <|
              .iff (instance_m φ W ρ τ) (instance_m φ T ρ τ)

def sentence_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (D I W T H : Term ℒ [] Θ .set)
    (ρ : Variable Γ .set → Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ D I W T H ρ τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (D I W T H : Term ℒ [] Θ .set)
    (ρ : Variable Γ .set → Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    (sentence_m φ D I W T H ρ τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hD hDI hH hφ hρ hτ
  let η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ :=
    { boundVal := fun {s} v => match s with | .set => (ρ v).eval ζ
      freeVal := fun {s} v => match s with | .set => (τ v).eval ζ }
  have hD₀ := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ ζ D).mp hD
  have hDI₀ := (subset_formula_l ζ D I).mp hDI
  have hH₀ := (PowerlessRelativeMembershipCollapse.spec_formula_l ζ I T H).mp hH
  have hρ₀ := (parameters_formula_l Γ ζ D (fun {s} v => match s with | .set => ρ v)).mp hρ
  have hτ₀ := (parameters_formula_l Δ ζ D (fun {s} v => match s with | .set => τ v)).mp hτ
  exact (instance_formula_l φ ζ W ρ τ η (fun _ => rfl) (fun _ => rfl)).trans
    ((formula_l hℳ φ ζ I W τ hD₀ hDI₀ hH₀ hφ η (fun _ => rfl)
      (fun v => hρ₀ _ v) (fun v => hτ₀ _ v)).trans
        (instance_formula_l φ ζ T ρ τ η (fun _ => rfl) (fun _ => rfl)).symm)

theorem derives_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (D I W T H : Term ℒ [] Θ .set)
    (ρ : Variable Γ .set → Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ D I W T H ρ τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ D I W T H ρ τ)

#print axioms formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCoveredCondensation
