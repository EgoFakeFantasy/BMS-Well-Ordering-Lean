import BMSConstructibleBridge.SecondOrderSections
import BMSConstructibleBridge.PowerlessBMSQuotientParameterTransfer
import BMSConstructibleBridge.PowerlessBMSQuotientReals
import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 原二阶历史行的纯隶属公式

沿原切片模板的完整算术翻译读取历史行，全部数量词保留为模型内部 ω。
输出显式限制为 ω 子集；逐行代表在 Prop 中存在，不选出 Type 值列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSecondOrderSections

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessArithmeticTerms PowerlessBMSQuotientTranslation PowerlessBMSQuotientArithmetic

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l

universe u

def parameters_m {Γ Δ : SortContext ℒ} (H R i : Term ℒ Γ Δ .set) :
    assignment_m [.set, .set, .num] Γ Δ
  | _, .here => H
  | _, .there .here => R
  | _, .there (.there .here) => i

def formula_m {Γ Δ : SortContext ℒ} (ω e H i R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (ThirdOrderTheory.subset_m R ω)
    (PowerlessArithmeticTranslation.formula_m (Γ := []) ω e (fun v => nomatch v)
      (parameters_m H R i) SecondOrderSections.template_m)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (w z H i S : Term ℒ Γ Δ .set)
    (A B : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega)
    (X Y : SecondOrderModel.set_l ℳ) (n : SecondOrderModel.num_l ℳ)
    (hw : w.eval η = K.omega) (hz : z.eval η = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hH : H.eval η = B.val) (hS : S.eval η = A.val) (hi : i.eval η = (numberCode_l K n).val)
    (hA : setRel_l K A X) (hB : setRel_l K B Y) :
    (formula_m w z H i S).satisfies η ↔ SecondOrderSections.spec_l Y n X := by
  let ξ : Env (arithmetic_l K) [] [.set, .set, .num] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => B
      | .there .here => A
      | .there (.there .here) => numberCode_l K n }
  let ξ' : Env ℳ [] [.set, .set, .num] := ((Env.empty.pushFree n).pushFree X).pushFree Y
  have hτ : agrees_l η (parameters_m H S i) ξ.freeVal := by
    intro s v
    cases v with
    | here => exact hH
    | there v => cases v with
      | here => exact hS
      | there v => cases v with
        | here => exact hi
        | there v => nomatch v
  have hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l K) ξ ξ' := by
    constructor
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => exact hB
      | there v => cases v with
        | here => exact hA
        | there v => cases v with
          | here => exact numberEquiv_numberCode_l K n
          | there v => nomatch v
  have hTranslation := PowerlessBMSQuotientParameterTransfer.formula_l K
    SecondOrderSections.template_m (SecondOrderArithmetic.pure_language_m _ rfl)
    ξ ξ' η w z (fun v => nomatch v) (parameters_m H S i) hw hz
    (fun v => nomatch v) hτ hRelated
  have hTemplate : SecondOrderSections.template_m.satisfies ξ' ↔
      SecondOrderSections.spec_l Y n X := by
    simp only [SecondOrderSections.template_m, SecondOrderSections.spec_l,
      Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  simp only [formula_m, Formula.satisfies, subset_formula_l]
  constructor
  · intro h
    exact hTemplate.mp (hTranslation.mp h.2)
  · intro h
    refine ⟨?_, hTranslation.mpr (hTemplate.mpr h)⟩
    rw [hS, hw]
    exact A.property

/-- 存在原二阶行及其纯集合代表，未把逐行存在提升成外部选择函数。 -/
theorem exists_l (K : source_coding_l hℳ)
    (B : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (Y : SecondOrderModel.set_l ℳ)
    (hB : setRel_l K B Y) (n : SecondOrderModel.num_l ℳ) :
    ∃ X : SecondOrderModel.set_l ℳ, ∃ A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega,
      setRel_l K A X ∧ SecondOrderSections.spec_l Y n X ∧
      (formula_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))).satisfies
        (((((Env.empty.pushFree A.val).pushFree (numberCode_l K n).val).pushFree B.val).pushFree
          (numberCode_l K (SecondOrderModel.zero_l ℳ)).val).pushFree K.omega) := by
  obtain ⟨X, hX⟩ := SecondOrderSections.exists_l hℳ Y n
  obtain ⟨A, hA⟩ := representative_exists_l K X
  refine ⟨X, A, hA, hX, ?_⟩
  exact (formula_l K _ _ _ _ _ _ A B X Y n rfl rfl rfl rfl rfl hA hB).mpr hX

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSecondOrderSections
