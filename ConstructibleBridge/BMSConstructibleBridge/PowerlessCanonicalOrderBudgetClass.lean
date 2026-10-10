import BMSConstructibleBridge.PowerlessCanonicalOrderBudgetInduction

/-! # 消去预算前提的同一原比较图 Class 身份

实际五参数 Class 环境给出三尾预算；其定义域取原阶段的实际后继，故终点
也在预算域内。原比较图只留 raw，在原内部归纳后才进入 Class。
不把 Class 身份误记为图属于层 W，不预设统一枚举或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderBudgetClass

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem class_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {δ H q : Raw}
    (W F P₀ ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W.val)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hδ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) δ)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F.val W.val)
    (hH : map_l (ℳ := 𝒱) H δ q)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val B P₀.val F.val H)
    (hOrder : ∀ a X P, value_l (ℳ := 𝒱) F.val a X → value_l (ℳ := 𝒱) H a P →
      wellOrder_l (ℳ := 𝒱) X P) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B H := by
  obtain ⟨D, hD⟩ := SecondOrderQuotient.surj_l hℳ δ
  obtain ⟨A, hA, hδA, _hSucc⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ D (hD ▸ hδ)
  have hδA' : mem_l hℳ δ (mk_l hℳ A) := hD ▸ hδA
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree P₀ |>.pushFree G |>.pushFree F |>.pushFree ω |>.pushFree W
  obtain ⟨Q, hBudget⟩ := PowerlessThreeDefBudgetExists.exists_l hℳ K hBase η hA
  have hEnv : PowerlessRelativeClassRelativization.env_l η =
      PowerlessCanonicalOrderBudgetInduction.parameters_l W.val ω.val F.val G.val P₀.val := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => cases v with
            | here => rfl
            | there v => cases v with
              | here => rfl
              | there v => nomatch v
  have hBudget' : PowerlessThreeDefBudget.spec_l hℳ
      (PowerlessCanonicalOrderBudgetInduction.parameters_l W.val ω.val F.val G.val P₀.val)
        B (mk_l hℳ A) Q := hEnv ▸ hBudget
  obtain ⟨ν, hQ⟩ := hBudget'.total δ hδA'
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
    (hBudget'.output_ordinal δ ν hQ)
  have hSelf : PowerlessCanonicalOrderRawPrefix.holds_l (𝒩 := 𝒱) H q δ H := by
    refine ⟨hH, fun a P => ?_⟩
    exact ⟨fun hP => ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hH hP).1, hP⟩,
      fun hP => hP.2⟩
  exact ⟨ν, C, hC, PowerlessCanonicalOrderBudgetInduction.bounded_l hBase K
    ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hδ hF hH hEquations hOrder
    hBudget' δ ν C H hQ hC hSelf⟩

#print axioms class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderBudgetClass
