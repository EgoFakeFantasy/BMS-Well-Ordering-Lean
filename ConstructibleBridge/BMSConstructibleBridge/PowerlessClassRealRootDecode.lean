import BMSConstructibleBridge.PowerlessKleeneBrouwerRootDecode
import BMSConstructibleBridge.PowerlessRootedRealSyntax
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 类内实数码的同一原根实际解码

原 Z₂ 任意模型中的语义辅助定理。输入仅为实际 Class 内的 ω 子集 V、
其原实数迹及一个合法根；数字关系 A、路径、可达域和原坍缩均内部构造。
输出是同一原图根的遗传资格，不只是 V 或其关系码的资格。
实际收集 C 的接线及最终 BMS 对象 Derives 仍须另行验收。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassRealRootDecode

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem hereditary_l (K : source_coding_l hℳ) {B V : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hVClass : PowerlessRelativeClassCorrespondence.member_l hℳ B V)
    (hVSub : ∀ x, mem_l hℳ x V → mem_l hℳ x K.omega)
    {R : SecondOrderModel.set_l ℳ} (hTrace : setRel_l K ⟨V, hVSub⟩ R)
    (r : SecondOrderModel.num_l ℳ) (hRoot : SecondOrderDomain.wf_l R r) :
    PowerlessHereditaryClass.member_l hℳ B (SecondOrderQuotient.mk_l hℳ ⟨R, r, hRoot⟩) := by
  have hOmegaClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  let O : type_l hℳ B := ⟨K.omega, hOmegaClass⟩
  let V₀ : type_l hℳ B := ⟨V, hVClass⟩
  let Z : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hOmegaClass
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  have hO : omega_l (ℳ := structure_l hℳ B hBase) O :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  obtain ⟨S, hS, _hSHC⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (X := O) hO
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    PowerlessRootedRealSyntax.row_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.fvar (.there .here))
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree V₀ |>.pushFree S |>.pushFree Z |>.pushFree O
  have hδ : Formula.IsDelta0 membershipLevyBound φ := PowerlessRootedRealSyntax.row_delta_m _ _ _ _ _ _
  obtain ⟨A, hA⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l hδ η O O
  have hFormula (a b : SecondOrderModel.num_l ℳ) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree
        (numberCode_l K b).val).pushFree (numberCode_l K a).val) ↔
      PowerlessRootedRealSyntax.row_l (𝒩 := 𝒱) K.omega Z.val S.val V
        (numberCode_l K a).val (numberCode_l K b).val :=
    PowerlessRootedRealSyntax.row_formula_l
      (((PowerlessRelativeClassRelativization.env_l η).pushFree
        (numberCode_l K b).val).pushFree (numberCode_l K a).val) _ _ _ _ _ _
  have hRead (a b : SecondOrderModel.num_l ℳ) : SecondOrderPairing.relation_l R a b ↔
      value_l (ℳ := 𝒱) A.val (numberCode_l K a).val (numberCode_l K b).val := by
    have hRow := PowerlessRootedRealSyntax.row_instance_l K hS hVSub hTrace a b
    constructor
    · intro hab
      exact (hA _ _).mpr ⟨(numberCode_l K a).property, (numberCode_l K b).property,
        (hFormula a b).mpr (hRow.mpr hab)⟩
    · intro hab
      exact hRow.mp ((hFormula a b).mp ((hA _ _).mp hab).2.2)
  exact PowerlessKleeneBrouwerRootDecode.hereditary_l K hBase A.property R r hRead hRoot

#print axioms hereditary_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassRealRootDecode
