import BMSConstructibleBridge.PowerlessRelationalCodeValidity
import BMSConstructibleBridge.PowerlessRelationalParameterAssignment
import BMSConstructibleBridge.PowerlessRelationalParameterDomain

/-! # 合法数码与跨域参数求值的共同存在

编码 K、实际三角图 T、数码和槽界在全部求值域之前选定。原内部合法性 V
实际存在，编译器同一输出属于 V；每个非空域仍有全部参数的真实赋值及正确
读数。这是任意原 Z₂ 模型中的加强语义接口；V 尚不被声明为相对类内对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalValidParameterCompilation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ K : source_coding_l hℳ, ∃ V : SecondOrderModel.set_l ℳ,
      SecondOrderTriangularFormulaSyntax.spec_l V ∧ ∃ e t₁ t₂ t₃ T : type_l hℳ B,
        ω.val = K.omega ∧ e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
        map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega ∧
        PowerlessBMSQuotientPairingBounds.spec_l K T.val ∧ ∃ c N : type_l hℳ B,
          mem_l hℳ c.val ω.val ∧ mem_l hℳ N.val ω.val ∧
          PowerlessRelationalCodeValidity.valid_l K V c.val N.val ∧
          ∃ ξ : Env (structure_l hℳ B hBase) [] Δ,
            PowerlessSourceEnvironment.bounded_l ξ N ∧ ∀ A,
              PowerlessRelationalParameterDomain.domain_l φ ξ ω e T t₁ t₂ t₃ c N A := by
  obtain ⟨K, e, t₁, t₂, t₃, T, hωEq, heEq, hMap, hSpec, hSystem⟩ :=
    PowerlessRelativeClassEvaluationSystem.uniform_coding_exists_l hω
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  obtain ⟨_, _, hStatic⟩ := hSystem ω
  obtain ⟨k, ξ, hk, hξ, hDistinct⟩ := PowerlessRelationalParameterAssignment.slots_l hω hStatic.1.1 Δ
  obtain ⟨c, N, hc, hN, hkN, hValid, hCompile⟩ :=
    PowerlessRelationalCodeValidity.formula_l K hωEq heEq hStatic.1 hMap hSpec hV
      hω hStatic.2.2.1 φ ξ hk hξ
  have hξN : PowerlessSourceEnvironment.bounded_l ξ N := fun t => hkN _ (hξ t)
  refine ⟨K, V, hV, e, t₁, t₂, t₃, T, hωEq, heEq, hMap, hSpec, c, N, hc, hN, hValid, ξ, hξN, ?_⟩
  intro A hA
  obtain ⟨S, G, hSG⟩ := hSystem A
  refine ⟨S, G, hSG, ?_⟩
  intro η m hm hM
  refine ⟨PowerlessRelationalParameterAssignment.exists_l hA ξ η (fun t => hM _ (hξN t)) hDistinct, ?_⟩
  exact fun f hf hRep => hCompile hSG hA m hm hM f hf η hRep

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalValidParameterCompilation
