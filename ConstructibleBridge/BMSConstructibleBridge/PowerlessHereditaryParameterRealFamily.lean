import BMSConstructibleBridge.PowerlessHereditaryRealWitnessFamily
import BMSConstructibleBridge.PowerlessHereditaryAmbientBaseGuard

/-! # 有限遗传参数的无额外守卫实数见证族

纯隶属 ℒ，原 Z₂ 背景。基底传递、遗传且非空，原有限参数遗传。
实际 ω 和初始良序由前置对象实例构造；仅扩充参数尾槽，不改写原
请求的输入／输出槽与逐见证语义。统一实数及其实际类内迹同时给出。

本模块是语义装配，不声称解码集合已经遗传、Collection 已完成，
也不以它替代原推导核中的固定高度 BMS 良序句子。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterRealFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

/-- 三个环境参数插在原参数之前；原请求的前两槽保持不动。 -/
def parameters_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ Δ [] (.set :: .set :: .set :: Δ) :=
  fun {s} v => match s with
    | .set => .fvar (.there (.there (.there v)))

def binding_m {Δ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Δ) [] (.set :: .set :: .set :: .set :: .set :: Δ) :=
  .map (fun v => nomatch v) (PowerlessClassPackedRequests.binding_m parameters_m)

def form_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: .set :: Δ) :=
  φ.substitute binding_m

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩 [] Δ)
    (B ω P₀ x V : carrier_l 𝒩) :
    (form_m φ).satisfies (((((χ.pushFree P₀).pushFree ω).pushFree B).pushFree x).pushFree V) ↔
      φ.satisfies ((χ.pushFree x).pushFree V) := by
  rw [form_m, Formula.satisfies_substitute]
  have hEnv :
      (((((χ.pushFree P₀).pushFree ω).pushFree B).pushFree x).pushFree V).pullback
        binding_m =
        (χ.pushFree x).pushFree V := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v =>
            simp only [binding_m, Env.pullback, PowerlessClassPackedRequests.binding_m, parameters_m,
              Term.eval_weakenFree, Term.eval, Env.pushFree_there]
  rw [hEnv]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem exists_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (hSome : ∀ x : M, mem_l hℳ x.val K.omega → ∃ V : M, φ.satisfies ((χ.pushFree x).pushFree V))
    (hReal : ∀ x V : M, mem_l hℳ x.val K.omega → φ.satisfies ((χ.pushFree x).pushFree V) →
      ∀ m, mem_l hℳ m V.val → mem_l hℳ m K.omega) :
    ∃ U : M, PowerlessHereditaryClass.member_l hℳ B U.val ∧
      ∃ hU : ∀ m, mem_l hℳ m U.val → mem_l hℳ m K.omega,
        ∃ H : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ H ∧
          ∀ n : SecondOrderModel.num_l ℳ, ∃ V : M,
            PowerlessHereditaryClass.member_l hℳ B V.val ∧
            φ.satisfies ((χ.pushFree (PowerlessRelativeClassInduction.number_l (hBase := hBase) K n)).pushFree V) ∧
            ∀ m, SecondOrderPairing.relation_l H n m ↔ mem_l hℳ (numberCode_l K m).val V.val := by
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec
  obtain ⟨P, hPHC, hGuard⟩ := PowerlessHereditaryAmbientBaseGuard.exists_l K hBase
    K.omega_spec hB hNonempty
  let B₀ : M := ⟨B, PowerlessHereditaryClass.contained_l hℳ hBase hB⟩
  let O : M := ⟨K.omega, PowerlessHereditaryClass.contained_l hℳ hBase hωHC⟩
  let P₀ : M := ⟨P, PowerlessHereditaryClass.contained_l hℳ hBase hPHC⟩
  let ξ := ((χ.pushFree (sort := SetTheory.SetSort.set) P₀).pushFree
    (sort := SetTheory.SetSort.set) O).pushFree (sort := SetTheory.SetSort.set) B₀
  have hParams' : ∀ v : Variable (.set :: .set :: .set :: Δ) .set,
      PowerlessHereditaryClass.member_l hℳ B (ξ.freeVal v).val := by
    intro v
    cases v with
    | here => exact hB
    | there v => cases v with
      | here => exact hωHC
      | there v => cases v with
        | here => exact hPHC
        | there v => exact hParams v
  obtain ⟨U, hUHC, hU, H, hTrace, hRows⟩ := PowerlessHereditaryRealWitnessFamily.exists_l K hB hNonempty
    (form_m φ) ξ (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    rfl rfl hGuard hParams'
    (fun x hx => by
      obtain ⟨V, hV⟩ := hSome x hx
      exact ⟨V, (formula_l φ χ B₀ O P₀ x V).mpr hV⟩)
    (fun x V hx hV => hReal x V hx ((formula_l φ χ B₀ O P₀ x V).mp hV))
  refine ⟨U, hUHC, hU, H, hTrace, fun n => ?_⟩
  obtain ⟨V, hVHC, hV, hRow⟩ := hRows n
  exact ⟨V, hVHC, (formula_l φ χ B₀ O P₀ _ V).mp hV, hRow⟩

#print axioms formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterRealFamily
