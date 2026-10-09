import BMSConstructibleBridge.PowerlessHereditaryParameterRealFamily
import BMSConstructibleBridge.PowerlessHereditaryRealRequestIntrinsic
import BMSConstructibleBridge.PowerlessHereditaryRealRequestDecode
import BMSConstructibleBridge.PowerlessHereditaryFiniteSequences
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 原遗传对象请求的整张类内带根见证族

纯隶属 ℒ，原 Z₂ 背景。实际数序列集、零与一在证明内构造并证明遗传。
原有限参数及原请求不更换。逐数遗传对象见证经同一实际带根请求
规范实数化，整张族的实际遗传内域迹 U 随同原模型实数 H 一起给出。

类内请求通过前置双向读数恢复为原 raw 请求。没有 Class 真值替代
raw 包络，也不声称解码集合 C 已在内域；Collection 仍是独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRootedWitnessFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

abbrev support_m : SortContext ℒ := [.set, .set, .set, .set]

private def binding_m {Δ : SortContext ℒ} :
    Substitution ℒ [] (.set :: .set :: Δ) [.set] (.set :: .set :: (support_m ++ Δ)) :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => .bvar .here
      | .there .here => .fvar (.there .here)
      | .there (.there v) => .fvar (.there (.there (.there (.there (.there (.there v)))))))

def request_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: (support_m ++ Δ)) :=
  .existsE .set <| .conj (φ.substitute binding_m)
    (PowerlessHereditaryRealRequestIntrinsic.formula_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.bvar .here) (.fvar .here))

def support_env_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (χ : Env 𝒩 [] Δ) (ω e o S : carrier_l 𝒩) : Env 𝒩 [] (support_m ++ Δ) where
  boundVal v := nomatch v
  freeVal {s} v := match s with
    | .set => match v with
      | .here => ω
      | .there .here => e
      | .there (.there .here) => o
      | .there (.there (.there .here)) => S
      | .there (.there (.there (.there v))) => χ.freeVal v

private theorem original_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩 [] Δ)
    (ω e o S x V X : carrier_l 𝒩) :
    (φ.substitute binding_m).satisfies
      ((((support_env_l χ ω e o S).pushFree x).pushFree V).pushBound X) ↔
        φ.satisfies ((χ.pushFree x).pushFree X) := by
  rw [Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (χ : Env 𝒩₀ [] Δ) (ω e o S x V : M) :
    (request_m φ).satisfies (((support_env_l χ ω e o S).pushFree x).pushFree V) ↔
      ∃ X : M, φ.satisfies ((χ.pushFree x).pushFree X) ∧
        PowerlessHereditaryRealRequest.holds_l B ω.val e.val o.val S.val X.val V.val := by
  simp only [request_m, Formula.satisfies, original_formula_l,
    PowerlessHereditaryRealRequestIntrinsic.formula_l, Term.eval]
  rfl

include hBase in
/-- 数序列母域的实际 raw 规格和遗传资格同时构造，未预供 S。 -/
theorem sequences_l (K : source_coding_l hℳ) :
    ∃ S : M, PowerlessHereditaryClass.member_l hℳ B S.val ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S.val := by
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec
  let O : M := ⟨K.omega, PowerlessHereditaryClass.contained_l hℳ hBase hωHC⟩
  have hO := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
  obtain ⟨S, hS, hEnvelope⟩ := PowerlessHereditaryFiniteSequences.exists_l hO
    ((PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) O).mp hωHC)
  obtain ⟨S', hRaw, hS'⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (X := O) hO
  have hEq : S' = S := (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    S' S (fun f => (hS' f).trans (hS f).symm)
  exact ⟨S, (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) S).mpr hEnvelope,
    hEq ▸ hRaw⟩

theorem exists_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (hSome : ∀ x : M, mem_l hℳ x.val K.omega → ∃ X : M,
      PowerlessHereditaryClass.member_l hℳ B X.val ∧ φ.satisfies ((χ.pushFree x).pushFree X)) :
    ∃ S : M, PowerlessHereditaryClass.member_l hℳ B S.val ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S.val ∧
      ∃ U : M, PowerlessHereditaryClass.member_l hℳ B U.val ∧
        ∃ hU : ∀ m, mem_l hℳ m U.val → mem_l hℳ m K.omega,
          ∃ H : SecondOrderModel.set_l ℳ, setRel_l K ⟨U.val, hU⟩ H ∧
            ∀ n : SecondOrderModel.num_l ℳ, ∃ V X : M,
              PowerlessHereditaryClass.member_l hℳ B V.val ∧
              PowerlessHereditaryClass.member_l hℳ B X.val ∧
              φ.satisfies ((χ.pushFree (PowerlessRelativeClassInduction.number_l (hBase := hBase) K n)).pushFree X) ∧
              PowerlessHereditaryRealRequest.holds_l B K.omega
                (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
                (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val S.val X.val V.val ∧
              ∀ m, SecondOrderPairing.relation_l H n m ↔ mem_l hℳ (numberCode_l K m).val V.val := by
  obtain ⟨S, hSHC, hS⟩ := sequences_l (hBase := hBase) K
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec
  let O : M := ⟨K.omega, PowerlessHereditaryClass.contained_l hℳ hBase hωHC⟩
  let e := PowerlessRelativeClassInduction.number_l (hBase := hBase) K (SecondOrderModel.zero_l ℳ)
  let o := PowerlessRelativeClassInduction.number_l (hBase := hBase) K
    (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))
  have heMem : mem_l hℳ e.val K.omega := (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have hoMem : mem_l hℳ o.val K.omega :=
    (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).property
  have heHC := PowerlessHereditaryClass.transitive_l hℳ hωHC heMem
  have hoHC := PowerlessHereditaryClass.transitive_l hℳ hωHC hoMem
  let ξ := support_env_l χ O e o S
  have hParams' : ∀ v : Variable (support_m ++ Δ) .set,
      PowerlessHereditaryClass.member_l hℳ B (ξ.freeVal v).val := by
    intro v
    cases v with
    | here => exact hωHC
    | there v => cases v with
      | here => exact heHC
      | there v => cases v with
        | here => exact hoHC
        | there v => cases v with
          | here => exact hSHC
          | there v => exact hParams v
  obtain ⟨U, hUHC, hU, H, hTrace, hRows⟩ := PowerlessHereditaryParameterRealFamily.exists_l K hB hNonempty
    (request_m φ) ξ hParams'
    (fun x hx => by
      obtain ⟨X, hXHC, hφ⟩ := hSome x hx
      obtain ⟨V, hV⟩ := PowerlessHereditaryRealRequest.exists_l (hBase := hBase) K hS hXHC
      let V₀ : M := ⟨V, PowerlessHereditaryRealRequest.class_l hV⟩
      exact ⟨V₀, (formula_l φ χ O e o S x V₀).mpr ⟨X, hφ, hV⟩⟩)
    (fun x V _ hV => by
      obtain ⟨_, _, hRequest⟩ := (formula_l φ χ O e o S x V).mp hV
      exact PowerlessHereditaryRealRequest.real_l hRequest)
  refine ⟨S, hSHC, hS, U, hUHC, hU, H, hTrace, fun n => ?_⟩
  obtain ⟨V, hVHC, hV, hRow⟩ := hRows n
  obtain ⟨X, hφ, hRequest⟩ := (formula_l φ χ O e o S _ V).mp hV
  have hXHC : PowerlessHereditaryClass.member_l hℳ B X.val := by
    obtain ⟨T, f, _r, h⟩ := hRequest
    exact ⟨T, f, K.omega, h.1⟩
  exact ⟨V, X, hVHC, hXHC, hφ, hRequest, hRow⟩

#print axioms formula_l
#print axioms sequences_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRootedWitnessFamily
