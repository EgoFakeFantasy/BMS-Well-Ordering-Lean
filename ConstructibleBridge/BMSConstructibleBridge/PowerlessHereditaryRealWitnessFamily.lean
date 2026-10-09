import BMSConstructibleBridge.PowerlessHereditaryParameterRelation
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalSkolemDerives
import BMSConstructibleBridge.PowerlessRelativeClassNumericGraph

/-! # 有限遗传参数的统一类内实数见证族

纯隶属 ℒ，背景原 Z₂。每个内部数索引都有实际 Class 实数见证时，
按同一规范比较选取原请求的最小见证。任意公式的数索引／成员关系
在实际 ω×ω 上分离，再数码化为一张遗传实数。没有点态见证冒充整族，
不抽取 Type 选择函数，也不假定首 Ω 或 Collection。

这是统一实数族的内域资格工具；尚未证明其解码所得对象集合遗传，
也未把本模块的语义装配声称为最终固定高度 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealWitnessFamily

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 关系首槽是输入数，次槽是成员数；选取输出另以存在量词绑定。 -/
def membership_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  .existsE .set <| .conj
    (PowerlessDefinableMembershipDiagram.at_m φ (up (.fvar .here)) (.bvar .here)
      (fun v => up (.fvar (.there (.there v)))))
    (SecondOrderObjectSyntax.member_m (up (.fvar (.there .here))) (.bvar .here))

theorem membership_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (n m : carrier_l 𝒩) :
    (membership_m φ).satisfies ((η.pushFree m).pushFree n) ↔
      ∃ V, φ.satisfies ((η.pushFree n).pushFree V) ∧ member_l 𝒩 m V := by
  change (∃ V, _ ∧ _) ↔ _
  apply exists_congr
  intro V
  have hEnv : PowerlessDefinableMembershipDiagram.env_l (((η.pushFree m).pushFree n).pushBound V)
      (fun v : Variable Δ .set => up (.fvar (.there (.there v)))) = η := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; rfl
  simp only [PowerlessDefinableMembershipDiagram.at_formula_l, hEnv, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, member_l, Arguments.eval, up, Term.eval_weakenBound,
    Term.eval, Env.pushFree_here, Env.pushFree_there, Env.pushBound_bound_here]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem exists_l (K : source_coding_l hℳ)
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (χ : Env 𝒩₀ [] Δ)
    (b ω P₀ : Term ℒ [] Δ .set) (hb : (b.eval χ).val = B) (hω : (ω.eval χ).val = K.omega)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B (P₀.eval χ).val)
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
  let O := ω.eval χ
  have hωRaw : SecondOrderOmega.omega_l hℳ O.val := hω.symm ▸ K.omega_spec
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase K.omega_spec
  obtain ⟨K', _e, r₁, r₂, r₃, Pair, Valid, hω', _he, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l (PowerlessBMSQuotientOmega.omega_l hℳ hωRaw)
  let θ := PowerlessCanonicalCodedSkolemSyntax.operator_m φ b ω P₀
  have hOpening : PowerlessSourceOpening.env_l χ = χ := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; rfl
  have hReading (x V : M) : θ.satisfies ((χ.pushFree x).pushFree V) ↔
      PowerlessCanonicalCodedSkolemSyntax.relation_l (𝒩 := 𝒩₀) φ χ
        ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ O (P₀.eval χ) x V := by
    have hb' : b.eval χ = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
      Subtype.ext hb
    simpa only [hOpening, PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l, hb'] using
      PowerlessCanonicalCodedSkolemSyntax.operator_formula_l
        (PowerlessRelativeClassStructure.ext_l hℳ B hBase) φ χ b ω P₀ x V
  obtain ⟨Q, _hQHC, hQ⟩ := PowerlessHereditaryParameterRelation.values_l hB hNonempty hωRaw
    (membership_m θ) χ hParams O O (hω.symm ▸ hωHC) (hω.symm ▸ hωHC)
  obtain ⟨U, hU, H, hTrace, hCode⟩ := PowerlessRelativeClassNumericGraph.coded_l (hBase := hBase) K Q
  have hUHC := PowerlessHereditarySubset.member_l hℳ hBase hωHC U.property hU
  refine ⟨U, hUHC, hU, H, hTrace, fun n => ?_⟩
  let N := PowerlessRelativeClassInduction.number_l (hBase := hBase) K n
  obtain ⟨V, hV, hUnique⟩ := PowerlessRelativeClassCanonicalSkolemDerives.result_l
    (hBase := hBase) K' φ b χ hb O (P₀.eval χ) N hω' hCoding hGuard
  have hN : mem_l hℳ N.val K.omega := (numberCode_l K n).property
  have hφ : φ.satisfies ((χ.pushFree N).pushFree V) := by
    rcases hV with hV | hV
    · exact hV.1
    · exact (hV.1 (hSome N hN)).elim
  have hVHC := PowerlessHereditarySubset.member_l hℳ hBase hωHC V.property (hReal N V hN hφ)
  refine ⟨V, hVHC, hφ, fun m => ?_⟩
  let L := PowerlessRelativeClassInduction.number_l (hBase := hBase) K m
  have hL : mem_l hℳ L.val K.omega := (numberCode_l K m).property
  have hEdge : SecondOrderPairing.relation_l H n m ↔
      ∃ W : M, θ.satisfies ((χ.pushFree N).pushFree W) ∧ mem_l hℳ L.val W.val := by
    have h' : value_l (ℳ := 𝒩₀) Q N L ↔
        ∃ W : M, θ.satisfies ((χ.pushFree N).pushFree W) ∧ member_l 𝒩₀ L W := by
      constructor
      · intro hQL
        exact (membership_formula_l (𝒩 := 𝒩₀) θ χ N L).mp ((hQ N L).mp hQL).2.2
      · intro hWitness
        exact (hQ N L).mpr ⟨hω.symm ▸ hN, hω.symm ▸ hL,
          (membership_formula_l (𝒩 := 𝒩₀) θ χ N L).mpr hWitness⟩
    exact (hCode n m).trans
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) Q N L).symm.trans
        (h'.trans (exists_congr (fun W => and_congr Iff.rfl Iff.rfl))))
  refine hEdge.trans ⟨?_, ?_⟩
  · rintro ⟨W, hW, hm⟩
    exact (hUnique W ((hReading N W).mp hW)) ▸ hm
  · intro hm
    exact ⟨V, (hReading N V).mpr hV, hm⟩

#print axioms membership_formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealWitnessFamily
