import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderStepAmbient
import BMSConstructibleBridge.PowerlessRelativeClassSequenceSlicesAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderInduction

/-! # 全部内部定长切片的环境良序归纳

归纳公式在环境商中解释，切片及其子集量词均不相对化。
每一步先由有限函数提升及外延性取得同一切片的类内载体，
再使用环境后继步骤。此语义接口不假定内部自然数外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderInductionAmbient

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem zero_l {ω n X R L P : type_l hℳ B}
    (hn : member_l 𝒩 n ω) (hEmpty : ∀ i, ¬member_l 𝒩 i n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒩) n X P)
    (hRead : ∀ f g, value_l (ℳ := 𝒩) L f g ↔ shortlex_l (ℳ₀ := 𝒩) ω X R f g) :
    wellOrder_l (ℳ := 𝒱) P.val L.val := by
  have hClass := PowerlessRelativeClassSequenceOrderSlices.zero_l hn hEmpty hP hRead
  apply PowerlessRelativeClassAmbientWellOrder.of_minimum_l hClass
  intro U hU
  obtain ⟨f, hf⟩ := hU.2
  let f' : type_l hℳ B := ⟨f,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P.property (hU.1 f hf)⟩
  refine ⟨f, hf, ?_⟩
  intro g hg hgf
  let g' : type_l hℳ B := ⟨g,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P.property (hU.1 g hg)⟩
  have hEq : g' = f' := PowerlessRelativeClassSequenceZeroOrder.unique_l hEmpty
    ((hP g').mp (hU.1 g hg)) ((hP f').mp (hU.1 f hf))
  have hEdge : value_l (ℳ := 𝒩) L g' f' :=
    (PowerlessRelativeClassFunctionAbsolute.value_l L g' f').mpr hgf
  rw [hEq] at hEdge
  exact hClass.1 f' (hU.1 f hf) hEdge

theorem all_l {ω X R L : type_l hℳ B} (hω : omega_l (ℳ := 𝒩) ω)
    (hR : wellOrder_l (ℳ := 𝒱) X.val R.val)
    (hRead : ∀ f g, value_l (ℳ := 𝒩) L f g ↔ shortlex_l (ℳ₀ := 𝒩) ω X R f g) :
    ∀ n : type_l hℳ B, member_l 𝒩 n ω → ∀ P : SecondOrderQuotient.type_l hℳ,
      PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒱) n.val X.val P →
        wellOrder_l (ℳ := 𝒱) P L.val := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωRaw := (PowerlessRelativeClassOmegaAbsolute.omega_l ω).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hωRaw K.omega_spec
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hωRaw
  let N : SecondOrderModel.num_l ℳ → type_l hℳ B :=
    PowerlessRelativeClassInduction.number_l (hBase := hBase) K
  have hNum (i : SecondOrderModel.num_l ℳ) : member_l 𝒩 (N i) ω := by
    change mem_l hℳ (numberCode_l K i).val ω.val
    rw [hωEq]
    exact (numberCode_l K i).property
  have hIrr (n : type_l hℳ B) (hn : member_l 𝒩 n ω) : ¬member_l 𝒩 n n :=
    hOrd.wellOrder.linear.irrefl n.val hn
  have hTrans (n : type_l hℳ B) (hn : member_l 𝒩 n ω) :
      ∀ i : type_l hℳ B, member_l 𝒩 i n →
        ∀ j : type_l hℳ B, member_l 𝒩 j i → member_l 𝒩 j n := by
    have hnOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) n.val := hOrd.mem hn
    exact fun i hi j hj => hnOrd.transitive i.val hi j.val hj
  let φ : Formula ℒ [] [.set, .set, .set] :=
    PowerlessRelativeClassSequenceOrderInduction.template_m
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  let η : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree L.val).pushFree X.val
  have hFormula (i : SecondOrderModel.num_l ℳ) :
      φ.satisfies (η.pushFree (numberCode_l K i).val) ↔ ∀ P,
        PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := 𝒱) (N i).val X.val P →
          wellOrder_l (ℳ := 𝒱) P L.val :=
    PowerlessRelativeClassSequenceOrderInduction.template_formula_l _ _ _ _
  have hAll := PowerlessBMSQuotientInduction.induction_l K φ η ?_ ?_
  · intro n hn
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hωEq ▸ hn⟩
    have hVal : (numberCode_l K i).val = n.val := congrArg Subtype.val hi
    have hEq : N i = n := Subtype.ext hVal
    exact hEq ▸ (hFormula i).mp (hAll i)
  · apply (hFormula (SecondOrderModel.zero_l ℳ)).mpr
    intro P hP
    obtain ⟨Q, hQP, hQ⟩ := PowerlessRelativeClassSequenceSlicesAbsolute.lift_l hω
      (hNum (SecondOrderModel.zero_l ℳ)) hP
    rw [← hQP]
    exact zero_l (hNum (SecondOrderModel.zero_l ℳ))
      (fun x => PowerlessBMSQuotientSuccessor.zero_l K x.val) hQ hRead
  · intro i hi
    apply (hFormula (SecondOrderModel.succ_l i)).mpr
    intro Q hQ
    obtain ⟨Q', hQQ, hQ'⟩ := PowerlessRelativeClassSequenceSlicesAbsolute.lift_l hω
      (hNum (SecondOrderModel.succ_l i)) hQ
    obtain ⟨P, hP⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (X := X) hω (hNum i)
    have hOld := (hFormula i).mp hi P.val (PowerlessRelativeClassSequenceSlicesAbsolute.spec_l hω (hNum i) hP)
    have hSucc := (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase)
      (N i) (N (SecondOrderModel.succ_l i))).mpr (PowerlessBMSQuotientSuccessor.successor_l K i)
    rw [← hQQ]
    exact PowerlessRelativeClassSequenceOrderStepAmbient.step_l
      (hNum i) (hNum (SecondOrderModel.succ_l i)) (hIrr _ (hNum i))
      (hIrr _ (hNum (SecondOrderModel.succ_l i))) hSucc (hTrans _ (hNum i))
      hP hQ' hRead hR hOld

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderInductionAmbient
