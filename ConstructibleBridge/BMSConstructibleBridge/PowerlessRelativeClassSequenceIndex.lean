import BMSConstructibleBridge.PowerlessBoundedSequenceIndex
import BMSConstructibleBridge.PowerlessRelativeClassSequenceCode
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 全体内部有限自然数序列的类内编号关系

每个序列有编号，同一编号最多对应一个序列；未使用配数反解的总性。
编号图首先是关系而非全域函数，之后才能取最小编号并补齐空编号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceIndex

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem absolute_l (ω e S one two I f : type_l hℳ B) :
    PowerlessBoundedSequenceIndex.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two I f ↔
      PowerlessBoundedSequenceIndex.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val S.val one.val two.val I.val f.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set, .set] :=
    (((((((Env.empty).pushFree f).pushFree I).pushFree two).pushFree one).pushFree S).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let i : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let g : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  exact (PowerlessBoundedSequenceIndex.formula_l η w z s a b i g).symm.trans
    ((PowerlessRelativeClassBounded.formula_l (hBase := hBase)
      (PowerlessBoundedSequenceIndex.delta_l w z s a b i g) η).trans
      (PowerlessBoundedSequenceIndex.formula_l (PowerlessRelativeClassRelativization.env_l η) w z s a b i g))

theorem exists_l (K : source_coding_l hℳ) {ω e S one two f : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S.val)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hone : one.val = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val)
    (htwo : two.val = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val)
    (hf : mem_l hℳ f.val S.val) : ∃ I : type_l hℳ B, mem_l hℳ I.val ω.val ∧
      PowerlessBoundedSequenceIndex.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two I f := by
  obtain ⟨n, hn, hfMap⟩ := (hS f.val).mp hf
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hiEq : n = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  rw [hiEq] at hfMap
  obtain ⟨c, hc⟩ := PowerlessBoundedSequenceCode.exists_l K hS hE i hfMap
  let p := SecondOrderPairing.value_l i c
  have hpω : mem_l hℳ (numberCode_l K p).val ω.val := hω.symm ▸ (numberCode_l K p).property
  let I : type_l hℳ B := ⟨(numberCode_l K p).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hpω⟩
  refine ⟨I, hpω, (absolute_l (hBase := hBase) ω e S one two I f).mpr ?_⟩
  rw [hω, he, hone, htwo]
  exact ⟨(numberCode_l K i).val, (numberCode_l K i).property,
    (numberCode_l K c).val, (numberCode_l K c).property, hfMap, hc,
    (PowerlessBoundedNumericPairing.instance_l K hS i c I.val).mpr rfl⟩

theorem unique_l (K : source_coding_l hℳ) {ω e S one two I f g : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S.val)
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hf : PowerlessBoundedSequenceIndex.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two I f)
    (hg : PowerlessBoundedSequenceIndex.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two I g) : f = g := by
  have hf₀ := (absolute_l (hBase := hBase) ω e S one two I f).mp hf
  have hg₀ := (absolute_l (hBase := hBase) ω e S one two I g).mp hg
  rw [hω, he] at hf₀ hg₀
  exact Subtype.ext (PowerlessBoundedSequenceIndex.unique_l K hS hf₀ hg₀)

theorem graph_l (ω e S one two : type_l hℳ B) : ∃ G : type_l hℳ B,
    ∀ I f : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) G I f ↔
      mem_l hℳ I.val ω.val ∧ mem_l hℳ f.val S.val ∧
        PowerlessBoundedSequenceIndex.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two I f := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree two).pushFree one).pushFree S).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  obtain ⟨G, hG⟩ := PowerlessRelativeClassRelationalGraph.exists_l (hBase := hBase)
    (PowerlessBoundedSequenceIndex.delta_l w z s a b (.fvar .here) (.fvar (.there .here))) η ω S
  refine ⟨G, fun I f => (hG I f).trans ?_⟩
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (PowerlessBoundedSequenceIndex.formula_l ((η.pushFree f).pushFree I) w z s a b
      (.fvar .here) (.fvar (.there .here))))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceIndex
