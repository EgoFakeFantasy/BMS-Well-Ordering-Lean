import BMSConstructibleBridge.PowerlessBoundedSequenceCode
import BMSConstructibleBridge.PowerlessRelativeClassBounded
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute

/-! # 精确有限序列编码的类内存在和绝对性

编码见证是内部自然数，故由类的传递性留在类内。S 的环境全称规格仍显式
保留；不以类内有限序列断言替代它，也不假设内部自然数为外部标准数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceCode

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

theorem absolute_l (ω e S one two n c f : type_l hℳ B) :
    PowerlessBoundedSequenceCode.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two n c f ↔
      PowerlessBoundedSequenceCode.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val S.val one.val two.val n.val c.val f.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    ((((((((Env.empty).pushFree f).pushFree c).pushFree n).pushFree two).pushFree one).pushFree S).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let k : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let d : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let g : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  exact (PowerlessBoundedSequenceCode.formula_l η w z s a b k d g).symm.trans
    ((PowerlessRelativeClassBounded.formula_l (hBase := hBase)
      (PowerlessBoundedSequenceCode.delta_l w z s a b k d g) η).trans
      (PowerlessBoundedSequenceCode.formula_l (PowerlessRelativeClassRelativization.env_l η) w z s a b k d g))

theorem exists_l (K : source_coding_l hℳ) {ω e S one two n f : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S.val)
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hone : one.val = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val)
    (htwo : two.val = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val)
    (hn : member_l (structure_l hℳ B hBase) n ω)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f n ω) :
    ∃ c : type_l hℳ B, member_l (structure_l hℳ B hBase) c ω ∧
      PowerlessBoundedSequenceCode.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two n c f := by
  have hn₀ : mem_l hℳ n.val K.omega := hω ▸ hn
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hn₀⟩
  have hiEq : n.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hf₀ : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val n.val ω.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n ω).mp hf
  rw [hiEq, hω] at hf₀
  obtain ⟨j, hj⟩ := PowerlessBoundedSequenceCode.exists_l K hS hE i hf₀
  have hjω : mem_l hℳ (numberCode_l K j).val ω.val := hω.symm ▸ (numberCode_l K j).property
  let c : type_l hℳ B := ⟨(numberCode_l K j).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hjω⟩
  refine ⟨c, hjω, (absolute_l (hBase := hBase) ω e S one two n c f).mpr ?_⟩
  simpa only [hω, he, hone, htwo, hiEq] using hj

theorem unique_l (K : source_coding_l hℳ) {ω e S one two n c f g : type_l hℳ B}
    (hω : ω.val = K.omega) (hn : member_l (structure_l hℳ B hBase) n ω)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f n ω)
    (hg : map_l (ℳ := structure_l hℳ B hBase) g n ω)
    (hcf : PowerlessBoundedSequenceCode.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two n c f)
    (hcg : PowerlessBoundedSequenceCode.holds_l (𝒩 := structure_l hℳ B hBase) ω e S one two n c g) : f = g := by
  have hf₀ : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val n.val ω.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n ω).mp hf
  have hg₀ : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g.val n.val ω.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g n ω).mp hg
  have hcf₀ := (absolute_l (hBase := hBase) ω e S one two n c f).mp hcf
  have hcg₀ := (absolute_l (hBase := hBase) ω e S one two n c g).mp hcg
  rw [hω] at hf₀ hg₀ hcf₀ hcg₀
  exact Subtype.ext (PowerlessBoundedSequenceCode.unique_l K (hω ▸ hn) hf₀ hg₀ hcf₀ hcg₀)

#print axioms absolute_l
#print axioms exists_l
#print axioms unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceCode
