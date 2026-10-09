import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMapsDerives
import BMSConstructibleBridge.PowerlessFunctionTraceBounded
import BMSConstructibleBridge.PowerlessFunctionIteration
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 实际无限迭代的有限限制留在共同极限层

无限图只需存在于原商。限制图的层界来自任意有限映射的内部归纳界，
不循环假定无限图已属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteFunctionRestriction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem trace_exists_l (K : source_coding_l hℳ) {A H a F : type_l hℳ}
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a F)
    (n : SecondOrderModel.num_l ℳ) : ∃ g,
      PowerlessFunctionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a (numberCode_l K n).val g ∧
      ∀ x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g x y ↔
        mem_l hℳ x (numberCode_l K (SecondOrderModel.succ_l n)).val ∧
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x y := by
  let e := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  let m := (numberCode_l K (SecondOrderModel.succ_l n)).val
  obtain ⟨hMap, h₀, hStep⟩ := hF
  obtain ⟨g, hg, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ (S := m) hMap
    (fun x hx => SecondOrderOmegaTransitive.member_l hℳ (k := m) K.omega_spec
      (numberCode_l K (SecondOrderModel.succ_l n)).property hx)
  have hg' : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g m A := hg
  have hRead' (x y : type_l hℳ) : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g x y ↔
      mem_l hℳ x m ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x y := hRead x y
  have heM : mem_l hℳ e m := (numberCode_mem_iff_lt_l K _ _).mpr (SecondOrderOrder.zero_succ_l hℳ n)
  refine ⟨g, ⟨m,
      (numberCode_l K (SecondOrderModel.succ_l n)).property, PowerlessBMSQuotientSuccessor.successor_l K n,
      hg', (hRead' e a).mpr ⟨heM, h₀⟩, ?_⟩, hRead'⟩
  intro k hk l _ x _ y _ hkl hx hy
  exact hStep k l x y
    (SecondOrderOmegaTransitive.member_l hℳ (k := (numberCode_l K n).val) K.omega_spec (numberCode_l K n).property hk) hkl
    ((hRead' k x).mp hx).2 ((hRead' l y).mp hy).2

theorem exists_l (K : source_coding_l hℳ) {B β C A H a F : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hωC : mem_l hℳ K.omega C) (hAC : mem_l hℳ A C)
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a F)
    (n : SecondOrderModel.num_l ℳ) : ∃ g, mem_l hℳ g C ∧
      PowerlessFunctionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A H a (numberCode_l K n).val g := by
  obtain ⟨g, hg, _⟩ := trace_exists_l K hF n
  have hgC : mem_l hℳ g C := by
    obtain ⟨m, hmω, _, hMap, _, _⟩ := hg
    exact PowerlessRelativeLimitFiniteMaps.member_l hℳ (n := m) (f := g)
      hBase hLimit hC K hωC hAC hmω hMap
  exact ⟨g, hgC, hg⟩

#print axioms trace_exists_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteFunctionRestriction
