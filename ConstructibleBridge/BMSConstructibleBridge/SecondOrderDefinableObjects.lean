import BMSConstructibleBridge.SecondOrderMemberStructure

/-!
# 可定义子集的内部集合收集上界

同一实际集合代码包含每个源公式及参数环境定义的子集，而且它的每个成员
都是原集合的子集。未宣称该收集上界已与原内部语法定义的 Def 精确相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableObjects

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : ∃ H : SecondOrderGraph.code_l ℳ,
      (∀ B, SecondOrderGraph.mem_l B H → ∀ C, SecondOrderGraph.mem_l C B → SecondOrderGraph.mem_l C A) ∧
      ∀ (Γ Δ : SortContext ℒ) (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
        (φ : Formula ℒ (.set :: Γ) Δ), ∃ B, SecondOrderGraph.mem_l B H ∧ ∀ C,
          SecondOrderGraph.mem_l C B ↔ ∃ n, relation_l A.real n A.root ∧
            Formula.satisfies (η.pushBound (SecondOrderMemberStructure.value_l hℳ A a ha n)) φ ∧
            SecondOrderBisimulation.eq_l C.real A.real C.root n := by
  obtain ⟨F, hF⟩ := SecondOrderMemberStructure.coverage_l hℳ A a ha
  obtain ⟨G, hG, H, hH⟩ := SecondOrderSubsetCollection.exists_l hℳ A F
  refine ⟨H, ?_, ?_⟩
  · intro B hB C hC
    obtain ⟨i, hi⟩ := (hH B).mp hB
    exact SecondOrderSubsetLayer.subset_l hℳ A F G hG i C
      ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) hi).mp hC)
  · intro Γ Δ η φ
    obtain ⟨i, hi⟩ := hF Γ Δ η φ
    refine ⟨SecondOrderSubsetLayer.code_l hℳ A F G hG i, (hH _).mpr ⟨i, SecondOrderGraph.refl_l hℳ _⟩, ?_⟩
    intro C
    refine (SecondOrderSubsetLayer.mem_l hℳ A F G hG i C).trans ?_
    apply exists_congr
    intro n
    exact and_congr Iff.rfl (and_congr (hi n) Iff.rfl)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableObjects
