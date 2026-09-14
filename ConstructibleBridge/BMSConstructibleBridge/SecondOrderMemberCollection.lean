import BMSConstructibleBridge.SecondOrderMemberFamily
import BMSConstructibleBridge.SecondOrderSubsetExact

/-!
# 实际成员结构的相容子集族及其集合收集

同一内部选择关系同时给出全索引切片、精确的原成员读取和全部源公式覆盖。
收集对象位于原图商解释中；尚不把它认作原内部语法的精确 Def。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollection

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) :
    ∃ F G, ∃ hG : SecondOrderSubsetLayer.spec_l A.real F A.root G,
      ∃ H : SecondOrderGraph.code_l ℳ,
        (∀ B, SecondOrderGraph.mem_l B H ↔
          ∃ i, SecondOrderGraph.eq_l B (SecondOrderSubsetLayer.code_l hℳ A F G hG i)) ∧
        (∀ i n (hn : relation_l A.real n A.root),
          SecondOrderGraph.mem_l (SecondOrderGraph.child_l hℳ A n hn)
            (SecondOrderSubsetLayer.code_l hℳ A F G hG i) ↔ relation_l F i n) ∧
        ∀ (Γ Δ : SortContext ℒ) (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
          (φ : Formula ℒ (.set :: Γ) Δ), ∃ i, ∀ n, relation_l F i n ↔
            Formula.satisfies (η.pushBound (SecondOrderMemberStructure.value_l hℳ A a ha n)) φ := by
  obtain ⟨F, hF, hφ⟩ := SecondOrderMemberFamily.exists_l hℳ A a ha
  obtain ⟨G, hG, H, hH⟩ := SecondOrderSubsetCollection.exists_l hℳ A F
  have h₁ (i n m : num_l ℳ) (hn : relation_l A.real n A.root)
      (hm : relation_l A.real m A.root) (h : SecondOrderBisimulation.eq_l A.real A.real n m) :
      relation_l F i n ↔ relation_l F i m := by
    apply hF i n m
    rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn,
      SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha m hm]
    exact h
  exact ⟨F, G, hG, H, hH, SecondOrderSubsetExact.mem_l hℳ A F G hG h₁, hφ⟩

/-- 源参数定义的子集由同一收集对象中的切片精确表示。 -/
theorem coverage_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) : ∃ H : SecondOrderGraph.code_l ℳ,
      (∀ B, SecondOrderGraph.mem_l B H → ∀ C, SecondOrderGraph.mem_l C B → SecondOrderGraph.mem_l C A) ∧
      ∀ (Γ Δ : SortContext ℒ) (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
        (φ : Formula ℒ (.set :: Γ) Δ), ∃ B, SecondOrderGraph.mem_l B H ∧
          ∀ n (hn : relation_l A.real n A.root),
            SecondOrderGraph.mem_l (SecondOrderGraph.child_l hℳ A n hn) B ↔
              Formula.satisfies (η.pushBound (SecondOrderMemberStructure.value_l hℳ A a ha n)) φ := by
  obtain ⟨F, G, hG, H, hH, hF, hφ⟩ := exists_l hℳ A a ha
  refine ⟨H, ?_, ?_⟩
  · intro B hB C hC
    obtain ⟨i, hi⟩ := (hH B).mp hB
    exact SecondOrderSubsetLayer.subset_l hℳ A F G hG i C
      ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) hi).mp hC)
  · intro Γ Δ η φ
    obtain ⟨i, hi⟩ := hφ Γ Δ η φ
    exact ⟨SecondOrderSubsetLayer.code_l hℳ A F G hG i,
      (hH _).mpr ⟨i, SecondOrderGraph.refl_l hℳ _⟩, fun n hn => (hF i n hn).trans (hi n)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberCollection
