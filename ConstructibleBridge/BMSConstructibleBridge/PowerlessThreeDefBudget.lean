import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetProvider

/-! # 有限 Class 参数环境的真实三次 Def 预算

背景为原 Z₂ 图商。规范预算的第三有限尾实际产生非零极限母层 C₀，
以及 C₁=Def(C₀)、C₂=Def(C₁)、目标 C=Def(C₂)。整个有限参数环境与当前
阶段在 C₀ 中；严格较早指标的预算层对象也真正属于 C₀。

证书不含前史、覆盖、Class 图或枚举字段；实际预算图可以留 raw，
不从其自身存在推出 Class 身份。共同起点及规范预算图的存在由既有
内部编码接口提供，后续实际内部归纳消费本证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessThreeDefBudget

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

structure spec_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) (B A Q : type_l hℳ) : Prop where
  domain_ordinal : Ordinal A
  source : ∀ a δ, value_l (ℳ := 𝒱) Q a δ → mem_l hℳ a A
  total : ∀ a, mem_l hℳ a A → ∃ δ, value_l (ℳ := 𝒱) Q a δ
  output_ordinal : ∀ a δ, value_l (ℳ := 𝒱) Q a δ → Ordinal δ
  layers : ∀ a δ C, value_l (ℳ := 𝒱) Q a δ →
    PowerlessRelativeHierarchySemantics.level_l hℳ B δ C →
      ∃ ξ C₀ C₁ C₂, PowerlessRelativeHierarchySemantics.limit_l hℳ ξ ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ B ξ C₀ ∧
        SecondOrderMemberDef.spec_l hℳ C₀ C₁ ∧ SecondOrderMemberDef.spec_l hℳ C₁ C₂ ∧
        SecondOrderMemberDef.spec_l hℳ C₂ C ∧
        (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C₀) ∧ mem_l hℳ a C₀ ∧
        ∀ b, mem_l hℳ b a → ∀ θ E, value_l (ℳ := 𝒱) Q b θ →
          PowerlessRelativeHierarchySemantics.level_l hℳ B θ E → mem_l hℳ E C₀

/-- 尾宽实际为三；不将旧两次 Def 的字段重复用作本证书。 -/
theorem of_tail_l {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) {B ξ Cstart Q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (A : SecondOrderGraph.code_l ℳ) (hA : Ordinal (mk_l hℳ A))
    {S Q₀ D₀ R G : SecondOrderModel.set_l ℳ} {r : SecondOrderModel.num_l ℳ}
    (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (hQ : ∀ i j, SecondOrderPairing.relation_l Q₀ i j ↔
      SecondOrderBisimulation.eq_l A.real A.real i j)
    (hD : SecondOrderRootRepresentatives.spec_l A.real Q₀ D₀ A.root)
    (hRel : SecondOrderRootOrdinalRelation.spec_l A.real Q₀ D₀ R)
    (hG : SecondOrderOrdinalBudgetGraph.spec_l S r R G)
    (hStartEq : SecondOrderOrdinalBudgetOrder.base_l hℳ hS r = ξ)
    (hStartLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ ξ)
    (hStartLevel : PowerlessRelativeHierarchySemantics.level_l hℳ B ξ Cstart)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) Cstart)
    (hAStart : mem_l hℳ (mk_l hℳ A) Cstart)
    (hReadQ : ∀ x y, value_l (ℳ := 𝒱) Q x y ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D₀, x =
        SecondOrderOrdinalBudgetFunction.index_l hℳ A hD n hn ∧ y =
        SecondOrderOrdinalBudgetOrder.tail_l hℳ hG hS
          (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n
          (SecondOrderModel.succ_l (SecondOrderModel.succ_l
            (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))))) :
    spec_l hℳ η B (mk_l hℳ A) Q := by
  let z := SecondOrderModel.zero_l ℳ
  let o := SecondOrderModel.succ_l z
  let t := SecondOrderModel.succ_l o
  let k := SecondOrderModel.succ_l t
  let hR := SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel
  let tail (n m : SecondOrderModel.num_l ℳ) : type_l hℳ :=
    SecondOrderOrdinalBudgetOrder.tail_l hℳ hG hS hR n m
  have hRead x y : value_l (ℳ := 𝒱) Q x y ↔ ∃ n, ∃ hn : SecondOrderModel.mem_l n D₀,
      x = SecondOrderOrdinalBudgetFunction.index_l hℳ A hD n hn ∧ y = tail n k := hReadQ x y
  have hBaseOrd : Ordinal (SecondOrderOrdinalBudgetOrder.base_l hℳ hS r) :=
    hStartEq.symm ▸ PowerlessRelativeLevelClosure.ordinal_l hℳ hStartLevel
  have hBaseLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ
      (SecondOrderOrdinalBudgetOrder.base_l hℳ hS r) := hStartEq.symm ▸ hStartLimit
  have hTailOrd n m (hn : SecondOrderModel.mem_l n D₀) : Ordinal (tail n m) :=
    PowerlessRelativeOrdinalBudgetReading.ordinal_l hℳ A hQ hD hRel hG hS hA hBaseOrd n m hn
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · intro a δ hValue
    obtain ⟨n, hn, ha, _⟩ := (hRead a δ).mp hValue
    exact (SecondOrderOrdinalBudgetFunction.index_covers_l hℳ A hQ hD a).mpr ⟨n, hn, ha⟩
  · intro a ha
    obtain ⟨n, hn, hIndex⟩ := (SecondOrderOrdinalBudgetFunction.index_covers_l hℳ A hQ hD a).mp ha
    exact ⟨tail n k, (hRead a _).mpr ⟨n, hn, hIndex, rfl⟩⟩
  · intro a δ hValue
    obtain ⟨n, hn, _ha, hδ⟩ := (hRead a δ).mp hValue
    exact hδ.symm ▸ hTailOrd n k hn
  · intro a δ C hValue hC
    obtain ⟨n, hn, ha, hδ⟩ := (hRead a δ).mp hValue
    subst δ
    have hLimit := SecondOrderOrdinalBudgetFinite.limit_l hℳ hG hS hR hBaseLimit n
    obtain ⟨C₀, hC₀⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase (hTailOrd n z hn)
    have hStartSubset : ∀ x, mem_l hℳ x Cstart → mem_l hℳ x C₀ :=
      PowerlessHierarchyLightHistoryBudgetProvider.level_subset_l hℳ hBase hStartLevel hC₀
        (fun x hx => SecondOrderOrdinalBudgetFinite.base_subset_l hℳ hG hS hR n z x (hStartEq.symm ▸ hx))
    obtain ⟨δ₁, C₁, hSucc₀₁, hLevel₁, hDef₀₁⟩ :=
      PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC₀
    have hδ₁ : δ₁ = tail n o := PowerlessHierarchyLightHistoryBudgetProvider.successor_eq_l hℳ hSucc₀₁
      (SecondOrderOrdinalBudgetFinite.successor_l hℳ hG hS hR n z)
    have hC₁ : PowerlessRelativeHierarchySemantics.level_l hℳ B (tail n o) C₁ := hδ₁ ▸ hLevel₁
    obtain ⟨δ₂, C₂, hSucc₁₂, hLevel₂, hDef₁₂⟩ :=
      PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC₁
    have hδ₂ : δ₂ = tail n t := PowerlessHierarchyLightHistoryBudgetProvider.successor_eq_l hℳ hSucc₁₂
      (SecondOrderOrdinalBudgetFinite.successor_l hℳ hG hS hR n o)
    have hC₂ : PowerlessRelativeHierarchySemantics.level_l hℳ B (tail n t) C₂ := hδ₂ ▸ hLevel₂
    obtain ⟨δ₃, C₃, hSucc₂₃, hLevel₃, hDef₂₃⟩ :=
      PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC₂
    have hδ₃ : δ₃ = tail n k := PowerlessHierarchyLightHistoryBudgetProvider.successor_eq_l hℳ hSucc₂₃
      (SecondOrderOrdinalBudgetFinite.successor_l hℳ hG hS hR n t)
    have hC₃ : PowerlessRelativeHierarchySemantics.level_l hℳ B (tail n k) C₃ := hδ₃ ▸ hLevel₃
    have hC₃Eq := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hC₃ hC
    have haDomain : mem_l hℳ a (mk_l hℳ A) :=
      (SecondOrderOrdinalBudgetFunction.index_covers_l hℳ A hQ hD a).mpr ⟨n, hn, ha⟩
    have haStart := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hStartLevel
      (mk_l hℳ A) hAStart a haDomain
    refine ⟨tail n z, C₀, C₁, C₂, hLimit, hC₀, hDef₀₁, hDef₁₂, hC₃Eq ▸ hDef₂₃,
      (fun s v => hStartSubset (η.freeVal v) (hParams s v)), hStartSubset a haStart, ?_⟩
    intro b hb θ E hQb hE
    obtain ⟨i, hi, hbi, hθ⟩ := (hRead b θ).mp hQb
    subst θ
    have hIndex : mem_l hℳ (SecondOrderOrdinalBudgetFunction.index_l hℳ A hD i hi)
        (SecondOrderOrdinalBudgetFunction.index_l hℳ A hD n hn) := by
      rw [← hbi, ← ha]
      exact hb
    exact PowerlessRelativeLevelClosure.members_l hℳ hBase
      (PowerlessRelativeOrdinalBudgetReading.earlier_l hℳ A hQ hD hRel hG hS i n hi hn hIndex k z)
      hE hC₀

#print axioms of_tail_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessThreeDefBudget
