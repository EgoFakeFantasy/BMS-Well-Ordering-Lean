import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetInduction
import BMSConstructibleBridge.PowerlessRelativeOrdinalBudgetReading

/-! # 从实际规范尾图构造轻量历史预算证书

背景为原 SecondOrderArithmetic.theory_m 的实际图商。给定固定规范代表域、
原预算尾图和实际尾二函数 F，以及含 B/D/W/指标母集的同一非零极限起点层，
本文件实际构造 BudgetInduction.budget_l 的全部五个字段。

预算输出为 tail(n,2)。每个零尾是非零极限，原层存在性及两次后继层存在
产生 C₀→Def(C₀)→Def²(C₀)。精确后继读数与原商外延性认同有限尾，实际层
唯一性认同给定目标层；较早指标的尾二严格属于当前零尾，故其整个实际
层对象属于 C₀。没有把历史覆盖、Class 历史或 budget_l 本身作为前提。

起点包含于零尾不被误当严格隶属：内部序数三歧性处理相等与严格较早，
反向隶属由原序数非自返性排除。所有参数先在同一起点层，再实际提升。
预算图 F 可以只在 raw 环境中，不要求它属于 Class 或起点层。

全部存在见证留在 Prop，不引入 Collection、可数性、外部良基或 Type 选择。
本文件只提供实际预算证书的语义装配；共同起点及原函数的存在由独立
BudgetExists 消去，最后 Class 长历史和原 Derives 另行封装。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetProvider

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct RawModel)

/-- 同一前驱的两个精确 raw 后继相等；无需额外后继选择。 -/
theorem successor_eq_l {a b c : type_l hℳ}
    (hb : PowerlessRelativeHierarchySemantics.successor_l hℳ a b)
    (hc : PowerlessRelativeHierarchySemantics.successor_l hℳ a c) : b = c :=
  SecondOrderQuotient.ext_l hℳ b c (fun x => (hb x).trans (hc x).symm)

/-- 序数子集读数实际提升层成员，包含相等情形，不假定起点严格较早。 -/
theorem level_subset_l {B ξ δ Cstart C : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hStart : PowerlessRelativeHierarchySemantics.level_l hℳ B ξ Cstart)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B δ C)
    (hSubset : ∀ x, mem_l hℳ x ξ → mem_l hℳ x δ) :
    ∀ x, mem_l hℳ x Cstart → mem_l hℳ x C := by
  have hξ := PowerlessRelativeLevelClosure.ordinal_l hℳ hStart
  have hδ := PowerlessRelativeLevelClosure.ordinal_l hℳ hC
  rcases SecondOrderOrdinalComparison.compare_l hℳ hξ hδ with hEq | hEarlier | hReverse
  · subst δ
    have hLevels : Cstart = C := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hStart hC
    exact fun x hx => hLevels ▸ hx
  · exact PowerlessRelativeLevelClosure.subset_l hℳ hBase hEarlier hStart hC
  · have hSelf : mem_l hℳ δ δ := hSubset δ hReverse
    exact False.elim (hδ.wellOrder.linear.irrefl δ hSelf hSelf)

/-- 固定实际尾二函数的完整预算证书；指标域是实际原码 A 的成员域。 -/
theorem budget_of_tail_l {B D W ξ Cstart F : type_l hℳ}
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
    (hBStart : mem_l hℳ B Cstart) (hDStart : mem_l hℳ D Cstart)
    (hWStart : mem_l hℳ W Cstart) (hAStart : mem_l hℳ (mk_l hℳ A) Cstart)
    (hReadF : ∀ x y, SecondOrderFunctionObjects.value_l hℳ F x y ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D₀, x =
        SecondOrderOrdinalBudgetFunction.index_l hℳ A hD n hn ∧ y =
        SecondOrderOrdinalBudgetOrder.tail_l hℳ hG hS
          (SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel) n
          (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))) :
    PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ B D W (mk_l hℳ A) F := by
  let z := SecondOrderModel.zero_l ℳ
  let o := SecondOrderModel.succ_l z
  let t := SecondOrderModel.succ_l o
  let hR := SecondOrderRootOrdinalRelation.wf_l hℳ A hQ hD hRel
  let tail (n m : SecondOrderModel.num_l ℳ) : type_l hℳ :=
    SecondOrderOrdinalBudgetOrder.tail_l hℳ hG hS hR n m
  have hRead (x y : type_l hℳ) : value_l (ℳ := RawModel) F x y ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D₀,
        x = SecondOrderOrdinalBudgetFunction.index_l hℳ A hD n hn ∧ y = tail n t := hReadF x y
  have hStartOrd : Ordinal ξ := PowerlessRelativeLevelClosure.ordinal_l hℳ hStartLevel
  have hBaseOrd : Ordinal (SecondOrderOrdinalBudgetOrder.base_l hℳ hS r) :=
    hStartEq.symm ▸ hStartOrd
  have hBaseLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ
      (SecondOrderOrdinalBudgetOrder.base_l hℳ hS r) := hStartEq.symm ▸ hStartLimit
  have hTailOrd (n m : SecondOrderModel.num_l ℳ) (hn : SecondOrderModel.mem_l n D₀) :
      Ordinal (tail n m) :=
    PowerlessRelativeOrdinalBudgetReading.ordinal_l hℳ A hQ hD hRel hG hS hA hBaseOrd n m hn
  have hBaseSubset (n m : SecondOrderModel.num_l ℳ) (x : type_l hℳ)
      (hx : mem_l hℳ x ξ) : mem_l hℳ x (tail n m) :=
    SecondOrderOrdinalBudgetFinite.base_subset_l hℳ hG hS hR n m x (hStartEq.symm ▸ hx)
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · intro a δ hValue
    obtain ⟨n, hn, ha, _hδ⟩ := (hRead a δ).mp hValue
    exact (SecondOrderOrdinalBudgetFunction.index_covers_l hℳ A hQ hD a).mpr ⟨n, hn, ha⟩
  · intro a ha
    obtain ⟨n, hn, hIndex⟩ := (SecondOrderOrdinalBudgetFunction.index_covers_l hℳ A hQ hD a).mp ha
    exact ⟨tail n t, (hRead a _).mpr ⟨n, hn, hIndex, rfl⟩⟩
  · intro a δ hValue
    obtain ⟨n, hn, _ha, hδ⟩ := (hRead a δ).mp hValue
    exact hδ.symm ▸ hTailOrd n t hn
  · intro a δ C hValue hC
    obtain ⟨n, hn, ha, hδ⟩ := (hRead a δ).mp hValue
    subst δ
    have hTailLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (tail n z) :=
      SecondOrderOrdinalBudgetFinite.limit_l hℳ hG hS hR hBaseLimit n
    obtain ⟨C₀, hC₀⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase (hTailOrd n z hn)
    have hStartSubset : ∀ x, mem_l hℳ x Cstart → mem_l hℳ x C₀ :=
      level_subset_l hℳ hBase hStartLevel hC₀ (hBaseSubset n z)
    obtain ⟨δ₁, C₁, hSucc₀₁, hLevel₁, hDef₀₁⟩ :=
      PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC₀
    have hTailSucc₀₁ : PowerlessRelativeHierarchySemantics.successor_l hℳ (tail n z) (tail n o) :=
      SecondOrderOrdinalBudgetFinite.successor_l hℳ hG hS hR n z
    have hδ₁ : δ₁ = tail n o := successor_eq_l hℳ hSucc₀₁ hTailSucc₀₁
    have hC₁ : PowerlessRelativeHierarchySemantics.level_l hℳ B (tail n o) C₁ := hδ₁ ▸ hLevel₁
    obtain ⟨δ₂, C₂, hSucc₁₂, hLevel₂, hDef₁₂⟩ :=
      PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC₁
    have hTailSucc₁₂ : PowerlessRelativeHierarchySemantics.successor_l hℳ (tail n o) (tail n t) :=
      SecondOrderOrdinalBudgetFinite.successor_l hℳ hG hS hR n o
    have hδ₂ : δ₂ = tail n t := successor_eq_l hℳ hSucc₁₂ hTailSucc₁₂
    have hC₂ : PowerlessRelativeHierarchySemantics.level_l hℳ B (tail n t) C₂ := hδ₂ ▸ hLevel₂
    have hC₂Eq : C₂ = C := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hC₂ hC
    have haDomain : mem_l hℳ a (mk_l hℳ A) :=
      (SecondOrderOrdinalBudgetFunction.index_covers_l hℳ A hQ hD a).mpr ⟨n, hn, ha⟩
    have haStart : mem_l hℳ a Cstart :=
      PowerlessRelativeLevelClosure.transitive_l hℳ hBase hStartLevel
        (mk_l hℳ A) hAStart a haDomain
    refine ⟨tail n z, C₀, C₁, hTailLimit, hC₀, hDef₀₁, hC₂Eq ▸ hDef₁₂,
      hStartSubset B hBStart, hStartSubset D hDStart, hStartSubset W hWStart,
      hStartSubset a haStart, ?_⟩
    intro b hb θ E hQb hE
    obtain ⟨i, hi, hbi, hθ⟩ := (hRead b θ).mp hQb
    subst θ
    have hIndex : mem_l hℳ (SecondOrderOrdinalBudgetFunction.index_l hℳ A hD i hi)
        (SecondOrderOrdinalBudgetFunction.index_l hℳ A hD n hn) := by
      rw [← hbi, ← ha]
      exact hb
    have hTailEarlier : mem_l hℳ (tail i t) (tail n z) :=
      PowerlessRelativeOrdinalBudgetReading.earlier_l hℳ A hQ hD hRel hG hS i n hi hn hIndex t z
    exact PowerlessRelativeLevelClosure.members_l hℳ hBase hTailEarlier hE hC₀

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetProvider
