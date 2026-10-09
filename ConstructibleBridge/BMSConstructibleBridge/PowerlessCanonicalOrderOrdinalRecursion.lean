import BMSConstructibleBridge.PowerlessCanonicalOrderOrdinalHistory
import BMSConstructibleBridge.SecondOrderCanonicalOrderComparison
import BMSConstructibleBridge.SecondOrderCanonicalBaseGuard

/-! # 同一原规范历史的序数递归读数

对象语言为纯隶属 ℒ，背景为原 Z₂ 模型及其实际图商。固定同一原数字
历史及其全 raw 重索引读数，恢复零、规范后继和极限的实际集合成员并。
旧编号 J、陪域 q 与序数图 Pord 都仍是 raw 对象，不假设它们属于 Class。

完整成员界显式消费实际种子守卫 hBound；该守卫可由已有
SecondOrderCanonicalBaseGuard.exists_l 的 guard_l 取得，不能从良序逆推。
后继的完整成员图及极限的完整 graph_l 保证当前图干净。极限并集的反向
读数再使用前驱图的成员界，不以 Value 合集代替集合成员并。

这些是后续有界检查器的语义辅助引理，不构造 Class 规范历史、枚举族，
也不宣称 BMS 终局对象推导；没有 Collection、外部良基归纳或选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderOrdinalRecursion

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev zeroCode_l (K : source_coding_l hℳ) :=
  (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

variable {t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q Pord : type_l hℳ}

/-- 由同一旧历史读取当前分支，不重新选择编码或满足关系。 -/
private theorem branch_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    (hRead : PowerlessCanonicalOrderOrdinalHistory.spec_l A I J G Pord)
    {a X P : type_l hℳ} (hFX : value_l (ℳ := 𝒱) F a X)
    (hP : value_l (ℳ := 𝒱) Pord a P) :
    SecondOrderComparisonCanonicalSyntax.branch_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid J T G P₀ a X P := by
  have ha := ((hRead a P).mp hP).1
  obtain ⟨i, hi, hia, hiP⟩ := ((hRead a P).mp hP).2
  exact h.canonical a ha i X P
    ⟨⟨hi, (h.configuration.layerRead i X).mpr ⟨a, hia, hFX⟩, hiP⟩, hia⟩

/-- 当前层的真实极限方程，保留原 F 的全部 raw 值。 -/
private theorem layer_union_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    {a X : type_l hℳ} (hFX : value_l (ℳ := 𝒱) F a X)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ a) :
    PowerlessRelativeHierarchySemantics.union_l hℳ F a X := by
  have ha := (SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.hierarchy.1 hFX).1
  have hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a :=
    SetTheory.Structure.IsOrdinal.mem h.configuration.ordinal ha
  rcases h.configuration.hierarchy.2 a X ⟨ha, hFX⟩ with
    ⟨hEmpty, _⟩ | ⟨b, _, hSucc, _, _⟩ | ⟨_, hUnion⟩
  · obtain ⟨b, hb⟩ := hLimit.1
    exact False.elim (hEmpty b hb)
  · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hSucc hLimit)
  · exact hUnion

/-- 零阶段同时认同原层载体与原完整种子图。 -/
theorem zero_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    (hRead : PowerlessCanonicalOrderOrdinalHistory.spec_l A I J G Pord)
    {a X P : type_l hℳ} (hFX : value_l (ℳ := 𝒱) F a X)
    (hP : value_l (ℳ := 𝒱) Pord a P)
    (hEmpty : PowerlessRelativeHierarchySemantics.empty_l hℳ a) : X = B ∧ P = P₀ := by
  have ha := ((hRead a P).mp hP).1
  have hXB : X = B := by
    rcases h.configuration.hierarchy.2 a X ⟨ha, hFX⟩ with
      ⟨_, hXB⟩ | ⟨b, _, hSucc, _, _⟩ | ⟨hLimit, _⟩
    · exact hXB
    · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc))
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
  refine ⟨hXB, ?_⟩
  rcases branch_l K h hRead hFX hP with
    ⟨_, hPP₀⟩ | ⟨b, _, _, _, hSucc, _⟩ | ⟨hLimit, _⟩
  · exact hPP₀
  · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc))
  · obtain ⟨b, hb⟩ := hLimit.1
    exact False.elim (hEmpty b hb)

/-- 后继输出使用同一原前驱层和同一序数图的前驱值。 -/
theorem successor_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    (hRead : PowerlessCanonicalOrderOrdinalHistory.spec_l A I J G Pord)
    {b a X Q : type_l hℳ} (hFX : value_l (ℳ := 𝒱) F a X)
    (hQ : value_l (ℳ := 𝒱) Pord a Q)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ b a) :
    ∃ Y P, value_l (ℳ := 𝒱) F b Y ∧ value_l (ℳ := 𝒱) Pord b P ∧
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) K.omega Y P (zeroCode_l K)
        t₁ t₂ t₃ Pair Valid X Q := by
  have ha := ((hRead a Q).mp hQ).1
  have hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a :=
    SetTheory.Structure.IsOrdinal.mem h.configuration.ordinal ha
  rcases branch_l K h hRead hFX hQ with
    ⟨hEmpty, _⟩ | ⟨c, j, Y, P, hSucc', hjc, hjY, hjP, hStep⟩ | ⟨hLimit, _⟩
  · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc))
  · have hcb := PowerlessRelativeHierarchyStep.successor_unique_l hℳ hα hSucc' hSucc
    subst c
    obtain ⟨d, hjd, hdY⟩ := (h.configuration.layerRead j Y).mp hjY
    have hdb := SecondOrderFunctionLaws.value_unique_l hℳ h.configuration.indexMap hjd hjc
    have hbY : value_l (ℳ := 𝒱) F b Y := hdb ▸ hdY
    have hj := SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.indexMap hjc
    exact ⟨Y, P, hbY, (hRead b P).mpr ⟨hj.2, j, hj.1, hjc, hjP⟩, hStep⟩
  · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hSucc hLimit)

/-- 实际种子成员界恢复每个实际层上的完整干净关系图。 -/
theorem bounded_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    (hRead : PowerlessCanonicalOrderOrdinalHistory.spec_l A I J G Pord)
    (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p)
    {a X P : type_l hℳ} (hFX : value_l (ℳ := 𝒱) F a X)
    (hP : value_l (ℳ := 𝒱) Pord a P) :
    ∀ p, mem_l hℳ p P → ∃ x y,
      mem_l hℳ x X ∧ mem_l hℳ y X ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
  rcases branch_l K h hRead hFX hP with
    ⟨hEmpty, hPP₀⟩ | ⟨_, _, _, _, _, _, _, _, hStep⟩ | ⟨hLimit, D, hD, hGraph⟩
  · have hXB := (zero_l K h hRead hFX hP hEmpty).1
    intro p hp
    obtain ⟨x, y, hx, hy, hxy⟩ := hBound p (hPP₀ ▸ hp)
    exact ⟨x, y, hXB.symm ▸ hx, hXB.symm ▸ hy, hxy⟩
  · exact SecondOrderCanonicalOrderComparison.bounded_l (C := X) hStep (fun _ hx => hx)
  · have hUnion := layer_union_l K h hFX hLimit
    intro p hp
    obtain ⟨x, y, ⟨i, Y, R, hi, hx, hy, _⟩, hxy⟩ := (hGraph p).mp hp
    obtain ⟨b, hib, hb⟩ := (hD i).mp hi.1
    obtain ⟨c, hic, hcY⟩ := (h.configuration.layerRead i Y).mp hi.2.1
    have hcb := SecondOrderFunctionLaws.value_unique_l hℳ h.configuration.indexMap hic hib
    have hbY : value_l (ℳ := 𝒱) F b Y := hcb ▸ hcY
    exact ⟨x, y, (hUnion x).mpr ⟨b, Y, hb, hbY, hx⟩,
      (hUnion y).mpr ⟨b, Y, hb, hbY, hy⟩, hxy⟩

/-- 极限值是全部前驱关系对象的真实成员并，量化所有 raw 成员。 -/
theorem limit_l (K : source_coding_l hℳ)
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zeroCode_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T G q)
    (hRead : PowerlessCanonicalOrderOrdinalHistory.spec_l A I J G Pord)
    (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p)
    {a Q : type_l hℳ} (hQ : value_l (ℳ := 𝒱) Pord a Q)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ a) :
    PowerlessRelativeHierarchySemantics.union_l hℳ Pord a Q := by
  have ha := ((hRead a Q).mp hQ).1
  have hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a :=
    SetTheory.Structure.IsOrdinal.mem h.configuration.ordinal ha
  obtain ⟨X, ⟨_, hFX⟩, _⟩ := h.configuration.hierarchy.1.2 a ha
  rcases branch_l K h hRead hFX hQ with
    ⟨hEmpty, _⟩ | ⟨b, _, _, _, hSucc, _⟩ | ⟨_, D, hD, hGraph⟩
  · obtain ⟨b, hb⟩ := hLimit.1
    exact False.elim (hEmpty b hb)
  · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ hα hSucc hLimit)
  · intro p
    constructor
    · intro hp
      obtain ⟨x, y, ⟨i, Y, R, hi, _, _, hxy⟩, hPair⟩ := (hGraph p).mp hp
      obtain ⟨b, hib, hb⟩ := (hD i).mp hi.1
      have hiA := SecondOrderFunctionLaws.value_mem_l hℳ h.configuration.indexMap hib
      have hbR : value_l (ℳ := 𝒱) Pord b R :=
        (hRead b R).mpr ⟨hiA.2, i, hiA.1, hib, hi.2.2⟩
      obtain ⟨s, hs, hsPair⟩ := hxy
      have hsp := SecondOrderPairObjects.ordered_unique_l hℳ hsPair hPair
      exact ⟨b, R, hb, hbR, hsp ▸ hs⟩
    · rintro ⟨b, R, hb, hbR, hpR⟩
      have hbA := ((hRead b R).mp hbR).1
      obtain ⟨i, _, hib, hiR⟩ := ((hRead b R).mp hbR).2
      obtain ⟨Y, ⟨_, hbY⟩, _⟩ := h.configuration.hierarchy.1.2 b hbA
      have hiY := (h.configuration.layerRead i Y).mpr ⟨b, hib, hbY⟩
      obtain ⟨x, y, hx, hy, hPair⟩ := bounded_l K h hRead hBound hbY hbR p hpR
      have hxy : value_l (ℳ := 𝒱) R x y := ⟨p, hpR, hPair⟩
      exact (hGraph p).mpr ⟨x, y,
        ⟨i, Y, R, ⟨(hD i).mpr ⟨b, hib, hb⟩, hiY, hiR⟩, hx, hy, hxy⟩, hPair⟩

#print axioms zero_l
#print axioms successor_l
#print axioms bounded_l
#print axioms limit_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderOrdinalRecursion
