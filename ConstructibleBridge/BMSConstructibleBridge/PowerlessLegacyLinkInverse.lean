import BMSConstructibleBridge.PowerlessLegacyAssignmentSyntax
import BMSConstructibleBridge.SecondOrderMemberFiniteFunctionAssignment
import BMSConstructibleBridge.SecondOrderFunctionRestriction

/-! # 实际有限赋值到原反转填充 link 的逆向表示

先限制实际 raw 函数到参数前缀，用原成员呈现的内部最小代表编码该有限
函数，再反转参数码。常值尾部沿同一规范枚举取得数值代表，因此恢复原
link 的全部内部数及全部 raw 输出读数。f 与 U 均不要求属于 Class。

非严格长度守卫写成等号或原内部严格序，即模型内部的 l≤L；不以外部
列表或标准有限性代替非标准长度。所有见证留在 Prop，也不新增 Type
选择。本接口只是受限翻译像行族的前置，不直接证明任意 Class 的原 Def
闭包，不构造反向公式编译或终局对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyLinkInverse

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)
open SecondOrderModel (num_l set_l)
open SecondOrderSequenceSyntax (read_l)
open SecondOrderLegacyAssignmentReversal (index_l reversed_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 规范枚举的全 raw 读数已足够，不另加 U 的 Class、映射或满射前提。 -/
theorem inverse_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : SecondOrderPairing.relation_l A.real a A.root)
    {E : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    {U f : SecondOrderQuotient.type_l hℳ} {l L : num_l ℳ}
    (hNumber : ∀ n y, value_l (ℳ := RawModel) U (numberCode_l K n).val y ↔
      y = (SecondOrderMemberStructure.value_l hℳ A a ha n).val)
    (hf : map_l (ℳ := RawModel) f (numberCode_l K L).val (mk_l hℳ A))
    (hLength : l = L ∨ SecondOrderOrder.lt_l l L)
    (hTail : ∃ b, mem_l hℳ b (mk_l hℳ A) ∧ ∀ i,
      SecondOrderOrder.lt_l i L → ¬SecondOrderOrder.lt_l i l →
        value_l (ℳ := RawModel) f (numberCode_l K i).val b) :
    ∃ c z, SecondOrderAssignmentSyntax.valid_l E c l ∧
      PowerlessLegacyAssignmentSyntax.link_l K E c l L z U f := by
  classical
  have hfRaw : SecondOrderFunctionObjects.map_l hℳ f
      (numberCode_l K L).val (mk_l hℳ A) := hf
  have hDomain : ∀ x, mem_l hℳ x (numberCode_l K l).val →
      mem_l hℳ x (numberCode_l K L).val := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := SecondOrderFiniteEnumerationRoots.member_number_l K l x hx
    have hiL : SecondOrderOrder.lt_l i L := hLength.elim
      (fun h => h ▸ hi) (fun h => SecondOrderOrder.trans_l hℳ hi h)
    exact hix ▸ (numberCode_mem_iff_lt_l K i L).mpr hiL
  obtain ⟨g, hg, hRestrict⟩ := SecondOrderFunctionRestriction.exists_l hℳ hfRaw hDomain
  obtain ⟨d, hd, hEncode⟩ := SecondOrderMemberFiniteFunctionAssignment.exists_l
    K A a ha hE l hg (fun y hy => hy)
  obtain ⟨c, hc, hReverse⟩ := SecondOrderLegacyAssignmentReversal.exists_l hℳ hE hd
  have hDouble (i j : num_l ℳ) : reversed_l E c l i j ↔ read_l E d i j := by
    constructor
    · rintro ⟨r, hri, hrj⟩
      obtain ⟨s, hsr, hsj⟩ := (hReverse r j).mp hrj
      have hsi : s = i := SecondOrderLegacyAssignmentReversal.unique_l hℳ
        ((SecondOrderLegacyAssignmentReversal.symmetric_l hℳ l s r).mp hsr) hri
      subst s
      exact hsj
    · intro hij
      obtain ⟨r, hir, _⟩ := SecondOrderLegacyAssignmentReversal.index_exists_l hℳ (hd.2 i j hij)
      exact ⟨r, (SecondOrderLegacyAssignmentReversal.symmetric_l hℳ l i r).mp hir,
        (hReverse r j).mpr ⟨i, hir, hij⟩⟩
  have hPrefix (i j : num_l ℳ) (hij : read_l E d i j) :
      value_l (ℳ := RawModel) f (numberCode_l K i).val
        (SecondOrderMemberStructure.value_l hℳ A a ha j).val :=
    ((hRestrict _ _).mp (hEncode i j hij)).2
  obtain ⟨b, hb, hTailValue⟩ := hTail
  obtain ⟨z, hz⟩ := SecondOrderMemberStructure.surjective_l hℳ A a ha ⟨b, hb⟩
  have hZ : value_l (ℳ := RawModel) U (numberCode_l K z).val b :=
    (hNumber z b).mpr (congrArg Subtype.val hz).symm
  refine ⟨c, z, hc, ?_⟩
  intro i y
  constructor
  · intro hValue
    have hiL := (numberCode_mem_iff_lt_l K i L).mp
      (SecondOrderFunctionProperties.value_mem_l hℳ hfRaw hValue).1
    by_cases hi : SecondOrderOrder.lt_l i l
    · obtain ⟨j, hij, _⟩ := hd.1 i hi
      have hy : y = (SecondOrderMemberStructure.value_l hℳ A a ha j).val :=
        SecondOrderFunctionProperties.value_unique_l hℳ hfRaw hValue (hPrefix i j hij)
      exact ⟨j, ⟨hiL, Or.inl ((hDouble i j).mpr hij)⟩, (hNumber j y).mpr hy⟩
    · have hy : y = b := SecondOrderFunctionProperties.value_unique_l
        hℳ hfRaw hValue (hTailValue i hiL hi)
      exact ⟨z, ⟨hiL, Or.inr ⟨hi, rfl⟩⟩, hy.symm ▸ hZ⟩
  · rintro ⟨j, hPad, hUValue⟩
    rcases hPad.2 with hRev | ⟨hi, hj⟩
    · have hy := (hNumber j y).mp hUValue
      exact hy.symm ▸ hPrefix i j ((hDouble i j).mp hRev)
    · subst j
      have hy : y = b := ((hNumber z y).mp hUValue).trans ((hNumber z b).mp hZ).symm
      exact hy.symm ▸ hTailValue i hPad.1 hi

#print axioms inverse_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyLinkInverse
