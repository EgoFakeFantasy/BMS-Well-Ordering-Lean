import BMSConstructibleBridge.PowerlessCanonicalOrderBudgetClass

/-! # 实际层历史上的同一规范比较 Class 图

原数字递归先产生 raw 比较历史，实际序数重索引保留其全部输出。
零／后继／极限方程和父序全部从该原历史取得，再用真实三尾预算归纳
证明同一重索引图属于 Class。这里不预设原 raw 陪域或编号图属于 Class，
不宣称统一枚举族或比较图属于层 W。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderClassHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

private abbrev zero_l (K : source_coding_l hℳ) :=
  (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem equations_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid P₀ A F r I J T H q Pord : Raw}
    (h : SecondOrderCanonicalLevelSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid B P₀ A F r I J T H q)
    (hRead : PowerlessCanonicalOrderOrdinalHistory.spec_l A I J H Pord)
    (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p) :
    PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁ t₂ t₃ Pair Valid B P₀ F Pord := by
  intro a X P hX hP
  have ha := (SecondOrderFunctionProperties.value_mem_l hℳ h.configuration.hierarchy.1 hX).1
  rcases h.configuration.hierarchy.2 a X ⟨ha, hX⟩ with
    ⟨hEmpty, _⟩ | ⟨b, _Y, hSucc, _hY, _hDef⟩ | ⟨hLimit, hUnion⟩
  · exact Or.inl ⟨hEmpty, PowerlessCanonicalOrderOrdinalRecursion.zero_l K h hRead hX hP hEmpty⟩
  · obtain ⟨Y, Q, hY, hQ, hStep⟩ :=
      PowerlessCanonicalOrderOrdinalRecursion.successor_l K h hRead hX hP hSucc
    exact Or.inr (Or.inl ⟨b, Y, Q, hSucc, hY, hQ, hStep⟩)
  · exact Or.inr (Or.inr ⟨hLimit, hUnion,
      PowerlessCanonicalOrderOrdinalRecursion.limit_l K h hRead hBound hP hLimit⟩)

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {δ : Raw}
    (W F P₀ ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W.val)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hδ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) δ)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F.val W.val)
    (hB : ∃ b, mem_l hℳ b B)
    (hSeed : wellOrder_l (ℳ := 𝒱) B P₀.val)
    (hBound : ∀ p, mem_l hℳ p P₀.val → ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p) :
    ∃ Pord : type_l hℳ B, ∃ q : Raw, map_l (ℳ := 𝒱) Pord.val δ q ∧
      PowerlessCanonicalOrderOrdinalRestriction.equations_l K
        t₁.val t₂.val t₃.val Pair.val Valid.val B P₀.val F.val Pord.val ∧
      ∀ a X P, value_l (ℳ := 𝒱) F.val a X →
        (value_l (ℳ := 𝒱) Pord.val a P ↔ SecondOrderCanonicalLevelSyntax.level_l
          K.omega (zero_l K) t₁.val t₂.val t₃.val Pair.val Valid.val B P₀.val a X P) := by
  obtain ⟨_he, ht₁, ht₂, ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hCode.omega_eq hCode.static
  obtain ⟨V, hV, _hUnique⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hCoding : SecondOrderComparisonStageTotal.coding_l K t₁.val t₂.val t₃.val Pair.val Valid.val :=
    ⟨ht₁, ht₂, ht₃, hPairMap, hPair, V, hV, hValid V hV⟩
  obtain ⟨I, J, T, H, q, hHistory⟩ :=
    SecondOrderCanonicalLevel.history_exists_l K hCoding hB hBase hSeed hBound hδ hF
  obtain ⟨Pord, hMap, hRead, hLevel, _hCanonical⟩ :=
    PowerlessCanonicalOrderOrdinalHistory.exists_l K hCoding hHistory
  have hEq := equations_l K hHistory hRead hBound
  have hOrder a X P (hX : value_l (ℳ := 𝒱) F.val a X)
      (hP : value_l (ℳ := 𝒱) Pord a P) : wellOrder_l (ℳ := 𝒱) X P :=
    SecondOrderCanonicalLevel.order_l ((hLevel a X P hX).mp hP)
  have hClass := PowerlessCanonicalOrderBudgetClass.class_l hBase K
    W F P₀ ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hδ hF hMap hEq hOrder
  exact ⟨⟨Pord, hClass⟩, q, hMap, hEq, hLevel⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderClassHistory
