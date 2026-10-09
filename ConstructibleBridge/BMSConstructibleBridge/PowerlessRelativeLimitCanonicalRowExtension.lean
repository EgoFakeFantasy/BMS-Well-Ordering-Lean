import BMSConstructibleBridge.SecondOrderRowOrderCanonical
import BMSConstructibleBridge.PowerlessRelativeLimitRowFamilyClosure
import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.SecondOrderWellOrderEndExtensionUnique

/-! # 指定非零极限层内的规范行序与末端扩张

六个实际 Class 参数均已属于同一真实层 C。先取得实际行族及其环境良序，
以全部 raw 行规格将行族收回 C，再在 C 内重新分离完全相同的规范序图。
待扩张载体 D 的行覆盖只用于把该良序限制到 D；此局部覆盖输入必须由
后续原 Def 认同提供，不是最终定理中已经消去的条件。

扩张图直接在 D×D 上作层内 Δ₀ 分离，逐成员排除垃圾。所有行对象、
比较坐标和良序子集量词保留原商范围，不从任意子集关系推出 Class 身份，
不要求可数性、Collection 或统一历史族。这里仍是原对象推导的语义辅助。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalRowExtension

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β C : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 全部行族、规范比较图和末端扩张图同时留在原指定层。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (I U A Q P D : type_l hℳ B)
    (hIC : mem_l hℳ I.val C) (hUC : mem_l hℳ U.val C)
    (hAC : mem_l hℳ A.val C) (hQC : mem_l hℳ Q.val C)
    (hPC : mem_l hℳ P.val C) (hDC : mem_l hℳ D.val C)
    (hU : wellOrder_l (ℳ := 𝒱) I.val U.val)
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hCover : ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x D.val →
      ∃ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ∧
        PowerlessRelativeClassRowFamily.row_l (ℳ₀ := 𝒱) A.val Q.val i x) :
    ∃ Y L E : type_l hℳ B,
      mem_l hℳ Y.val C ∧ mem_l hℳ L.val C ∧ mem_l hℳ E.val C ∧
      PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒱) I.val A.val Q.val Y.val ∧
      PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱)
        I.val U.val A.val Q.val Y.val L.val ∧ wellOrder_l (ℳ := 𝒱) Y.val L.val ∧
      SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱)
        A.val D.val P.val L.val E.val ∧ wellOrder_l (ℳ := 𝒱) D.val E.val := by
  obtain ⟨Y, L, hFamily, hGraph, hOrder⟩ :=
    PowerlessRelativeClassRowOrderCanonical.exists_l (hBase := hBase) I A Q U hU
  have hFamilyRaw := SecondOrderRowOrderCanonical.family_ambient_l (hBase := hBase) hFamily
  have hYC : mem_l hℳ Y.val C := PowerlessRelativeLimitRowFamilyClosure.member_l
    hBase hLimit hC hIC hAC hQC hFamilyRaw
  -- 只重新构造同一规范图，随后用完整图唯一性认同原 Class 对象。
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassRowOrderCanonical.comparison_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree Q.val).pushFree A.val).pushFree U.val).pushFree I.val
  have hParams : ∀ s (v : Variable
      [SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (η.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hIC
    | there v => cases v with
      | here => exact hUC
      | there v => cases v with
        | here => exact hAC
        | there v => cases v with
          | here => exact hQC
          | there v => nomatch v
  obtain ⟨L₀, hL₀C, hL₀⟩ := PowerlessRelativeLimitRelationalGraph.exists_member_l
    hBase hLimit hC (φ := φ)
      (PowerlessRelativeClassRowOrderCanonical.comparison_delta_l _ _ _ _ _ _) η hYC hYC hParams
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔
      PowerlessRelativeClassRowOrderCanonical.comparison_l (ℳ₀ := 𝒱)
        I.val U.val A.val Q.val x y :=
    PowerlessRelativeClassRowOrderCanonical.comparison_formula_l _ _ _ _ _ _ _
  have hGraph₀ : PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱)
      I.val U.val A.val Q.val Y.val L₀ := by
    intro p
    exact (hL₀ p).trans (exists_congr fun x => exists_congr fun y =>
      and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (hφ x y))))
  have hL₀Eq : L₀ = L.val := PowerlessRelativeClassRowOrderCanonical.graph_unique_l hGraph₀ hGraph
  have hLC : mem_l hℳ L.val C := hL₀Eq ▸ hL₀C
  have hDY : subset_l (ℳ := 𝒱) D.val Y.val :=
    fun x hx => (hFamilyRaw x).mpr (hCover x hx)
  have hDOrder : wellOrder_l (ℳ := 𝒱) D.val L.val :=
    PowerlessRelativeClassAmbientWellOrder.of_subset_l hOrder hDY
  -- D×D 上的同层分离直接给出干净扩张图，参数中没有 C 本身。
  let ψ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    SecondOrderWellOrderEndExtension.body_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let ξ : Env 𝒱 [] [.set, .set, .set] :=
    ((Env.empty.pushFree L.val).pushFree P.val).pushFree A.val
  have hParams' : ∀ s (v : Variable
      [SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (ξ.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hAC
    | there v => cases v with
      | here => exact hPC
      | there v => cases v with
        | here => exact hLC
        | there v => nomatch v
  obtain ⟨E₀, hE₀C, hE₀⟩ := PowerlessRelativeLimitRelationalGraph.exists_member_l
    hBase hLimit hC (φ := ψ) (SecondOrderWellOrderEndExtension.body_delta_l _ _ _ _ _)
      ξ hDC hDC hParams'
  have hψ x y : ψ.satisfies ((ξ.pushFree y).pushFree x) ↔
      SecondOrderWellOrderEndExtension.body_l (ℳ₀ := 𝒱) A.val P.val L.val x y :=
    SecondOrderWellOrderEndExtension.body_formula_l _ _ _ _ _ _
  have hEGraph : SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱)
      A.val D.val P.val L.val E₀ := by
    intro p
    refine (hE₀ p).trans ?_
    constructor
    · rintro ⟨x, y, hx, hy, hPair, hBody⟩
      exact ⟨x, y, hx, hy, (hψ x y).mp hBody, hPair⟩
    · rintro ⟨x, y, hx, hy, hBody, hPair⟩
      exact ⟨x, y, hx, hy, hPair, (hψ x y).mpr hBody⟩
  have hEOrder : wellOrder_l (ℳ := 𝒱) D.val E₀ :=
    SecondOrderWellOrderEndExtension.of_graph_l hP hDOrder
      (SecondOrderWellOrderEndExtensionUnique.reading_l hEGraph)
  let E : type_l hℳ B := ⟨E₀, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hC) hE₀C⟩
  exact ⟨Y, L, E, hYC, hLC, hE₀C, hFamilyRaw, hGraph, hOrder, hEGraph, hEOrder⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalRowExtension
