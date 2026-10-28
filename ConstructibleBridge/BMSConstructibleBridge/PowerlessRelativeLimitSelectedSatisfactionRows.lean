import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeLimitRowFamilyClosure

/-! # 旧翻译像的受限 Sat 行族：指定层内查询与两步 Def 界

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。查询参数
和实际索引 J 均已属于指定非零极限层 W。纯 Δ₀ 查询图在 W 内重新构造，
然后用精确行族的有限界取得 Y∈Def(Def(W))；已有全 raw 行像证书的对象
还可经早共同层回收留在 W。查询不需要 Sat 正确性；
原 Def 行的识别另消费旧翻译、赋值常值尾及求值保持性的真实证书。

全部指标、元素和行对象均量化全部 raw 商。既不缩小为 Class 量词，
也不从任意子集推断 Class。参数在 W 内及两步原 Def 见证是明确输入；
本语义层界不构造长前史、统一枚举或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSelectedSatisfactionRows

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)
open PowerlessRelativeClassSatisfactionAllSlots (query_m query_l query_delta_l query_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 查询图直接重建在 W 内，不与可能含垃圾成员的已有图作对象相等比较。 -/
theorem query_exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {β W : SecondOrderQuotient.type_l hℳ}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω A S Idx Sat J : type_l hℳ B)
    (hωW : mem_l hℳ ω.val W) (hAW : mem_l hℳ A.val W)
    (hSW : mem_l hℳ S.val W) (hIdxW : mem_l hℳ Idx.val W)
    (hSatW : mem_l hℳ Sat.val W) (hJW : mem_l hℳ J.val W) :
    ∃ Q : type_l hℳ B, mem_l hℳ Q.val W ∧
      ∀ t x : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := RawModel) Q.val t x ↔ mem_l hℳ t J.val ∧ mem_l hℳ x A.val ∧
          query_l (ℳ₀ := RawModel) ω.val A.val S.val Idx.val Sat.val t x := by
  let η : Env RawModel [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree Sat.val).pushFree Idx.val).pushFree S.val).pushFree A.val).pushFree ω.val
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    query_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, .set, .set, .set, .set] s),
      mem_l hℳ (η.freeVal v) W := by
    intro s v
    cases s
    match v with
    | .here => exact hωW
    | .there .here => exact hAW
    | .there (.there .here) => exact hSW
    | .there (.there (.there .here)) => exact hIdxW
    | .there (.there (.there (.there .here))) => exact hSatW
  obtain ⟨q, hqW, hq⟩ := PowerlessRelativeLimitRelationalGraph.exists_l
    hBase hLimit hW (φ := φ) (query_delta_l _ _ _ _ _ _ _) η hJW hAW hParams
  let Q : type_l hℳ B := ⟨q, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hW) hqW⟩
  refine ⟨Q, hqW, fun t x => (hq t x).trans ?_⟩
  exact and_congr Iff.rfl (and_congr Iff.rfl (query_formula_l _ _ _ _ _ _ _ _))

/-- 行族整体的界是两次 Def 输出 E，不把它声称为已经属于 W。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {β W D E : SecondOrderQuotient.type_l hℳ}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hCD : SecondOrderMemberDef.spec_l hℳ W D) (hDE : SecondOrderMemberDef.spec_l hℳ D E)
    (ω A S Idx Sat J : type_l hℳ B)
    (hωW : mem_l hℳ ω.val W) (hAW : mem_l hℳ A.val W)
    (hSW : mem_l hℳ S.val W) (hIdxW : mem_l hℳ Idx.val W)
    (hSatW : mem_l hℳ Sat.val W) (hJW : mem_l hℳ J.val W) :
    ∃ Y : type_l hℳ B, mem_l hℳ Y.val E ∧
      ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y.val ↔
        ∃ t : SecondOrderQuotient.type_l hℳ, mem_l hℳ t J.val ∧
          ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x Z ↔
            mem_l hℳ x A.val ∧ query_l (ℳ₀ := RawModel) ω.val A.val S.val Idx.val Sat.val t x := by
  obtain ⟨Q, hQW, hQ⟩ := query_exists_l hBase hLimit hW ω A S Idx Sat J
    hωW hAW hSW hIdxW hSatW hJW
  obtain ⟨Y, hYE, hY⟩ := PowerlessRelativeLimitRowFamilyBounded.exists_l
    hBase hW hCD hDE J A Q hJW hAW hQW
  refine ⟨Y, hYE, fun Z => (hY Z).trans ?_⟩
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  apply forall_congr'
  intro x
  apply iff_congr Iff.rfl
  apply and_congr_right
  intro hx
  exact (hQ t x).trans ⟨fun h => h.2.2, fun h => ⟨ht, hx, h⟩⟩

/-- 给定对象的精确行像留在原 W；不把 Def²W 的界误报为 W 成员性。 -/
theorem member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {β W Y : SecondOrderQuotient.type_l hℳ}
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (ω A S Idx Sat J : type_l hℳ B)
    (hωW : mem_l hℳ ω.val W) (hAW : mem_l hℳ A.val W)
    (hSW : mem_l hℳ S.val W) (hIdxW : mem_l hℳ Idx.val W)
    (hSatW : mem_l hℳ Sat.val W) (hJW : mem_l hℳ J.val W)
    (hY : ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y ↔
      ∃ t : SecondOrderQuotient.type_l hℳ, mem_l hℳ t J.val ∧
        ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x Z ↔
          mem_l hℳ x A.val ∧ query_l (ℳ₀ := RawModel) ω.val A.val S.val Idx.val Sat.val t x) :
    mem_l hℳ Y W := by
  obtain ⟨Q, hQW, hQ⟩ := query_exists_l hBase hLimit hW ω A S Idx Sat J
    hωW hAW hSW hIdxW hSatW hJW
  apply PowerlessRelativeLimitRowFamilyClosure.member_l hBase hLimit hW hJW hAW hQW
  intro Z
  refine (hY Z).trans ?_
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  apply forall_congr'
  intro x
  apply iff_congr Iff.rfl
  apply and_congr_right
  intro hx
  exact ((hQ t x).trans ⟨fun h => h.2.2, fun h => ⟨ht, hx, h⟩⟩).symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSelectedSatisfactionRows
