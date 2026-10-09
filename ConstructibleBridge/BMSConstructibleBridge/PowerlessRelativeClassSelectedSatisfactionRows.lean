import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.PowerlessRelativeClassRowFamilyAmbient

/-! # 实际受限指标上的 Sat 精确行族

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。给定实际
Class 指标集 J，仅对 J 的成员取行，不把查询失败的类外指标也纳入行族。
统一查询图与行族均实际构造，并保留全部 raw 指标、元素及行对象读数。

本接口不要求母集可数或带良序；也不直接把这些 Sat 行认作原 Def。原四
标签代码翻译像及常值尾条件由调用者的实际 J 筛选和双向原行读数取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSelectedSatisfactionRows

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSatisfactionAllSlots (query_m query_l query_delta_l query_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

include hBase in
theorem exists_l (ω A S I R J : type_l hℳ B) :
    ∃ Y : type_l hℳ B, ∀ Z : SecondOrderQuotient.type_l hℳ, mem_l hℳ Z Y.val ↔
      ∃ t : SecondOrderQuotient.type_l hℳ, mem_l hℳ t J.val ∧
        ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x Z ↔
          mem_l hℳ x A.val ∧ query_l (ℳ₀ := RawModel) ω.val A.val S.val I.val R.val t x := by
  let η : Env ClassModel [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree R).pushFree I).pushFree S).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    query_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
  have hQuery (t x : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree x).pushFree t) ↔
        query_l (ℳ₀ := RawModel) ω.val A.val S.val I.val R.val t x :=
    query_formula_l _ _ _ _ _ _ _ _
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (hBase := hBase) (φ := φ) (query_delta_l _ _ _ _ _ _ _) η J A
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassRowFamilyAmbient.exists_l (hBase := hBase) J A Q
  refine ⟨Y, fun Z => (hY Z).trans ?_⟩
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  apply forall_congr'
  intro x
  apply iff_congr Iff.rfl
  apply and_congr_right
  intro hx
  exact (hQ t x).trans
    ⟨fun h => (hQuery t x).mp h.2.2, fun h => ⟨ht, hx, (hQuery t x).mpr h⟩⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSelectedSatisfactionRows
