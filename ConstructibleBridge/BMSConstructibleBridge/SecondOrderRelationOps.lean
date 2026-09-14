import BMSConstructibleBridge.SecondOrderRelations

/-!
# 内部二元关系的基本封闭操作

对角、反向、复合与添点均由指定的纯公式理解构造。关系见证始终属于同一
模型集合域，为内部双模拟等价律提供实数见证，不量化任意外部关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationOps

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

theorem diagonal_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) :
    ∃ X : set_l ℳ, ∀ a b, relation_l X a b ↔ a = b := by
  exact SecondOrderRelations.comprehension_l hℳ
    (.equal (.fvar .here) (.fvar (.there .here))) rfl (Env.empty (M := ℳ))

theorem converse_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X : set_l ℳ) :
    ∃ Y : set_l ℳ, ∀ a b, relation_l Y a b ↔ relation_l X b a := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree X)
  refine ⟨Y, fun a b => (hY a b).trans ?_⟩
  exact SecondOrderPairing.edge_l _ _ _ _

theorem comp_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) :
    ∃ Z : set_l ℳ, ∀ a c, relation_l Z a c ↔
      ∃ b, relation_l X a b ∧ relation_l Y b c := by
  let φ : Formula signature_m [] [.num, .num, .set, .set] :=
    .existsE .num (.conj
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here)
        (.fvar (.there .here))))
  obtain ⟨Z, hZ⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree Y).pushFree X)
  refine ⟨Z, fun a c => (hZ a c).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

theorem extend_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X : set_l ℳ) (a b : num_l ℳ) :
    ∃ Y : set_l ℳ, ∀ c d, relation_l Y c d ↔ relation_l X c d ∨ (c = a ∧ d = b) := by
  let φ : Formula signature_m [] [.num, .num, .set, .num, .num] :=
    .disj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))
      (.conj (.equal (.fvar .here) (.fvar (.there (.there (.there .here)))))
        (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here)))))))
  obtain ⟨Y, hY⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree b).pushFree a).pushFree X)
  refine ⟨Y, fun c d => (hY c d).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationOps
