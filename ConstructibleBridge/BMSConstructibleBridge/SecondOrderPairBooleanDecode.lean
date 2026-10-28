import BMSConstructibleBridge.SecondOrderRelations

/-! # 配对坐标零一图的二元解码

对象语言是原双排序 num/set 的纯零、后继、加乘和成员语言；背景理论为
`SecondOrderArithmetic.theory_m`，正式推导关系为原核 `Derives`。
实际正文为 ∃v (pair(n,l,v) ∧ edge(W,v,1))，理解实例产生原模型中的实数 X。
所有坐标均在内部数域中，不要求 W 为 Class，不抽取 Type 层见证函数。
这里只解码已有二维零一图的一值列，不宣称无限图 Class 化或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairBooleanDecode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderPairing

set_option autoImplicit false

universe u

/-- 三个自由槽依次为首坐标、次坐标、原二维图；配对值由数存在量词绑定。 -/
def formula_m : Formula signature_m [] [.num, .num, .set] :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (numeral_m 1)))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

/-- 在原模型的全部内部坐标上，把配对码处的值一查询恢复为二元关系。 -/
def spec_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (W X : set_l ℳ) : Prop :=
  ∀ n l, relation_l X n l ↔
    relation_l W (value_l n l) (succ_l (zero_l ℳ))

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (W : set_l ℳ) (n l : num_l ℳ) :
    formula_m.satisfies ((((Env.empty).pushFree W).pushFree l).pushFree n) ↔
      relation_l W (value_l n l) (succ_l (zero_l ℳ)) := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l]
  change (∃ v : num_l ℳ, value_l n l = v ∧
    relation_l W v (succ_l (zero_l ℳ))) ↔ _
  constructor
  · rintro ⟨v, rfl, h⟩
    exact h
  · intro h
    exact ⟨value_l n l, rfl, h⟩

/-- 由原二元理解产生实际内部实数；W 不需满足函数性或 Class 条件。 -/
theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (W : set_l ℳ) :
    ∃ X : set_l ℳ, spec_l W X := by
  obtain ⟨X, hX⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    ((Env.empty).pushFree W)
  exact ⟨X, fun n l => (hX n l).trans (formula_l W n l)⟩

/-- 产生此解码实数的实际原 Z₂ 理解实例。 -/
theorem derives_m : Derives theory_m []
    (SecondOrderArithmetic.comprehension_m (SecondOrderRelations.formula_m formula_m)) :=
  SecondOrderRelations.comprehension_m formula_m pure_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairBooleanDecode
