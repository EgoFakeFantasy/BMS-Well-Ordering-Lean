import BMSConstructibleBridge.SecondOrderRelations
import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslation

/-! # 原配对坐标图的三参数查询解码

对象语言为原 num/set 纯二阶算术语言，背景理论为原 `theory_m`，正式推导
关系为 `Derives`。原二元理解产生实际内部实数 X，把 W 的 (pair(n,l),q)
查询展平为 X 的 (n,pair(l,q)) 查询。全部配对均为同一旧平方分支配对。

W 可以是任意内部实数，不要求函数性或 Class 性质，不抽取 Type 层见证族。
本模块只给图的逐坐标解码；非法输入上的总化值及其 Valid guard 是另项义务，
这里不构造 Class 图，也不宣称 BMS 的对象推导终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairFunctionDecode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderPairing

set_option autoImplicit false

universe u

/-- 自由槽为 n、展平坐标 s、W；数存在量词依次绑定 l、q、pair(n,l)。 -/
def formula_m : Formula signature_m [] [.num, .num, .set] :=
  .existsE .num (.existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.bvar (.there (.there .here))) (.bvar (.there .here))
      (.fvar (.there .here)))
    (.conj
      (PrimitiveFormulas.pair_m (.fvar .here) (.bvar (.there (.there .here))) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here)
        (.bvar (.there .here)))))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

/-- 三参数查询规格仍是原翻译模块的实际嵌套配对查询。 -/
def spec_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (W X : set_l ℳ) : Prop :=
  ∀ n l q, SecondOrderLegacyFormulaTranslation.query_l X n l q ↔
    relation_l W (value_l n l) q

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (W : set_l ℳ) (n s : num_l ℳ) :
    formula_m.satisfies ((((Env.empty).pushFree W).pushFree s).pushFree n) ↔
      ∃ l q, value_l l q = s ∧ relation_l W (value_l n l) q := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l]
  change (∃ l q i : num_l ℳ, value_l l q = s ∧ value_l n l = i ∧
    relation_l W i q) ↔ _
  constructor
  · rintro ⟨l, q, i, hs, rfl, h⟩
    exact ⟨l, q, hs, h⟩
  · rintro ⟨l, q, hs, h⟩
    exact ⟨l, q, value_l n l, hs, rfl, h⟩

/-- 配对单射性排除展平坐标的其他分解，包括任意非标准内部坐标。 -/
theorem paired_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (W : set_l ℳ) (n l q : num_l ℳ) :
    formula_m.satisfies ((((Env.empty).pushFree W).pushFree (value_l l q)).pushFree n) ↔
      relation_l W (value_l n l) q := by
  rw [formula_l]
  constructor
  · rintro ⟨a, b, hab, h⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ a b l q hab
    exact h
  · intro h
    exact ⟨l, q, rfl, h⟩

/-- 由原理解得到展平后的实际内部实数，而非外部关系的强制集合化。 -/
theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (W : set_l ℳ) :
    ∃ X : set_l ℳ, spec_l W X := by
  obtain ⟨X, hX⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    ((Env.empty).pushFree W)
  exact ⟨X, fun n l q => (hX n (value_l l q)).trans (paired_formula_l hℳ W n l q)⟩

/-- 产生同一展平解码实数的实际原 Z₂ 理解实例。 -/
theorem derives_m : Derives theory_m []
    (SecondOrderArithmetic.comprehension_m (SecondOrderRelations.formula_m formula_m)) :=
  SecondOrderRelations.comprehension_m formula_m pure_m

/-- 部分查询的解码保留原合法性守卫，排除非法输入的默认零。 -/
def guarded_formula_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num <| .existsE .num <| .existsE .num <| .conj
    (PrimitiveFormulas.pair_m (.bvar (.there (.there .here))) (.bvar (.there .here))
      (.fvar (.there .here))) <| .conj
    (PrimitiveFormulas.pair_m (.fvar .here) (.bvar (.there (.there .here))) (.bvar .here)) <| .conj
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there (.there .here))))
    (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.bvar (.there .here)))

theorem guarded_pure_m : language_m guarded_formula_m = true := pure_language_m _ rfl

def guarded_spec_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (V W X : set_l ℳ) : Prop :=
  ∀ n l q, SecondOrderLegacyFormulaTranslation.query_l X n l q ↔
    relation_l V n l ∧ relation_l W (value_l n l) q

theorem guarded_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (V W : set_l ℳ) (n s : num_l ℳ) :
    guarded_formula_m.satisfies (((((Env.empty).pushFree W).pushFree V).pushFree s).pushFree n) ↔
      ∃ l q, value_l l q = s ∧ relation_l V n l ∧ relation_l W (value_l n l) q := by
  simp only [guarded_formula_m, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l]
  change (∃ l q i : num_l ℳ, value_l l q = s ∧ value_l n l = i ∧
    relation_l V n l ∧ relation_l W i q) ↔ _
  constructor
  · rintro ⟨l, q, i, hs, rfl, hV, hW⟩
    exact ⟨l, q, hs, hV, hW⟩
  · rintro ⟨l, q, hs, hV, hW⟩
    exact ⟨l, q, value_l n l, hs, rfl, hV, hW⟩

theorem guarded_paired_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (V W : set_l ℳ) (n l q : num_l ℳ) :
    guarded_formula_m.satisfies
      (((((Env.empty).pushFree W).pushFree V).pushFree (value_l l q)).pushFree n) ↔
        relation_l V n l ∧ relation_l W (value_l n l) q := by
  rw [guarded_formula_l]
  constructor
  · rintro ⟨a, b, hab, hV, hW⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ a b l q hab
    exact ⟨hV, hW⟩
  · rintro ⟨hV, hW⟩
    exact ⟨l, q, rfl, hV, hW⟩

theorem exists_guarded_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (V W : set_l ℳ) :
    ∃ X : set_l ℳ, guarded_spec_l V W X := by
  obtain ⟨X, hX⟩ := SecondOrderRelations.comprehension_l hℳ guarded_formula_m guarded_pure_m
    (((Env.empty).pushFree W).pushFree V)
  exact ⟨X, fun n l q => (hX n (value_l l q)).trans (guarded_paired_formula_l hℳ V W n l q)⟩

theorem guarded_derives_m : Derives theory_m []
    (SecondOrderArithmetic.comprehension_m (SecondOrderRelations.formula_m guarded_formula_m)) :=
  SecondOrderRelations.comprehension_m guarded_formula_m guarded_pure_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairFunctionDecode
