import BMSConstructibleBridge.SecondOrderUnpairing

/-!
# 任意模型内部的二元关系理解

把有实际纯公式的二元性质编码为模型集合，而非任意外部二元关系的集合。
同一配对双射确保原坐标规格和全实数外延性；不增加选择或标准性公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelations

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

private def insert {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: .num :: Δ) [.num, .num] (.num :: Δ)
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there v)

private theorem insert_pure {Δ : SortContext signature_m} :
    SecondOrderSubstitution.images_m (insert (Δ := Δ)) := by
  intro s v
  cases v with
  | here => rfl
  | there v =>
      cases v with
      | here => rfl
      | there v => cases s <;> rfl

private def substitution {Δ : SortContext signature_m} :
    Substitution signature_m [] (.num :: .num :: Δ) [.num, .num] (.num :: Δ) :=
  .map (fun v => nomatch v) insert

private def body {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ)) :
    Formula signature_m [.num, .num] (.num :: Δ) := φ.substitute substitution

private theorem body_pure {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ)) (hφ : language_m φ = true) :
    language_m (body φ) = true := by
  refine (SecondOrderSubstitution.form_subst_m φ (fun v => nomatch v) insert ?_
    insert_pure).trans hφ
  intro s v
  nomatch v

/-- 自由首变量是配对值；原来的两个坐标移入存在量词，其他参数保留。 -/
def formula_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ)) : Formula signature_m [] (.num :: Δ) :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (.fvar .here)) (body φ)))

theorem pure_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ)) (hφ : language_m φ = true) :
    language_m (formula_m φ) = true := by
  change (language_m (PrimitiveFormulas.pair_m (Γ := [.num, .num]) (Δ := .num :: Δ)
    (.bvar (.there .here)) (.bvar .here)
    (.fvar .here)) && language_m (body φ)) = true
  rw [body_pure φ hφ, Bool.and_true]
  exact pure_language_m _ (PrimitiveFormulas.pair_pure_l _ _ _ rfl rfl rfl)

/-- 二元理解的实际对象实例；正文仍可含任意二阶量词和混合参数。 -/
theorem comprehension_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ)) (hφ : language_m φ = true) :
    Derives theory_m [] (SecondOrderArithmetic.comprehension_m (formula_m φ)) :=
  comprehension_derives_m _ (pure_m φ hφ)

private theorem body_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: .num :: Δ))
    (η : Env ℳ [] Δ) (z m n : num_l ℳ) :
    Formula.satisfies (((η.pushFree z).pushBound m).pushBound n) (body φ) ↔
      Formula.satisfies ((η.pushFree n).pushFree m) φ := by
  refine (Formula.satisfies_substitute _ substitution φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η φ)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v =>
        cases v with
        | here => rfl
        | there v => cases s <;> rfl

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: .num :: Δ))
    (η : Env ℳ [] Δ) (z : num_l ℳ) :
    Formula.satisfies (η.pushFree z) (formula_m φ) ↔
      ∃ m n, SecondOrderPairing.value_l m n = z ∧
        Formula.satisfies ((η.pushFree n).pushFree m) φ := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l, body_l]
  rfl

/-- 由实际理解公理产生模型集合，不把外部集合强塞进 Henkin 集合域。 -/
theorem comprehension_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: .num :: Δ)) (hφ : language_m φ = true)
    (η : Env ℳ [] Δ) :
    ∃ X : set_l ℳ, ∀ m n, SecondOrderPairing.relation_l X m n ↔
      Formula.satisfies ((η.pushFree n).pushFree m) φ := by
  obtain ⟨X, hX⟩ := SecondOrderModel.comprehension_l hℳ (formula_m φ) (pure_m φ hφ) η
  refine ⟨X, fun m n => (hX _).trans ((formula_l φ η _).trans ?_)⟩
  constructor
  · rintro ⟨a, b, h, h₁⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ a b m n h
    exact h₁
  · intro h
    exact ⟨m, n, rfl, h⟩

/-- 每个模型数都是某个配对值，因此边逐点相同即内部实数相等。 -/
theorem ext_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ)
    (h : ∀ m n, SecondOrderPairing.relation_l X m n ↔ SecondOrderPairing.relation_l Y m n) :
    X = Y := by
  apply SecondOrderModel.ext_l hℳ X Y
  intro z
  obtain ⟨m, n, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ z
  exact h m n

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelations
