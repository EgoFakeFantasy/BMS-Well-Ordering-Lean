import BMSConstructibleBridge.SecondOrderSubsetCollection

/-!
# 按内部公式选择的切片集合

保留原统一切片图，只把满足实际内部索引谓词的切片根拼到新根下。
适用于合法公式及有效参数筛选，也适用于其他内部索引子族；不使用集合收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSelectedSubsetCollection

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def insert_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: Δ) [.num] (.num :: Δ)
  | _, .here => .bvar .here
  | _, .there v => .fvar (.there v)

private def body_m {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) :
    Formula signature_m [.num] (.num :: Δ) :=
  φ.substitute (show Substitution signature_m [] (.num :: Δ) [.num] (.num :: Δ) from
    .map (fun v => nomatch v) insert_m)

def selector_m {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) :
    Formula signature_m [] (.num :: Δ) :=
  .existsE .num (.conj (PrimitiveFormulas.pair_m (numeral_m 1) (.bvar .here) (.fvar .here))
    (body_m φ))

theorem pure_m {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (hφ : language_m φ = true) : language_m (selector_m φ) = true := by
  have hBody : language_m (body_m φ) = true := by
    refine (SecondOrderSubstitution.form_subst_m φ _ _ ?_ ?_).trans hφ
    · intro s v
      nomatch v
    · intro s v
      cases v <;> rfl
  change (language_m (PrimitiveFormulas.pair_m (Γ := [.num]) (Δ := .num :: Δ)
    (numeral_m 1) (.bvar .here) (.fvar .here)) && language_m (body_m φ)) = true
  rw [hBody]
  rfl

theorem selector_l {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (η : Env ℳ [] Δ) (a : num_l ℳ) : (selector_m φ).satisfies (η.pushFree a) ↔
      ∃ i, SecondOrderSubsetLayer.root_l i = a ∧ φ.satisfies (η.pushFree i) := by
  simp only [selector_m, Formula.satisfies, SecondOrderPairing.formula_l]
  apply exists_congr
  intro i
  apply and_congr Iff.rfl
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v <;> rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (A : SecondOrderGraph.code_l ℳ) (F : set_l ℳ) :
    ∃ G, ∃ hG : SecondOrderSubsetLayer.spec_l A.real F A.root G,
      ∃ H : SecondOrderGraph.code_l ℳ, ∀ B, SecondOrderGraph.mem_l B H ↔
        ∃ i, φ.satisfies (η.pushFree i) ∧
          SecondOrderGraph.eq_l B (SecondOrderSubsetLayer.code_l hℳ A F G hG i) := by
  obtain ⟨G, hG⟩ := SecondOrderSubsetLayer.exists_l hℳ A.real F A.root
  obtain ⟨P, hP⟩ := comprehension_l hℳ (selector_m φ) (pure_m φ hφ) η
  have hRead a : mem_l a P ↔ ∃ i, SecondOrderSubsetLayer.root_l i = a ∧
      φ.satisfies (η.pushFree i) := (hP a).trans (selector_l φ η a)
  have hD a (ha : mem_l a P) : SecondOrderDomain.wf_l G a := by
    obtain ⟨i, rfl, _⟩ := (hRead a).mp ha
    exact SecondOrderSubsetLayer.wf_l hℳ A F G hG i
  obtain ⟨H, hH⟩ := SecondOrderGraftSemantics.exists_l hℳ G P hD
  refine ⟨G, hG, H, fun B => (hH B).trans ?_⟩
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨i, rfl, hi⟩ := (hRead a).mp ha
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨_, (hRead _).mpr ⟨i, rfl, hi⟩, h⟩

theorem family_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (A : SecondOrderGraph.code_l ℳ) (F : set_l ℳ) :
    ∃ H : SecondOrderGraph.code_l ℳ, ∀ B, SecondOrderGraph.mem_l B H ↔
      ∃ i, φ.satisfies (η.pushFree i) ∧ ∀ C, SecondOrderGraph.mem_l C B ↔
        ∃ a, SecondOrderPairing.relation_l A.real a A.root ∧ SecondOrderPairing.relation_l F i a ∧
          SecondOrderBisimulation.eq_l C.real A.real C.root a := by
  obtain ⟨G, hG, H, hH⟩ := exists_l hℳ φ hφ η A F
  refine ⟨H, fun B => (hH B).trans ?_⟩
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, fun C =>
      (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ C) h).trans
        (SecondOrderSubsetLayer.mem_l hℳ A F G hG i C)⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, (SecondOrderGraph.ext_l hℳ B _).mpr
      (fun C => (h C).trans (SecondOrderSubsetLayer.mem_l hℳ A F G hG i C).symm)⟩

#print axioms exists_l
#print axioms family_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSelectedSubsetCollection
