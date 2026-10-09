import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.PowerlessAssignmentUpdate
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 原 Z₂ 商中的精确函数更新

对象语言为纯隶属 ℒ，背景与正式推导关系均为原 Z₂。原定义域 D 与
陪域 A 已经给出，更新图由 D×A 上的实际关系像构造。不调用要求
完整 PowerlessTheory 的更新或映射定理，也不使用 Collection。
取值方程量化全部原商对象，输出保持原定义域和原陪域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionUpdate

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def matrix_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  .disj (.conj (.equal (.fvar .here) (.fvar (.there (.there (.there .here)))))
    (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here)))))))
    (.conj (.neg (.equal (.fvar .here) (.fvar (.there (.there (.there .here))))))
      (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
        (.fvar .here) (.fvar (.there .here))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {f D A i a : type_l hℳ} (hf : map_l (ℳ := 𝒱) f D A)
    (hi : mem_l hℳ i D) (ha : mem_l hℳ a A) :
    ∃ g : type_l hℳ, map_l (ℳ := 𝒱) g D A ∧
      PowerlessAssignmentUpdate.update_l (ℳ := 𝒱) f i a g := by
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree a).pushFree i).pushFree f
  have hRead (x y : type_l hℳ) : matrix_m.satisfies ((η.pushFree y).pushFree x) ↔
      (x = i ∧ y = a) ∨ (x ≠ i ∧ value_l (ℳ := 𝒱) f x y) := by
    simp only [matrix_m, Formula.satisfies, value_formula_l, Term.eval]
    rfl
  obtain ⟨g, hg⟩ := SecondOrderDefinableRelationImage.exists_l hℳ matrix_m η D A
  have hValue (x y : type_l hℳ) : value_l (ℳ := 𝒱) g x y ↔
      mem_l hℳ x D ∧ mem_l hℳ y A ∧ ((x = i ∧ y = a) ∨ (x ≠ i ∧ value_l (ℳ := 𝒱) f x y)) := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨x', y', hx, hy, hφ, hp'⟩ := (hg p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl
      exact ⟨hx, hy, (hRead x y).mp hφ⟩
    · rintro ⟨hx, hy, hφ⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hg p).mpr ⟨x, y, hx, hy, (hRead x y).mpr hφ, hp⟩, hp⟩
  have hUpdate : PowerlessAssignmentUpdate.update_l (ℳ := 𝒱) f i a g := by
    intro x y
    refine (hValue x y).trans ⟨And.right ∘ And.right, ?_⟩
    intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨hne, hxy⟩
    · exact ⟨hi, ha, Or.inl ⟨rfl, rfl⟩⟩
    · have hBounds := SecondOrderFunctionProperties.value_mem_l hℳ hf hxy
      exact ⟨hBounds.1, hBounds.2, Or.inr ⟨hne, hxy⟩⟩
  refine ⟨g, ⟨?_, ?_⟩, hUpdate⟩
  · intro p hp
    obtain ⟨x, y, hx, hy, _, hxy⟩ := (hg p).mp hp
    exact ⟨x, y, hx, hy, hxy⟩
  · intro x hx
    classical
    by_cases hxi : x = i
    · subst x
      refine ⟨a, ⟨ha, (hUpdate i a).mpr (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
      intro y hy
      rcases (hUpdate i y).mp hy.2 with ⟨_, hya⟩ | ⟨hne, _⟩
      · exact hya
      · exact (hne rfl).elim
    · obtain ⟨y, hy, hUnique⟩ := hf.2 x hx
      refine ⟨y, ⟨hy.1, (hUpdate x y).mpr (Or.inr ⟨hxi, hy.2⟩)⟩, ?_⟩
      intro z hz
      rcases (hUpdate x z).mp hz.2 with ⟨hEq, _⟩ | ⟨_, hValue⟩
      · exact (hxi hEq).elim
      · exact hUnique z ⟨hz.1, hValue⟩

theorem length_unique_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {f D E A C : type_l hℳ} (hf : map_l (ℳ := 𝒱) f D A) (hg : map_l (ℳ := 𝒱) f E C) : D = E := by
  apply SecondOrderQuotient.ext_l hℳ
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hg hy.2).1
  · intro hx
    obtain ⟨y, hy, _⟩ := hg.2 x hx
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hf hy.2).1

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def schema_m {Γ Δ : SortContext ℒ} (f D A i a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderObjectSyntax.map_m f D A) <|
    .imp (SecondOrderObjectSyntax.member_m i D) <|
      .imp (SecondOrderObjectSyntax.member_m a A) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up D) (up A))
          (PowerlessAssignmentUpdate.update_m (up f) (up i) (up a) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (f D A i a : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m f D A i a)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (f D A i a : Term ℒ [] Δ .set) :
    (sentence_m f D A i a).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, map_formula_l, PowerlessAssignmentUpdate.update_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hf hi ha => exists_l hℳ hf hi ha

theorem derives_m {Δ : SortContext ℒ} (f D A i a : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m f D A i a)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ f D A i a)

#print axioms exists_l
#print axioms length_unique_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFunctionUpdate
