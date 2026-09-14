import BMSConstructibleBridge.SecondOrderGraftSemantics
import BMSConstructibleBridge.SecondOrderInterpretation
import BMSConstructibleBridge.GraphSeparation

/-!
# 任意模型内部图码的完整分离构造

任意源公式的原翻译产生内部选择集合；实际新根拼接、内部域保持和成员换码
共同给出整个分离对象的成员规格。正文的换码不变性由已证完整公式解释导出，
不作为调用者的额外前提。此处先给任意模型构造，后续再回传闭模式对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open GraphTranslation SecondOrderInterpretation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def empty : assignment_l ℳ [] := fun {_} v => nomatch v

def predicate_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (τ : assignment_l ℳ Δ) (A : SecondOrderGraph.code_l ℳ) : Prop :=
  Formula.satisfies (target_l empty (push_l A τ)) (form_m φ)

theorem predicate_congr_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (τ : assignment_l ℳ Δ)
    (A B : SecondOrderGraph.code_l ℳ) (h : SecondOrderGraph.eq_l A B) :
    predicate_l φ τ A ↔ predicate_l φ τ B := by
  apply SecondOrderInterpretation.congr_l hℳ
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => exact h
    | there v => exact SecondOrderGraph.refl_l hℳ (τ v)

def environment_l {Δ : SortContext ℒ} (τ : assignment_l ℳ Δ) (A : SecondOrderGraph.code_l ℳ) :
    Env ℳ [] (.num :: .set :: context_m Δ) :=
  ⟨Assignment.empty, Assignment.push (M := ℳ) (sort := .num) A.root
    (Assignment.push (M := ℳ) (sort := .set) A.real (values_l τ))⟩

private theorem body_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (τ : assignment_l ℳ Δ)
    (A : SecondOrderGraph.code_l ℳ) (a : num_l ℳ) (h : SecondOrderPairing.relation_l A.real a A.root) :
    Formula.satisfies ((environment_l τ A).pushFree a) (GraphSeparation.body_m φ) ↔
      predicate_l φ τ (SecondOrderGraph.child_l hℳ A a h) := by
  refine (Formula.satisfies_substitute ((environment_l τ A).pushFree a) _ (form_m φ)).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => Formula.satisfies η (form_m φ))
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem selector_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (τ : assignment_l ℳ Δ)
    (A : SecondOrderGraph.code_l ℳ) (a : num_l ℳ) :
    Formula.satisfies ((environment_l τ A).pushFree a) (GraphSeparation.selector_m φ) ↔
      ∃ h : SecondOrderPairing.relation_l A.real a A.root,
        predicate_l φ τ (SecondOrderGraph.child_l hℳ A a h) := by
  rw [GraphSeparation.selector_m, Formula.satisfies, SecondOrderPairing.edge_l]
  change (SecondOrderPairing.relation_l A.real a A.root ∧
    Formula.satisfies ((environment_l τ A).pushFree a) (GraphSeparation.body_m φ)) ↔ _
  exact ⟨fun ⟨h, h₁⟩ => ⟨h, (body_l hℳ φ τ A a h).mp h₁⟩,
    fun ⟨h, h₁⟩ => ⟨h, (body_l hℳ φ τ A a h).mpr h₁⟩⟩

/-- 任意含参数原公式的完整分离对象存在于内部图解释域。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (τ : assignment_l ℳ Δ) (A : SecondOrderGraph.code_l ℳ) :
    ∃ C : SecondOrderGraph.code_l ℳ, ∀ B,
      SecondOrderGraph.mem_l B C ↔ SecondOrderGraph.mem_l B A ∧ predicate_l φ τ B := by
  obtain ⟨P, hP⟩ := SecondOrderModel.comprehension_l hℳ (GraphSeparation.selector_m φ)
    (GraphSeparation.selector_pure_m φ) (environment_l τ A)
  have h₀ := fun a => (hP a).trans (selector_l hℳ φ τ A a)
  have h₁ : ∀ a, mem_l a P → SecondOrderDomain.wf_l A.real a := by
    intro a h
    obtain ⟨h, _⟩ := (h₀ a).mp h
    exact SecondOrderDomain.child_l hℳ A.real A.root a A.wf h
  obtain ⟨C, hC⟩ := SecondOrderGraftSemantics.exists_l hℳ A.real P h₁
  refine ⟨C, fun B => (hC B).trans ?_⟩
  constructor
  · rintro ⟨a, h, h₂⟩
    obtain ⟨h, h₃⟩ := (h₀ a).mp h
    exact ⟨⟨a, h, h₂⟩,
      (predicate_congr_l hℳ φ τ B (SecondOrderGraph.child_l hℳ A a h) h₂).mpr h₃⟩
  · rintro ⟨⟨a, h, h₂⟩, h₃⟩
    exact ⟨a, (h₀ a).mpr ⟨h,
      (predicate_congr_l hℳ φ τ B (SecondOrderGraph.child_l hℳ A a h) h₂).mp h₃⟩, h₂⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSeparation
