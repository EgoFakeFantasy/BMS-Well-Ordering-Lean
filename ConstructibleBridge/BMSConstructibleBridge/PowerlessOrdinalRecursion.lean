import BMSConstructibleBridge.PowerlessOrdinalRelation
import BMSConstructibleBridge.PowerlessWellRecursionPresentation

/-!
# 上游内部序数上的前史递归

消去辅助关系图 R，结论中的前驱关系直接采用模型隶属。
算子的参数及完整前驱图保持不变；集合序数不转成宿主 Ordinal。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRecursion

open Logic FirstOrder ThirdOrderSemantics PowerlessWellRecursionSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ : SortContext ℒ}

def history_l (H f a : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p H ↔ ∃ x y, ordered_l x y p ∧ member_l ℳ x a ∧ value_l f x y

theorem history_iff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R f B H a : carrier_l ℳ} (hR : PowerlessOrdinalRelation.relation_l A R)
    (hf : map_l f A B) (ha : member_l ℳ a A) : PowerlessHistory.history_l H f R a ↔ history_l H f a := by
  apply forall_congr'
  intro p
  apply iff_congr Iff.rfl
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  constructor
  · rintro ⟨hp, hx, hy⟩
    exact ⟨hp, ((PowerlessOrdinalRelation.value_l hℳ hR).mp hx).2.2, hy⟩
  · rintro ⟨hp, hx, hy⟩
    exact ⟨hp, (PowerlessOrdinalRelation.value_l hℳ hR).mpr
      ⟨(PowerlessFunction.value_mem_l hℳ hf hy).1, ha, hx⟩, hy⟩

def recursion_l (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f A : carrier_l ℳ) : Prop :=
  ∃ B, map_l f A B ∧ ∀ a y, value_l f a y → ∃ H, history_l H f a ∧ rule_l φ η a H y

theorem recursion_iff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {A R f : carrier_l ℳ} (hR : PowerlessOrdinalRelation.relation_l A R) :
    PowerlessWellRecursionPresentation.recursion_l φ η f A R ↔ recursion_l φ η f A := by
  apply exists_congr
  intro B
  apply and_congr_right
  intro hf
  apply forall_congr'
  intro a
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro hy
  exact exists_congr fun _ => and_congr (history_iff_l hℳ hR hf (PowerlessFunction.value_mem_l hℳ hf hy).1) Iff.rfl

def recursion_m (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) : Formula ℒ [] (.set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: .set :: Γ) [.set] (.set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .fvar .here
      | .set, .there .here => .fvar (.there .here)
      | .set, .there (.there .here) => .bvar .here
      | .set, .there (.there (.there v)) => .fvar (.there (.there v)))
  .existsE .set (.conj (PowerlessOrdinalRelation.relation_m (.fvar (.there .here)) (.bvar .here))
    ((PowerlessWellRecursionPresentation.recursion_m φ).substitute σ))

theorem recursion_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f A : carrier_l ℳ) :
    (recursion_m φ).satisfies (((PowerlessComprehension.env_l η).pushFree A).pushFree f) ↔ recursion_l φ η f A := by
  have h : (recursion_m φ).satisfies (((PowerlessComprehension.env_l η).pushFree A).pushFree f) ↔
      ∃ R, PowerlessOrdinalRelation.relation_l A R ∧ PowerlessWellRecursionPresentation.recursion_l φ η f A R := by
    simp only [recursion_m, Formula.satisfies, PowerlessOrdinalRelation.relation_formula_l, Formula.satisfies_substitute]
    apply exists_congr
    intro R
    apply and_congr Iff.rfl
    rw [← PowerlessWellRecursionPresentation.recursion_formula_l φ η f A R]
    apply Iff.of_eq
    apply congrArg (fun η => (PowerlessWellRecursionPresentation.recursion_m φ).satisfies η)
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      match s, v with
      | .set, .here => rfl
      | .set, .there .here => rfl
      | .set, .there (.there .here) => rfl
      | .set, .there (.there (.there v)) => rfl
  refine h.trans ⟨?_, ?_⟩
  · rintro ⟨R, hR, hf⟩
    exact (recursion_iff_l hℳ φ η hR).mp hf
  · intro hf
    obtain ⟨R, hR⟩ := PowerlessOrdinalRelation.exists_l hℳ A
    exact ⟨R, hR, (recursion_iff_l hℳ φ η hR).mpr hf⟩

theorem exists_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A : carrier_l ℳ} (hA : PowerlessOrdinal.ordinal_l A)
    (h₀ : ∀ x, member_l ℳ x A → ∀ H, ∃ y, rule_l φ η x H y) : ∃! f, recursion_l φ η f A := by
  obtain ⟨R, hR⟩ := PowerlessOrdinalRelation.exists_l hℳ A
  obtain ⟨f, hf, h₁⟩ := PowerlessWellRecursionPresentation.exists_unique_l hℳ φ η h
    (PowerlessOrdinalRelation.wellOrder_l hℳ hA hR) h₀
  exact ⟨f, (recursion_iff_l hℳ φ η hR).mp hf, fun g hg => h₁ g ((recursion_iff_l hℳ φ η hR).mpr hg)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalRecursion
