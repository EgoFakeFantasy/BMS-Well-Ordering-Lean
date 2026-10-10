import BMSConstructibleBridge.GraphInterpretation

/-!
# 公式分离的根选择器

把任意源公式的分离正文接入实际翻译，证明换码不变性及分离码的完整成员规格。
根选择器同时有实际纯二阶公式和对象理解推导。但新根拼接及其域保持在本文件
仍只核验标准语义，不能把选择器的理解推导当作整个分离公理的对象解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphSeparation

open Logic FirstOrder SecondOrderSyntax GraphInterpretation GraphTranslation

set_option autoImplicit false

private def empty : assignment_l [] := fun v => nomatch v

/-- 含自由参数的任意源正文，使用其实际翻译真值。 -/
def predicate_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (τ : assignment_l Δ) (A : CountableGraph.code_l) : Prop :=
  Formula.satisfies (target_l empty (push_l A τ)) (form_m φ)

theorem predicate_congr_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (τ : assignment_l Δ) (A B : CountableGraph.code_l) (h : CountableGraph.eq_l A B) :
    predicate_l φ τ A ↔ predicate_l φ τ B := by
  apply GraphInterpretation.congr_l φ empty empty (push_l A τ) (push_l B τ)
  · intro s v
    nomatch v
  · intro s v
    cases v with
    | here => exact h
    | there v => exact CountableGraph.refl_l (τ v)

/-- 对实际公式正文进行图码分离，不将不变性列为外加前提。 -/
def code_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (τ : assignment_l Δ) (A : CountableGraph.code_l) : CountableGraph.code_l :=
  CountableGraph.sep_l A (predicate_l φ τ)

theorem mem_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (τ : assignment_l Δ) (A B : CountableGraph.code_l) :
    CountableGraph.mem_l B (code_l φ τ A) ↔
      CountableGraph.mem_l B A ∧ predicate_l φ τ B :=
  CountableGraph.sep_mem_l A _ (predicate_congr_l φ τ) B

private def insert {Δ : SortContext ℒ} : VariableSubstitution signature_m
    (context_m (.set :: Δ)) [] (.num :: .num :: .set :: context_m Δ)
  | _, .here => .fvar .here
  | _, .there v => .fvar (.there (.there v))

private theorem insert_pure {Δ : SortContext ℒ} : SecondOrderSubstitution.images_m (insert (Δ := Δ)) := by
  intro s v
  cases v <;> rfl

/-- 原翻译正文在分离选择器参数布局中的实例化。 -/
def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula signature_m [] (.num :: .num :: .set :: context_m Δ) :=
  (form_m φ).substitute (.map VariableSubstitution.boundId insert)

private theorem body_pure {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    SecondOrderArithmetic.language_m (body_m φ) = true := by
  refine (SecondOrderSubstitution.form_subst_m (form_m φ) VariableSubstitution.boundId insert
    ?_ insert_pure).trans (form_pure_m φ)
  intro s v
  rfl

/-- 自由参数依次为候选子根、母根、原关系实数，以及其余源参数的图码。 -/
def selector_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula signature_m [] (.num :: .num :: .set :: context_m Δ) :=
  .conj (GraphSyntax.edge_m (.fvar (.there (.there .here)))
    (.fvar .here) (.fvar (.there .here))) (body_m φ)

theorem selector_pure_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    SecondOrderArithmetic.language_m (selector_m φ) = true := by
  have h := SecondOrderArithmetic.pure_language_m
    (GraphSyntax.edge_m (Γ := []) (Δ := .num :: .num :: .set :: context_m Δ)
      (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))
    (GraphSyntax.edge_pure_m _ _ _ rfl rfl rfl)
  exact congrArg₂ (· && ·) h (body_pure φ)

/-- 完整对象理解产生满足实际选择正文的根编号集合。 -/
theorem comprehension_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.comprehension_m (selector_m φ)) :=
  SecondOrderArithmetic.comprehension_derives_m _ (selector_pure_m φ)

def environment_l {Δ : SortContext ℒ} (τ : assignment_l Δ) (A : CountableGraph.code_l) :
    Env structure_l [] (.num :: .set :: context_m Δ) :=
  ⟨Assignment.empty, Assignment.push (M := structure_l) (sort := .num) A.root
    (Assignment.push (M := structure_l) (sort := .set) (CountableGraph.real_l A) (values_l τ))⟩

private theorem body_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (τ : assignment_l Δ) (A : CountableGraph.code_l) (a : Nat) (h : A.rel a A.root) :
    Formula.satisfies ((environment_l τ A).pushFree a) (body_m φ) ↔
      predicate_l φ τ (CountableGraph.child_l A a h) := by
  refine (Formula.satisfies_substitute ((environment_l τ A).pushFree a)
    (.map VariableSubstitution.boundId insert) (form_m φ)).trans ?_
  have h₁ : (((environment_l τ A).pushFree a).pullback
      (.map VariableSubstitution.boundId insert)) =
      target_l empty (push_l (CountableGraph.child_l A a h) τ) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  exact Iff.of_eq (congrArg (fun η => Formula.satisfies η (form_m φ)) h₁)

/-- 标准环境中的选择器精确筛选原母根的满足正文的直接子节点。 -/
theorem selector_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (τ : assignment_l Δ) (A : CountableGraph.code_l) (a : Nat) :
    Formula.satisfies ((environment_l τ A).pushFree a) (selector_m φ) ↔
      ∃ h : A.rel a A.root, predicate_l φ τ (CountableGraph.child_l A a h) := by
  rw [selector_m, Formula.satisfies, GraphSyntax.edge_l]
  change (GraphSyntax.relation_l (CountableGraph.real_l A) a A.root ∧
    Formula.satisfies ((environment_l τ A).pushFree a) (body_m φ)) ↔ _
  rw [GraphDomain.relation_real_l]
  constructor
  · rintro ⟨h, h₁⟩
    exact ⟨h, (body_l φ τ A a h).mp h₁⟩
  · rintro ⟨h, h₁⟩
    exact ⟨h, (body_l φ τ A a h).mpr h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.GraphSeparation
