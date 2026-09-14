import BMSConstructibleBridge.GraphTranslation

/-!
# 图码解释的完整公式语义

源集合变量由实际图码赋值，再分别送到商结构和值为实数／根的双排序环境。
此处使用逐变量赋值映射，而非全局选择商代表，保留量词递归所需的环境对应。
语义正确性针对标准双排序结构，不宣称任意 Henkin 模型外部良基或对象可导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphInterpretation

open Logic FirstOrder SecondOrderSyntax GraphTranslation

set_option autoImplicit false

/-- 所有源变量排序都是集合；赋值保留实际图码代表。 -/
abbrev assignment_l (Γ : SortContext ℒ) := ∀ {s}, Variable Γ s → CountableGraph.code_l

def push_l {Γ : SortContext ℒ} (A : CountableGraph.code_l) (ρ : assignment_l Γ) :
    assignment_l (.set :: Γ)
  | _, .here => A
  | _, .there v => ρ v

/-- 源变量按根、关系的顺序展开为双排序赋值。 -/
def values_l : {Γ : SortContext ℒ} → assignment_l Γ → Assignment structure_l (context_m Γ)
  | List.nil, _ => Assignment.empty
  | .set :: Γ, ρ => Assignment.push (M := structure_l) (sort := .num) (ρ .here).root
      (Assignment.push (M := structure_l) (sort := .set) (CountableGraph.real_l (ρ .here))
        (values_l (Γ := Γ) (fun v => ρ (.there v))))

def target_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ) :
    Env structure_l (context_m Γ) (context_m Δ) := ⟨values_l ρ, values_l τ⟩

def source_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ) :
    Env GraphQuotient.structure_l Γ Δ :=
  ⟨fun v => GraphQuotient.mk_l (ρ v), fun v => GraphQuotient.mk_l (τ v)⟩

theorem target_push_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ)
    (A : CountableGraph.code_l) : target_l (push_l A ρ) τ =
      ((target_l ρ τ).pushBound (CountableGraph.real_l A)).pushBound A.root := rfl

theorem source_push_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ)
    (A : CountableGraph.code_l) : source_l (push_l A ρ) τ =
      (source_l ρ τ).pushBound (GraphQuotient.mk_l A) := by
  apply Env.ext
  · intro s v
    cases v <;> rfl
  · intro s v
    rfl

theorem root_var_l : {Γ : SortContext ℒ} → (ρ : assignment_l Γ) →
    (v : Variable Γ .set) → values_l ρ (root_var_m v) = (ρ v).root
  | .set :: _, _, .here => rfl
  | .set :: _, ρ, .there v => root_var_l (fun v => ρ (.there v)) v

theorem graph_var_l : {Γ : SortContext ℒ} → (ρ : assignment_l Γ) →
    (v : Variable Γ .set) → values_l ρ (graph_var_m v) = CountableGraph.real_l (ρ v)
  | .set :: _, _, .here => rfl
  | .set :: _, ρ, .there v => graph_var_l (fun v => ρ (.there v)) v

/-- 源项取实际代码值；无函数符号分支。 -/
def term_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ) :
    Term ℒ Γ Δ .set → CountableGraph.code_l
  | .bvar v => ρ v
  | .fvar v => τ v
  | .app f _ => nomatch f

theorem root_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ)
    (s : Term ℒ Γ Δ .set) : (root_m s).eval (target_l ρ τ) = (term_l ρ τ s).root := by
  match s with
  | .bvar v => exact root_var_l ρ v
  | .fvar v => exact root_var_l τ v
  | .app f _ => nomatch f

theorem graph_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ)
    (s : Term ℒ Γ Δ .set) :
    (graph_m s).eval (target_l ρ τ) = CountableGraph.real_l (term_l ρ τ s) := by
  match s with
  | .bvar v => exact graph_var_l ρ v
  | .fvar v => exact graph_var_l τ v
  | .app f _ => nomatch f

theorem term_eq_l {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ)
    (s : Term ℒ Γ Δ .set) : s.eval (source_l ρ τ) = GraphQuotient.mk_l (term_l ρ τ s) := by
  match s with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

private theorem code_exists (X : Set Nat) (a : Nat) (h : Acc (GraphSyntax.relation_l X) a) :
    ∃ A : CountableGraph.code_l, CountableGraph.real_l A = X ∧ A.root = a := by
  refine ⟨⟨GraphSyntax.relation_l X, a, h⟩, ?_, rfl⟩
  ext n
  change Nat.pair n.unpair.1 n.unpair.2 ∈ X ↔ n ∈ X
  rw [Nat.pair_unpair]

/-- 双排序域量化恰好遍历所有实际图码，无需选择商代表。 -/
private theorem all_target {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (φ : Formula signature_m (.num :: .set :: Γ) Δ) :
    Formula.satisfies η (.forallE .set (.forallE .num
      (.imp (domain_m (.bvar (.there .here)) (.bvar .here)) φ))) ↔
      ∀ A : CountableGraph.code_l,
        Formula.satisfies ((η.pushBound (CountableGraph.real_l A)).pushBound A.root) φ := by
  rw [Formula.satisfies]
  simp_rw [Formula.satisfies, domain_l]
  change (∀ X a, Acc (GraphSyntax.relation_l X) a →
    Formula.satisfies ((η.pushBound X).pushBound a) φ) ↔ _
  constructor
  · intro h A
    apply h (CountableGraph.real_l A) A.root
    rw [GraphDomain.relation_real_l]
    exact A.wf
  · intro h X a h₁
    obtain ⟨A, rfl, rfl⟩ := code_exists X a h₁
    exact h A

private theorem exists_target {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (φ : Formula signature_m (.num :: .set :: Γ) Δ) :
    Formula.satisfies η (.existsE .set (.existsE .num
      (.conj (domain_m (.bvar (.there .here)) (.bvar .here)) φ))) ↔
      ∃ A : CountableGraph.code_l,
        Formula.satisfies ((η.pushBound (CountableGraph.real_l A)).pushBound A.root) φ := by
  rw [Formula.satisfies]
  simp_rw [Formula.satisfies, domain_l]
  change (∃ X a, Acc (GraphSyntax.relation_l X) a ∧
    Formula.satisfies ((η.pushBound X).pushBound a) φ) ↔ _
  constructor
  · rintro ⟨X, a, h, h₁⟩
    obtain ⟨A, rfl, rfl⟩ := code_exists X a h
    exact ⟨A, h₁⟩
  · rintro ⟨A, h⟩
    refine ⟨CountableGraph.real_l A, A.root, ?_, h⟩
    rw [GraphDomain.relation_real_l]
    exact A.wf

private theorem all_source {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ)
    (φ : Formula ℒ (.set :: Γ) Δ) :
    Formula.satisfies (source_l ρ τ) (.forallE .set φ) ↔
      ∀ A, Formula.satisfies (source_l (push_l A ρ) τ) φ := by
  change (∀ a : GraphQuotient.type_l,
    Formula.satisfies ((source_l ρ τ).pushBound a) φ) ↔ _
  simp_rw [source_push_l]
  constructor
  · exact fun h A => h (GraphQuotient.mk_l A)
  · intro h a
    obtain ⟨A, rfl⟩ := GraphQuotient.surj_l a
    exact h A

private theorem exists_source {Γ Δ : SortContext ℒ} (ρ : assignment_l Γ) (τ : assignment_l Δ)
    (φ : Formula ℒ (.set :: Γ) Δ) :
    Formula.satisfies (source_l ρ τ) (.existsE .set φ) ↔
      ∃ A, Formula.satisfies (source_l (push_l A ρ) τ) φ := by
  change (∃ a : GraphQuotient.type_l,
    Formula.satisfies ((source_l ρ τ).pushBound a) φ) ↔ _
  simp_rw [source_push_l]
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨A, rfl⟩ := GraphQuotient.surj_l a
    exact ⟨A, h⟩
  · exact fun ⟨A, h⟩ => ⟨GraphQuotient.mk_l A, h⟩

/-- 实际递归翻译逐公式保持标准真值，包括等词和全部集合量词。 -/
theorem form_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (ρ : assignment_l Γ) (τ : assignment_l Δ) :
    Formula.satisfies (target_l ρ τ) (form_m φ) ↔
      Formula.satisfies (source_l ρ τ) φ := by
  match φ with
  | .falsum => rfl
  | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      rw [form_m, GraphTranslation.mem_l, graph_l, graph_l, root_l, root_l,
        GraphDomain.relation_real_l, GraphDomain.relation_real_l]
      change CountableGraph.mem_l (term_l ρ τ s) (term_l ρ τ t) ↔
        GraphQuotient.mem_l (s.eval (source_l ρ τ)) (t.eval (source_l ρ τ))
      rw [term_eq_l, term_eq_l, GraphQuotient.mem_iff_l]
  | @Formula.equal _ _ _ .set s t =>
      rw [form_m, GraphTranslation.eq_l, graph_l, graph_l, root_l, root_l,
        GraphDomain.relation_real_l, GraphDomain.relation_real_l]
      change CountableGraph.eq_l (term_l ρ τ s) (term_l ρ τ t) ↔
        s.eval (source_l ρ τ) = t.eval (source_l ρ τ)
      rw [term_eq_l, term_eq_l]
      exact (GraphQuotient.eq_iff_l (term_l ρ τ s) (term_l ρ τ t)).symm
  | .neg φ => exact not_congr (form_l φ ρ τ)
  | .conj φ ψ => exact and_congr (form_l φ ρ τ) (form_l ψ ρ τ)
  | .disj φ ψ => exact or_congr (form_l φ ρ τ) (form_l ψ ρ τ)
  | .imp φ ψ => exact imp_congr (form_l φ ρ τ) (form_l ψ ρ τ)
  | .iff φ ψ => exact iff_congr (form_l φ ρ τ) (form_l ψ ρ τ)
  | .forallE .set φ =>
      exact (all_target (target_l ρ τ) (form_m φ)).trans
        ((forall_congr' (fun A => by
          rw [← target_push_l]
          exact form_l φ (push_l A ρ) τ)).trans (all_source ρ τ φ).symm)
  | .existsE .set φ =>
      exact (exists_target (target_l ρ τ) (form_m φ)).trans
        ((exists_congr (fun A => by
          rw [← target_push_l]
          exact form_l φ (push_l A ρ) τ)).trans (exists_source ρ τ φ).symm)
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

/-- 逐变量换为双模拟码不改变源商环境。 -/
theorem source_congr_l {Γ Δ : SortContext ℒ}
    (ρ ρ₁ : assignment_l Γ) (τ τ₁ : assignment_l Δ)
    (hρ : ∀ {s} (v : Variable Γ s), CountableGraph.eq_l (ρ v) (ρ₁ v))
    (hτ : ∀ {s} (v : Variable Δ s), CountableGraph.eq_l (τ v) (τ₁ v)) :
    source_l ρ τ = source_l ρ₁ τ₁ := by
  apply Env.ext
  · intro s v
    exact (GraphQuotient.eq_iff_l (ρ v) (ρ₁ v)).mpr (hρ v)
  · intro s v
    exact (GraphQuotient.eq_iff_l (τ v) (τ₁ v)).mpr (hτ v)

/-- 任意含参数翻译公式的真值在逐变量换码后不变。 -/
theorem congr_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ)
    (ρ ρ₁ : assignment_l Γ) (τ τ₁ : assignment_l Δ)
    (hρ : ∀ {s} (v : Variable Γ s), CountableGraph.eq_l (ρ v) (ρ₁ v))
    (hτ : ∀ {s} (v : Variable Δ s), CountableGraph.eq_l (τ v) (τ₁ v)) :
    Formula.satisfies (target_l ρ τ) (form_m φ) ↔
      Formula.satisfies (target_l ρ₁ τ₁) (form_m φ) := by
  rw [form_l, form_l, source_congr_l ρ ρ₁ τ τ₁ hρ hτ]

end YesMetaZFC.BMS.ConstructibleBridge.GraphInterpretation
