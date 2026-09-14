import BMSConstructibleBridge.SecondOrderQuotient
import BMSConstructibleBridge.GraphTranslation

/-!
# 任意二阶模型中的完整图码公式解释

复用原翻译，不改变等词、成员、变量展开或域限制。数、实数、双模拟见证和
下降链都在指定模型内量化；量词覆盖内部根域代码及其商的全部元素。
本文件不是全部 TMC 公理验证，也不把语义等价报告为已经编码的对象证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInterpretation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic GraphTranslation

set_option autoImplicit false

universe u

abbrev assignment_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m) (Γ : SortContext ℒ) :=
  ∀ {s}, Variable Γ s → SecondOrderGraph.code_l ℳ

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def push_l {Γ : SortContext ℒ} (A : SecondOrderGraph.code_l ℳ) (ρ : assignment_l ℳ Γ) :
    assignment_l ℳ (.set :: Γ)
  | _, .here => A
  | _, .there v => ρ v

def values_l : {Γ : SortContext ℒ} → assignment_l ℳ Γ → Assignment ℳ (context_m Γ)
  | List.nil, _ => Assignment.empty
  | .set :: Γ, ρ => Assignment.push (M := ℳ) (sort := .num) (ρ .here).root
      (Assignment.push (M := ℳ) (sort := .set) (ρ .here).real
        (values_l (Γ := Γ) (fun v => ρ (.there v))))

def target_l {Γ Δ : SortContext ℒ} (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) :
    Env ℳ (context_m Γ) (context_m Δ) := ⟨values_l ρ, values_l τ⟩

def source_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) :
    Env (SecondOrderQuotient.structure_l hℳ) Γ Δ :=
  ⟨fun v => SecondOrderQuotient.mk_l hℳ (ρ v), fun v => SecondOrderQuotient.mk_l hℳ (τ v)⟩

theorem target_push_l {Γ Δ : SortContext ℒ} (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ)
    (A : SecondOrderGraph.code_l ℳ) : target_l (push_l A ρ) τ =
      ((target_l ρ τ).pushBound A.real).pushBound A.root := rfl

theorem source_push_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) (A : SecondOrderGraph.code_l ℳ) :
    source_l hℳ (push_l A ρ) τ =
      (source_l hℳ ρ τ).pushBound (SecondOrderQuotient.mk_l hℳ A) := by
  apply Env.ext
  · intro s v
    cases v <;> rfl
  · intro s v
    rfl

theorem root_var_l : {Γ : SortContext ℒ} → (ρ : assignment_l ℳ Γ) →
    (v : Variable Γ .set) → values_l ρ (root_var_m v) = (ρ v).root
  | .set :: _, _, .here => rfl
  | .set :: _, ρ, .there v => root_var_l (fun v => ρ (.there v)) v

theorem graph_var_l : {Γ : SortContext ℒ} → (ρ : assignment_l ℳ Γ) →
    (v : Variable Γ .set) → values_l ρ (graph_var_m v) = (ρ v).real
  | .set :: _, _, .here => rfl
  | .set :: _, ρ, .there v => graph_var_l (fun v => ρ (.there v)) v

def term_l {Γ Δ : SortContext ℒ} (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) :
    Term ℒ Γ Δ .set → SecondOrderGraph.code_l ℳ
  | .bvar v => ρ v
  | .fvar v => τ v
  | .app f _ => nomatch f

theorem root_l {Γ Δ : SortContext ℒ} (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ)
    (s : Term ℒ Γ Δ .set) : (root_m s).eval (target_l ρ τ) = (term_l ρ τ s).root := by
  match s with
  | .bvar v => exact root_var_l ρ v
  | .fvar v => exact root_var_l τ v
  | .app f _ => nomatch f

theorem graph_l {Γ Δ : SortContext ℒ} (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ)
    (s : Term ℒ Γ Δ .set) : (graph_m s).eval (target_l ρ τ) = (term_l ρ τ s).real := by
  match s with
  | .bvar v => exact graph_var_l ρ v
  | .fvar v => exact graph_var_l τ v
  | .app f _ => nomatch f

theorem term_eq_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) (s : Term ℒ Γ Δ .set) :
    s.eval (source_l hℳ ρ τ) = SecondOrderQuotient.mk_l hℳ (term_l ρ τ s) := by
  match s with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem domain_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (X : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num) :
    Formula.satisfies η (domain_m X a) ↔ SecondOrderDomain.wf_l (X.eval η) (a.eval η) := by
  rw [domain_m, Formula.satisfies_substitute, SecondOrderDomain.formula_l]
  rfl

theorem eq_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (X Y : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (atom_m GraphSyntax.eq_m X Y a b) ↔
      SecondOrderBisimulation.eq_l (X.eval η) (Y.eval η) (a.eval η) (b.eval η) := by
  rw [atom_m, Formula.satisfies_substitute, SecondOrderBisimulation.eq_formula_l]
  rfl

theorem mem_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (X Y : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (atom_m GraphSyntax.mem_m X Y a b) ↔
      ∃ c, SecondOrderPairing.relation_l (Y.eval η) c (b.eval η) ∧
        SecondOrderBisimulation.eq_l (X.eval η) (Y.eval η) (a.eval η) c := by
  rw [atom_m, Formula.satisfies_substitute, SecondOrderBisimulation.mem_formula_l]
  rfl

private theorem all_target {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m (.num :: .set :: Γ) Δ) :
    Formula.satisfies η (.forallE .set (.forallE .num
      (.imp (domain_m (.bvar (.there .here)) (.bvar .here)) φ))) ↔
      ∀ A : SecondOrderGraph.code_l ℳ,
        Formula.satisfies ((η.pushBound A.real).pushBound A.root) φ := by
  rw [Formula.satisfies]
  simp_rw [Formula.satisfies, domain_l]
  change (∀ X a, SecondOrderDomain.wf_l X a →
    Formula.satisfies ((η.pushBound X).pushBound a) φ) ↔ _
  exact ⟨fun h A => h A.real A.root A.wf, fun h X a h₁ => h ⟨X, a, h₁⟩⟩

private theorem exists_target {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m (.num :: .set :: Γ) Δ) :
    Formula.satisfies η (.existsE .set (.existsE .num
      (.conj (domain_m (.bvar (.there .here)) (.bvar .here)) φ))) ↔
      ∃ A : SecondOrderGraph.code_l ℳ,
        Formula.satisfies ((η.pushBound A.real).pushBound A.root) φ := by
  rw [Formula.satisfies]
  simp_rw [Formula.satisfies, domain_l]
  change (∃ X a, SecondOrderDomain.wf_l X a ∧
    Formula.satisfies ((η.pushBound X).pushBound a) φ) ↔ _
  exact ⟨fun ⟨X, a, h, h₁⟩ => ⟨⟨X, a, h⟩, h₁⟩,
    fun ⟨A, h⟩ => ⟨A.real, A.root, A.wf, h⟩⟩

private theorem all_source (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) (φ : Formula ℒ (.set :: Γ) Δ) :
    Formula.satisfies (source_l hℳ ρ τ) (.forallE .set φ) ↔
      ∀ A, Formula.satisfies (source_l hℳ (push_l A ρ) τ) φ := by
  change (∀ a : SecondOrderQuotient.type_l hℳ,
    Formula.satisfies ((source_l hℳ ρ τ).pushBound a) φ) ↔ _
  simp_rw [source_push_l]
  constructor
  · exact fun h A => h (SecondOrderQuotient.mk_l hℳ A)
  · intro h a
    obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
    exact h A

private theorem exists_source (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) (φ : Formula ℒ (.set :: Γ) Δ) :
    Formula.satisfies (source_l hℳ ρ τ) (.existsE .set φ) ↔
      ∃ A, Formula.satisfies (source_l hℳ (push_l A ρ) τ) φ := by
  change (∃ a : SecondOrderQuotient.type_l hℳ,
    Formula.satisfies ((source_l hℳ ρ τ).pushBound a) φ) ↔ _
  simp_rw [source_push_l]
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
    exact ⟨A, h⟩
  · exact fun ⟨A, h⟩ => ⟨SecondOrderQuotient.mk_l hℳ A, h⟩

/-- 原递归翻译的任意模型真值定理；覆盖所有原公式、绑定及自由参数。 -/
theorem form_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ Γ Δ) (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ) :
    Formula.satisfies (target_l ρ τ) (form_m φ) ↔
      Formula.satisfies (source_l hℳ ρ τ) φ := by
  match φ with
  | .falsum => rfl
  | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      rw [form_m, mem_l, graph_l, graph_l, root_l, root_l]
      change SecondOrderGraph.mem_l (term_l ρ τ s) (term_l ρ τ t) ↔
        SecondOrderQuotient.mem_l hℳ (s.eval (source_l hℳ ρ τ)) (t.eval (source_l hℳ ρ τ))
      rw [term_eq_l, term_eq_l, SecondOrderQuotient.mem_iff_l]
  | @Formula.equal _ _ _ .set s t =>
      rw [form_m, eq_l, graph_l, graph_l, root_l, root_l]
      change SecondOrderGraph.eq_l (term_l ρ τ s) (term_l ρ τ t) ↔
        s.eval (source_l hℳ ρ τ) = t.eval (source_l hℳ ρ τ)
      rw [term_eq_l, term_eq_l]
      exact (SecondOrderQuotient.eq_iff_l hℳ (term_l ρ τ s) (term_l ρ τ t)).symm
  | .neg φ => exact not_congr (form_l hℳ φ ρ τ)
  | .conj φ ψ => exact and_congr (form_l hℳ φ ρ τ) (form_l hℳ ψ ρ τ)
  | .disj φ ψ => exact or_congr (form_l hℳ φ ρ τ) (form_l hℳ ψ ρ τ)
  | .imp φ ψ => exact imp_congr (form_l hℳ φ ρ τ) (form_l hℳ ψ ρ τ)
  | .iff φ ψ => exact iff_congr (form_l hℳ φ ρ τ) (form_l hℳ ψ ρ τ)
  | .forallE .set φ =>
      exact (all_target (target_l ρ τ) (form_m φ)).trans
        ((forall_congr' (fun A => by
          rw [← target_push_l]
          exact form_l hℳ φ (push_l A ρ) τ)).trans (all_source hℳ ρ τ φ).symm)
  | .existsE .set φ =>
      exact (exists_target (target_l ρ τ) (form_m φ)).trans
        ((exists_congr (fun A => by
          rw [← target_push_l]
          exact form_l hℳ φ (push_l A ρ) τ)).trans (exists_source hℳ ρ τ φ).symm)
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

theorem source_congr_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (ρ ρ₁ : assignment_l ℳ Γ) (τ τ₁ : assignment_l ℳ Δ)
    (hρ : ∀ {s} (v : Variable Γ s), SecondOrderGraph.eq_l (ρ v) (ρ₁ v))
    (hτ : ∀ {s} (v : Variable Δ s), SecondOrderGraph.eq_l (τ v) (τ₁ v)) :
    source_l hℳ ρ τ = source_l hℳ ρ₁ τ₁ := by
  apply Env.ext
  · intro s v
    exact (SecondOrderQuotient.eq_iff_l hℳ (ρ v) (ρ₁ v)).mpr (hρ v)
  · intro s v
    exact (SecondOrderQuotient.eq_iff_l hℳ (τ v) (τ₁ v)).mpr (hτ v)

theorem congr_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ Γ Δ) (ρ ρ₁ : assignment_l ℳ Γ) (τ τ₁ : assignment_l ℳ Δ)
    (hρ : ∀ {s} (v : Variable Γ s), SecondOrderGraph.eq_l (ρ v) (ρ₁ v))
    (hτ : ∀ {s} (v : Variable Δ s), SecondOrderGraph.eq_l (τ v) (τ₁ v)) :
    Formula.satisfies (target_l ρ τ) (form_m φ) ↔
      Formula.satisfies (target_l ρ₁ τ₁) (form_m φ) := by
  rw [form_l hℳ, form_l hℳ, source_congr_l hℳ ρ ρ₁ τ τ₁ hρ hτ]

/-- 指定源环境可逐变量选取代码代表；不固定所有商元素的全局代表函数。 -/
theorem source_surj_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) :
    ∃ (ρ : assignment_l ℳ Γ) (τ : assignment_l ℳ Δ), source_l hℳ ρ τ = η := by
  classical
  let ρ : assignment_l ℳ Γ := fun v => (SecondOrderQuotient.surj_l hℳ (η.boundVal v)).choose
  let τ : assignment_l ℳ Δ := fun v => (SecondOrderQuotient.surj_l hℳ (η.freeVal v)).choose
  refine ⟨ρ, τ, ?_⟩
  apply Env.ext
  · intro s v
    exact (SecondOrderQuotient.surj_l hℳ (η.boundVal v)).choose_spec
  · intro s v
    exact (SecondOrderQuotient.surj_l hℳ (η.freeVal v)).choose_spec

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderInterpretation
