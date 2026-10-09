import BMSConstructibleBridge.PowerlessRelativeMembershipCollapse
import BMSConstructibleBridge.PowerlessRelativization

/-! # 实际成员坍缩保持任意原公式

对象语言是纯隶属 ℒ，正式出口仍为原 Z₂ 的 GraphTranslation 推导。
两组原环境只通过同一实际 H 的图值联系；量词前进使用真实满射，
量词返回使用真实映射的全域性，不从 Prop 中抽取 Type 层坍缩函数。

模式逐一处理任意外部原公式和任意绑定／自由参数代入，不建立内部
统一真值谓词。这里消费实际坍缩规格；实际壳及其坍缩仍由原构造取得，
本消去规则不是最终源模型存在性或 BMS 良序结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSatisfaction

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 全部原变量属于源域，并由原图联系两侧赋值；域参数不在此关系内。 -/
def env_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} (I H : type_l hℳ)
    (η ξ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) : Prop :=
  (∀ v : Variable Γ .set, mem_l hℳ (η.boundVal v) I ∧
    SecondOrderFunctionObjects.value_l hℳ H (η.boundVal v) (ξ.boundVal v)) ∧
  (∀ v : Variable Δ .set, mem_l hℳ (η.freeVal v) I ∧
    SecondOrderFunctionObjects.value_l hℳ H (η.freeVal v) (ξ.freeVal v))

theorem term_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} {I H : type_l hℳ}
    {η ξ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ}
    (h : env_l hℳ I H η ξ) (t : Term ℒ Γ Δ .set) :
    mem_l hℳ (t.eval η) I ∧ SecondOrderFunctionObjects.value_l hℳ H (t.eval η) (t.eval ξ) := by
  match t with
  | .bvar v => exact h.1 v
  | .fvar v => exact h.2 v
  | .app f _ => nomatch f

theorem push_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} {I H x y : type_l hℳ}
    {η ξ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ}
    (h : env_l hℳ I H η ξ) (hx : mem_l hℳ x I)
    (hxy : SecondOrderFunctionObjects.value_l hℳ H x y) :
    env_l hℳ I H (η.pushBound (sort := SetTheory.SetSort.set) x)
      (ξ.pushBound (sort := SetTheory.SetSort.set) y) := by
  refine ⟨?_, h.2⟩
  intro v
  cases v with
  | here => exact ⟨hx, hxy⟩
  | there v => exact h.1 v

/-- 任意原公式的相对化真值沿同一实际坍缩图双向保持。 -/
theorem formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) {I T H : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l (hℳ := hℳ) I T H)
    (η ξ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (h : env_l hℳ I H η ξ) :
    (PowerlessRelativization.formula_m φ).satisfies (η.pushFree I) ↔
      (PowerlessRelativization.formula_m φ).satisfies (ξ.pushFree T) := by
  match φ with
  | .falsum => rfl
  | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      change mem_l hℳ ((s.weakenFree SetTheory.SetSort.set).eval (η.pushFree I))
          ((t.weakenFree SetTheory.SetSort.set).eval (η.pushFree I)) ↔
        mem_l hℳ ((s.weakenFree SetTheory.SetSort.set).eval (ξ.pushFree T))
          ((t.weakenFree SetTheory.SetSort.set).eval (ξ.pushFree T))
      simp only [Term.eval_weakenFree]
      exact hH.2.2.2.2.2 _ _ _ _ (term_l hℳ h s).1 (term_l hℳ h t).1
        (term_l hℳ h s).2 (term_l hℳ h t).2
  | .equal (sort := SetTheory.SetSort.set) s t =>
      change (s.weakenFree SetTheory.SetSort.set).eval (η.pushFree I) =
          (t.weakenFree SetTheory.SetSort.set).eval (η.pushFree I) ↔
        (s.weakenFree SetTheory.SetSort.set).eval (ξ.pushFree T) =
          (t.weakenFree SetTheory.SetSort.set).eval (ξ.pushFree T)
      simp only [Term.eval_weakenFree]
      have hs := (term_l hℳ h s).2
      have ht := (term_l hℳ h t).2
      constructor
      · intro hst
        exact SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hs (hst.symm ▸ ht)
      · intro hst
        exact hH.2.2.2.2.1 _ _ _ hs (hst.symm ▸ ht)
  | .neg φ => exact not_congr (formula_l hℳ φ hH η ξ h)
  | .conj φ ψ => exact and_congr (formula_l hℳ φ hH η ξ h) (formula_l hℳ ψ hH η ξ h)
  | .disj φ ψ => exact or_congr (formula_l hℳ φ hH η ξ h) (formula_l hℳ ψ hH η ξ h)
  | .imp φ ψ => exact imp_congr (formula_l hℳ φ hH η ξ h) (formula_l hℳ ψ hH η ξ h)
  | .iff φ ψ => exact iff_congr (formula_l hℳ φ hH η ξ h) (formula_l hℳ ψ hH η ξ h)
  | .forallE .set φ =>
      change (∀ x : type_l hℳ, mem_l hℳ x I →
        (PowerlessRelativization.formula_m φ).satisfies ((η.pushFree I).pushBound x)) ↔
        ∀ y : type_l hℳ, mem_l hℳ y T →
          (PowerlessRelativization.formula_m φ).satisfies ((ξ.pushFree T).pushBound y)
      constructor
      · intro hφ y hy
        obtain ⟨x, hx, hxy⟩ := hH.2.2.1 y hy
        exact (formula_l hℳ φ hH (η.pushBound x) (ξ.pushBound y)
          (push_l hℳ h hx hxy)).mp (hφ x hx)
      · intro hφ x hx
        obtain ⟨y, hy, _⟩ := hH.2.1.2 x hx
        exact (formula_l hℳ φ hH (η.pushBound x) (ξ.pushBound y)
          (push_l hℳ h hx hy.2)).mpr (hφ y hy.1)
  | .existsE .set φ =>
      change (∃ x : type_l hℳ, mem_l hℳ x I ∧
        (PowerlessRelativization.formula_m φ).satisfies ((η.pushFree I).pushBound x)) ↔
        ∃ y : type_l hℳ, mem_l hℳ y T ∧
          (PowerlessRelativization.formula_m φ).satisfies ((ξ.pushFree T).pushBound y)
      constructor
      · rintro ⟨x, hx, hφ⟩
        obtain ⟨y, hy, _⟩ := hH.2.1.2 x hx
        exact ⟨y, hy.1, (formula_l hℳ φ hH (η.pushBound x) (ξ.pushBound y)
          (push_l hℳ h hx hy.2)).mp hφ⟩
      · rintro ⟨y, hy, hφ⟩
        obtain ⟨x, hx, hxy⟩ := hH.2.2.1 y hy
        exact ⟨x, hx, (formula_l hℳ φ hH (η.pushBound x) (ξ.pushBound y)
          (push_l hℳ h hx hxy)).mpr hφ⟩

/-- 有限变量槽的源域资格及同一图值关系，保留空上下文。 -/
def assignment_m {Θ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (I H : Term ℒ Θ Ε .set) (σ τ : Variable Δ .set → Term ℒ Θ Ε .set) : Formula ℒ Θ Ε :=
  match Δ with
  | [] => .truth
  | .set :: Δ => .conj (.conj (SecondOrderObjectSyntax.member_m (σ .here) I)
      (SecondOrderObjectSyntax.value_m H (σ .here) (τ .here)))
      (assignment_m Δ I H (fun v => σ (.there v)) (fun v => τ (.there v)))

theorem assignment_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) Θ Ε)
    (I H : Term ℒ Θ Ε .set) (σ τ : Variable Δ .set → Term ℒ Θ Ε .set) :
    (assignment_m Δ I H σ τ).satisfies ζ ↔ ∀ v : Variable Δ .set,
      mem_l hℳ ((σ v).eval ζ) (I.eval ζ) ∧
        SecondOrderFunctionObjects.value_l hℳ (H.eval ζ) ((σ v).eval ζ) ((τ v).eval ζ) := by
  induction Δ with
  | nil =>
      constructor
      · intro _ v; nomatch v
      · intro _; trivial
  | cons s Δ ih =>
      cases s
      simp only [assignment_m, Formula.satisfies, SecondOrderObjectSyntax.value_l, ih]
      constructor
      · rintro ⟨h₀, h₁⟩ v
        cases v with
        | here => exact h₀
        | there v => exact h₁ v
      · intro h
        exact ⟨h .here, fun v => h (.there v)⟩

def binding_m {Γ Δ Θ : SortContext ℒ} (A : Term ℒ [] Θ .set)
    (ρ : Variable Γ .set → Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    Substitution ℒ Γ (.set :: Δ) [] Θ :=
  .map (fun {s} v => match s with | .set => ρ v)
    (fun {s} v => match s with | .set => match v with | .here => A | .there v => τ v)

def instance_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (A : Term ℒ [] Θ .set)
    (ρ : Variable Γ .set → Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  (PowerlessRelativization.formula_m φ).substitute (binding_m A ρ τ)

theorem instance_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ζ : Env 𝒩 [] Θ) (A : Term ℒ [] Θ .set)
    (ρ : Variable Γ .set → Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set)
    (η : Env 𝒩 Γ Δ) (hρ : ∀ v, (ρ v).eval ζ = η.boundVal v)
    (hτ : ∀ v, (τ v).eval ζ = η.freeVal v) :
    (instance_m φ A ρ τ).satisfies ζ ↔
      (PowerlessRelativization.formula_m φ).satisfies (η.pushFree (A.eval ζ)) := by
  rw [instance_m, Formula.satisfies_substitute]
  have h : ζ.pullback (binding_m A ρ τ) = η.pushFree (A.eval ζ) := by
    apply Env.ext
    · intro s v
      cases s
      exact hρ v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => exact hτ v
  rw [h]

def schema_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (I T H : Term ℒ [] Θ .set)
    (ρ₀ ρ₁ : Variable Γ .set → Term ℒ [] Θ .set)
    (τ₀ τ₁ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
    .imp (assignment_m Γ I H ρ₀ ρ₁) <| .imp (assignment_m Δ I H τ₀ τ₁) <|
      .iff (instance_m φ I ρ₀ τ₀) (instance_m φ T ρ₁ τ₁)

def sentence_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (I T H : Term ℒ [] Θ .set)
    (ρ₀ ρ₁ : Variable Γ .set → Term ℒ [] Θ .set)
    (τ₀ τ₁ : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ I T H ρ₀ ρ₁ τ₀ τ₁)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (I T H : Term ℒ [] Θ .set)
    (ρ₀ ρ₁ : Variable Γ .set → Term ℒ [] Θ .set)
    (τ₀ τ₁ : Variable Δ .set → Term ℒ [] Θ .set) :
    (sentence_m φ I T H ρ₀ ρ₁ τ₀ τ₁).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ hH hρ hτ
  let η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ :=
    { boundVal := fun {s} v => match s with | .set => (ρ₀ v).eval ζ
      freeVal := fun {s} v => match s with | .set => (τ₀ v).eval ζ }
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ :=
    { boundVal := fun {s} v => match s with | .set => (ρ₁ v).eval ζ
      freeVal := fun {s} v => match s with | .set => (τ₁ v).eval ζ }
  have h : env_l hℳ (I.eval ζ) (H.eval ζ) η ξ :=
    ⟨(assignment_formula_l hℳ Γ ζ I H ρ₀ ρ₁).mp hρ,
      (assignment_formula_l hℳ Δ ζ I H τ₀ τ₁).mp hτ⟩
  exact (instance_formula_l φ ζ I ρ₀ τ₀ η (fun _ => rfl) (fun _ => rfl)).trans
    ((formula_l hℳ φ ((PowerlessRelativeMembershipCollapse.spec_formula_l ζ I T H).mp hH)
      η ξ h).trans (instance_formula_l φ ζ T ρ₁ τ₁ ξ (fun _ => rfl) (fun _ => rfl)).symm)

/-- 每个原公式实例在原推导核中可推导，不假定模型外部良基。 -/
theorem derives_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (I T H : Term ℒ [] Θ .set)
    (ρ₀ ρ₁ : Variable Γ .set → Term ℒ [] Θ .set)
    (τ₀ τ₁ : Variable Δ .set → Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ I T H ρ₀ ρ₁ τ₀ τ₁)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ I T H ρ₀ ρ₁ τ₀ τ₁)

#print axioms formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSatisfaction
