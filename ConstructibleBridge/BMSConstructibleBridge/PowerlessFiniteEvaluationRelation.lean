import BMSConstructibleBridge.PowerlessFiniteEvaluationQueryGraph

/-! # ω × 有限赋值集上的实际求值关系图

固定所有类内静态参数后取得集合关系，规格在类内和全部原商输入上
分别成立。存在句回到原 Z₂；参数的实际序列及编码规格仍由调用者构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationRelation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω e N T A S t₁ t₂ t₃ Q G : carrier_l 𝒩) : Prop :=
  ∀ n f, value_l G n f ↔ member_l 𝒩 n ω ∧ member_l 𝒩 f S ∧
    PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q n f

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def spec_m {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .forallE .set <| .forallE .set <|
    let n : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let f : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    .iff (SecondOrderObjectSyntax.value_m (w G) n f) <|
      .conj (SecondOrderObjectSyntax.member_m n (w ω)) <|
        .conj (SecondOrderObjectSyntax.member_m f (w S))
          (PowerlessFiniteEvaluationQuery.formula_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S)
            (w t₁) (w t₂) (w t₃) (w Q) n f)

theorem spec_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e N T A S t₁ t₂ t₃ Q G : Term ℒ Γ Δ .set) :
    (spec_m C ω e N T A S t₁ t₂ t₃ Q G).satisfies η ↔
      spec_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (Q.eval η) (G.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, value_formula_l, PowerlessFiniteEvaluationQuery.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    ∃ G : type_l hℳ B, spec_l (𝒩 := structure_l hℳ B hBase)
      (C.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (Q.eval η) G := by
  obtain ⟨G, hG⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (PowerlessFiniteEvaluationQueryGraph.matrix_delta_l C ω e N T A S t₁ t₂ t₃ Q) η (ω.eval η) (S.eval η)
  exact ⟨G, fun n f => (hG n f).trans (and_congr Iff.rfl (and_congr Iff.rfl
    (PowerlessFiniteEvaluationQueryGraph.matrix_formula_l η C ω e N T A S t₁ t₂ t₃ Q n f)))⟩

theorem exists_ambient_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    let ρ := PowerlessRelativeClassRelativization.env_l η
    ∃ G : type_l hℳ B, spec_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      (C.eval ρ) (ω.eval ρ) (e.eval ρ) (N.eval ρ) (T.eval ρ) (A.eval ρ) (S.eval ρ)
        (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) (Q.eval ρ) G.val := by
  obtain ⟨G, hG⟩ := PowerlessFiniteEvaluationQueryGraph.exists_ambient_l η C ω e N T A S t₁ t₂ t₃ Q
    (ω.eval η) (S.eval η)
  have hEval (t : Term ℒ [] Δ .set) : (t.eval η).val = t.eval (PowerlessRelativeClassRelativization.env_l η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar _ => rfl
    | .app f _ => nomatch f
  refine ⟨G, ?_⟩
  simpa only [spec_l, hEval, ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using hG

def schema_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set (spec_m (up C) (up ω) (up e) (up N) (up T) (up A) (up S)
    (up t₁) (up t₂) (up t₃) (up Q) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m C ω e N T A S t₁ t₂ t₃ Q)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) {Δ : SortContext ℒ}
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    (sentence_m C ω e N T A S t₁ t₂ t₃ Q).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, spec_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact exists_l η C ω e N T A S t₁ t₂ t₃ Q

theorem derives_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m
      (PowerlessRelativeClassRelativization.guarded_m (sentence_m C ω e N T A S t₁ t₂ t₃ Q))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase =>
    models_l hℳ B hBase C ω e N T A S t₁ t₂ t₃ Q)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationRelation
