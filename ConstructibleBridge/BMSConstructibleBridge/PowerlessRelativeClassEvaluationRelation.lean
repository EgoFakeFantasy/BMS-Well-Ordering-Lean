import BMSConstructibleBridge.PowerlessRelativeClassEvaluationAbsolute

/-! # 带实际逻辑方程的类内集合求值关系

同一个集合图同时满足逐值规格与四分支方程，原商出口还保留类内方程。
此处消去调用者预设的图，仍显式消费序列规格及已证稳定查询方程；
完整公式编译、反射及 Collection 不包含在本模块的结论中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationRelation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) (ω.eval η) (A.eval η) (S.eval η))
    (hQ : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) (ω.eval η) (C.eval η) (Q.eval η))
    (hEquation : PowerlessFiniteEvaluationEquations.equations_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η)
      (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)) :
    ∃ G : type_l hℳ B, PowerlessFiniteEvaluationRelation.spec_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η)
      (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Q.eval η) G ∧
      PowerlessFiniteEvaluationRelationEquations.equations_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
        (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) G := by
  obtain ⟨G, hG⟩ := PowerlessFiniteEvaluationRelation.exists_l η C ω e N T A S t₁ t₂ t₃ Q
  exact ⟨G, hG, PowerlessFiniteEvaluationRelationEquations.equations_of_query_l hG hS hQ hEquation⟩

theorem exists_ambient_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set)
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval (PowerlessRelativeClassRelativization.env_l η)))
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval (PowerlessRelativeClassRelativization.env_l η)) (A.eval (PowerlessRelativeClassRelativization.env_l η))
      (S.eval (PowerlessRelativeClassRelativization.env_l η)))
    (hQ : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval (PowerlessRelativeClassRelativization.env_l η)) (C.eval (PowerlessRelativeClassRelativization.env_l η))
      (Q.eval (PowerlessRelativeClassRelativization.env_l η)))
    (hEquation : let ρ := PowerlessRelativeClassRelativization.env_l η
      PowerlessFiniteEvaluationEquations.equations_l (C.eval ρ) (ω.eval ρ) (e.eval ρ) (N.eval ρ)
        (T.eval ρ) (A.eval ρ) (S.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ)) :
    let ρ := PowerlessRelativeClassRelativization.env_l η
    ∃ G : type_l hℳ B, PowerlessFiniteEvaluationRelation.spec_l (C.eval ρ) (ω.eval ρ) (e.eval ρ) (N.eval ρ)
      (T.eval ρ) (A.eval ρ) (S.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) (Q.eval ρ) G.val ∧
      PowerlessFiniteEvaluationRelationEquations.equations_l (ω.eval ρ) (e.eval ρ) (T.eval ρ) (A.eval ρ)
        (S.eval ρ) (t₁.eval ρ) (t₂.eval ρ) (t₃.eval ρ) G.val ∧
      PowerlessFiniteEvaluationRelationEquations.equations_l (𝒩 := structure_l hℳ B hBase)
        (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) G := by
  obtain ⟨G, hG⟩ := PowerlessFiniteEvaluationRelation.exists_ambient_l η C ω e N T A S t₁ t₂ t₃ Q
  have hEquations := PowerlessFiniteEvaluationRelationEquations.equations_of_query_l hG hS hQ hEquation
  refine ⟨G, hG, hEquations, ?_⟩
  have hEval (t : Term ℒ [] Δ .set) : (t.eval η).val = t.eval (PowerlessRelativeClassRelativization.env_l η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar _ => rfl
    | .app f _ => nomatch f
  apply PowerlessRelativeClassEvaluationAbsolute.equations_l (ω.eval η) (e.eval η) (T.eval η)
    (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) G
  · simpa only [hEval] using hω
  · simpa only [hEval] using hS
  · simpa only [hEval] using hEquations

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
    .imp (PowerlessFiniteSequencesSyntax.spec_m ω C Q) <|
      .imp (PowerlessFiniteEvaluationEquations.equations_m C ω e N T A S t₁ t₂ t₃) <|
        .existsE .set <| .conj
          (PowerlessFiniteEvaluationRelation.spec_m (up C) (up ω) (up e) (up N) (up T) (up A) (up S)
            (up t₁) (up t₂) (up t₃) (up Q) (.bvar .here))
          (PowerlessFiniteEvaluationRelationEquations.equations_m (up ω) (up e) (up T) (up A) (up S)
            (up t₁) (up t₂) (up t₃) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m C ω e N T A S t₁ t₂ t₃ Q)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) {Δ : SortContext ℒ}
    (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    (sentence_m C ω e N T A S t₁ t₂ t₃ Q).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessFiniteEvaluationEquations.equations_formula_l, PowerlessFiniteEvaluationRelation.spec_formula_l,
    PowerlessFiniteEvaluationRelationEquations.equations_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hS hQ hEquation => exists_l η C ω e N T A S t₁ t₂ t₃ Q hS hQ hEquation

theorem derives_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m
      (PowerlessRelativeClassRelativization.guarded_m (sentence_m C ω e N T A S t₁ t₂ t₃ Q))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase =>
    models_l hℳ B hBase C ω e N T A S t₁ t₂ t₃ Q)

#print axioms exists_ambient_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationRelation
