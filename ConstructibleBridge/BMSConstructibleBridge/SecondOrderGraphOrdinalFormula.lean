import BMSConstructibleBridge.SecondOrderFormulaArguments
import BMSConstructibleBridge.PowerlessProjectEnvironment
import YesMetaZFC.SetTheory.Ord.Basic

/-! # 上游实际序数公式的图翻译

直接翻译 Project 的“传递且隶属良序”正文，而不是调用依赖完整收集背景的
相似判据。只有原图商外延性用于两套语法桥，根域作为显式语义证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphOrdinalFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  GraphTranslation.context_m

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def project_m : SetTheory.Definitional.Project.Formula 1 1 :=
  SetTheory.Definitional.Project.Formula.isOrdinal SetTheory.Definitional.Term.newest

open SetTheory.Definitional.Project in
theorem project_closed_m : project_m.FreeClosed := by
  simp [project_m, Formula.isOrdinal, Formula.isTransitive,
    Formula.isWellOrderOn, Formula.isLinearOrderOn, Formula.isStrictPartialOrderOn,
    Formula.isIrreflexiveOn, Formula.isTransitiveOn, Formula.isLeastOf,
    Formula.lessOrEqual, Formula.forallMem, Formula.existsMem, Formula.subset,
    Formula.extensionalEq, Formula.pairArguments, SetTheory.Definitional.Formula.FreeClosed,
    SetTheory.Definitional.TermVector.FreeClosed, SetTheory.Definitional.Term.freeSupport,
    SetTheory.Definitional.TermVector.get, SetTheory.Definitional.Term.newest,
    SetTheory.Definitional.Term.weaken, SetTheory.Definitional.Term.rename, SetTheory.Definitional.Term.bind]

def source_m : Formula ℒ [.set] [] :=
  SetTheory.Definitional.Project.fo_formula project_m project_closed_m

def bind_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) : Substitution signature_m [.num, .set] [] Γ Δ :=
  .map (fun v => match v with | .here => r | .there .here => A) (fun v => nomatch v)

def formula_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  (GraphTranslation.form_m source_m).substitute (bind_m A r)

theorem pure_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (hA : pure_term_m A = true) (hr : pure_term_m r = true) :
    language_m (formula_m A r) = true := by
  refine (SecondOrderSubstitution.form_subst_m (GraphTranslation.form_m source_m) _ _ ?_ ?_).trans
    (GraphTranslation.form_pure_m source_m)
  · intro s v
    match v with
    | .here => exact hr
    | .there .here => exact hA
  · intro s v
    nomatch v

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (A : Term signature_m Γ Δ .set) (r : Term signature_m Γ Δ .num)
    (hA : SecondOrderDomain.wf_l (A.eval η) (r.eval η)) :
    (formula_m A r).satisfies η ↔ SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ ⟨A.eval η, r.eval η, hA⟩) := by
  let C : SecondOrderGraph.code_l ℳ := ⟨A.eval η, r.eval η, hA⟩
  let ρ : SecondOrderInterpretation.assignment_l ℳ [.set] := fun v => match v with | .here => C
  let τ : SecondOrderInterpretation.assignment_l ℳ [] := fun v => nomatch v
  rw [formula_m, Formula.satisfies_substitute]
  have hEnv : Env.pullback η (bind_m A r) = SecondOrderInterpretation.target_l ρ τ := by
    apply Env.ext
    · intro s v
      match v with
      | .here => rfl
      | .there .here => rfl
    · intro s v
      nomatch v
  rw [hEnv, SecondOrderInterpretation.form_l hℳ source_m ρ τ]
  have hExt : SetTheory.Extensional
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) :=
    ⟨SecondOrderQuotient.ext_l hℳ⟩
  exact (SetTheory.Definitional.Project.FirstOrderSemantics.formula_correct hExt project_m project_closed_m
    (SecondOrderInterpretation.source_l hℳ ρ τ) (fun _ => SecondOrderQuotient.mk_l hℳ C)).trans
    (SetTheory.Definitional.Project.Formula.satisfies_isOrdinal_iff _ SetTheory.Definitional.Term.newest)

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphOrdinalFormula
