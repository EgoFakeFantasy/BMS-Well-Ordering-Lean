import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.MinimumLength
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.StandardOpening

/-!
# 公式码最小长度的闭包汇总

本模块把各构造分支的前两位反演汇总到 `FormulaCodeₘ` 的一步生成关系，再在对象逻辑
内部全称化。公开接口因此只要求代码项 admissible，不暴露实现定义占用的保留编号。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

private theorem gq_formula_minimum_closure_theory_fresh
    (id : FreeVarId) :
    ∀ formula, godel_quotation_theory formula →
      (SetSort.set, id) ∉
        Formula.freeSupport formula := by
  intro formula hFormula
  rw [(godel_quotation_theory_sentence hFormula).2]
  exact List.not_mem_nil

/-- 一步公式生成的四个分支统一给出第零位。 -/
theorem
    gq_formula_code_generation_implies_zero_mem_domain_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310]
        [code]) :
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition FormulaCodeₘ code ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(code)) := by
  have hGenerationAdmissible :
      Formula.Admissible
        (formula_code_generation_condition
          FormulaCodeₘ code) := by
    unfold formula_code_generation_condition
    prove_admissible
  have hAtomicFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl <;> simp
  have hImplicationFresh :
      ReservedIdsFresh [307, 308] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl <;> simp
  have hUniversalFresh :
      ReservedIdsFresh [309, 310] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl <;> simp
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [formula_code_generation_condition
      FormulaCodeₘ code]
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hGenerationAdmissible)
  unfold formula_code_generation_condition at hGeneration
  apply FirstOrder.Derives.disjElim hGeneration
  · let Δ : Context signature :=
      (code ∈ₘ AtomicCodeₘ) :: Γ
    have hMinimum :
        Δ ⊢ₘ[godel_quotation_theory]
          formula_code_minimum_domain_condition code :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_atomic_formula_member_implies_minimum_domain_of_fresh
              code hCode hAtomicFresh)
        (FirstOrder.Derives.assumption (by simp [Δ]))
    exact FirstOrder.Derives.conjElimLeft hMinimum
  · let tail : SetFormula :=
      (∃ₘ[SetSort.set, 306],
        ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
          (code ≐ₘ neg_codeₘ(x#306)))) ∨ₘ
      ((∃ₘ[SetSort.set, 307],
        ∃ₘ[SetSort.set, 308],
          (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
            (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (code ≐ₘ imp_codeₘ(x#307, x#308)))) ∨ₘ
        (∃ₘ[SetSort.set, 309],
          ∃ₘ[SetSort.set, 310],
            (((x#309 ∈ₘ VarSymₘ) ∧ₘ
              (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
              (code ≐ₘ
                forall_codeₘ(x#309, x#310)))))
    let Δ : Context signature := tail :: Γ
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory] tail :=
      FirstOrder.Derives.assumption (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTail
    · let negation : SetFormula :=
        ∃ₘ[SetSort.set, 306],
          ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
            (code ≐ₘ neg_codeₘ(x#306)))
      let Ε : Context signature := negation :: Δ
      have hMinimum :
          Ε ⊢ₘ[godel_quotation_theory]
            formula_code_minimum_domain_condition code :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp [Ε, negation]) <|
              gq_negation_generation_implies_minimum_domain
                code hCode
                (hFresh code (by simp) 306 (by simp)))
          (FirstOrder.Derives.assumption
            (by simp [Ε, negation]))
      exact FirstOrder.Derives.conjElimLeft hMinimum
    · let rest : SetFormula :=
        (∃ₘ[SetSort.set, 307],
          ∃ₘ[SetSort.set, 308],
            (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
              (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
              (code ≐ₘ imp_codeₘ(x#307, x#308)))) ∨ₘ
          (∃ₘ[SetSort.set, 309],
            ∃ₘ[SetSort.set, 310],
              (((x#309 ∈ₘ VarSymₘ) ∧ₘ
                (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
                (code ≐ₘ
                  forall_codeₘ(x#309, x#310))))
      let Ε : Context signature := rest :: Δ
      have hRest :
          Ε ⊢ₘ[godel_quotation_theory] rest :=
        FirstOrder.Derives.assumption (by simp [Ε])
      apply FirstOrder.Derives.disjElim hRest
      · let implication : SetFormula :=
          ∃ₘ[SetSort.set, 307],
            ∃ₘ[SetSort.set, 308],
              (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
                (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
                (code ≐ₘ imp_codeₘ(x#307, x#308)))
        let Ζ : Context signature := implication :: Ε
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ζ)
            (by simp) <|
              gq_implication_generation_implies_zero_domain
                code hCode hImplicationFresh)
          (FirstOrder.Derives.assumption
            (T := godel_quotation_theory)
            (Γ := Ζ) (φ := implication)
            List.mem_cons_self)
      · let universal : SetFormula :=
          ∃ₘ[SetSort.set, 309],
            ∃ₘ[SetSort.set, 310],
              (((x#309 ∈ₘ VarSymₘ) ∧ₘ
                (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
                (code ≐ₘ
                  forall_codeₘ(x#309, x#310)))
        let Ζ : Context signature := universal :: Ε
        have hMinimum :
            Ζ ⊢ₘ[godel_quotation_theory]
              formula_code_minimum_domain_condition code :=
          FirstOrder.Derives.impElim
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ)
              (by simp [Ζ, universal]) <|
                gq_universal_generation_implies_minimum_domain
                  code hCode hUniversalFresh)
            (FirstOrder.Derives.assumption
              (by simp [Ζ, universal]))
        exact FirstOrder.Derives.conjElimLeft hMinimum

/-- 完整公式码成员经生成反演给出第零位。 -/
theorem
    gq_formula_code_member_implies_zero_mem_domain_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310, 600]
        [code]) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(code)) := by
  have hGenerationFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310, 600]
        [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hBranchFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310]
        [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp
  have hMemberAdmissible :
      Formula.Admissible
        (code ∈ₘ FormulaCodeₘ) :=
    membership_formula_admissible
      hCode formula_code_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [code ∈ₘ FormulaCodeₘ]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMemberAdmissible)
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_formula_code_member_implies_generation_of_fresh
            code hCode hGenerationFresh)
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        gq_formula_code_generation_implies_zero_mem_domain_of_fresh
          code hCode hBranchFresh)
    hGeneration

/-- 对象层全称化后的公式码零位定理。 -/
theorem gq_formula_code_zero_mem_domain_universal :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 700],
        ((x#700 ∈ₘ FormulaCodeₘ) ⟶ₘ
          (numₘ(0) ∈ₘ domₘ(x#700))) := by
  let code : SetTerm := x#700
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using set_variable_admissible 700
  have hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310, 600]
        [code] := by
    simpa [code] using
      reserved_ids_fresh_cons_variable
        700
        (by
          intro id hId
          simp only [List.mem_cons,
            List.not_mem_nil, or_false] at hId
          rcases hId with
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide)
        (reserved_ids_fresh_nil
          [230, 231, 232, 233, 234,
            306, 307, 308, 309, 310, 600])
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        (code ∈ₘ FormulaCodeₘ) ⟶ₘ
          (numₘ(0) ∈ₘ domₘ(code)) :=
    gq_formula_code_member_implies_zero_mem_domain_of_fresh
      code hCode hFresh
  simpa [code] using
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := []) (sort := SetSort.set)
      (eigen := 700)
      (gq_formula_minimum_closure_theory_fresh 700)
      (by
        intro formula hFormula
        cases hFormula)
      hPoint

/-- 任意 admissible 完整公式码都在第零位有定义。 -/
theorem gq_formula_code_member_implies_zero_mem_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        (numₘ(0) ∈ₘ domₘ(code)) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := code)
      gq_formula_code_zero_mem_domain_universal
  have hNumeralFixed :
      Term.substituteFree SetSort.set 700 code
          (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 700 code (numₘ(0)) <| by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hNumeralFixed] using hAt

/-- 蕴含生成分支由左子公式零位导出完整的前两个位置。 -/
theorem
    gq_implication_generation_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh [307, 308] [code]) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 307],
        ∃ₘ[SetSort.set, 308],
          (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
            (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (code ≐ₘ imp_codeₘ(x#307, x#308)))) ⟶ₘ
        formula_code_minimum_domain_condition code := by
  let left : SetTerm := x#307
  let right : SetTerm := x#308
  let shape : SetFormula :=
    code ≐ₘ imp_codeₘ(left, right)
  let body : SetFormula :=
    ((left ∈ₘ FormulaCodeₘ) ∧ₘ
      (right ∈ₘ FormulaCodeₘ)) ∧ₘ shape
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 308], body
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 307], inner
  have hLeft :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 307
  have hRight :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 308
  have hConstructor :
      Term.Admissible
        (imp_codeₘ(left, right)) SetSort.set :=
    implication_formula_code_term_admissible
      left right hLeft hRight
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, shape]
    prove_admissible
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ
          formula_code_minimum_domain_condition code := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hMembers :
        Γ ⊢ₘ[godel_quotation_theory]
          (left ∈ₘ FormulaCodeₘ) ∧ₘ
            (right ∈ₘ FormulaCodeₘ) :=
      FirstOrder.Derives.conjElimLeft hBody
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ imp_codeₘ(left, right) := by
      simpa [shape] using
        FirstOrder.Derives.conjElimRight hBody
    have hOpening :=
      FirstOrder.Derives.impElim
        (gq_implication_formula_opening_inversion
          (Γ := Γ) left right hLeft hRight)
        hMembers
    have hLeftZero :
        Γ ⊢ₘ[godel_quotation_theory]
          numₘ(0) ∈ₘ domₘ(left) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp [Γ]) <|
            gq_formula_code_member_implies_zero_mem_domain
              left hLeft)
        (FirstOrder.Derives.conjElimLeft hMembers)
    have hOne :=
      gq_implication_formula_one_mem_domain
        left right hLeft hRight hMembers hLeftZero
    have hMinimum :
        Γ ⊢ₘ[godel_quotation_theory]
          formula_code_minimum_domain_condition
            (imp_codeₘ(left, right)) := by
      unfold formula_code_minimum_domain_condition
      exact FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft hOpening)
        hOne
    exact gq_formula_minimum_domain_transport
      code (imp_codeₘ(left, right))
      hCode hConstructor hEquality hMinimum
  change ⊢ₘ[godel_quotation_theory]
    condition ⟶ₘ
      formula_code_minimum_domain_condition code
  have hAt308 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 308)
      (gq_formula_minimum_closure_theory_fresh 308)
      (by
        intro formula hFormula
        cases hFormula)
      (formula_code_minimum_domain_condition_fresh
        code 308
        (hFresh code (by simp) 308 (by simp)))
      hPoint
  exact Metatheory.Derives.exists_imp_of_imp
    (T := godel_quotation_theory)
    (Γ := [])
    (sort := SetSort.set)
    (eigen := 307)
    (gq_formula_minimum_closure_theory_fresh 307)
    (by
      intro formula hFormula
      cases hFormula)
    (formula_code_minimum_domain_condition_fresh
      code 307
      (hFresh code (by simp) 307 (by simp)))
    hAt308

/-- 一步公式生成的四个分支统一给出第一位。 -/
theorem
    gq_formula_code_generation_implies_one_mem_domain_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310]
        [code]) :
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition FormulaCodeₘ code ⟶ₘ
        (numₘ(1) ∈ₘ domₘ(code)) := by
  have hGenerationAdmissible :
      Formula.Admissible
        (formula_code_generation_condition
          FormulaCodeₘ code) := by
    unfold formula_code_generation_condition
    prove_admissible
  have hAtomicFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl <;> simp
  have hImplicationFresh :
      ReservedIdsFresh [307, 308] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl <;> simp
  have hUniversalFresh :
      ReservedIdsFresh [309, 310] [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with rfl | rfl <;> simp
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [formula_code_generation_condition
      FormulaCodeₘ code]
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hGenerationAdmissible)
  unfold formula_code_generation_condition at hGeneration
  apply FirstOrder.Derives.disjElim hGeneration
  · let Δ : Context signature :=
      (code ∈ₘ AtomicCodeₘ) :: Γ
    have hMinimum :
        Δ ⊢ₘ[godel_quotation_theory]
          formula_code_minimum_domain_condition code :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_atomic_formula_member_implies_minimum_domain_of_fresh
              code hCode hAtomicFresh)
        (FirstOrder.Derives.assumption (by simp [Δ]))
    exact FirstOrder.Derives.conjElimRight hMinimum
  · let tail : SetFormula :=
      (∃ₘ[SetSort.set, 306],
        ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
          (code ≐ₘ neg_codeₘ(x#306)))) ∨ₘ
      ((∃ₘ[SetSort.set, 307],
        ∃ₘ[SetSort.set, 308],
          (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
            (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (code ≐ₘ imp_codeₘ(x#307, x#308)))) ∨ₘ
        (∃ₘ[SetSort.set, 309],
          ∃ₘ[SetSort.set, 310],
            (((x#309 ∈ₘ VarSymₘ) ∧ₘ
              (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
              (code ≐ₘ
                forall_codeₘ(x#309, x#310)))))
    let Δ : Context signature := tail :: Γ
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory] tail :=
      FirstOrder.Derives.assumption (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTail
    · let negation : SetFormula :=
        ∃ₘ[SetSort.set, 306],
          ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
            (code ≐ₘ neg_codeₘ(x#306)))
      let Ε : Context signature := negation :: Δ
      have hMinimum :
          Ε ⊢ₘ[godel_quotation_theory]
            formula_code_minimum_domain_condition code :=
        FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ε) (by simp [Ε, negation]) <|
              gq_negation_generation_implies_minimum_domain
                code hCode
                (hFresh code (by simp) 306 (by simp)))
          (FirstOrder.Derives.assumption
            (by simp [Ε, negation]))
      exact FirstOrder.Derives.conjElimRight hMinimum
    · let rest : SetFormula :=
        (∃ₘ[SetSort.set, 307],
          ∃ₘ[SetSort.set, 308],
            (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
              (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
              (code ≐ₘ imp_codeₘ(x#307, x#308)))) ∨ₘ
          (∃ₘ[SetSort.set, 309],
            ∃ₘ[SetSort.set, 310],
              (((x#309 ∈ₘ VarSymₘ) ∧ₘ
                (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
                (code ≐ₘ
                  forall_codeₘ(x#309, x#310))))
      let Ε : Context signature := rest :: Δ
      have hRest :
          Ε ⊢ₘ[godel_quotation_theory] rest :=
        FirstOrder.Derives.assumption (by simp [Ε])
      apply FirstOrder.Derives.disjElim hRest
      · let implication : SetFormula :=
          ∃ₘ[SetSort.set, 307],
            ∃ₘ[SetSort.set, 308],
              (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
                (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
                (code ≐ₘ imp_codeₘ(x#307, x#308)))
        let Ζ : Context signature := implication :: Ε
        have hMinimum :
            Ζ ⊢ₘ[godel_quotation_theory]
              formula_code_minimum_domain_condition code :=
          FirstOrder.Derives.impElim
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ) (by simp) <|
                gq_implication_generation_implies_minimum_domain
                  code hCode hImplicationFresh)
            (FirstOrder.Derives.assumption
              (T := godel_quotation_theory)
              (Γ := Ζ) (φ := implication)
              List.mem_cons_self)
        exact FirstOrder.Derives.conjElimRight hMinimum
      · let universal : SetFormula :=
          ∃ₘ[SetSort.set, 309],
            ∃ₘ[SetSort.set, 310],
              (((x#309 ∈ₘ VarSymₘ) ∧ₘ
                (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
                (code ≐ₘ
                  forall_codeₘ(x#309, x#310)))
        let Ζ : Context signature := universal :: Ε
        have hMinimum :
            Ζ ⊢ₘ[godel_quotation_theory]
              formula_code_minimum_domain_condition code :=
          FirstOrder.Derives.impElim
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ)
              (by simp [Ζ, universal]) <|
                gq_universal_generation_implies_minimum_domain
                  code hCode hUniversalFresh)
            (FirstOrder.Derives.assumption
              (by simp [Ζ, universal]))
        exact FirstOrder.Derives.conjElimRight hMinimum

/-- 一步公式生成统一给出前两个位置。 -/
theorem
    gq_formula_code_generation_implies_minimum_domain_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310]
        [code]) :
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition FormulaCodeₘ code ⟶ₘ
        formula_code_minimum_domain_condition code := by
  have hGenerationAdmissible :
      Formula.Admissible
        (formula_code_generation_condition
          FormulaCodeₘ code) := by
    unfold formula_code_generation_condition
    prove_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [formula_code_generation_condition FormulaCodeₘ code]
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition FormulaCodeₘ code :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hGenerationAdmissible)
  exact FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_formula_code_generation_implies_zero_mem_domain_of_fresh
            code hCode hFresh)
      hGeneration)
    (FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_formula_code_generation_implies_one_mem_domain_of_fresh
            code hCode hFresh)
      hGeneration)

/-- 完整公式码成员经生成反演统一给出前两个位置。 -/
theorem
    gq_formula_code_member_implies_minimum_domain_of_fresh
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310, 600]
        [code]) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        formula_code_minimum_domain_condition code := by
  have hGenerationFresh :
      ReservedIdsFresh
        [306, 307, 308, 309, 310, 600]
        [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hBranchFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310]
        [code] := by
    intro term hTerm id hId
    apply hFresh term hTerm id
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId ⊢
    rcases hId with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp
  have hMemberAdmissible :
      Formula.Admissible
        (code ∈ₘ FormulaCodeₘ) :=
    membership_formula_admissible
      hCode formula_code_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [code ∈ₘ FormulaCodeₘ]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMemberAdmissible)
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition FormulaCodeₘ code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_formula_code_member_implies_generation_of_fresh
            code hCode hGenerationFresh)
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        gq_formula_code_generation_implies_minimum_domain_of_fresh
          code hCode hBranchFresh)
    hGeneration

/-- 对象层全称化后的公式码最小长度定理。 -/
theorem gq_formula_code_minimum_domain_universal :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 700],
        ((x#700 ∈ₘ FormulaCodeₘ) ⟶ₘ
          formula_code_minimum_domain_condition
            (x#700)) := by
  let code : SetTerm := x#700
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using set_variable_admissible 700
  have hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234,
          306, 307, 308, 309, 310, 600]
        [code] := by
    simpa [code] using
      reserved_ids_fresh_cons_variable
        700
        (by
          intro id hId
          simp only [List.mem_cons,
            List.not_mem_nil, or_false] at hId
          rcases hId with
            rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide)
        (reserved_ids_fresh_nil
          [230, 231, 232, 233, 234,
            306, 307, 308, 309, 310, 600])
  have hPoint :=
    gq_formula_code_member_implies_minimum_domain_of_fresh
      code hCode hFresh
  simpa [code] using
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := []) (sort := SetSort.set)
      (eigen := 700)
      (gq_formula_minimum_closure_theory_fresh 700)
      (by
        intro formula hFormula
        cases hFormula)
      hPoint

/-- 任意 admissible 完整公式码至少具有前两个位置。 -/
theorem gq_formula_code_member_implies_minimum_domain
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ FormulaCodeₘ) ⟶ₘ
        formula_code_minimum_domain_condition code := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := code)
      gq_formula_code_minimum_domain_universal
  have hZeroFixed :
      Term.substituteFree SetSort.set 700 code
          (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 700 code (numₘ(0)) <| by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
  have hOneFixed :
      Term.substituteFree SetSort.set 700 code
          (numₘ(1)) =
        numₘ(1) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 700 code (numₘ(1)) <| by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
  simpa [formula_code_minimum_domain_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hZeroFixed, hOneFixed] using hAt

/-- 标准 token 行缺少第一号位置时，它不可能是完整公式码。 -/
theorem
    gq_standard_token_sequence_formula_code_not_of_one_absent
    (tokens : List Nat)
    (hOne : tokens[1]? = none) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence tokens ∈ₘ
        FormulaCodeₘ) := by
  let code : SetTerm := standard_token_sequence tokens
  let membership : SetFormula :=
    code ∈ₘ FormulaCodeₘ
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    dsimp only [membership]
    exact membership_formula_admissible
      hCode formula_code_set_term_admissible
  change ⊢ₘ[godel_quotation_theory] ¬ₘ membership
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete
        hMembershipAdmissible)
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory] membership :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hMinimum :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_minimum_domain_condition code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_formula_code_member_implies_minimum_domain
            code hCode)
      (by simpa [membership] using hMember)
  have hOneDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(1) ∈ₘ domₘ(code) :=
    FirstOrder.Derives.conjElimRight <| by
      simpa [formula_code_minimum_domain_condition] using
        hMinimum
  have hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(tokens.length) := by
    simpa [code] using
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_weaken_standard_sequence
            (standard_token_sequence_domain_eq_length
              tokens)
  have hLengthMember :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(1) ∈ₘ numₘ(tokens.length) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        (numₘ(1)) (domₘ(code))
        (numₘ(tokens.length))
        (finite_numeral_term_admissible 1)
        (domain_term_admissible code hCode)
        (finite_numeral_term_admissible tokens.length)
        hDomain)
      hOneDomain
  have hNotLt : ¬ 1 < tokens.length := by
    intro hLt
    have hSome :
        tokens[1]? = some tokens[1] :=
      List.getElem?_eq_getElem hLt
    rw [hOne] at hSome
    contradiction
  have hNotMember :
      ⊢ₘ[godel_quotation_theory]
        ¬ₘ (numₘ(1) ∈ₘ
          numₘ(tokens.length)) :=
    gq_weaken_standard_sequence
      (standard_sequence_finite_numeral_not_mem_of_not_lt
        1 tokens.length hNotLt)
  exact FirstOrder.Derives.negElim
    hLengthMember
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
      hNotMember)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
