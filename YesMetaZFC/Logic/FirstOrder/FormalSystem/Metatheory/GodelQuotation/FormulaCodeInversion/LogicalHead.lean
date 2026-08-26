import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemAtomicFormulaDecodeRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.ImplicationConstructionInversion

/-!
# 公式码首 token 的逻辑符号拒绝

本模块给出公式码生成反演的一个局部结论：标准 token 串若以裸否定符号起首，
则不属于 `FormulaCodeₘ`。证明只展开一步公式生成；原子分支交给 checked decoder，
三个复合分支由首 token 必为左括号直接排除。
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

private theorem gq_formula_negation_branch_falsum_of_negation_head
    (tail : List Nat) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 306],
        ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
          (standard_token_sequence
              (Numbered.logical_token .negation :: tail) ≐ₘ
            neg_codeₘ(x#306)))) ⟶ₘ
        Formula.falsum := by
  let body : SetTerm := x#306
  let conditionBody : SetFormula :=
    (body ∈ₘ FormulaCodeₘ) ∧ₘ
      (standard_token_sequence
          (Numbered.logical_token .negation :: tail) ≐ₘ
        neg_codeₘ(body))
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 306], conditionBody
  have hBody :
      Term.Admissible body SetSort.set := by
    simpa [body] using set_variable_admissible 306
  have hConditionBody :
      Formula.Admissible conditionBody := by
    dsimp only [conditionBody]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hBody formula_code_set_term_admissible)
      (Formula.Admissible.equal
        (standard_token_sequence_admissible
          (Numbered.logical_token .negation :: tail))
        (negation_formula_code_term_admissible
          body hBody))
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 306 hConditionBody
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 306)
    (body := conditionBody)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hConditionBody)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 306 0 conditionBody
  · exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := conditionBody :: Γ
    have hAt :
        Δ ⊢ₘ[godel_quotation_theory] conditionBody :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete hConditionBody)
    exact
      gq_standard_token_sequence_negation_falsum_of_first_mismatch
        (Numbered.logical_token .negation :: tail)
        body hBody
        (Numbered.logical_token .negation)
        (by simp)
        (by native_decide)
        (FirstOrder.Derives.conjElimLeft hAt)
        (FirstOrder.Derives.conjElimRight hAt)

private theorem gq_formula_implication_branch_falsum_of_negation_head
    (tail : List Nat) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 307],
        ∃ₘ[SetSort.set, 308],
          (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
            (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (standard_token_sequence
                (Numbered.logical_token .negation :: tail) ≐ₘ
              imp_codeₘ(x#307, x#308)))) ⟶ₘ
        Formula.falsum := by
  let left : SetTerm := x#307
  let right : SetTerm := x#308
  let conditionBody : SetFormula :=
    ((left ∈ₘ FormulaCodeₘ) ∧ₘ
      (right ∈ₘ FormulaCodeₘ)) ∧ₘ
      (standard_token_sequence
          (Numbered.logical_token .negation :: tail) ≐ₘ
        imp_codeₘ(left, right))
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 308], conditionBody
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 307], inner
  have hLeft :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 307
  have hRight :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 308
  have hConditionBody :
      Formula.Admissible conditionBody := by
    dsimp only [conditionBody]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hLeft formula_code_set_term_admissible)
        (membership_formula_admissible
          hRight formula_code_set_term_admissible))
      (Formula.Admissible.equal
        (standard_token_sequence_admissible
          (Numbered.logical_token .negation :: tail))
        (implication_formula_code_term_admissible
          left right hLeft hRight))
  have hInner :
      Formula.Admissible inner := by
    dsimp only [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 308 hConditionBody
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 307 hInner
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 307)
    (body := inner)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hInner)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 307 0 inner
  · exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := inner :: Γ
    have hInnerAt :
        Δ ⊢ₘ[godel_quotation_theory] inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete hInner)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 308)
      (body := conditionBody)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hConditionBody)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 308 0 conditionBody
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 308) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 308 0 conditionBody
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, 308)
            SetSort.set 307 0 inner hInnerFresh
    · exact List.not_mem_nil
    · exact hInnerAt
    · let Ε : Context signature := conditionBody :: Δ
      have hAt :
          Ε ⊢ₘ[godel_quotation_theory] conditionBody :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hConditionBody)
      have hMembers :=
        FirstOrder.Derives.conjElimLeft hAt
      exact
        gq_standard_token_sequence_implication_falsum_of_first_mismatch
          (Numbered.logical_token .negation :: tail)
          left right hLeft hRight
          (Numbered.logical_token .negation)
          (by simp)
          (by native_decide)
          (FirstOrder.Derives.conjElimLeft hMembers)
          (FirstOrder.Derives.conjElimRight hMembers)
          (FirstOrder.Derives.conjElimRight hAt)

private theorem gq_formula_universal_branch_falsum_of_negation_head
    (tail : List Nat) :
    ⊢ₘ[godel_quotation_theory]
      (∃ₘ[SetSort.set, 309],
        ∃ₘ[SetSort.set, 310],
          (((x#309 ∈ₘ VarSymₘ) ∧ₘ
            (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
            (standard_token_sequence
                (Numbered.logical_token .negation :: tail) ≐ₘ
              forall_codeₘ(x#309, x#310)))) ⟶ₘ
        Formula.falsum := by
  let boundVariable : SetTerm := x#309
  let body : SetTerm := x#310
  let conditionBody : SetFormula :=
    ((boundVariable ∈ₘ VarSymₘ) ∧ₘ
      (body ∈ₘ FormulaCodeₘ)) ∧ₘ
      (standard_token_sequence
          (Numbered.logical_token .negation :: tail) ≐ₘ
        forall_codeₘ(boundVariable, body))
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 310], conditionBody
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 309], inner
  have hBoundVariable :
      Term.Admissible boundVariable SetSort.set := by
    simpa [boundVariable] using
      set_variable_admissible 309
  have hBody :
      Term.Admissible body SetSort.set := by
    simpa [body] using set_variable_admissible 310
  have hConditionBody :
      Formula.Admissible conditionBody := by
    dsimp only [conditionBody]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hBoundVariable
          variable_symbol_set_term_admissible)
        (membership_formula_admissible
          hBody formula_code_set_term_admissible))
      (Formula.Admissible.equal
        (standard_token_sequence_admissible
          (Numbered.logical_token .negation :: tail))
        (universal_formula_code_term_admissible
          boundVariable body hBoundVariable hBody))
  have hInner :
      Formula.Admissible inner := by
    dsimp only [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 310 hConditionBody
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 309 hInner
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 309)
    (body := inner)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hInner)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [condition, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set 309 0 inner
  · exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := inner :: Γ
    have hInnerAt :
        Δ ⊢ₘ[godel_quotation_theory] inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete hInner)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 310)
      (body := conditionBody)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hConditionBody)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 310 0 conditionBody
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 310) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 310 0 conditionBody
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, 310)
            SetSort.set 309 0 inner hInnerFresh
    · exact List.not_mem_nil
    · exact hInnerAt
    · let Ε : Context signature := conditionBody :: Δ
      have hAt :
          Ε ⊢ₘ[godel_quotation_theory] conditionBody :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hConditionBody)
      have hMembers :=
        FirstOrder.Derives.conjElimLeft hAt
      exact
        gq_standard_token_sequence_universal_falsum_of_first_mismatch
          (Numbered.logical_token .negation :: tail)
          boundVariable body hBoundVariable hBody
          (Numbered.logical_token .negation)
          (by simp)
          (by native_decide)
          (FirstOrder.Derives.conjElimLeft hMembers)
          (FirstOrder.Derives.conjElimRight hMembers)
          (FirstOrder.Derives.conjElimRight hAt)

/--
标准 token 串以裸否定符号起首时，一步公式生成的四个分支全部矛盾。
-/
theorem gq_formula_generation_falsum_of_negation_head
    (tail : List Nat)
    (hTokens :
      FSFormulaTokens
        (Numbered.logical_token .negation :: tail)) :
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition
          FormulaCodeₘ
          (standard_token_sequence
            (Numbered.logical_token .negation :: tail)) ⟶ₘ
        Formula.falsum := by
  let code : SetTerm :=
    standard_token_sequence
      (Numbered.logical_token .negation :: tail)
  let atomic : SetFormula :=
    code ∈ₘ AtomicCodeₘ
  let negation : SetFormula :=
    ∃ₘ[SetSort.set, 306],
      ((x#306 ∈ₘ FormulaCodeₘ) ∧ₘ
        (code ≐ₘ neg_codeₘ(x#306)))
  let implication : SetFormula :=
    ∃ₘ[SetSort.set, 307],
      ∃ₘ[SetSort.set, 308],
        (((x#307 ∈ₘ FormulaCodeₘ) ∧ₘ
          (x#308 ∈ₘ FormulaCodeₘ)) ∧ₘ
          (code ≐ₘ imp_codeₘ(x#307, x#308)))
  let universal : SetFormula :=
    ∃ₘ[SetSort.set, 309],
      ∃ₘ[SetSort.set, 310],
        (((x#309 ∈ₘ VarSymₘ) ∧ₘ
          (x#310 ∈ₘ FormulaCodeₘ)) ∧ₘ
          (code ≐ₘ forall_codeₘ(x#309, x#310)))
  let rest : SetFormula :=
    implication ∨ₘ universal
  let tailBranches : SetFormula :=
    negation ∨ₘ rest
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible
        (Numbered.logical_token .negation :: tail)
  have hGenerationAdmissible :
      Formula.Admissible
        (formula_code_generation_condition
          FormulaCodeₘ code) := by
    exact Formula.Admissible.imp_right <|
      (gq_formula_code_member_implies_generation
        code hCode
        (by simp [code])).admissible
  change
    ⊢ₘ[godel_quotation_theory]
      formula_code_generation_condition
          FormulaCodeₘ code ⟶ₘ
        Formula.falsum
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
  have hShape :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic ∨ₘ tailBranches := by
    simpa [formula_code_generation_condition,
      atomic, tailBranches, rest, negation,
      implication, universal] using hGeneration
  apply FirstOrder.Derives.disjElim hShape
  · let Δ : Context signature := atomic :: Γ
    have hAtomic :
        Δ ⊢ₘ[godel_quotation_theory] atomic :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hDecode :=
      fs_named_hilbert_tokens_decode_with_env_negation_head_none
        0 [] tail
    have hAtomicNot :
        ⊢ₘ[godel_quotation_theory]
          ¬ₘ atomic := by
      simpa [atomic, code] using
        gq_standard_atomic_formula_code_not_of_decode_none
          0 []
          (Numbered.logical_token .negation :: tail)
          hTokens hDecode
    exact FirstOrder.Derives.negElim
      hAtomic
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ])
        hAtomicNot)
  · let Δ : Context signature := tailBranches :: Γ
    have hTail :
        Δ ⊢ₘ[godel_quotation_theory]
          tailBranches :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTail
    · let Ε : Context signature := negation :: Δ
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε)
          (by simp [Ε, negation, code]) <|
            gq_formula_negation_branch_falsum_of_negation_head
              tail)
        (FirstOrder.Derives.assumption
          (by simp [negation, code]))
    · let Ε : Context signature := rest :: Δ
      have hRest :
          Ε ⊢ₘ[godel_quotation_theory] rest :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
      apply FirstOrder.Derives.disjElim hRest
      · let Ζ : Context signature := implication :: Ε
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ζ)
            (by simp [Ζ, implication, code]) <|
              gq_formula_implication_branch_falsum_of_negation_head
                tail)
          (FirstOrder.Derives.assumption
            (by simp [implication, code]))
      · let Ζ : Context signature := universal :: Ε
        exact FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Ζ)
            (by simp [Ζ, universal, code]) <|
              gq_formula_universal_branch_falsum_of_negation_head
                tail)
          (FirstOrder.Derives.assumption
            (by simp [universal, code]))

/-- 以裸否定 token 起首的标准序列不属于完整公式码集合。 -/
theorem gq_standard_formula_code_not_of_negation_head
    (tail : List Nat)
    (hTokens :
      FSFormulaTokens
        (Numbered.logical_token .negation :: tail)) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence
          (Numbered.logical_token .negation :: tail) ∈ₘ
        FormulaCodeₘ) := by
  let code : SetTerm :=
    standard_token_sequence
      (Numbered.logical_token .negation :: tail)
  let membership : SetFormula :=
    code ∈ₘ FormulaCodeₘ
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible
        (Numbered.logical_token .negation :: tail)
  have hMembership :
      Formula.Admissible membership := by
    dsimp only [membership]
    prove_admissible
  change
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ membership
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete hMembership)
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory] membership :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hMembership)
  have hGeneration :
      Γ ⊢ₘ[godel_quotation_theory]
        formula_code_generation_condition
          FormulaCodeₘ code :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_formula_code_member_implies_generation
            code hCode
            (by simp [code]))
      (by simpa [membership] using hMember)
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [code] using
          gq_formula_generation_falsum_of_negation_head
            tail hTokens)
    hGeneration

/--
标准否定 token 串不能同时等于对象蕴含构造码。

证明只对蕴含左右正文的有限定义域做对象层消去。左正文长度为零时，
第二 token 直接冲突；左正文长度为后继时，左切片以裸否定 token 起首，
由 `gq_standard_formula_code_not_of_negation_head` 排除其公式码成员。
-/
theorem gq_standard_negation_tokens_falsum_of_implication_equality
    {Γ : Context signature}
    (bodyTokens : List Nat)
    (left right : SetTerm)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hTokens :
      FSFormulaTokens
        (Numbered.negation_tokens bodyTokens))
    (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ)
    (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence
            (Numbered.negation_tokens bodyTokens) ≐ₘ
          imp_codeₘ(left, right)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  let tokens : List Nat :=
    Numbered.negation_tokens bodyTokens
  have hParent :
      Term.CheckCertificate
        (imp_codeₘ(left, right)) SetSort.set := by
    prove_term_check
  have hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    gq_formula_code_member_implies_finite_sequence
      left hLeft.admissible hLeftMember
  have hRightFinite :
    Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    gq_formula_code_member_implies_finite_sequence
      right hRight.admissible hRightMember
  have hLeftDomainMember :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ∈ₘ domₘ(imp_codeₘ(left, right)) :=
    gq_implication_left_domain_mem_code_domain
      left right hLeftFinite hRightFinite
  apply
    gq_domain_length_elim_of_member_of_standard_equality
      (child := left)
      (parent := imp_codeₘ(left, right))
      tokens Formula.falsum
      hLeftDomainMember hEquality
      (hChild := hLeft) (hParent := hParent)
  intro leftLength hLeftLength
  let leftDomainCondition : SetFormula :=
    domₘ(left) ≐ₘ numₘ(leftLength)
  let Δ : Context signature :=
    leftDomainCondition :: Γ
  have hWeakenΓΔ :
      ∀ formula, formula ∈ Γ → formula ∈ Δ := by
    intro formula hFormula
    exact List.mem_cons_of_mem leftDomainCondition hFormula
  have hLeftDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength) :=
    FirstOrder.Derives.assumption
      (by simp [Δ, leftDomainCondition])
  have hLeftFinite' :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hLeftFinite
  have hRightFinite' :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hRightFinite
  have hLeftMember' :
      Δ ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hLeftMember
  have hRightMember' :
      Δ ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hRightMember
  have hEquality' :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right) :=
    FirstOrder.Derives.context_weaken
      (Γ := Γ) (Δ := Δ) hWeakenΓΔ hEquality
  have hRightDomainMember' :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ∈ₘ domₘ(imp_codeₘ(left, right)) :=
    gq_implication_right_domain_mem_code_domain
      left right leftLength
      hLeftFinite' hRightFinite' hLeftDomain
  apply
    gq_domain_length_elim_of_member_of_standard_equality
      (child := right)
      (parent := imp_codeₘ(left, right))
      tokens Formula.falsum
      hRightDomainMember' hEquality'
      (hChild := hRight) (hParent := hParent)
  intro rightLength hRightLength
  let rightDomainCondition : SetFormula :=
    domₘ(right) ≐ₘ numₘ(rightLength)
  let Ε : Context signature :=
    rightDomainCondition :: Δ
  have hWeakenΔΕ :
      ∀ formula, formula ∈ Δ → formula ∈ Ε := by
    intro formula hFormula
    exact List.mem_cons_of_mem rightDomainCondition hFormula
  have hLeftFinite'' :
      Ε ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hLeftFinite'
  have hRightFinite'' :
      Ε ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hRightFinite'
  have hLeftMember'' :
      Ε ⊢ₘ[godel_quotation_theory]
        left ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hLeftMember'
  have hRightMember'' :
      Ε ⊢ₘ[godel_quotation_theory]
        right ∈ₘ FormulaCodeₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hRightMember'
  have hLeftDomain' :
      Ε ⊢ₘ[godel_quotation_theory]
        domₘ(left) ≐ₘ numₘ(leftLength) :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hLeftDomain
  have hRightDomain :
      Ε ⊢ₘ[godel_quotation_theory]
        domₘ(right) ≐ₘ numₘ(rightLength) :=
    FirstOrder.Derives.assumption
      (by simp [Ε, rightDomainCondition])
  have hEquality'' :
      Ε ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          imp_codeₘ(left, right) :=
    FirstOrder.Derives.context_weaken
      (Γ := Δ) (Δ := Ε) hWeakenΔΕ hEquality'
  by_cases hZero : leftLength = 0
  · subst leftLength
    exact
      gq_implication_standard_code_falsum_of_not_slice_shape
        left right tokens 0 rightLength
        hLeftFinite'' hRightFinite''
        hLeftDomain' hRightDomain hEquality''
        (by
          intro hShape
          have hPoint := congrArg
            (fun values => values[1]?)
            hShape
          have hTokenEquality :
              Numbered.logical_token .negation =
                Numbered.logical_token .implication := by
            simpa [tokens, Numbered.negation_tokens,
              Numbered.implication_tokens] using hPoint
          have hNe :
              Numbered.logical_token .negation ≠
                Numbered.logical_token .implication := by
            native_decide
          exact hNe hTokenEquality)
        (hLeft := hLeft) (hRight := hRight)
  · cases leftLength with
    | zero =>
        contradiction
    | succ leftLength =>
        let leftTokens : List Nat :=
          (tokens.drop 1).take (leftLength + 1)
        let tailSlice : List Nat :=
          (bodyTokens ++
            [Numbered.logical_token .rightParenthesis]).take
            leftLength
        have hLeftTokens :
            FSFormulaTokens leftTokens := by
          intro token hToken
          apply hTokens token
          exact
            List.mem_of_mem_drop
              (List.mem_of_mem_take hToken)
        have hLeftTokensShape :
            leftTokens =
              Numbered.logical_token .negation :: tailSlice := by
          simp [leftTokens, tailSlice, tokens,
            Numbered.negation_tokens]
        have hLeftTokens' :
            FSFormulaTokens
              (Numbered.logical_token .negation ::
                tailSlice) := by
          simpa [hLeftTokensShape] using hLeftTokens
        have hFormulaNot :
            ⊢ₘ[godel_quotation_theory]
              ¬ₘ (standard_token_sequence
                (Numbered.logical_token .negation ::
                  tailSlice) ∈ₘ FormulaCodeₘ) :=
          gq_standard_formula_code_not_of_negation_head
            tailSlice hLeftTokens'
        have hBodies := by
          simpa [tokens, leftTokens] using
            gq_implication_bodies_eq_standard_token_slices_of_domains
              left right tokens
              (leftLength + 1) rightLength
              hLeftFinite'' hRightFinite''
              hLeftDomain' hRightDomain hEquality''
              (hLeft := hLeft) (hRight := hRight)
        have hStandardMember :
            Ε ⊢ₘ[godel_quotation_theory]
              standard_token_sequence leftTokens ∈ₘ
                FormulaCodeₘ := by
          exact FirstOrder.Derives.iffElimRight
            (membership_left_iff_of_equality
              left
              (standard_token_sequence leftTokens)
              FormulaCodeₘ
              hLeft.admissible
              (standard_token_sequence_admissible leftTokens)
              formula_code_set_term_admissible
              (FirstOrder.Derives.conjElimLeft hBodies))
            hLeftMember''
        have hNotMember :
            Ε ⊢ₘ[godel_quotation_theory]
              ¬ₘ (standard_token_sequence leftTokens ∈ₘ
                FormulaCodeₘ) := by
          simpa [hLeftTokensShape] using
            FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ε) (by simp)
              hFormulaNot
        exact FirstOrder.Derives.negElim
          hStandardMember hNotMember

/-- 上一反演的闭蕴含接口，供更强对象理论直接弱化使用。 -/
theorem gq_standard_negation_tokens_implication_equality_rejection
    (bodyTokens : List Nat)
    (left right : SetTerm)
    (hLeft : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRight : Term.CheckCertificate right SetSort.set := by
      prove_term_check)
    (hTokens :
      FSFormulaTokens
        (Numbered.negation_tokens bodyTokens)) :
    ⊢ₘ[godel_quotation_theory]
      (((left ∈ₘ FormulaCodeₘ) ∧ₘ
          (right ∈ₘ FormulaCodeₘ)) ∧ₘ
        (standard_token_sequence
            (Numbered.negation_tokens bodyTokens) ≐ₘ
          imp_codeₘ(left, right))) ⟶ₘ
      Formula.falsum := by
  let condition : SetFormula :=
    (((left ∈ₘ FormulaCodeₘ) ∧ₘ
        (right ∈ₘ FormulaCodeₘ)) ∧ₘ
      (standard_token_sequence
          (Numbered.negation_tokens bodyTokens) ≐ₘ
        imp_codeₘ(left, right)))
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.conj
      (Formula.Admissible.conj
        (membership_formula_admissible
          hLeft.admissible formula_code_set_term_admissible)
        (membership_formula_admissible
          hRight.admissible formula_code_set_term_admissible))
      (Formula.Admissible.equal
        (standard_token_sequence_admissible
          (Numbered.negation_tokens bodyTokens))
        (implication_formula_code_term_admissible
          left right hLeft.admissible hRight.admissible))
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hConditionAt :
      Γ ⊢ₘ[godel_quotation_theory] condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
  have hMembers :
      Γ ⊢ₘ[godel_quotation_theory]
        (left ∈ₘ FormulaCodeₘ) ∧ₘ
          (right ∈ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.conjElimLeft hConditionAt
  exact
    gq_standard_negation_tokens_falsum_of_implication_equality
      (Γ := Γ) bodyTokens left right
      (hLeft := hLeft) (hRight := hRight)
      hTokens
      (FirstOrder.Derives.conjElimLeft hMembers)
      (FirstOrder.Derives.conjElimRight hMembers)
      (FirstOrder.Derives.conjElimRight hConditionAt)


end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
