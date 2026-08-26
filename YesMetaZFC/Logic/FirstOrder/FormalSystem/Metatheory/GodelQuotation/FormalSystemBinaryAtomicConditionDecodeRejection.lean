import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemBinaryAtomicCodeDecodeRejection

/-!
# FormalSystem 二元原子条件的 checked 解码拒绝

本模块只消去 `binary_atomic_formula_code_condition` 的两个对象项见证，并把
等式/隶属形状分派给不含保留编号的二元原子拒绝内核。
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

/--
有限签名检查通过时，二元原子定义条件与 checked 公式 decoder 的具体失败矛盾。
-/
theorem gq_binary_atomic_condition_decode_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      binary_atomic_formula_code_condition
          (standard_token_sequence tokens) ⟶ₘ
        Formula.falsum := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let left : SetTerm := x#233
  let right : SetTerm := x#234
  let equalityShape : SetFormula :=
    code ≐ₘ
      equality_atomic_formula_code_term left right
  let membershipShape : SetFormula :=
    code ≐ₘ
      membership_atomic_formula_code_term left right
  let body : SetFormula :=
    ((term_codeₘ(left) ∧ₘ term_codeₘ(right)) ∧ₘ
      (equalityShape ∨ₘ membershipShape))
  let inner : SetFormula :=
    ∃ₘ[SetSort.set, 234], body
  let condition : SetFormula :=
    ∃ₘ[SetSort.set, 233], inner
  have hLeft :
      Term.Admissible left SetSort.set := by
    simpa [left] using set_variable_admissible 233
  have hRight :
      Term.Admissible right SetSort.set := by
    simpa [right] using set_variable_admissible 234
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hBody :
      Formula.Admissible body := by
    dsimp only [body, equalityShape, membershipShape]
    prove_admissible
  have hInner :
      Formula.Admissible inner := by
    dsimp only [inner]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 234 hBody
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    exact Formula.Admissible.exists_closeFreeAt
      SetSort.set 233 hInner
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete hCondition)
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 233)
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
        SetSort.set 233 0 inner
  · exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := inner :: Γ
    have hInnerAt :
        Δ ⊢ₘ[godel_quotation_theory]
          inner :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete hInner)
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 234)
      (body := body)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hBody)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [inner, Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 234 0 body
      · rcases List.mem_singleton.mp hFormula with rfl
        have hInnerFresh :
            (SetSort.set, 234) ∉
              Formula.freeSupport inner := by
          simpa [inner, Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              SetSort.set 234 0 body
        simpa [condition] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, 234)
            SetSort.set 233 0 inner hInnerFresh
    · exact List.not_mem_nil
    · exact hInnerAt
    · let Ε : Context signature := body :: Δ
      have hAt :
          Ε ⊢ₘ[godel_quotation_theory]
            body :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete hBody)
      have hTerms :
          Ε ⊢ₘ[godel_quotation_theory]
            term_codeₘ(left) ∧ₘ
              term_codeₘ(right) := by
        simpa [body] using
          FirstOrder.Derives.conjElimLeft hAt
      have hShapes :
          Ε ⊢ₘ[godel_quotation_theory]
            equalityShape ∨ₘ membershipShape := by
        simpa [body] using
          FirstOrder.Derives.conjElimRight hAt
      apply FirstOrder.Derives.disjElim hShapes
      · let Ζ : Context signature :=
          equalityShape :: Ε
        have hTerms' :
            Ζ ⊢ₘ[godel_quotation_theory]
              term_codeₘ(left) ∧ₘ
                term_codeₘ(right) :=
          FirstOrder.Derives.context_weaken_cons hTerms
        have hLeftMember :
            Ζ ⊢ₘ[godel_quotation_theory]
              left ∈ₘ TermCodeₘ :=
          FirstOrder.Derives.iffElimRight
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ) (by simp [Ζ]) <|
                gq_term_code_definition_instance
                  left hLeft)
            (FirstOrder.Derives.conjElimLeft hTerms')
        have hRightMember :
            Ζ ⊢ₘ[godel_quotation_theory]
              right ∈ₘ TermCodeₘ :=
          FirstOrder.Derives.iffElimRight
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ) (by simp [Ζ]) <|
                gq_term_code_definition_instance
                  right hRight)
            (FirstOrder.Derives.conjElimRight hTerms')
        have hEquality :
            Ζ ⊢ₘ[godel_quotation_theory]
              standard_token_sequence tokens ≐ₘ
                equality_atomic_formula_code_term
                  left right := by
          simpa [equalityShape, code] using
            (FirstOrder.Derives.assumption
              (T := godel_quotation_theory)
              (Γ := Ζ) (φ := equalityShape)
              (by simp [Ζ]))
        exact
          gq_equality_atomic_code_decode_falsum
            freeBase boundNames left right tokens
            hTokens hLeftMember hRightMember
            hEquality hDecode
            (hLeft := by
              simpa [left] using
                Term.check_admissible_complete hLeft)
            (hRight := by
              simpa [right] using
                Term.check_admissible_complete hRight)
      · let Ζ : Context signature :=
          membershipShape :: Ε
        have hTerms' :
            Ζ ⊢ₘ[godel_quotation_theory]
              term_codeₘ(left) ∧ₘ
                term_codeₘ(right) :=
          FirstOrder.Derives.context_weaken_cons hTerms
        have hLeftMember :
            Ζ ⊢ₘ[godel_quotation_theory]
              left ∈ₘ TermCodeₘ :=
          FirstOrder.Derives.iffElimRight
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ) (by simp [Ζ]) <|
                gq_term_code_definition_instance
                  left hLeft)
            (FirstOrder.Derives.conjElimLeft hTerms')
        have hRightMember :
            Ζ ⊢ₘ[godel_quotation_theory]
              right ∈ₘ TermCodeₘ :=
          FirstOrder.Derives.iffElimRight
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Ζ) (by simp [Ζ]) <|
                gq_term_code_definition_instance
                  right hRight)
            (FirstOrder.Derives.conjElimRight hTerms')
        have hEquality :
            Ζ ⊢ₘ[godel_quotation_theory]
              standard_token_sequence tokens ≐ₘ
                membership_atomic_formula_code_term
                  left right := by
          simpa [membershipShape, code] using
            (FirstOrder.Derives.assumption
              (T := godel_quotation_theory)
              (Γ := Ζ) (φ := membershipShape)
              (by simp [Ζ]))
        exact
          gq_membership_atomic_code_decode_falsum
            freeBase boundNames left right tokens
            hTokens hLeftMember hRightMember
            hEquality hDecode
            (hLeft := by
              simpa [left] using
                Term.check_admissible_complete hLeft)
            (hRight := by
              simpa [right] using
                Term.check_admissible_complete hRight)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
