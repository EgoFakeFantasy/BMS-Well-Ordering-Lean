import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.NamedFormulaPayloadFailure

/-!
# checked 命题逻辑基础证书的失败反演

本模块反演 `fs_logical_base_axiom_check` 的 tag 0–6 失败。结果只保留对象端
拒绝所需的两类信息：

* 固定 arity 的 payload 失败；
* payload 成功解码，但最终公式与对应命题模式不同。

这与成功反演模块形成对偶，并且不调用任何 Hilbert 公理反向实例。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-- tag 0–6 对应的公式 payload 长度。 -/
def fs_logical_propositional_payload_arity
    (tag : Nat) : Nat :=
  match tag with
  | 0 => 3
  | 1 => 1
  | 4 => 1
  | _ => 2

/-- tag 0–6 的 checked 失败结果。 -/
inductive FSLogicalPropositionalCheckFailureView
    (freeBase : Nat) (formula : SetFormula)
    (payload : Nat) : Nat → Prop
  | payload_failure
      {tag : Nat}
      (hFailure :
        FSNamedFormulaPayloadArityFailure
          freeBase payload
          (fs_logical_propositional_payload_arity tag)) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload tag
  | implication_distribution_mismatch
      (antecedent middle consequent : SetFormula)
      (hPayload :
        fs_named_formula_payload_decode freeBase payload =
          some [antecedent, middle, consequent])
      (hFormula :
        formula ≠
          Formula.imp
            (Formula.imp antecedent
              (Formula.imp middle consequent))
            (Formula.imp
              (Formula.imp antecedent middle)
              (Formula.imp antecedent consequent))) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload 0
  | self_implication_mismatch
      (body : SetFormula)
      (hPayload :
        fs_named_formula_payload_decode freeBase payload =
          some [body])
      (hFormula :
        formula ≠ Formula.imp body (Formula.imp body body)) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload 1
  | weakening_mismatch
      (body extra : SetFormula)
      (hPayload :
        fs_named_formula_payload_decode freeBase payload =
          some [body, extra])
      (hFormula :
        formula ≠ Formula.imp body (Formula.imp extra body)) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload 2
  | contradiction_mismatch
      (body conclusion : SetFormula)
      (hPayload :
        fs_named_formula_payload_decode freeBase payload =
          some [body, conclusion])
      (hFormula :
        formula ≠
          Formula.imp body
            (Formula.imp (Formula.neg body) conclusion)) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload 3
  | classical_mismatch
      (body : SetFormula)
      (hPayload :
        fs_named_formula_payload_decode freeBase payload =
          some [body])
      (hFormula :
        formula ≠
          Formula.imp
            (Formula.imp (Formula.neg body) body)
            body) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload 4
  | explosion_mismatch
      (body conclusion : SetFormula)
      (hPayload :
        fs_named_formula_payload_decode freeBase payload =
          some [body, conclusion])
      (hFormula :
        formula ≠
          Formula.imp (Formula.neg body)
            (Formula.imp body conclusion)) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload 5
  | case_analysis_mismatch
      (body conclusion : SetFormula)
      (hPayload :
        fs_named_formula_payload_decode freeBase payload =
          some [body, conclusion])
      (hFormula :
        formula ≠
          Formula.imp
            (Formula.imp body conclusion)
            (Formula.imp
              (Formula.imp (Formula.neg body) conclusion)
              conclusion)) :
      FSLogicalPropositionalCheckFailureView
        freeBase formula payload 6

/--
具名运行时 checker 的命题分支失败反演。

失败若不来自 payload 的长度或字段解码，就精确落到最终公式结构不匹配。
-/
theorem fs_logical_base_axiom_check_propositional_failure
    {freeBase : Nat}
    {formula : SetFormula} {certificate : Nat}
    (hCheck :
      fs_logical_base_axiom_check
        freeBase formula certificate = false)
    (hTagBound :
      (godel_unpair_value certificate).1 ≤ 6) :
    FSLogicalPropositionalCheckFailureView
      freeBase formula
      (godel_unpair_value certificate).2
      (godel_unpair_value certificate).1 := by
  unfold fs_logical_base_axiom_check at hCheck
  unfold fs_logical_base_axiom_check_with at hCheck
  generalize hPair :
      godel_unpair_value certificate = pair at hCheck hTagBound ⊢
  dsimp only at hCheck
  have hCases :
      pair.1 = 0 ∨ pair.1 = 1 ∨ pair.1 = 2 ∨
        pair.1 = 3 ∨ pair.1 = 4 ∨ pair.1 = 5 ∨
          pair.1 = 6 := by
    omega
  rcases hCases with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · rw [h0] at hCheck ⊢
    cases
        fs_named_formula_payload_arity_view
          freeBase pair.2 3 with
    | failure hFailure =>
        exact .payload_failure hFailure
    | decoded formulas hPayload hLength =>
        cases formulas with
        | nil =>
            simp at hLength
        | cons antecedent tail =>
            cases tail with
            | nil =>
                simp at hLength
            | cons middle tail =>
                cases tail with
                | nil =>
                    simp at hLength
                | cons consequent tail =>
                    cases tail with
                    | cons extra rest =>
                        simp at hLength
                    | nil =>
                        simp [hPayload] at hCheck
                        exact
                          .implication_distribution_mismatch
                            antecedent middle consequent hPayload
                            (fs_formula_code_eq_ne_of_false hCheck)
  · rw [h1] at hCheck ⊢
    cases
        fs_named_formula_payload_arity_view
          freeBase pair.2 1 with
    | failure hFailure =>
        exact .payload_failure hFailure
    | decoded formulas hPayload hLength =>
        cases formulas with
        | nil =>
            simp at hLength
        | cons body tail =>
            cases tail with
            | cons extra rest =>
                simp at hLength
            | nil =>
                simp [hPayload] at hCheck
                exact
                  .self_implication_mismatch body hPayload
                    (fs_formula_code_eq_ne_of_false hCheck)
  · rw [h2] at hCheck ⊢
    cases
        fs_named_formula_payload_arity_view
          freeBase pair.2 2 with
    | failure hFailure =>
        exact .payload_failure hFailure
    | decoded formulas hPayload hLength =>
        cases formulas with
        | nil =>
            simp at hLength
        | cons body tail =>
            cases tail with
            | nil =>
                simp at hLength
            | cons extra tail =>
                cases tail with
                | cons rest more =>
                    simp at hLength
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .weakening_mismatch body extra hPayload
                        (fs_formula_code_eq_ne_of_false hCheck)
  · rw [h3] at hCheck ⊢
    cases
        fs_named_formula_payload_arity_view
          freeBase pair.2 2 with
    | failure hFailure =>
        exact .payload_failure hFailure
    | decoded formulas hPayload hLength =>
        cases formulas with
        | nil =>
            simp at hLength
        | cons body tail =>
            cases tail with
            | nil =>
                simp at hLength
            | cons conclusion tail =>
                cases tail with
                | cons rest more =>
                    simp at hLength
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .contradiction_mismatch
                        body conclusion hPayload
                        (fs_formula_code_eq_ne_of_false hCheck)
  · rw [h4] at hCheck ⊢
    cases
        fs_named_formula_payload_arity_view
          freeBase pair.2 1 with
    | failure hFailure =>
        exact .payload_failure hFailure
    | decoded formulas hPayload hLength =>
        cases formulas with
        | nil =>
            simp at hLength
        | cons body tail =>
            cases tail with
            | cons extra rest =>
                simp at hLength
            | nil =>
                simp [hPayload] at hCheck
                exact
                  .classical_mismatch body hPayload
                    (fs_formula_code_eq_ne_of_false hCheck)
  · rw [h5] at hCheck ⊢
    cases
        fs_named_formula_payload_arity_view
          freeBase pair.2 2 with
    | failure hFailure =>
        exact .payload_failure hFailure
    | decoded formulas hPayload hLength =>
        cases formulas with
        | nil =>
            simp at hLength
        | cons body tail =>
            cases tail with
            | nil =>
                simp at hLength
            | cons conclusion tail =>
                cases tail with
                | cons rest more =>
                    simp at hLength
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .explosion_mismatch
                        body conclusion hPayload
                        (fs_formula_code_eq_ne_of_false hCheck)
  · rw [h6] at hCheck ⊢
    cases
        fs_named_formula_payload_arity_view
          freeBase pair.2 2 with
    | failure hFailure =>
        exact .payload_failure hFailure
    | decoded formulas hPayload hLength =>
        cases formulas with
        | nil =>
            simp at hLength
        | cons body tail =>
            cases tail with
            | nil =>
                simp at hLength
            | cons conclusion tail =>
                cases tail with
                | cons rest more =>
                    simp at hLength
                | nil =>
                    simp [hPayload] at hCheck
                    exact
                      .case_analysis_mismatch
                        body conclusion hPayload
                        (fs_formula_code_eq_ne_of_false hCheck)

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
