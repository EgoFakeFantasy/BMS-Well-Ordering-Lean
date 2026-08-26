import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemBinaryAtomicConditionDecodeRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemPredicateApplicationDecodeRejection

/-!
# FormalSystem 原子公式码的 checked 解码拒绝

本模块合并二元原子与普通谓词应用两条真实拒绝分支，并沿 `AtomicCodeₘ` 的两个
对象定义实例得到标准原子公式码的闭否定。
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

/-- 原子公式生成条件与 checked 公式 decoder 的具体失败矛盾。 -/
theorem gq_atomic_formula_condition_decode_falsum
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      atomic_formula_code_condition
          (standard_token_sequence tokens) ⟶ₘ
        Formula.falsum := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let binary : SetFormula :=
    binary_atomic_formula_code_condition code
  let predicate : SetFormula :=
    predicate_application_code_condition code
  let condition : SetFormula :=
    atomic_formula_code_condition code
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hCondition :
      Formula.Admissible condition := by
    dsimp only [condition]
    prove_admissible
  change
    ⊢ₘ[godel_quotation_theory]
      condition ⟶ₘ Formula.falsum
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [condition]
  have hAt :
      Γ ⊢ₘ[godel_quotation_theory]
        condition :=
    FirstOrder.Derives.assumption
      (by simp [Γ])
      (Formula.check_admissible_complete
        hCondition)
  have hShape :
      Γ ⊢ₘ[godel_quotation_theory]
        binary ∨ₘ predicate := by
    simpa [condition, binary, predicate,
      atomic_formula_code_condition] using hAt
  apply FirstOrder.Derives.disjElim hShape
  · let Δ : Context signature := binary :: Γ
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ)
        (by simp [Δ, binary, code]) <|
          gq_binary_atomic_condition_decode_falsum
            freeBase boundNames tokens
            hTokens hDecode)
      (by
        simpa [binary, code] using
          (FirstOrder.Derives.assumption
            (T := godel_quotation_theory)
            (Γ := Δ) (φ := binary)
            (by simp [Δ])))
  · let Δ : Context signature := predicate :: Γ
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ)
        (by simp [Δ, predicate, code]) <|
          gq_predicate_application_condition_decode_falsum
            freeBase boundNames tokens
            hTokens hDecode)
      (by
        simpa [predicate, code] using
          (FirstOrder.Derives.assumption
            (T := godel_quotation_theory)
            (Γ := Δ) (φ := predicate)
            (by simp [Δ])))

/--
有限签名检查通过且公式 decoder 失败时，标准 token 序列不属于对象原子公式码
集合。
-/
theorem gq_standard_atomic_formula_code_not_of_decode_none
    (freeBase : Nat) (boundNames : List Nat)
    (tokens : List Nat)
    (hTokens : FSFormulaTokens tokens)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase boundNames tokens =
        none) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence tokens ∈ₘ
        AtomicCodeₘ) := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let membership : SetFormula :=
    code ∈ₘ AtomicCodeₘ
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hMembership :
      Formula.Admissible membership := by
    dsimp only [membership]
    exact membership_formula_admissible
      hCode atomic_formula_code_set_term_admissible
  change
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ membership
  apply FirstOrder.Derives.negIntro
    (hBodyCheck :=
      Formula.check_admissible_complete hMembership)
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        code ∈ₘ AtomicCodeₘ := by
    simpa [Γ, membership] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ) (φ := membership)
        (by simp [Γ])
        (Formula.check_admissible_complete
          hMembership))
  have hAtomic :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic_formula_codeₘ(code) :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_atomic_formula_code_set_definition_instance
            code hCode)
      hMember
  have hFresh :
      ReservedIdsFresh
        [230, 231, 232, 233, 234] [code] :=
    reserved_ids_fresh_cons_closed
      (by simp [code])
      (reserved_ids_fresh_nil
        [230, 231, 232, 233, 234])
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        atomic_formula_code_condition code :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_atomic_formula_code_definition_instance
            code hCode hFresh)
      hAtomic
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <| by
        simpa [code] using
          gq_atomic_formula_condition_decode_falsum
            freeBase boundNames tokens
            hTokens hDecode)
    hCondition

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
