import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Family
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCode

/-!
# 非空代码字符串序列族

本模块把 `seq₊_spaceₘ(CodeStrₘ)` 成员降为普通代码字符串序列成员，再复用公共
有限序列族接口。该层只处理 Gödel quotation 联合理论的嵌入。
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

/-- 非空代码字符串序列满足 `flattenₘ` 所需的完整有限序列族条件。 -/
theorem gq_code_string_positive_sequence_member_implies_family_condition
    {Γ : Context signature}
    (sequence : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ seq₊_spaceₘ(CodeStrₘ)) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_family_condition sequence := by
  have hNonempty :
      Γ ⊢ₘ[godel_quotation_theory]
        CodeStrₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence
          standard_token_sequence_code_string_ne_empty
  have hSpace :
      Γ ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ seq_spaceₘ(CodeStrₘ) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            gq_weaken_standard_sequence <|
              nonempty_sequence_space_member_implies_sequence_space
                CodeStrₘ sequence
                code_string_space_term_admissible
                hSequence)
        hNonempty)
      hPositive
  exact
    code_string_sequence_member_implies_family_condition_of_theory
      (T := godel_quotation_theory)
      (fun _ hFormula => Or.inl hFormula)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      sequence hSequence hSpace

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
