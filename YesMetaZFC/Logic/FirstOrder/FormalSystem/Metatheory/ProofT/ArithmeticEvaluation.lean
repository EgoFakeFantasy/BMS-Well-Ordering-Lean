import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.StructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomainSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSupportTheory

/-!
# 内在有限算术求值支撑

本模块把有限序列语义与 Quine 结构编码所需的对象算术合并为一个可复用合同。
支撑理论只由新的内在定义组成，不依赖已退役的旧实现或桥接层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open QuineEncoding
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 有限序列算术求值所需的最小对象理论合同。 -/
structure ArithmeticEvaluationSupport (T : SetTheory)
    extends FiniteSequenceEvaluationSupport T where
  contains_infinity :
    ∀ {sentence}, infinity_theory sentence → T sentence
  contains_godel_pairing_core :
    ∀ {sentence}, godel_pairing_core_theory sentence → T sentence

private theorem natural_exponentiation_theory_subset_godel_pairing_core_theory
    {sentence : SetSentence}
    (hSentence : natural_exponentiation_theory sentence) :
    godel_pairing_core_theory sentence :=
  Or.inr hSentence

namespace ArithmeticEvaluationSupport

/-- 有限算术求值支撑沿理论包含直接提升。 -/
theorem theory_weaken
    {T U : SetTheory}
    (S : ArithmeticEvaluationSupport T)
    (hTU : Theory.Extends U T) :
    ArithmeticEvaluationSupport U where
  toFiniteSequenceEvaluationSupport :=
    S.toFiniteSequenceEvaluationSupport.theory_weaken hTU
  contains_infinity := fun hSentence =>
    hTU (S.contains_infinity hSentence)
  contains_godel_pairing_core := fun hSentence =>
    hTU (S.contains_godel_pairing_core hSentence)

/-- 每个外部有限 numeral 在支撑理论中属于对象 `ω`。 -/
theorem finite_numeral_mem_omega
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (number : Nat) :
    Γ ⊢ₘ[T] (numₘ(number) : SetOpenTerm free) ∈ₘ ωₘ := by
  exact FirstOrder.Derives.theory_weaken
    S.contains_infinity
    (infinity_finite_numeral_mem_omega number)

/-- 加法定义合同可在当前求值支撑中直接使用。 -/
theorem addition_definition_instance_derives
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right result : SetOpenTerm free) :
    Γ ⊢ₘ[T] natural_addition_definition_instance left right result := by
  apply FirstOrder.Derives.theory_weaken
    (fun hSentence => S.contains_godel_pairing_core
      (natural_exponentiation_theory_subset_godel_pairing_core_theory
        (natural_multiplication_theory_subset_natural_exponentiation_theory
          (natural_addition_theory_subset_natural_multiplication_theory
            hSentence))))
  exact natural_addition_definition_instance_derives left right result

/-- 乘法定义合同可在当前求值支撑中直接使用。 -/
theorem multiplication_definition_instance_derives
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right result : SetOpenTerm free) :
    Γ ⊢ₘ[T] natural_multiplication_definition_instance left right result := by
  apply FirstOrder.Derives.theory_weaken
    (fun hSentence => S.contains_godel_pairing_core
      (natural_exponentiation_theory_subset_godel_pairing_core_theory
        (natural_multiplication_theory_subset_natural_exponentiation_theory
          hSentence)))
  exact natural_multiplication_definition_instance_derives left right result

/-- 幂定义合同可在当前求值支撑中直接使用。 -/
theorem exponentiation_definition_instance_derives
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (base exponent result : SetOpenTerm free) :
    Γ ⊢ₘ[T] natural_exponentiation_definition_instance base exponent result := by
  apply FirstOrder.Derives.theory_weaken
    (fun hSentence => S.contains_godel_pairing_core
      (natural_exponentiation_theory_subset_godel_pairing_core_theory
        hSentence))
  exact natural_exponentiation_definition_instance_derives base exponent result

/-- 配数定义合同可在当前求值支撑中直接使用。 -/
theorem pairing_definition_instance_derives
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right candidate : SetOpenTerm free) :
    Γ ⊢ₘ[T] godel_pairing_definition_instance left right candidate := by
  apply FirstOrder.Derives.theory_weaken S.contains_godel_pairing_core
  exact godel_pairing_definition_instance_derives left right candidate

end ArithmeticEvaluationSupport

/-- 新内在算术求值层的联合理论。 -/
def intrinsic_arithmetic_evaluation_theory : SetTheory :=
  Theory.union formal_language_encoding_theory
    finite_sequence_support_theory

private theorem infinity_theory_subset_formal_language_encoding_theory
    {sentence : SetSentence}
    (hSentence : infinity_theory sentence) :
    formal_language_encoding_theory sentence := by
  exact natural_addition_bound_theory_subset_formal_language_encoding_theory
    (natural_exponentiation_bound_theory_subset_addition_bound_theory
      (godel_pairing_core_theory_subset_bound_theory
        (natural_exponentiation_theory_subset_godel_pairing_core_theory
          (natural_multiplication_theory_subset_natural_exponentiation_theory
            (natural_addition_theory_subset_natural_multiplication_theory
              (natural_set_theory_subset_natural_addition_theory
                (natural_order_type_theory_subset_natural_subset_type_theory
                  (bounded_subset_theory_subset_natural_order_type_theory
                    (unbounded_subset_theory_subset_bounded_subset_theory
                      (infinity_theory_subset_unbounded_subset_theory
                        hSentence))))))))))

private theorem godel_pairing_core_theory_subset_formal_language_encoding_theory
    {sentence : SetSentence}
    (hSentence : godel_pairing_core_theory sentence) :
    formal_language_encoding_theory sentence :=
  natural_addition_bound_theory_subset_formal_language_encoding_theory
    (natural_exponentiation_bound_theory_subset_addition_bound_theory
      (godel_pairing_core_theory_subset_bound_theory hSentence))

/-- 新联合理论的有限序列算术求值支撑实例。 -/
theorem intrinsic_arithmetic_evaluation_support :
    ArithmeticEvaluationSupport intrinsic_arithmetic_evaluation_theory where
  toFiniteSequenceEvaluationSupport :=
    { toFiniteSequenceGraphSupport :=
        { toArithmeticSupport :=
            { contains_membership_irreflexive := fun hSentence =>
                Or.inr (finite_sequence_support_theory.contains_membership_irreflexive
                  hSentence)
              contains_empty_set := fun hSentence =>
                Or.inr (finite_sequence_support_theory.contains_empty_set_symbol
                  hSentence)
              contains_successor := fun hSentence =>
                Or.inr (finite_sequence_support_theory.contains_successor
                  hSentence) }
          contains_binary_union := fun hSentence =>
            Or.inr (finite_sequence_support_theory.contains_binary_union hSentence)
          contains_ordered_pair := fun hSentence =>
            Or.inr (finite_sequence_support_theory.contains_ordered_pair hSentence)
          contains_function_predicate := fun hSentence =>
            Or.inr (finite_sequence_support_theory.contains_function_predicate hSentence)
          contains_finite_sequence_concatenation := fun hSentence =>
            Or.inr (finite_sequence_support_theory.contains_finite_sequence_concatenation
              hSentence) }
      contains_function_application := fun hSentence =>
        Or.inr (finite_sequence_support_theory.contains_function_application hSentence)
      contains_finite_sequence_formal_system := fun hSentence =>
        Or.inr (finite_sequence_support_theory.contains_finite_sequence_formal_system
          hSentence) }
  contains_infinity := fun hSentence =>
    Or.inl (infinity_theory_subset_formal_language_encoding_theory hSentence)
  contains_godel_pairing_core := fun hSentence =>
    Or.inl (godel_pairing_core_theory_subset_formal_language_encoding_theory hSentence)

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
