import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicForallPrefix
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchemaClosure

/-!
# ZFC schema 证书的内在条件

分离、收集与替换只携带参数个数、开放 body 码及必要的结构变换中间码。核心公式
直接由 de Bruijn 下标和 Hilbert 结构码构造；全称前缀由内在有限轨迹闭合。替换
像集中的输入/输出交换直接使用 `swapBound`，不再经过临时自由变量替换链。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC
namespace IntrinsicSchemaCertificate

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open IntrinsicLogicalCertificate

set_option autoImplicit false

abbrev schema_free : SetContext := [SetSort.set, SetSort.set]

def schema_formula_slot : SetOpenTerm schema_free :=
  .fvar .here

def schema_certificate_slot : SetOpenTerm schema_free :=
  .fvar (.there .here)

/-! ## Hilbert 结构码组合 -/

def schema_conjunction_code {bound free : SetContext}
    (left right : SetTerm bound free) : SetTerm bound free :=
  neg_codeₘ(imp_codeₘ(left, neg_codeₘ(right)))

def schema_iff_code {bound free : SetContext}
    (left right : SetTerm bound free) : SetTerm bound free :=
  neg_codeₘ(imp_codeₘ(
    imp_codeₘ(left, right),
    neg_codeₘ(imp_codeₘ(right, left))))

def schema_exists_code {bound free : SetContext}
    (body : SetTerm bound free) : SetTerm bound free :=
  neg_codeₘ(all_codeₘ(neg_codeₘ(body)))

def schema_certificate_payload {bound free : SetContext}
    (tag : Nat) (parameterCount bodyCode : SetTerm bound free) :
    SetTerm bound free :=
  godel_pairₘ(numₘ(tag), godel_pairₘ(parameterCount, bodyCode))

@[simp] theorem schema_certificate_payload_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (tag : Nat) (parameterCount bodyCode : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (schema_certificate_payload tag parameterCount bodyCode).substituteMapped
        boundSubstitution freeSubstitution =
      schema_certificate_payload tag
        (parameterCount.substituteMapped boundSubstitution freeSubstitution)
        (bodyCode.substituteMapped boundSubstitution freeSubstitution) := by
  simp [schema_certificate_payload, Term.substituteMapped,
    Arguments.substituteMapped]

/-! ## 分离核心 -/

def separation_core_code {bound free : SetContext}
    (bodyCode : SetTerm bound free) : SetTerm bound free :=
  let element : SetTerm bound free := bound_var_codeₘ(numₘ(0))
  let source : SetTerm bound free := bound_var_codeₘ(numₘ(1))
  let parameter : SetTerm bound free := bound_var_codeₘ(numₘ(2))
  let matrix :=
    schema_iff_code
      (mem_codeₘ(element, source))
      (schema_conjunction_code
        (mem_codeₘ(element, parameter)) bodyCode)
  all_codeₘ(
    schema_exists_code
      (all_codeₘ(matrix)))

@[simp] theorem separation_core_code_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (bodyCode : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (separation_core_code bodyCode).substituteMapped
        boundSubstitution freeSubstitution =
      separation_core_code
        (bodyCode.substituteMapped boundSubstitution freeSubstitution) := by
  simp [separation_core_code, schema_conjunction_code, schema_iff_code,
    schema_exists_code, Term.substituteMapped, Arguments.substituteMapped]

/-! ## 收集核心 -/

def collection_core_code {bound free : SetContext}
    (bodyUnderOne bodyUnderTwo : SetTerm bound free) :
    SetTerm bound free :=
  let familyInAntecedent : SetTerm bound free := bound_var_codeₘ(numₘ(2))
  let memberInAntecedent : SetTerm bound free := bound_var_codeₘ(numₘ(1))
  let antecedent :=
    all_codeₘ(
      imp_codeₘ(
        mem_codeₘ(memberInAntecedent, familyInAntecedent),
        schema_exists_code bodyUnderOne))
  let familyInConsequent : SetTerm bound free := bound_var_codeₘ(numₘ(3))
  let memberInConsequent : SetTerm bound free := bound_var_codeₘ(numₘ(2))
  let inputInConsequent : SetTerm bound free := bound_var_codeₘ(numₘ(1))
  let outputInConsequent : SetTerm bound free := bound_var_codeₘ(numₘ(0))
  let outputBody :=
    schema_conjunction_code
      (mem_codeₘ(outputInConsequent, memberInConsequent)) bodyUnderTwo
  let consequent :=
    schema_exists_code
      (
      all_codeₘ(
        imp_codeₘ(
          mem_codeₘ(inputInConsequent, familyInConsequent),
          schema_exists_code outputBody)))
  all_codeₘ(imp_codeₘ(antecedent, consequent))

/-! ## 替换核心 -/

def replacement_core_code {bound free : SetContext}
    (firstOutputCode secondOutputCode imageCode : SetTerm bound free) :
    SetTerm bound free :=
  let firstOutput : SetTerm bound free := bound_var_codeₘ(numₘ(1))
  let secondOutput : SetTerm bound free := bound_var_codeₘ(numₘ(0))
  let functionality :=
    all_codeₘ(
      all_codeₘ(
        all_codeₘ(
          imp_codeₘ(
            schema_conjunction_code firstOutputCode secondOutputCode,
            eq_codeₘ(firstOutput, secondOutput)))))
  let element : SetTerm bound free := bound_var_codeₘ(numₘ(0))
  let imageSet : SetTerm bound free := bound_var_codeₘ(numₘ(1))
  let source : SetTerm bound free := bound_var_codeₘ(numₘ(3))
  let input : SetTerm bound free := bound_var_codeₘ(numₘ(0))
  let imageMembership :=
    schema_exists_code
      (schema_conjunction_code
        (mem_codeₘ(input, source)) imageCode)
  let imageDefinition :=
    all_codeₘ(
      schema_exists_code
        (all_codeₘ(
          schema_iff_code
            (mem_codeₘ(element, imageSet)) imageMembership)))
  imp_codeₘ(functionality, imageDefinition)

@[simp] theorem replacement_core_code_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (firstOutputCode secondOutputCode imageCode :
      SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (replacement_core_code firstOutputCode secondOutputCode imageCode).substituteMapped
        boundSubstitution freeSubstitution =
      replacement_core_code
        (firstOutputCode.substituteMapped boundSubstitution freeSubstitution)
        (secondOutputCode.substituteMapped boundSubstitution freeSubstitution)
        (imageCode.substituteMapped boundSubstitution freeSubstitution) := by
  simp [replacement_core_code, schema_conjunction_code, schema_iff_code,
    schema_exists_code, Term.substituteMapped,
    Arguments.substituteMapped]

/-! ## witness 上下文 -/

abbrev schema_bound : SetContext :=
  [SetSort.set, SetSort.set, SetSort.set, SetSort.set]

def schema_plan : BoundedWitnessPlan schema_free [] schema_bound :=
  .cons (ωₘ : SetTerm [] schema_free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (syntax_formula_code_set_term : SetOpenTerm schema_free))
      (.cons
        (weaken_bound_context [SetSort.set, SetSort.set]
          (syntax_formula_code_set_term : SetOpenTerm schema_free))
        (.cons
          (weaken_bound_context
            [SetSort.set, SetSort.set, SetSort.set]
            (syntax_formula_code_set_term : SetOpenTerm schema_free))
          (.nil _))))

def schema_parameter : SetTerm schema_bound schema_free :=
  .bvar (.there (.there (.there .here)))

def schema_body : SetTerm schema_bound schema_free :=
  .bvar (.there (.there .here))

def schema_shift_one : SetTerm schema_bound schema_free :=
  .bvar (.there .here)

def schema_shift_two : SetTerm schema_bound schema_free :=
  .bvar .here

/-! ## cutoff 提升 -/

def schema_shift_one_condition
    {bound free : SetContext}
    (parameter bodyCode shiftOne : SetTerm bound free) :
    SetFormula bound free :=
  formula_weaken_bound_condition
    (Sₘ(parameter)) numₘ(1) bodyCode shiftOne

def schema_shift_two_condition
    {bound free : SetContext}
    (parameter shiftOne shiftTwo : SetTerm bound free) :
    SetFormula bound free :=
  formula_weaken_bound_condition
    (Sₘ(Sₘ(parameter))) numₘ(1) shiftOne shiftTwo

def collection_shift_one_condition
    (parameter bodyCode shiftOne : SetTerm schema_bound schema_free) :
    SetFormula schema_bound schema_free :=
  formula_weaken_bound_condition
    (Sₘ(Sₘ(parameter))) numₘ(2) bodyCode shiftOne

def collection_shift_two_condition
    (parameter shiftOne shiftTwo : SetTerm schema_bound schema_free) :
    SetFormula schema_bound schema_free :=
  formula_weaken_bound_condition
    (Sₘ(Sₘ(Sₘ(parameter)))) numₘ(2) shiftOne shiftTwo

/-! ## 分离分支 -/

def separation_condition_at
    {bound free : SetContext}
    (formula certificate parameter bodyCode shiftOne shiftTwo :
      SetTerm bound free) : SetFormula bound free :=
  let coreCode := separation_core_code shiftTwo
  (certificate ≐ₘ
      schema_certificate_payload 0 parameter bodyCode) ∧ₘ
    ((parameter ∈ₘ ωₘ ∧ₘ
        formula_code_condition (Sₘ(parameter)) bodyCode) ∧ₘ
      ((schema_shift_one_condition parameter bodyCode shiftOne ∧ₘ
          schema_shift_two_condition parameter shiftOne shiftTwo) ∧ₘ
        ((formula_code_condition parameter coreCode ∧ₘ
            formula_code_condition numₘ(0) formula) ∧ₘ
          forall_prefix_code_condition parameter coreCode formula)))

def separation_condition
    (formula certificate : SetTerm schema_bound schema_free) :
    SetFormula schema_bound schema_free :=
  separation_condition_at formula certificate
    schema_parameter schema_body schema_shift_one schema_shift_two

@[simp] theorem separation_condition_at_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (formula certificate parameter bodyCode shiftOne shiftTwo :
      SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (separation_condition_at formula certificate parameter bodyCode
          shiftOne shiftTwo) =
      separation_condition_at
        (formula.substituteMapped boundSubstitution freeSubstitution)
        (certificate.substituteMapped boundSubstitution freeSubstitution)
        (parameter.substituteMapped boundSubstitution freeSubstitution)
        (bodyCode.substituteMapped boundSubstitution freeSubstitution)
        (shiftOne.substituteMapped boundSubstitution freeSubstitution)
        (shiftTwo.substituteMapped boundSubstitution freeSubstitution) := by
  simp [separation_condition_at, separation_core_code_substituteMapped,
    schema_shift_one_condition, schema_shift_two_condition,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped]

theorem separation_condition_delta0
    (formula certificate : SetTerm schema_bound schema_free) :
    Formula.IsDelta0 set_levy_bound
      (separation_condition formula certificate) := by
  let parameter := schema_parameter
  let bodyCode := schema_body
  let shiftOne := schema_shift_one
  let shiftTwo := schema_shift_two
  let coreCode := separation_core_code shiftTwo
  have hPayload : Formula.IsDelta0 set_levy_bound
      (certificate ≐ₘ
        schema_certificate_payload 0 parameter bodyCode) :=
    Formula.IsDelta0.equal certificate
      (schema_certificate_payload 0 parameter bodyCode)
  have hParameter : Formula.IsDelta0 set_levy_bound
      (parameter ∈ₘ ωₘ) :=
    Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership 𝒂ₘ(parameter, ωₘ)
  have hBody : Formula.IsDelta0 set_levy_bound
      (formula_code_condition (Sₘ(parameter)) bodyCode) :=
    formula_code_condition_delta0 (Sₘ(parameter)) bodyCode
  have hShiftOne : Formula.IsDelta0 set_levy_bound
      (schema_shift_one_condition parameter bodyCode shiftOne) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(parameter), numₘ(1), numₘ(0), bodyCode, shiftOne)
  have hShiftTwo : Formula.IsDelta0 set_levy_bound
      (schema_shift_two_condition parameter shiftOne shiftTwo) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(Sₘ(parameter)), numₘ(1), numₘ(0), shiftOne, shiftTwo)
  have hCore : Formula.IsDelta0 set_levy_bound
      (formula_code_condition parameter coreCode) :=
    formula_code_condition_delta0 parameter coreCode
  have hFormula : Formula.IsDelta0 set_levy_bound
      (formula_code_condition numₘ(0) formula) :=
    formula_code_condition_delta0 numₘ(0) formula
  have hPrefix : Formula.IsDelta0 set_levy_bound
      (forall_prefix_code_condition parameter coreCode formula) :=
    forall_prefix_code_condition_delta0 parameter coreCode formula
  simpa [separation_condition, parameter, bodyCode, shiftOne,
    shiftTwo, coreCode, schema_shift_one_condition,
    schema_shift_two_condition] using!
    Formula.IsDelta0.conj hPayload
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hParameter hBody)
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj hShiftOne hShiftTwo)
          (Formula.IsDelta0.conj
            (Formula.IsDelta0.conj hCore hFormula) hPrefix)))

def separation_branch : BoundedBinaryBranch schema_free where
  tag := 0
  bound := schema_bound
  plan := schema_plan
  condition := separation_condition
  delta0 := by
    intro formula certificate
    exact separation_condition_delta0 formula certificate

/-! ## 收集分支 -/

def collection_condition
    (formula certificate : SetTerm schema_bound schema_free) :
    SetFormula schema_bound schema_free :=
  let parameter := schema_parameter
  let bodyCode := schema_body
  let shiftOne := schema_shift_one
  let shiftTwo := schema_shift_two
  let coreCode := collection_core_code shiftOne shiftTwo
  (certificate ≐ₘ
      schema_certificate_payload 1 parameter bodyCode) ∧ₘ
    ((parameter ∈ₘ ωₘ ∧ₘ
        formula_code_condition (Sₘ(Sₘ(parameter))) bodyCode) ∧ₘ
      ((collection_shift_one_condition parameter bodyCode shiftOne ∧ₘ
          collection_shift_two_condition parameter shiftOne shiftTwo) ∧ₘ
        ((formula_code_condition parameter coreCode ∧ₘ
            formula_code_condition numₘ(0) formula) ∧ₘ
          forall_prefix_code_condition parameter coreCode formula)))

theorem collection_condition_delta0
    (formula certificate : SetTerm schema_bound schema_free) :
    Formula.IsDelta0 set_levy_bound
      (collection_condition formula certificate) := by
  let parameter := schema_parameter
  let bodyCode := schema_body
  let shiftOne := schema_shift_one
  let shiftTwo := schema_shift_two
  let coreCode := collection_core_code shiftOne shiftTwo
  have hPayload : Formula.IsDelta0 set_levy_bound
      (certificate ≐ₘ
        schema_certificate_payload 1 parameter bodyCode) :=
    Formula.IsDelta0.equal certificate
      (schema_certificate_payload 1 parameter bodyCode)
  have hParameter : Formula.IsDelta0 set_levy_bound
      (parameter ∈ₘ ωₘ) :=
    Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership 𝒂ₘ(parameter, ωₘ)
  have hBody : Formula.IsDelta0 set_levy_bound
      (formula_code_condition (Sₘ(Sₘ(parameter))) bodyCode) :=
    formula_code_condition_delta0 (Sₘ(Sₘ(parameter))) bodyCode
  have hShiftOne : Formula.IsDelta0 set_levy_bound
      (collection_shift_one_condition parameter bodyCode shiftOne) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(Sₘ(parameter)), numₘ(2), numₘ(0), bodyCode, shiftOne)
  have hShiftTwo : Formula.IsDelta0 set_levy_bound
      (collection_shift_two_condition parameter shiftOne shiftTwo) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(Sₘ(Sₘ(parameter))), numₘ(2), numₘ(0), shiftOne, shiftTwo)
  have hCore : Formula.IsDelta0 set_levy_bound
      (formula_code_condition parameter coreCode) :=
    formula_code_condition_delta0 parameter coreCode
  have hFormula : Formula.IsDelta0 set_levy_bound
      (formula_code_condition numₘ(0) formula) :=
    formula_code_condition_delta0 numₘ(0) formula
  have hPrefix : Formula.IsDelta0 set_levy_bound
      (forall_prefix_code_condition parameter coreCode formula) :=
    forall_prefix_code_condition_delta0 parameter coreCode formula
  simpa [collection_condition, parameter, bodyCode, shiftOne,
    shiftTwo, coreCode, collection_shift_one_condition,
    collection_shift_two_condition] using
    Formula.IsDelta0.conj hPayload
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hParameter hBody)
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj hShiftOne hShiftTwo)
          (Formula.IsDelta0.conj
            (Formula.IsDelta0.conj hCore hFormula) hPrefix)))

def collection_branch : BoundedBinaryBranch schema_free where
  tag := 1
  bound := schema_bound
  plan := schema_plan
  condition := collection_condition
  delta0 := by
    intro formula certificate
    exact collection_condition_delta0 formula certificate

/-! ## 替换分支 -/

abbrev replacement_bound : SetContext :=
  [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
    SetSort.set, SetSort.set, SetSort.set]

def replacement_plan :
    BoundedWitnessPlan schema_free [] replacement_bound :=
  .cons (ωₘ : SetTerm [] schema_free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (syntax_formula_code_set_term : SetOpenTerm schema_free))
      (.cons
        (weaken_bound_context [SetSort.set, SetSort.set]
          (syntax_formula_code_set_term : SetOpenTerm schema_free))
        (.cons
          (weaken_bound_context
            [SetSort.set, SetSort.set, SetSort.set]
            (syntax_formula_code_set_term : SetOpenTerm schema_free))
          (.cons
            (weaken_bound_context
              [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
              (syntax_formula_code_set_term : SetOpenTerm schema_free))
            (.cons
              (weaken_bound_context
                [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
                  SetSort.set]
                (syntax_formula_code_set_term : SetOpenTerm schema_free))
              (.cons
                (weaken_bound_context
                  [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
                    SetSort.set, SetSort.set]
                  (syntax_formula_code_set_term : SetOpenTerm schema_free))
                (.nil _)))))))

def replacement_parameter : SetTerm replacement_bound schema_free :=
  .bvar (.there (.there (.there (.there (.there (.there .here))))))

def replacement_body : SetTerm replacement_bound schema_free :=
  .bvar (.there (.there (.there (.there (.there .here)))))

def replacement_first_output : SetTerm replacement_bound schema_free :=
  .bvar (.there (.there (.there (.there .here))))

def replacement_second_output : SetTerm replacement_bound schema_free :=
  .bvar (.there (.there (.there .here)))

def replacement_under_one : SetTerm replacement_bound schema_free :=
  .bvar (.there (.there .here))

def replacement_under_two : SetTerm replacement_bound schema_free :=
  .bvar (.there .here)

def replacement_image : SetTerm replacement_bound schema_free :=
  .bvar .here

def replacement_first_output_condition
    {bound free : SetContext}
    (parameter bodyCode firstOutputCode :
      SetTerm bound free) : SetFormula bound free :=
  formula_weaken_bound_condition
    (Sₘ(Sₘ(parameter))) numₘ(0) bodyCode firstOutputCode

def replacement_second_output_condition
    {bound free : SetContext}
    (parameter bodyCode secondOutputCode :
      SetTerm bound free) : SetFormula bound free :=
  formula_weaken_bound_condition
    (Sₘ(Sₘ(parameter))) numₘ(1) bodyCode secondOutputCode

def replacement_under_one_condition
    {bound free : SetContext}
    (parameter bodyCode underOneCode :
      SetTerm bound free) : SetFormula bound free :=
  formula_weaken_bound_condition
    (Sₘ(Sₘ(parameter))) numₘ(2) bodyCode underOneCode

def replacement_under_two_condition
    {bound free : SetContext}
    (parameter underOneCode underTwoCode :
      SetTerm bound free) : SetFormula bound free :=
  formula_weaken_bound_condition
    (Sₘ(Sₘ(Sₘ(parameter)))) numₘ(2) underOneCode underTwoCode

def replacement_image_condition
    {bound free : SetContext}
    (parameter underTwoCode imageCode :
      SetTerm bound free) : SetFormula bound free :=
  formula_swap_bound_condition
    (Sₘ(Sₘ(Sₘ(Sₘ(parameter))))) numₘ(0) underTwoCode imageCode

def replacement_condition_at
    {bound free : SetContext}
    (formula certificate parameter bodyCode firstOutputCode secondOutputCode
      underOneCode underTwoCode imageCode : SetTerm bound free) :
    SetFormula bound free :=
  let coreCode := replacement_core_code
    firstOutputCode secondOutputCode imageCode
  (certificate ≐ₘ
      schema_certificate_payload 2 parameter bodyCode) ∧ₘ
    ((parameter ∈ₘ ωₘ ∧ₘ
        formula_code_condition (Sₘ(Sₘ(parameter))) bodyCode) ∧ₘ
      ((replacement_first_output_condition
          parameter bodyCode firstOutputCode ∧ₘ
        replacement_second_output_condition
          parameter bodyCode secondOutputCode) ∧ₘ
        ((replacement_under_one_condition
            parameter bodyCode underOneCode ∧ₘ
          replacement_under_two_condition
            parameter underOneCode underTwoCode) ∧ₘ
          (replacement_image_condition
              parameter underTwoCode imageCode ∧ₘ
            ((formula_code_condition parameter coreCode ∧ₘ
                formula_code_condition numₘ(0) formula) ∧ₘ
              forall_prefix_code_condition parameter coreCode formula)))))

def replacement_condition
    (formula certificate : SetTerm replacement_bound schema_free) :
    SetFormula replacement_bound schema_free :=
  replacement_condition_at formula certificate
    replacement_parameter replacement_body replacement_first_output
    replacement_second_output replacement_under_one replacement_under_two
    replacement_image

@[simp] theorem replacement_condition_at_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (formula certificate parameter bodyCode firstOutputCode secondOutputCode
      underOneCode underTwoCode imageCode : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (replacement_condition_at formula certificate parameter bodyCode
          firstOutputCode secondOutputCode underOneCode underTwoCode imageCode) =
      replacement_condition_at
        (formula.substituteMapped boundSubstitution freeSubstitution)
        (certificate.substituteMapped boundSubstitution freeSubstitution)
        (parameter.substituteMapped boundSubstitution freeSubstitution)
        (bodyCode.substituteMapped boundSubstitution freeSubstitution)
        (firstOutputCode.substituteMapped boundSubstitution freeSubstitution)
        (secondOutputCode.substituteMapped boundSubstitution freeSubstitution)
        (underOneCode.substituteMapped boundSubstitution freeSubstitution)
        (underTwoCode.substituteMapped boundSubstitution freeSubstitution)
        (imageCode.substituteMapped boundSubstitution freeSubstitution) := by
  simp [replacement_condition_at,
    replacement_second_output_condition,
    replacement_under_one_condition, replacement_under_two_condition,
    replacement_first_output_condition, replacement_image_condition,
    forall_prefix_code_condition_substituteMapped,
    replacement_core_code_substituteMapped,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped]

theorem replacement_condition_delta0
    (formula certificate : SetTerm replacement_bound schema_free) :
    Formula.IsDelta0 set_levy_bound
      (replacement_condition formula certificate) := by
  let parameter := replacement_parameter
  let bodyCode := replacement_body
  let firstOutputCode := replacement_first_output
  let secondOutputCode := replacement_second_output
  let underOneCode := replacement_under_one
  let underTwoCode := replacement_under_two
  let imageCode := replacement_image
  let coreCode := replacement_core_code
    firstOutputCode secondOutputCode imageCode
  have hPayload : Formula.IsDelta0 set_levy_bound
      (certificate ≐ₘ
        schema_certificate_payload 2 parameter bodyCode) :=
    Formula.IsDelta0.equal certificate
      (schema_certificate_payload 2 parameter bodyCode)
  have hParameter : Formula.IsDelta0 set_levy_bound
      (parameter ∈ₘ ωₘ) :=
    Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.membership 𝒂ₘ(parameter, ωₘ)
  have hBody : Formula.IsDelta0 set_levy_bound
      (formula_code_condition (Sₘ(Sₘ(parameter))) bodyCode) :=
    formula_code_condition_delta0 (Sₘ(Sₘ(parameter))) bodyCode
  have hFirstOutput : Formula.IsDelta0 set_levy_bound
      (replacement_first_output_condition
        parameter bodyCode firstOutputCode) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(Sₘ(parameter)), numₘ(0), numₘ(0), bodyCode,
        firstOutputCode)
  have hSecondOutput : Formula.IsDelta0 set_levy_bound
      (replacement_second_output_condition
        parameter bodyCode secondOutputCode) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(Sₘ(parameter)), numₘ(1), numₘ(0), bodyCode,
        secondOutputCode)
  have hUnderOne : Formula.IsDelta0 set_levy_bound
      (replacement_under_one_condition
        parameter bodyCode underOneCode) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(Sₘ(parameter)), numₘ(2), numₘ(0), bodyCode,
        underOneCode)
  have hUnderTwo : Formula.IsDelta0 set_levy_bound
      (replacement_under_two_condition
        parameter underOneCode underTwoCode) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .weakenBound,
        Sₘ(Sₘ(Sₘ(parameter))), numₘ(2), numₘ(0), underOneCode,
        underTwoCode)
  have hImage : Formula.IsDelta0 set_levy_bound
      (replacement_image_condition
        parameter underTwoCode imageCode) := by
    exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
      RelationSymbol.syntaxTransform
      𝒂ₘ(
        syntax_code_kind_term .formula,
        syntax_transform_operation_term .swapBound,
        Sₘ(Sₘ(Sₘ(Sₘ(parameter)))), numₘ(0), numₘ(0), underTwoCode,
        imageCode)
  have hCore : Formula.IsDelta0 set_levy_bound
      (formula_code_condition parameter coreCode) :=
    formula_code_condition_delta0 parameter coreCode
  have hFormula : Formula.IsDelta0 set_levy_bound
      (formula_code_condition numₘ(0) formula) :=
    formula_code_condition_delta0 numₘ(0) formula
  have hPrefix : Formula.IsDelta0 set_levy_bound
      (forall_prefix_code_condition parameter coreCode formula) :=
    forall_prefix_code_condition_delta0 parameter coreCode formula
  simpa [replacement_condition, parameter, bodyCode,
    firstOutputCode, secondOutputCode, underOneCode, underTwoCode,
    imageCode, coreCode, replacement_first_output_condition,
    replacement_second_output_condition,
    replacement_under_one_condition, replacement_under_two_condition,
    replacement_image_condition] using!
    Formula.IsDelta0.conj hPayload
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj hParameter hBody)
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj hFirstOutput hSecondOutput)
          (Formula.IsDelta0.conj
            (Formula.IsDelta0.conj hUnderOne hUnderTwo)
            (Formula.IsDelta0.conj hImage
              (Formula.IsDelta0.conj
                (Formula.IsDelta0.conj hCore hFormula) hPrefix)))))

def replacement_branch : BoundedBinaryBranch schema_free where
  tag := 2
  bound := replacement_bound
  plan := replacement_plan
  condition := replacement_condition
  delta0 := by
    intro formula certificate
    exact replacement_condition_delta0 formula certificate

def schema_branches : List (BoundedBinaryBranch schema_free) :=
  [separation_branch, collection_branch]

def replacement_schema_branches :
    List (BoundedBinaryBranch schema_free) :=
  [separation_branch, replacement_branch]

end IntrinsicSchemaCertificate
end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
