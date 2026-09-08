import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta0Support
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchemaClosure

/-!
# ZFC 逻辑证书的内在基础层

本模块把十二类 Hilbert 逻辑公理统一接到直接 Quine 结构码上。命题分支的
payload 是有限自然数序列，其元素本身就是公式结构码；量词和等式分支则直接
携带参与变换的结构码，不再复制旧层的 token 序列、数值码和变量名。

所有分支的 witness 都由 bound-context 类型索引，并且条件只使用结构语法关系、
有界存在式和有限配对，因此不会重新引入停机、良构或新鲜性桥接义务。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC
namespace IntrinsicLogicalCertificate

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

abbrev logical_free : SetContext :=
  [SetSort.set, SetSort.set, SetSort.set, SetSort.set]

abbrev unary_bound : SetContext :=
  [SetSort.set, SetSort.set]

abbrev binary_bound : SetContext :=
  [SetSort.set, SetSort.set]

abbrev ternary_bound : SetContext :=
  [SetSort.set, SetSort.set]

def sequence_slot : SetOpenTerm logical_free :=
  .fvar .here

def certificates_slot : SetOpenTerm logical_free :=
  .fvar (.there .here)

def index_slot : SetOpenTerm logical_free :=
  .fvar (.there (.there .here))

def certificate_slot : SetOpenTerm logical_free :=
  .fvar (.there (.there (.there .here)))

def formula_slot : SetOpenTerm logical_free :=
  sequence_slot ·ₘ index_slot

/-! ## 公式码 payload -/

/- `formula_code_atₘ` 已同时约束深度、自然数域与结构分支，不重复附加载体守卫。 -/
def formula_payload_condition
    {bound free : SetContext}
    (formulaCode : SetTerm bound free) :
    SetFormula bound free :=
  formula_code_atₘ(numₘ(0), formulaCode)

@[simp] theorem formula_payload_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (formulaCode : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (formula_payload_condition formulaCode) =
      formula_payload_condition
        (formulaCode.substituteMapped
          boundSubstitution freeSubstitution) := by
  simp [formula_payload_condition, Formula.substituteMapped,
    Arguments.substituteMapped]

theorem formula_payload_condition_delta0
    {bound free : SetContext}
    (formulaCode : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (formula_payload_condition formulaCode) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.isFormulaCodeAt
    𝒂ₘ(numₘ(0), formulaCode)

/-! ## 直接项码与任意深度公式码 -/

def term_payload_condition
    {bound free : SetContext}
    (termCode : SetTerm bound free) :
    SetFormula bound free :=
  term_code_atₘ(numₘ(0), termCode)

@[simp] theorem term_payload_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (termCode : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (term_payload_condition termCode) =
      term_payload_condition
        (termCode.substituteMapped boundSubstitution freeSubstitution) := by
  simp [term_payload_condition, Formula.substituteMapped,
    Arguments.substituteMapped]

theorem term_payload_condition_delta0
    {bound free : SetContext}
    (termCode : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (term_payload_condition termCode) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.isTermCodeAt
    𝒂ₘ(numₘ(0), termCode)

def formula_code_condition
    {bound free : SetContext}
    (depth formulaCode : SetTerm bound free) :
    SetFormula bound free :=
  formula_code_atₘ(depth, formulaCode)

@[simp] theorem formula_code_condition_substituteMapped
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (depth formulaCode : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (formula_code_condition depth formulaCode) =
      formula_code_condition
        (depth.substituteMapped boundSubstitution freeSubstitution)
        (formulaCode.substituteMapped
          boundSubstitution freeSubstitution) := by
  simp [formula_code_condition, Formula.substituteMapped,
    Arguments.substituteMapped]

theorem formula_code_condition_delta0
    {bound free : SetContext}
    (depth formulaCode : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (formula_code_condition depth formulaCode) := by
  exact Formula.IsDelta0.rel (ℬ := set_levy_bound)
    RelationSymbol.isFormulaCodeAt
    𝒂ₘ(depth, formulaCode)

/-! ## witness 计划 -/

def unary_plan {free : SetContext} :
    BoundedWitnessPlan free [] unary_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (seq_spaceₘ(ωₘ) : SetOpenTerm free))
      (.nil _))

def binary_plan {free : SetContext} :
    BoundedWitnessPlan free [] binary_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (seq_spaceₘ(ωₘ) : SetOpenTerm free))
      (.nil _))

def ternary_plan {free : SetContext} :
    BoundedWitnessPlan free [] ternary_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (seq_spaceₘ(ωₘ) : SetOpenTerm free))
      (.nil _))

/-! ## 命题基础证书矩阵 -/

def unary_payload {free : SetContext} : SetTerm unary_bound free :=
  .bvar (.there .here)

def unary_sequence {free : SetContext} : SetTerm unary_bound free :=
  .bvar .here

def unary_condition
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm unary_bound free →
      SetTerm unary_bound free)
    (formula certificate : SetTerm unary_bound free) :
    SetFormula unary_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(tag), unary_payload)) ∧ₘ
    (nat_sequence_code_condition unary_sequence unary_payload ∧ₘ
      ((domₘ(unary_sequence) ≐ₘ numₘ(1)) ∧ₘ
        (formula_payload_condition (unary_sequence ·ₘ numₘ(0)) ∧ₘ
          (formula ≐ₘ constructor (unary_sequence ·ₘ numₘ(0))))))

theorem unary_condition_delta0
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm unary_bound free →
      SetTerm unary_bound free)
    (formula certificate : SetTerm unary_bound free) :
    Formula.IsDelta0 set_levy_bound
      (unary_condition tag constructor formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(tag), unary_payload)))
    (Formula.IsDelta0.conj
      (nat_sequence_code_condition_delta0 unary_sequence unary_payload)
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal (domₘ(unary_sequence)) (numₘ(1)))
        (Formula.IsDelta0.conj
          (formula_payload_condition_delta0
            (unary_sequence ·ₘ numₘ(0)))
          (Formula.IsDelta0.equal formula
            (constructor (unary_sequence ·ₘ numₘ(0)))))))

def binary_payload {free : SetContext} : SetTerm binary_bound free :=
  .bvar (.there .here)

def binary_sequence {free : SetContext} : SetTerm binary_bound free :=
  .bvar .here

def binary_left {free : SetContext} : SetTerm binary_bound free :=
  binary_sequence ·ₘ numₘ(0)

def binary_right {free : SetContext} : SetTerm binary_bound free :=
  binary_sequence ·ₘ numₘ(1)

def binary_condition
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm binary_bound free →
      SetTerm binary_bound free →
      SetTerm binary_bound free)
    (formula certificate : SetTerm binary_bound free) :
    SetFormula binary_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(tag), binary_payload)) ∧ₘ
    (nat_sequence_code_condition binary_sequence binary_payload ∧ₘ
      ((domₘ(binary_sequence) ≐ₘ numₘ(2)) ∧ₘ
        ((formula_payload_condition binary_left ∧ₘ
          formula_payload_condition binary_right) ∧ₘ
          (formula ≐ₘ constructor binary_left binary_right))))

theorem binary_condition_delta0
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm binary_bound free →
      SetTerm binary_bound free →
      SetTerm binary_bound free)
    (formula certificate : SetTerm binary_bound free) :
    Formula.IsDelta0 set_levy_bound
      (binary_condition tag constructor formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(tag), binary_payload)))
    (Formula.IsDelta0.conj
      (nat_sequence_code_condition_delta0 binary_sequence binary_payload)
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal (domₘ(binary_sequence)) (numₘ(2)))
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj
            (formula_payload_condition_delta0 binary_left)
            (formula_payload_condition_delta0 binary_right))
          (Formula.IsDelta0.equal formula
            (constructor binary_left binary_right)))))

def ternary_payload {free : SetContext} : SetTerm ternary_bound free :=
  .bvar (.there .here)

def ternary_sequence {free : SetContext} : SetTerm ternary_bound free :=
  .bvar .here

def ternary_first {free : SetContext} : SetTerm ternary_bound free :=
  ternary_sequence ·ₘ numₘ(0)

def ternary_second {free : SetContext} : SetTerm ternary_bound free :=
  ternary_sequence ·ₘ numₘ(1)

def ternary_third {free : SetContext} : SetTerm ternary_bound free :=
  ternary_sequence ·ₘ numₘ(2)

def ternary_condition
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm ternary_bound free →
      SetTerm ternary_bound free →
      SetTerm ternary_bound free →
      SetTerm ternary_bound free)
    (formula certificate : SetTerm ternary_bound free) :
    SetFormula ternary_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(tag), ternary_payload)) ∧ₘ
    (nat_sequence_code_condition ternary_sequence ternary_payload ∧ₘ
      ((domₘ(ternary_sequence) ≐ₘ numₘ(3)) ∧ₘ
        ((formula_payload_condition ternary_first ∧ₘ
            formula_payload_condition ternary_second) ∧ₘ
          (formula_payload_condition ternary_third ∧ₘ
            (formula ≐ₘ constructor ternary_first ternary_second ternary_third)))))

theorem ternary_condition_delta0
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm ternary_bound free →
      SetTerm ternary_bound free →
      SetTerm ternary_bound free →
      SetTerm ternary_bound free)
    (formula certificate : SetTerm ternary_bound free) :
    Formula.IsDelta0 set_levy_bound
      (ternary_condition tag constructor formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(tag), ternary_payload)))
    (Formula.IsDelta0.conj
      (nat_sequence_code_condition_delta0 ternary_sequence ternary_payload)
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.equal (domₘ(ternary_sequence)) (numₘ(3)))
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj
            (formula_payload_condition_delta0 ternary_first)
            (formula_payload_condition_delta0 ternary_second))
          (Formula.IsDelta0.conj
            (formula_payload_condition_delta0 ternary_third)
            (Formula.IsDelta0.equal formula
              (constructor ternary_first ternary_second ternary_third))))))

/-! ## 七类命题分支 -/

def unary_branch
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm unary_bound free →
      SetTerm unary_bound free) :
    BoundedBinaryBranch free where
  tag := tag
  bound := unary_bound
  plan := unary_plan
  condition := unary_condition tag constructor
  delta0 := by
    intro formula certificate
    exact unary_condition_delta0 tag constructor formula certificate

def binary_branch
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm binary_bound free →
      SetTerm binary_bound free →
      SetTerm binary_bound free) :
    BoundedBinaryBranch free where
  tag := tag
  bound := binary_bound
  plan := binary_plan
  condition := binary_condition tag constructor
  delta0 := by
    intro formula certificate
    exact binary_condition_delta0 tag constructor formula certificate

def ternary_branch
    {free : SetContext}
    (tag : Nat)
    (constructor : SetTerm ternary_bound free →
      SetTerm ternary_bound free →
      SetTerm ternary_bound free →
      SetTerm ternary_bound free) :
    BoundedBinaryBranch free where
  tag := tag
  bound := ternary_bound
  plan := ternary_plan
  condition := ternary_condition tag constructor
  delta0 := by
    intro formula certificate
    exact ternary_condition_delta0 tag constructor formula certificate

def propositional_branches {free : SetContext} :
    List (BoundedBinaryBranch free) :=
  [ ternary_branch 0 (fun first second third =>
        implication_distribution_axiom_code_term first second third),
    unary_branch 1 (fun formula =>
      self_implication_axiom_code_term formula),
    binary_branch 2 (fun left right =>
      weakening_axiom_code_term left right),
    binary_branch 3 (fun left right =>
      contradiction_axiom_code_term left right),
    unary_branch 4 (fun formula =>
      classical_axiom_code_term formula),
    binary_branch 5 (fun left right =>
      explosion_axiom_code_term left right),
    binary_branch 6 (fun left right =>
      case_analysis_axiom_code_term left right) ]

/-! ## 一阶量词与等式分支 -/

abbrev specialization_bound : SetContext :=
  [SetSort.set, SetSort.set, SetSort.set, SetSort.set]

def specialization_plan {free : SetContext} :
    BoundedWitnessPlan free [] specialization_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (ωₘ : SetOpenTerm free))
      (.cons
        (weaken_bound_context [SetSort.set, SetSort.set]
          (ωₘ : SetOpenTerm free))
        (.cons
          (weaken_bound_context
            [SetSort.set, SetSort.set, SetSort.set]
            (ωₘ : SetOpenTerm free))
          (.nil _))))

def specialization_payload {free : SetContext} :
    SetTerm specialization_bound free :=
  .bvar (.there (.there (.there .here)))

def specialization_body {free : SetContext} :
    SetTerm specialization_bound free :=
  .bvar (.there (.there .here))

def specialization_replacement {free : SetContext} :
    SetTerm specialization_bound free :=
  .bvar (.there .here)

def specialization_result {free : SetContext} :
    SetTerm specialization_bound free :=
  .bvar .here

def specialization_condition
    {free : SetContext}
    (formula certificate : SetTerm specialization_bound free) :
    SetFormula specialization_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(7), specialization_payload)) ∧ₘ
    ((specialization_payload ≐ₘ
        godel_pairₘ(specialization_body,
          godel_pairₘ(specialization_replacement, specialization_result))) ∧ₘ
      (((formula_code_condition numₘ(1) specialization_body ∧ₘ
          term_payload_condition specialization_replacement) ∧ₘ
        formula_payload_condition specialization_result) ∧ₘ
        (formula_open_bound_condition
            specialization_replacement specialization_body specialization_result ∧ₘ
          (formula ≐ₘ specialization_axiom_code_term
            specialization_body specialization_result))))

theorem specialization_condition_delta0
    {free : SetContext}
    (formula certificate : SetTerm specialization_bound free) :
    Formula.IsDelta0 set_levy_bound
      (specialization_condition formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(7), specialization_payload)))
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.equal specialization_payload
        (godel_pairₘ(specialization_body,
          godel_pairₘ(specialization_replacement, specialization_result))))
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.conj
            (formula_code_condition_delta0 numₘ(1) specialization_body)
            (term_payload_condition_delta0 specialization_replacement))
          (formula_payload_condition_delta0 specialization_result))
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel (ℬ := set_levy_bound)
            RelationSymbol.syntaxTransform
            𝒂ₘ(
              syntax_code_kind_term .formula,
              syntax_transform_operation_term .openBound,
              numₘ(0), numₘ(0), specialization_replacement,
              specialization_body, specialization_result))
          (Formula.IsDelta0.equal formula
            (specialization_axiom_code_term
              specialization_body specialization_result)))))

def specialization_branch {free : SetContext} :
    BoundedBinaryBranch free where
  tag := 7
  bound := specialization_bound
  plan := specialization_plan
  condition := specialization_condition
  delta0 := by
    intro formula certificate
    exact specialization_condition_delta0 formula certificate

abbrev forall_distribution_bound : SetContext :=
  [SetSort.set, SetSort.set, SetSort.set]

def forall_distribution_plan {free : SetContext} :
    BoundedWitnessPlan free [] forall_distribution_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (ωₘ : SetOpenTerm free))
      (.cons
        (weaken_bound_context [SetSort.set, SetSort.set]
          (ωₘ : SetOpenTerm free))
        (.nil _)))

def forall_distribution_payload {free : SetContext} :
    SetTerm forall_distribution_bound free :=
  .bvar (.there (.there .here))

def forall_distribution_antecedent {free : SetContext} :
    SetTerm forall_distribution_bound free :=
  .bvar (.there .here)

def forall_distribution_consequent {free : SetContext} :
    SetTerm forall_distribution_bound free :=
  .bvar .here

def forall_distribution_condition
    {free : SetContext}
    (formula certificate : SetTerm forall_distribution_bound free) :
    SetFormula forall_distribution_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(8), forall_distribution_payload)) ∧ₘ
    ((forall_distribution_payload ≐ₘ
        godel_pairₘ(forall_distribution_antecedent,
          forall_distribution_consequent)) ∧ₘ
      ((formula_code_condition numₘ(1) forall_distribution_antecedent ∧ₘ
          formula_code_condition numₘ(1) forall_distribution_consequent) ∧ₘ
        (formula ≐ₘ quantifier_distribution_axiom_code_term
          forall_distribution_antecedent forall_distribution_consequent)))

theorem forall_distribution_condition_delta0
    {free : SetContext}
    (formula certificate : SetTerm forall_distribution_bound free) :
    Formula.IsDelta0 set_levy_bound
      (forall_distribution_condition formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(8), forall_distribution_payload)))
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.equal forall_distribution_payload
        (godel_pairₘ(forall_distribution_antecedent,
          forall_distribution_consequent)))
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (formula_code_condition_delta0 numₘ(1)
            forall_distribution_antecedent)
          (formula_code_condition_delta0 numₘ(1)
            forall_distribution_consequent))
        (Formula.IsDelta0.equal formula
          (quantifier_distribution_axiom_code_term
            forall_distribution_antecedent forall_distribution_consequent))))

def forall_distribution_branch {free : SetContext} :
    BoundedBinaryBranch free where
  tag := 8
  bound := forall_distribution_bound
  plan := forall_distribution_plan
  condition := forall_distribution_condition
  delta0 := by
    intro formula certificate
    exact forall_distribution_condition_delta0 formula certificate

abbrev vacuous_forall_bound : SetContext :=
  [SetSort.set]

def vacuous_forall_plan {free : SetContext} :
    BoundedWitnessPlan free [] vacuous_forall_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.nil _)

def vacuous_forall_payload {free : SetContext} :
    SetTerm vacuous_forall_bound free :=
  .bvar .here

abbrev intrinsic_vacuous_forall_axiom_code_term
    {bound free : SetContext}
    (body : SetTerm bound free) : SetTerm bound free :=
  imp_codeₘ(body, all_codeₘ(body))

def vacuous_forall_condition
    {free : SetContext}
    (formula certificate : SetTerm vacuous_forall_bound free) :
    SetFormula vacuous_forall_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(9), vacuous_forall_payload)) ∧ₘ
    (formula_payload_condition vacuous_forall_payload ∧ₘ
      (formula ≐ₘ intrinsic_vacuous_forall_axiom_code_term
        vacuous_forall_payload))

theorem vacuous_forall_condition_delta0
    {free : SetContext}
    (formula certificate : SetTerm vacuous_forall_bound free) :
    Formula.IsDelta0 set_levy_bound
      (vacuous_forall_condition formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(9), vacuous_forall_payload)))
    (Formula.IsDelta0.conj
      (formula_payload_condition_delta0 vacuous_forall_payload)
      (Formula.IsDelta0.equal formula
        (intrinsic_vacuous_forall_axiom_code_term
          vacuous_forall_payload)))

def vacuous_forall_branch {free : SetContext} :
    BoundedBinaryBranch free where
  tag := 9
  bound := vacuous_forall_bound
  plan := vacuous_forall_plan
  condition := vacuous_forall_condition
  delta0 := by
    intro formula certificate
    exact vacuous_forall_condition_delta0 formula certificate

abbrev equality_substitution_bound : SetContext :=
  [SetSort.set, SetSort.set, SetSort.set,
    SetSort.set, SetSort.set, SetSort.set]

def equality_substitution_plan {free : SetContext} :
    BoundedWitnessPlan free [] equality_substitution_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (ωₘ : SetOpenTerm free))
      (.cons
        (weaken_bound_context [SetSort.set, SetSort.set]
          (ωₘ : SetOpenTerm free))
        (.cons
          (weaken_bound_context
            [SetSort.set, SetSort.set, SetSort.set]
            (ωₘ : SetOpenTerm free))
          (.cons
            (weaken_bound_context
              [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
              (ωₘ : SetOpenTerm free))
            (.cons
              (weaken_bound_context
                [SetSort.set, SetSort.set, SetSort.set,
                  SetSort.set, SetSort.set]
                (ωₘ : SetOpenTerm free))
              (.nil _))))))

def equality_substitution_payload {free : SetContext} :
    SetTerm equality_substitution_bound free :=
  .bvar (.there (.there (.there (.there (.there .here)))))

def equality_substitution_left {free : SetContext} :
    SetTerm equality_substitution_bound free :=
  .bvar (.there (.there (.there (.there .here))))

def equality_substitution_right {free : SetContext} :
    SetTerm equality_substitution_bound free :=
  .bvar (.there (.there (.there .here)))

def equality_substitution_body {free : SetContext} :
    SetTerm equality_substitution_bound free :=
  .bvar (.there (.there .here))

def equality_substitution_left_result {free : SetContext} :
    SetTerm equality_substitution_bound free :=
  .bvar (.there .here)

def equality_substitution_right_result {free : SetContext} :
    SetTerm equality_substitution_bound free :=
  .bvar .here

abbrev intrinsic_equality_substitution_axiom_code_term
    {bound free : SetContext}
    (left right leftResult rightResult : SetTerm bound free) :
    SetTerm bound free :=
  imp_codeₘ(eq_codeₘ(left, right),
    imp_codeₘ(leftResult, rightResult))

def equality_substitution_condition
    {free : SetContext}
    (formula certificate : SetTerm equality_substitution_bound free) :
    SetFormula equality_substitution_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(10), equality_substitution_payload)) ∧ₘ
    ((equality_substitution_payload ≐ₘ
        godel_pairₘ(equality_substitution_left,
          godel_pairₘ(equality_substitution_right,
            godel_pairₘ(equality_substitution_body,
              godel_pairₘ(equality_substitution_left_result,
                equality_substitution_right_result))))) ∧ₘ
      ((formula_open_bound_condition
          equality_substitution_left equality_substitution_body
            equality_substitution_left_result ∧ₘ
        formula_open_bound_condition
          equality_substitution_right equality_substitution_body
            equality_substitution_right_result) ∧ₘ
        (formula ≐ₘ intrinsic_equality_substitution_axiom_code_term
          equality_substitution_left equality_substitution_right
            equality_substitution_left_result
            equality_substitution_right_result)))

theorem equality_substitution_condition_delta0
    {free : SetContext}
    (formula certificate : SetTerm equality_substitution_bound free) :
    Formula.IsDelta0 set_levy_bound
      (equality_substitution_condition formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(10), equality_substitution_payload)))
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.equal equality_substitution_payload
        (godel_pairₘ(equality_substitution_left,
          godel_pairₘ(equality_substitution_right,
            godel_pairₘ(equality_substitution_body,
              godel_pairₘ(equality_substitution_left_result,
                equality_substitution_right_result))))))
      (Formula.IsDelta0.conj
        (Formula.IsDelta0.conj
          (Formula.IsDelta0.rel (ℬ := set_levy_bound)
            RelationSymbol.syntaxTransform
            𝒂ₘ(
              syntax_code_kind_term .formula,
              syntax_transform_operation_term .openBound,
              numₘ(0), numₘ(0), equality_substitution_left,
              equality_substitution_body,
              equality_substitution_left_result))
          (Formula.IsDelta0.rel (ℬ := set_levy_bound)
            RelationSymbol.syntaxTransform
            𝒂ₘ(
              syntax_code_kind_term .formula,
              syntax_transform_operation_term .openBound,
              numₘ(0), numₘ(0), equality_substitution_right,
              equality_substitution_body,
              equality_substitution_right_result)))
        (Formula.IsDelta0.equal formula
          (intrinsic_equality_substitution_axiom_code_term
            equality_substitution_left equality_substitution_right
              equality_substitution_left_result
              equality_substitution_right_result))))

def equality_substitution_branch {free : SetContext} :
    BoundedBinaryBranch free where
  tag := 10
  bound := equality_substitution_bound
  plan := equality_substitution_plan
  condition := equality_substitution_condition
  delta0 := by
    intro formula certificate
    exact equality_substitution_condition_delta0 formula certificate

abbrev equality_reflexivity_bound : SetContext :=
  [SetSort.set, SetSort.set]

def equality_reflexivity_plan {free : SetContext} :
    BoundedWitnessPlan free [] equality_reflexivity_bound :=
  .cons (ωₘ : SetTerm [] free)
    (.cons
      (weaken_bound_context [SetSort.set]
        (ωₘ : SetOpenTerm free))
      (.nil _))

def equality_reflexivity_payload {free : SetContext} :
    SetTerm equality_reflexivity_bound free :=
  .bvar (.there .here)

def equality_reflexivity_term {free : SetContext} :
    SetTerm equality_reflexivity_bound free :=
  .bvar .here

def equality_reflexivity_condition
    {free : SetContext}
    (formula certificate : SetTerm equality_reflexivity_bound free) :
    SetFormula equality_reflexivity_bound free :=
  (certificate ≐ₘ
    godel_pairₘ(numₘ(11), equality_reflexivity_payload)) ∧ₘ
    ((equality_reflexivity_payload ≐ₘ equality_reflexivity_term) ∧ₘ
      (term_payload_condition equality_reflexivity_term ∧ₘ
        (formula ≐ₘ equality_reflexivity_axiom_code_term
          equality_reflexivity_term)))

theorem equality_reflexivity_condition_delta0
    {free : SetContext}
    (formula certificate : SetTerm equality_reflexivity_bound free) :
    Formula.IsDelta0 set_levy_bound
      (equality_reflexivity_condition formula certificate) := by
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.equal certificate
      (godel_pairₘ(numₘ(11), equality_reflexivity_payload)))
    (Formula.IsDelta0.conj
      (Formula.IsDelta0.equal equality_reflexivity_payload
        equality_reflexivity_term)
      (Formula.IsDelta0.conj
        (term_payload_condition_delta0 equality_reflexivity_term)
        (Formula.IsDelta0.equal formula
          (equality_reflexivity_axiom_code_term
            equality_reflexivity_term))))

def equality_reflexivity_branch {free : SetContext} :
    BoundedBinaryBranch free where
  tag := 11
  bound := equality_reflexivity_bound
  plan := equality_reflexivity_plan
  condition := equality_reflexivity_condition
  delta0 := by
    intro formula certificate
    exact equality_reflexivity_condition_delta0 formula certificate

def first_order_branches {free : SetContext} :
    List (BoundedBinaryBranch free) :=
  [ specialization_branch, forall_distribution_branch,
    vacuous_forall_branch, equality_substitution_branch,
    equality_reflexivity_branch ]

def logical_branches {free : SetContext} :
    List (BoundedBinaryBranch free) :=
  propositional_branches ++ first_order_branches

def propositional_condition_template : FormulaTemplate.Quaternary where
  body :=
    bounded_binary_condition_list propositional_branches
      (formula_slot : SetOpenTerm logical_free)
      (certificate_slot : SetOpenTerm logical_free)

theorem propositional_condition_template_delta0 :
    Formula.IsDelta0 set_levy_bound
      propositional_condition_template.body := by
  exact bounded_binary_condition_list_delta0 propositional_branches
    (formula_slot : SetOpenTerm logical_free)
    (certificate_slot : SetOpenTerm logical_free)

def logical_condition_template : FormulaTemplate.Quaternary where
  body :=
    bounded_binary_condition_list logical_branches
      (formula_slot : SetOpenTerm logical_free)
      (certificate_slot : SetOpenTerm logical_free)

/-- 四元模板应用后直接恢复当前上下文中的逻辑分支析取。 -/
@[simp] theorem logical_condition_template_apply
    {free : SetContext}
    (sequence certificates index certificate : SetOpenTerm free) :
    logical_condition_template sequence certificates index certificate =
      bounded_binary_condition_list
        (logical_branches (free := free))
        (sequence ·ₘ index) certificate := by
  simp [logical_condition_template, FormulaTemplate.apply_four,
    FormulaTemplate.instantiate, logical_branches, propositional_branches,
    first_order_branches, bounded_binary_condition_list,
    BoundedBinaryBranch.condition_closed,
    bounded_witness_closure_substituteMapped,
    BoundedWitnessPlan.transport, unary_branch, binary_branch,
    ternary_branch, specialization_branch, forall_distribution_branch,
    vacuous_forall_branch, equality_substitution_branch,
    equality_reflexivity_branch, unary_plan, binary_plan, ternary_plan,
    specialization_plan, forall_distribution_plan, vacuous_forall_plan,
    equality_substitution_plan, equality_reflexivity_plan,
    unary_condition, binary_condition, ternary_condition,
    unary_payload, unary_sequence, binary_payload, binary_sequence,
    binary_left, binary_right, ternary_payload, ternary_sequence,
    ternary_first, ternary_second, ternary_third,
    specialization_condition, forall_distribution_condition,
    vacuous_forall_condition, equality_substitution_condition,
    equality_reflexivity_condition, specialization_payload,
    specialization_body, specialization_replacement,
    specialization_result, forall_distribution_payload,
    forall_distribution_antecedent, forall_distribution_consequent,
    vacuous_forall_payload, equality_substitution_payload,
    equality_substitution_left, equality_substitution_right,
    equality_substitution_body, equality_substitution_left_result,
    equality_substitution_right_result, equality_reflexivity_payload,
    equality_reflexivity_term, sequence_slot,
    index_slot, certificate_slot, formula_slot, weaken_bound_context,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons, VariableSubstitution.liftBound,
    VariableSubstitution.weakenBound]

theorem logical_condition_template_delta0 :
    Formula.IsDelta0 set_levy_bound
      logical_condition_template.body := by
  exact bounded_binary_condition_list_delta0 logical_branches
    (formula_slot : SetOpenTerm logical_free)
    (certificate_slot : SetOpenTerm logical_free)

end IntrinsicLogicalCertificate
end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
