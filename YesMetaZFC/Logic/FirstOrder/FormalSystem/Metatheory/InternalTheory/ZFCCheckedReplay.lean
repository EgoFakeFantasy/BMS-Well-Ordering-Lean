import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.DefinitionContracts
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifier

/-!
# ZFC checked replay 的对象层推导桥

本模块只接通已经存在的对象编码合同与 `fs_zfc_support_theory`：

* raw 支持理论中的自然演绎推导编译为标准 Hilbert 推导；
* Gödel quotation 与逻辑规则编码的局部推导可以进入同一条 raw 支持理论；
* 后续证书 verifier 的每个分支都沿这条具体桥接闭合。

这里不引入新的证明谓词，也不把理论可枚举性提升为对象层假设。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-! ## raw 支持理论桥接 -/

/-- raw 支持理论中的自然演绎推导可直接编译到 ZFC 内部 Hilbert 理论。 -/
theorem fs_zfc_support_hilbert_derives_of_raw
    {formula : SetFormula}
    (hDerives :
      Derives fs_zfc_support_raw_theory [] formula) :
    HilbertDerives fs_zfc_support_theory
      (Formula.hilbertize SetSort.set formula) := by
  simpa [fs_zfc_support_theory, fs_zfc_support_raw_theory,
    fs_internal_project_theory, fs_internal_project_raw_theory,
    fs_internal_theory, fs_internal_raw_theory] using
    hDerives.to_hilbert SetSort.set

/-- 逻辑规则编码理论中的自然演绎推导进入 ZFC raw 支持理论。 -/
theorem fs_zfc_support_raw_derives_of_logical_rules
    {formula : SetFormula}
    (hDerives :
      Derives logical_rule_encoding_theory [] formula) :
    Derives fs_zfc_support_raw_theory [] formula :=
  FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_logical_rules hFormula)
    hDerives

/-- 逻辑公理码定义理论中的推导进入 ZFC raw 支持理论。 -/
private theorem fs_zfc_support_raw_derives_of_logical_axiom_code
    {formula : SetFormula}
    (hDerives :
      Derives logical_axiom_code_theory [] formula) :
    Derives fs_zfc_support_raw_theory [] formula :=
  fs_zfc_support_raw_derives_of_logical_rules
    (FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        logical_axiom_code_theory_subset_logical_rule_encoding_theory
          hFormula)
      hDerives)

/-- Gödel quotation 理论中的 Hilbert 推导进入 ZFC raw 支持理论。 -/
theorem fs_zfc_support_raw_derives_of_godel_quotation
    {formula : SetFormula}
    (hDerives :
      Derives godel_quotation_theory [] formula) :
    Derives fs_zfc_support_raw_theory [] formula :=
  FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_godel_quotation hFormula)
    hDerives

/-- 标准有限序列语义中的对象推导进入 ZFC raw 支持理论。 -/
theorem fs_zfc_support_raw_derives_of_standard_sequence
    {formula : SetFormula}
    (hDerives :
      Derives standard_sequence_semantics_theory [] formula) :
    Derives fs_zfc_support_raw_theory [] formula :=
  FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_standard_sequence_semantics hFormula)
    hDerives

/-- Gödel 配对定义理论中的对象推导进入 ZFC raw 支持理论。 -/
theorem fs_zfc_support_raw_derives_of_godel_pairing
    {formula : SetFormula}
    (hDerives :
      Derives godel_pairing_theory [] formula) :
    Derives fs_zfc_support_raw_theory [] formula :=
  FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_godel_pairing hFormula)
    hDerives

/-- 逻辑规则编码理论中的推导进入 ZFC 支持理论。 -/
theorem fs_zfc_support_hilbert_derives_of_logical_rules
    {formula : SetFormula}
    (hDerives :
      Derives logical_rule_encoding_theory [] formula) :
    HilbertDerives fs_zfc_support_theory
      (Formula.hilbertize SetSort.set formula) :=
  fs_zfc_support_hilbert_derives_of_raw
    (fs_zfc_support_raw_derives_of_logical_rules hDerives)

/-- Gödel quotation 理论中的推导进入 ZFC 支持理论。 -/
theorem fs_zfc_support_hilbert_derives_of_godel_quotation
    {formula : SetFormula}
    (hDerives :
      Derives godel_quotation_theory [] formula) :
    HilbertDerives fs_zfc_support_theory
      (Formula.hilbertize SetSort.set formula) :=
  fs_zfc_support_hilbert_derives_of_raw
    (fs_zfc_support_raw_derives_of_godel_quotation hDerives)

/-! ## 命题公理模式成员 -/

/-- 由一个真实公式码推出其自蕴含命题公理模式成员。 -/
private theorem fs_zfc_support_raw_self_implication_axiom_member
    (bodyCode : SetTerm)
    (hBodyCode : Term.Admissible bodyCode SetSort.set)
    (hBodyCodeClosed : Term.freeSupport bodyCode = [])
    (hBodyFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(bodyCode)) :
    Derives fs_zfc_support_raw_theory [] (
      self_implication_axiom_code_term bodyCode ∈ₘ
        SelfImpAxiomsₘ) := by
  let code := self_implication_axiom_code_term bodyCode
  have hCode :
      Term.Admissible code SetSort.set :=
    self_implication_axiom_code_term_admissible
      bodyCode hBodyCode
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hBodyCodeClosed]
  have hBodyCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 403 depth bodyCode =
        bodyCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 403 depth bodyCode hBodyCode.2 (by
        rw [hBodyCodeClosed]
        exact List.not_mem_nil)
  have hCodeClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 403 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 403 depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hBodyCodeSubstitute :
      Term.substituteFree SetSort.set 403 bodyCode bodyCode =
        bodyCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 403 bodyCode bodyCode (by
        rw [hBodyCodeClosed]
        exact List.not_mem_nil)
  have hCodeSubstitute :
      Term.substituteFree SetSort.set 403 bodyCode code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 403 bodyCode code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        propositional_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hSelfDefinition :=
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimRight hDefinition)
  have hSelfInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hSelfDefinition
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hSelfIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ SelfImpAxiomsₘ) ↔ₘ
          self_implication_axiom_condition code) := by
    simpa [code, self_implication_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hBodyCodeClose] using hSelfInstance
  have hBody :
      Derives fs_zfc_support_raw_theory [] (
        formula_codeₘ(bodyCode) ∧ₘ
          (code ≐ₘ self_implication_axiom_code_term
            bodyCode)) := by
    apply FirstOrder.Derives.conjIntro
    · exact hBodyFormulaCode
    · simpa [code] using
        (FirstOrder.Derives.eq_refl_m
          (T := fs_zfc_support_raw_theory)
          (Γ := [])
          (sort := SetSort.set) code)
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 403 bodyCode
          (formula_codeₘ(x#403) ∧ₘ
            (code ≐ₘ self_implication_axiom_code_term
              (x#403)))) := by
    simpa [Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hBodyCodeSubstitute, hCodeSubstitute] using hBody
  have hConditionInstance :=
    FirstOrder.Derives.exists_intro_substituted
      (T := fs_zfc_support_raw_theory)
      (Γ := [])
      (witness := bodyCode) 403 hInstance
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        self_implication_axiom_condition code) := by
    simpa [self_implication_axiom_condition, code,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hBodyCodeClose, hCodeClose] using
        hConditionInstance
  simpa [code] using
    FirstOrder.Derives.iffElimLeft hSelfIff hCondition

/-! ## 逻辑公理码的公共对象层入口 -/

private theorem fs_zfc_support_raw_logical_axiom_code_iff_member
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    Derives fs_zfc_support_raw_theory [] (logical_axiom_codeₘ(code) ↔ₘ
      (code ∈ₘ LogicAxiomsₘ)) := by
  exact fs_zfc_support_raw_derives_of_logical_axiom_code
    (logical_axiom_code_iff_logic_axiom_set_member
      code hCode)

private theorem fs_zfc_support_raw_logical_axiom_member_iff_generation
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hClosed : Term.freeSupport code = []) :
    Derives fs_zfc_support_raw_theory [] ((code ∈ₘ LogicAxiomsₘ) ↔ₘ
      logical_axiom_code_generation_condition
        LogicAxiomsₘ code) := by
  exact fs_zfc_support_raw_derives_of_logical_axiom_code
    (logical_axiom_set_member_iff_generation
      code hCode hClosed)

/-- 闭代码满足逻辑公理生成条件时，回放为完整逻辑公理码。 -/
theorem fs_zfc_support_raw_logical_axiom_code_of_generation_condition
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hClosed : Term.freeSupport code = [])
    (hGeneration :
      Derives fs_zfc_support_raw_theory [] (
        logical_axiom_code_generation_condition
          LogicAxiomsₘ code)) :
    Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  have hMember :
      Derives fs_zfc_support_raw_theory [] (code ∈ₘ LogicAxiomsₘ) :=
    Derives.iffElimLeft
      (fs_zfc_support_raw_logical_axiom_member_iff_generation
        code hCode hClosed)
      hGeneration
  exact Derives.iffElimLeft
    (fs_zfc_support_raw_logical_axiom_code_iff_member
      code hCode)
    hMember

/-- 逻辑公理码可反演为其在对象层逻辑公理集合中的成员关系。 -/
theorem fs_zfc_support_raw_logical_axiom_member_of_code
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hLogical :
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code)) :
    Derives fs_zfc_support_raw_theory [] (code ∈ₘ LogicAxiomsₘ) := by
  exact Derives.iffElimRight
    (fs_zfc_support_raw_logical_axiom_code_iff_member code hCode)
    hLogical

theorem fs_zfc_support_raw_logical_axiom_code_of_base_condition
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set)
    (hClosed : Term.freeSupport code = [])
    (hBase : Derives fs_zfc_support_raw_theory [] (base_logical_axiom_condition code)) :
    Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  have hBaseAdmissible :
      Formula.Admissible (base_logical_axiom_condition code) :=
    base_logical_axiom_condition_admissible code hCode
  have hGeneration :
      Derives fs_zfc_support_raw_theory [] (
        logical_axiom_code_generation_condition
          LogicAxiomsₘ code) :=
    by
      have hCandidate :
          Term.Admissible LogicAxiomsₘ SetSort.set :=
        logical_axiom_set_term_admissible
      have hCandidateVariable :
          Term.Admissible (x#454) SetSort.set :=
        set_variable_admissible 454
      have hVariable :
          Term.Admissible (x#455) SetSort.set :=
        set_variable_admissible 455
      have hCandidateMember :
          Formula.Admissible
            ((x#454) ∈ₘ LogicAxiomsₘ) :=
        membership_formula_admissible
          hCandidateVariable hCandidate
      have hClosure :
          Formula.Admissible
            (canonical_forall_closure_code_condition
              (x#454) (x#455) code) :=
        canonical_forall_closure_code_condition_admissible
          (x#454) (x#455) code
          hCandidateVariable hVariable hCode
      have hRight :
          Formula.Admissible
            (∃ₘ[SetSort.set, 454],
              ∃ₘ[SetSort.set, 455],
                ((x#454 ∈ₘ LogicAxiomsₘ) ∧ₘ
                  canonical_forall_closure_code_condition
                    (x#454) (x#455) code)) := by
        simpa [logical_axiom_code_generation_condition] using
          Formula.Admissible.exists_closeFreeAt
            SetSort.set 454
            (Formula.Admissible.exists_closeFreeAt
              SetSort.set 455
              (Formula.Admissible.conj
                hCandidateMember hClosure))
      exact Derives.disjIntroLeft hBase
  have hMember :
      Derives fs_zfc_support_raw_theory [] (code ∈ₘ LogicAxiomsₘ) :=
    Derives.iffElimLeft
      (fs_zfc_support_raw_logical_axiom_member_iff_generation
        code hCode hClosed)
      hGeneration
  exact Derives.iffElimLeft
    (fs_zfc_support_raw_logical_axiom_code_iff_member
      code hCode)
    hMember

/-! ## schema 条件的 checked 装配 -/

/-- 分离证书的显式编号条件可由五个对象层组件逐项装配。 -/
theorem fs_zfc_support_raw_separation_condition_with_base_of_components
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormulaFresh :
      ∀ id, id = base ∨ id = base + 1 ∨ id = base + 2 ∨
        id = base + 3 ∨ id = base + 4 →
        (SetSort.set, id) ∉ Term.freeSupport formula)
    (hCertificateFresh :
      ∀ id, id = base ∨ id = base + 1 ∨ id = base + 2 ∨
        id = base + 3 ∨ id = base + 4 →
        (SetSort.set, id) ∉ Term.freeSupport certificate)
    (hCertificateEq :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(0)) (x#base) (x#(base + 1))))
    (hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(0))
          (x#base) (x#(base + 1))))
    (hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (x#base ∈ₘ ωₘ))
    (hSequence :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (x#(base + 2)) (x#(base + 1))
          (base + 5) (base + 6)))
    (hClassifier :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(x#base)) (x#(base + 2))
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)))
    (hShiftFirst :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (x#base) (x#(base + 2)) (x#(base + 3))
          (base + 17) (base + 18) (base + 19)))
    (hShiftSecond :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (x#base) (x#(base + 3)) (x#(base + 4))
          (base + 25) (base + 26) (base + 27)))
    (hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          (x#base)
          (fs_zfc_separation_core_code
            (x#base) (x#(base + 4)))
          formula (base + 33) (base + 34))) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_separation_condition_with_base
        formula certificate base) := by
  let parameter : SetTerm := x#base
  let bodyTokenCode : SetTerm := x#(base + 1)
  let bodyCode : SetTerm := x#(base + 2)
  let shiftOne : SetTerm := x#(base + 3)
  let shiftTwo : SetTerm := x#(base + 4)
  let parameterOne : SetTerm := Sₘ(parameter)
  let parameterTwo : SetTerm := Sₘ(parameterOne)
  let body : SetFormula :=
    (certificate ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(0)) parameter bodyTokenCode) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificate (numₘ(0))
          parameter bodyTokenCode) ∧ₘ
        ((parameter ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              bodyCode bodyTokenCode
              (base + 5) (base + 6)) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                parameterOne bodyCode
                (base + 7) (base + 8)
                (base + 9) (base + 10)
                (base + 11) (base + 12)
                (base + 13) (base + 14)
                (base + 15) (base + 16)) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  parameter bodyCode shiftOne
                  (base + 17) (base + 18) (base + 19)) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    parameter shiftOne shiftTwo
                    (base + 25) (base + 26) (base + 27)) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    parameter
                    (fs_zfc_separation_core_code
                      parameter shiftTwo)
                     formula (base + 33) (base + 34)))))))
  have hBody : Derives fs_zfc_support_raw_theory [] body := by
    dsimp [body, parameter, bodyTokenCode, bodyCode, shiftOne,
      shiftTwo, parameterOne, parameterTwo]
    exact FirstOrder.Derives.conjIntro
      hCertificateEq
      (FirstOrder.Derives.conjIntro
        hCertificateBounds
        (FirstOrder.Derives.conjIntro
          hParameterNatural
          (FirstOrder.Derives.conjIntro
            hSequence
            (FirstOrder.Derives.conjIntro
              hClassifier
              (FirstOrder.Derives.conjIntro
                hShiftFirst
                (FirstOrder.Derives.conjIntro
                  hShiftSecond hPrefix))))))
  unfold fs_zfc_separation_condition_with_base
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#base) base
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 1) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 1)) (base + 1)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 2) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 2) 0 (x#(base + 1)) _
    (by simp) (set_variable_admissible (base + 1)).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 2)) (base + 2)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 3) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 3) 0 (x#(base + 1)) _
    (by simp) (set_variable_admissible (base + 1)).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 3) 0 (x#(base + 2)) _
    (by simp) (set_variable_admissible (base + 2)).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 3)) (base + 3)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 4) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 4) 0 (x#(base + 1)) _
    (by simp) (set_variable_admissible (base + 1)).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 4) 0 (x#(base + 2)) _
    (by simp) (set_variable_admissible (base + 2)).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 3) (base + 4) 0 (x#(base + 3)) _
    (by simp) (set_variable_admissible (base + 3)).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 4)) (base + 4)
  have hFormulaFixed (id : FreeVarId) (replacement : SetTerm)
      (hFresh : (SetSort.set, id) ∉ Term.freeSupport formula) :
      Term.substituteFree SetSort.set id replacement formula =
        formula :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formula hFresh
  have hCertificateFixed (id : FreeVarId) (replacement : SetTerm)
      (hFresh : (SetSort.set, id) ∉ Term.freeSupport certificate) :
      Term.substituteFree SetSort.set id replacement certificate =
        certificate :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement certificate hFresh
  have hFormulaBaseFixed :
      Term.substituteFree SetSort.set base (x#base) formula =
        formula :=
    hFormulaFixed base (x#base)
      (hFormulaFresh base (by simp))
  have hFormulaOneFixed :
      Term.substituteFree SetSort.set (base + 1)
          (x#(base + 1)) formula =
        formula :=
    hFormulaFixed (base + 1) (x#(base + 1))
      (hFormulaFresh (base + 1) (by simp))
  have hFormulaTwoFixed :
      Term.substituteFree SetSort.set (base + 2)
          (x#(base + 2)) formula =
        formula :=
    hFormulaFixed (base + 2) (x#(base + 2))
      (hFormulaFresh (base + 2) (by simp))
  have hFormulaThreeFixed :
      Term.substituteFree SetSort.set (base + 3)
          (x#(base + 3)) formula =
        formula :=
    hFormulaFixed (base + 3) (x#(base + 3))
      (hFormulaFresh (base + 3) (by simp))
  have hFormulaFourFixed :
      Term.substituteFree SetSort.set (base + 4)
          (x#(base + 4)) formula =
        formula :=
    hFormulaFixed (base + 4) (x#(base + 4))
      (hFormulaFresh (base + 4) (by simp))
  have hCertificateBaseFixed :
      Term.substituteFree SetSort.set base (x#base) certificate =
        certificate :=
    hCertificateFixed base (x#base)
      (hCertificateFresh base (by simp))
  have hCertificateOneFixed :
      Term.substituteFree SetSort.set (base + 1)
          (x#(base + 1)) certificate =
        certificate :=
    hCertificateFixed (base + 1) (x#(base + 1))
      (hCertificateFresh (base + 1) (by simp))
  have hCertificateTwoFixed :
      Term.substituteFree SetSort.set (base + 2)
          (x#(base + 2)) certificate =
        certificate :=
    hCertificateFixed (base + 2) (x#(base + 2))
      (hCertificateFresh (base + 2) (by simp))
  have hCertificateThreeFixed :
      Term.substituteFree SetSort.set (base + 3)
          (x#(base + 3)) certificate =
        certificate :=
    hCertificateFixed (base + 3) (x#(base + 3))
      (hCertificateFresh (base + 3) (by simp))
  have hCertificateFourFixed :
      Term.substituteFree SetSort.set (base + 4)
          (x#(base + 4)) certificate =
        certificate :=
    hCertificateFixed (base + 4) (x#(base + 4))
      (hCertificateFresh (base + 4) (by simp))
  simpa [Formula.substituteFree_self, Term.substituteFree_self,
    Formula.substituteFree, Term.substituteFree,
    set_variable, fs_zfc_separation_condition_with_base,
    body, parameter, bodyTokenCode, bodyCode, shiftOne,
    shiftTwo, parameterOne, parameterTwo,
    fs_zfc_schema_certificate_bounds,
    fs_zfc_schema_payload_term,
    fs_zfc_schema_body_payload_term,
    hFormulaBaseFixed, hFormulaOneFixed, hFormulaTwoFixed,
    hFormulaThreeFixed, hFormulaFourFixed,
    hCertificateBaseFixed, hCertificateOneFixed,
    hCertificateTwoFixed, hCertificateThreeFixed,
    hCertificateFourFixed] using hBody

/-! 收集 schema 与分离 schema 共用同一套显式编号运输。 -/

/-- 收集证书的显式编号条件可由五个对象层组件逐项装配。 -/
theorem fs_zfc_support_raw_collection_condition_with_base_of_components
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormulaFresh :
      ∀ id, id = base ∨ id = base + 1 ∨ id = base + 2 ∨
        id = base + 3 ∨ id = base + 4 →
        (SetSort.set, id) ∉ Term.freeSupport formula)
    (hCertificateFresh :
      ∀ id, id = base ∨ id = base + 1 ∨ id = base + 2 ∨
        id = base + 3 ∨ id = base + 4 →
        (SetSort.set, id) ∉ Term.freeSupport certificate)
    (hCertificateEq :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(1)) (x#base) (x#(base + 1))))
    (hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(1))
          (x#base) (x#(base + 1))))
    (hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (x#base ∈ₘ ωₘ))
    (hSequence :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (x#(base + 2)) (x#(base + 1))
          (base + 5) (base + 6)))
    (hClassifier :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(Sₘ(x#base))) (x#(base + 2))
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)))
    (hShiftFirst :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (x#base) (x#(base + 2)) (x#(base + 3))
          (base + 17) (base + 18) (base + 19)))
    (hShiftSecond :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (x#base) (x#(base + 3)) (x#(base + 4))
          (base + 25) (base + 26) (base + 27)))
    (hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          (x#base)
          (fs_zfc_collection_core_code
            (x#base) (x#(base + 3)) (x#(base + 4)))
          formula (base + 33) (base + 34))) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_collection_condition_with_base
        formula certificate base) := by
  let parameter : SetTerm := x#base
  let bodyTokenCode : SetTerm := x#(base + 1)
  let bodyCode : SetTerm := x#(base + 2)
  let shiftOne : SetTerm := x#(base + 3)
  let shiftTwo : SetTerm := x#(base + 4)
  let parameterOne : SetTerm := Sₘ(parameter)
  let parameterTwo : SetTerm := Sₘ(parameterOne)
  let parameterThree : SetTerm := Sₘ(parameterTwo)
  let body : SetFormula :=
    (certificate ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(1)) parameter bodyTokenCode) ∧ₘ
      ((fs_zfc_schema_certificate_bounds
          certificate (numₘ(1))
          parameter bodyTokenCode) ∧ₘ
        ((parameter ∈ₘ ωₘ) ∧ₘ
          ((nat_sequence_code_condition_with_ids
              bodyCode bodyTokenCode
              (base + 5) (base + 6)) ∧ₘ
            ((canonical_project_formula_code_condition_with_ids
                parameterTwo bodyCode
                (base + 7) (base + 8)
                (base + 9) (base + 10)
                (base + 11) (base + 12)
                (base + 13) (base + 14)
                (base + 15) (base + 16)) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  parameter bodyCode shiftOne
                  (base + 17) (base + 18) (base + 19)) ∧ₘ
                ((canonical_project_shift_code_condition_with_ids
                    parameter shiftOne shiftTwo
                    (base + 25) (base + 26) (base + 27)) ∧ₘ
                  canonical_forall_prefix_code_condition_with_ids
                    parameter
                    (fs_zfc_collection_core_code
                      parameter shiftOne shiftTwo)
                     formula (base + 33) (base + 34)))))))
  have hBody : Derives fs_zfc_support_raw_theory [] body := by
    dsimp [body, parameter, bodyTokenCode, bodyCode, shiftOne,
      shiftTwo, parameterOne, parameterTwo, parameterThree]
    exact FirstOrder.Derives.conjIntro
      hCertificateEq
      (FirstOrder.Derives.conjIntro
        hCertificateBounds
        (FirstOrder.Derives.conjIntro
          hParameterNatural
          (FirstOrder.Derives.conjIntro
            hSequence
            (FirstOrder.Derives.conjIntro
              hClassifier
              (FirstOrder.Derives.conjIntro
                hShiftFirst
                (FirstOrder.Derives.conjIntro
                  hShiftSecond hPrefix))))))
  unfold fs_zfc_collection_condition_with_base
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#base) base
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 1) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 1)) (base + 1)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 2) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 2) 0 (x#(base + 1)) _
    (by simp) (set_variable_admissible (base + 1)).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 2)) (base + 2)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 3) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 3) 0 (x#(base + 1)) _
    (by simp) (set_variable_admissible (base + 1)).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 3) 0 (x#(base + 2)) _
    (by simp) (set_variable_admissible (base + 2)).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 3)) (base + 3)
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set base (base + 4) 0 (x#base) _
    (by simp) (set_variable_admissible base).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 1) (base + 4) 0 (x#(base + 1)) _
    (by simp) (set_variable_admissible (base + 1)).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 2) (base + 4) 0 (x#(base + 2)) _
    (by simp) (set_variable_admissible (base + 2)).2 (by
      simp [Term.freeSupport])]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set (base + 3) (base + 4) 0 (x#(base + 3)) _
    (by simp) (set_variable_admissible (base + 3)).2 (by
      simp [Term.freeSupport])]
  nd_apply FirstOrder.Derives.exists_intro_substituted
    (witness := x#(base + 4)) (base + 4)
  have hFormulaFixed (id : FreeVarId) (replacement : SetTerm)
      (hFresh : (SetSort.set, id) ∉ Term.freeSupport formula) :
      Term.substituteFree SetSort.set id replacement formula =
        formula :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement formula hFresh
  have hCertificateFixed (id : FreeVarId) (replacement : SetTerm)
      (hFresh : (SetSort.set, id) ∉ Term.freeSupport certificate) :
      Term.substituteFree SetSort.set id replacement certificate =
        certificate :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement certificate hFresh
  have hFormulaBaseFixed :
      Term.substituteFree SetSort.set base (x#base) formula =
        formula :=
    hFormulaFixed base (x#base)
      (hFormulaFresh base (by simp))
  have hFormulaOneFixed :
      Term.substituteFree SetSort.set (base + 1)
          (x#(base + 1)) formula =
        formula :=
    hFormulaFixed (base + 1) (x#(base + 1))
      (hFormulaFresh (base + 1) (by simp))
  have hFormulaTwoFixed :
      Term.substituteFree SetSort.set (base + 2)
          (x#(base + 2)) formula =
        formula :=
    hFormulaFixed (base + 2) (x#(base + 2))
      (hFormulaFresh (base + 2) (by simp))
  have hFormulaThreeFixed :
      Term.substituteFree SetSort.set (base + 3)
          (x#(base + 3)) formula =
        formula :=
    hFormulaFixed (base + 3) (x#(base + 3))
      (hFormulaFresh (base + 3) (by simp))
  have hFormulaFourFixed :
      Term.substituteFree SetSort.set (base + 4)
          (x#(base + 4)) formula =
        formula :=
    hFormulaFixed (base + 4) (x#(base + 4))
      (hFormulaFresh (base + 4) (by simp))
  have hCertificateBaseFixed :
      Term.substituteFree SetSort.set base (x#base) certificate =
        certificate :=
    hCertificateFixed base (x#base)
      (hCertificateFresh base (by simp))
  have hCertificateOneFixed :
      Term.substituteFree SetSort.set (base + 1)
          (x#(base + 1)) certificate =
        certificate :=
    hCertificateFixed (base + 1) (x#(base + 1))
      (hCertificateFresh (base + 1) (by simp))
  have hCertificateTwoFixed :
      Term.substituteFree SetSort.set (base + 2)
          (x#(base + 2)) certificate =
        certificate :=
    hCertificateFixed (base + 2) (x#(base + 2))
      (hCertificateFresh (base + 2) (by simp))
  have hCertificateThreeFixed :
      Term.substituteFree SetSort.set (base + 3)
          (x#(base + 3)) certificate =
        certificate :=
    hCertificateFixed (base + 3) (x#(base + 3))
      (hCertificateFresh (base + 3) (by simp))
  have hCertificateFourFixed :
      Term.substituteFree SetSort.set (base + 4)
          (x#(base + 4)) certificate =
        certificate :=
    hCertificateFixed (base + 4) (x#(base + 4))
      (hCertificateFresh (base + 4) (by simp))
  simpa [Formula.substituteFree_self, Term.substituteFree_self,
    Formula.substituteFree, Term.substituteFree,
    set_variable, fs_zfc_collection_condition_with_base,
    body, parameter, bodyTokenCode, bodyCode, shiftOne,
    shiftTwo, parameterOne, parameterTwo, parameterThree,
    fs_zfc_schema_certificate_bounds,
    fs_zfc_schema_payload_term,
    fs_zfc_schema_body_payload_term,
    hFormulaBaseFixed, hFormulaOneFixed, hFormulaTwoFixed,
    hFormulaThreeFixed, hFormulaFourFixed,
    hCertificateBaseFixed, hCertificateOneFixed,
    hCertificateTwoFixed, hCertificateThreeFixed,
    hCertificateFourFixed] using hBody

theorem fs_zfc_support_raw_formula_code_term_is_formula_code
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula) :
    Derives fs_zfc_support_raw_theory [] (
      formula_codeₘ(fs_zfc_formula_code_term formula)) := by
  unfold fs_zfc_formula_code_term
  cases hQuote : GodelQuotation.Numbered.quote? formula with
  | none =>
      rcases GodelQuotation.Numbered.quote?_exists hFormula with
        ⟨code, hCode⟩
      simp [hQuote] at hCode
  | some code =>
      simpa [hQuote] using
        fs_zfc_support_raw_derives_of_godel_quotation
          (GodelQuotation.Numbered.quote?_is_formula_code hQuote)

/-! ## Gödel 配对的地面计算 -/

private theorem fs_zfc_support_raw_membership_transport
    (left right first second : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set)
    (hFirstEquality :
      Derives fs_zfc_support_raw_theory [] (left ≐ₘ first))
    (hSecondEquality :
      Derives fs_zfc_support_raw_theory [] (right ≐ₘ second))
    (hMember :
      Derives fs_zfc_support_raw_theory [] (left ∈ₘ right)) :
    Derives fs_zfc_support_raw_theory [] (first ∈ₘ second) := by
  have hLeftTransport :=
    membership_left_iff_of_equality
      left first right hLeft hFirst hRight hFirstEquality
  have hRightTransport :=
    membership_right_iff_of_equality
      first right second hFirst hRight hSecond hSecondEquality
  exact FirstOrder.Derives.iffElimRight
    hRightTransport
    (FirstOrder.Derives.iffElimRight
      hLeftTransport hMember)

private theorem fs_zfc_support_raw_not_membership_transport
    (left right first second : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set)
    (hFirstEquality :
      Derives fs_zfc_support_raw_theory [] (left ≐ₘ first))
    (hSecondEquality :
      Derives fs_zfc_support_raw_theory [] (right ≐ₘ second))
    (hNotMember :
      Derives fs_zfc_support_raw_theory [] (¬ₘ (left ∈ₘ right))) :
    Derives fs_zfc_support_raw_theory [] (¬ₘ (first ∈ₘ second)) := by
  have hMemberAdmissible :
      Formula.Admissible (first ∈ₘ second) :=
    membership_formula_admissible hFirst hSecond
  nd_apply FirstOrder.Derives.negIntro
  have hMember :
      [first ∈ₘ second] ⊢ₘ[fs_zfc_support_raw_theory]
        first ∈ₘ second :=
    .assumption (by simp)
  have hLeftTransport :=
    membership_left_iff_of_equality
      left first right hLeft hFirst hRight hFirstEquality
  have hRightTransport :=
    membership_right_iff_of_equality
      first right second hFirst hRight hSecond hSecondEquality
  have hFirstRight :
      [first ∈ₘ second] ⊢ₘ[fs_zfc_support_raw_theory]
        first ∈ₘ right :=
    FirstOrder.Derives.iffElimLeft
      (FirstOrder.Derives.context_weaken_cons hRightTransport)
      hMember
  have hLeftRight :
      [first ∈ₘ second] ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ right :=
    FirstOrder.Derives.iffElimLeft
      (FirstOrder.Derives.context_weaken_cons hLeftTransport)
      hFirstRight
  exact FirstOrder.Derives.negElim
    hLeftRight
    (FirstOrder.Derives.context_weaken_cons hNotMember)

private theorem fs_zfc_support_raw_not_equality_transport
    (left right first second : SetTerm)
    (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set)
    (hFirstEquality :
      Derives fs_zfc_support_raw_theory [] (left ≐ₘ first))
    (hSecondEquality :
      Derives fs_zfc_support_raw_theory [] (right ≐ₘ second))
    (hNotEquality :
      Derives fs_zfc_support_raw_theory [] (¬ₘ (left ≐ₘ right))) :
    Derives fs_zfc_support_raw_theory [] (¬ₘ (first ≐ₘ second)) := by
  have hEqualityAdmissible :
      Formula.Admissible (first ≐ₘ second) :=
    Formula.Admissible.equal hFirst hSecond
  nd_apply FirstOrder.Derives.negIntro
  have hEquality :
      [first ≐ₘ second] ⊢ₘ[fs_zfc_support_raw_theory]
        first ≐ₘ second :=
    .assumption (by simp)
  have hSecondSymm :
      Derives fs_zfc_support_raw_theory [] (second ≐ₘ right) :=
    Metatheory.Derives.equality_symm
      hSecondEquality
  have hTransport :
      [first ≐ₘ second] ⊢ₘ[fs_zfc_support_raw_theory]
        left ≐ₘ right :=
    let hLeftSecond :
        [first ≐ₘ second] ⊢ₘ[fs_zfc_support_raw_theory]
          left ≐ₘ second :=
      Metatheory.Derives.equality_trans
        (FirstOrder.Derives.context_weaken_cons hFirstEquality)
        hEquality
    Metatheory.Derives.equality_trans
      hLeftSecond
      (FirstOrder.Derives.context_weaken_cons hSecondSymm)
  exact FirstOrder.Derives.negElim
    hTransport
    (FirstOrder.Derives.context_weaken_cons hNotEquality)

private theorem fs_zfc_support_raw_exponentiation_addition_value
    (base exponent addend : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      ((numₘ(base) ^ₘ numₘ(exponent)) +ₘ numₘ(addend)) ≐ₘ
        numₘ((base ^ exponent) + addend)) := by
  have hExponentRaw :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_finite_numeral_exponentiation
        base exponent)
  have hExponent :
      Derives fs_zfc_support_raw_theory [] (
        (numₘ(base) ^ₘ numₘ(exponent)) ≐ₘ
          numₘ(base ^ exponent)) :=
    Metatheory.Derives.equality_symm
      hExponentRaw
  have hAddRaw :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_finite_numeral_addition
        (base ^ exponent) addend)
  have hAdd :
      Derives fs_zfc_support_raw_theory [] (
        (numₘ(base ^ exponent) +ₘ numₘ(addend)) ≐ₘ
          numₘ((base ^ exponent) + addend)) :=
    Metatheory.Derives.equality_symm
      hAddRaw
  have hCongr :=
    natural_addition_term_congr_of_equalities
      (numₘ(base) ^ₘ numₘ(exponent))
      (numₘ(base ^ exponent))
      (numₘ(addend)) (numₘ(addend))
      (natural_exponentiation_term_admissible
        (numₘ(base)) (numₘ(exponent))
        (finite_numeral_term_admissible base)
        (finite_numeral_term_admissible exponent))
      (finite_numeral_term_admissible (base ^ exponent))
      (finite_numeral_term_admissible addend)
      (finite_numeral_term_admissible addend)
      hExponent
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(addend)))
  exact Metatheory.Derives.equality_trans
    hCongr hAdd

theorem fs_zfc_support_raw_godel_pair_value_eq
    (left right : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      godel_pairₘ(⟨numₘ(left), numₘ(right)⟩ₘ) ≐ₘ
        numₘ(godel_pair_value left right)) := by
  let pair : SetTerm := ⟨numₘ(left), numₘ(right)⟩ₘ
  let candidate : SetTerm := numₘ(godel_pair_value left right)
  have hLeft : Term.Admissible (numₘ(left)) SetSort.set :=
    finite_numeral_term_admissible left
  have hRight : Term.Admissible (numₘ(right)) SetSort.set :=
    finite_numeral_term_admissible right
  have hPair : Term.Admissible pair SetSort.set := by
    simpa [pair] using ordered_pair_term_admissible
      (numₘ(left)) (numₘ(right)) hLeft hRight
  have hCandidate : Term.Admissible candidate SetSort.set := by
    simpa [candidate] using
      finite_numeral_term_admissible (godel_pair_value left right)
  have hPairMember :
      Derives fs_zfc_support_raw_theory [] (pair ∈ₘ (ωₘ ×ₘ ωₘ)) := by
    let T : SetTheory :=
      Theory.union relation_plane_theory
        standard_sequence_semantics_theory
    have hLeftOmega :
        Derives T [] (numₘ(left) ∈ₘ ωₘ) :=
      FirstOrder.Derives.theory_weaken
        (fun _ hFormula => Or.inr hFormula)
        (standard_sequence_finite_numeral_mem_omega left)
    have hRightOmega :
        Derives T [] (numₘ(right) ∈ₘ ωₘ) :=
      FirstOrder.Derives.theory_weaken
        (fun _ hFormula => Or.inr hFormula)
        (standard_sequence_finite_numeral_mem_omega right)
    have hRule :
        Derives T [] (
          (numₘ(left) ∈ₘ ωₘ) ⟶ₘ
            (numₘ(right) ∈ₘ ωₘ) ⟶ₘ
              (⟨numₘ(left), numₘ(right)⟩ₘ ∈ₘ
                (ωₘ ×ₘ ωₘ))) :=
      FirstOrder.Derives.theory_weaken
        (fun _ hFormula => Or.inl hFormula)
        (ordered_pair_mem_cartesian_product
          ωₘ ωₘ (numₘ(left)) (numₘ(right))
          omega_term_admissible omega_term_admissible
          hLeft hRight)
    have hPairT :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim hRule hLeftOmega)
        hRightOmega
    apply FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        match hFormula with
        | Or.inl hRelation =>
            fs_zfc_support_raw_contains_relation_plane hRelation
        | Or.inr hSequence =>
            fs_zfc_support_raw_contains_standard_sequence_semantics
              hSequence)
    simpa [pair, T] using hPairT
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairing_definition_instance pair candidate) :=
    fs_zfc_support_raw_derives_of_godel_pairing
      (godel_pairing_definition_instance_derives
        pair candidate hPair hCandidate)
  have hContract :
      Derives fs_zfc_support_raw_theory [] (
        (candidate ≐ₘ godel_pairₘ(pair)) ↔ₘ
          godel_pairing_condition pair candidate) :=
    FirstOrder.Derives.impElim hDefinition hPairMember
  have hCandidateOmega :
      Derives fs_zfc_support_raw_theory [] (candidate ∈ₘ ωₘ) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_omega
        (godel_pair_value left right))
  have hPairLeftProjection :
      Derives fs_zfc_support_raw_theory [] (
        (pair)₀ₘ ≐ₘ numₘ(left)) := by
    apply FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_relation_plane
          (right_projection_operator_theory_subset_relation_plane_theory
            (left_projection_operator_theory_subset_right_projection_operator_theory
              hFormula)))
    simpa [pair] using
      ordered_pair_term_left_projection_eq
        (numₘ(left)) (numₘ(right)) hLeft hRight
  have hPairRightProjection :
      Derives fs_zfc_support_raw_theory [] (
        (pair)₁ₘ ≐ₘ numₘ(right)) := by
    apply FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_relation_plane
          (right_projection_operator_theory_subset_relation_plane_theory
            hFormula))
    simpa [pair] using
      ordered_pair_term_right_projection_eq
        (numₘ(left)) (numₘ(right)) hLeft hRight
  have hPairLeftTerm :
      Term.Admissible (pair)₀ₘ SetSort.set :=
    left_projection_term_admissible pair hPair
  have hPairRightTerm :
      Term.Admissible (pair)₁ₘ SetSort.set :=
    right_projection_term_admissible pair hPair
  have hPairLeftProjectionSymm :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(left) ≐ₘ (pair)₀ₘ) :=
    Metatheory.Derives.equality_symm
      hPairLeftProjection
  have hPairRightProjectionSymm :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(right) ≐ₘ (pair)₁ₘ) :=
    Metatheory.Derives.equality_symm
      hPairRightProjection
  by_cases hOrder : left < right
  · have hFirstCalculation :
        Derives fs_zfc_support_raw_theory [] (
          candidate ≐ₘ
            (((pair)₁ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ)) := by
      have hNumeric :=
        fs_zfc_support_raw_exponentiation_addition_value
          right 2 left
      have hProjectionPower :=
        Metatheory.Derives.binary_term_constructor_congr_of_equalities
          (fun base exponent => base ^ₘ exponent)
          (fun base exponent hBase hExponent =>
            natural_exponentiation_term_admissible
              base exponent hBase hExponent)
          (by intros; simp [Term.substituteFree])
          (pair)₁ₘ (numₘ(right))
          (numₘ(2)) (numₘ(2))
          hPairRightTerm hRight
          (finite_numeral_term_admissible 2)
          (finite_numeral_term_admissible 2)
          hPairRightProjection
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (numₘ(2)))
      have hProjectionSum :=
        natural_addition_term_congr_of_equalities
          ((pair)₁ₘ ^ₘ numₘ(2))
          (numₘ(right) ^ₘ numₘ(2))
          (pair)₀ₘ (numₘ(left))
          (natural_exponentiation_term_admissible
            (pair)₁ₘ (numₘ(2))
            hPairRightTerm (finite_numeral_term_admissible 2))
          (natural_exponentiation_term_admissible
            (numₘ(right)) (numₘ(2))
            hRight (finite_numeral_term_admissible 2))
          hPairLeftTerm hLeft
          hProjectionPower hPairLeftProjection
      have hCandidateToNumeric :
          Derives fs_zfc_support_raw_theory [] (
            candidate ≐ₘ
              ((numₘ(right) ^ₘ numₘ(2)) +ₘ numₘ(left))) := by
        simpa [candidate, godel_pair_value, hOrder] using
          Metatheory.Derives.equality_symm
            hNumeric
      have hNumericToPair :
          Derives fs_zfc_support_raw_theory [] (
            ((numₘ(right) ^ₘ numₘ(2)) +ₘ numₘ(left)) ≐ₘ
              (((pair)₁ₘ ^ₘ numₘ(2)) +ₘ (pair)₀ₘ)) :=
        Metatheory.Derives.equality_symm
          hProjectionSum
      have hResult := Metatheory.Derives.equality_trans
        hCandidateToNumeric hNumericToPair
      simpa [finite_numeral_term, successor_term] using hResult
    have hSecondNotMemberNumeral :
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ (numₘ(right) ∈ₘ numₘ(left))) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_not_mem_of_not_lt
          right left (by omega))
    have hSecondNotMember :=
      fs_zfc_support_raw_not_membership_transport
        (numₘ(right)) (numₘ(left))
        ((pair)₁ₘ) ((pair)₀ₘ)
        hRight hLeft hPairRightTerm hPairLeftTerm
        hPairRightProjectionSymm
        hPairLeftProjectionSymm
        hSecondNotMemberNumeral
    have hNotEqualityNumeral :
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ (numₘ(right) ≐ₘ numₘ(left))) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_ne
          (by omega : right ≠ left))
    have hNotEquality :=
      fs_zfc_support_raw_not_equality_transport
        (numₘ(right)) (numₘ(left))
        ((pair)₁ₘ) ((pair)₀ₘ)
        hPairRightTerm hPairLeftTerm
        hPairRightProjectionSymm
        hPairLeftProjectionSymm
        hNotEqualityNumeral
    have hNotNaturalLeq :
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ (natural_leq_condition (pair)₁ₘ (pair)₀ₘ)) := by
      have hConditionAdmissible :
          Formula.Admissible
            (natural_leq_condition (pair)₁ₘ (pair)₀ₘ) := by
        simpa [natural_leq_condition] using
          Formula.Admissible.disj
            (Formula.Admissible.equal hPairRightTerm hPairLeftTerm)
            (membership_formula_admissible
              hPairRightTerm hPairLeftTerm)
      nd_apply FirstOrder.Derives.negIntro
      have hCondition :
          [natural_leq_condition (pair)₁ₘ (pair)₀ₘ]
            ⊢ₘ[fs_zfc_support_raw_theory]
              natural_leq_condition (pair)₁ₘ (pair)₀ₘ := by
        simpa [natural_leq_condition] using
          (FirstOrder.Derives.assumption
            (T := fs_zfc_support_raw_theory)
            (Γ := [natural_leq_condition (pair)₁ₘ (pair)₀ₘ])
            (φ := natural_leq_condition (pair)₁ₘ (pair)₀ₘ)
            (by simp))
      simpa [natural_leq_condition] using
        FirstOrder.Derives.disjElim hCondition
          (by
            have hEqualityAdmissible :
                Formula.Admissible ((pair)₁ₘ ≐ₘ (pair)₀ₘ) :=
              Formula.Admissible.equal hPairRightTerm hPairLeftTerm
            have hEquality :
                ((pair)₁ₘ ≐ₘ (pair)₀ₘ) ::
                  [natural_leq_condition (pair)₁ₘ (pair)₀ₘ]
                  ⊢ₘ[fs_zfc_support_raw_theory]
                    (pair)₁ₘ ≐ₘ (pair)₀ₘ :=
              .assumption (by simp)
            exact FirstOrder.Derives.negElim
              hEquality
              (FirstOrder.Derives.context_weaken
                (Γ := [])
                (Δ := [(pair)₁ₘ ≐ₘ (pair)₀ₘ,
                  natural_leq_condition (pair)₁ₘ (pair)₀ₘ])
                (by simp) hNotEquality))
          (by
            have hMembershipAdmissible :
                Formula.Admissible ((pair)₁ₘ ∈ₘ (pair)₀ₘ) :=
              membership_formula_admissible
                hPairRightTerm hPairLeftTerm
            have hMembership :
                ((pair)₁ₘ ∈ₘ (pair)₀ₘ) ::
                  [natural_leq_condition (pair)₁ₘ (pair)₀ₘ]
                  ⊢ₘ[fs_zfc_support_raw_theory]
                    (pair)₁ₘ ∈ₘ (pair)₀ₘ :=
              .assumption (by simp)
            exact FirstOrder.Derives.negElim
              hMembership
              (FirstOrder.Derives.context_weaken
                (Γ := [])
                (Δ := [(pair)₁ₘ ∈ₘ (pair)₀ₘ,
                  natural_leq_condition (pair)₁ₘ (pair)₀ₘ])
                (by simp) hSecondNotMember))
    have hFirstImp :
        Derives fs_zfc_support_raw_theory [] (
          ((pair)₀ₘ ∈ₘ (pair)₁ₘ) ⟶ₘ
            (candidate ≐ₘ
              (((pair)₁ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ))) := by
      nd_apply FirstOrder.Derives.impIntro
      exact FirstOrder.Derives.context_weaken_cons hFirstCalculation
    have hSecondImp :
        Derives fs_zfc_support_raw_theory [] (
          (natural_leq_condition (pair)₁ₘ (pair)₀ₘ) ⟶ₘ
            (candidate ≐ₘ
              ((((pair)₀ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ) +ₘ
                (pair)₁ₘ))) := by
      have hConditionAdmissible :
          Formula.Admissible
            (natural_leq_condition (pair)₁ₘ (pair)₀ₘ) := by
        simpa [natural_leq_condition] using
          Formula.Admissible.disj
            (Formula.Admissible.equal hPairRightTerm hPairLeftTerm)
            (membership_formula_admissible
              hPairRightTerm hPairLeftTerm)
      have hSecondTermAdmissible :
          Term.Admissible
            ((((pair)₀ₘ ^ₘ numₘ(2)) +ₘ (pair)₀ₘ) +ₘ
              (pair)₁ₘ) SetSort.set :=
        natural_addition_term_admissible
          (((pair)₀ₘ ^ₘ numₘ(2)) +ₘ (pair)₀ₘ) (pair)₁ₘ
          (natural_addition_term_admissible
            ((pair)₀ₘ ^ₘ numₘ(2)) (pair)₀ₘ
            (natural_exponentiation_term_admissible
              (pair)₀ₘ (numₘ(2))
              hPairLeftTerm (finite_numeral_term_admissible 2))
            hPairLeftTerm)
          hPairRightTerm
      have hSecondFormulaAdmissible :
          Formula.Admissible
            (candidate ≐ₘ
              ((((pair)₀ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ) +ₘ
                (pair)₁ₘ)) := by
        simpa [finite_numeral_term, successor_term] using
          Formula.Admissible.equal hCandidate hSecondTermAdmissible
      nd_apply FirstOrder.Derives.impIntro
      exact FirstOrder.Derives.falsumElim
        (FirstOrder.Derives.negElim
          (.assumption (by simp))
          (FirstOrder.Derives.context_weaken_cons hNotNaturalLeq))
    have hCondition :=
      FirstOrder.Derives.conjIntro hCandidateOmega
        (FirstOrder.Derives.conjIntro hFirstImp hSecondImp)
    have hCandidatePair :
        Derives fs_zfc_support_raw_theory [] (
          candidate ≐ₘ godel_pairₘ(pair)) :=
      FirstOrder.Derives.iffElimLeft hContract hCondition
    have hResult :=
      Metatheory.Derives.equality_symm
        hCandidatePair
    simpa [pair, candidate] using hResult
  · have hNotFirstMemberNumeral :
        Derives fs_zfc_support_raw_theory [] (
          ¬ₘ (numₘ(left) ∈ₘ numₘ(right))) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_not_mem_of_not_lt
          left right (by omega))
    have hNotFirstMember :=
      fs_zfc_support_raw_not_membership_transport
        (numₘ(left)) (numₘ(right))
        ((pair)₀ₘ) ((pair)₁ₘ)
        hLeft hRight hPairLeftTerm hPairRightTerm
        hPairLeftProjectionSymm
        hPairRightProjectionSymm
        hNotFirstMemberNumeral
    have hSecondCalculation :
        Derives fs_zfc_support_raw_theory [] (
          candidate ≐ₘ
            ((((pair)₀ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ) +ₘ
              (pair)₁ₘ)) := by
      have hInnerNumeric :=
        fs_zfc_support_raw_exponentiation_addition_value
          left 2 left
      have hOuterNumericRaw :=
        fs_zfc_support_raw_derives_of_standard_sequence
          (standard_token_sequence_finite_numeral_addition
            (left ^ 2 + left) right)
      have hOuterNumeric :
          Derives fs_zfc_support_raw_theory [] (
            (numₘ(left ^ 2 + left) +ₘ numₘ(right)) ≐ₘ
              numₘ((left ^ 2 + left) + right)) :=
        Metatheory.Derives.equality_symm
          hOuterNumericRaw
      have hInnerProjection :=
        Metatheory.Derives.binary_term_constructor_congr_of_equalities
          (fun base exponent => base ^ₘ exponent)
          (fun base exponent hBase hExponent =>
            natural_exponentiation_term_admissible
              base exponent hBase hExponent)
          (by intros; simp [Term.substituteFree])
          (pair)₀ₘ (numₘ(left))
          (numₘ(2)) (numₘ(2))
          hPairLeftTerm hLeft
          (finite_numeral_term_admissible 2)
          (finite_numeral_term_admissible 2)
          hPairLeftProjection
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) (numₘ(2)))
      have hInnerSumProjection :=
        natural_addition_term_congr_of_equalities
          ((pair)₀ₘ ^ₘ numₘ(2))
          (numₘ(left) ^ₘ numₘ(2))
          (pair)₀ₘ (numₘ(left))
          (natural_exponentiation_term_admissible
            (pair)₀ₘ (numₘ(2))
            hPairLeftTerm (finite_numeral_term_admissible 2))
          (natural_exponentiation_term_admissible
            (numₘ(left)) (numₘ(2))
            hLeft (finite_numeral_term_admissible 2))
          hPairLeftTerm hLeft
          hInnerProjection hPairLeftProjection
      have hInnerToNumeric :=
        Metatheory.Derives.equality_trans
          hInnerSumProjection
          hInnerNumeric
      have hOuterProjection :=
        natural_addition_term_congr_of_equalities
          (((pair)₀ₘ ^ₘ numₘ(2)) +ₘ (pair)₀ₘ)
          (numₘ(left ^ 2 + left))
          (pair)₁ₘ (numₘ(right))
          (natural_addition_term_admissible
            ((pair)₀ₘ ^ₘ numₘ(2)) (pair)₀ₘ
            (natural_exponentiation_term_admissible
              (pair)₀ₘ (numₘ(2))
              hPairLeftTerm (finite_numeral_term_admissible 2))
            hPairLeftTerm)
          (finite_numeral_term_admissible (left ^ 2 + left))
          hPairRightTerm hRight
          hInnerToNumeric hPairRightProjection
      have hOuterToNumeric :=
        Metatheory.Derives.equality_trans
          hOuterProjection
          hOuterNumeric
      have hResult := Metatheory.Derives.equality_symm
        hOuterToNumeric
      simpa [candidate, godel_pair_value, if_neg hOrder,
        finite_numeral_term, successor_term] using hResult
    have hFirstImp :
        Derives fs_zfc_support_raw_theory [] (
          ((pair)₀ₘ ∈ₘ (pair)₁ₘ) ⟶ₘ
            (candidate ≐ₘ
              (((pair)₁ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ))) := by
      have hFirstTermAdmissible :
          Term.Admissible
            (((pair)₁ₘ ^ₘ numₘ(2)) +ₘ (pair)₀ₘ) SetSort.set :=
        natural_addition_term_admissible
          ((pair)₁ₘ ^ₘ numₘ(2)) (pair)₀ₘ
          (natural_exponentiation_term_admissible
            (pair)₁ₘ (numₘ(2))
            hPairRightTerm (finite_numeral_term_admissible 2))
          hPairLeftTerm
      have hFirstFormulaAdmissible :
          Formula.Admissible
            (candidate ≐ₘ
              (((pair)₁ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ)) := by
        simpa [finite_numeral_term, successor_term] using
          Formula.Admissible.equal hCandidate hFirstTermAdmissible
      nd_apply FirstOrder.Derives.impIntro
      exact FirstOrder.Derives.falsumElim
        (FirstOrder.Derives.negElim
          (.assumption (by simp))
          (FirstOrder.Derives.context_weaken_cons hNotFirstMember))
    have hSecondImp :
        Derives fs_zfc_support_raw_theory [] (
          (natural_leq_condition (pair)₁ₘ (pair)₀ₘ) ⟶ₘ
            (candidate ≐ₘ
              ((((pair)₀ₘ ^ₘ Sₘ(Sₘ(∅ₘ))) +ₘ (pair)₀ₘ) +ₘ
                (pair)₁ₘ))) := by
      have hConditionAdmissible :
          Formula.Admissible
            (natural_leq_condition (pair)₁ₘ (pair)₀ₘ) := by
        simpa [natural_leq_condition] using
          Formula.Admissible.disj
            (Formula.Admissible.equal hPairRightTerm hPairLeftTerm)
            (membership_formula_admissible
              hPairRightTerm hPairLeftTerm)
      nd_apply FirstOrder.Derives.impIntro
      exact FirstOrder.Derives.context_weaken_cons hSecondCalculation
    have hCondition :=
      FirstOrder.Derives.conjIntro hCandidateOmega
        (FirstOrder.Derives.conjIntro hFirstImp hSecondImp)
    have hCandidatePair :
        Derives fs_zfc_support_raw_theory [] (
          candidate ≐ₘ godel_pairₘ(pair)) :=
      FirstOrder.Derives.iffElimLeft hContract hCondition
    have hResult :=
      Metatheory.Derives.equality_symm
        hCandidatePair
    simpa [pair, candidate] using hResult

/-! ## checked 逻辑行的第一条端到端分支 -/

/-- 自蕴含命题公理可以产生一个实际的 ZFC 内部逻辑公理码。 -/
theorem fs_zfc_support_hilbert_self_implication_logical_axiom_code_exists
    {body : SetFormula}
    (hBody : Formula.Admissible body) :
    ∃ code,
      GodelQuotation.Numbered.quote? (Formula.imp body
          (Formula.imp body body)) = some code ∧
      HilbertDerives fs_zfc_support_theory
        (Formula.hilbertize SetSort.set
          (logical_axiom_codeₘ(code))) := by
  rcases GodelQuotation.Numbered.quote?_exists hBody with
    ⟨bodyCode, hBodyQuote⟩
  have hBodyCodeBoundary :=
    GodelQuotation.Numbered.quote?_code_boundary hBodyQuote
  have hBodyCodeAdmissible :
      Term.Admissible bodyCode SetSort.set :=
    hBodyCodeBoundary.1
  have hBodyCodeClosed :
      Term.freeSupport bodyCode = [] :=
    hBodyCodeBoundary.2
  have hBodyFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(bodyCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code hBodyQuote)
  let code := self_implication_axiom_code_term bodyCode
  have hCode :
      Term.Admissible code SetSort.set :=
    self_implication_axiom_code_term_admissible
      bodyCode hBodyCodeAdmissible
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hBodyCodeClosed]
  have hSelfMember :=
    fs_zfc_support_raw_self_implication_axiom_member
      bodyCode hBodyCodeAdmissible hBodyCodeClosed
      hBodyFormulaCode
  have hImplicationDistribution :
      Formula.Admissible (code ∈ₘ ImpDistribAxiomsₘ) :=
    membership_formula_admissible hCode
      implication_distribution_axiom_set_term_admissible
  have hSelfImplication :
      Formula.Admissible (code ∈ₘ SelfImpAxiomsₘ) :=
    membership_formula_admissible hCode
      self_implication_axiom_set_term_admissible
  have hWeakening :
      Formula.Admissible (code ∈ₘ WeakeningAxiomsₘ) :=
    membership_formula_admissible hCode
      weakening_axiom_set_term_admissible
  have hContradiction :
      Formula.Admissible (code ∈ₘ ContradictionAxiomsₘ) :=
    membership_formula_admissible hCode
      contradiction_axiom_set_term_admissible
  have hClassical :
      Formula.Admissible (code ∈ₘ ClassicalAxiomsₘ) :=
    membership_formula_admissible hCode
      classical_axiom_set_term_admissible
  have hExplosion :
      Formula.Admissible (code ∈ₘ ExplosionAxiomsₘ) :=
    membership_formula_admissible hCode
      explosion_axiom_set_term_admissible
  have hCaseAnalysis :
      Formula.Admissible (code ∈ₘ CaseAnalysisAxiomsₘ) :=
    membership_formula_admissible hCode
      case_analysis_axiom_set_term_admissible
  have hSpecialization :
      Formula.Admissible (code ∈ₘ SpecializationAxiomsₘ) :=
    membership_formula_admissible hCode
      specialization_axiom_set_term_admissible
  have hQuantifierDistribution :
      Formula.Admissible (code ∈ₘ ForallDistribAxiomsₘ) :=
    membership_formula_admissible hCode
      quantifier_distribution_axiom_set_term_admissible
  have hVacuousQuantifier :
      Formula.Admissible (code ∈ₘ VacuousForallAxiomsₘ) :=
    membership_formula_admissible hCode
      vacuous_quantifier_axiom_set_term_admissible
  have hEqualitySubstitution :
      Formula.Admissible (code ∈ₘ EqualitySubstAxiomsₘ) :=
    membership_formula_admissible hCode
      equality_substitution_axiom_set_term_admissible
  have hEqualityReflexivity :
      Formula.Admissible (code ∈ₘ EqualityReflAxiomsₘ) :=
    membership_formula_admissible hCode
      equality_reflexivity_axiom_set_term_admissible
  let hEqualityTail : SetFormula :=
    (code ∈ₘ EqualitySubstAxiomsₘ) ∨ₘ
      (code ∈ₘ EqualityReflAxiomsₘ)
  let hVacuousTail : SetFormula :=
    (code ∈ₘ VacuousForallAxiomsₘ) ∨ₘ hEqualityTail
  let hQuantifierTail : SetFormula :=
    (code ∈ₘ ForallDistribAxiomsₘ) ∨ₘ hVacuousTail
  let hSpecializationTail : SetFormula :=
    (code ∈ₘ SpecializationAxiomsₘ) ∨ₘ hQuantifierTail
  let hCaseAnalysisTail : SetFormula :=
    (code ∈ₘ CaseAnalysisAxiomsₘ) ∨ₘ hSpecializationTail
  let hExplosionTail : SetFormula :=
    (code ∈ₘ ExplosionAxiomsₘ) ∨ₘ hCaseAnalysisTail
  let hClassicalTail : SetFormula :=
    (code ∈ₘ ClassicalAxiomsₘ) ∨ₘ hExplosionTail
  let hContradictionTail : SetFormula :=
    (code ∈ₘ ContradictionAxiomsₘ) ∨ₘ hClassicalTail
  let hTailFormula : SetFormula :=
    (code ∈ₘ WeakeningAxiomsₘ) ∨ₘ hContradictionTail
  have hEqualityTailAdmissible :
      Formula.Admissible hEqualityTail := by
    dsimp [hEqualityTail]
    exact Formula.Admissible.disj
      hEqualitySubstitution hEqualityReflexivity
  have hVacuousTailAdmissible :
      Formula.Admissible hVacuousTail := by
    dsimp [hVacuousTail]
    exact Formula.Admissible.disj
      hVacuousQuantifier hEqualityTailAdmissible
  have hQuantifierTailAdmissible :
      Formula.Admissible hQuantifierTail := by
    dsimp [hQuantifierTail]
    exact Formula.Admissible.disj
      hQuantifierDistribution hVacuousTailAdmissible
  have hSpecializationTailAdmissible :
      Formula.Admissible hSpecializationTail := by
    dsimp [hSpecializationTail]
    exact Formula.Admissible.disj
      hSpecialization hQuantifierTailAdmissible
  have hCaseAnalysisTailAdmissible :
      Formula.Admissible hCaseAnalysisTail := by
    dsimp [hCaseAnalysisTail]
    exact Formula.Admissible.disj
      hCaseAnalysis hSpecializationTailAdmissible
  have hExplosionTailAdmissible :
      Formula.Admissible hExplosionTail := by
    dsimp [hExplosionTail]
    exact Formula.Admissible.disj
      hExplosion hCaseAnalysisTailAdmissible
  have hClassicalTailAdmissible :
      Formula.Admissible hClassicalTail := by
    dsimp [hClassicalTail]
    exact Formula.Admissible.disj
      hClassical hExplosionTailAdmissible
  have hContradictionTailAdmissible :
      Formula.Admissible hContradictionTail := by
    dsimp [hContradictionTail]
    exact Formula.Admissible.disj
      hContradiction hClassicalTailAdmissible
  have hTail :
      Formula.Admissible hTailFormula := by
    dsimp [hTailFormula]
    exact Formula.Admissible.disj
      hWeakening hContradictionTailAdmissible
  let hSelfTailFormula : SetFormula :=
    (code ∈ₘ SelfImpAxiomsₘ) ∨ₘ hTailFormula
  have hSelfTail :
      Derives fs_zfc_support_raw_theory [] hSelfTailFormula := by
    dsimp [hSelfTailFormula]
    exact FirstOrder.Derives.disjIntroLeft hSelfMember
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        base_logical_axiom_condition code) := by
    simpa [base_logical_axiom_condition, code] using
      (FirstOrder.Derives.disjIntroRight hSelfTail)
  have hLogicalRaw :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hLogical :=
    fs_zfc_support_hilbert_derives_of_raw hLogicalRaw
  have hBodyHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize
            GodelQuotation.QuotationNumbering.objectSort body) =
        some bodyCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hBodyQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp body (Formula.imp body body)) =
        some code := by
    simp [code, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hBodyHilbertQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
