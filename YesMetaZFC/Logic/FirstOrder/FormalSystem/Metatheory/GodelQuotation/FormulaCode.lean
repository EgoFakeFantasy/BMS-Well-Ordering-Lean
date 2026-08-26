import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.DefinitionContracts
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequence
/-!
# Gödel quotation 的对象编码闭包
本模块把文献 `BYFH ⊆ XuLe`、`cBDS ⊆ BDS` 以及公式构造递归闭包落实为
`Derives` 定理。核心公式集继续使用无有限级别护栏的最小闭包；标准序列语义与
表达式定义理论在本层显式联合，以精确记录符号串正确性所需的对象集合论依赖。
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
/-- Gödel quotation 编码正确性使用的稳定对象理论入口。 -/
def godel_quotation_theory : SetTheory :=
  Theory.union standard_sequence_semantics_theory
    substitution_variable_theory
@[derive_close_sentence]
theorem godel_quotation_theory_sentence
    {formula : SetFormula} (hFormula : godel_quotation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with hFormula | hFormula
  · exact standard_sequence_semantics_theory_sentence hFormula
  · exact substitution_variable_theory_sentence hFormula
/-- 标准序列语义理论嵌入 Gödel quotation 联合理论。 -/
theorem gq_weaken_standard_sequence
    {Γ : Context signature}
    {φ : SetFormula}
    (h : Γ ⊢ₘ[standard_sequence_semantics_theory] φ) :
    Γ ⊢ₘ[godel_quotation_theory] φ :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inl hFormula) h
/-- 单点集运算理论嵌入 Gödel quotation 联合理论。 -/
theorem gq_weaken_singleton {φ : SetFormula} (h : ⊢ₘ[singleton_operator_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ :=
  gq_weaken_standard_sequence <|
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inl hFormula)
      h
/-- 表达式替换定义理论嵌入 Gödel quotation 联合理论。 -/
theorem gq_weaken_substitution_variable {φ : SetFormula} (h : ⊢ₘ[substitution_variable_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inr hFormula) h
/-- 公式码定义理论嵌入 Gödel quotation 联合理论。 -/
theorem gq_weaken_formula_code {φ : SetFormula} (h : ⊢ₘ[formula_code_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_substitution_variable
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      formula_code_theory_subset_substitution_variable_theory hFormula) h
/-- 公式构造定义理论嵌入 Gödel quotation 联合理论。 -/
theorem gq_weaken_formula_constructor {φ : SetFormula} (h : ⊢ₘ[formula_constructor_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_formula_code
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      formula_constructor_theory_subset_formula_code_theory hFormula) h
/-- 符号编码运算定义理论嵌入 Gödel quotation 联合理论。 -/
theorem gq_weaken_symbol_operator {φ : SetFormula} (h : ⊢ₘ[symbol_code_operator_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_formula_constructor
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      symbol_code_operator_theory_subset_formula_constructor_theory hFormula) h
private theorem gq_weaken_formal_language {φ : SetFormula} (h : ⊢ₘ[formal_language_encoding_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_symbol_operator
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      formal_language_encoding_theory_subset_symbol_code_operator_theory
        hFormula) h
theorem gq_weaken_term_code_set {φ : SetFormula} (h : ⊢ₘ[term_code_set_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_formal_language
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      term_sequence_encoding_theory_subset_formal_language_encoding_theory (term_code_predicate_theory_subset_term_sequence_encoding_theory
          (term_code_set_theory_subset_term_code_predicate_theory hFormula))) h
theorem gq_weaken_term_code_predicate {φ : SetFormula} (h : ⊢ₘ[term_code_predicate_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_formal_language
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      term_sequence_encoding_theory_subset_formal_language_encoding_theory (term_code_predicate_theory_subset_term_sequence_encoding_theory
          hFormula)) h
theorem gq_weaken_atomic_formula {φ : SetFormula} (h : ⊢ₘ[atomic_formula_encoding_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_formal_language
  simpa [formal_language_encoding_theory] using h
private theorem gq_weaken_variable_symbol {φ : SetFormula} (h : ⊢ₘ[variable_symbol_encoding_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_formal_language
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      term_sequence_encoding_theory_subset_formal_language_encoding_theory (term_code_predicate_theory_subset_term_sequence_encoding_theory
          (term_code_set_theory_subset_term_code_predicate_theory (formal_language_symbol_theory_subset_term_code_set_theory
              (function_symbol_encoding_theory_subset_formal_language_symbol_theory (constant_symbol_encoding_theory_subset_function_symbol_encoding_theory
                  (variable_symbol_encoding_theory_subset_constant_symbol_encoding_theory
                    hFormula))))))) h
private theorem gq_weaken_constant_symbol {φ : SetFormula} (h : ⊢ₘ[constant_symbol_encoding_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_formal_language
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      term_sequence_encoding_theory_subset_formal_language_encoding_theory (term_code_predicate_theory_subset_term_sequence_encoding_theory
          (term_code_set_theory_subset_term_code_predicate_theory (formal_language_symbol_theory_subset_term_code_set_theory
              (function_symbol_encoding_theory_subset_formal_language_symbol_theory (constant_symbol_encoding_theory_subset_function_symbol_encoding_theory
                  hFormula)))))) h
/--
把关系平面理论中的推导统一弱化到 Gödel quotation 理论。
quotation 的可代入性、出现性与公式码模块都需要这个公共入口；将它公开可避免
下游重复展开整条理论包含链。
-/
theorem gq_weaken_relation_plane {φ : SetFormula} (h : ⊢ₘ[relation_plane_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_standard_sequence
  have hFunction : ⊢ₘ[function_application_theory] φ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_plane_theory_subset_function_application_theory hFormula) h
  exact FirstOrder.Derives.theory_weaken (fun _ hf => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf)))))))))) hFunction
/-- 子集定义理论嵌入 Gödel quotation 联合理论。 -/
theorem gq_weaken_subset {φ : SetFormula} (h : ⊢ₘ[subset_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_relation_plane
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula => subset_theory_subset_relation_plane_theory hFormula) h
private theorem gq_weaken_function_predicate {φ : SetFormula} (h : ⊢ₘ[function_predicate_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_standard_sequence
  apply standard_sequence_weaken_function_application
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      function_predicate_theory_subset_function_application_theory
        hFormula) h
private theorem gq_weaken_singleton_operator {φ : SetFormula} (h : ⊢ₘ[singleton_operator_theory] φ) :
    ⊢ₘ[godel_quotation_theory] φ := by
  apply gq_weaken_relation_plane
  exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
      relation_function_theory_subset_relation_plane_theory <|
        singleton_operator_theory_subset_relation_function_theory
          hFormula) h
private theorem gq_finite_numeral_open (value depth : Nat) (replacement : SetTerm) :
    Term.openAt SetSort.set depth replacement (numₘ(value)) =
      numₘ(value) :=
  Term.openAt_eq_self_of_boundClosed
    SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
private theorem gq_finite_numeral_close (value : Nat) (id : FreeVarId) (depth : Nat) :
    Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
      numₘ(value) :=
  Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    SetSort.set id depth (numₘ(value)) (finite_numeral_term_admissible value).2 (by simp [finite_numeral_term_freeSupport])
/-! ## 定义合同的通用消去接口 -/
/-- 在联合理论中把对象子集关系消去为逐点成员蕴含。 -/
theorem gq_subset_member_imp
    {Γ : Context signature} (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hElement : Term.Admissible element SetSort.set) (hSubset : Γ ⊢ₘ[godel_quotation_theory] left ⊆ₘ right) :
    Γ ⊢ₘ[godel_quotation_theory] (element ∈ₘ left) ⟶ₘ (element ∈ₘ right) := by
  have hDefinition :
      Γ ⊢ₘ[godel_quotation_theory] (left ⊆ₘ right) ↔ₘ subset_condition left right :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_subset (subset_definition_instance_derives_of_admissible
            left right hLeft hRight)
  have hCondition := FirstOrder.Derives.iffElimRight
    hDefinition hSubset
  have hAt := FirstOrder.Derives.forall_elim
    (term := element) hCondition
  have hLeftOpen := Term.openAt_eq_self_of_boundClosed
    SetSort.set 0 element left hLeft.2
  have hRightOpen := Term.openAt_eq_self_of_boundClosed
    SetSort.set 0 element right hRight.2
  simpa [subset_condition, Formula.openAt,
    Term.openAt, hLeftOpen, hRightOpen] using hAt
/-- 在联合理论中把对象子集关系消去为具体成员传递。 -/
theorem gq_subset_member
    {Γ : Context signature} (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hElement : Term.Admissible element SetSort.set) (hSubset : Γ ⊢ₘ[godel_quotation_theory] left ⊆ₘ right)
    (hMember : Γ ⊢ₘ[godel_quotation_theory] element ∈ₘ left) :
    Γ ⊢ₘ[godel_quotation_theory] element ∈ₘ right :=
  FirstOrder.Derives.impElim (gq_subset_member_imp
      left right element hLeft hRight hElement hSubset)
    hMember
/--
变量收集项的基础成员反演。
若 `source` 是闭编码项且已经落入项码或公式码集合，那么 `varsₘ(source)` 中的任意
成员必为变量符号，并且它的首 token 确实在 `source` 的某个定义域位置出现。结论
保留为对象层蕴含，便于后续在量词与假设上下文中直接弱化使用。
-/
theorem gq_variable_collection_member_inversion (source : SetTerm) (hSource : Numbered.CodeBoundary source) (hSourceCode :
      ⊢ₘ[godel_quotation_theory]
        source ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ)) :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 314], ((x#314 ∈ₘ varsₘ(source)) ⟶ₘ ((x#314 ∈ₘ VarSymₘ) ∧ₘ
            variable_symbol_occurs_condition (x#314) source)) := by
  let variableCode : SetTerm := x#314
  let candidate := varsₘ(source)
  let member : SetFormula := variableCode ∈ₘ candidate
  have hVariable :
      Term.Admissible variableCode SetSort.set := by
    simp [variableCode, set_variable_admissible]
  have hCandidate :
      Term.Admissible candidate SetSort.set := by
    simpa [candidate] using
      variable_collection_term_admissible source hSource.1
  have hCandidateSupport :
      Term.freeSupport candidate = [] := by
    simp [candidate, Term.freeSupport, Term.freeSupportList,
      hSource.2]
  have hFresh :
      ReservedIdsFresh [312, 313] [source, candidate] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl
    · rw [hSource.2]
      exact List.not_mem_nil
    · rw [hCandidateSupport]
      exact List.not_mem_nil
  have hDefinition :=
    gq_weaken_substitution_variable <|
      variable_collection_definition_instance_derives
        source candidate hSource.1 hCandidate hFresh
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        candidate ≐ₘ varsₘ(source) := by
    simpa [candidate] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) candidate)
  have hSpec :
      ⊢ₘ[godel_quotation_theory]
        variable_collection_spec source candidate :=
    FirstOrder.Derives.iffElimRight (FirstOrder.Derives.impElim hDefinition hSourceCode)
      hReflexive
  have hSubset :
      ⊢ₘ[godel_quotation_theory]
        candidate ⊆ₘ VarSymₘ :=
    FirstOrder.Derives.conjElimLeft hSpec
  have hPointwise :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 313], ((x#313 ∈ₘ VarSymₘ) ⟶ₘ (((x#313 ∈ₘ candidate) ↔ₘ
              variable_symbol_occurs_condition (x#313) source))) :=
    FirstOrder.Derives.conjElimRight hSpec
  have hSubsetDefinition := gq_weaken_subset (subset_definition_instance_derives_of_admissible
      candidate VarSymₘ hCandidate
      variable_symbol_set_term_admissible)
  have hSubsetCondition :=
    FirstOrder.Derives.iffElimRight
      hSubsetDefinition hSubset
  have hSubsetAt :=
    FirstOrder.Derives.forall_elim
      (term := variableCode) hSubsetCondition
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  have hVariableSymbolsOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term VarSymₘ = VarSymₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term VarSymₘ
      variable_symbol_set_term_admissible.2
  have hSourceClose313 (depth : Nat) :
      Term.closeFreeAt SetSort.set 313 depth source = source :=
    Numbered.CodeBoundary.closeFreeAt_eq
      hSource 313 depth
  have hSourceClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth source = source :=
    Numbered.CodeBoundary.closeFreeAt_eq hSource id depth
  have hCandidateClose313 (depth : Nat) :
      Term.closeFreeAt SetSort.set 313 depth candidate = candidate :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 313 depth candidate hCandidate.2 (by rw [hCandidateSupport]; exact List.not_mem_nil)
  have hCandidateClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth candidate = candidate :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth candidate hCandidate.2 (by rw [hCandidateSupport]; exact List.not_mem_nil)
  have hSubsetAt' :
      ⊢ₘ[godel_quotation_theory] (variableCode ∈ₘ candidate) ⟶ₘ (variableCode ∈ₘ VarSymₘ) := by
    simpa [subset_condition, Formula.openAt,
      Term.openAt, hCandidateOpen,
      hVariableSymbolsOpen] using hSubsetAt
  have hPointwiseAt :=
    FirstOrder.Derives.forall_elim
      (term := variableCode) hPointwise
  have hPointwiseAt' :
      ⊢ₘ[godel_quotation_theory] (variableCode ∈ₘ VarSymₘ) ⟶ₘ (((variableCode ∈ₘ candidate) ↔ₘ
            variable_symbol_occurs_condition
              variableCode source)) := by
    simpa [variable_symbol_occurs_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      variableCode,
      hCandidateOpen, hVariableSymbolsOpen,
      Numbered.CodeBoundary.openAt_eq hSource,
      Numbered.CodeBoundary.substituteFree_eq hSource,
      hSourceClose313, hSourceClose,
      hCandidateClose313, hCandidateClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using
      hPointwiseAt
  have hOpen :
      ⊢ₘ[godel_quotation_theory]
      member ⟶ₘ ((variableCode ∈ₘ VarSymₘ) ∧ₘ
          variable_symbol_occurs_condition variableCode source) := by
    have hMemberAdmissible :
        Formula.Admissible member := by
      simpa [member, candidate] using
        membership_formula_admissible hVariable hCandidate
    nd_apply FirstOrder.Derives.impIntro
    have hMember :
        [member] ⊢ₘ[godel_quotation_theory]
          variableCode ∈ₘ candidate := by
      have hMember' :
          [member] ⊢ₘ[godel_quotation_theory] member :=
        FirstOrder.Derives.assumption
          (T := godel_quotation_theory) (Γ := [member]) (by simp)
      simpa [member, candidate] using hMember'
    have hVariableSymbol :
        [member] ⊢ₘ[godel_quotation_theory]
          variableCode ∈ₘ VarSymₘ :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hSubsetAt')
        hMember
    have hOccurs :
        [member] ⊢ₘ[godel_quotation_theory]
          variable_symbol_occurs_condition variableCode source :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hPointwiseAt')
          hVariableSymbol)
        hMember
    exact FirstOrder.Derives.conjIntro hVariableSymbol hOccurs
  have hTheoryFresh :
      ∀ formula, godel_quotation_theory formula → (SetSort.set, 314) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := godel_quotation_theory) (Γ := []) (sort := SetSort.set) (eigen := 314)
      hTheoryFresh (by simp) hOpen
  simpa [variableCode, candidate, member] using hGeneralized

/--
变量收集定义的正向成员接口。源码是合法表达式码、候选是变量符号且确实在源码中
出现时，该候选属于 `varsₘ(source)`；结论保留为对象层蕴含，供任意上下文弱化。
-/
theorem gq_variable_collection_member_of_occurrence_imp
    (source variableCode : SetTerm)
    (hSource : Numbered.CodeBoundary source)
    (hVariable : Numbered.CodeBoundary variableCode) :
    ⊢ₘ[godel_quotation_theory]
      source ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) ⟶ₘ
        variableCode ∈ₘ VarSymₘ ⟶ₘ
          variable_symbol_occurs_condition variableCode source ⟶ₘ
            variableCode ∈ₘ varsₘ(source) := by
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := Formula.check_admissible_complete <|
      membership_formula_admissible hSource.1 <|
        binary_union_term_admissible
          TermCodeₘ FormulaCodeₘ
          term_code_set_term_admissible
          formula_code_set_term_admissible)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := Formula.check_admissible_complete <|
      membership_formula_admissible
        hVariable.1 variable_symbol_set_term_admissible)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck := Formula.check_admissible_complete <|
      variable_symbol_occurs_condition_admissible
        variableCode source hVariable.1 hSource.1)
  let candidate := varsₘ(source)
  let occurrence :=
    variable_symbol_occurs_condition variableCode source
  let variableSymbol : SetFormula := variableCode ∈ₘ VarSymₘ
  let sourceCode : SetFormula :=
    source ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ)
  let Γ : Context signature :=
    [occurrence, variableSymbol, sourceCode]
  have hCandidate :
      Term.Admissible candidate SetSort.set := by
    simpa [candidate] using
      variable_collection_term_admissible source hSource.1
  have hCandidateSupport :
      Term.freeSupport candidate = [] := by
    simp [candidate, Term.freeSupport, Term.freeSupportList,
      hSource.2]
  have hFresh :
      ReservedIdsFresh [312, 313] [source, candidate] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl
    · rw [hSource.2]
      exact List.not_mem_nil
    · rw [hCandidateSupport]
      exact List.not_mem_nil
  have hDefinition :
      Γ ⊢ₘ[godel_quotation_theory]
        variable_collection_definition_instance source candidate :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_substitution_variable <|
          variable_collection_definition_instance_derives
            source candidate hSource.1 hCandidate hFresh
  have hSourceCode :
      Γ ⊢ₘ[godel_quotation_theory] sourceCode :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hReflexive :
      Γ ⊢ₘ[godel_quotation_theory]
        candidate ≐ₘ varsₘ(source) := by
    simpa [candidate] using
      (FirstOrder.Derives.eq_refl_m
        (T := godel_quotation_theory) (Γ := Γ)
        (sort := SetSort.set) candidate)
  have hSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        variable_collection_spec source candidate :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.impElim hDefinition hSourceCode)
      hReflexive
  have hPointwise :=
    FirstOrder.Derives.forall_elim
      (term := variableCode)
      (FirstOrder.Derives.conjElimRight hSpec)
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  have hSourceClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth source = source :=
    Numbered.CodeBoundary.closeFreeAt_eq hSource id depth
  have hVariableClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth variableCode = variableCode :=
    Numbered.CodeBoundary.closeFreeAt_eq hVariable id depth
  have hCandidateClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth candidate = candidate :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth candidate hCandidate.2
      (by rw [hCandidateSupport]; exact List.not_mem_nil)
  have hPointwise' :
      Γ ⊢ₘ[godel_quotation_theory]
        variableCode ∈ₘ VarSymₘ ⟶ₘ
          ((variableCode ∈ₘ candidate) ↔ₘ occurrence) := by
    simpa [occurrence, variable_symbol_occurs_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hCandidateOpen,
      Numbered.CodeBoundary.openAt_eq hSource,
      Numbered.CodeBoundary.substituteFree_eq hSource,
      Numbered.CodeBoundary.openAt_eq hVariable,
      Numbered.CodeBoundary.substituteFree_eq hVariable,
      hSourceClose, hVariableClose, hCandidateClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using
      hPointwise
  have hVariableSymbol :
      Γ ⊢ₘ[godel_quotation_theory] variableCode ∈ₘ VarSymₘ :=
    FirstOrder.Derives.assumption (by simp [Γ, variableSymbol])
  have hOccurrence :
      Γ ⊢ₘ[godel_quotation_theory] occurrence :=
    FirstOrder.Derives.assumption
      (T := godel_quotation_theory) (Γ := Γ) (φ := occurrence)
      (by simp [Γ])
      (Formula.check_admissible_complete <| by
        simpa [occurrence] using
          variable_symbol_occurs_condition_admissible
            variableCode source hVariable.1 hSource.1)
  simpa [candidate] using
    FirstOrder.Derives.iffElimLeft
      (FirstOrder.Derives.impElim hPointwise' hVariableSymbol)
      hOccurrence

/-- 右侧集合成员可在 quotation 联合理论中注入二元并。 -/
theorem gq_mem_binary_union_right (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hElement : Term.Admissible element SetSort.set) (hMember : ⊢ₘ[godel_quotation_theory] element ∈ₘ right) :
    ⊢ₘ[godel_quotation_theory] element ∈ₘ (left ∪ₘ right) := by
  have hInjection := gq_weaken_relation_plane (mem_binary_union_right left right element hLeft hRight hElement)
  exact FirstOrder.Derives.impElim hInjection hMember
/-- 左侧集合成员可在 quotation 联合理论中注入二元并。 -/
theorem gq_mem_binary_union_left (left right element : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hElement : Term.Admissible element SetSort.set) (hMember : ⊢ₘ[godel_quotation_theory] element ∈ₘ left) :
    ⊢ₘ[godel_quotation_theory] element ∈ₘ (left ∪ₘ right) := by
  have hInjection := gq_weaken_relation_plane (mem_binary_union_left left right element hLeft hRight hElement)
  exact FirstOrder.Derives.impElim hInjection hMember
/-- 变量符号集合定义公理在任意 admissible 符号项处的实例。 -/
theorem gq_variable_symbol_definition_instance (symbol : SetTerm) (hSymbol : Term.Admissible symbol SetSort.set)
    (hFresh : (SetSort.set, 200) ∉ Term.freeSupport symbol) :
    ⊢ₘ[godel_quotation_theory] ((symbol ∈ₘ VarSymₘ) ↔ₘ variable_symbol_condition symbol) := by
  have hAxiom :
      ⊢ₘ[variable_symbol_encoding_theory]
        variable_symbol_set_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hInstance := FirstOrder.Derives.forall_elim
    (term := symbol) hAxiom
  have hSymbolOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term symbol = symbol :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term symbol hSymbol.2
  have hSymbolClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 200 depth symbol = symbol :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 200 depth symbol hSymbol.2 hFresh
  apply gq_weaken_variable_symbol
  simpa [variable_symbol_set_definition_axiom,
    variable_symbol_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hSymbolOpen, hSymbolClose,
    gq_finite_numeral_open, gq_finite_numeral_close] using hInstance
/-- 变量符号集合成员必为代码字符串。 -/
theorem gq_variable_symbol_member_implies_code_string (symbol : SetTerm) (hSymbol : Term.Admissible symbol SetSort.set)
    (hFresh : (SetSort.set, 200) ∉ Term.freeSupport symbol) :
    ⊢ₘ[godel_quotation_theory] (symbol ∈ₘ VarSymₘ) ⟶ₘ (symbol ∈ₘ CodeStrₘ) := by
  let membership : SetFormula := symbol ∈ₘ VarSymₘ
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSymbol variable_symbol_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  have hMembership :
      [membership] ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ VarSymₘ := by
    simpa [membership] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory) (Γ := [membership])
        (φ := membership) (by simp))
  have hCondition :
      [membership] ⊢ₘ[godel_quotation_theory]
        variable_symbol_condition symbol :=
    FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons <|
        gq_variable_symbol_definition_instance
          symbol hSymbol hFresh)
      hMembership
  exact FirstOrder.Derives.conjElimLeft hCondition
/--
变量符号编码必在下标零处有定义。
证明不假定变量编号是外部 numeral：先从 `VarSymₘ` 的对象定义反演内部编号，再把
长度一符号码视为单有序对函数图。因而该接口可直接用于对象层量词见证。
-/
theorem gq_variable_symbol_zero_mem_domain (symbol : SetTerm) (hSymbol : Term.Admissible symbol SetSort.set)
    (hFresh : (SetSort.set, 200) ∉ Term.freeSupport symbol) :
    ⊢ₘ[godel_quotation_theory] (symbol ∈ₘ VarSymₘ) ⟶ₘ (numₘ(0) ∈ₘ domₘ(symbol)) := by
  let membership : SetFormula := symbol ∈ₘ VarSymₘ
  let Γ : Context signature := [membership]
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSymbol variable_symbol_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  have hMembership :
      Γ ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ VarSymₘ :=
    FirstOrder.Derives.assumption (by simp [Γ, membership])
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        variable_symbol_condition symbol :=
    FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons <|
        gq_variable_symbol_definition_instance
          symbol hSymbol hFresh)
      hMembership
  let witness : SetTerm := x#200
  let witnessCondition : SetFormula := (witness ∈ₘ ωₘ) ∧ₘ (symbol ≐ₘ variable_symbol_code_term witness)
  have hWitnessConditionAdmissible :
      Formula.Admissible witnessCondition := by
    dsimp [witnessCondition, witness]
    exact Formula.Admissible.conj (membership_formula_admissible (set_variable_admissible 200) omega_term_admissible) (Formula.Admissible.equal hSymbol
        (variable_symbol_code_term_admissible (x#200) (set_variable_admissible 200)))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 200], witnessCondition := by
    simpa [variable_symbol_condition, witnessCondition,
      witness, Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable] using
      FirstOrder.Derives.conjElimRight hCondition
  apply FirstOrder.Derives.exists_elim (T := godel_quotation_theory) (Γ := Γ) (sort := SetSort.set) (eigen := 200) (body := witnessCondition)
      (conclusion := numₘ(0) ∈ₘ domₘ(symbol))
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [membership, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList] using hFresh
  · simp [Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport]
    exact hFresh
  · exact hExists
  · let rawCode := variable_symbol_code_term witness
    let number := variable_symbol_number_term witness
    let pair := ⟨numₘ(0), number⟩ₘ
    let Δ : Context signature := [witnessCondition, membership]
    have hWitness :
        Term.Admissible witness SetSort.set := by
      simpa [witness] using set_variable_admissible 200
    have hNumber :
        Term.Admissible number SetSort.set := by
      simpa [number, variable_symbol_number_term] using
        indexed_prime_power_code_term_admissible
          3 witness hWitness
    have hRawCode :
        Term.Admissible rawCode SetSort.set := by
      simpa [rawCode] using
        variable_symbol_code_term_admissible witness hWitness
    have hPair :
        Term.Admissible pair SetSort.set := by
      simpa [pair] using
        ordered_pair_term_admissible (numₘ(0)) number (finite_numeral_term_admissible 0) hNumber
    have hWitnessCondition :
        Δ ⊢ₘ[godel_quotation_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hSymbolRaw :
        Δ ⊢ₘ[godel_quotation_theory]
          symbol ≐ₘ rawCode := by
      simpa [witnessCondition, rawCode] using
        FirstOrder.Derives.conjElimRight hWitnessCondition
    have hSymbolFinite :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition symbol := by
      have hCodeString :
          Δ ⊢ₘ[godel_quotation_theory]
            symbol ∈ₘ CodeStrₘ :=
        FirstOrder.Derives.conjElimLeft <| by
          simpa [variable_symbol_condition] using
            FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := Δ) (by simp [Γ, Δ])
              hCondition
      have hFiniteImp :
          Δ ⊢ₘ[godel_quotation_theory] (symbol ∈ₘ CodeStrₘ) ⟶ₘ
              finite_sequence_condition symbol := by
        exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_standard_sequence <|
              code_string_member_implies_finite_sequence_at
                symbol hSymbol
      exact FirstOrder.Derives.impElim hFiniteImp hCodeString
    have hRawFinite :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition rawCode := by
      exact FirstOrder.Derives.iffElimRight (finite_sequence_condition_iff_of_equality
          symbol rawCode hSymbol hRawCode hSymbolRaw)
        hSymbolFinite
    have hRawFunction :
        Δ ⊢ₘ[godel_quotation_theory]
          is_function_formula rawCode :=
      FirstOrder.Derives.conjElimLeft hRawFinite
    have hRawRelation :
        Δ ⊢ₘ[godel_quotation_theory]
          is_relation_formula rawCode :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_function_predicate <|
              is_function_implies_is_relation
                rawCode hRawCode)
        hRawFunction
    have hSingletonSpec :
        Δ ⊢ₘ[godel_quotation_theory]
          singleton_spec pair rawCode := by
      simpa [rawCode, pair, number,
        variable_symbol_code_term,
        singleton_symbol_code_term] using
        FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_singleton_operator <|
              singleton_term_spec_derives pair hPair
    have hPairMember :
        Δ ⊢ₘ[godel_quotation_theory]
          pair ∈ₘ rawCode := by
      have hMembershipIff :=
        singleton_spec_membership_iff
          pair rawCode pair hPair hRawCode hPair
          hSingletonSpec
      exact FirstOrder.Derives.iffElimLeft
        hMembershipIff (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set) pair)
    have hRawDomain :
        Δ ⊢ₘ[godel_quotation_theory]
          numₘ(0) ∈ₘ domₘ(rawCode) :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp [Δ]) <|
              gq_weaken_function_predicate <|
                relation_member_left_coordinate_mem_domain
                  rawCode (numₘ(0)) number
                  hRawCode (finite_numeral_term_admissible 0)
                  hNumber)
          hRawRelation) (by simpa [pair] using hPairMember)
    have hDomainEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(symbol) ≐ₘ domₘ(rawCode) :=
      domain_term_congr_of_equality
        symbol rawCode hSymbol hRawCode hSymbolRaw
    exact FirstOrder.Derives.iffElimLeft (membership_right_iff_of_equality (numₘ(0)) (domₘ(symbol)) (domₘ(rawCode)) (finite_numeral_term_admissible 0)
        (domain_term_admissible symbol hSymbol) (domain_term_admissible rawCode hRawCode)
        hDomainEquality)
      hRawDomain
/-- 常元符号集合定义公理在任意 admissible 符号项处的实例。 -/
theorem gq_constant_symbol_definition_instance (symbol : SetTerm) (hSymbol : Term.Admissible symbol SetSort.set)
    (hFresh : (SetSort.set, 201) ∉ Term.freeSupport symbol) :
    ⊢ₘ[godel_quotation_theory] ((symbol ∈ₘ ConstSymₘ) ↔ₘ constant_symbol_condition symbol) := by
  have hAxiom :
      ⊢ₘ[constant_symbol_encoding_theory]
        constant_symbol_set_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hInstance := FirstOrder.Derives.forall_elim
    (term := symbol) hAxiom
  have hSymbolOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term symbol = symbol :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term symbol hSymbol.2
  have hSymbolClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 201 depth symbol = symbol :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 201 depth symbol hSymbol.2 hFresh
  apply gq_weaken_constant_symbol
  simpa [constant_symbol_set_definition_axiom,
    constant_symbol_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hSymbolOpen, hSymbolClose,
    gq_finite_numeral_open, gq_finite_numeral_close] using hInstance
/-- 项编码集合对变量符号集合的闭包分量。 -/
theorem gq_variable_symbols_subset_term_codes :
    ⊢ₘ[godel_quotation_theory] VarSymₘ ⊆ₘ TermCodeₘ := by
  have hAxiom :
      ⊢ₘ[term_code_set_theory] term_code_set_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr <| Or.inl rfl
  exact gq_weaken_term_code_set (FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimLeft hAxiom))
/-- 项编码集合满足变量、常元和正元函数应用的完整闭包条件。 -/
theorem gq_term_code_closed :
    ⊢ₘ[godel_quotation_theory]
      term_code_closed_condition TermCodeₘ := by
  have hAxiom :
      ⊢ₘ[term_code_set_theory] term_code_set_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr <| Or.inl rfl
  exact gq_weaken_term_code_set (FirstOrder.Derives.conjElimLeft hAxiom)
/-- 每个项编码都是代码字符串。 -/
theorem gq_term_codes_subset_code_strings :
    ⊢ₘ[godel_quotation_theory]
      TermCodeₘ ⊆ₘ CodeStrₘ := by
  have hAxiom :
      ⊢ₘ[term_code_set_theory]
        term_code_set_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr <| Or.inl rfl
  exact gq_weaken_term_code_set <|
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hAxiom
/-- 项编码集合成员可直接消去为代码字符串成员。 -/
theorem gq_term_code_member_implies_code_string
    (code : SetTerm)
    (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      (code ∈ₘ TermCodeₘ) ⟶ₘ
        (code ∈ₘ CodeStrₘ) :=
  gq_subset_member_imp
    TermCodeₘ CodeStrₘ code
    term_code_set_term_admissible
    code_string_space_term_admissible
    hCode gq_term_codes_subset_code_strings
/-- 项编码集合对常元符号集合的闭包分量。 -/
theorem gq_constant_symbols_subset_term_codes :
    ⊢ₘ[godel_quotation_theory] ConstSymₘ ⊆ₘ TermCodeₘ :=
  FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight gq_term_code_closed)
/-- 项编码集合对一次正元函数应用构造的闭包分量。 -/
theorem gq_term_application_closed :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 214],
        term_application_from_condition
            TermCodeₘ (x#214) ⟶ₘ ((x#214) ∈ₘ TermCodeₘ) :=
  FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight gq_term_code_closed)
/-- “是项编码”谓词在任意 admissible 项处的定义实例。 -/
theorem gq_term_code_definition_instance (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      is_term_code_definition_instance code := by
  have hAxiom :
      ⊢ₘ[term_code_predicate_theory]
        is_term_code_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hInstance := FirstOrder.Derives.forall_elim
    (term := code) hAxiom
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  apply gq_weaken_term_code_predicate
  simpa [is_term_code_definition_axiom,
    is_term_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hCodeOpen] using hInstance
/-- 任意变量符号编码也是项编码。 -/
theorem gq_term_code_of_variable_symbol (variableCode : SetTerm) (hVariable : Term.Admissible variableCode SetSort.set)
    (hMember : ⊢ₘ[godel_quotation_theory] variableCode ∈ₘ VarSymₘ) :
    ⊢ₘ[godel_quotation_theory] term_codeₘ(variableCode) := by
  have hSetMember := gq_subset_member
    VarSymₘ TermCodeₘ variableCode
    variable_symbol_set_term_admissible
    term_code_set_term_admissible hVariable
    gq_variable_symbols_subset_term_codes hMember
  exact FirstOrder.Derives.iffElimLeft (gq_term_code_definition_instance variableCode hVariable)
    hSetMember
/-! ## 非空项编码序列的定义合同 -/
/-- `TermSeqₘ` 定义公理在任意 admissible 序列项处的实例。 -/
theorem gq_term_sequence_set_definition_instance (sequence : SetTerm) (hSequence : Term.Admissible sequence SetSort.set)
    (hFresh : (SetSort.set, 220) ∉ Term.freeSupport sequence) :
    ⊢ₘ[godel_quotation_theory] ((sequence ∈ₘ TermSeqₘ) ↔ₘ
        term_sequence_condition sequence) := by
  have hAxiom :
      ⊢ₘ[term_sequence_encoding_theory]
        term_sequence_set_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hInstance := FirstOrder.Derives.forall_elim
    (term := sequence) hAxiom
  have hSequenceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term sequence = sequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term sequence hSequence.2
  have hSequenceClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 220 depth sequence = sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 220 depth sequence hSequence.2 hFresh
  apply gq_weaken_atomic_formula
  have hLifted :
      ⊢ₘ[atomic_formula_encoding_theory]
        Formula.openAt SetSort.set 0 sequence (Formula.closeFreeAt SetSort.set 0 0 ((x#0 ∈ₘ TermSeqₘ) ↔ₘ
              term_sequence_condition (x#0))) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inr hFormula) hInstance
  simpa [term_sequence_set_definition_axiom,
    term_sequence_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hSequenceOpen,
    hSequenceClose] using hLifted
/--
非空代码字符串序列若在定义域内逐点满足 `term_codeₘ`，则属于 `TermSeqₘ`。
-/
theorem gq_term_sequence_mem (sequence : SetTerm) (hSequence : Term.Admissible sequence SetSort.set)
    (hFresh : (SetSort.set, 220) ∉ Term.freeSupport sequence)
    (hPositive :
      ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ seq₊_spaceₘ(CodeStrₘ)) (hValues :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 220], (x#220 ∈ₘ domₘ(sequence)) ⟶ₘ
            term_codeₘ(sequence ·ₘ x#220)) :
    ⊢ₘ[godel_quotation_theory] sequence ∈ₘ TermSeqₘ := by
  exact FirstOrder.Derives.iffElimLeft (gq_term_sequence_set_definition_instance
      sequence hSequence hFresh)
    (FirstOrder.Derives.conjIntro hPositive hValues)
/-! ## 原子公式集与公式闭包的定义合同 -/
/-- “是原子公式编码”谓词在新鲜实参处的定义实例。 -/
theorem gq_atomic_formula_code_definition_instance (code : SetTerm) (hCode : Term.Admissible code SetSort.set)
    (hFresh : ReservedIdsFresh [230, 231, 232, 233, 234] [code]) :
    ⊢ₘ[godel_quotation_theory]
      is_atomic_formula_code_definition_instance code := by
  have hAxiom :
      ⊢ₘ[atomic_formula_encoding_theory]
        is_atomic_formula_code_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hInstance := FirstOrder.Derives.forall_elim
    (term := code) hAxiom
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hCodeClose230 (depth : Nat) :
      Term.closeFreeAt SetSort.set 230 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 230 depth code hCode.2 (hFresh code (by simp) 230 (by simp))
  have hCodeClose231 (depth : Nat) :
      Term.closeFreeAt SetSort.set 231 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 231 depth code hCode.2 (hFresh code (by simp) 231 (by simp))
  have hCodeClose232 (depth : Nat) :
      Term.closeFreeAt SetSort.set 232 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 232 depth code hCode.2 (hFresh code (by simp) 232 (by simp))
  have hCodeClose233 (depth : Nat) :
      Term.closeFreeAt SetSort.set 233 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 233 depth code hCode.2 (hFresh code (by simp) 233 (by simp))
  have hCodeClose234 (depth : Nat) :
      Term.closeFreeAt SetSort.set 234 depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 234 depth code hCode.2 (hFresh code (by simp) 234 (by simp))
  apply gq_weaken_atomic_formula
  simpa [is_atomic_formula_code_definition_axiom,
    is_atomic_formula_code_definition_instance,
    atomic_formula_code_condition,
    binary_atomic_formula_code_condition,
    predicate_application_code_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hCodeOpen,
    hCodeClose230, hCodeClose231, hCodeClose232,
    hCodeClose233, hCodeClose234,
    gq_finite_numeral_open, gq_finite_numeral_close] using hInstance
/-- 原子公式编码集合定义公理在任意 admissible 编码项处的实例。 -/
theorem gq_atomic_formula_code_set_definition_instance (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory] ((code ∈ₘ AtomicCodeₘ) ↔ₘ atomic_formula_codeₘ(code)) := by
  have hAxiom :
      ⊢ₘ[formula_code_theory] formula_code_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hDefinition := FirstOrder.Derives.conjElimLeft hAxiom
  have hInstance := FirstOrder.Derives.forall_elim
    (term := code) hDefinition
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  apply gq_weaken_formula_code
  simpa [formula_code_definition_axiom,
    atomic_formula_code_set_definition_axiom,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt, Term.substituteFree,
    set_variable, set_bound_variable, hCodeOpen] using hInstance
/-- 完整公式编码集合确实满足原子、否定、蕴含和全称量化闭包。 -/
theorem gq_formula_code_closed :
    ⊢ₘ[godel_quotation_theory]
      formula_code_closed_condition FormulaCodeₘ := by
  have hAxiom :
      ⊢ₘ[formula_code_theory] formula_code_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hSetDefinition := FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight hAxiom)
  exact gq_weaken_formula_code (FirstOrder.Derives.conjElimLeft hSetDefinition)
/-- 每个公式编码都是代码字符串。 -/
theorem gq_formula_codes_subset_code_strings :
    ⊢ₘ[godel_quotation_theory]
      FormulaCodeₘ ⊆ₘ CodeStrₘ := by
  have hAxiom :
      ⊢ₘ[formula_code_theory] formula_code_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hSetDefinition := FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight hAxiom)
  exact gq_weaken_formula_code
    (FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hSetDefinition)
/-- 公式编码集合成员可直接消去为代码字符串成员。 -/
theorem gq_formula_code_member_implies_code_string (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory] (code ∈ₘ FormulaCodeₘ) ⟶ₘ (code ∈ₘ CodeStrₘ) := by
  exact gq_subset_member_imp
    FormulaCodeₘ CodeStrₘ code
    formula_code_set_term_admissible
    code_string_space_term_admissible
    hCode gq_formula_codes_subset_code_strings
/-- 文献中的 `cBDS ⊆ BDS`：原子公式编码集合包含于完整公式编码集合。 -/
theorem gq_atomic_formula_codes_subset_formula_codes :
    ⊢ₘ[godel_quotation_theory] AtomicCodeₘ ⊆ₘ FormulaCodeₘ :=
  FirstOrder.Derives.conjElimLeft gq_formula_code_closed
/-- “是公式编码”谓词在任意 admissible 编码项处的定义实例。 -/
theorem gq_formula_code_definition_instance (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      is_formula_code_definition_instance code := by
  have hAxiom :
      ⊢ₘ[formula_code_theory] formula_code_definition_axiom := by
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inl rfl
  have hDefinition := FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight hAxiom)
  have hInstance := FirstOrder.Derives.forall_elim
    (term := code) hDefinition
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  apply gq_weaken_formula_code
  simpa [formula_code_definition_axiom,
    is_formula_code_definition_axiom,
    is_formula_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt, Term.substituteFree,
    set_variable, set_bound_variable, hCodeOpen] using hInstance
/-- 原子公式集合的成员经 `AtomicCodeₘ ⊆ FormulaCodeₘ` 落入完整公式集合。 -/
theorem gq_formula_code_mem_of_atomic_mem (code : SetTerm) (hCode : Term.Admissible code SetSort.set)
    (hMember : ⊢ₘ[godel_quotation_theory] code ∈ₘ AtomicCodeₘ) :
    ⊢ₘ[godel_quotation_theory] code ∈ₘ FormulaCodeₘ := by
  exact gq_subset_member
    AtomicCodeₘ FormulaCodeₘ code
    atomic_formula_code_set_term_admissible
    formula_code_set_term_admissible hCode
    gq_atomic_formula_codes_subset_formula_codes hMember
/-- 完整公式集合成员满足对象谓词 `formula_codeₘ`。 -/
theorem gq_is_formula_code_of_mem
    {Γ : Context signature} (code : SetTerm) (hCode : Term.Admissible code SetSort.set) (hMember :
      Γ ⊢ₘ[godel_quotation_theory] code ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory] formula_codeₘ(code) :=
  FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (gq_formula_code_definition_instance code hCode))
    hMember
/--
两个项编码按文献的等式/隶属原子串形状组合后，所得编码属于完整公式集合。
`freeSupport = []` 精确表达 quotation 结果是闭对象项，并同时解除定义内部保留编号的
捕获风险。
-/
theorem gq_binary_atomic_formula_code_mem (left right code : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hCode : Term.Admissible code SetSort.set) (hLeftSupport : Term.freeSupport left = []) (hRightSupport : Term.freeSupport right = [])
    (hCodeSupport : Term.freeSupport code = []) (hLeftCode : ⊢ₘ[godel_quotation_theory] term_codeₘ(left))
    (hRightCode : ⊢ₘ[godel_quotation_theory] term_codeₘ(right)) (hShape :
      ⊢ₘ[godel_quotation_theory] (code ≐ₘ equality_atomic_formula_code_term left right) ∨ₘ (code ≐ₘ membership_atomic_formula_code_term left right)) :
    ⊢ₘ[godel_quotation_theory] code ∈ₘ FormulaCodeₘ := by
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hLeftClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth left = left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth left hLeft.2 (by rw [hLeftSupport]; exact List.not_mem_nil)
  have hRightClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth right = right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth right hRight.2 (by rw [hRightSupport]; exact List.not_mem_nil)
  have hCodeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth code hCode.2 (by rw [hCodeSupport]; exact List.not_mem_nil)
  have hFresh : ReservedIdsFresh
      [230, 231, 232, 233, 234] [code] := by
    intro candidate hCandidate id hId
    simp at hCandidate
    subst candidate
    rw [hCodeSupport]
    exact List.not_mem_nil
  have hAtomicDefinition :=
    gq_atomic_formula_code_definition_instance
      code hCode hFresh
  have hAtomicConditionAdmissible :
      Formula.Admissible (atomic_formula_code_condition code) :=
    Formula.Admissible.iff_right
      hAtomicDefinition.admissible
  have hPredicateConditionAdmissible :
      Formula.Admissible (predicate_application_code_condition code) :=
    Formula.Admissible.disj_right
      hAtomicConditionAdmissible
  have hBinaryCondition :
      ⊢ₘ[godel_quotation_theory]
        binary_atomic_formula_code_condition code := by
    rw [binary_atomic_formula_code_condition]
    nd_apply FirstOrder.Derives.exists_intro (term := left)
    nd_apply FirstOrder.Derives.exists_intro (term := right)
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hLeftOpen, hRightOpen, hCodeOpen,
      hLeftClose, hRightClose, hCodeClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using
      FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro hLeftCode hRightCode)
        hShape
  have hAtomicCondition :
      ⊢ₘ[godel_quotation_theory]
        atomic_formula_code_condition code :=
    FirstOrder.Derives.disjIntroLeft hBinaryCondition
  have hAtomicCode :
      ⊢ₘ[godel_quotation_theory] atomic_formula_codeₘ(code) :=
    FirstOrder.Derives.iffElimLeft
      hAtomicDefinition
      hAtomicCondition
  have hAtomicMember :
      ⊢ₘ[godel_quotation_theory] code ∈ₘ AtomicCodeₘ :=
    FirstOrder.Derives.iffElimLeft (gq_atomic_formula_code_set_definition_instance code hCode)
      hAtomicCode
  exact gq_formula_code_mem_of_atomic_mem code hCode hAtomicMember
/--
参数属于 `TermSeqₘ` 且定义域长度与元数一致时，普通正元谓词应用编码属于完整
公式编码集合。
-/
theorem gq_predicate_application_formula_code_mem (arityPredecessor index : Nat) (arguments : SetTerm) (hArguments : Term.Admissible arguments SetSort.set)
    (hArgumentsClosed : Term.freeSupport arguments = []) (hTermSequence :
      ⊢ₘ[godel_quotation_theory] arguments ∈ₘ TermSeqₘ) (hDomain :
      ⊢ₘ[godel_quotation_theory]
        domₘ(arguments) ≐ₘ Sₘ(numₘ(arityPredecessor))) :
    ⊢ₘ[godel_quotation_theory]
      predicate_application_code_term (numₘ(arityPredecessor)) (numₘ(index)) arguments ∈ₘ
        FormulaCodeₘ := by
  let arityTerm : SetTerm := numₘ(arityPredecessor)
  let indexTerm : SetTerm := numₘ(index)
  let code : SetTerm :=
    predicate_application_code_term arityTerm indexTerm arguments
  have hArity : Term.Admissible arityTerm SetSort.set :=
    finite_numeral_term_admissible arityPredecessor
  have hIndex : Term.Admissible indexTerm SetSort.set :=
    finite_numeral_term_admissible index
  have hCode : Term.Admissible code SetSort.set :=
    predicate_application_code_term_admissible
      arityTerm indexTerm arguments hArity hIndex hArguments
  have hArityMem :
      ⊢ₘ[godel_quotation_theory] arityTerm ∈ₘ ωₘ :=
    gq_weaken_standard_sequence <| by
      simpa [arityTerm] using
        standard_sequence_finite_numeral_mem_omega arityPredecessor
  have hIndexMem :
      ⊢ₘ[godel_quotation_theory] indexTerm ∈ₘ ωₘ :=
    gq_weaken_standard_sequence <| by
      simpa [indexTerm] using
        standard_sequence_finite_numeral_mem_omega index
  have hCodeReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ
          predicate_application_code_term
            arityTerm indexTerm arguments :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) code
  have hBase :
      ⊢ₘ[godel_quotation_theory] (((arityTerm ∈ₘ ωₘ) ∧ₘ ((indexTerm ∈ₘ ωₘ) ∧ₘ ((arguments ∈ₘ TermSeqₘ) ∧ₘ (domₘ(arguments) ≐ₘ Sₘ(arityTerm))))) ∧ₘ (code ≐ₘ
            predicate_application_code_term
              arityTerm indexTerm arguments)) :=
    FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro hArityMem (FirstOrder.Derives.conjIntro hIndexMem (FirstOrder.Derives.conjIntro hTermSequence
            (by simpa [arityTerm] using hDomain))))
      hCodeReflexive
  have hArgumentsOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term arguments = arguments :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term arguments hArguments.2
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hArgumentsClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth arguments = arguments :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth arguments hArguments.2 (by rw [hArgumentsClosed]; exact List.not_mem_nil)
  have hCodeClosed : Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hArgumentsClosed, arityTerm, indexTerm,
      finite_numeral_term_freeSupport]
  have hCodeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth code hCode.2 (by rw [hCodeClosed]; exact List.not_mem_nil)
  have hFresh : ReservedIdsFresh
      [230, 231, 232, 233, 234] [code] := by
    intro candidate hCandidate id hId
    simp at hCandidate
    subst candidate
    rw [hCodeClosed]
    exact List.not_mem_nil
  have hAtomicDefinition :=
    gq_atomic_formula_code_definition_instance
      code hCode hFresh
  have hAtomicConditionAdmissible :
      Formula.Admissible (atomic_formula_code_condition code) :=
    Formula.Admissible.iff_right
      hAtomicDefinition.admissible
  have hBinaryConditionAdmissible :
      Formula.Admissible (binary_atomic_formula_code_condition code) :=
    Formula.Admissible.disj_left
      hAtomicConditionAdmissible
  have hPredicateCondition :
      ⊢ₘ[godel_quotation_theory]
        predicate_application_code_condition code := by
    rw [predicate_application_code_condition]
    nd_apply FirstOrder.Derives.exists_intro (term := arityTerm)
    nd_apply FirstOrder.Derives.exists_intro (term := indexTerm)
    nd_apply FirstOrder.Derives.exists_intro (term := arguments)
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      arityTerm, indexTerm, code,
      hArgumentsOpen, hCodeOpen,
      hArgumentsClose, hCodeClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using hBase
  have hAtomicCondition :
      ⊢ₘ[godel_quotation_theory]
        atomic_formula_code_condition code :=
    FirstOrder.Derives.disjIntroRight hPredicateCondition
  have hAtomicCode :
      ⊢ₘ[godel_quotation_theory] atomic_formula_codeₘ(code) :=
    FirstOrder.Derives.iffElimLeft
      hAtomicDefinition
      hAtomicCondition
  have hAtomicMember :
      ⊢ₘ[godel_quotation_theory] code ∈ₘ AtomicCodeₘ :=
    FirstOrder.Derives.iffElimLeft (gq_atomic_formula_code_set_definition_instance code hCode)
      hAtomicCode
  simpa [code] using
    gq_formula_code_mem_of_atomic_mem code hCode hAtomicMember
/-- 完整公式集合对否定编码封闭。 -/
theorem gq_formula_code_mem_negation
    {Γ : Context signature} (body : SetTerm) (hBody : Term.Admissible body SetSort.set) (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory] body ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      neg_codeₘ(body) ∈ₘ FormulaCodeₘ := by
  have hClosure :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
      FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight gq_formula_code_closed)
  have hAt := FirstOrder.Derives.forall_elim
    (term := body) hClosure
  have hBodyOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term body = body :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term body hBody.2
  have hFormulaCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term FormulaCodeₘ = FormulaCodeₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term FormulaCodeₘ
      formula_code_set_term_admissible.2
  exact FirstOrder.Derives.impElim (by simpa [formula_code_closed_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hBodyOpen, hFormulaCodeOpen] using hAt)
    hBodyMember
/-- 完整公式集合对蕴含编码封闭。 -/
theorem gq_formula_code_mem_implication
    {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory] left ∈ₘ FormulaCodeₘ) (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory] right ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      imp_codeₘ(left, right) ∈ₘ FormulaCodeₘ := by
  have hClosure :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
      FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight gq_formula_code_closed))
  have hLeftAt := FirstOrder.Derives.forall_elim
    (term := left) hClosure
  have hRightAt := FirstOrder.Derives.forall_elim
    (term := right) hLeftAt
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  have hFormulaCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term FormulaCodeₘ = FormulaCodeₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term FormulaCodeₘ
      formula_code_set_term_admissible.2
  have hImplication :
      Γ ⊢ₘ[godel_quotation_theory] (left ∈ₘ FormulaCodeₘ ∧ₘ right ∈ₘ FormulaCodeₘ) ⟶ₘ
          imp_codeₘ(left, right) ∈ₘ FormulaCodeₘ := by
    simpa [formula_code_closed_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hLeftOpen, hRightOpen, hFormulaCodeOpen] using hRightAt
  exact FirstOrder.Derives.impElim hImplication (FirstOrder.Derives.conjIntro hLeftMember hRightMember)
/--
全称构造函数项无条件展开为它的括号化原始字符串。
这里仅使用构造函数的定义等价，不要求正文已经属于公式码集合；后续反演定理因此可以
先读取固定前缀，再独立处理正文的语法合法性。
-/
theorem gq_universal_formula_code_eq_string (boundVariable body : SetTerm) (hBoundVariable :
      Term.Admissible boundVariable SetSort.set) (hBody : Term.Admissible body SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      forall_codeₘ(boundVariable, body) ≐ₘ
        universal_formula_string_term boundVariable body := by
  let code := forall_codeₘ(boundVariable, body)
  have hCode :
      Term.Admissible code SetSort.set :=
    universal_formula_code_term_admissible
      boundVariable body hBoundVariable hBody
  have hDefinition :=
    gq_weaken_formula_constructor <|
      universal_formula_code_definition_instance_derives
        boundVariable body code
        hBoundVariable hBody hCode
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ forall_codeₘ(boundVariable, body) := by
    simpa [code] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code)
  simpa [code,
    universal_formula_code_definition_instance] using
    FirstOrder.Derives.iffElimRight
      hDefinition hReflexive
/-- 完整公式集合对带变量符号的全称量化编码封闭。 -/
theorem gq_formula_code_mem_universal
    {Γ : Context signature} (boundVariable body : SetTerm) (hVariable : Term.Admissible boundVariable SetSort.set) (hBody : Term.Admissible body SetSort.set)
    (hVariableMember :
      Γ ⊢ₘ[godel_quotation_theory] boundVariable ∈ₘ VarSymₘ) (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory] body ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      forall_codeₘ(boundVariable, body) ∈ₘ FormulaCodeₘ := by
  have hClosure :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) <|
      FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight gq_formula_code_closed))
  have hVariableAt := FirstOrder.Derives.forall_elim
    (term := boundVariable) hClosure
  have hBodyAt := FirstOrder.Derives.forall_elim
    (term := body) hVariableAt
  have hVariableOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term boundVariable = boundVariable :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term boundVariable hVariable.2
  have hBodyOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term body = body :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term body hBody.2
  have hFormulaCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term FormulaCodeₘ = FormulaCodeₘ :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term FormulaCodeₘ
      formula_code_set_term_admissible.2
  have hUniversal :
      Γ ⊢ₘ[godel_quotation_theory] (boundVariable ∈ₘ VarSymₘ ∧ₘ body ∈ₘ FormulaCodeₘ) ⟶ₘ
          forall_codeₘ(boundVariable, body) ∈ₘ FormulaCodeₘ := by
    simpa [formula_code_closed_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hVariableOpen, hBodyOpen, hFormulaCodeOpen] using hBodyAt
  exact FirstOrder.Derives.impElim hUniversal (FirstOrder.Derives.conjIntro hVariableMember hBodyMember)
/--
完整公式集合对文献 11.5 的存在量词缩写 `¬∀¬` 封闭。
该定理只串接核心 `¬ / ∀` 闭包，因此不向 `FormulaCodeₘ` 增加第四个原始构造子。
-/
theorem gq_formula_code_mem_existential
    {Γ : Context signature} (boundVariable body : SetTerm) (hVariable : Term.Admissible boundVariable SetSort.set) (hBody : Term.Admissible body SetSort.set)
    (hVariableMember :
      Γ ⊢ₘ[godel_quotation_theory] boundVariable ∈ₘ VarSymₘ) (hBodyMember :
      Γ ⊢ₘ[godel_quotation_theory] body ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      existential_formula_code_term boundVariable body ∈ₘ
        FormulaCodeₘ := by
  have hNegBody : Term.Admissible (neg_codeₘ(body)) SetSort.set :=
    negation_formula_code_term_admissible body hBody
  have hNegBodyMember :
      Γ ⊢ₘ[godel_quotation_theory]
        neg_codeₘ(body) ∈ₘ FormulaCodeₘ :=
    gq_formula_code_mem_negation body hBody hBodyMember
  have hUniversal :
      Term.Admissible (forall_codeₘ(boundVariable, neg_codeₘ(body)))
        SetSort.set :=
    universal_formula_code_term_admissible
      boundVariable (neg_codeₘ(body)) hVariable hNegBody
  have hUniversalMember :
      Γ ⊢ₘ[godel_quotation_theory]
        forall_codeₘ(boundVariable, neg_codeₘ(body)) ∈ₘ
          FormulaCodeₘ :=
    gq_formula_code_mem_universal
      boundVariable (neg_codeₘ(body))
      hVariable hNegBody hVariableMember hNegBodyMember
  exact gq_formula_code_mem_negation (forall_codeₘ(boundVariable, neg_codeₘ(body)))
    hUniversal hUniversalMember
/--
完整公式集合对文献 11.6 的合取缩写 `¬(φ → ¬ψ)` 封闭。
它直接复用核心否定和蕴含闭包，因而与 `Formula.hilbert_conj` 的归约完全一致。
-/
theorem gq_formula_code_mem_conjunction
    {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) (hLeftMember :
      Γ ⊢ₘ[godel_quotation_theory] left ∈ₘ FormulaCodeₘ) (hRightMember :
      Γ ⊢ₘ[godel_quotation_theory] right ∈ₘ FormulaCodeₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      conjunction_formula_code_term left right ∈ₘ
        FormulaCodeₘ := by
  have hNegRight : Term.Admissible (neg_codeₘ(right)) SetSort.set :=
    negation_formula_code_term_admissible right hRight
  have hNegRightMember :
      Γ ⊢ₘ[godel_quotation_theory]
        neg_codeₘ(right) ∈ₘ FormulaCodeₘ :=
    gq_formula_code_mem_negation right hRight hRightMember
  have hImplication :
      Term.Admissible (imp_codeₘ(left, neg_codeₘ(right))) SetSort.set :=
    implication_formula_code_term_admissible
      left (neg_codeₘ(right)) hLeft hNegRight
  have hImplicationMember :
      Γ ⊢ₘ[godel_quotation_theory]
        imp_codeₘ(left, neg_codeₘ(right)) ∈ₘ FormulaCodeₘ :=
    gq_formula_code_mem_implication
      left (neg_codeₘ(right))
      hLeft hNegRight hLeftMember hNegRightMember
  exact gq_formula_code_mem_negation (imp_codeₘ(left, neg_codeₘ(right)))
    hImplication hImplicationMember
/-! ## 文献变量标签的编码正确性 -/
private theorem gq_infinity_subset_natural_exponentiation
    {formula : SetFormula} (hFormula : infinity_theory formula) :
    natural_exponentiation_theory formula :=
  natural_multiplication_theory_subset_natural_exponentiation_theory <|
    natural_addition_theory_subset_natural_multiplication_theory <|
      natural_set_theory_subset_natural_addition_theory <|
        natural_order_type_theory_subset_natural_subset_type_theory <|
          bounded_subset_theory_subset_natural_order_type_theory <|
            unbounded_subset_theory_subset_bounded_subset_theory <|
              infinity_theory_subset_unbounded_subset_theory hFormula
/-- 规范 quotation 使用的具名变量编码确实属于变量符号集合。 -/
theorem named_variable_code_mem_variable_symbols (name : Nat) :
    ⊢ₘ[godel_quotation_theory]
      named_variable_code name ∈ₘ VarSymₘ := by
  let index : SetTerm := numₘ(name)
  let exponent : SetTerm := Sₘ(index)
  let number : SetTerm := variable_symbol_number_term index
  let rawCode : SetTerm := variable_symbol_code_term index
  let variableCode : SetTerm := named_variable_code name
  have hIndex : Term.Admissible index SetSort.set :=
    finite_numeral_term_admissible name
  have hExponent : Term.Admissible exponent SetSort.set :=
    successor_term_admissible index hIndex
  have hNumber : Term.Admissible number SetSort.set :=
    indexed_prime_power_code_term_admissible 3 index hIndex
  have hRawCode : Term.Admissible rawCode SetSort.set :=
    variable_symbol_code_term_admissible index hIndex
  have hVariableCode : Term.Admissible variableCode SetSort.set :=
    variable_code_term_admissible index hIndex
  have hNumeralInNaturalExponentiation (value : Nat) :
      ⊢ₘ[natural_exponentiation_theory] numₘ(value) ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        gq_infinity_subset_natural_exponentiation hFormula) (infinity_finite_numeral_mem_omega value)
  have hExponentMem :
      ⊢ₘ[natural_exponentiation_theory] exponent ∈ₘ ωₘ := by
    simpa [exponent, index, finite_numeral_term] using
      hNumeralInNaturalExponentiation (name + 1)
  have hNumberMemNatural :
      ⊢ₘ[natural_exponentiation_theory] number ∈ₘ ωₘ := by
    simpa [number, variable_symbol_number_term,
      indexed_prime_power_code_term, prime_power_code_term,
      exponent, index] using
      natural_exponentiation_term_mem_omega (numₘ(3)) exponent (finite_numeral_term_admissible 3) hExponent (hNumeralInNaturalExponentiation 3) hExponentMem
  have hNumberMemStandard :
      ⊢ₘ[standard_sequence_semantics_theory] number ∈ₘ ωₘ :=
    standard_sequence_weaken_natural_exponentiation hNumberMemNatural
  have hNumberClosed : Term.freeSupport number = [] := by
    simp [number,
      Term.freeSupport, Term.freeSupportList,
      index, finite_numeral_term_freeSupport]
  have hRawCodeString :
      ⊢ₘ[godel_quotation_theory] rawCode ∈ₘ CodeStrₘ :=
    gq_weaken_standard_sequence <| by
      simpa [rawCode, variable_symbol_code_term] using
        singleton_symbol_code_mem_code_string
          number hNumber hNumberClosed hNumberMemStandard
  have hOperatorDefinition := gq_weaken_symbol_operator (variable_code_definition_instance_derives
      index variableCode hIndex hVariableCode)
  have hVariableReflexive :
      ⊢ₘ[godel_quotation_theory]
        variableCode ≐ₘ var_codeₘ(index) := by
    simpa [variableCode, named_variable_code, index] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) variableCode)
  have hVariableRaw :
      ⊢ₘ[godel_quotation_theory] variableCode ≐ₘ rawCode := by
    simpa [variableCode, rawCode, index] using
      FirstOrder.Derives.iffElimRight
        hOperatorDefinition hVariableReflexive
  have hVariableCodeString :
      ⊢ₘ[godel_quotation_theory] variableCode ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.iffElimLeft (membership_left_iff_of_equality
        variableCode rawCode CodeStrₘ
        hVariableCode hRawCode
        code_string_space_term_admissible hVariableRaw)
      hRawCodeString
  have hIndexMem :
      ⊢ₘ[godel_quotation_theory] index ∈ₘ ωₘ :=
    gq_weaken_standard_sequence <| by
      simpa [index] using
        standard_sequence_finite_numeral_mem_omega name
  have hVariableSupport : Term.freeSupport variableCode = [] := by
    simp [variableCode]
  have hVariableFresh : (SetSort.set, 200) ∉ Term.freeSupport variableCode := by
    rw [hVariableSupport]
    exact List.not_mem_nil
  have hDefinition :=
    gq_variable_symbol_definition_instance
      variableCode hVariableCode hVariableFresh
  have hCondition :
      ⊢ₘ[godel_quotation_theory]
        variable_symbol_condition variableCode := by
    apply FirstOrder.Derives.conjIntro hVariableCodeString
    nd_apply FirstOrder.Derives.exists_intro (term := index)
    have hVariableOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 index variableCode hVariableCode.2
    have hVariableClose (depth : Nat) :
        Term.closeFreeAt SetSort.set 200 depth variableCode =
          variableCode :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 200 depth variableCode hVariableCode.2 (by rw [hVariableSupport]; simp)
    simpa [variable_symbol_condition, variableCode, rawCode,
      index, Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hVariableOpen, hVariableClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using
      FirstOrder.Derives.conjIntro hIndexMem hVariableRaw
  exact FirstOrder.Derives.iffElimLeft
    hDefinition (by simpa [variableCode] using hCondition)
/-- 规范具名变量编码同时满足“是项编码”谓词。 -/
theorem named_variable_code_is_term_code (name : Nat) :
    ⊢ₘ[godel_quotation_theory]
      term_codeₘ(named_variable_code name) :=
  gq_term_code_of_variable_symbol (named_variable_code name) (variable_code_term_admissible (numₘ(name)) (finite_numeral_term_admissible name))
    (named_variable_code_mem_variable_symbols name)
/-- 第 `index` 个原始常元符号编码属于常元符号集合。 -/
theorem constant_symbol_code_mem_constant_symbols (index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      constant_symbol_code_term (numₘ(index)) ∈ₘ ConstSymₘ := by
  let indexTerm : SetTerm := numₘ(index)
  let exponent : SetTerm := Sₘ(indexTerm)
  let number : SetTerm := constant_symbol_number_term indexTerm
  let rawCode : SetTerm := constant_symbol_code_term indexTerm
  have hIndex : Term.Admissible indexTerm SetSort.set :=
    finite_numeral_term_admissible index
  have hExponent : Term.Admissible exponent SetSort.set :=
    successor_term_admissible indexTerm hIndex
  have hNumber : Term.Admissible number SetSort.set :=
    indexed_prime_power_code_term_admissible 5 indexTerm hIndex
  have hRawCode : Term.Admissible rawCode SetSort.set :=
    constant_symbol_code_term_admissible indexTerm hIndex
  have hNumeralInNaturalExponentiation (value : Nat) :
      ⊢ₘ[natural_exponentiation_theory] numₘ(value) ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        gq_infinity_subset_natural_exponentiation hFormula) (infinity_finite_numeral_mem_omega value)
  have hExponentMem :
      ⊢ₘ[natural_exponentiation_theory] exponent ∈ₘ ωₘ := by
    simpa [exponent, indexTerm, finite_numeral_term] using
      hNumeralInNaturalExponentiation (index + 1)
  have hNumberMemNatural :
      ⊢ₘ[natural_exponentiation_theory] number ∈ₘ ωₘ := by
    simpa [number, constant_symbol_number_term,
      indexed_prime_power_code_term, prime_power_code_term,
      exponent, indexTerm] using
      natural_exponentiation_term_mem_omega (numₘ(5)) exponent (finite_numeral_term_admissible 5) hExponent (hNumeralInNaturalExponentiation 5) hExponentMem
  have hNumberMemStandard :
      ⊢ₘ[standard_sequence_semantics_theory] number ∈ₘ ωₘ :=
    standard_sequence_weaken_natural_exponentiation
      hNumberMemNatural
  have hNumberClosed : Term.freeSupport number = [] := by
    simp [number, Term.freeSupport, Term.freeSupportList,
      indexTerm, finite_numeral_term_freeSupport]
  have hRawCodeString :
      ⊢ₘ[godel_quotation_theory] rawCode ∈ₘ CodeStrₘ :=
    gq_weaken_standard_sequence <| by
      simpa [rawCode, constant_symbol_code_term] using
        singleton_symbol_code_mem_code_string
          number hNumber hNumberClosed hNumberMemStandard
  have hIndexMem :
      ⊢ₘ[godel_quotation_theory] indexTerm ∈ₘ ωₘ :=
    gq_weaken_standard_sequence <| by
      simpa [indexTerm] using
        standard_sequence_finite_numeral_mem_omega index
  have hRawSupport : Term.freeSupport rawCode = [] := by
    simp [rawCode, Term.freeSupport, Term.freeSupportList,
      indexTerm, finite_numeral_term_freeSupport]
  have hRawFresh : (SetSort.set, 201) ∉ Term.freeSupport rawCode := by
    rw [hRawSupport]
    exact List.not_mem_nil
  have hDefinition :=
    gq_constant_symbol_definition_instance
      rawCode hRawCode hRawFresh
  have hCondition :
      ⊢ₘ[godel_quotation_theory]
        constant_symbol_condition rawCode := by
    apply FirstOrder.Derives.conjIntro hRawCodeString
    nd_apply FirstOrder.Derives.exists_intro (term := indexTerm)
    have hRawOpen := Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 indexTerm rawCode hRawCode.2
    have hRawClose (depth : Nat) :
        Term.closeFreeAt SetSort.set 201 depth rawCode = rawCode :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 201 depth rawCode hRawCode.2 (by
          simp [rawCode, Term.freeSupport, Term.freeSupportList,
            indexTerm, finite_numeral_term_freeSupport])
    simpa [constant_symbol_condition, rawCode, indexTerm,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hRawOpen, hRawClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using
      FirstOrder.Derives.conjIntro hIndexMem
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) rawCode)
  exact FirstOrder.Derives.iffElimLeft
    hDefinition
    hCondition
/-- 常元编码运算的规范结果属于常元符号集合。 -/
theorem constant_code_mem_constant_symbols (index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      const_codeₘ(numₘ(index)) ∈ₘ ConstSymₘ := by
  let indexTerm : SetTerm := numₘ(index)
  let code : SetTerm := const_codeₘ(indexTerm)
  let rawCode : SetTerm := constant_symbol_code_term indexTerm
  have hIndex : Term.Admissible indexTerm SetSort.set :=
    finite_numeral_term_admissible index
  have hCode : Term.Admissible code SetSort.set :=
    constant_code_term_admissible indexTerm hIndex
  have hRawCode : Term.Admissible rawCode SetSort.set :=
    constant_symbol_code_term_admissible indexTerm hIndex
  have hDefinition := gq_weaken_symbol_operator (constant_code_definition_instance_derives
      indexTerm code hIndex hCode)
  have hCodeRaw :
      ⊢ₘ[godel_quotation_theory] code ≐ₘ rawCode := by
    have hReflexive :
        ⊢ₘ[godel_quotation_theory]
          code ≐ₘ const_codeₘ(indexTerm) := by
      simpa [code] using
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) code)
    simpa [code, rawCode,
      constant_code_definition_instance] using
      FirstOrder.Derives.iffElimRight hDefinition hReflexive
  exact FirstOrder.Derives.iffElimLeft (membership_left_iff_of_equality
      code rawCode ConstSymₘ hCode hRawCode
      constant_symbol_set_term_admissible hCodeRaw) (by
      simpa [rawCode, indexTerm] using
        constant_symbol_code_mem_constant_symbols index)
/-- 常元编码运算的规范结果满足“是项编码”谓词。 -/
theorem constant_code_is_term_code (index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      term_codeₘ(const_codeₘ(numₘ(index))) := by
  let code : SetTerm := const_codeₘ(numₘ(index))
  have hCode : Term.Admissible code SetSort.set :=
    constant_code_term_admissible (numₘ(index)) (finite_numeral_term_admissible index)
  have hSetMember := gq_subset_member
    ConstSymₘ TermCodeₘ code
    constant_symbol_set_term_admissible
    term_code_set_term_admissible hCode
    gq_constant_symbols_subset_term_codes (by
      simpa [code] using constant_code_mem_constant_symbols index)
  exact FirstOrder.Derives.iffElimLeft (gq_term_code_definition_instance code hCode) hSetMember
/--
非空参数序列满足编码字符串空间、定义域和逐点项编码条件时，正元函数应用结果
满足“是项编码”谓词。
-/
theorem gq_term_application_code_is_term_code (arityPredecessor index : Nat) (arguments : SetTerm) (hArguments : Term.Admissible arguments SetSort.set)
    (hArgumentsClosed : Term.freeSupport arguments = []) (hArgumentsPositive :
      ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)) (hDomain :
      ⊢ₘ[godel_quotation_theory]
        domₘ(arguments) ≐ₘ Sₘ(numₘ(arityPredecessor))) (hValues :
      ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 213], (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ ((arguments ·ₘ x#213) ∈ₘ TermCodeₘ)) :
    ⊢ₘ[godel_quotation_theory]
      term_codeₘ(
        term_application_code_term (numₘ(arityPredecessor)) (numₘ(index)) arguments) := by
  let arityTerm : SetTerm := numₘ(arityPredecessor)
  let indexTerm : SetTerm := numₘ(index)
  let code : SetTerm :=
    term_application_code_term arityTerm indexTerm arguments
  have hArity : Term.Admissible arityTerm SetSort.set :=
    finite_numeral_term_admissible arityPredecessor
  have hIndex : Term.Admissible indexTerm SetSort.set :=
    finite_numeral_term_admissible index
  have hCode : Term.Admissible code SetSort.set :=
    term_application_code_term_admissible
      arityTerm indexTerm arguments hArity hIndex hArguments
  have hArityMem :
      ⊢ₘ[godel_quotation_theory] arityTerm ∈ₘ ωₘ :=
    gq_weaken_standard_sequence <| by
      simpa [arityTerm] using
        standard_sequence_finite_numeral_mem_omega arityPredecessor
  have hIndexMem :
      ⊢ₘ[godel_quotation_theory] indexTerm ∈ₘ ωₘ :=
    gq_weaken_standard_sequence <| by
      simpa [indexTerm] using
        standard_sequence_finite_numeral_mem_omega index
  have hCodeReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ
          term_application_code_term
            arityTerm indexTerm arguments :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) code
  have hBase :
      ⊢ₘ[godel_quotation_theory] ((arityTerm ∈ₘ ωₘ) ∧ₘ ((indexTerm ∈ₘ ωₘ) ∧ₘ ((arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ∧ₘ (domₘ(arguments) ≐ₘ Sₘ(arityTerm))))) ∧ₘ
          ((∀ₘ[SetSort.set, 213], (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ ((arguments ·ₘ x#213) ∈ₘ TermCodeₘ)) ∧ₘ (code ≐ₘ
              term_application_code_term
                arityTerm indexTerm arguments)) :=
    FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro hArityMem (FirstOrder.Derives.conjIntro hIndexMem (FirstOrder.Derives.conjIntro
            hArgumentsPositive (by simpa [arityTerm] using hDomain)))) (FirstOrder.Derives.conjIntro hValues hCodeReflexive)
  have hArgumentsOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term arguments = arguments :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term arguments hArguments.2
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hArgumentsClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth arguments = arguments :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth arguments hArguments.2 (by rw [hArgumentsClosed]; exact List.not_mem_nil)
  have hCodeClosed : Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hArgumentsClosed, arityTerm, indexTerm,
      finite_numeral_term_freeSupport]
  have hCodeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth code hCode.2 (by rw [hCodeClosed]; exact List.not_mem_nil)
  have hClosureAt := FirstOrder.Derives.forall_elim
    (term := code) gq_term_application_closed
  have hClosureAt' :
      ⊢ₘ[godel_quotation_theory]
        term_application_from_condition TermCodeₘ code ⟶ₘ (code ∈ₘ TermCodeₘ) := by
    simpa [term_application_from_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      hCodeOpen, hCodeClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using
      hClosureAt
  have hCondition :
      ⊢ₘ[godel_quotation_theory]
        term_application_from_condition TermCodeₘ code := by
    rw [term_application_from_condition]
    nd_apply FirstOrder.Derives.exists_intro (term := arityTerm)
    nd_apply FirstOrder.Derives.exists_intro (term := indexTerm)
    nd_apply FirstOrder.Derives.exists_intro (term := arguments)
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt, Term.substituteFree,
      set_variable, set_bound_variable,
      arityTerm, indexTerm, code,
      hArgumentsOpen, hCodeOpen,
      hArgumentsClose, hCodeClose,
      gq_finite_numeral_open, gq_finite_numeral_close] using hBase
  have hSetMember :
      ⊢ₘ[godel_quotation_theory] code ∈ₘ TermCodeₘ :=
    FirstOrder.Derives.impElim hClosureAt' hCondition
  exact FirstOrder.Derives.iffElimLeft (gq_term_code_definition_instance code hCode) hSetMember
/-! ## quotation 的项编码与原子公式编码 -/
/-- 两个项 quotation 组成的隶属原子编码属于完整公式集合。 -/
theorem gq_membership_formula_code_mem (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hLeftSupport : Term.freeSupport left = []) (hRightSupport : Term.freeSupport right = []) (hLeftCode : ⊢ₘ[godel_quotation_theory] term_codeₘ(left))
    (hRightCode : ⊢ₘ[godel_quotation_theory] term_codeₘ(right)) :
    ⊢ₘ[godel_quotation_theory]
      membership_atomic_formula_code_term left right ∈ₘ FormulaCodeₘ := by
  let code := membership_atomic_formula_code_term left right
  have hCode : Term.Admissible code SetSort.set :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term left right
      membership_symbol_code_term_admissible hLeft hRight
  have hCodeSupport : Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      hLeftSupport, hRightSupport]
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ membership_atomic_formula_code_term left right := by
    simpa [code] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code)
  have hEqualityCode :
      Term.Admissible (equality_atomic_formula_code_term left right)
        SetSort.set :=
    binary_atomic_formula_code_term_admissible
      equality_symbol_code_term left right (logical_symbol_code_term_admissible .equality)
      hLeft hRight
  exact gq_binary_atomic_formula_code_mem
    left right code hLeft hRight hCode
    hLeftSupport hRightSupport hCodeSupport
    hLeftCode hRightCode
      (FirstOrder.Derives.disjIntroRight hReflexive)
/-- 两个项 quotation 组成的等式原子编码属于完整公式集合。 -/
theorem gq_equality_formula_code_mem (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hLeftSupport : Term.freeSupport left = []) (hRightSupport : Term.freeSupport right = []) (hLeftCode : ⊢ₘ[godel_quotation_theory] term_codeₘ(left))
    (hRightCode : ⊢ₘ[godel_quotation_theory] term_codeₘ(right)) :
    ⊢ₘ[godel_quotation_theory]
      eq_codeₘ(left, right) ∈ₘ FormulaCodeₘ := by
  let code := eq_codeₘ(left, right)
  let rawCode := equality_atomic_formula_code_term left right
  have hCode : Term.Admissible code SetSort.set :=
    equality_formula_code_term_admissible left right hLeft hRight
  have hCodeSupport : Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hLeftSupport, hRightSupport]
  have hDefinition := gq_weaken_formula_constructor (equality_formula_code_definition_instance_derives
      left right code hLeft hRight hCode)
  have hReflexive :
      ⊢ₘ[godel_quotation_theory] code ≐ₘ eq_codeₘ(left, right) := by
    simpa [code] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code)
  have hDefinition' :
      ⊢ₘ[godel_quotation_theory] (code ≐ₘ eq_codeₘ(left, right)) ↔ₘ (code ≐ₘ rawCode) := by
    have hContract := FirstOrder.Derives.impElim hDefinition (FirstOrder.Derives.conjIntro hLeftCode hRightCode)
    simpa [equality_formula_code_definition_instance, rawCode] using
      hContract
  have hRawEquality :
      ⊢ₘ[godel_quotation_theory] code ≐ₘ rawCode := by
    exact FirstOrder.Derives.iffElimRight hDefinition' hReflexive
  have hMembershipCode :
      Term.Admissible (membership_atomic_formula_code_term left right)
        SetSort.set :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term left right
      membership_symbol_code_term_admissible
      hLeft hRight
  exact gq_binary_atomic_formula_code_mem
    left right code hLeft hRight hCode
    hLeftSupport hRightSupport hCodeSupport
    hLeftCode hRightCode
      (FirstOrder.Derives.disjIntroLeft
        (by simpa [rawCode] using hRawEquality))
/-- 完整公式编码集合由规范等式原子码见证为非空。 -/
theorem formula_code_set_nonempty_derives :
    ⊢ₘ[godel_quotation_theory]
      FormulaCodeₘ ≠ₘ ∅ₘ := by
  let constantCode : SetTerm :=
    const_codeₘ(numₘ(0))
  let witness : SetTerm :=
    eq_codeₘ(constantCode, constantCode)
  have hConstant :
      Term.Admissible constantCode SetSort.set :=
    constant_code_term_admissible (numₘ(0)) (finite_numeral_term_admissible 0)
  have hConstantSupport :
      Term.freeSupport constantCode = [] := by
    native_decide
  have hWitness :
      Term.Admissible witness SetSort.set :=
    equality_formula_code_term_admissible
      constantCode constantCode hConstant hConstant
  have hWitnessMember :
      ⊢ₘ[godel_quotation_theory]
        witness ∈ₘ FormulaCodeₘ := by
    simpa [witness, constantCode] using (gq_equality_formula_code_mem
        constantCode constantCode
        hConstant hConstant
        hConstantSupport hConstantSupport (by
          simpa [constantCode] using
            constant_code_is_term_code 0) (by
          simpa [constantCode] using
            constant_code_is_term_code 0))
  have hNonempty :
      ⊢ₘ[godel_quotation_theory] (witness ∈ₘ FormulaCodeₘ) ⟶ₘ (FormulaCodeₘ ≠ₘ ∅ₘ) := by
    apply gq_weaken_standard_sequence
    exact FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFormula))))) (member_implies_set_nonempty
        witness FormulaCodeₘ
        hWitness formula_code_set_term_admissible)
  exact FirstOrder.Derives.impElim
    hNonempty hWitnessMember
/-! ## 结构 quotation 的公式编码正确性 -/
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
