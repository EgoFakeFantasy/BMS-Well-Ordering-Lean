import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.Sequence
/-!
# Gödel 替换规格的输运与对象接口
本模块封装闭代码上的规格输运、唯一性以及 quotation 专用替换结论。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
universe u v w
attribute [local simp] finite_numeral_term_freeSupport
/-! ## 闭代码上的替换规格输运 -/
/--
自由变量替换逐参数穿过 `code_substitution_spec`。
规格内部的 `310`、`311` 已被关闭为局部 binder；显式的新鲜性条件保证实参与
替换项在构造规格时没有被这两个编号捕获。该交换律把 LN 展开封装在 substitution
公共层，后续关系图不必重复展开整套分片定义。
-/
theorem code_substitution_spec_substituteFree (parameter : FreeVarId) (substitute source boundVariable replacement candidate : SetTerm)
    (hFresh : ReservedIdsFresh [310, 311]
      [substitute, source, boundVariable, replacement, candidate])
    (hSubstitute : Term.CheckCertificate substitute SetSort.set := by
      prove_term_check)
    (hSource : Term.CheckCertificate source SetSort.set := by
      prove_term_check)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set := by
      prove_term_check)
    (hReplacement : Term.CheckCertificate replacement SetSort.set := by
      prove_term_check)
    (hCandidate : Term.CheckCertificate candidate SetSort.set := by
      prove_term_check) :
    Formula.substituteFree SetSort.set parameter substitute (code_substitution_spec
          source boundVariable replacement candidate) =
      code_substitution_spec (Term.substituteFree SetSort.set parameter substitute source) (Term.substituteFree SetSort.set parameter substitute boundVariable)
        (Term.substituteFree SetSort.set parameter substitute replacement) (Term.substituteFree SetSort.set parameter substitute candidate) := by
  have hClose (term : SetTerm)
      (hTerm : Term.CheckCertificate term SetSort.set) (hTermMem :
        term ∈ [substitute, source, boundVariable, replacement, candidate]) (reserved depth : Nat) (hReserved : reserved ∈ [310, 311]) :
      Term.closeFreeAt SetSort.set reserved depth term = term :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set reserved depth term hTerm.admissible.2
      (hFresh term hTermMem reserved hReserved)
  have hSubstitutedClosed (term : SetTerm)
      (hTerm : Term.CheckCertificate term SetSort.set) :
      Term.BoundClosed (Term.substituteFree SetSort.set parameter substitute term) :=
    Term.substituteFree_scoped
      hTerm.admissible.2 hSubstitute.admissible.2
  have hSubstitutedFresh (term : SetTerm) (hTermMem :
        term ∈ [substitute, source, boundVariable, replacement, candidate]) (reserved : Nat) (hReserved : reserved ∈ [310, 311]) : (SetSort.set, reserved) ∉
        Term.freeSupport (Term.substituteFree SetSort.set parameter substitute term) :=
    Term.not_mem_freeSupport_substituteFree (SetSort.set, reserved) SetSort.set parameter substitute term (hFresh substitute (by simp) reserved hReserved)
      (hFresh term hTermMem reserved hReserved)
  have hCloseSubstituted (term : SetTerm)
      (hTerm : Term.CheckCertificate term SetSort.set) (hTermMem :
        term ∈ [substitute, source, boundVariable, replacement, candidate]) (reserved depth : Nat) (hReserved : reserved ∈ [310, 311]) :
      Term.closeFreeAt SetSort.set reserved depth (Term.substituteFree SetSort.set parameter substitute term) =
        Term.substituteFree SetSort.set parameter substitute term :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set reserved depth (Term.substituteFree SetSort.set parameter substitute term) (hSubstitutedClosed term hTerm)
      (hSubstitutedFresh term hTermMem reserved hReserved)
  have hZero : Term.CheckCertificate (numₘ(0)) SetSort.set := by
    prove_term_check
  have hZeroFresh (reserved : Nat) : (SetSort.set, reserved) ∉ Term.freeSupport (numₘ(0)) := by
    rw [finite_numeral_term_freeSupport]
    intro hMember
    cases hMember
  have hZeroClose (reserved depth : Nat) :
      Term.closeFreeAt SetSort.set reserved depth (numₘ(0)) =
        numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set reserved depth (numₘ(0))
        hZero.admissible.2 (hZeroFresh reserved)
  have hZeroFixed :
      Term.substituteFree SetSort.set parameter substitute (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter substitute (numₘ(0)) (by
        rw [finite_numeral_term_freeSupport]
        intro hMember
        cases hMember)
  simp [code_substitution_spec, substitution_piece_condition,
    Formula.substituteFree, Formula.next_depth,
    Formula.closeFreeAt, Term.substituteFree,
    Term.closeFreeAt, set_variable,
    finite_numeral_term,
    hClose source hSource (by simp),
    hClose boundVariable hBoundVariable (by simp),
    hClose replacement hReplacement (by simp),
    hClose candidate hCandidate (by simp),
    hCloseSubstituted source hSource (by simp),
    hCloseSubstituted boundVariable hBoundVariable (by simp),
    hCloseSubstituted replacement hReplacement (by simp),
    hCloseSubstituted candidate hCandidate (by simp),
    ]
/--
四个闭代码分别沿已证明等式变化时，`code_substitution_spec` 保持成立。
quotation 与标准序列项都没有对象语言自由变量，因此本接口恰好覆盖编码计算层需要的
输运，同时把规格内部的保留编号 `310`、`311` 完全封装在实现内。
-/
theorem code_substitution_spec_congr_of_code_equalities
    {T : SetTheory} {Γ : Context signature} (source₁ source₂ boundVariable₁ boundVariable₂
      replacement₁ replacement₂ candidate₁ candidate₂ : SetTerm) (hSource₁ : Numbered.CodeBoundary source₁) (hSource₂ : Numbered.CodeBoundary source₂)
    (hBoundVariable₁ : Numbered.CodeBoundary boundVariable₁) (hBoundVariable₂ : Numbered.CodeBoundary boundVariable₂)
    (hReplacement₁ : Numbered.CodeBoundary replacement₁) (hReplacement₂ : Numbered.CodeBoundary replacement₂) (hCandidate₁ : Numbered.CodeBoundary candidate₁)
    (hCandidate₂ : Numbered.CodeBoundary candidate₂) (hSourceEquality : Γ ⊢ₘ[T] source₁ ≐ₘ source₂) (hBoundVariableEquality :
      Γ ⊢ₘ[T] boundVariable₁ ≐ₘ boundVariable₂) (hReplacementEquality :
      Γ ⊢ₘ[T] replacement₁ ≐ₘ replacement₂) (hCandidateEquality : Γ ⊢ₘ[T] candidate₁ ≐ₘ candidate₂) (hSpecification :
      Γ ⊢ₘ[T]
        code_substitution_spec
          source₁ boundVariable₁ replacement₁ candidate₁) :
    Γ ⊢ₘ[T]
      code_substitution_spec
        source₂ boundVariable₂ replacement₂ candidate₂ := by
  let parameter : FreeVarId := 397
  have hFixed (term replacement : SetTerm) (hTerm : Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set parameter replacement term = term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement term (by
        rw [hTerm.2]
        simp)
  have hClose (term : SetTerm) (hTerm : Numbered.CodeBoundary term) (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth term = term :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth term hTerm.1.2 (by
        rw [hTerm.2]
        simp)
  have hZero : Numbered.CodeBoundary (numₘ(0)) := by
    exact ⟨finite_numeral_term_admissible 0, by
      rw [finite_numeral_term_freeSupport]⟩
  let sourceBody : SetFormula :=
    code_substitution_spec (x#parameter) boundVariable₁ replacement₁ candidate₁
  have hSourceTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := source₁) (right := source₂)
      (body := sourceBody)
      hSourceEquality (by
        simpa [sourceBody, parameter, code_substitution_spec,
          substitution_piece_condition, Formula.substituteFree,
          Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
          Term.closeFreeAt, set_variable,
          hClose source₁ hSource₁,
          hClose boundVariable₁ hBoundVariable₁,
          hClose replacement₁ hReplacement₁,
          hClose candidate₁ hCandidate₁,
          hClose (numₘ(0)) hZero,
          hFixed (numₘ(0)) source₁ hZero,
          hFixed boundVariable₁ source₁ hBoundVariable₁,
          hFixed replacement₁ source₁ hReplacement₁,
          hFixed candidate₁ source₁ hCandidate₁] using hSpecification)
  have hSourceSpecification :
      Γ ⊢ₘ[T]
        code_substitution_spec
          source₂ boundVariable₁ replacement₁ candidate₁ := by
    simpa [sourceBody, parameter, code_substitution_spec,
      substitution_piece_condition, Formula.substituteFree,
      Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
      Term.closeFreeAt, set_variable,
      hClose source₂ hSource₂,
      hClose boundVariable₁ hBoundVariable₁,
      hClose replacement₁ hReplacement₁,
      hClose candidate₁ hCandidate₁,
      hClose (numₘ(0)) hZero,
      hFixed (numₘ(0)) source₂ hZero,
      hFixed boundVariable₁ source₂ hBoundVariable₁,
      hFixed replacement₁ source₂ hReplacement₁,
      hFixed candidate₁ source₂ hCandidate₁] using hSourceTransport
  let boundVariableBody : SetFormula :=
    code_substitution_spec
      source₂ (x#parameter) replacement₁ candidate₁
  have hBoundVariableTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := boundVariable₁) (right := boundVariable₂)
      (body := boundVariableBody)
      hBoundVariableEquality (by
        simpa [boundVariableBody, parameter, code_substitution_spec,
          substitution_piece_condition, Formula.substituteFree,
          Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
          Term.closeFreeAt, set_variable,
          hClose source₂ hSource₂,
          hClose boundVariable₁ hBoundVariable₁,
          hClose replacement₁ hReplacement₁,
          hClose candidate₁ hCandidate₁,
          hClose (numₘ(0)) hZero,
          hFixed (numₘ(0)) boundVariable₁ hZero,
          hFixed source₂ boundVariable₁ hSource₂,
          hFixed replacement₁ boundVariable₁ hReplacement₁,
          hFixed candidate₁ boundVariable₁ hCandidate₁] using
          hSourceSpecification)
  have hBoundVariableSpecification :
      Γ ⊢ₘ[T]
        code_substitution_spec
          source₂ boundVariable₂ replacement₁ candidate₁ := by
    simpa [boundVariableBody, parameter, code_substitution_spec,
      substitution_piece_condition, Formula.substituteFree,
      Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
      Term.closeFreeAt, set_variable,
      hClose source₂ hSource₂,
      hClose boundVariable₂ hBoundVariable₂,
      hClose replacement₁ hReplacement₁,
      hClose candidate₁ hCandidate₁,
      hClose (numₘ(0)) hZero,
      hFixed (numₘ(0)) boundVariable₂ hZero,
      hFixed source₂ boundVariable₂ hSource₂,
      hFixed replacement₁ boundVariable₂ hReplacement₁,
      hFixed candidate₁ boundVariable₂ hCandidate₁] using
      hBoundVariableTransport
  let replacementBody : SetFormula :=
    code_substitution_spec
      source₂ boundVariable₂ (x#parameter) candidate₁
  have hReplacementTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := replacement₁) (right := replacement₂)
      (body := replacementBody)
      hReplacementEquality (by
        simpa [replacementBody, parameter, code_substitution_spec,
          substitution_piece_condition, Formula.substituteFree,
          Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
          Term.closeFreeAt, set_variable,
          hClose source₂ hSource₂,
          hClose boundVariable₂ hBoundVariable₂,
          hClose replacement₁ hReplacement₁,
          hClose candidate₁ hCandidate₁,
          hClose (numₘ(0)) hZero,
          hFixed (numₘ(0)) replacement₁ hZero,
          hFixed source₂ replacement₁ hSource₂,
          hFixed boundVariable₂ replacement₁ hBoundVariable₂,
          hFixed candidate₁ replacement₁ hCandidate₁] using
          hBoundVariableSpecification)
  have hReplacementSpecification :
      Γ ⊢ₘ[T]
        code_substitution_spec
          source₂ boundVariable₂ replacement₂ candidate₁ := by
    simpa [replacementBody, parameter, code_substitution_spec,
      substitution_piece_condition, Formula.substituteFree,
      Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
      Term.closeFreeAt, set_variable,
      hClose source₂ hSource₂,
      hClose boundVariable₂ hBoundVariable₂,
      hClose replacement₂ hReplacement₂,
      hClose candidate₁ hCandidate₁,
      hClose (numₘ(0)) hZero,
      hFixed (numₘ(0)) replacement₂ hZero,
      hFixed source₂ replacement₂ hSource₂,
      hFixed boundVariable₂ replacement₂ hBoundVariable₂,
      hFixed candidate₁ replacement₂ hCandidate₁] using
      hReplacementTransport
  let candidateBody : SetFormula :=
    code_substitution_spec
      source₂ boundVariable₂ replacement₂ (x#parameter)
  have hCandidateTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := candidate₁) (right := candidate₂)
      (body := candidateBody)
      hCandidateEquality (by
        simpa [candidateBody, parameter, code_substitution_spec,
          substitution_piece_condition, Formula.substituteFree,
          Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
          Term.closeFreeAt, set_variable,
          hClose source₂ hSource₂,
          hClose boundVariable₂ hBoundVariable₂,
          hClose replacement₂ hReplacement₂,
          hClose candidate₁ hCandidate₁,
          hClose (numₘ(0)) hZero,
          hFixed (numₘ(0)) candidate₁ hZero,
          hFixed source₂ candidate₁ hSource₂,
          hFixed boundVariable₂ candidate₁ hBoundVariable₂,
          hFixed replacement₂ candidate₁ hReplacement₂] using
          hReplacementSpecification)
  simpa [candidateBody, parameter, code_substitution_spec,
    substitution_piece_condition, Formula.substituteFree,
    Formula.next_depth, Formula.closeFreeAt, Term.substituteFree,
    Term.closeFreeAt, set_variable,
    hClose source₂ hSource₂,
    hClose boundVariable₂ hBoundVariable₂,
    hClose replacement₂ hReplacement₂,
    hClose candidate₂ hCandidate₂,
    hClose (numₘ(0)) hZero,
    hFixed (numₘ(0)) candidate₂ hZero,
    hFixed source₂ candidate₂ hSource₂,
    hFixed boundVariable₂ candidate₂ hBoundVariable₂,
    hFixed replacement₂ candidate₂ hReplacement₂] using
    hCandidateTransport
/-! ## 对象替换函数的定义规格 -/
/-- 编码级替换定义的标准前置编码条件。 -/
def code_substitution_precondition (source boundVariable replacement : SetTerm) : SetFormula := ((source ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ)) ∧ₘ
      (boundVariable ∈ₘ VarSymₘ)) ∧ₘ
    term_codeₘ(replacement)
/-- 三个 admissible 输入自动给出编码替换前置条件的公式边界。 -/
theorem code_substitution_precondition_admissible (source boundVariable replacement : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set) (hReplacement : Term.Admissible replacement SetSort.set) :
    Formula.Admissible (code_substitution_precondition
        source boundVariable replacement) := by
  have hCodeUnion :
      Term.Admissible (TermCodeₘ ∪ₘ FormulaCodeₘ) SetSort.set :=
    binary_union_term_admissible
      TermCodeₘ FormulaCodeₘ
      term_code_set_term_admissible
      formula_code_set_term_admissible
  have hSourceCode :=
    membership_formula_admissible hSource hCodeUnion
  have hBoundVariableCode :=
    membership_formula_admissible
      hBoundVariable variable_symbol_set_term_admissible
  have hReplacementCode :
      Formula.Admissible (term_codeₘ(replacement)) := by
    apply Formula.Admissible.rel
    simpa [signature] using (ArgsAdmissible.cons hReplacement ArgsAdmissible.nil)
  simpa [code_substitution_precondition] using
    Formula.Admissible.conj (Formula.Admissible.conj hSourceCode hBoundVariableCode)
      hReplacementCode
/- 编码替换函数项的合法性由三个输入项证书计算。 -/
@[term_check]
theorem code_substitution_term_check
    {source boundVariable replacement : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hReplacement : Term.CheckCertificate replacement SetSort.set) :
    Term.CheckCertificate
      (subst_codeₘ(source, boundVariable, replacement)) SetSort.set :=
  Term.check_admissible_complete <|
    code_substitution_term_admissible
      source boundVariable replacement
      hSource.admissible hBoundVariable.admissible
      hReplacement.admissible
/- 编码替换前置条件的公式合法性由三个输入项证书计算。 -/
@[formula_check]
theorem code_substitution_precondition_check
    {source boundVariable replacement : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hReplacement : Term.CheckCertificate replacement SetSort.set) :
    Formula.CheckCertificate
      (code_substitution_precondition
        source boundVariable replacement) :=
  Formula.check_admissible_complete <|
    code_substitution_precondition_admissible
      source boundVariable replacement
      hSource.admissible hBoundVariable.admissible
      hReplacement.admissible
/- 编码替换规格的公式合法性由四个输入项证书计算。 -/
@[formula_check]
theorem code_substitution_spec_check
    {source boundVariable replacement candidate : SetTerm}
    (hSource : Term.CheckCertificate source SetSort.set := by
      prove_term_check)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set := by
      prove_term_check)
    (hReplacement : Term.CheckCertificate replacement SetSort.set := by
      prove_term_check)
    (hCandidate : Term.CheckCertificate candidate SetSort.set := by
      prove_term_check) :
    Formula.CheckCertificate
      (code_substitution_spec
        source boundVariable replacement candidate) :=
  Formula.check_admissible_complete <|
    code_substitution_spec_admissible
      source boundVariable replacement candidate
      hSource.admissible hBoundVariable.admissible
      hReplacement.admissible hCandidate.admissible
/--
任意满足替换规格的候选在定义前提下都等于规范对象函数项。
该方向是后续把标准符号串计算结果接回 `subst_codeₘ` 的唯一性接口。
-/
theorem code_substitution_spec_implies_eq_term
    (source boundVariable replacement candidate : SetTerm)
    (hSource : Term.CheckCertificate source SetSort.set)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set)
    (hReplacement : Term.CheckCertificate replacement SetSort.set)
    (hCandidate : Term.CheckCertificate candidate SetSort.set)
    (hFresh : ReservedIdsFresh [310, 311]
      [source, boundVariable, replacement, candidate]) :
    ⊢ₘ[substitution_variable_theory]
      code_substitution_precondition source boundVariable replacement ⟶ₘ
        code_substitution_spec source boundVariable replacement candidate ⟶ₘ
          candidate ≐ₘ
            subst_codeₘ(source, boundVariable, replacement) := by
  have hDefinition :=
    code_substitution_definition_instance_derives
      source boundVariable replacement candidate
      hSource.admissible hBoundVariable.admissible
      hReplacement.admissible hCandidate.admissible hFresh
  have hDefinition' :
      ⊢ₘ[substitution_variable_theory]
        code_substitution_precondition source boundVariable replacement ⟶ₘ ((candidate ≐ₘ
              subst_codeₘ(source, boundVariable, replacement)) ↔ₘ
            code_substitution_spec source boundVariable replacement candidate) := by
    simpa only [code_substitution_precondition,
      code_substitution_definition_instance] using hDefinition
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      [code_substitution_spec source boundVariable replacement candidate,
        code_substitution_precondition source boundVariable replacement]
        ⊢ₘ[substitution_variable_theory]
          code_substitution_precondition source boundVariable replacement :=
    .assumption (by simp)
  have hSpecification :
      [code_substitution_spec source boundVariable replacement candidate,
        code_substitution_precondition source boundVariable replacement]
        ⊢ₘ[substitution_variable_theory]
          code_substitution_spec source boundVariable replacement candidate :=
    .assumption (by simp)
  have hSpecificationIff := FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons hDefinition')
    hPrecondition
  exact FirstOrder.Derives.iffElimLeft hSpecificationIff hSpecification
/-- 在定义前提下，`code_substitution_spec` 的候选唯一。 -/
theorem code_substitution_spec_unique_derives
    (source boundVariable replacement first second : SetTerm)
    (hFirstFresh : ReservedIdsFresh [310, 311]
      [source, boundVariable, replacement, first])
    (hSecondFresh : ReservedIdsFresh [310, 311]
      [source, boundVariable, replacement, second])
    (hSource : Term.CheckCertificate source SetSort.set := by
      prove_term_check)
    (hBoundVariable : Term.CheckCertificate boundVariable SetSort.set := by
      prove_term_check)
    (hReplacement : Term.CheckCertificate replacement SetSort.set := by
      prove_term_check)
    (hFirst : Term.CheckCertificate first SetSort.set := by
      prove_term_check)
    (hSecond : Term.CheckCertificate second SetSort.set := by
      prove_term_check) :
    ⊢ₘ[substitution_variable_theory]
      code_substitution_precondition source boundVariable replacement ⟶ₘ
        code_substitution_spec source boundVariable replacement first ⟶ₘ
          code_substitution_spec source boundVariable replacement second ⟶ₘ
            first ≐ₘ second := by
  let canonical := subst_codeₘ(source, boundVariable, replacement)
  have hFirstEq := code_substitution_spec_implies_eq_term
    source boundVariable replacement first
    hSource hBoundVariable hReplacement hFirst hFirstFresh
  have hSecondEq := code_substitution_spec_implies_eq_term
    source boundVariable replacement second
    hSource hBoundVariable hReplacement hSecond hSecondFresh
  have hSecondSymm :
      ⊢ₘ[substitution_variable_theory] (second ≐ₘ canonical) ⟶ₘ (canonical ≐ₘ second) :=
    Metatheory.Derives.equality_symm_imp
  have hTrans :
      ⊢ₘ[substitution_variable_theory] (first ≐ₘ canonical) ⟶ₘ (canonical ≐ₘ second) ⟶ₘ (first ≐ₘ second) :=
    Metatheory.Derives.equality_trans_imp
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let precondition :=
    code_substitution_precondition source boundVariable replacement
  let firstSpec :=
    code_substitution_spec source boundVariable replacement first
  let secondSpec :=
    code_substitution_spec source boundVariable replacement second
  have hPrecondition :
      [secondSpec, firstSpec, precondition]
        ⊢ₘ[substitution_variable_theory] precondition :=
    .assumption (by simp)
  have hFirstSpec :
      [secondSpec, firstSpec, precondition]
        ⊢ₘ[substitution_variable_theory] firstSpec :=
    .assumption (by simp)
  have hSecondSpec :
      [secondSpec, firstSpec, precondition]
        ⊢ₘ[substitution_variable_theory] secondSpec :=
    .assumption (by simp)
  have hFirstEqAt :
      [secondSpec, firstSpec, precondition]
        ⊢ₘ[substitution_variable_theory] first ≐ₘ canonical :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons <|
            FirstOrder.Derives.context_weaken_cons hFirstEq) (by simpa [precondition] using hPrecondition)) (by simpa [firstSpec] using hFirstSpec)
  have hSecondEqAt :
      [secondSpec, firstSpec, precondition]
        ⊢ₘ[substitution_variable_theory] second ≐ₘ canonical :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons <|
            FirstOrder.Derives.context_weaken_cons hSecondEq) (by simpa [precondition] using hPrecondition)) (by simpa [secondSpec] using hSecondSpec)
  have hCanonicalSecond := FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons hSecondSymm)
    hSecondEqAt
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.context_weaken_cons hTrans)
      hFirstEqAt)
    hCanonicalSecond
/-! ## quotation 专用的对象替换规格 -/
/--
成功 quotation 的公式与替换项自动满足对象替换函数的编码前置条件。
这条接口把公式代码、具名变量符号代码和替换项代码三个成员事实统一打包；关系图式
对角化等需要调用替换函数唯一性的模块可以直接复用，而不必重新展开编码闭包证明。
-/
theorem quote?_code_substitution_precondition_derives
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {sourceCode : SetTerm}
    {replacement : Term σ} {replacementCode : SetTerm} (id : FreeVarId) (hSourceQuote : Numbered.quote? formula = some sourceCode) (hReplacementQuote :
      Numbered.quote_term_with?
        free_name [] replacement = some replacementCode) :
    ⊢ₘ[godel_quotation_theory]
      code_substitution_precondition sourceCode (named_variable_code (free_name id)) replacementCode := by
  have hSource : Term.CheckCertificate sourceCode SetSort.set :=
    Term.check_admissible_complete
      (Numbered.quote?_code_boundary hSourceQuote).1
  have hSourceUnion :
      ⊢ₘ[godel_quotation_theory]
        sourceCode ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ) :=
    gq_mem_binary_union_right
      TermCodeₘ FormulaCodeₘ sourceCode
      term_code_set_term_admissible formula_code_set_term_admissible
      hSource.admissible
      (Numbered.quote?_formula_code_mem hSourceQuote)
  have hVariableMember :
      ⊢ₘ[godel_quotation_theory]
        named_variable_code (free_name id) ∈ₘ VarSymₘ :=
    named_variable_code_mem_variable_symbols (free_name id)
  have hReplacementCode :
      ⊢ₘ[godel_quotation_theory] term_codeₘ(replacementCode) :=
    Numbered.quote_term_with?_is_term_code _ _ hReplacementQuote
  exact FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro hSourceUnion hVariableMember)
    hReplacementCode
/--
quotation 后的真实目标代码满足逐 token 替换规格。
本定理把四个标准序列值分别输运回源公式代码、变量符号代码、替换项代码和目标公式
代码；因此结果候选不再是抽象函数项 `subst_codeₘ`，而是替换后公式自身的 quotation。
-/
theorem quote?_substitution_result_spec_derives
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    {sourceTokens : List Nat} {sourceCode : SetTerm}
    {replacement : Term σ}
    {replacementTokens : List Nat} {replacementCode : SetTerm}
    {targetCode : SetTerm} (id : FreeVarId) (hSourceTokens :
      Numbered.quote_tokens? formula = some sourceTokens) (hSourceCode : Numbered.quote? formula = some sourceCode) (hReplacementTokens :
      quote_term_tokens? replacement = some replacementTokens) (hReplacementCode :
      Numbered.quote_term_with?
        free_name [] replacement = some replacementCode) (hTargetCode :
      Numbered.quote? (Formula.substituteFree
            numbering.objectSort id replacement formula) =
        some targetCode) :
    ⊢ₘ[godel_quotation_theory]
      code_substitution_spec
        sourceCode (Numbered.named_variable_code (free_name id))
        replacementCode targetCode := by
  let boundToken := variable_token (free_name id)
  let standardSource := standard_token_sequence sourceTokens
  let standardBound := standard_token_sequence [boundToken]
  let standardReplacement :=
    standard_token_sequence replacementTokens
  let targetTokens :=
    substitute_tokens sourceTokens boundToken replacementTokens
  let standardTarget := standard_token_sequence targetTokens
  have hReplacementClosed : Term.BoundClosed replacement :=
    quote_term_tokens?_boundClosed_of_some hReplacementTokens
  have hTargetTokens :
      Numbered.quote_tokens? (Formula.substituteFree
            numbering.objectSort id replacement formula) =
        some targetTokens := by
    simpa [targetTokens, boundToken] using (quote_tokens?_substituteFree_some
        hReplacementClosed hSourceTokens hReplacementTokens)
  have hStandardBoundary (tokens : List Nat) :
      Numbered.CodeBoundary (standard_token_sequence tokens) :=
    ⟨standard_token_sequence_admissible tokens,
      standard_token_sequence_freeSupport_nil tokens⟩
  have hSourceBoundary : Numbered.CodeBoundary sourceCode :=
    Numbered.quote?_code_boundary hSourceCode
  have hBoundBoundary :
      Numbered.CodeBoundary (Numbered.named_variable_code (free_name id)) := by
    exact
      ⟨variable_code_term_admissible (numₘ(free_name id)) (finite_numeral_term_admissible (free_name id)),
        named_variable_code_freeSupport (free_name id)⟩
  have hReplacementBoundary :
      Numbered.CodeBoundary replacementCode :=
    Numbered.quote_term_with?_code_boundary
      free_name [] hReplacementCode
  have hTargetBoundary : Numbered.CodeBoundary targetCode :=
    Numbered.quote?_code_boundary hTargetCode
  have hSourceValue :
      ⊢ₘ[godel_quotation_theory]
        sourceCode ≐ₘ standardSource := by
    simpa [standardSource] using
      quote?_eq_standard_token_sequence hSourceTokens hSourceCode
  have hBoundValue :
      ⊢ₘ[godel_quotation_theory]
        Numbered.named_variable_code (free_name id) ≐ₘ
          standardBound := by
    simpa [standardBound, boundToken] using
      named_variable_code_eq_standard_token_sequence (free_name id)
  have hReplacementValue :
      ⊢ₘ[godel_quotation_theory]
        replacementCode ≐ₘ standardReplacement := by
    simpa [quote_term_tokens?, standardReplacement] using
      quote_term_with?_eq_standard_token_sequence
        free_name [] hReplacementTokens hReplacementCode
  have hTargetValue :
      ⊢ₘ[godel_quotation_theory]
        targetCode ≐ₘ standardTarget := by
    simpa [standardTarget] using
      quote?_eq_standard_token_sequence hTargetTokens hTargetCode
  have hStandardSourceValue :
      ⊢ₘ[godel_quotation_theory]
        standardSource ≐ₘ sourceCode :=
    Metatheory.Derives.equality_symm hSourceValue
  have hStandardBoundValue :
      ⊢ₘ[godel_quotation_theory]
        standardBound ≐ₘ
          Numbered.named_variable_code (free_name id) :=
    Metatheory.Derives.equality_symm hBoundValue
  have hStandardReplacementValue :
      ⊢ₘ[godel_quotation_theory]
        standardReplacement ≐ₘ replacementCode :=
    Metatheory.Derives.equality_symm hReplacementValue
  have hStandardTargetValue :
      ⊢ₘ[godel_quotation_theory]
        standardTarget ≐ₘ targetCode :=
    Metatheory.Derives.equality_symm hTargetValue
  have hStandardSpecification :
      ⊢ₘ[godel_quotation_theory]
        code_substitution_spec standardSource standardBound
          standardReplacement standardTarget := by
    simpa [standardSource, standardBound, standardReplacement,
      standardTarget, targetTokens, boundToken] using
      gq_weaken_standard_sequence (standard_token_sequence_code_substitution_spec
          sourceTokens boundToken replacementTokens)
  exact code_substitution_spec_congr_of_code_equalities
    standardSource sourceCode
    standardBound (Numbered.named_variable_code (free_name id))
    standardReplacement replacementCode
    standardTarget targetCode (hStandardBoundary sourceTokens)
    hSourceBoundary (hStandardBoundary [boundToken])
    hBoundBoundary (hStandardBoundary replacementTokens)
    hReplacementBoundary (hStandardBoundary targetTokens)
    hTargetBoundary
    hStandardSourceValue
    hStandardBoundValue
    hStandardReplacementValue
    hStandardTargetValue
    hStandardSpecification
/--
quotation 后的真实替换结果码等于对象替换函数项。
真实结果先由逐 token 正确性满足 `code_substitution_spec`，再由对象函数定义的唯一性
收束到 `subst_codeₘ`；调用方无需再次展开标准序列运输或保留变量新鲜性。
-/
theorem quote?_substitution_result_eq_derives
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ}
    {sourceTokens : List Nat} {sourceCode : SetTerm}
    {replacement : Term σ}
    {replacementTokens : List Nat} {replacementCode : SetTerm}
    {targetCode : SetTerm} (id : FreeVarId) (hSourceTokens :
      Numbered.quote_tokens? formula = some sourceTokens) (hSourceCode :
      Numbered.quote? formula = some sourceCode) (hReplacementTokens :
      quote_term_tokens? replacement = some replacementTokens) (hReplacementCode :
      Numbered.quote_term_with?
        free_name [] replacement = some replacementCode) (hTargetCode :
      Numbered.quote? (Formula.substituteFree
            numbering.objectSort id replacement formula) =
        some targetCode) :
    ⊢ₘ[godel_quotation_theory]
      targetCode ≐ₘ
        subst_codeₘ(
          sourceCode,
          Numbered.named_variable_code (free_name id),
          replacementCode) := by
  have hSourceBoundary : Numbered.CodeBoundary sourceCode :=
    Numbered.quote?_code_boundary hSourceCode
  have hBoundBoundary :
      Numbered.CodeBoundary (Numbered.named_variable_code (free_name id)) :=
    ⟨variable_code_term_admissible (numₘ(free_name id)) (finite_numeral_term_admissible (free_name id)),
      named_variable_code_freeSupport (free_name id)⟩
  have hReplacementBoundary :
      Numbered.CodeBoundary replacementCode :=
    Numbered.quote_term_with?_code_boundary
      free_name [] hReplacementCode
  have hTargetBoundary : Numbered.CodeBoundary targetCode :=
    Numbered.quote?_code_boundary hTargetCode
  have hSourceCheck :
      Term.CheckCertificate sourceCode SetSort.set :=
    Term.check_admissible_complete hSourceBoundary.1
  have hBoundCheck :
      Term.CheckCertificate
        (Numbered.named_variable_code (free_name id)) SetSort.set :=
    Term.check_admissible_complete hBoundBoundary.1
  have hReplacementCheck :
      Term.CheckCertificate replacementCode SetSort.set :=
    Term.check_admissible_complete hReplacementBoundary.1
  have hTargetCheck :
      Term.CheckCertificate targetCode SetSort.set :=
    Term.check_admissible_complete hTargetBoundary.1
  have hFresh : ReservedIdsFresh [310, 311]
      [sourceCode,
        Numbered.named_variable_code (free_name id),
        replacementCode, targetCode] := by
    intro candidate hCandidate reserved hReserved
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hCandidate
    rcases hCandidate with
      rfl | rfl | rfl | rfl
    · rw [hSourceBoundary.2]
      intro hMember
      cases hMember
    · rw [hBoundBoundary.2]
      intro hMember
      cases hMember
    · rw [hReplacementBoundary.2]
      intro hMember
      cases hMember
    · rw [hTargetBoundary.2]
      intro hMember
      cases hMember
  have hPrecondition :=
    quote?_code_substitution_precondition_derives
      id hSourceCode hReplacementCode
  have hSpecification :=
    quote?_substitution_result_spec_derives
      id hSourceTokens hSourceCode
      hReplacementTokens hReplacementCode hTargetCode
  have hUnique :=
    gq_weaken_substitution_variable <|
      code_substitution_spec_implies_eq_term
        sourceCode (Numbered.named_variable_code (free_name id))
        replacementCode targetCode
        hSourceCheck hBoundCheck
        hReplacementCheck hTargetCheck hFresh
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hUnique hPrecondition)
    hSpecification
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
