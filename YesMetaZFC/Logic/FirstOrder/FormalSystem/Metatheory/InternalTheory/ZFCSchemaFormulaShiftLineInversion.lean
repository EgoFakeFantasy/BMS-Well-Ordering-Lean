import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaAtomicConstructorDisjointness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.VariableSymbolConstruction

/-!
# ZFC schema 公式 shift 行反演

本模块在 `fs_zfc_support_raw_theory` 内反演同步公式 shift 轨迹的一行。
公共辅助接口只消去正有限序列空间与动态规范 binder，不依赖标准 numeral 点值。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-!
后续反演会反复建立临时 eigenvariable 上下文。以下四个自由支撑组合子只陈述
语法构造器的精确支撑，不携带对象理论强度。
-/
private theorem fs_shift_unary_term_fresh
    (symbol : FunctionSymbol)
    (term : SetTerm)
    (freeVariable : FreeVariable signature)
    (hTerm :
      freeVariable ∉ Term.freeSupport term) :
    freeVariable ∉
      Term.freeSupport
        (Term.app symbol [term]) := by
  change freeVariable ∉
    Term.freeSupport term ++ []
  exact List.not_mem_append hTerm List.not_mem_nil

private theorem fs_shift_binary_term_fresh
    (symbol : FunctionSymbol)
    (left right : SetTerm)
    (freeVariable : FreeVariable signature)
    (hLeft :
      freeVariable ∉ Term.freeSupport left)
    (hRight :
      freeVariable ∉ Term.freeSupport right) :
    freeVariable ∉
      Term.freeSupport
        (Term.app symbol [left, right]) := by
  change freeVariable ∉
    Term.freeSupport left ++
      (Term.freeSupport right ++ [])
  exact List.not_mem_append hLeft <|
    List.not_mem_append hRight List.not_mem_nil

private theorem fs_shift_membership_fresh
    (left right : SetTerm)
    (freeVariable : FreeVariable signature)
    (hLeft :
      freeVariable ∉ Term.freeSupport left)
    (hRight :
      freeVariable ∉ Term.freeSupport right) :
    freeVariable ∉
      Formula.freeSupport (left ∈ₘ right) := by
  change freeVariable ∉
    Term.freeSupport left ++
      (Term.freeSupport right ++ [])
  exact List.not_mem_append hLeft <|
    List.not_mem_append hRight List.not_mem_nil

private theorem fs_shift_equality_fresh
    (left right : SetTerm)
    (freeVariable : FreeVariable signature)
    (hLeft :
      freeVariable ∉ Term.freeSupport left)
    (hRight :
      freeVariable ∉ Term.freeSupport right) :
    freeVariable ∉
      Formula.freeSupport (left ≐ₘ right) := by
  change freeVariable ∉
    Term.freeSupport left ++
      Term.freeSupport right
  exact List.not_mem_append hLeft hRight

private theorem fs_shift_conjunction_fresh
    (left right : SetFormula)
    (freeVariable : FreeVariable signature)
    (hLeft :
      freeVariable ∉ Formula.freeSupport left)
    (hRight :
      freeVariable ∉ Formula.freeSupport right) :
    freeVariable ∉
      Formula.freeSupport (left ∧ₘ right) := by
  change freeVariable ∉
    Formula.freeSupport left ++
      Formula.freeSupport right
  exact List.not_mem_append hLeft hRight

/--
正有限序列在任意已知定义域位置上的值属于目标集合。

目标非空是 `seq_spaceₘ` 定义合同所需的精确前提；本接口不额外要求序列下标为
标准 numeral。
-/
theorem fs_zfc_support_raw_positive_sequence_application_mem
    {Γ : Context signature}
    (target sequence index : SetTerm)
    (hTarget : Term.Admissible target SetSort.set)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hTargetNonempty :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        target ≠ₘ ∅ₘ)
    (hPositive :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ∈ₘ seq₊_spaceₘ(target))
    (hDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        index ∈ₘ domₘ(sequence)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (sequence ·ₘ index) ∈ₘ target := by
  have hPositiveToSpace :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (target ≠ₘ ∅ₘ) ⟶ₘ
          ((sequence ∈ₘ seq₊_spaceₘ(target)) ⟶ₘ
            (sequence ∈ₘ seq_spaceₘ(target))) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_standard_sequence_semantics
              hFormula) <|
          nonempty_sequence_space_member_implies_sequence_space
            target sequence hTarget hSequence
  have hSpace :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        sequence ∈ₘ seq_spaceₘ(target) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hPositiveToSpace hTargetNonempty)
      hPositive
  have hApplication :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (target ≠ₘ ∅ₘ) ⟶ₘ
          ((sequence ∈ₘ seq_spaceₘ(target)) ⟶ₘ
            ((index ∈ₘ domₘ(sequence)) ⟶ₘ
              ((sequence ·ₘ index) ∈ₘ target))) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_standard_sequence_semantics
              hFormula) <|
          sequence_space_member_application_mem
            target sequence index
            hTarget hSequence hIndex
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hApplication hTargetNonempty)
      hSpace)
    hDomain

private theorem
    fs_zfc_support_raw_infinity_subset_natural_multiplication
    {formula : SetFormula}
    (hFormula : infinity_theory formula) :
    natural_multiplication_theory formula :=
  natural_addition_theory_subset_natural_multiplication_theory <|
    natural_set_theory_subset_natural_addition_theory <|
      natural_order_type_theory_subset_natural_subset_type_theory <|
        bounded_subset_theory_subset_natural_order_type_theory <|
          unbounded_subset_theory_subset_bounded_subset_theory <|
            infinity_theory_subset_unbounded_subset_theory hFormula

private theorem
    fs_zfc_support_raw_contains_natural_multiplication
    {formula : SetFormula}
    (hFormula : natural_multiplication_theory formula) :
    fs_zfc_support_raw_theory formula :=
  fs_zfc_support_raw_contains_natural_addition_bound <|
    natural_exponentiation_bound_theory_subset_addition_bound_theory <|
      natural_exponentiation_theory_subset_bound_theory <|
        natural_multiplication_theory_subset_natural_exponentiation_theory
          hFormula

/-- 动态深度对应的规范 binder 名称仍属于对象自然数。 -/
theorem fs_zfc_support_raw_canonical_binder_name_mem_omega
    {Γ : Context signature}
    (depth : SetTerm)
    (hDepth : Term.Admissible depth SetSort.set)
    (hDepthMem :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        depth ∈ₘ ωₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_binder_name_term depth ∈ₘ ωₘ := by
  let product : SetTerm := numₘ(2) *ₘ depth
  let productMembership : SetFormula :=
    product ∈ₘ ωₘ
  have hProduct :
      Term.Admissible product SetSort.set :=
    natural_multiplication_term_admissible
      (numₘ(2)) depth
      (finite_numeral_term_admissible 2)
      hDepth
  have hMultiplicationImp :
      ⊢ₘ[natural_multiplication_theory]
        (depth ∈ₘ ωₘ) ⟶ₘ productMembership := by
    let membership : SetFormula := depth ∈ₘ ωₘ
    let Δ : Context signature := [membership]
    have hMembership :
        Formula.Admissible membership :=
      membership_formula_admissible
        hDepth omega_term_admissible
    nd_apply FirstOrder.Derives.impIntro
    have hDepthAt :
        Δ ⊢ₘ[natural_multiplication_theory]
          depth ∈ₘ ωₘ := by
      simpa [Δ, membership] using
        (FirstOrder.Derives.assumption
          (T := natural_multiplication_theory)
          (Γ := Δ) (φ := membership)
          (by simp [Δ]))
    have hTwoAt :
        Δ ⊢ₘ[natural_multiplication_theory]
          numₘ(2) ∈ₘ ωₘ :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ]) <|
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_infinity_subset_natural_multiplication
                hFormula)
            (infinity_finite_numeral_mem_omega 2)
    simpa [productMembership, product] using
      natural_multiplication_term_mem_omega
        (numₘ(2)) depth
        (finite_numeral_term_admissible 2)
        hDepth hTwoAt hDepthAt
  have hProductMem :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        product ∈ₘ ωₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_natural_multiplication
                hFormula)
            hMultiplicationImp)
      hDepthMem
  have hSuccessorImp :
      ⊢ₘ[infinity_theory]
        (product ∈ₘ ωₘ) ⟶ₘ
          (Sₘ(product) ∈ₘ ωₘ) := by
    let Δ : Context signature := [productMembership]
    have hProductMembership :
        Formula.Admissible productMembership :=
      membership_formula_admissible
        hProduct omega_term_admissible
    nd_apply FirstOrder.Derives.impIntro
    exact infinity_successor_term_mem_omega
      product hProduct <| by
        simpa [Δ, productMembership] using
          (FirstOrder.Derives.assumption
            (T := infinity_theory)
            (Γ := Δ) (φ := productMembership)
            (by simp [Δ]))
  have hNameMem :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Sₘ(product) ∈ₘ ωₘ :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_infinity
                hFormula)
            hSuccessorImp)
      hProductMem
  simpa [canonical_binder_name_term, product] using
    hNameMem

/-- 动态深度对应的规范 binder 编码属于变量符号集合。 -/
theorem fs_zfc_support_raw_canonical_binder_variable_mem
    {Γ : Context signature}
    (depth : SetTerm)
    (hDepth : Term.Admissible depth SetSort.set)
    (hDepthMem :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        depth ∈ₘ ωₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_binder_variable_code_term depth ∈ₘ
        VarSymₘ := by
  have hName :
      Term.Admissible
        (canonical_binder_name_term depth)
        SetSort.set :=
    successor_term_admissible
      (numₘ(2) *ₘ depth) <|
        natural_multiplication_term_admissible
          (numₘ(2)) depth
          (finite_numeral_term_admissible 2)
          hDepth
  have hNameMem :=
    fs_zfc_support_raw_canonical_binder_name_mem_omega
      depth hDepth hDepthMem
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation
              hFormula) <|
          GodelQuotation.gq_variable_code_mem_variable_symbols
            (canonical_binder_name_term depth)
            hName)
    hNameMem

/--
当前左码是规范原子码时，同步 shift 行的复合构造分支均不可成立。

结论保留动态入口深度 `depths ·ₘ index`，因而本层只负责构造标签排他；
入口深度的 numeral 化与原子 shift 唯一性留给下一层组合定理。
-/
theorem fs_zfc_support_raw_canonical_formula_shift_line_implies_atomic
    {Γ : Context signature}
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat)
    (cutoff leftCodes rightCodes depths index : SetTerm)
    (firstPremiseId secondPremiseId atomicBaseId : FreeVarId)
    (hCutoff : Term.Admissible cutoff SetSort.set)
    (hLeftCodes : Term.Admissible leftCodes SetSort.set)
    (hRightCodes : Term.Admissible rightCodes SetSort.set)
    (hDepths : Term.Admissible depths SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hPremiseIds : firstPremiseId ≠ secondPremiseId)
    (hPremiseFreshTerms :
      ReservedIdsFresh
        [firstPremiseId, secondPremiseId]
        [leftCodes, rightCodes, depths, index])
    (hPremiseFreshContext :
      ∀ id, id ∈ [firstPremiseId, secondPremiseId] →
        ∀ formula, formula ∈ Γ →
          (SetSort.set, id) ∉
            Formula.freeSupport formula)
    (hLeftPositive :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        leftCodes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ))
    (hDepthPositive :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        depths ∈ₘ seq₊_spaceₘ(ωₘ))
    (hLeftDepthDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        domₘ(leftCodes) ≐ₘ domₘ(depths))
    (hIndexDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        index ∈ₘ domₘ(leftCodes))
    (hSourceShape :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        CanonicalProjectTrace.canonical_project_atom_code
            kind leftDepth rightDepth ≐ₘ
          (leftCodes ·ₘ index))
    (hLine :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths index
          firstPremiseId secondPremiseId atomicBaseId) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      canonical_project_atomic_shift_condition_with_ids
        cutoff (depths ·ₘ index)
        (leftCodes ·ₘ index) (rightCodes ·ₘ index)
        atomicBaseId (atomicBaseId + 1)
        (atomicBaseId + 2) (atomicBaseId + 3)
        (atomicBaseId + 4) (atomicBaseId + 6) := by
  let currentLeft : SetTerm := leftCodes ·ₘ index
  let currentRight : SetTerm := rightCodes ·ₘ index
  let currentDepth : SetTerm := depths ·ₘ index
  let atomicBranch : SetFormula :=
    canonical_project_atomic_shift_condition_with_ids
      cutoff currentDepth currentLeft currentRight
      atomicBaseId (atomicBaseId + 1)
      (atomicBaseId + 2) (atomicBaseId + 3)
      (atomicBaseId + 4) (atomicBaseId + 6)
  let firstPremise : SetTerm := x#firstPremiseId
  let secondPremise : SetTerm := x#secondPremiseId
  let negationBody : SetFormula :=
    ((((firstPremise ∈ₘ index) ∧ₘ
          (firstPremise ∈ₘ domₘ(leftCodes))) ∧ₘ
        ((depths ·ₘ firstPremise) ≐ₘ currentDepth)) ∧ₘ
      ((currentLeft ≐ₘ
          neg_codeₘ(leftCodes ·ₘ firstPremise)) ∧ₘ
        (currentRight ≐ₘ
          neg_codeₘ(rightCodes ·ₘ firstPremise))))
  let negationBranch : SetFormula :=
    ∃ₘ[SetSort.set, firstPremiseId], negationBody
  let implicationBody : SetFormula :=
    (((((firstPremise ∈ₘ index) ∧ₘ
            (firstPremise ∈ₘ domₘ(leftCodes))) ∧ₘ
          ((secondPremise ∈ₘ index) ∧ₘ
            (secondPremise ∈ₘ domₘ(leftCodes)))) ∧ₘ
        (((depths ·ₘ firstPremise) ≐ₘ currentDepth) ∧ₘ
          ((depths ·ₘ secondPremise) ≐ₘ currentDepth))) ∧ₘ
      ((currentLeft ≐ₘ
          imp_codeₘ(
            leftCodes ·ₘ firstPremise,
            leftCodes ·ₘ secondPremise)) ∧ₘ
        (currentRight ≐ₘ
          imp_codeₘ(
            rightCodes ·ₘ firstPremise,
            rightCodes ·ₘ secondPremise))))
  let implicationOuterBody : SetFormula :=
    ∃ₘ[SetSort.set, secondPremiseId], implicationBody
  let implicationBranch : SetFormula :=
    ∃ₘ[SetSort.set, firstPremiseId],
      implicationOuterBody
  let universalBody : SetFormula :=
    ((((firstPremise ∈ₘ index) ∧ₘ
          (firstPremise ∈ₘ domₘ(leftCodes))) ∧ₘ
        ((depths ·ₘ firstPremise) ≐ₘ
          Sₘ(currentDepth))) ∧ₘ
      ((currentLeft ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term currentDepth,
            leftCodes ·ₘ firstPremise)) ∧ₘ
        (currentRight ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term
              (Sₘ(currentDepth)),
            rightCodes ·ₘ firstPremise))))
  let universalBranch : SetFormula :=
    ∃ₘ[SetSort.set, firstPremiseId], universalBody
  let compositeBranches : SetFormula :=
    negationBranch ∨ₘ
      (implicationBranch ∨ₘ universalBranch)
  have hCurrentLeft :
      Term.Admissible currentLeft SetSort.set :=
    function_application_term_admissible
      leftCodes index hLeftCodes hIndex
  have hCurrentRight :
      Term.Admissible currentRight SetSort.set :=
    function_application_term_admissible
      rightCodes index hRightCodes hIndex
  have hCurrentDepth :
      Term.Admissible currentDepth SetSort.set :=
    function_application_term_admissible
      depths index hDepths hIndex
  have hLineAdmissible :=
    canonical_project_formula_shift_line_condition_with_ids_admissible
      cutoff leftCodes rightCodes depths index
      firstPremiseId secondPremiseId atomicBaseId
      hCutoff hLeftCodes hRightCodes hDepths hIndex
  rw [canonical_project_formula_shift_line_condition_with_ids]
    at hLineAdmissible
  have hNegationBranchAdmissible :
      Formula.Admissible negationBranch := by
    simpa [negationBranch, negationBody,
      firstPremise, currentLeft, currentRight,
      currentDepth] using
      Formula.Admissible.disj_left <|
        Formula.Admissible.disj_right
          hLineAdmissible
  have hImplicationBranchAdmissible :
      Formula.Admissible implicationBranch := by
    simpa [implicationBranch, implicationOuterBody,
      implicationBody, firstPremise, secondPremise,
      currentLeft, currentRight, currentDepth] using
      Formula.Admissible.disj_left <|
        Formula.Admissible.disj_right <|
          Formula.Admissible.disj_right
            hLineAdmissible
  have hUniversalBranchAdmissible :
      Formula.Admissible universalBranch := by
    simpa [universalBranch, universalBody,
      firstPremise, currentLeft, currentRight,
      currentDepth] using
      Formula.Admissible.disj_right <|
        Formula.Admissible.disj_right <|
          Formula.Admissible.disj_right
            hLineAdmissible
  have hNegationBodyAdmissible :
      Formula.Admissible negationBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := firstPremise)
        SetSort.set hNegationBranchAdmissible
        (set_variable_admissible firstPremiseId)
    simpa [negationBranch, negationBody,
      firstPremise, Formula.openAt_closeFreeAt] using
      hOpened
  have hImplicationOuterBodyAdmissible :
      Formula.Admissible implicationOuterBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := firstPremise)
        SetSort.set hImplicationBranchAdmissible
        (set_variable_admissible firstPremiseId)
    simpa [implicationBranch, implicationOuterBody,
      firstPremise, Formula.openAt_closeFreeAt] using
      hOpened
  have hImplicationBodyAdmissible :
      Formula.Admissible implicationBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := secondPremise)
        SetSort.set hImplicationOuterBodyAdmissible
        (set_variable_admissible secondPremiseId)
    simpa [implicationOuterBody, implicationBody,
      secondPremise, Formula.openAt_closeFreeAt] using
      hOpened
  have hUniversalBodyAdmissible :
      Formula.Admissible universalBody := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (term := firstPremise)
        SetSort.set hUniversalBranchAdmissible
        (set_variable_admissible firstPremiseId)
    simpa [universalBranch, universalBody,
      firstPremise, Formula.openAt_closeFreeAt] using
      hOpened
  have hFirstFreshNegationBranch :
      (SetSort.set, firstPremiseId) ∉
        Formula.freeSupport negationBranch := by
    simpa [negationBranch, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set firstPremiseId 0 negationBody
  have hFirstFreshImplicationBranch :
      (SetSort.set, firstPremiseId) ∉
        Formula.freeSupport implicationBranch := by
    simpa [implicationBranch, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set firstPremiseId 0 implicationOuterBody
  have hFirstFreshUniversalBranch :
      (SetSort.set, firstPremiseId) ∉
        Formula.freeSupport universalBranch := by
    simpa [universalBranch, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set firstPremiseId 0 universalBody
  have hFirstFreshComposite :
      (SetSort.set, firstPremiseId) ∉
        Formula.freeSupport compositeBranches := by
    change (SetSort.set, firstPremiseId) ∉
      Formula.freeSupport negationBranch ++
        (Formula.freeSupport implicationBranch ++
          Formula.freeSupport universalBranch)
    exact List.not_mem_append hFirstFreshNegationBranch <|
      List.not_mem_append hFirstFreshImplicationBranch
        hFirstFreshUniversalBranch
  have hFirstFreshRemaining :
      (SetSort.set, firstPremiseId) ∉
        Formula.freeSupport
          (implicationBranch ∨ₘ universalBranch) := by
    change (SetSort.set, firstPremiseId) ∉
      Formula.freeSupport implicationBranch ++
        Formula.freeSupport universalBranch
    exact List.not_mem_append hFirstFreshImplicationBranch
      hFirstFreshUniversalBranch
  have hSecondFreshLeftCodes :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport leftCodes :=
    hPremiseFreshTerms leftCodes (by simp)
      secondPremiseId (by simp)
  have hSecondFreshRightCodes :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport rightCodes :=
    hPremiseFreshTerms rightCodes (by simp)
      secondPremiseId (by simp)
  have hSecondFreshDepths :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport depths :=
    hPremiseFreshTerms depths (by simp)
      secondPremiseId (by simp)
  have hSecondFreshIndex :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport index :=
    hPremiseFreshTerms index (by simp)
      secondPremiseId (by simp)
  have hSecondFreshFirstPremise :
      (SetSort.set, secondPremiseId) ∉
        Term.freeSupport firstPremise := by
    intro hMember
    change (SetSort.set, secondPremiseId) ∈
      [(SetSort.set, firstPremiseId)] at hMember
    exact hPremiseIds <|
      (congrArg Prod.snd
        (List.mem_singleton.mp hMember)).symm
  have hSecondFreshNegationBody :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport negationBody := by
    have hDomain :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport (domₘ(leftCodes)) := by
      simpa [domain_term] using
        fs_shift_unary_term_fresh
          .domain leftCodes
          (SetSort.set, secondPremiseId)
          hSecondFreshLeftCodes
    have hCurrentLeftFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport currentLeft := by
      simpa [currentLeft, function_application_term] using
        fs_shift_binary_term_fresh
          .application leftCodes index
          (SetSort.set, secondPremiseId)
          hSecondFreshLeftCodes hSecondFreshIndex
    have hCurrentRightFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport currentRight := by
      simpa [currentRight, function_application_term] using
        fs_shift_binary_term_fresh
          .application rightCodes index
          (SetSort.set, secondPremiseId)
          hSecondFreshRightCodes hSecondFreshIndex
    have hCurrentDepthFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport currentDepth := by
      simpa [currentDepth, function_application_term] using
        fs_shift_binary_term_fresh
          .application depths index
          (SetSort.set, secondPremiseId)
          hSecondFreshDepths hSecondFreshIndex
    have hLeftPremiseFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (leftCodes ·ₘ firstPremise) := by
      simpa [function_application_term] using
        fs_shift_binary_term_fresh
          .application leftCodes firstPremise
          (SetSort.set, secondPremiseId)
          hSecondFreshLeftCodes hSecondFreshFirstPremise
    have hRightPremiseFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (rightCodes ·ₘ firstPremise) := by
      simpa [function_application_term] using
        fs_shift_binary_term_fresh
          .application rightCodes firstPremise
          (SetSort.set, secondPremiseId)
          hSecondFreshRightCodes hSecondFreshFirstPremise
    have hDepthPremiseFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (depths ·ₘ firstPremise) := by
      simpa [function_application_term] using
        fs_shift_binary_term_fresh
          .application depths firstPremise
          (SetSort.set, secondPremiseId)
          hSecondFreshDepths hSecondFreshFirstPremise
    have hNegLeftFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (neg_codeₘ(leftCodes ·ₘ firstPremise)) := by
      simpa [negation_formula_code_term] using
        fs_shift_unary_term_fresh
          .negationFormulaCode
          (leftCodes ·ₘ firstPremise)
          (SetSort.set, secondPremiseId)
          hLeftPremiseFresh
    have hNegRightFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (neg_codeₘ(rightCodes ·ₘ firstPremise)) := by
      simpa [negation_formula_code_term] using
        fs_shift_unary_term_fresh
          .negationFormulaCode
          (rightCodes ·ₘ firstPremise)
          (SetSort.set, secondPremiseId)
          hRightPremiseFresh
    simpa [negationBody] using
      fs_shift_conjunction_fresh
        (((firstPremise ∈ₘ index) ∧ₘ
            (firstPremise ∈ₘ domₘ(leftCodes))) ∧ₘ
          ((depths ·ₘ firstPremise) ≐ₘ currentDepth))
        ((currentLeft ≐ₘ
            neg_codeₘ(leftCodes ·ₘ firstPremise)) ∧ₘ
          (currentRight ≐ₘ
            neg_codeₘ(rightCodes ·ₘ firstPremise)))
        (SetSort.set, secondPremiseId)
        (fs_shift_conjunction_fresh
          ((firstPremise ∈ₘ index) ∧ₘ
            (firstPremise ∈ₘ domₘ(leftCodes)))
          ((depths ·ₘ firstPremise) ≐ₘ currentDepth)
          (SetSort.set, secondPremiseId)
          (fs_shift_conjunction_fresh
            (firstPremise ∈ₘ index)
            (firstPremise ∈ₘ domₘ(leftCodes))
            (SetSort.set, secondPremiseId)
            (fs_shift_membership_fresh
              firstPremise index
              (SetSort.set, secondPremiseId)
              hSecondFreshFirstPremise
              hSecondFreshIndex)
            (fs_shift_membership_fresh
              firstPremise (domₘ(leftCodes))
              (SetSort.set, secondPremiseId)
              hSecondFreshFirstPremise hDomain))
          (fs_shift_equality_fresh
            (depths ·ₘ firstPremise) currentDepth
            (SetSort.set, secondPremiseId)
            hDepthPremiseFresh hCurrentDepthFresh))
        (fs_shift_conjunction_fresh
          (currentLeft ≐ₘ
            neg_codeₘ(leftCodes ·ₘ firstPremise))
          (currentRight ≐ₘ
            neg_codeₘ(rightCodes ·ₘ firstPremise))
          (SetSort.set, secondPremiseId)
          (fs_shift_equality_fresh
            currentLeft
            (neg_codeₘ(leftCodes ·ₘ firstPremise))
            (SetSort.set, secondPremiseId)
            hCurrentLeftFresh hNegLeftFresh)
          (fs_shift_equality_fresh
            currentRight
            (neg_codeₘ(rightCodes ·ₘ firstPremise))
            (SetSort.set, secondPremiseId)
            hCurrentRightFresh hNegRightFresh))
  have hSecondFreshUniversalBody :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport universalBody := by
    have hTwoFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport (numₘ(2)) := by
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil
    have hCurrentLeftFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport currentLeft := by
      simpa [currentLeft, function_application_term] using
        fs_shift_binary_term_fresh
          .application leftCodes index
          (SetSort.set, secondPremiseId)
          hSecondFreshLeftCodes hSecondFreshIndex
    have hCurrentRightFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport currentRight := by
      simpa [currentRight, function_application_term] using
        fs_shift_binary_term_fresh
          .application rightCodes index
          (SetSort.set, secondPremiseId)
          hSecondFreshRightCodes hSecondFreshIndex
    have hCurrentDepthFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport currentDepth := by
      simpa [currentDepth, function_application_term] using
        fs_shift_binary_term_fresh
          .application depths index
          (SetSort.set, secondPremiseId)
          hSecondFreshDepths hSecondFreshIndex
    have hSuccessorDepthFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport (Sₘ(currentDepth)) := by
      simpa [successor_term] using
        fs_shift_unary_term_fresh
          .successor currentDepth
          (SetSort.set, secondPremiseId)
          hCurrentDepthFresh
    have hLeftPremiseFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (leftCodes ·ₘ firstPremise) := by
      simpa [function_application_term] using
        fs_shift_binary_term_fresh
          .application leftCodes firstPremise
          (SetSort.set, secondPremiseId)
          hSecondFreshLeftCodes hSecondFreshFirstPremise
    have hRightPremiseFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (rightCodes ·ₘ firstPremise) := by
      simpa [function_application_term] using
        fs_shift_binary_term_fresh
          .application rightCodes firstPremise
          (SetSort.set, secondPremiseId)
          hSecondFreshRightCodes hSecondFreshFirstPremise
    have hDepthPremiseFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (depths ·ₘ firstPremise) := by
      simpa [function_application_term] using
        fs_shift_binary_term_fresh
          .application depths firstPremise
          (SetSort.set, secondPremiseId)
          hSecondFreshDepths hSecondFreshFirstPremise
    have hBinderFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (canonical_binder_variable_code_term
              currentDepth) := by
      have hTwice :
          (SetSort.set, secondPremiseId) ∉
            Term.freeSupport
              (numₘ(2) *ₘ currentDepth) := by
        simpa [natural_multiplication_term] using
          fs_shift_binary_term_fresh
            .naturalMultiplication (numₘ(2)) currentDepth
            (SetSort.set, secondPremiseId)
            hTwoFresh hCurrentDepthFresh
      have hName :
          (SetSort.set, secondPremiseId) ∉
            Term.freeSupport
              (canonical_binder_name_term
                currentDepth) := by
        simpa [canonical_binder_name_term,
          successor_term] using
          fs_shift_unary_term_fresh
            .successor (numₘ(2) *ₘ currentDepth)
            (SetSort.set, secondPremiseId)
            hTwice
      simpa [canonical_binder_variable_code_term,
        variable_code_term] using
        fs_shift_unary_term_fresh
          .variableCode
          (canonical_binder_name_term currentDepth)
          (SetSort.set, secondPremiseId)
          hName
    have hSuccessorBinderFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (canonical_binder_variable_code_term
              Sₘ(currentDepth)) := by
      have hTwice :
          (SetSort.set, secondPremiseId) ∉
            Term.freeSupport
              (numₘ(2) *ₘ Sₘ(currentDepth)) := by
        simpa [natural_multiplication_term] using
          fs_shift_binary_term_fresh
            .naturalMultiplication
            (numₘ(2)) (Sₘ(currentDepth))
            (SetSort.set, secondPremiseId)
            hTwoFresh hSuccessorDepthFresh
      have hName :
          (SetSort.set, secondPremiseId) ∉
            Term.freeSupport
              (canonical_binder_name_term
                Sₘ(currentDepth)) := by
        simpa [canonical_binder_name_term,
          successor_term] using
          fs_shift_unary_term_fresh
            .successor
            (numₘ(2) *ₘ Sₘ(currentDepth))
            (SetSort.set, secondPremiseId)
            hTwice
      simpa [canonical_binder_variable_code_term,
        variable_code_term] using
        fs_shift_unary_term_fresh
          .variableCode
          (canonical_binder_name_term
            Sₘ(currentDepth))
          (SetSort.set, secondPremiseId)
          hName
    have hLeftUniversalFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (forall_codeₘ(
              canonical_binder_variable_code_term
                currentDepth,
              leftCodes ·ₘ firstPremise)) := by
      simpa [universal_formula_code_term] using
        fs_shift_binary_term_fresh
          .universalFormulaCode
          (canonical_binder_variable_code_term
            currentDepth)
          (leftCodes ·ₘ firstPremise)
          (SetSort.set, secondPremiseId)
          hBinderFresh hLeftPremiseFresh
    have hRightUniversalFresh :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport
            (forall_codeₘ(
              canonical_binder_variable_code_term
                Sₘ(currentDepth),
              rightCodes ·ₘ firstPremise)) := by
      simpa [universal_formula_code_term] using
        fs_shift_binary_term_fresh
          .universalFormulaCode
          (canonical_binder_variable_code_term
            Sₘ(currentDepth))
          (rightCodes ·ₘ firstPremise)
          (SetSort.set, secondPremiseId)
          hSuccessorBinderFresh hRightPremiseFresh
    have hDomain :
        (SetSort.set, secondPremiseId) ∉
          Term.freeSupport (domₘ(leftCodes)) := by
      simpa [domain_term] using
        fs_shift_unary_term_fresh
          .domain leftCodes
          (SetSort.set, secondPremiseId)
          hSecondFreshLeftCodes
    simpa [universalBody] using
      fs_shift_conjunction_fresh
        (((firstPremise ∈ₘ index) ∧ₘ
            (firstPremise ∈ₘ domₘ(leftCodes))) ∧ₘ
          ((depths ·ₘ firstPremise) ≐ₘ
            Sₘ(currentDepth)))
        ((currentLeft ≐ₘ
            forall_codeₘ(
              canonical_binder_variable_code_term
                currentDepth,
              leftCodes ·ₘ firstPremise)) ∧ₘ
          (currentRight ≐ₘ
            forall_codeₘ(
              canonical_binder_variable_code_term
                Sₘ(currentDepth),
              rightCodes ·ₘ firstPremise)))
        (SetSort.set, secondPremiseId)
        (fs_shift_conjunction_fresh
          ((firstPremise ∈ₘ index) ∧ₘ
            (firstPremise ∈ₘ domₘ(leftCodes)))
          ((depths ·ₘ firstPremise) ≐ₘ
            Sₘ(currentDepth))
          (SetSort.set, secondPremiseId)
          (fs_shift_conjunction_fresh
            (firstPremise ∈ₘ index)
            (firstPremise ∈ₘ domₘ(leftCodes))
            (SetSort.set, secondPremiseId)
            (fs_shift_membership_fresh
              firstPremise index
              (SetSort.set, secondPremiseId)
              hSecondFreshFirstPremise
              hSecondFreshIndex)
            (fs_shift_membership_fresh
              firstPremise (domₘ(leftCodes))
              (SetSort.set, secondPremiseId)
              hSecondFreshFirstPremise hDomain))
          (fs_shift_equality_fresh
            (depths ·ₘ firstPremise)
            (Sₘ(currentDepth))
            (SetSort.set, secondPremiseId)
            hDepthPremiseFresh hSuccessorDepthFresh))
        (fs_shift_conjunction_fresh
          (currentLeft ≐ₘ
            forall_codeₘ(
              canonical_binder_variable_code_term
                currentDepth,
              leftCodes ·ₘ firstPremise))
          (currentRight ≐ₘ
            forall_codeₘ(
              canonical_binder_variable_code_term
                Sₘ(currentDepth),
              rightCodes ·ₘ firstPremise))
          (SetSort.set, secondPremiseId)
          (fs_shift_equality_fresh
            currentLeft
            (forall_codeₘ(
              canonical_binder_variable_code_term
                currentDepth,
              leftCodes ·ₘ firstPremise))
            (SetSort.set, secondPremiseId)
            hCurrentLeftFresh hLeftUniversalFresh)
          (fs_shift_equality_fresh
            currentRight
            (forall_codeₘ(
              canonical_binder_variable_code_term
                Sₘ(currentDepth),
              rightCodes ·ₘ firstPremise))
            (SetSort.set, secondPremiseId)
            hCurrentRightFresh hRightUniversalFresh))
  have hSecondFreshNegationBranch :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport negationBranch := by
    simpa [negationBranch, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, secondPremiseId)
        SetSort.set firstPremiseId 0
        negationBody hSecondFreshNegationBody
  have hSecondFreshImplicationOuterBody :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport implicationOuterBody := by
    simpa [implicationOuterBody, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set secondPremiseId 0 implicationBody
  have hSecondFreshImplicationBranch :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport implicationBranch := by
    simpa [implicationBranch, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, secondPremiseId)
        SetSort.set firstPremiseId 0
        implicationOuterBody
        hSecondFreshImplicationOuterBody
  have hSecondFreshUniversalBranch :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport universalBranch := by
    simpa [universalBranch, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (SetSort.set, secondPremiseId)
        SetSort.set firstPremiseId 0
        universalBody hSecondFreshUniversalBody
  have hSecondFreshComposite :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport compositeBranches := by
    change (SetSort.set, secondPremiseId) ∉
      Formula.freeSupport negationBranch ++
        (Formula.freeSupport implicationBranch ++
          Formula.freeSupport universalBranch)
    exact List.not_mem_append hSecondFreshNegationBranch <|
      List.not_mem_append hSecondFreshImplicationBranch
        hSecondFreshUniversalBranch
  have hSecondFreshRemaining :
      (SetSort.set, secondPremiseId) ∉
        Formula.freeSupport
          (implicationBranch ∨ₘ universalBranch) := by
    change (SetSort.set, secondPremiseId) ∉
      Formula.freeSupport implicationBranch ++
        Formula.freeSupport universalBranch
    exact List.not_mem_append hSecondFreshImplicationBranch
      hSecondFreshUniversalBranch
  have hFormulaCodeNonempty :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        FormulaCodeₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_godel_quotation
          GodelQuotation.formula_code_set_nonempty_derives
  have hOmegaNonempty :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ωₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        fs_zfc_support_raw_derives_of_standard_sequence
          GodelQuotation.standard_sequence_omega_ne_empty
  have hIndexDepthDomain :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        index ∈ₘ domₘ(depths) :=
    FirstOrder.Derives.iffElimRight
      (membership_right_iff_of_equality
        index (domₘ(leftCodes)) (domₘ(depths))
        hIndex
        (domain_term_admissible leftCodes hLeftCodes)
        (domain_term_admissible depths hDepths)
        hLeftDepthDomain)
      hIndexDomain
  have hCurrentDepthMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        currentDepth ∈ₘ ωₘ := by
    simpa [currentDepth] using
      fs_zfc_support_raw_positive_sequence_application_mem
        ωₘ depths index omega_term_admissible
        hDepths hIndex hOmegaNonempty
        hDepthPositive hIndexDepthDomain
  have hBinderMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_binder_variable_code_term
            currentDepth ∈ₘ VarSymₘ :=
    fs_zfc_support_raw_canonical_binder_variable_mem
      currentDepth hCurrentDepth hCurrentDepthMember
  have hCases :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        atomicBranch ∨ₘ compositeBranches := by
    simpa [atomicBranch, compositeBranches,
      negationBranch, implicationBranch,
      implicationOuterBody, universalBranch,
      negationBody, implicationBody, universalBody,
      firstPremise, secondPremise,
      currentLeft, currentRight, currentDepth,
      canonical_project_formula_shift_line_condition_with_ids] using
      hLine
  apply FirstOrder.Derives.disjElim hCases
  · simpa [atomicBranch] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := atomicBranch :: Γ)
        (φ := atomicBranch) (by simp))
  · let Δ : Context signature :=
      compositeBranches :: Γ
    have hComposite :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          compositeBranches :=
      FirstOrder.Derives.assumption (by simp [Δ])
    exact FirstOrder.Derives.falsumElim
      (φ := atomicBranch) <|
        FirstOrder.Derives.disjElim hComposite
          (by
            let Ε : Context signature :=
              negationBranch :: Δ
            have hNegationExists :
                Ε ⊢ₘ[fs_zfc_support_raw_theory]
                  negationBranch :=
              FirstOrder.Derives.assumption
                (by simp [Ε])
            nd_apply FirstOrder.Derives.exists_elim
              (T := fs_zfc_support_raw_theory)
              (Γ := Ε)
              (sort := SetSort.set)
              (eigen := firstPremiseId)
              (body := negationBody)
              (conclusion := Formula.falsum)
              (hBodyCheck :=
                Formula.check_admissible_complete
                  hNegationBodyAdmissible)
            · intro formula hFormula
              rw [(fs_zfc_support_raw_theory_sentence
                hFormula).2]
              exact List.not_mem_nil
            · intro formula hFormula
              simp only [Ε, Δ, List.mem_cons] at hFormula
              rcases hFormula with rfl | rfl | hFormula
              · exact hFirstFreshNegationBranch
              · exact hFirstFreshComposite
              · exact
                  hPremiseFreshContext
                    firstPremiseId (by simp)
                    formula hFormula
            · simp [Formula.freeSupport]
            · simpa [negationBranch] using
                hNegationExists
            · let Ζ : Context signature :=
                negationBody :: Ε
              have hBody :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    negationBody :=
                FirstOrder.Derives.assumption
                  (by simp [Ζ])
                  (Formula.check_admissible_complete
                    hNegationBodyAdmissible)
              have hFormulaCodeNonemptyAt :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    FormulaCodeₘ ≠ₘ ∅ₘ :=
                FirstOrder.Derives.context_weaken_cons <|
                  FirstOrder.Derives.context_weaken_cons <|
                    FirstOrder.Derives.context_weaken_cons
                      hFormulaCodeNonempty
              have hLeftPositiveAt :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    leftCodes ∈ₘ
                      seq₊_spaceₘ(FormulaCodeₘ) :=
                FirstOrder.Derives.context_weaken_cons <|
                  FirstOrder.Derives.context_weaken_cons <|
                    FirstOrder.Derives.context_weaken_cons
                      hLeftPositive
              have hSourceShapeAt :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    CanonicalProjectTrace.canonical_project_atom_code
                        kind leftDepth rightDepth ≐ₘ
                      currentLeft := by
                exact FirstOrder.Derives.context_weaken_cons <|
                  FirstOrder.Derives.context_weaken_cons <|
                    FirstOrder.Derives.context_weaken_cons <| by
                      simpa [currentLeft] using hSourceShape
              have hPremiseDomain :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    firstPremise ∈ₘ
                      domₘ(leftCodes) := by
                simpa [negationBody] using
                  FirstOrder.Derives.conjElimRight <|
                    FirstOrder.Derives.conjElimLeft <|
                      FirstOrder.Derives.conjElimLeft
                        hBody
              have hPremiseMember :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    (leftCodes ·ₘ firstPremise) ∈ₘ
                      FormulaCodeₘ :=
                fs_zfc_support_raw_positive_sequence_application_mem
                  FormulaCodeₘ leftCodes firstPremise
                  formula_code_set_term_admissible
                  hLeftCodes
                  (set_variable_admissible firstPremiseId)
                  hFormulaCodeNonemptyAt
                  hLeftPositiveAt
                  hPremiseDomain
              have hLeftShape :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    currentLeft ≐ₘ
                      neg_codeₘ(
                        leftCodes ·ₘ firstPremise) := by
                simpa [negationBody] using
                  FirstOrder.Derives.conjElimLeft <|
                    FirstOrder.Derives.conjElimRight
                      hBody
              have hShape :
                  Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                    CanonicalProjectTrace.canonical_project_atom_code
                        kind leftDepth rightDepth ≐ₘ
                      neg_codeₘ(
                        leftCodes ·ₘ firstPremise) :=
                Metatheory.Derives.equality_trans
                  hSourceShapeAt
                  hLeftShape
              exact
                fs_zfc_support_raw_canonical_atom_ne_negation_branch
                  kind leftDepth rightDepth
                  (leftCodes ·ₘ firstPremise)
                  (function_application_term_admissible
                    leftCodes firstPremise hLeftCodes
                    (set_variable_admissible firstPremiseId))
                  hPremiseMember hShape)
          (by
            let Ε : Context signature :=
              (implicationBranch ∨ₘ universalBranch) :: Δ
            have hRemaining :
                Ε ⊢ₘ[fs_zfc_support_raw_theory]
                  implicationBranch ∨ₘ universalBranch :=
              FirstOrder.Derives.assumption (by simp [Ε])
            exact FirstOrder.Derives.disjElim hRemaining
              (by
                let Ζ : Context signature :=
                  implicationBranch :: Ε
                have hFirstExists :
                    Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                      implicationBranch :=
                  FirstOrder.Derives.assumption
                    (by simp [Ζ])
                nd_apply FirstOrder.Derives.exists_elim
                  (T := fs_zfc_support_raw_theory)
                  (Γ := Ζ)
                  (sort := SetSort.set)
                  (eigen := firstPremiseId)
                  (body := implicationOuterBody)
                  (conclusion := Formula.falsum)
                  (hBodyCheck :=
                    Formula.check_admissible_complete
                      hImplicationOuterBodyAdmissible)
                · intro formula hFormula
                  rw [(fs_zfc_support_raw_theory_sentence
                    hFormula).2]
                  exact List.not_mem_nil
                · intro formula hFormula
                  simp only [Ζ, Ε, Δ, List.mem_cons]
                    at hFormula
                  rcases hFormula with
                    rfl | rfl | rfl | hFormula
                  · exact hFirstFreshImplicationBranch
                  · exact hFirstFreshRemaining
                  · exact hFirstFreshComposite
                  · exact
                      hPremiseFreshContext
                        firstPremiseId (by simp)
                        formula hFormula
                · simp [Formula.freeSupport]
                · simpa [implicationBranch] using
                    hFirstExists
                · let Η : Context signature :=
                    implicationOuterBody :: Ζ
                  have hSecondExists :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        implicationOuterBody :=
                    FirstOrder.Derives.assumption
                      (by simp [Η])
                      (Formula.check_admissible_complete
                        hImplicationOuterBodyAdmissible)
                  nd_apply FirstOrder.Derives.exists_elim
                    (T := fs_zfc_support_raw_theory)
                    (Γ := Η)
                    (sort := SetSort.set)
                    (eigen := secondPremiseId)
                    (body := implicationBody)
                    (conclusion := Formula.falsum)
                    (hBodyCheck :=
                      Formula.check_admissible_complete
                        hImplicationBodyAdmissible)
                  · intro formula hFormula
                    rw [(fs_zfc_support_raw_theory_sentence
                      hFormula).2]
                    exact List.not_mem_nil
                  · intro formula hFormula
                    simp only [Η, Ζ, Ε, Δ,
                      List.mem_cons] at hFormula
                    rcases hFormula with
                      rfl | rfl | rfl | rfl | hFormula
                    · exact hSecondFreshImplicationOuterBody
                    · exact hSecondFreshImplicationBranch
                    · exact hSecondFreshRemaining
                    · exact hSecondFreshComposite
                    · exact
                        hPremiseFreshContext
                          secondPremiseId (by simp)
                          formula hFormula
                  · simp [Formula.freeSupport]
                  · simpa [implicationOuterBody] using
                      hSecondExists
                  · let Θ : Context signature :=
                      implicationBody :: Η
                    have hBody :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          implicationBody :=
                      FirstOrder.Derives.assumption
                        (by simp [Θ])
                        (Formula.check_admissible_complete
                          hImplicationBodyAdmissible)
                    have hFormulaCodeNonemptyAt :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          FormulaCodeₘ ≠ₘ ∅ₘ :=
                      FirstOrder.Derives.context_weaken_cons <|
                        FirstOrder.Derives.context_weaken_cons <|
                          FirstOrder.Derives.context_weaken_cons <|
                            FirstOrder.Derives.context_weaken_cons <|
                              FirstOrder.Derives.context_weaken_cons
                                hFormulaCodeNonempty
                    have hLeftPositiveAt :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          leftCodes ∈ₘ
                            seq₊_spaceₘ(FormulaCodeₘ) :=
                      FirstOrder.Derives.context_weaken_cons <|
                        FirstOrder.Derives.context_weaken_cons <|
                          FirstOrder.Derives.context_weaken_cons <|
                            FirstOrder.Derives.context_weaken_cons <|
                              FirstOrder.Derives.context_weaken_cons
                                hLeftPositive
                    have hSourceShapeAt :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          CanonicalProjectTrace.canonical_project_atom_code
                              kind leftDepth rightDepth ≐ₘ
                            currentLeft := by
                      exact FirstOrder.Derives.context_weaken_cons <|
                        FirstOrder.Derives.context_weaken_cons <|
                          FirstOrder.Derives.context_weaken_cons <|
                            FirstOrder.Derives.context_weaken_cons <|
                              FirstOrder.Derives.context_weaken_cons <| by
                                simpa [currentLeft] using hSourceShape
                    have hPremiseData :=
                      FirstOrder.Derives.conjElimLeft <|
                        FirstOrder.Derives.conjElimLeft
                          hBody
                    have hFirstDomain :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          firstPremise ∈ₘ
                            domₘ(leftCodes) := by
                      simpa [implicationBody] using
                        FirstOrder.Derives.conjElimRight <|
                          FirstOrder.Derives.conjElimLeft
                            hPremiseData
                    have hSecondDomain :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          secondPremise ∈ₘ
                            domₘ(leftCodes) := by
                      simpa [implicationBody] using
                        FirstOrder.Derives.conjElimRight <|
                          FirstOrder.Derives.conjElimRight
                            hPremiseData
                    have hFirstMember :=
                      fs_zfc_support_raw_positive_sequence_application_mem
                        FormulaCodeₘ leftCodes firstPremise
                        formula_code_set_term_admissible
                        hLeftCodes
                        (set_variable_admissible
                          firstPremiseId)
                        hFormulaCodeNonemptyAt
                        hLeftPositiveAt
                        hFirstDomain
                    have hSecondMember :=
                      fs_zfc_support_raw_positive_sequence_application_mem
                        FormulaCodeₘ leftCodes secondPremise
                        formula_code_set_term_admissible
                        hLeftCodes
                        (set_variable_admissible
                          secondPremiseId)
                        hFormulaCodeNonemptyAt
                        hLeftPositiveAt
                        hSecondDomain
                    have hLeftShape :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          currentLeft ≐ₘ
                            imp_codeₘ(
                              leftCodes ·ₘ firstPremise,
                              leftCodes ·ₘ secondPremise) := by
                      simpa [implicationBody] using
                        FirstOrder.Derives.conjElimLeft <|
                          FirstOrder.Derives.conjElimRight
                            hBody
                    have hShape :
                        Θ ⊢ₘ[fs_zfc_support_raw_theory]
                          CanonicalProjectTrace.canonical_project_atom_code
                              kind leftDepth rightDepth ≐ₘ
                            imp_codeₘ(
                              leftCodes ·ₘ firstPremise,
                              leftCodes ·ₘ secondPremise) :=
                      Metatheory.Derives.equality_trans
                        hSourceShapeAt
                        hLeftShape
                    exact
                      fs_zfc_support_raw_canonical_atom_ne_implication_branch
                        kind leftDepth rightDepth
                        (leftCodes ·ₘ firstPremise)
                        (leftCodes ·ₘ secondPremise)
                        (function_application_term_admissible
                          leftCodes firstPremise hLeftCodes
                          (set_variable_admissible
                            firstPremiseId))
                        (function_application_term_admissible
                          leftCodes secondPremise hLeftCodes
                          (set_variable_admissible
                            secondPremiseId))
                        hFirstMember hSecondMember hShape)
              (by
                let Ζ : Context signature :=
                  universalBranch :: Ε
                have hUniversalExists :
                    Ζ ⊢ₘ[fs_zfc_support_raw_theory]
                      universalBranch :=
                  FirstOrder.Derives.assumption
                    (by simp [Ζ])
                nd_apply FirstOrder.Derives.exists_elim
                  (T := fs_zfc_support_raw_theory)
                  (Γ := Ζ)
                  (sort := SetSort.set)
                  (eigen := firstPremiseId)
                  (body := universalBody)
                  (conclusion := Formula.falsum)
                  (hBodyCheck :=
                    Formula.check_admissible_complete
                      hUniversalBodyAdmissible)
                · intro formula hFormula
                  rw [(fs_zfc_support_raw_theory_sentence
                    hFormula).2]
                  exact List.not_mem_nil
                · intro formula hFormula
                  simp only [Ζ, Ε, Δ, List.mem_cons]
                    at hFormula
                  rcases hFormula with
                    rfl | rfl | rfl | hFormula
                  · exact hFirstFreshUniversalBranch
                  · exact hFirstFreshRemaining
                  · exact hFirstFreshComposite
                  · exact
                      hPremiseFreshContext
                        firstPremiseId (by simp)
                        formula hFormula
                · simp [Formula.freeSupport]
                · simpa [universalBranch] using
                    hUniversalExists
                · let Η : Context signature :=
                    universalBody :: Ζ
                  have hBody :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        universalBody :=
                    FirstOrder.Derives.assumption
                      (by simp [Η])
                      (Formula.check_admissible_complete
                        hUniversalBodyAdmissible)
                  have hFormulaCodeNonemptyAt :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        FormulaCodeₘ ≠ₘ ∅ₘ :=
                    FirstOrder.Derives.context_weaken_cons <|
                      FirstOrder.Derives.context_weaken_cons <|
                        FirstOrder.Derives.context_weaken_cons <|
                          FirstOrder.Derives.context_weaken_cons
                            hFormulaCodeNonempty
                  have hLeftPositiveAt :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        leftCodes ∈ₘ
                          seq₊_spaceₘ(FormulaCodeₘ) :=
                    FirstOrder.Derives.context_weaken_cons <|
                      FirstOrder.Derives.context_weaken_cons <|
                        FirstOrder.Derives.context_weaken_cons <|
                          FirstOrder.Derives.context_weaken_cons
                            hLeftPositive
                  have hSourceShapeAt :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        CanonicalProjectTrace.canonical_project_atom_code
                            kind leftDepth rightDepth ≐ₘ
                          currentLeft := by
                    exact FirstOrder.Derives.context_weaken_cons <|
                      FirstOrder.Derives.context_weaken_cons <|
                        FirstOrder.Derives.context_weaken_cons <|
                          FirstOrder.Derives.context_weaken_cons <| by
                            simpa [currentLeft] using hSourceShape
                  have hBinderMemberAt :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        canonical_binder_variable_code_term
                            currentDepth ∈ₘ VarSymₘ :=
                    FirstOrder.Derives.context_weaken_cons <|
                      FirstOrder.Derives.context_weaken_cons <|
                        FirstOrder.Derives.context_weaken_cons <|
                          FirstOrder.Derives.context_weaken_cons
                            hBinderMember
                  have hPremiseDomain :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        firstPremise ∈ₘ
                          domₘ(leftCodes) := by
                    simpa [universalBody] using
                      FirstOrder.Derives.conjElimRight <|
                        FirstOrder.Derives.conjElimLeft <|
                          FirstOrder.Derives.conjElimLeft
                            hBody
                  have hPremiseMember :=
                    fs_zfc_support_raw_positive_sequence_application_mem
                      FormulaCodeₘ leftCodes firstPremise
                      formula_code_set_term_admissible
                      hLeftCodes
                      (set_variable_admissible firstPremiseId)
                      hFormulaCodeNonemptyAt
                      hLeftPositiveAt
                      hPremiseDomain
                  have hLeftShape :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        currentLeft ≐ₘ
                          forall_codeₘ(
                            canonical_binder_variable_code_term
                              currentDepth,
                            leftCodes ·ₘ firstPremise) := by
                    simpa [universalBody] using
                      FirstOrder.Derives.conjElimLeft <|
                        FirstOrder.Derives.conjElimRight
                          hBody
                  have hShape :
                      Η ⊢ₘ[fs_zfc_support_raw_theory]
                        CanonicalProjectTrace.canonical_project_atom_code
                            kind leftDepth rightDepth ≐ₘ
                          forall_codeₘ(
                            canonical_binder_variable_code_term
                              currentDepth,
                            leftCodes ·ₘ firstPremise) :=
                    Metatheory.Derives.equality_trans
                      hSourceShapeAt
                      hLeftShape
                  exact
                    fs_zfc_support_raw_canonical_atom_ne_universal_branch
                      kind leftDepth rightDepth
                      (canonical_binder_variable_code_term
                        currentDepth)
                      (leftCodes ·ₘ firstPremise)
                      (canonical_binder_variable_code_term_admissible
                        currentDepth hCurrentDepth)
                      (function_application_term_admissible
                        leftCodes firstPremise hLeftCodes
                        (set_variable_admissible
                          firstPremiseId))
                      hBinderMemberAt
                      hPremiseMember hShape))

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
