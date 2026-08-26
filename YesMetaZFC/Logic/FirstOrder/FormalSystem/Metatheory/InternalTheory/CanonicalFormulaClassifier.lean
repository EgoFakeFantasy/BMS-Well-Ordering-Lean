import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Numbered
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy
/-!
# 规范纯集合论公式码分类器
Gödel quotation 把 locally nameless 公式中的 binder 依深度规范编号为
`2 * depth + 1`。本模块把这一元层递归过程改写成对象集合论中可检查的有限构造证书：
* 一条证书由公式码序列和对应的 quotation 深度序列组成；
* 原子行只允许变量之间的等式、隶属或项目子集关系；
* 否定、蕴含和全称量词行只能引用严格更早的行；
* 全称量词的变量码必须由当前深度规范生成；
* 最后一行必须等于待分类公式码及其入口深度。
因此该分类器既排除了 FormalSystem 扩展签名中的编码函数/关系，也排除了非规范的
α-改名。后续 ZFC 分离、收集模式只需在此公共解析证书上叠加各自的固定骨架。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false
/-! ## Canonical 内部变量分配 -/
/-- 为内部分类证书中的 binder 统一选择严格新鲜的编号。 -/
def canonical_formula_classifier_fresh_base (terms : List SetTerm) : FreeVarId :=
  FreshVariable.fresh_id SetSort.set (terms.map fun term => term ≐ₘ term)
/--
规范公式分类器的 fresh 起点及其任意后继都避开输入项的自由变量支持。
分类器会连续分配一段 binder 编号；该偏移版本统一承担后续所有有界量词的界项
新鲜性，而不要求每个调用点重新展开 `FreshVariable.formulas_bound`。
-/
theorem canonical_formula_classifier_fresh_offset_not_mem
    {terms : List SetTerm} {term : SetTerm} (hTerm : term ∈ terms) (offset : Nat) : (SetSort.set,
      canonical_formula_classifier_fresh_base terms + offset) ∉
      Term.freeSupport term := by
  intro hMember
  have hFormula :
      term ≐ₘ term ∈ (terms.map fun source => source ≐ₘ source) :=
    List.mem_map.mpr ⟨term, hTerm, rfl⟩
  have hFormulaMember : (SetSort.set,
        canonical_formula_classifier_fresh_base terms + offset) ∈
        Formula.freeSupport (term ≐ₘ term) := by
    change (SetSort.set,
        canonical_formula_classifier_fresh_base terms + offset) ∈
        Term.freeSupport term ++ Term.freeSupport term
    exact List.mem_append.mpr (Or.inl hMember)
  have hLt :=
    FreshVariable.formulas_id_lt_m
      hFormula hFormulaMember
  dsimp [canonical_formula_classifier_fresh_base,
    FreshVariable.fresh_id] at hLt
  exact (Nat.not_lt_of_ge (Nat.le_add_right _ _)) hLt
/-! ## 规范变量与纯集合论原子 -/
/-- quotation 深度 `depth` 对应的规范 binder 名称 `2 * depth + 1`。 -/
abbrev canonical_binder_name_term (depth : SetTerm) : SetTerm :=
  Sₘ(numₘ(2) *ₘ depth)
/-- quotation 深度 `depth` 对应的规范变量符号码。 -/
abbrev canonical_binder_variable_code_term (depth : SetTerm) : SetTerm :=
  var_codeₘ(canonical_binder_name_term depth)
/-- 显式指定深度见证 binder 的规范 scope 变量条件。 -/
def canonical_scoped_variable_code_condition_with_id (depth variableCode : SetTerm) (variableDepthId : FreeVarId) : SetFormula :=
  ∃ₘ[SetSort.set, variableDepthId], ((x#variableDepthId ∈ₘ depth) ∧ₘ (variableCode ≐ₘ
        canonical_binder_variable_code_term (x#variableDepthId)))
/-- `variableCode` 是严格早于 `depth` 引入的某个规范 binder 变量。 -/
def canonical_scoped_variable_code_condition (depth variableCode : SetTerm) : SetFormula :=
  let variableDepthId :=
    canonical_formula_classifier_fresh_base
      [depth, variableCode]
  canonical_scoped_variable_code_condition_with_id
    depth variableCode variableDepthId
/-- FormalSystem 签名中项目子集关系的规范二元原子码。 -/
abbrev project_subset_atomic_code_term (left right : SetTerm) : SetTerm :=
  predicate_application_code_term (numₘ(1)) (numₘ(RelationSymbol.subset.ctorIdx)) (GodelQuotation.Numbered.argument_sequence [left, right])
/--
显式指定四个内部 binder 的规范项目原子条件。
两个变量码见证各自带有一个深度见证。把四个编号作为接口参数传入，能使外层逐行
全称证明统一控制新鲜性，避免固定编号在嵌套量词下发生捕获。
-/
def canonical_project_atomic_code_condition_with_ids (depth code : SetTerm) (leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) :
    SetFormula :=
  ∃ₘ[SetSort.set, leftVariableCodeId],
    (x#leftVariableCodeId ∈ₘ TermCodeₘ) ∧ₘ
      (∃ₘ[SetSort.set, rightVariableCodeId],
        (x#rightVariableCodeId ∈ₘ TermCodeₘ) ∧ₘ
          ((canonical_scoped_variable_code_condition_with_id
              depth (x#leftVariableCodeId) leftVariableDepthId ∧ₘ
            canonical_scoped_variable_code_condition_with_id
              depth (x#rightVariableCodeId) rightVariableDepthId) ∧ₘ
            ((code ≐ₘ
                eq_codeₘ(x#leftVariableCodeId, x#rightVariableCodeId)) ∨ₘ
              ((code ≐ₘ
                  membership_atomic_formula_code_term
                    (x#leftVariableCodeId) (x#rightVariableCodeId)) ∨ₘ
                (code ≐ₘ
                  project_subset_atomic_code_term
                    (x#leftVariableCodeId) (x#rightVariableCodeId))))))
/--
`code` 是当前规范 scope 中的等式、隶属或项目子集原子。
独立使用时统一分配四个严格新鲜的内部 binder；需要置于外层量词中的调用方应使用
`canonical_project_atomic_code_condition_with_ids` 显式传入编号。
-/
def canonical_project_atomic_code_condition (depth code : SetTerm) : SetFormula :=
  let leftVariableCodeId :=
    canonical_formula_classifier_fresh_base [depth, code]
  let rightVariableCodeId := leftVariableCodeId + 1
  let leftVariableDepthId := leftVariableCodeId + 2
  let rightVariableDepthId := leftVariableCodeId + 3
  canonical_project_atomic_code_condition_with_ids
    depth code
    leftVariableCodeId rightVariableCodeId
    leftVariableDepthId rightVariableDepthId
/-! ## 有限构造证书 -/
/--
规范公式构造证书的一行。
`codes` 保存子公式码，`depths` 保存相应入口深度。复合行只能引用属于当前自然数
指标的更早行；这使证书本身承担良基递归，而无需再引入对象层递归函数。
-/
def canonical_project_formula_line_condition_with_ids (codes depths index : SetTerm) (firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) :
    SetFormula :=
  canonical_project_atomic_code_condition_with_ids (depths ·ₘ index) (codes ·ₘ index)
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId ∨ₘ
    ((∃ₘ[SetSort.set, firstPremiseId],
        (x#firstPremiseId ∈ₘ index) ∧ₘ
          (((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
              ((depths ·ₘ x#firstPremiseId) ≐ₘ
                (depths ·ₘ index))) ∧ₘ
            ((codes ·ₘ index) ≐ₘ
              neg_codeₘ(codes ·ₘ x#firstPremiseId)))) ∨ₘ
      ((∃ₘ[SetSort.set, firstPremiseId],
          (x#firstPremiseId ∈ₘ index) ∧ₘ
            (∃ₘ[SetSort.set, secondPremiseId],
              (x#secondPremiseId ∈ₘ index) ∧ₘ
                ((((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                    (x#secondPremiseId ∈ₘ domₘ(codes))) ∧ₘ
                    (((depths ·ₘ x#firstPremiseId) ≐ₘ
                        (depths ·ₘ index)) ∧ₘ
                      ((depths ·ₘ x#secondPremiseId) ≐ₘ
                        (depths ·ₘ index)))) ∧ₘ
                  ((codes ·ₘ index) ≐ₘ
                    imp_codeₘ(
                      codes ·ₘ x#firstPremiseId,
                      codes ·ₘ x#secondPremiseId))))) ∨ₘ
        (∃ₘ[SetSort.set, firstPremiseId],
          (x#firstPremiseId ∈ₘ index) ∧ₘ
            (((x#firstPremiseId ∈ₘ domₘ(codes)) ∧ₘ
                ((depths ·ₘ x#firstPremiseId) ≐ₘ
                  Sₘ(depths ·ₘ index))) ∧ₘ
              ((codes ·ₘ index) ≐ₘ
                forall_codeₘ(
                  canonical_binder_variable_code_term
                    (depths ·ₘ index),
                  codes ·ₘ x#firstPremiseId))))))
/-- 独立使用的一行证书条件。 -/
def canonical_project_formula_line_condition (codes depths index : SetTerm) : SetFormula :=
  let firstPremiseId :=
    canonical_formula_classifier_fresh_base
      [codes, depths, index]
  let secondPremiseId := firstPremiseId + 1
  let leftVariableCodeId := firstPremiseId + 2
  let rightVariableCodeId := firstPremiseId + 3
  let leftVariableDepthId := firstPremiseId + 4
  let rightVariableDepthId := firstPremiseId + 5
  canonical_project_formula_line_condition_with_ids
    codes depths index
    firstPremiseId secondPremiseId
    leftVariableCodeId rightVariableCodeId
    leftVariableDepthId rightVariableDepthId
/-- 规范构造轨迹的受定义域约束末行合同。 -/
def canonical_project_formula_terminal_condition (entryDepth code codes depths lastIndex : SetTerm) :
    SetFormula :=
  let domainCondition := (lastIndex ∈ₘ domₘ(codes)) ∧ₘ (domₘ(codes) ≐ₘ Sₘ(lastIndex))
  let valueCondition := (code ≐ₘ (codes ·ₘ lastIndex)) ∧ₘ (entryDepth ≐ₘ (depths ·ₘ lastIndex))
  domainCondition ∧ₘ valueCondition
/--
给定两条候选序列的规范纯集合论 trace 条件。
两个序列必须非空、定义域相同；每一行满足公共构造规则，末行同时给出候选公式码和
入口 quotation 深度。把序列见证留作自由项，使外层存在量词的代入与轨迹合法性证明
可以各自复用这一核心。
-/
def canonical_project_formula_trace_condition_with_ids (entryDepth code codes depths : SetTerm) (lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) :
    SetFormula := ((((codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ (depths ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ (domₘ(codes) ≐ₘ domₘ(depths))) ∧ₘ (numₘ(0) ∈ₘ domₘ(codes))) ∧ₘ
    ((∀ₘ[SetSort.set, indexId], (x#indexId ∈ₘ domₘ(codes)) ⟶ₘ
          canonical_project_formula_line_condition_with_ids
            codes depths (x#indexId)
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) ∧ₘ (∃ₘ[SetSort.set, lastIndexId],
        canonical_project_formula_terminal_condition
          entryDepth code codes depths (x#lastIndexId)))
/--
显式指定所有内部 binder 的规范纯集合论公式码分类条件。
外层量词提供公式码和入口深度轨迹的两条有限序列；其具体合法性由
`canonical_project_formula_trace_condition_with_ids` 统一表达。
-/
def canonical_project_formula_code_condition_with_ids (entryDepth code : SetTerm) (codesId depthsId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) :
    SetFormula := ((entryDepth ∈ₘ ωₘ) ∧ₘ formula_codeₘ(code)) ∧ₘ
      (∃ₘ[SetSort.set, codesId],
        (x#codesId ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          (∃ₘ[SetSort.set, depthsId],
            canonical_project_formula_trace_condition_with_ids
              entryDepth code (x#codesId) (x#depthsId)
              lastIndexId indexId
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId))
/--
`code` 是在 `entryDepth` 个规范外层 binder 下得到的纯集合论 Hilbert 公式码。
-/
def canonical_project_formula_code_condition (entryDepth code : SetTerm) : SetFormula :=
  let codesId :=
    canonical_formula_classifier_fresh_base [entryDepth, code]
  let depthsId := codesId + 1
  let lastIndexId := codesId + 2
  let indexId := codesId + 3
  let firstPremiseId := codesId + 4
  let secondPremiseId := codesId + 5
  let leftVariableCodeId := codesId + 6
  let rightVariableCodeId := codesId + 7
  let leftVariableDepthId := codesId + 8
  let rightVariableDepthId := codesId + 9
  canonical_project_formula_code_condition_with_ids
    entryDepth code
    codesId depthsId lastIndexId indexId
    firstPremiseId secondPremiseId
    leftVariableCodeId rightVariableCodeId
    leftVariableDepthId rightVariableDepthId
/-! ## 分类器公式的公共 admissibility -/
/-- 规范 binder 变量码构造保持集合项 admissibility。 -/
theorem canonical_binder_variable_code_term_admissible (depth : SetTerm) (hDepth : Term.Admissible depth SetSort.set) :
    Term.Admissible (canonical_binder_variable_code_term depth)
      SetSort.set :=
  variable_code_term_admissible _ (successor_term_admissible _ (natural_multiplication_term_admissible (numₘ(2)) depth (finite_numeral_term_admissible 2)
        hDepth))
/-- 项目子集原子码构造保持集合项 admissibility。 -/
theorem canonical_project_subset_atomic_code_term_admissible (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible (project_subset_atomic_code_term left right)
      SetSort.set := by
  have hArguments :
      Term.Admissible (GodelQuotation.Numbered.argument_sequence
          [left, right]) SetSort.set :=
    GodelQuotation.seq_admissible_m 0 <| by
      intro term hTerm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with rfl | rfl
      · exact hLeft
      · exact hRight
  exact predicate_application_code_term_admissible (numₘ(1)) (numₘ(RelationSymbol.subset.ctorIdx)) (GodelQuotation.Numbered.argument_sequence [left, right])
    (finite_numeral_term_admissible 1) (finite_numeral_term_admissible
      RelationSymbol.subset.ctorIdx)
    hArguments
/-- 显式深度见证版本的规范 scope 变量条件是 admissible 公式。 -/
theorem canonical_scoped_variable_code_condition_with_id_admissible (depth variableCode : SetTerm) (variableDepthId : FreeVarId)
    (hDepth : Term.Admissible depth SetSort.set) (hVariableCode :
      Term.Admissible variableCode SetSort.set) :
    Formula.Admissible (canonical_scoped_variable_code_condition_with_id
        depth variableCode variableDepthId) := by
  unfold canonical_scoped_variable_code_condition_with_id
  apply Formula.Admissible.exists_closeFreeAt
  apply Formula.Admissible.conj
  · exact membership_formula_admissible (set_variable_admissible variableDepthId) hDepth
  · exact Formula.Admissible.equal hVariableCode (canonical_binder_variable_code_term_admissible (x#variableDepthId) (set_variable_admissible variableDepthId))
/-- 显式内部编号的规范项目原子分类条件是 admissible 公式。 -/
theorem canonical_project_atomic_code_condition_with_ids_admissible (depth code : SetTerm) (leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hDepth : Term.Admissible depth SetSort.set) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (canonical_project_atomic_code_condition_with_ids
        depth code
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  let leftVariable := x#leftVariableCodeId
  let rightVariable := x#rightVariableCodeId
  have hLeftVariable :
      Term.Admissible leftVariable SetSort.set :=
    set_variable_admissible leftVariableCodeId
  have hRightVariable :
      Term.Admissible rightVariable SetSort.set :=
    set_variable_admissible rightVariableCodeId
  have hEqualityCode :
      Term.Admissible (eq_codeₘ(leftVariable, rightVariable))
        SetSort.set :=
    equality_formula_code_term_admissible
      leftVariable rightVariable
      hLeftVariable hRightVariable
  have hMembershipCode :
      Term.Admissible (membership_atomic_formula_code_term
          leftVariable rightVariable)
        SetSort.set :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term
      leftVariable rightVariable
      membership_symbol_code_term_admissible
      hLeftVariable hRightVariable
  have hSubsetCode :
      Term.Admissible (project_subset_atomic_code_term
          leftVariable rightVariable)
        SetSort.set :=
    canonical_project_subset_atomic_code_term_admissible
      leftVariable rightVariable
      hLeftVariable hRightVariable
  have hRightBody :
      Formula.Admissible
        ((rightVariable ∈ₘ TermCodeₘ) ∧ₘ
          ((canonical_scoped_variable_code_condition_with_id
              depth leftVariable leftVariableDepthId ∧ₘ
            canonical_scoped_variable_code_condition_with_id
              depth rightVariable rightVariableDepthId) ∧ₘ
            ((code ≐ₘ eq_codeₘ(leftVariable, rightVariable)) ∨ₘ
              ((code ≐ₘ
                  membership_atomic_formula_code_term
                    leftVariable rightVariable) ∨ₘ
                (code ≐ₘ
                  project_subset_atomic_code_term
                    leftVariable rightVariable))))) :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hRightVariable
        term_code_set_term_admissible)
      (Formula.Admissible.conj
        (Formula.Admissible.conj
          (canonical_scoped_variable_code_condition_with_id_admissible
            depth leftVariable leftVariableDepthId
            hDepth hLeftVariable)
          (canonical_scoped_variable_code_condition_with_id_admissible
            depth rightVariable rightVariableDepthId
            hDepth hRightVariable))
        (Formula.Admissible.disj
          (Formula.Admissible.equal hCode hEqualityCode)
          (Formula.Admissible.disj
            (Formula.Admissible.equal hCode hMembershipCode)
            (Formula.Admissible.equal hCode hSubsetCode))))
  have hRight :=
    Formula.Admissible.exists_closeFreeAt
      SetSort.set rightVariableCodeId hRightBody
  have hOuterBody :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hLeftVariable
        term_code_set_term_admissible)
      hRight
  simpa [canonical_project_atomic_code_condition_with_ids,
    leftVariable, rightVariable] using
    Formula.Admissible.exists_closeFreeAt
      SetSort.set leftVariableCodeId hOuterBody
/-- 规范原子分类条件由深度项与代码项的计算证书直接合成。 -/
@[formula_check]
theorem canonical_project_atomic_code_condition_with_ids_check
    (depth code : SetTerm)
    (leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId)
    (hDepth : Term.CheckCertificate depth SetSort.set)
    (hCode : Term.CheckCertificate code SetSort.set) :
    Formula.CheckCertificate
      (canonical_project_atomic_code_condition_with_ids
        depth code
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) :=
  Formula.check_admissible_complete <|
    canonical_project_atomic_code_condition_with_ids_admissible
      depth code
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hDepth.admissible hCode.admissible
/-- 显式内部编号的一条规范公式轨迹行是 admissible 公式。 -/
theorem canonical_project_formula_line_condition_with_ids_admissible (codes depths index : SetTerm) (firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hCodes : Term.Admissible codes SetSort.set) (hDepths : Term.Admissible depths SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible (canonical_project_formula_line_condition_with_ids
        codes depths index
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  prove_admissible
/-- 规范公式轨迹行由三项计算证书直接合成，避免展开大型析取树。 -/
@[formula_check]
theorem canonical_project_formula_line_condition_with_ids_check
    (codes depths index : SetTerm)
    (firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId)
    (hCodes : Term.CheckCertificate codes SetSort.set)
    (hDepths : Term.CheckCertificate depths SetSort.set)
    (hIndex : Term.CheckCertificate index SetSort.set) :
    Formula.CheckCertificate
      (canonical_project_formula_line_condition_with_ids
        codes depths index
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) :=
  Formula.check_admissible_complete <|
    canonical_project_formula_line_condition_with_ids_admissible
      codes depths index
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId
      hCodes.admissible hDepths.admissible hIndex.admissible
/-- 规范公式轨迹的末行合同是 admissible 公式。 -/
theorem canonical_project_formula_terminal_condition_admissible (entryDepth code codes depths lastIndex : SetTerm)
    (hEntryDepth : Term.Admissible entryDepth SetSort.set) (hCode : Term.Admissible code SetSort.set) (hCodes : Term.Admissible codes SetSort.set)
    (hDepths : Term.Admissible depths SetSort.set) (hLastIndex : Term.Admissible lastIndex SetSort.set) :
    Formula.Admissible (canonical_project_formula_terminal_condition
        entryDepth code codes depths lastIndex) := by
  have hCodesDomain :=
    domain_term_admissible codes hCodes
  have hCodeAtLast :=
    function_application_term_admissible
      codes lastIndex hCodes hLastIndex
  have hDepthAtLast :=
    function_application_term_admissible
      depths lastIndex hDepths hLastIndex
  unfold canonical_project_formula_terminal_condition
  exact Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
        hLastIndex hCodesDomain) (Formula.Admissible.equal hCodesDomain (successor_term_admissible lastIndex hLastIndex))) (Formula.Admissible.conj
      (Formula.Admissible.equal hCode hCodeAtLast) (Formula.Admissible.equal hEntryDepth hDepthAtLast))
/-- 给定两条候选序列的规范公式轨迹条件是 admissible 公式。 -/
theorem canonical_project_formula_trace_condition_with_ids_admissible (entryDepth code codes depths : SetTerm) (lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hEntryDepth : Term.Admissible entryDepth SetSort.set) (hCode : Term.Admissible code SetSort.set)
    (hCodes : Term.Admissible codes SetSort.set) (hDepths : Term.Admissible depths SetSort.set) :
    Formula.Admissible (canonical_project_formula_trace_condition_with_ids
        entryDepth code codes depths
        lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  let index := x#indexId
  let lastIndex := x#lastIndexId
  have hIndex : Term.Admissible index SetSort.set :=
    set_variable_admissible indexId
  have hLastIndex :
      Term.Admissible lastIndex SetSort.set :=
    set_variable_admissible lastIndexId
  have hCodesDomain :=
    domain_term_admissible codes hCodes
  have hDepthsDomain :=
    domain_term_admissible depths hDepths
  have hLine :
      Formula.Admissible ((x#indexId ∈ₘ domₘ(codes)) ⟶ₘ
          canonical_project_formula_line_condition_with_ids
            codes depths (x#indexId)
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) :=
    Formula.Admissible.imp (membership_formula_admissible hIndex hCodesDomain) (canonical_project_formula_line_condition_with_ids_admissible
        codes depths index
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
        hCodes hDepths hIndex)
  have hTerminal :
      Formula.Admissible (∃ₘ[SetSort.set, lastIndexId],
          canonical_project_formula_terminal_condition
            entryDepth code codes depths (x#lastIndexId)) :=
    Formula.Admissible.exists_closeFreeAt _ _ <|
      canonical_project_formula_terminal_condition_admissible
        entryDepth code codes depths lastIndex
        hEntryDepth hCode hCodes hDepths hLastIndex
  unfold canonical_project_formula_trace_condition_with_ids
  exact Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible hCodes
            (nonempty_finite_sequence_space_term_admissible
              FormulaCodeₘ formula_code_set_term_admissible)) (membership_formula_admissible hDepths (nonempty_finite_sequence_space_term_admissible
              ωₘ omega_term_admissible))) (Formula.Admissible.equal
          hCodesDomain hDepthsDomain)) (membership_formula_admissible (finite_numeral_term_admissible 0)
        hCodesDomain)) (Formula.Admissible.conj (Formula.Admissible.forall_closeFreeAt
        SetSort.set indexId hLine)
      hTerminal)
/-- 显式内部编号的规范公式总分类条件是 admissible 公式。 -/
theorem canonical_project_formula_code_condition_with_ids_admissible (entryDepth code : SetTerm) (codesId depthsId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) (hEntryDepth : Term.Admissible entryDepth SetSort.set) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (canonical_project_formula_code_condition_with_ids
        entryDepth code
        codesId depthsId lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId) := by
  let codes := x#codesId
  let depths := x#depthsId
  have hCodes : Term.Admissible codes SetSort.set :=
    set_variable_admissible codesId
  have hDepths : Term.Admissible depths SetSort.set :=
    set_variable_admissible depthsId
  have hTrace :
      Formula.Admissible
        (∃ₘ[SetSort.set, depthsId],
          canonical_project_formula_trace_condition_with_ids
            entryDepth code codes depths
            lastIndexId indexId
            firstPremiseId secondPremiseId
            leftVariableCodeId rightVariableCodeId
            leftVariableDepthId rightVariableDepthId) :=
    Formula.Admissible.exists_closeFreeAt SetSort.set depthsId <|
      canonical_project_formula_trace_condition_with_ids_admissible
        entryDepth code codes depths
        lastIndexId indexId
        firstPremiseId secondPremiseId
        leftVariableCodeId rightVariableCodeId
        leftVariableDepthId rightVariableDepthId
        hEntryDepth hCode hCodes hDepths
  have hCodesBody :
      Formula.Admissible
        ((codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
          (∃ₘ[SetSort.set, depthsId],
            canonical_project_formula_trace_condition_with_ids
              entryDepth code codes depths
              lastIndexId indexId
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId)) :=
    Formula.Admissible.conj
      (membership_formula_admissible
        hCodes
        (nonempty_finite_sequence_space_term_admissible
          FormulaCodeₘ formula_code_set_term_admissible))
      hTrace
  unfold canonical_project_formula_code_condition_with_ids
  exact Formula.Admissible.conj
    (Formula.Admissible.conj
      (membership_formula_admissible
        hEntryDepth omega_term_admissible)
      (is_formula_code_formula_admissible hCode))
    (Formula.Admissible.exists_closeFreeAt
      SetSort.set codesId hCodesBody)
/-! ## 规范深度平移的同步解析 -/
/--
把一个规范变量深度沿切点 `cutoff` 平移一层。
切点以前的参数深度保持不变；切点及其后的局部 binder 深度统一取后继。
-/
def canonical_shifted_depth_condition (cutoff sourceDepth targetDepth : SetTerm) : SetFormula := (((sourceDepth ∈ₘ cutoff) ∧ₘ (targetDepth ≐ₘ sourceDepth)) ∨ₘ
    ((((sourceDepth ≐ₘ cutoff) ∨ₘ (cutoff ∈ₘ sourceDepth))) ∧ₘ (targetDepth ≐ₘ Sₘ(sourceDepth))))

/-- 规范深度平移条件只含原子关系与布尔联结词。 -/
theorem canonical_shifted_depth_condition_delta0
    (cutoff sourceDepth targetDepth : SetTerm) :
    Formula.IsDelta0 ProofT.set_levy_bound
      (canonical_shifted_depth_condition
        cutoff sourceDepth targetDepth) := by
  have hBefore :
      Formula.IsDelta0 ProofT.set_levy_bound
        ((sourceDepth ∈ₘ cutoff) ∧ₘ
          (targetDepth ≐ₘ sourceDepth)) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [sourceDepth, cutoff])
      (Formula.IsDelta0.equal
        targetDepth sourceDepth)
  have hAfter :
      Formula.IsDelta0 ProofT.set_levy_bound
        (((sourceDepth ≐ₘ cutoff) ∨ₘ
            (cutoff ∈ₘ sourceDepth)) ∧ₘ
          (targetDepth ≐ₘ Sₘ(sourceDepth))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.disj
        (Formula.IsDelta0.equal
          sourceDepth cutoff)
        (Formula.IsDelta0.rel
          RelationSymbol.membership
          [cutoff, sourceDepth]))
      (Formula.IsDelta0.equal
        targetDepth (Sₘ(sourceDepth)))
  simpa [canonical_shifted_depth_condition] using
    Formula.IsDelta0.disj hBefore hAfter
/-- 一个目标深度见证正确实现变量深度平移。 -/
def canonical_shifted_variable_target_condition (cutoff sourceDepth rightVariable targetDepth : SetTerm) :
    SetFormula :=
  canonical_shifted_depth_condition
      cutoff sourceDepth targetDepth ∧ₘ (rightVariable ≐ₘ
      canonical_binder_variable_code_term targetDepth)
/-- 显式指定深度见证的规范变量同步平移条件。 -/
def canonical_shifted_variable_code_condition_with_id (cutoff entryDepth leftVariable rightVariable : SetTerm) (variableDepthId : FreeVarId) : SetFormula :=
  ∃ₘ[SetSort.set, variableDepthId], (((x#variableDepthId ∈ₘ entryDepth) ∧ₘ (leftVariable ≐ₘ
        canonical_binder_variable_code_term (x#variableDepthId))) ∧ₘ (∃ₘ[SetSort.set, variableDepthId + 1],
        canonical_shifted_variable_target_condition
          cutoff (x#variableDepthId) rightVariable (x#(variableDepthId + 1))))
/-- 一个规范变量码按给定切点平移到右侧环境。 -/
def canonical_shifted_variable_code_condition (cutoff entryDepth leftVariable rightVariable : SetTerm) :
    SetFormula :=
  let variableDepthId :=
    canonical_formula_classifier_fresh_base
      [cutoff, entryDepth, leftVariable, rightVariable]
  canonical_shifted_variable_code_condition_with_id
    cutoff entryDepth leftVariable rightVariable
    variableDepthId
/--
显式指定全部内部编号的原子同步平移条件。
前四个编号承载左右两个变量码，后两个编号分别作为两组变量深度见证的起点；
每个深度条件还会占用其起点的后继编号。
-/
def canonical_project_atomic_shift_condition_with_ids (cutoff entryDepth leftCode rightCode : SetTerm) :
    FreeVarId → FreeVarId → FreeVarId → FreeVarId →
      FreeVarId → FreeVarId → SetFormula :=
  fun leftFirstId rightFirstId leftSecondId rightSecondId
      firstDepthId secondDepthId =>
  ∃ₘ[SetSort.set, leftFirstId],
    ∃ₘ[SetSort.set, rightFirstId],
      ∃ₘ[SetSort.set, leftSecondId],
        ∃ₘ[SetSort.set, rightSecondId], ((canonical_shifted_variable_code_condition_with_id
              cutoff entryDepth (x#leftFirstId) (x#rightFirstId)
              firstDepthId ∧ₘ
            canonical_shifted_variable_code_condition_with_id
              cutoff entryDepth (x#leftSecondId) (x#rightSecondId)
              secondDepthId) ∧ₘ (((leftCode ≐ₘ
                  eq_codeₘ(
                    x#leftFirstId, x#leftSecondId)) ∧ₘ (rightCode ≐ₘ
                  eq_codeₘ(
                    x#rightFirstId, x#rightSecondId))) ∨ₘ ((((leftCode ≐ₘ
                    membership_atomic_formula_code_term (x#leftFirstId) (x#leftSecondId)) ∧ₘ (rightCode ≐ₘ
                    membership_atomic_formula_code_term (x#rightFirstId) (x#rightSecondId)))) ∨ₘ ((leftCode ≐ₘ
                    project_subset_atomic_code_term (x#leftFirstId) (x#leftSecondId)) ∧ₘ (rightCode ≐ₘ
                    project_subset_atomic_code_term (x#rightFirstId) (x#rightSecondId))))))
/--
两个原子公式码具有完全相同的纯集合论骨架，变量按切点同步平移。
所有内部编号一次性从共同 fresh base 分配，因此外层变量码见证代入后，内层深度
见证的编号不会重新计算；这使条件对闭项替换严格稳定，而不只是在 α-等价意义下稳定。
-/
def canonical_project_atomic_shift_condition (cutoff entryDepth leftCode rightCode : SetTerm) :
    SetFormula :=
  let base :=
    canonical_formula_classifier_fresh_base
      [cutoff, entryDepth, leftCode, rightCode]
  canonical_project_atomic_shift_condition_with_ids
    cutoff entryDepth leftCode rightCode
    base (base + 1) (base + 2) (base + 3) (base + 4) (base + 6)
/--
同步深度平移证书的一行。
左右公式共享同一构造标签和同一组前提行；右侧入口深度恒为左侧深度的后继。
-/
def canonical_project_formula_shift_line_condition_with_ids (cutoff leftCodes rightCodes depths index : SetTerm)
    (firstPremiseId secondPremiseId atomicBaseId : FreeVarId) :
    SetFormula :=
  canonical_project_atomic_shift_condition_with_ids
      cutoff (depths ·ₘ index) (leftCodes ·ₘ index) (rightCodes ·ₘ index)
      atomicBaseId (atomicBaseId + 1) (atomicBaseId + 2) (atomicBaseId + 3) (atomicBaseId + 4) (atomicBaseId + 6) ∨ₘ ((∃ₘ[SetSort.set, firstPremiseId],
        ((((x#firstPremiseId ∈ₘ index) ∧ₘ (x#firstPremiseId ∈ₘ domₘ(leftCodes))) ∧ₘ ((depths ·ₘ x#firstPremiseId) ≐ₘ (depths ·ₘ index))) ∧ₘ
          (((leftCodes ·ₘ index) ≐ₘ
              neg_codeₘ(leftCodes ·ₘ x#firstPremiseId)) ∧ₘ ((rightCodes ·ₘ index) ≐ₘ
              neg_codeₘ(rightCodes ·ₘ x#firstPremiseId))))) ∨ₘ ((∃ₘ[SetSort.set, firstPremiseId],
          ∃ₘ[SetSort.set, secondPremiseId], (((((x#firstPremiseId ∈ₘ index) ∧ₘ (x#firstPremiseId ∈ₘ domₘ(leftCodes))) ∧ₘ ((x#secondPremiseId ∈ₘ index) ∧ₘ
                  (x#secondPremiseId ∈ₘ domₘ(leftCodes)))) ∧ₘ (((depths ·ₘ x#firstPremiseId) ≐ₘ (depths ·ₘ index)) ∧ₘ ((depths ·ₘ x#secondPremiseId) ≐ₘ
                  (depths ·ₘ index)))) ∧ₘ (((leftCodes ·ₘ index) ≐ₘ
                  imp_codeₘ(
                    leftCodes ·ₘ x#firstPremiseId,
                    leftCodes ·ₘ x#secondPremiseId)) ∧ₘ ((rightCodes ·ₘ index) ≐ₘ
                  imp_codeₘ(
                    rightCodes ·ₘ x#firstPremiseId,
                    rightCodes ·ₘ x#secondPremiseId))))) ∨ₘ (∃ₘ[SetSort.set, firstPremiseId], ((((x#firstPremiseId ∈ₘ index) ∧ₘ
                (x#firstPremiseId ∈ₘ domₘ(leftCodes))) ∧ₘ ((depths ·ₘ x#firstPremiseId) ≐ₘ
                Sₘ(depths ·ₘ index))) ∧ₘ (((leftCodes ·ₘ index) ≐ₘ
                forall_codeₘ(
                  canonical_binder_variable_code_term (depths ·ₘ index),
                  leftCodes ·ₘ x#firstPremiseId)) ∧ₘ ((rightCodes ·ₘ index) ≐ₘ
                forall_codeₘ(
                  canonical_binder_variable_code_term (Sₘ(depths ·ₘ index)),
                  rightCodes ·ₘ x#firstPremiseId)))))))
/-- 同步平移证书的三个并行序列及其末行合同。 -/
def canonical_project_formula_shift_trace_condition (cutoff entryDepth leftCode rightCode
      leftCodes rightCodes depths : SetTerm) (lastIndexId indexId firstPremiseId secondPremiseId
      atomicBaseId : FreeVarId) :
    SetFormula :=
  let sequenceCondition := ((leftCodes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ (rightCodes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ))) ∧ₘ (depths ∈ₘ seq₊_spaceₘ(ωₘ))
  let domainCondition := (domₘ(leftCodes) ≐ₘ domₘ(rightCodes)) ∧ₘ (domₘ(leftCodes) ≐ₘ domₘ(depths))
  let lineCondition :=
    ∀ₘ[SetSort.set, indexId], (x#indexId ∈ₘ domₘ(leftCodes)) ⟶ₘ
        canonical_project_formula_shift_line_condition_with_ids
          cutoff leftCodes rightCodes depths (x#indexId)
          firstPremiseId secondPremiseId atomicBaseId
  let terminalCondition :=
    ∃ₘ[SetSort.set, lastIndexId], (((x#lastIndexId ∈ₘ domₘ(leftCodes)) ∧ₘ (domₘ(leftCodes) ≐ₘ Sₘ(x#lastIndexId))) ∧ₘ (((leftCode ≐ₘ
            (leftCodes ·ₘ x#lastIndexId)) ∧ₘ (rightCode ≐ₘ (rightCodes ·ₘ x#lastIndexId))) ∧ₘ (entryDepth ≐ₘ (depths ·ₘ x#lastIndexId))))
  (sequenceCondition ∧ₘ domainCondition) ∧ₘ ((numₘ(0) ∈ₘ domₘ(leftCodes)) ∧ₘ (lineCondition ∧ₘ terminalCondition))
/--
显式指定内部 binder 的规范公式深度平移关系核心。
右侧公式对应把左侧所有深度不小于 `cutoff` 的 binder 名称统一平移一层。
-/
def canonical_project_formula_shift_code_condition_with_ids (cutoff entryDepth leftCode rightCode : SetTerm) (leftCodesId rightCodesId depthsId lastIndexId
      indexId firstPremiseId secondPremiseId
      atomicBaseId : FreeVarId) :
    SetFormula := ((((cutoff ∈ₘ ωₘ) ∧ₘ (entryDepth ∈ₘ ωₘ)) ∧ₘ ((cutoff ≐ₘ entryDepth) ∨ₘ (cutoff ∈ₘ entryDepth))) ∧ₘ (formula_codeₘ(leftCode) ∧ₘ
      formula_codeₘ(rightCode))) ∧ₘ (∃ₘ[SetSort.set, leftCodesId],
      ∃ₘ[SetSort.set, rightCodesId],
        ∃ₘ[SetSort.set, depthsId],
          canonical_project_formula_shift_trace_condition
            cutoff entryDepth leftCode rightCode (x#leftCodesId) (x#rightCodesId) (x#depthsId)
            lastIndexId indexId firstPremiseId secondPremiseId
            atomicBaseId)
/-- 规范纯集合论公式码在给定深度切点上的同步平移关系。 -/
def canonical_project_formula_shift_code_condition (cutoff entryDepth leftCode rightCode : SetTerm) :
    SetFormula :=
  let leftCodesId :=
    canonical_formula_classifier_fresh_base
      [cutoff, entryDepth, leftCode, rightCode]
  let rightCodesId := leftCodesId + 1
  let depthsId := leftCodesId + 2
  let lastIndexId := leftCodesId + 3
  let indexId := leftCodesId + 4
  let firstPremiseId := leftCodesId + 5
  let secondPremiseId := leftCodesId + 6
  let atomicBaseId := leftCodesId + 7
  canonical_project_formula_shift_code_condition_with_ids
    cutoff entryDepth leftCode rightCode
    leftCodesId rightCodesId depthsId lastIndexId
    indexId firstPremiseId secondPremiseId atomicBaseId
/-! ## 规范深度平移的公共 admissibility -/
/-- 规范深度平移的算术分支是 admissible 公式。 -/
theorem canonical_shifted_depth_condition_admissible (cutoff sourceDepth targetDepth : SetTerm) (hCutoff : Term.Admissible cutoff SetSort.set)
    (hSourceDepth : Term.Admissible sourceDepth SetSort.set) (hTargetDepth : Term.Admissible targetDepth SetSort.set) :
    Formula.Admissible (canonical_shifted_depth_condition
        cutoff sourceDepth targetDepth) := by
  unfold canonical_shifted_depth_condition
  exact Formula.Admissible.disj (Formula.Admissible.conj (membership_formula_admissible
        hSourceDepth hCutoff) (Formula.Admissible.equal
        hTargetDepth hSourceDepth)) (Formula.Admissible.conj (Formula.Admissible.disj (Formula.Admissible.equal
          hSourceDepth hCutoff) (membership_formula_admissible
          hCutoff hSourceDepth)) (Formula.Admissible.equal
        hTargetDepth (successor_term_admissible
          sourceDepth hSourceDepth)))
/-- 规范变量的目标深度与目标变量码合同是 admissible 公式。 -/
theorem canonical_shifted_variable_target_condition_admissible (cutoff sourceDepth rightVariable targetDepth : SetTerm)
    (hCutoff : Term.Admissible cutoff SetSort.set) (hSourceDepth : Term.Admissible sourceDepth SetSort.set)
    (hRightVariable : Term.Admissible rightVariable SetSort.set) (hTargetDepth : Term.Admissible targetDepth SetSort.set) :
    Formula.Admissible (canonical_shifted_variable_target_condition
        cutoff sourceDepth rightVariable targetDepth) := by
  unfold canonical_shifted_variable_target_condition
  exact Formula.Admissible.conj (canonical_shifted_depth_condition_admissible
      cutoff sourceDepth targetDepth
      hCutoff hSourceDepth hTargetDepth) (Formula.Admissible.equal
      hRightVariable (canonical_binder_variable_code_term_admissible
        targetDepth hTargetDepth))
/-- 显式深度见证的变量同步平移条件是 admissible 公式。 -/
theorem canonical_shifted_variable_code_condition_with_id_admissible (cutoff entryDepth leftVariable rightVariable : SetTerm) (variableDepthId : FreeVarId)
    (hCutoff : Term.Admissible cutoff SetSort.set) (hEntryDepth : Term.Admissible entryDepth SetSort.set)
    (hLeftVariable : Term.Admissible leftVariable SetSort.set) (hRightVariable : Term.Admissible rightVariable SetSort.set) :
    Formula.Admissible (canonical_shifted_variable_code_condition_with_id
        cutoff entryDepth leftVariable rightVariable
        variableDepthId) := by
  let sourceDepth := x#variableDepthId
  let targetDepth := x#(variableDepthId + 1)
  have hSourceDepth :
      Term.Admissible sourceDepth SetSort.set :=
    set_variable_admissible variableDepthId
  have hTargetDepth :
      Term.Admissible targetDepth SetSort.set :=
    set_variable_admissible (variableDepthId + 1)
  unfold canonical_shifted_variable_code_condition_with_id
  apply Formula.Admissible.exists_closeFreeAt
  exact Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
        hSourceDepth hEntryDepth) (Formula.Admissible.equal
        hLeftVariable (canonical_binder_variable_code_term_admissible
          sourceDepth hSourceDepth))) (Formula.Admissible.exists_closeFreeAt _ _ <|
      canonical_shifted_variable_target_condition_admissible
        cutoff sourceDepth rightVariable targetDepth
        hCutoff hSourceDepth hRightVariable hTargetDepth)
/-- 自动新鲜编号版本的变量同步平移条件是 admissible 公式。 -/
theorem canonical_shifted_variable_code_condition_admissible (cutoff entryDepth leftVariable rightVariable : SetTerm)
    (hCutoff : Term.Admissible cutoff SetSort.set) (hEntryDepth : Term.Admissible entryDepth SetSort.set)
    (hLeftVariable : Term.Admissible leftVariable SetSort.set) (hRightVariable : Term.Admissible rightVariable SetSort.set) :
    Formula.Admissible (canonical_shifted_variable_code_condition
        cutoff entryDepth leftVariable rightVariable) := by
  unfold canonical_shifted_variable_code_condition
  exact
    canonical_shifted_variable_code_condition_with_id_admissible
      cutoff entryDepth leftVariable rightVariable (canonical_formula_classifier_fresh_base
        [cutoff, entryDepth, leftVariable, rightVariable])
      hCutoff hEntryDepth hLeftVariable hRightVariable
/-- 显式编号的两个同步原子码骨架条件是 admissible 公式。 -/
theorem canonical_project_atomic_shift_condition_with_ids_admissible (cutoff entryDepth leftCode rightCode : SetTerm)
    (leftFirstId rightFirstId leftSecondId rightSecondId :
      FreeVarId) (firstDepthId secondDepthId : FreeVarId) (hCutoff : Term.Admissible cutoff SetSort.set) (hEntryDepth : Term.Admissible entryDepth SetSort.set)
    (hLeftCode : Term.Admissible leftCode SetSort.set) (hRightCode : Term.Admissible rightCode SetSort.set) :
    Formula.Admissible (canonical_project_atomic_shift_condition_with_ids
        cutoff entryDepth leftCode rightCode
        leftFirstId rightFirstId leftSecondId rightSecondId
        firstDepthId secondDepthId) := by
  let leftFirst := x#leftFirstId
  let rightFirst := x#rightFirstId
  let leftSecond := x#leftSecondId
  let rightSecond := x#rightSecondId
  have hLeftFirst : Term.Admissible leftFirst SetSort.set :=
    set_variable_admissible leftFirstId
  have hRightFirst : Term.Admissible rightFirst SetSort.set :=
    set_variable_admissible rightFirstId
  have hLeftSecond : Term.Admissible leftSecond SetSort.set :=
    set_variable_admissible leftSecondId
  have hRightSecond : Term.Admissible rightSecond SetSort.set :=
    set_variable_admissible rightSecondId
  have hEqualityLeft :=
    equality_formula_code_term_admissible
      leftFirst leftSecond hLeftFirst hLeftSecond
  have hEqualityRight :=
    equality_formula_code_term_admissible
      rightFirst rightSecond hRightFirst hRightSecond
  have hMembershipLeft :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term
      leftFirst leftSecond
      membership_symbol_code_term_admissible
      hLeftFirst hLeftSecond
  have hMembershipRight :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term
      rightFirst rightSecond
      membership_symbol_code_term_admissible
      hRightFirst hRightSecond
  have hSubsetLeft :=
    canonical_project_subset_atomic_code_term_admissible
      leftFirst leftSecond hLeftFirst hLeftSecond
  have hSubsetRight :=
    canonical_project_subset_atomic_code_term_admissible
      rightFirst rightSecond hRightFirst hRightSecond
  unfold canonical_project_atomic_shift_condition_with_ids
  apply Formula.Admissible.exists_closeFreeAt
  apply Formula.Admissible.exists_closeFreeAt
  apply Formula.Admissible.exists_closeFreeAt
  apply Formula.Admissible.exists_closeFreeAt
  exact Formula.Admissible.conj (Formula.Admissible.conj (canonical_shifted_variable_code_condition_with_id_admissible
        cutoff entryDepth leftFirst rightFirst
        firstDepthId
        hCutoff hEntryDepth hLeftFirst hRightFirst) (canonical_shifted_variable_code_condition_with_id_admissible
        cutoff entryDepth leftSecond rightSecond
        secondDepthId
        hCutoff hEntryDepth hLeftSecond hRightSecond)) (Formula.Admissible.disj (Formula.Admissible.conj (Formula.Admissible.equal hLeftCode hEqualityLeft)
        (Formula.Admissible.equal hRightCode hEqualityRight)) (Formula.Admissible.disj (Formula.Admissible.conj (Formula.Admissible.equal
            hLeftCode hMembershipLeft) (Formula.Admissible.equal
            hRightCode hMembershipRight)) (Formula.Admissible.conj (Formula.Admissible.equal hLeftCode hSubsetLeft)
          (Formula.Admissible.equal hRightCode hSubsetRight))))
/-- 自动分配全部内部编号的同步原子码骨架条件是 admissible 公式。 -/
theorem canonical_project_atomic_shift_condition_admissible (cutoff entryDepth leftCode rightCode : SetTerm) (hCutoff : Term.Admissible cutoff SetSort.set)
    (hEntryDepth : Term.Admissible entryDepth SetSort.set) (hLeftCode : Term.Admissible leftCode SetSort.set)
    (hRightCode : Term.Admissible rightCode SetSort.set) :
    Formula.Admissible (canonical_project_atomic_shift_condition
        cutoff entryDepth leftCode rightCode) := by
  unfold canonical_project_atomic_shift_condition
  exact
    canonical_project_atomic_shift_condition_with_ids_admissible
      cutoff entryDepth leftCode rightCode (canonical_formula_classifier_fresh_base
        [cutoff, entryDepth, leftCode, rightCode]) (canonical_formula_classifier_fresh_base
        [cutoff, entryDepth, leftCode, rightCode] + 1) (canonical_formula_classifier_fresh_base
        [cutoff, entryDepth, leftCode, rightCode] + 2) (canonical_formula_classifier_fresh_base
        [cutoff, entryDepth, leftCode, rightCode] + 3) (canonical_formula_classifier_fresh_base
        [cutoff, entryDepth, leftCode, rightCode] + 4) (canonical_formula_classifier_fresh_base
        [cutoff, entryDepth, leftCode, rightCode] + 6)
      hCutoff hEntryDepth hLeftCode hRightCode
/-- 显式前提编号的一条同步平移轨迹行是 admissible 公式。 -/
theorem canonical_project_formula_shift_line_condition_with_ids_admissible (cutoff leftCodes rightCodes depths index : SetTerm)
    (firstPremiseId secondPremiseId atomicBaseId : FreeVarId) (hCutoff : Term.Admissible cutoff SetSort.set)
    (hLeftCodes : Term.Admissible leftCodes SetSort.set) (hRightCodes : Term.Admissible rightCodes SetSort.set) (hDepths : Term.Admissible depths SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible (canonical_project_formula_shift_line_condition_with_ids
        cutoff leftCodes rightCodes depths index
        firstPremiseId secondPremiseId atomicBaseId) := by
  let firstPremise := x#firstPremiseId
  let secondPremise := x#secondPremiseId
  have hFirstPremise :
      Term.Admissible firstPremise SetSort.set :=
    set_variable_admissible firstPremiseId
  have hSecondPremise :
      Term.Admissible secondPremise SetSort.set :=
    set_variable_admissible secondPremiseId
  have hLeftAt (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :
      Term.Admissible (leftCodes ·ₘ point) SetSort.set :=
    function_application_term_admissible
      leftCodes point hLeftCodes hPoint
  have hRightAt (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :
      Term.Admissible (rightCodes ·ₘ point) SetSort.set :=
    function_application_term_admissible
      rightCodes point hRightCodes hPoint
  have hDepthAt (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :
      Term.Admissible (depths ·ₘ point) SetSort.set :=
    function_application_term_admissible
      depths point hDepths hPoint
  have hEarlier (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :
      Formula.Admissible (point ∈ₘ index) :=
    membership_formula_admissible hPoint hIndex
  have hPremiseDomain (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :
      Formula.Admissible (point ∈ₘ domₘ(leftCodes)) :=
    membership_formula_admissible hPoint (domain_term_admissible leftCodes hLeftCodes)
  have hDepthAgreement (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :
      Formula.Admissible ((depths ·ₘ point) ≐ₘ (depths ·ₘ index)) :=
    Formula.Admissible.equal (hDepthAt point hPoint) (hDepthAt index hIndex)
  have hLeftNegation :
      Formula.Admissible ((leftCodes ·ₘ index) ≐ₘ
          neg_codeₘ(leftCodes ·ₘ firstPremise)) :=
    Formula.Admissible.equal (hLeftAt index hIndex) (negation_formula_code_term_admissible _ (hLeftAt firstPremise hFirstPremise))
  have hRightNegation :
      Formula.Admissible ((rightCodes ·ₘ index) ≐ₘ
          neg_codeₘ(rightCodes ·ₘ firstPremise)) :=
    Formula.Admissible.equal (hRightAt index hIndex) (negation_formula_code_term_admissible _ (hRightAt firstPremise hFirstPremise))
  have hLeftImplication :
      Formula.Admissible ((leftCodes ·ₘ index) ≐ₘ
          imp_codeₘ(
            leftCodes ·ₘ firstPremise,
            leftCodes ·ₘ secondPremise)) :=
    Formula.Admissible.equal (hLeftAt index hIndex) (implication_formula_code_term_admissible _ _ (hLeftAt firstPremise hFirstPremise)
        (hLeftAt secondPremise hSecondPremise))
  have hRightImplication :
      Formula.Admissible ((rightCodes ·ₘ index) ≐ₘ
          imp_codeₘ(
            rightCodes ·ₘ firstPremise,
            rightCodes ·ₘ secondPremise)) :=
    Formula.Admissible.equal (hRightAt index hIndex) (implication_formula_code_term_admissible _ _ (hRightAt firstPremise hFirstPremise)
        (hRightAt secondPremise hSecondPremise))
  have hUniversalDepth :
      Formula.Admissible ((depths ·ₘ firstPremise) ≐ₘ
          Sₘ(depths ·ₘ index)) :=
    Formula.Admissible.equal (hDepthAt firstPremise hFirstPremise) (successor_term_admissible _ (hDepthAt index hIndex))
  have hLeftUniversal :
      Formula.Admissible ((leftCodes ·ₘ index) ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term (depths ·ₘ index),
            leftCodes ·ₘ firstPremise)) :=
    Formula.Admissible.equal (hLeftAt index hIndex) (universal_formula_code_term_admissible _ _ (canonical_binder_variable_code_term_admissible _
          (hDepthAt index hIndex)) (hLeftAt firstPremise hFirstPremise))
  have hRightUniversal :
      Formula.Admissible ((rightCodes ·ₘ index) ≐ₘ
          forall_codeₘ(
            canonical_binder_variable_code_term (Sₘ(depths ·ₘ index)),
            rightCodes ·ₘ firstPremise)) :=
    Formula.Admissible.equal (hRightAt index hIndex) (universal_formula_code_term_admissible _ _ (canonical_binder_variable_code_term_admissible _
          (successor_term_admissible _ (hDepthAt index hIndex))) (hRightAt firstPremise hFirstPremise))
  unfold canonical_project_formula_shift_line_condition_with_ids
  exact Formula.Admissible.disj (canonical_project_atomic_shift_condition_with_ids_admissible
      cutoff (depths ·ₘ index) (leftCodes ·ₘ index) (rightCodes ·ₘ index)
      atomicBaseId (atomicBaseId + 1) (atomicBaseId + 2) (atomicBaseId + 3) (atomicBaseId + 4) (atomicBaseId + 6)
      hCutoff (hDepthAt index hIndex) (hLeftAt index hIndex) (hRightAt index hIndex)) (Formula.Admissible.disj (Formula.Admissible.exists_closeFreeAt _ _ <|
        Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (hEarlier firstPremise hFirstPremise)
              (hPremiseDomain firstPremise hFirstPremise)) (hDepthAgreement firstPremise hFirstPremise)) (Formula.Admissible.conj
            hLeftNegation hRightNegation)) (Formula.Admissible.disj (Formula.Admissible.exists_closeFreeAt _ _ <|
          Formula.Admissible.exists_closeFreeAt _ _ <|
            Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (hEarlier firstPremise hFirstPremise)
                    (hPremiseDomain firstPremise hFirstPremise)) (Formula.Admissible.conj (hEarlier secondPremise hSecondPremise)
                    (hPremiseDomain secondPremise hSecondPremise))) (Formula.Admissible.conj (hDepthAgreement
                    firstPremise hFirstPremise) (hDepthAgreement
                    secondPremise hSecondPremise))) (Formula.Admissible.conj
                hLeftImplication hRightImplication)) (Formula.Admissible.exists_closeFreeAt _ _ <|
          Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (hEarlier firstPremise hFirstPremise)
                (hPremiseDomain firstPremise hFirstPremise))
              hUniversalDepth) (Formula.Admissible.conj
              hLeftUniversal hRightUniversal))))
/-- 给定三条候选序列的同步平移轨迹条件是 admissible 公式。 -/
theorem canonical_project_formula_shift_trace_condition_admissible (cutoff entryDepth leftCode rightCode
      leftCodes rightCodes depths : SetTerm) (lastIndexId indexId firstPremiseId secondPremiseId
      atomicBaseId : FreeVarId) (hCutoff : Term.Admissible cutoff SetSort.set) (hEntryDepth : Term.Admissible entryDepth SetSort.set)
    (hLeftCode : Term.Admissible leftCode SetSort.set) (hRightCode : Term.Admissible rightCode SetSort.set) (hLeftCodes : Term.Admissible leftCodes SetSort.set)
    (hRightCodes : Term.Admissible rightCodes SetSort.set) (hDepths : Term.Admissible depths SetSort.set) :
    Formula.Admissible (canonical_project_formula_shift_trace_condition
        cutoff entryDepth leftCode rightCode
        leftCodes rightCodes depths
        lastIndexId indexId firstPremiseId secondPremiseId
        atomicBaseId) := by
  let index := x#indexId
  let lastIndex := x#lastIndexId
  have hIndex : Term.Admissible index SetSort.set :=
    set_variable_admissible indexId
  have hLastIndex : Term.Admissible lastIndex SetSort.set :=
    set_variable_admissible lastIndexId
  have hLeftDomain := domain_term_admissible leftCodes hLeftCodes
  have hRightDomain := domain_term_admissible rightCodes hRightCodes
  have hDepthDomain := domain_term_admissible depths hDepths
  have hLeftAt (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :=
    function_application_term_admissible
      leftCodes point hLeftCodes hPoint
  have hRightAt (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :=
    function_application_term_admissible
      rightCodes point hRightCodes hPoint
  have hDepthAt (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :=
    function_application_term_admissible
      depths point hDepths hPoint
  have hLine :
      Formula.Admissible ((index ∈ₘ domₘ(leftCodes)) ⟶ₘ
          canonical_project_formula_shift_line_condition_with_ids
            cutoff leftCodes rightCodes depths index
            firstPremiseId secondPremiseId atomicBaseId) :=
    Formula.Admissible.imp (membership_formula_admissible hIndex hLeftDomain) (canonical_project_formula_shift_line_condition_with_ids_admissible
        cutoff leftCodes rightCodes depths index
        firstPremiseId secondPremiseId atomicBaseId
        hCutoff hLeftCodes hRightCodes hDepths hIndex)
  have hTerminal :
      Formula.Admissible (∃ₘ[SetSort.set, lastIndexId], (((x#lastIndexId ∈ₘ domₘ(leftCodes)) ∧ₘ (domₘ(leftCodes) ≐ₘ Sₘ(x#lastIndexId))) ∧ₘ (((leftCode ≐ₘ
                (leftCodes ·ₘ x#lastIndexId)) ∧ₘ (rightCode ≐ₘ (rightCodes ·ₘ x#lastIndexId))) ∧ₘ (entryDepth ≐ₘ (depths ·ₘ x#lastIndexId))))) :=
    Formula.Admissible.exists_closeFreeAt _ _ <|
      Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
            hLastIndex hLeftDomain) (Formula.Admissible.equal hLeftDomain (successor_term_admissible
              lastIndex hLastIndex))) (Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.equal hLeftCode (hLeftAt lastIndex hLastIndex))
            (Formula.Admissible.equal hRightCode (hRightAt lastIndex hLastIndex))) (Formula.Admissible.equal hEntryDepth (hDepthAt lastIndex hLastIndex)))
  unfold canonical_project_formula_shift_trace_condition
  exact Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible hLeftCodes
            (nonempty_finite_sequence_space_term_admissible
              FormulaCodeₘ formula_code_set_term_admissible)) (membership_formula_admissible hRightCodes (nonempty_finite_sequence_space_term_admissible
              FormulaCodeₘ formula_code_set_term_admissible))) (membership_formula_admissible hDepths (nonempty_finite_sequence_space_term_admissible
            ωₘ omega_term_admissible))) (Formula.Admissible.conj (Formula.Admissible.equal
          hLeftDomain hRightDomain) (Formula.Admissible.equal
          hLeftDomain hDepthDomain))) (Formula.Admissible.conj (membership_formula_admissible (finite_numeral_term_admissible 0)
        hLeftDomain) (Formula.Admissible.conj (Formula.Admissible.forall_closeFreeAt
          SetSort.set indexId hLine)
        hTerminal))
/-- 显式内部编号的同步平移总分类条件是 admissible 公式。 -/
theorem canonical_project_formula_shift_code_condition_with_ids_admissible (cutoff entryDepth leftCode rightCode : SetTerm)
    (leftCodesId rightCodesId depthsId lastIndexId
      indexId firstPremiseId secondPremiseId
      atomicBaseId : FreeVarId) (hCutoff : Term.Admissible cutoff SetSort.set) (hEntryDepth : Term.Admissible entryDepth SetSort.set)
    (hLeftCode : Term.Admissible leftCode SetSort.set) (hRightCode : Term.Admissible rightCode SetSort.set) :
    Formula.Admissible (canonical_project_formula_shift_code_condition_with_ids
        cutoff entryDepth leftCode rightCode
        leftCodesId rightCodesId depthsId lastIndexId
        indexId firstPremiseId secondPremiseId
        atomicBaseId) := by
  let leftCodes := x#leftCodesId
  let rightCodes := x#rightCodesId
  let depths := x#depthsId
  have hLeftCodes : Term.Admissible leftCodes SetSort.set :=
    set_variable_admissible leftCodesId
  have hRightCodes : Term.Admissible rightCodes SetSort.set :=
    set_variable_admissible rightCodesId
  have hDepths : Term.Admissible depths SetSort.set :=
    set_variable_admissible depthsId
  unfold canonical_project_formula_shift_code_condition_with_ids
  exact Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
            hCutoff omega_term_admissible) (membership_formula_admissible
            hEntryDepth omega_term_admissible)) (Formula.Admissible.disj (Formula.Admissible.equal
            hCutoff hEntryDepth) (membership_formula_admissible
            hCutoff hEntryDepth))) (Formula.Admissible.conj (is_formula_code_formula_admissible hLeftCode) (is_formula_code_formula_admissible hRightCode)))
    (Formula.Admissible.exists_closeFreeAt _ _ <|
      Formula.Admissible.exists_closeFreeAt _ _ <|
        Formula.Admissible.exists_closeFreeAt _ _ <|
          canonical_project_formula_shift_trace_condition_admissible
            cutoff entryDepth leftCode rightCode
            leftCodes rightCodes depths
            lastIndexId indexId
            firstPremiseId secondPremiseId atomicBaseId
            hCutoff hEntryDepth hLeftCode hRightCode
            hLeftCodes hRightCodes hDepths)
/-! ## 任意长规范全称前缀 -/
/-- 规范全称前缀证书在一个位置上的剥离方程。 -/
def canonical_forall_prefix_step_condition (trace index : SetTerm) : SetFormula := (trace ·ₘ index) ≐ₘ
    forall_codeₘ(
      canonical_binder_variable_code_term index,
      trace ·ₘ Sₘ(index))

/-- 规范全称前缀的一步剥离方程是原子等式。 -/
theorem canonical_forall_prefix_step_condition_delta0
    (trace index : SetTerm) :
    Formula.IsDelta0 ProofT.set_levy_bound
      (canonical_forall_prefix_step_condition trace index) := by
  simpa [canonical_forall_prefix_step_condition] using
    Formula.IsDelta0.equal
      (trace ·ₘ index)
      (forall_codeₘ(
        canonical_binder_variable_code_term index,
        trace ·ₘ Sₘ(index)))
/-- 一个序列是从 `code` 逐层剥离到 `core` 的规范全称前缀轨迹。 -/
def canonical_forall_prefix_trace_condition (binderCount core code trace : SetTerm) (indexId : FreeVarId) :
    SetFormula := ((trace ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ (domₘ(trace) ≐ₘ Sₘ(binderCount))) ∧ₘ (((trace ·ₘ numₘ(0)) ≐ₘ code) ∧ₘ ((∀ₘ[SetSort.set, indexId],
          (x#indexId ∈ₘ binderCount) ⟶ₘ
            canonical_forall_prefix_step_condition
              trace (x#indexId)) ∧ₘ ((trace ·ₘ binderCount) ≐ₘ core)))
/-- 动态长度的规范全称前缀关系核心。 -/
def canonical_forall_prefix_code_condition_with_ids (binderCount core code : SetTerm) (traceId indexId : FreeVarId) :
    SetFormula := (((binderCount ∈ₘ ωₘ) ∧ₘ
      formula_codeₘ(core)) ∧ₘ
      formula_codeₘ(code)) ∧ₘ (∃ₘ[SetSort.set, traceId],
      canonical_forall_prefix_trace_condition
        binderCount core code (x#traceId) indexId)
/-- `code` 是在 `core` 外依次加入 `binderCount` 个规范全称量词所得的公式码。 -/
def canonical_forall_prefix_code_condition (binderCount core code : SetTerm) : SetFormula :=
  let traceId :=
    canonical_formula_classifier_fresh_base
      [binderCount, core, code]
  let indexId := traceId + 1
  canonical_forall_prefix_code_condition_with_ids
    binderCount core code traceId indexId
/-! ## 规范全称前缀的公共 admissibility -/
/-- 规范全称前缀的一步剥离方程是 admissible 公式。 -/
theorem canonical_forall_prefix_step_condition_admissible (trace index : SetTerm) (hTrace : Term.Admissible trace SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible (canonical_forall_prefix_step_condition trace index) := by
  have hCurrent :=
    function_application_term_admissible
      trace index hTrace hIndex
  have hNextIndex :=
    successor_term_admissible index hIndex
  have hNext :=
    function_application_term_admissible
      trace (Sₘ(index)) hTrace hNextIndex
  unfold canonical_forall_prefix_step_condition
  exact Formula.Admissible.equal hCurrent (universal_formula_code_term_admissible _ _ (canonical_binder_variable_code_term_admissible
        index hIndex)
      hNext)
/-- 规范全称前缀的一步剥离方程由轨迹与索引项证书直接计算。 -/
@[formula_check]
theorem canonical_forall_prefix_step_condition_check
    (trace index : SetTerm)
    (hTrace : Term.CheckCertificate trace SetSort.set)
    (hIndex : Term.CheckCertificate index SetSort.set) :
    Formula.CheckCertificate
      (canonical_forall_prefix_step_condition trace index) :=
  Formula.check_certificate_of_admissible
    (canonical_forall_prefix_step_condition_admissible
      trace index hTrace.admissible hIndex.admissible)
/-- 给定候选序列的规范全称前缀轨迹条件是 admissible 公式。 -/
theorem canonical_forall_prefix_trace_condition_admissible (binderCount core code trace : SetTerm) (indexId : FreeVarId)
    (hBinderCount : Term.Admissible binderCount SetSort.set) (hCore : Term.Admissible core SetSort.set) (hCode : Term.Admissible code SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set) :
    Formula.Admissible (canonical_forall_prefix_trace_condition
        binderCount core code trace indexId) := by
  let index : SetTerm := x#indexId
  have hIndex : Term.Admissible index SetSort.set :=
    set_variable_admissible indexId
  have hTraceDomain :=
    domain_term_admissible trace hTrace
  have hAt (point : SetTerm) (hPoint : Term.Admissible point SetSort.set) :
      Term.Admissible (trace ·ₘ point) SetSort.set :=
    function_application_term_admissible
      trace point hTrace hPoint
  have hStep :
      Formula.Admissible ((index ∈ₘ binderCount) ⟶ₘ
          canonical_forall_prefix_step_condition trace index) :=
    Formula.Admissible.imp (membership_formula_admissible hIndex hBinderCount) (canonical_forall_prefix_step_condition_admissible
        trace index hTrace hIndex)
  unfold canonical_forall_prefix_trace_condition
  exact Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible hTrace (nonempty_finite_sequence_space_term_admissible
          FormulaCodeₘ formula_code_set_term_admissible)) (Formula.Admissible.equal hTraceDomain (successor_term_admissible binderCount hBinderCount)))
    (Formula.Admissible.conj (Formula.Admissible.equal (hAt (numₘ(0)) (finite_numeral_term_admissible 0))
        hCode) (Formula.Admissible.conj (Formula.Admissible.forall_closeFreeAt
          SetSort.set indexId hStep) (Formula.Admissible.equal (hAt binderCount hBinderCount)
          hCore)))
/-- 显式内部编号的规范全称前缀分类条件是 admissible 公式。 -/
theorem canonical_forall_prefix_code_condition_with_ids_admissible (binderCount core code : SetTerm) (traceId indexId : FreeVarId)
    (hBinderCount : Term.Admissible binderCount SetSort.set) (hCore : Term.Admissible core SetSort.set) (hCode : Term.Admissible code SetSort.set) :
    Formula.Admissible (canonical_forall_prefix_code_condition_with_ids
        binderCount core code traceId indexId) := by
  let trace : SetTerm := x#traceId
  have hTrace : Term.Admissible trace SetSort.set :=
    set_variable_admissible traceId
  unfold canonical_forall_prefix_code_condition_with_ids
  exact Formula.Admissible.conj (Formula.Admissible.conj (Formula.Admissible.conj (membership_formula_admissible
          hBinderCount omega_term_admissible) (is_formula_code_formula_admissible hCore)) (is_formula_code_formula_admissible hCode))
    (Formula.Admissible.exists_closeFreeAt _ _ <|
      canonical_forall_prefix_trace_condition_admissible
        binderCount core code trace indexId
        hBinderCount hCore hCode hTrace)
/-! ## 可计算句法边界 -/
/-- 规范纯集合论公式码分类器的标准二元模板满足公共句法边界。 -/
theorem canonical_project_formula_code_template_admissible :
    Formula.Admissible (canonical_project_formula_code_condition (x#0) (x#1)) := by
  apply Formula.check_admissible_sound
  native_decide
/-- 规范公式深度平移关系的标准四元模板满足公共句法边界。 -/
theorem canonical_project_formula_shift_code_template_admissible :
    Formula.Admissible (canonical_project_formula_shift_code_condition (x#0) (x#1) (x#2) (x#3)) := by
  apply Formula.check_admissible_sound
  native_decide
/-- 规范全称前缀关系的标准三元模板满足公共句法边界。 -/
theorem canonical_forall_prefix_code_template_admissible :
    Formula.Admissible (canonical_forall_prefix_code_condition (x#0) (x#1) (x#2)) := by
  apply Formula.check_admissible_sound
  native_decide
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
