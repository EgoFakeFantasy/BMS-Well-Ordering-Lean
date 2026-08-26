import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.CodeNaming
import YesMetaZFC.Logic.FirstOrder.Hilbert.Compilation
import YesMetaZFC.Logic.FirstOrder.Hilbert.Diagonal
/-!
# FormalSystem quotation 上的关系图式对角引理
本模块采用 Foundation 的关系图式构造，不再要求对象语言中存在全局 `namer` 或
对角函数项。给定规范名称编码关系 `NameCode(x,n)`，编码级对角图定义为
`Diag(x,y) :⇔ ∃ n, NameCode(x,n) ∧ SubstCode(x,var,n,y)`。
对目标公式 `θ(y)` 的对角模板是 `∀ y, Diag(x,y) → θ(y)`。本模块从规范命名合同、
quotation substitution 正确性和替换规格唯一性内部推出图值与图唯一性，不再让调用方
携带这两项事实。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-! ## 关系式编码对角操作 -/
/-- 对角引理统一在内部 Hilbert 片段上读取目标公式。 -/
def fs_diagonal_target (body : SetFormula) : SetFormula :=
  Formula.hilbertize SetSort.set body
/-- 一个公式除指定代码变量外不含其他自由变量。 -/
def fs_only_code_variable_formula (id : FreeVarId) (formula : SetFormula) : Prop :=
  ∀ freeVariable, freeVariable ∈ Formula.freeSupport formula →
    freeVariable = (SetSort.set, id)
/-- 一个二元关系图只依赖源代码变量和结果变量。 -/
def fs_only_graph_variables (sourceId resultId : FreeVarId) (formula : SetFormula) : Prop :=
  ∀ freeVariable, freeVariable ∈ Formula.freeSupport formula →
    freeVariable = (SetSort.set, sourceId) ∨
      freeVariable = (SetSort.set, resultId)
/-! ## 内部新鲜编号与对角理论 -/
/--
`code_substitution_spec` 内部使用 `310`、`311` 两个保留编号。对角层从公共代码变量
之上统一分配三个内部编号，确保源、结果和名称见证都不会被这些 binder 捕获。
-/
def fs_diagonal_source_id (codeId : FreeVarId) : FreeVarId :=
  Nat.max codeId 311 + 1
/-- 对角图的结果变量编号。 -/
def fs_diagonal_result_id (codeId : FreeVarId) : FreeVarId :=
  fs_diagonal_source_id codeId + 1
/-- 对角图的规范名称见证编号。 -/
def fs_diagonal_name_id (codeId : FreeVarId) : FreeVarId :=
  fs_diagonal_source_id codeId + 2
/--
构造层把背景理论与规范命名理论的 Hilbert 归约像合并。
编码层自然演绎证书先编译到 `Theory.hilbertize code_naming_theory`，随后与用户背景
理论合并。最终公共接口再通过 `fs_extends_code_naming` 与 Hilbert cut 消去该临时层。
-/
def fs_diagonal_theory (theory : SetTheory) : SetTheory :=
  Theory.union (Theory.hilbertize SetSort.set code_naming_theory)
    theory
/--
目标理论承载 Gödel quotation 编码层的精确条件。
这里不要求编码公理逐字属于目标理论；只要求目标理论能在 Hilbert 系统中证明
`code_naming_theory` 的 Hilbert 归约像。该条件正是消去 `fs_diagonal_theory`
临时扩张所需的全部数学内容。
-/
def fs_extends_code_naming (theory : SetTheory) : Prop :=
  Theory.hilbert_extends theory (Theory.hilbertize SetSort.set code_naming_theory)
/-- 逐字包含 Hilbert 化编码理论时，自动得到编码承载条件。 -/
theorem fs_extends_code_naming_of_subset
    {theory : SetTheory} (hSubset :
      ∀ formula,
        Theory.hilbertize SetSort.set code_naming_theory formula →
          theory formula) :
    fs_extends_code_naming theory :=
  Theory.hilbert_extends_of_subset hSubset
/--
目标理论一旦承载编码层，就在 Hilbert 意义下扩张完整的临时对角理论。
编码分支由承载条件处理，背景理论分支由反身性处理。
-/
theorem fs_extends_diagonal_theory
    {theory : SetTheory} (hCodeNaming : fs_extends_code_naming theory) :
    Theory.hilbert_extends theory (fs_diagonal_theory theory) :=
  Theory.hilbert_extends_union hCodeNaming (Theory.hilbert_extends_refl theory)
/-- 把临时对角理论中的 Hilbert 推导 cut 回目标理论。 -/
theorem fs_diagonal_derives_in_theory
    {theory : SetTheory} {formula : SetFormula} (hCodeNaming : fs_extends_code_naming theory) (hDerives :
      HilbertDerives (fs_diagonal_theory theory) formula) :
    HilbertDerives theory formula :=
  hDerives.theory_cut (fs_extends_diagonal_theory hCodeNaming)
/-! ## 关系式编码对角操作 -/
/-- 把原目标的代码变量改名为关系图的结果变量。 -/
def fs_diagonal_body (codeId : FreeVarId) (body : SetFormula) : SetFormula :=
  Formula.substituteFree SetSort.set codeId (x#(fs_diagonal_result_id codeId)) (fs_diagonal_target body)
/--
由规范名称编码关系与既有 `code_substitution_spec` 组成的真实编码对角图。
名称关系固定为 `canonical_name_code_spec`；三个自由编号都由上一节的统一分配器
生成，调用方不能替换为任意关系，也不需要再证明保留编号新鲜性。
-/
def fs_code_diagonal_graph (codeId : FreeVarId) : SetFormula :=
  ∃ₘ[SetSort.set, fs_diagonal_name_id codeId], ((x#(fs_diagonal_name_id codeId) ≐ₘ
        name_codeₘ(x#(fs_diagonal_source_id codeId))) ∧ₘ
      code_substitution_spec (x#(fs_diagonal_source_id codeId)) (Numbered.named_variable_code (free_name (fs_diagonal_source_id codeId)))
        (x#(fs_diagonal_name_id codeId)) (x#(fs_diagonal_result_id codeId)))
/-- 源变量实例化后、尚未消去规范名称存在见证的对角图体。 -/
private def fs_diagonal_source_graph_body (codeId : FreeVarId) (templateName : SetTerm) : SetFormula := ((x#(fs_diagonal_name_id codeId) ≐ₘ
      name_codeₘ(templateName)) ∧ₘ
    code_substitution_spec
      templateName (Numbered.named_variable_code (free_name (fs_diagonal_source_id codeId))) (x#(fs_diagonal_name_id codeId))
      (x#(fs_diagonal_result_id codeId)))
/-- 编码对角图的 Hilbert 归约。 -/
def fs_code_diagonal_graph_core (codeId : FreeVarId) : SetFormula :=
  fs_diagonal_target (fs_code_diagonal_graph codeId)
/-- Foundation 式 `∀ y, Diag(x,y) → θ(y)` 对角模板。 -/
def fs_diagonal_template (codeId : FreeVarId) (body : SetFormula) : SetFormula :=
  hilbert_relational_diagonal_template SetSort.set (fs_diagonal_result_id codeId) (fs_code_diagonal_graph_core codeId) (fs_diagonal_body codeId body)
/-- 对角模板应用到表示其自身 quotation 值的规范闭项。 -/
def fs_diagonal_fixed_point (codeId : FreeVarId) (templateName : SetTerm) (body : SetFormula) : SetFormula :=
  hilbert_relational_diagonal_fixed_point SetSort.set (fs_diagonal_source_id codeId) (fs_diagonal_result_id codeId) (fs_code_diagonal_graph_core codeId)
    templateName (fs_diagonal_body codeId body)
/-! ## Proof-carrying 对角数据 -/
/--
FormalSystem 关系对角化的完整数据。
这是内部证明证书，不再作为公共对角引理的调用接口。图的语法、内部变量和编码理论
扩张都由本模块固定；规范 quotation 与固定点 quotation 由后文的 canonical 构造器
自动生成。背景理论只需声明其成员均为句子，由此统一推出所有内部编号的新鲜性。
-/
structure FsDiagonalizationData (theory : SetTheory) (codeId : FreeVarId) (body : SetFormula) where
  h_body_admissible : Formula.Admissible body
  h_body_only_code_variable : fs_only_code_variable_formula codeId body
  template_naming :
    CanonicalFormulaNameData (fs_diagonal_template codeId body)
  fixed_point_code : SetTerm
  h_theory_sentence :
    ∀ formula, theory formula → Formula.Sentence formula
  h_fixed_point_quote :
    Numbered.quote? (fs_diagonal_fixed_point codeId
          template_naming.name_term body) =
      some fixed_point_code
namespace FsDiagonalizationData
/-! ## 公共投影 -/
abbrev diagonal_graph
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (_data : FsDiagonalizationData theory codeId body) : SetFormula :=
  fs_code_diagonal_graph codeId
abbrev core_graph
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (_data : FsDiagonalizationData theory codeId body) : SetFormula :=
  fs_code_diagonal_graph_core codeId
/-- 对角模板使用的内部源变量。 -/
abbrev source_id
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (_data : FsDiagonalizationData theory codeId body) : FreeVarId :=
  fs_diagonal_source_id codeId
/-- 对角模板量化的内部结果变量。 -/
abbrev result_id
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (_data : FsDiagonalizationData theory codeId body) : FreeVarId :=
  fs_diagonal_result_id codeId
/-- 对角图内部的规范名称见证变量。 -/
abbrev name_id
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (_data : FsDiagonalizationData theory codeId body) : FreeVarId :=
  fs_diagonal_name_id codeId
/-- 对角模板的对象 quotation。 -/
abbrev template_code
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) : SetTerm :=
  data.template_naming.formula_code
/-- 表示模板 quotation 值的规范闭项。 -/
abbrev template_name
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) : SetTerm :=
  data.template_naming.name_term
/-- 规范闭项自身的对象 quotation。 -/
abbrev template_name_code
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) : SetTerm :=
  data.template_naming.name_code
/-- 对角模板的规范 token quotation。 -/
abbrev template_tokens
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) : List Nat :=
  data.template_naming.tokens
/-- 对角模板 quotation 等式由规范命名数据直接给出。 -/
theorem h_template_quote
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.quote? (fs_diagonal_template codeId body) =
      some data.template_code :=
  data.template_naming.h_formula_code
/-- 规范名称 quotation 等式由规范命名数据直接给出。 -/
theorem h_template_name_quote
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.quote_term_with? free_name [] data.template_name =
      some data.template_name_code :=
  data.template_naming.h_name_code
@[simp]
theorem h_template_name_admissible
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Term.Admissible data.template_name SetSort.set :=
  data.template_naming.name_term_admissible
@[simp]
theorem h_template_name_freeSupport_nil
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Term.freeSupport data.template_name = [] :=
  data.template_naming.name_term_freeSupport_nil
/-- 固定点 token quotation是模板 token 的规范命名实例。 -/
theorem fixed_point_tokens
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.quote_tokens? (fs_diagonal_fixed_point codeId data.template_name body) =
      some (substitute_tokens data.template_tokens (variable_token (free_name data.source_id)) (canonical_name_tokens data.template_tokens)) := by
  simpa [fs_diagonal_fixed_point,
    hilbert_relational_diagonal_fixed_point] using (data.template_naming.named_instance_tokens data.source_id)
/-- 模板 quotation 的代码边界。 -/
theorem template_code_boundary
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.CodeBoundary data.template_code :=
  Numbered.quote?_code_boundary data.h_template_quote
/-- 模板 quotation 的项检查证书由数据边界自动投影。 -/
@[term_check]
theorem template_code_check
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula}
    (data : FsDiagonalizationData theory codeId body) :
    Term.CheckCertificate data.template_code SetSort.set :=
  data.template_code_boundary.check_certificate
/-- 模板 quotation 的规范闭项本身也是 closed 代码边界项。 -/
theorem template_name_boundary
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.CodeBoundary data.template_name :=
  ⟨data.h_template_name_admissible,
    data.h_template_name_freeSupport_nil⟩
/-- 模板规范名称的项检查证书由数据边界自动投影。 -/
@[term_check]
theorem template_name_check
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula}
    (data : FsDiagonalizationData theory codeId body) :
    Term.CheckCertificate data.template_name SetSort.set :=
  data.template_name_boundary.check_certificate
/-- 模板规范名称 quotation 的代码边界。 -/
theorem template_name_code_boundary
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.CodeBoundary data.template_name_code :=
  Numbered.quote_term_with?_code_boundary
    free_name [] data.h_template_name_quote
/-- 模板规范名称 quotation 的项检查证书由数据边界自动投影。 -/
@[term_check]
theorem template_name_code_check
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula}
    (data : FsDiagonalizationData theory codeId body) :
    Term.CheckCertificate data.template_name_code SetSort.set :=
  data.template_name_code_boundary.check_certificate
/-- 固定点 quotation 的代码边界。 -/
theorem fixed_point_code_boundary
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.CodeBoundary data.fixed_point_code :=
  Numbered.quote?_code_boundary data.h_fixed_point_quote
/-- 固定点 quotation 的项检查证书由数据边界自动投影。 -/
@[term_check]
theorem fixed_point_code_check
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula}
    (data : FsDiagonalizationData theory codeId body) :
    Term.CheckCertificate data.fixed_point_code SetSort.set :=
  data.fixed_point_code_boundary.check_certificate
/-! ## 内部编号互异性 -/
@[simp]
theorem fs_diagonal_code_ne_source (codeId : FreeVarId) :
    codeId ≠ fs_diagonal_source_id codeId := by
  exact Nat.ne_of_lt <| by
    simpa [fs_diagonal_source_id] using
      Nat.lt_succ_of_le (Nat.le_max_left codeId 311)
@[simp]
theorem fs_diagonal_code_ne_result (codeId : FreeVarId) :
    codeId ≠ fs_diagonal_result_id codeId := by
  have hSource :
      codeId < fs_diagonal_source_id codeId :=
    Nat.lt_of_not_ge (fun h =>
      fs_diagonal_code_ne_source codeId (Nat.le_antisymm h (Nat.le_of_lt <| by
            simpa [fs_diagonal_source_id] using
              Nat.lt_succ_of_le (Nat.le_max_left codeId 311))).symm)
  exact Nat.ne_of_lt <| by
    simpa [fs_diagonal_result_id] using
      Nat.lt_trans hSource (Nat.lt_succ_self (fs_diagonal_source_id codeId))
@[simp]
theorem fs_diagonal_source_ne_result (codeId : FreeVarId) :
    fs_diagonal_source_id codeId ≠
      fs_diagonal_result_id codeId := by
  simp [fs_diagonal_result_id]
@[simp]
theorem fs_diagonal_name_ne_result (codeId : FreeVarId) :
    fs_diagonal_name_id codeId ≠
      fs_diagonal_result_id codeId := by
  simp [fs_diagonal_name_id, fs_diagonal_result_id]
@[simp]
theorem fs_diagonal_source_ne_name (codeId : FreeVarId) :
    fs_diagonal_source_id codeId ≠
      fs_diagonal_name_id codeId := by
  simp [fs_diagonal_name_id]
@[simp]
theorem fs_diagonal_source_ne_reserved (codeId : FreeVarId) :
    fs_diagonal_source_id codeId ≠ 310 ∧
      fs_diagonal_source_id codeId ≠ 311 := by
  have h311 :
      311 < fs_diagonal_source_id codeId := by
    simpa [fs_diagonal_source_id] using
      Nat.lt_succ_of_le (Nat.le_max_right codeId 311)
  exact ⟨Nat.ne_of_gt (Nat.lt_trans (by omega) h311),
    Nat.ne_of_gt h311⟩
@[simp]
theorem fs_diagonal_result_ne_reserved (codeId : FreeVarId) :
    fs_diagonal_result_id codeId ≠ 310 ∧
      fs_diagonal_result_id codeId ≠ 311 := by
  have h311 :
      311 < fs_diagonal_result_id codeId := by
    exact Nat.lt_trans (Nat.lt_succ_of_le (Nat.le_max_right codeId 311)) (by
        simp [fs_diagonal_result_id, fs_diagonal_source_id])
  exact ⟨Nat.ne_of_gt (Nat.lt_trans (by omega) h311),
    Nat.ne_of_gt h311⟩
@[simp]
theorem fs_diagonal_name_ne_reserved (codeId : FreeVarId) :
    fs_diagonal_name_id codeId ≠ 310 ∧
      fs_diagonal_name_id codeId ≠ 311 := by
  have h311 :
      311 < fs_diagonal_name_id codeId := by
    exact Nat.lt_trans (Nat.lt_succ_of_le (Nat.le_max_right codeId 311)) (by
        simp [fs_diagonal_name_id, fs_diagonal_source_id])
  exact ⟨Nat.ne_of_gt (Nat.lt_trans (by omega) h311),
    Nat.ne_of_gt h311⟩
@[simp]
theorem fs_diagonal_source_ne_310 (codeId : FreeVarId) :
    fs_diagonal_source_id codeId ≠ 310 := (fs_diagonal_source_ne_reserved codeId).1
@[simp]
theorem fs_diagonal_source_ne_311 (codeId : FreeVarId) :
    fs_diagonal_source_id codeId ≠ 311 := (fs_diagonal_source_ne_reserved codeId).2
@[simp]
theorem fs_diagonal_result_ne_310 (codeId : FreeVarId) :
    fs_diagonal_result_id codeId ≠ 310 := (fs_diagonal_result_ne_reserved codeId).1
@[simp]
theorem fs_diagonal_result_ne_311 (codeId : FreeVarId) :
    fs_diagonal_result_id codeId ≠ 311 := (fs_diagonal_result_ne_reserved codeId).2
@[simp]
theorem fs_diagonal_name_ne_310 (codeId : FreeVarId) :
    fs_diagonal_name_id codeId ≠ 310 := (fs_diagonal_name_ne_reserved codeId).1
@[simp]
theorem fs_diagonal_name_ne_311 (codeId : FreeVarId) :
    fs_diagonal_name_id codeId ≠ 311 := (fs_diagonal_name_ne_reserved codeId).2
/-! ## 固定对角图的语法边界 -/
/-- 固定的编码对角图对每个公共代码变量编号都自动满足良构性。 -/
theorem fs_code_diagonal_graph_admissible (codeId : FreeVarId) :
    Formula.Admissible (fs_code_diagonal_graph codeId) := by
  let source : SetTerm := x#(fs_diagonal_source_id codeId)
  let result : SetTerm := x#(fs_diagonal_result_id codeId)
  let name : SetTerm := x#(fs_diagonal_name_id codeId)
  have hSource : Term.Admissible source SetSort.set :=
    set_variable_admissible _
  have hResult : Term.Admissible result SetSort.set :=
    set_variable_admissible _
  have hName : Term.Admissible name SetSort.set :=
    set_variable_admissible _
  have hNameValue :=
    canonical_name_code_term_admissible source hSource
  have hNameEquality :
      Formula.Admissible (name ≐ₘ name_codeₘ(source)) :=
    ⟨FormulaWellFormed.equal hName.1 hNameValue.1,
      FormulaScoped.equal hName.2 hNameValue.2⟩
  have hVariableCode :
      Term.Admissible (Numbered.named_variable_code (free_name (fs_diagonal_source_id codeId)))
        SetSort.set :=
    variable_code_term_admissible _ (finite_numeral_term_admissible _)
  have hSubstitution :=
    code_substitution_spec_admissible
      source (Numbered.named_variable_code (free_name (fs_diagonal_source_id codeId)))
      name result hSource hVariableCode hName hResult
  have hBody := Formula.Admissible.conj hNameEquality hSubstitution
  simpa [fs_code_diagonal_graph, source, result, name] using
    Formula.Admissible.exists_closeFreeAt SetSort.set (fs_diagonal_name_id codeId) hBody
/-- 固定编码图关闭名称见证后，只留下源代码变量和结果代码变量。 -/
theorem fs_code_diagonal_graph_only_variables (codeId : FreeVarId) :
    fs_only_graph_variables (fs_diagonal_source_id codeId) (fs_diagonal_result_id codeId) (fs_code_diagonal_graph codeId) := by
  rintro ⟨sort, id⟩ hMember
  cases sort
  by_cases hSource : id = fs_diagonal_source_id codeId
  · subst id
    exact Or.inl rfl
  by_cases hResult : id = fs_diagonal_result_id codeId
  · subst id
    exact Or.inr rfl
  exfalso
  have hNumeralClose (closedId depth number : Nat) :
      Term.closeFreeAt SetSort.set closedId depth (numₘ(number)) =
        numₘ(number) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set closedId depth (numₘ(number)) (finite_numeral_term_admissible number).2 (by rw [finite_numeral_term_freeSupport]; simp)
  have hResultName :
      fs_diagonal_result_id codeId ≠ fs_diagonal_name_id codeId := (fs_diagonal_name_ne_result codeId).symm
  simp [fs_code_diagonal_graph, code_substitution_spec,
    substitution_piece_condition, Formula.closeFreeAt,
    Formula.next_depth, Term.closeFreeAt, Formula.freeSupport,
    Term.freeSupport, Term.freeSupportList, hSource, hResult,
    hResultName, hNumeralClose,
    finite_numeral_term_freeSupport] at hMember
/-- 目标公式良构时，关系图式对角模板的 quotation 也自动有定义。 -/
theorem fs_diagonal_template_admissible (codeId : FreeVarId) (body : SetFormula) (hBody : Formula.Admissible body) :
    Formula.Admissible (fs_diagonal_template codeId body) := by
  have hGraph :=
    fs_code_diagonal_graph_admissible codeId
  have hGraphCore :
      Formula.Admissible (fs_code_diagonal_graph_core codeId) := by
    simpa [fs_code_diagonal_graph_core, fs_diagonal_target] using (show Formula.Admissible (Formula.hilbertize SetSort.set (fs_code_diagonal_graph codeId)) from
        ⟨Numbered.hilbertize_well_formed SetSort.set hGraph.1,
          Numbered.hilbertize_scoped SetSort.set hGraph.2⟩)
  have hTarget :
      Formula.Admissible (fs_diagonal_target body) := by
    simpa [fs_diagonal_target] using (show Formula.Admissible (Formula.hilbertize SetSort.set body) from
        ⟨Numbered.hilbertize_well_formed SetSort.set hBody.1,
          Numbered.hilbertize_scoped SetSort.set hBody.2⟩)
  have hRenamed :
      Formula.Admissible (fs_diagonal_body codeId body) := by
    simpa [fs_diagonal_body] using
      Formula.Admissible.substituteFree SetSort.set codeId
        hTarget (set_variable_admissible (fs_diagonal_result_id codeId))
  have hImplication :=
    Formula.Admissible.imp hGraphCore hRenamed
  simpa [fs_diagonal_template,
    hilbert_relational_diagonal_template] using
    Formula.Admissible.forall_closeFreeAt SetSort.set (fs_diagonal_result_id codeId) hImplication
/-! ## 自由变量与良构性 -/
/-- Hilbert 归约后的目标公式仍然 admissible。 -/
theorem target_admissible
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Formula.Admissible (fs_diagonal_target body) := by
  simpa [fs_diagonal_target] using (show Formula.Admissible (Formula.hilbertize SetSort.set body) from
      ⟨Numbered.hilbertize_well_formed
          SetSort.set data.h_body_admissible.1,
        Numbered.hilbertize_scoped
          SetSort.set data.h_body_admissible.2⟩)
/-- 改名后的固定点目标体仍然 admissible。 -/
theorem diagonal_body_admissible
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Formula.Admissible (fs_diagonal_body codeId body) := by
  simpa [fs_diagonal_body] using
    Formula.Admissible.substituteFree SetSort.set codeId
      data.target_admissible (set_variable_admissible data.result_id)
/-- Hilbert 归约不会引入新的自由变量。 -/
theorem target_only_code_variable
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    fs_only_code_variable_formula codeId (fs_diagonal_target body) := by
  intro freeVariable hMember
  apply data.h_body_only_code_variable freeVariable
  exact (Formula.mem_freeSupport_hilbertize_iff (σ := signature) SetSort.set freeVariable body).mp <| by
      simpa [fs_diagonal_target] using hMember
/-- 改名替换消去原目标的公共代码变量。 -/
theorem diagonal_body_code_fresh
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (_data : FsDiagonalizationData theory codeId body) : (SetSort.set, codeId) ∉
      Formula.freeSupport (fs_diagonal_body codeId body) := by
  apply Formula.target_not_mem_freeSupport_substituteFree
  simp [Term.freeSupport]
/-- 改名后的目标也不含对角图的内部源变量。 -/
theorem diagonal_body_source_fresh
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) : (SetSort.set, data.source_id) ∉
      Formula.freeSupport (fs_diagonal_body codeId body) := by
  have hReplacementFresh : (SetSort.set, data.source_id) ∉
        Term.freeSupport (x#data.result_id) := by
    intro hMember
    change (SetSort.set, data.source_id) ∈
        [(SetSort.set, data.result_id)] at hMember
    have hEqual : (SetSort.set, data.source_id) = (SetSort.set, data.result_id) := by
      exact List.mem_singleton.mp hMember
    exact fs_diagonal_source_ne_result codeId (congrArg Prod.snd hEqual)
  have hTargetFresh : (SetSort.set, data.source_id) ∉
        Formula.freeSupport (fs_diagonal_target body) := by
    intro hMember
    have hEq := data.target_only_code_variable (SetSort.set, data.source_id) hMember
    exact fs_diagonal_code_ne_source codeId (congrArg Prod.snd hEq).symm
  exact Formula.not_mem_freeSupport_substituteFree (SetSort.set, data.source_id) SetSort.set codeId (x#data.result_id) (fs_diagonal_target body)
    hReplacementFresh hTargetFresh
/-- 原目标中结果变量新鲜，因此改名后再实例化等于直接实例化代码变量。 -/
theorem target_result_fresh
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) : (SetSort.set, data.result_id) ∉
      Formula.freeSupport (fs_diagonal_target body) := by
  intro hMember
  have hEq := data.target_only_code_variable (SetSort.set, data.result_id) hMember
  have : data.result_id = codeId := congrArg Prod.snd hEq
  exact fs_diagonal_code_ne_result codeId this.symm
/-- 改名后的目标只依赖结果变量。 -/
theorem diagonal_body_only_result
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    fs_only_code_variable_formula data.result_id (fs_diagonal_body codeId body) := by
  intro freeVariable hMember
  by_cases hResult : freeVariable = (SetSort.set, data.result_id)
  · exact hResult
  · by_cases hSource : freeVariable = (SetSort.set, codeId)
    · subst freeVariable
      exact (data.diagonal_body_code_fresh hMember).elim
    · have hReplacementFresh :
          freeVariable ∉ Term.freeSupport (x#data.result_id) := by
        simpa [Term.freeSupport] using hResult
      have hTargetFresh :
          freeVariable ∉ Formula.freeSupport (fs_diagonal_target body) := by
        intro hTargetMember
        exact hSource (data.target_only_code_variable freeVariable hTargetMember)
      exact ((Formula.not_mem_freeSupport_substituteFree
        freeVariable SetSort.set codeId (x#data.result_id) (fs_diagonal_target body) hReplacementFresh hTargetFresh) hMember).elim
/-- Hilbert 归约后的编码图仍只依赖源变量与结果变量。 -/
theorem core_graph_only_variables
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    fs_only_graph_variables data.source_id data.result_id
      data.core_graph := by
  intro freeVariable hMember
  apply fs_code_diagonal_graph_only_variables codeId freeVariable
  exact (Formula.mem_freeSupport_hilbertize_iff (σ := signature) SetSort.set freeVariable data.diagonal_graph).mp <| by
      simpa [core_graph, fs_code_diagonal_graph_core,
        fs_diagonal_target] using hMember
/-- 对角模板只留下自动生成的内部源代码变量。 -/
theorem template_only_source_variable
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    fs_only_code_variable_formula data.source_id (fs_diagonal_template codeId body) := by
  intro freeVariable hMember
  let implication :=
    Formula.imp data.core_graph (fs_diagonal_body codeId body)
  have hClosedMember :
      freeVariable ∈ Formula.freeSupport (Formula.closeFreeAt SetSort.set data.result_id 0 implication) := by
    simpa [fs_diagonal_template,
      hilbert_relational_diagonal_template, implication,
      Formula.freeSupport] using hMember
  by_cases hSource :
      freeVariable = (SetSort.set, data.source_id)
  · exact hSource
  · have hNeResult :
        freeVariable ≠ (SetSort.set, data.result_id) := by
      intro hEq
      subst freeVariable
      exact (Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set data.result_id 0 implication) hClosedMember
    have hGraphFresh :
        freeVariable ∉ Formula.freeSupport data.core_graph := by
      intro hGraphMember
      rcases data.core_graph_only_variables
          freeVariable hGraphMember with hGraphSource | hGraphResult
      · exact hSource hGraphSource
      · exact hNeResult hGraphResult
    have hBodyFresh :
        freeVariable ∉ Formula.freeSupport (fs_diagonal_body codeId body) := by
      intro hBodyMember
      exact hNeResult (data.diagonal_body_only_result freeVariable hBodyMember)
    have hImplicationFresh :
        freeVariable ∉ Formula.freeSupport implication := by
      simp [implication, Formula.freeSupport, hGraphFresh, hBodyFresh]
    exact ((Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      freeVariable SetSort.set data.result_id 0 implication
      hImplicationFresh) hClosedMember).elim
/-- 固定点候选满足公共公式良构性边界。 -/
theorem fixed_point_admissible
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Formula.Admissible (fs_diagonal_fixed_point codeId data.template_name body) := by
  exact Formula.Admissible.substituteFree SetSort.set data.source_id
    data.template_naming.h_formula_admissible
    data.h_template_name_admissible
/-- 模板应用规范闭项名称后成为无自由变量公式。 -/
theorem fixed_point_freeSupport_nil
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Formula.freeSupport (fs_diagonal_fixed_point codeId
          data.template_name body) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro freeVariable hMember
  by_cases hSource :
      freeVariable = (SetSort.set, data.source_id)
  · subst freeVariable
    exact (Formula.target_not_mem_freeSupport_substituteFree
      SetSort.set data.source_id data.template_name (fs_diagonal_template codeId body) (by rw [data.h_template_name_freeSupport_nil]; simp)) hMember
  · have hNameFresh :
        freeVariable ∉ Term.freeSupport data.template_name := by
      rw [data.h_template_name_freeSupport_nil]
      simp
    have hTemplateFresh :
        freeVariable ∉ Formula.freeSupport (fs_diagonal_template codeId body) := by
      intro hTemplateMember
      exact hSource (data.template_only_source_variable
          freeVariable hTemplateMember)
    exact (Formula.not_mem_freeSupport_substituteFree
      freeVariable SetSort.set data.source_id data.template_name (fs_diagonal_template codeId body)
      hNameFresh hTemplateFresh) hMember
/-- FormalSystem 关系对角固定点是真正的句子。 -/
theorem fixed_point_sentence
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Formula.Sentence (fs_diagonal_fixed_point codeId data.template_name body) :=
  ⟨data.fixed_point_admissible, data.fixed_point_freeSupport_nil⟩
/-! ## 规范名称与替换图的内部计算 -/
/-- 模板 quotation 代码在对象理论中等于其规范闭项名称。 -/
theorem template_code_value_derives
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ⊢ₘ[code_naming_theory]
      data.template_code ≐ₘ data.template_name := by
  apply code_naming_weaken_godel_quotation
  simpa [template_name,
    CanonicalFormulaNameData.name_term,
    canonical_name_term] using (quote?_eq_standard_token_sequence
      data.template_naming.h_formula_tokens
      data.h_template_quote)
/-- 模板规范名称的 quotation 是对象命名函数在模板代码值处的真实值。 -/
theorem template_name_code_value_derives
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ⊢ₘ[code_naming_theory]
      data.template_name_code ≐ₘ
        name_codeₘ(data.template_name) := by
  simpa [template_name,
    template_name_code,
    CanonicalFormulaNameData.name_term,
    canonical_name_term,
    data.template_naming.name_code_eq_value] using (canonical_name_code_value_derives data.template_tokens)
/-- 对角替换使用的变量符号代码边界。 -/
theorem diagonal_variable_code_boundary
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Numbered.CodeBoundary (Numbered.named_variable_code (free_name data.source_id)) :=
  ⟨variable_code_term_admissible (numₘ(free_name data.source_id)) (finite_numeral_term_admissible (free_name data.source_id)),
    named_variable_code_freeSupport (free_name data.source_id)⟩
/-- 对角替换变量代码的项检查证书由数据边界自动投影。 -/
@[term_check]
theorem diagonal_variable_code_check
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula}
    (data : FsDiagonalizationData theory codeId body) :
    Term.CheckCertificate
      (Numbered.named_variable_code (free_name data.source_id))
      SetSort.set :=
  data.diagonal_variable_code_boundary.check_certificate
/--
真实固定点 quotation 满足以模板规范名称为源、以规范名称 quotation 为替换项的
编码替换规格。
-/
theorem fixed_point_substitution_spec_derives
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ⊢ₘ[code_naming_theory]
      code_substitution_spec
        data.template_name (Numbered.named_variable_code (free_name data.source_id))
        data.template_name_code
        data.fixed_point_code := by
  have hQuoted :
      ⊢ₘ[godel_quotation_theory]
        code_substitution_spec
          data.template_code (Numbered.named_variable_code (free_name data.source_id))
          data.template_name_code
          data.fixed_point_code := by
    simpa [fs_diagonal_fixed_point,
      hilbert_relational_diagonal_fixed_point] using (quote?_substitution_result_spec_derives (formula := fs_diagonal_template codeId body)
        (sourceTokens := data.template_tokens) (sourceCode := data.template_code) (replacement := data.template_name) (replacementTokens :=
          canonical_name_tokens data.template_tokens) (replacementCode := data.template_name_code) (targetCode := data.fixed_point_code)
        data.source_id
        data.template_naming.h_formula_tokens
        data.h_template_quote
        data.template_naming.name_term_tokens
        data.h_template_name_quote
        data.h_fixed_point_quote)
  have hQuoted' :
      ⊢ₘ[code_naming_theory]
        code_substitution_spec
          data.template_code (Numbered.named_variable_code (free_name data.source_id))
          data.template_name_code
          data.fixed_point_code :=
    code_naming_weaken_godel_quotation hQuoted
  have hVariableRefl :
      ⊢ₘ[code_naming_theory]
        Numbered.named_variable_code (free_name data.source_id) ≐ₘ
          Numbered.named_variable_code (free_name data.source_id) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set)
      (term := Numbered.named_variable_code (free_name data.source_id))
      (hTermCheck := data.diagonal_variable_code_boundary.check_certificate)
  have hReplacementRefl :
      ⊢ₘ[code_naming_theory]
        data.template_name_code ≐ₘ data.template_name_code :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set)
      (term := data.template_name_code)
      (hTermCheck := data.template_name_code_boundary.check_certificate)
  have hCandidateRefl :
      ⊢ₘ[code_naming_theory]
        data.fixed_point_code ≐ₘ data.fixed_point_code :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set)
      (term := data.fixed_point_code)
      (hTermCheck := data.fixed_point_code_boundary.check_certificate)
  exact code_substitution_spec_congr_of_code_equalities
    data.template_code data.template_name (Numbered.named_variable_code (free_name data.source_id)) (Numbered.named_variable_code (free_name data.source_id))
    data.template_name_code data.template_name_code
    data.fixed_point_code data.fixed_point_code
    data.template_code_boundary data.template_name_boundary
    data.diagonal_variable_code_boundary
    data.diagonal_variable_code_boundary
    data.template_name_code_boundary
    data.template_name_code_boundary
    data.fixed_point_code_boundary data.fixed_point_code_boundary
    data.template_code_value_derives
    hVariableRefl hReplacementRefl hCandidateRefl hQuoted'
/--
模板规范名称、其具名源变量代码和规范名称 quotation 自动满足 substitution 前置条件。
quotation 闭包先给出模板语法代码处的前置条件，再沿
`template_code = template_name` 输运到对象语言实际使用的规范闭项。
-/
theorem template_substitution_precondition_derives
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ⊢ₘ[code_naming_theory]
      code_substitution_precondition
        data.template_name (Numbered.named_variable_code (free_name data.source_id))
        data.template_name_code := by
  let boundCode :=
    Numbered.named_variable_code (free_name data.source_id)
  let preconditionBody : SetFormula :=
    code_substitution_precondition (x#data.source_id) boundCode data.template_name_code
  have hFixed (parameter : FreeVarId) (substitute term : SetTerm) (hTerm : Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set parameter substitute term = term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter substitute term (by
        rw [hTerm.2]
        simp)
  have hQuoted :
      ⊢ₘ[code_naming_theory]
        code_substitution_precondition
          data.template_code boundCode data.template_name_code :=
    code_naming_weaken_godel_quotation <|
      quote?_code_substitution_precondition_derives
        data.source_id data.h_template_quote data.h_template_name_quote
  have hQuotedInstance :
      ⊢ₘ[code_naming_theory]
        Formula.substituteFree SetSort.set data.source_id
          data.template_code preconditionBody := by
    simpa [preconditionBody, boundCode,
      code_substitution_precondition,
      Formula.substituteFree, Term.substituteFree,
      hFixed data.source_id data.template_code
        boundCode data.diagonal_variable_code_boundary,
      hFixed data.source_id data.template_code
        data.template_name_code data.template_name_code_boundary] using hQuoted
  have hTransport := FirstOrder.Derives.eq_subst_m (T := code_naming_theory) (Γ := []) (sort := SetSort.set) (eigen := data.source_id)
    (left := data.template_code) (right := data.template_name) (body := preconditionBody)
    data.template_code_value_derives hQuotedInstance
    (hLeftCheck := data.template_code_boundary.check_certificate)
    (hRightCheck := data.template_name_boundary.check_certificate)
  simpa [preconditionBody, boundCode,
    code_substitution_precondition,
    Formula.substituteFree, Term.substituteFree,
    hFixed data.source_id data.template_name
      boundCode data.diagonal_variable_code_boundary,
    hFixed data.source_id data.template_name
      data.template_name_code data.template_name_code_boundary] using hTransport
/--
自由支撑为空的闭项对任意保留编号都新鲜。
该引理只负责消去 `ReservedIdsFresh` 中反复出现的闭项分支；具体哪些 quotation
项是闭项，仍由各自的代码边界或 quotation 正确性定理给出。
-/
private theorem fs_reserved_id_fresh_of_freeSupport_nil (term : SetTerm) (id : FreeVarId) (hSupport : Term.freeSupport term = []) :
    (SetSort.set, id) ∉ Term.freeSupport term := by
  rw [hSupport]
  intro hMember
  cases hMember
/-- 自动分配的单变量项与一个不同的保留编号彼此新鲜。 -/
private theorem fs_reserved_id_fresh_variable (variableId reserved : FreeVarId) (hNe : variableId ≠ reserved) :
    (SetSort.set, reserved) ∉ Term.freeSupport (x#variableId) := by
  intro hMember
  change (SetSort.set, reserved) ∈
      [(SetSort.set, variableId)] at hMember
  have hPair : (SetSort.set, reserved) = (SetSort.set, variableId) :=
    List.mem_singleton.mp hMember
  exact hNe (congrArg Prod.snd hPair).symm
/--
把真实对角图的源变量实例化为模板规范名称，只改变图体中的源代码参数。
此处集中处理存在 binder 与 `code_substitution_spec` 内部保留编号之间的交换律；后续
图值和图唯一性证明只消费这个规范展开式。
-/
private theorem source_graph_substitute_eq
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Formula.substituteFree SetSort.set data.source_id
        data.template_name data.diagonal_graph = (∃ₘ[SetSort.set, data.name_id],
        fs_diagonal_source_graph_body codeId data.template_name) := by
  let boundCode :=
    Numbered.named_variable_code (free_name data.source_id)
  let rawBody : SetFormula := ((x#data.name_id ≐ₘ name_codeₘ(x#data.source_id)) ∧ₘ
      code_substitution_spec (x#data.source_id) boundCode (x#data.name_id) (x#data.result_id))
  let sourceBody : SetFormula :=
    fs_diagonal_source_graph_body codeId data.template_name
  have hFixed (parameter : FreeVarId) (substitute term : SetTerm) (hTerm : Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set parameter substitute term = term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter substitute term (by
        rw [hTerm.2]
        simp)
  have hSourceFresh :
      ReservedIdsFresh [310, 311]
        [data.template_name, x#data.source_id, boundCode,
          x#data.name_id, x#data.result_id] := by
    intro term hTerm reserved hReserved
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm hReserved
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        data.template_name reserved
        data.h_template_name_freeSupport_nil
    · rcases hReserved with rfl | rfl
      · exact fs_reserved_id_fresh_variable
          data.source_id 310 (fs_diagonal_source_ne_310 codeId)
      · exact fs_reserved_id_fresh_variable
          data.source_id 311 (fs_diagonal_source_ne_311 codeId)
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        boundCode reserved (by
          simp [boundCode, named_variable_code_freeSupport])
    · rcases hReserved with rfl | rfl
      · exact fs_reserved_id_fresh_variable
          data.name_id 310 (fs_diagonal_name_ne_310 codeId)
      · exact fs_reserved_id_fresh_variable
          data.name_id 311 (fs_diagonal_name_ne_311 codeId)
    · rcases hReserved with rfl | rfl
      · exact fs_reserved_id_fresh_variable
          data.result_id 310 (fs_diagonal_result_ne_310 codeId)
      · exact fs_reserved_id_fresh_variable
          data.result_id 311 (fs_diagonal_result_ne_311 codeId)
  have hSourceSpec :=
    code_substitution_spec_substituteFree
      data.source_id data.template_name (x#data.source_id) boundCode (x#data.name_id) (x#data.result_id)
      hSourceFresh
  have hSourceSpecEq :
      Formula.substituteFree SetSort.set data.source_id
          data.template_name (code_substitution_spec (x#data.source_id) boundCode (x#data.name_id) (x#data.result_id)) =
        code_substitution_spec
          data.template_name boundCode (x#data.name_id) (x#data.result_id) := by
    simpa [boundCode, Term.substituteFree,
      hFixed data.source_id data.template_name
        boundCode data.diagonal_variable_code_boundary, (fs_diagonal_source_ne_name codeId).symm, (fs_diagonal_source_ne_result codeId).symm] using hSourceSpec
  have hSourceBodyEq :
      Formula.substituteFree SetSort.set data.source_id
          data.template_name rawBody =
        sourceBody := by
    simp [rawBody, sourceBody, fs_diagonal_source_graph_body,
      Formula.substituteFree, Term.substituteFree,
      hSourceSpecEq, boundCode, (fs_diagonal_source_ne_name codeId).symm]
  change
    Formula.substituteFree SetSort.set data.source_id
        data.template_name (Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set data.name_id 0 rawBody)) =
      Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set data.name_id 0 sourceBody)
  simp only [Formula.substituteFree]
  apply congrArg (fun formula : SetFormula =>
    Formula.existsE SetSort.set formula)
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set data.source_id data.name_id 0
    data.template_name rawBody (fs_diagonal_source_ne_name codeId)
    data.h_template_name_admissible.2 (by rw [data.h_template_name_freeSupport_nil]; simp)]
  rw [hSourceBodyEq]
/--
原始对角图在模板规范名称处取到真实固定点 quotation。
这里保留为透明证明证书，使严格 Hilbert 编译器能够逐节点核验自然演绎树。
-/
def raw_graph_value_derives
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ⊢ₘ[code_naming_theory]
      Formula.substituteFree SetSort.set data.result_id
        data.fixed_point_code (Formula.substituteFree SetSort.set data.source_id
          data.template_name data.diagonal_graph) := by
  let boundCode :=
    Numbered.named_variable_code (free_name data.source_id)
  let sourceBody : SetFormula :=
    fs_diagonal_source_graph_body codeId data.template_name
  let graphBody : SetFormula := ((x#data.name_id ≐ₘ name_codeₘ(data.template_name)) ∧ₘ
      code_substitution_spec
        data.template_name boundCode (x#data.name_id)
        data.fixed_point_code
    )
  have hFixed (parameter : FreeVarId) (substitute term : SetTerm) (hTerm : Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set parameter substitute term = term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter substitute term (by
        rw [hTerm.2]
        simp)
  have hSourceGraph :
      Formula.substituteFree SetSort.set data.source_id
          data.template_name data.diagonal_graph = (∃ₘ[SetSort.set, data.name_id], sourceBody) := by
    simpa [sourceBody] using data.source_graph_substitute_eq
  have hResultFresh :
      ReservedIdsFresh [310, 311]
        [data.fixed_point_code, data.template_name, boundCode,
          x#data.name_id, x#data.result_id] := by
    intro term hTerm reserved hReserved
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm hReserved
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        data.fixed_point_code reserved data.fixed_point_code_boundary.2
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        data.template_name reserved
        data.h_template_name_freeSupport_nil
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        boundCode reserved (by
          simp [boundCode, named_variable_code_freeSupport])
    · rcases hReserved with rfl | rfl
      · exact fs_reserved_id_fresh_variable
          data.name_id 310 (fs_diagonal_name_ne_310 codeId)
      · exact fs_reserved_id_fresh_variable
          data.name_id 311 (fs_diagonal_name_ne_311 codeId)
    · rcases hReserved with rfl | rfl
      · exact fs_reserved_id_fresh_variable
          data.result_id 310 (fs_diagonal_result_ne_310 codeId)
      · exact fs_reserved_id_fresh_variable
          data.result_id 311 (fs_diagonal_result_ne_311 codeId)
  have hResultSpec :=
    code_substitution_spec_substituteFree
      data.result_id data.fixed_point_code
      data.template_name boundCode (x#data.name_id) (x#data.result_id)
      hResultFresh
  have hResultSpecEq :
      Formula.substituteFree SetSort.set data.result_id
          data.fixed_point_code (code_substitution_spec
            data.template_name boundCode (x#data.name_id) (x#data.result_id)) =
        code_substitution_spec
          data.template_name boundCode (x#data.name_id) data.fixed_point_code := by
    simpa [boundCode, Term.substituteFree,
      hFixed data.result_id data.fixed_point_code
        data.template_name data.template_name_boundary,
      hFixed data.result_id data.fixed_point_code
        boundCode data.diagonal_variable_code_boundary,
      fs_diagonal_name_ne_result codeId] using hResultSpec
  have hResultBodyEq :
      Formula.substituteFree SetSort.set data.result_id
          data.fixed_point_code sourceBody =
        graphBody := by
    simp [sourceBody, fs_diagonal_source_graph_body,
      graphBody, Formula.substituteFree,
      Term.substituteFree, hResultSpecEq, boundCode,
      hFixed data.result_id data.fixed_point_code
        data.template_name data.template_name_boundary,
      fs_diagonal_name_ne_result codeId]
  have hResultGraph :
      Formula.substituteFree SetSort.set data.result_id
          data.fixed_point_code (∃ₘ[SetSort.set, data.name_id], sourceBody) = (∃ₘ[SetSort.set, data.name_id], graphBody) := by
    simp only [Formula.substituteFree]
    apply congrArg (fun formula : SetFormula =>
      Formula.existsE SetSort.set formula)
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set data.result_id data.name_id 0
      data.fixed_point_code sourceBody (Ne.symm <| fs_diagonal_name_ne_result codeId)
      data.fixed_point_code_boundary.1.2 (by rw [data.fixed_point_code_boundary.2]; simp)]
    rw [hResultBodyEq]
  have hOpenFresh :
      ReservedIdsFresh [310, 311]
        [data.template_name_code, data.template_name, boundCode,
          x#data.name_id, data.fixed_point_code] := by
    intro term hTerm reserved hReserved
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm hReserved
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        data.template_name_code reserved
        data.template_name_code_boundary.2
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        data.template_name reserved
        data.h_template_name_freeSupport_nil
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        boundCode reserved (by
          simp [boundCode, named_variable_code_freeSupport])
    · rcases hReserved with rfl | rfl
      · exact fs_reserved_id_fresh_variable
          data.name_id 310 (fs_diagonal_name_ne_310 codeId)
      · exact fs_reserved_id_fresh_variable
          data.name_id 311 (fs_diagonal_name_ne_311 codeId)
    · exact fs_reserved_id_fresh_of_freeSupport_nil
        data.fixed_point_code reserved data.fixed_point_code_boundary.2
  have hOpenSpec :=
    code_substitution_spec_substituteFree
      data.name_id data.template_name_code
      data.template_name boundCode (x#data.name_id) data.fixed_point_code
      hOpenFresh
  have hOpenSpecEq :
      Formula.substituteFree SetSort.set data.name_id
          data.template_name_code (code_substitution_spec
            data.template_name boundCode (x#data.name_id) data.fixed_point_code) =
        code_substitution_spec
          data.template_name boundCode
          data.template_name_code data.fixed_point_code := by
    simpa [boundCode, Term.substituteFree,
      hFixed data.name_id data.template_name_code
        data.template_name data.template_name_boundary,
      hFixed data.name_id data.template_name_code
        boundCode data.diagonal_variable_code_boundary,
      hFixed data.name_id data.template_name_code
        data.fixed_point_code data.fixed_point_code_boundary] using
      hOpenSpec
  have hConjunction :
      ⊢ₘ[code_naming_theory] (data.template_name_code ≐ₘ
            name_codeₘ(data.template_name)) ∧ₘ
          code_substitution_spec
            data.template_name boundCode
            data.template_name_code
            data.fixed_point_code :=
    FirstOrder.Derives.conjIntro
      data.template_name_code_value_derives
      data.fixed_point_substitution_spec_derives
  have hGraphBodyOpen :
      Formula.substituteFree SetSort.set data.name_id
          data.template_name_code graphBody = ((data.template_name_code ≐ₘ
            name_codeₘ(data.template_name)) ∧ₘ
          code_substitution_spec
            data.template_name boundCode
            data.template_name_code data.fixed_point_code) := by
    simp [graphBody, Formula.substituteFree,
      Term.substituteFree, hOpenSpecEq,
      hFixed data.name_id data.template_name_code
        data.template_name data.template_name_boundary]
  have hExists :
      ⊢ₘ[code_naming_theory] (∃ₘ[SetSort.set, data.name_id], graphBody) := by
    nd_apply FirstOrder.Derives.exists_intro
      (term := data.template_name_code)
      (hTermCheck := data.template_name_code_boundary.check_certificate)
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    rw [hGraphBodyOpen]
    exact hConjunction
  have hTargetEq :
      Formula.substituteFree SetSort.set data.result_id
          data.fixed_point_code (Formula.substituteFree SetSort.set data.source_id
            data.template_name data.diagonal_graph) = (∃ₘ[SetSort.set, data.name_id], graphBody) := by
    rw [hSourceGraph, hResultGraph]
  exact FirstOrder.Derives.formula_cast hTargetEq.symm hExists
/--
真实对角图在模板规范名称处的结果唯一。
展开名称见证后，第一合取把任意见证识别为模板规范名称的 quotation；Leibniz
替换把第二合取输运到该规范 replacement，最后由 `code_substitution_spec` 的函数性
得到真实固定点代码与任意候选相等。
与图值证书相同，本证明保持透明，供严格 Hilbert 编译自动化读取实际推导节点。
-/
def raw_graph_unique_derives
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ⊢ₘ[code_naming_theory]
      Formula.imp (Formula.substituteFree SetSort.set data.source_id
          data.template_name data.diagonal_graph) (data.fixed_point_code ≐ₘ x#data.result_id) := by
  let boundCode :=
    Numbered.named_variable_code (free_name data.source_id)
  let sourceBody : SetFormula :=
    fs_diagonal_source_graph_body codeId data.template_name
  let sourceGraph : SetFormula :=
    Formula.substituteFree SetSort.set data.source_id
      data.template_name data.diagonal_graph
  let conclusion : SetFormula :=
    data.fixed_point_code ≐ₘ x#data.result_id
  have hFixed (parameter : FreeVarId) (substitute term : SetTerm) (hTerm : Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set parameter substitute term = term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter substitute term (by
        rw [hTerm.2]
        simp)
  have hSourceGraph :
      sourceGraph = (∃ₘ[SetSort.set, data.name_id], sourceBody) := by
    simpa [sourceGraph, sourceBody] using data.source_graph_substitute_eq
  have hTemplateNameCheck :
      Term.CheckCertificate data.template_name SetSort.set :=
    data.template_name_boundary.check_certificate
  have hBoundCodeCheck :
      Term.CheckCertificate boundCode SetSort.set :=
    data.diagonal_variable_code_boundary.check_certificate
  have hNameCodeCheck :
      Term.CheckCertificate
        (name_codeₘ(data.template_name)) SetSort.set := by
    prove_term_check
  have hSourceBodyCheck :
      Formula.CheckCertificate sourceBody := by
    simpa [sourceBody, fs_diagonal_source_graph_body, boundCode] using
      Formula.CheckCertificate.conj
        (Formula.CheckCertificate.equal
          (sort := SetSort.set)
          (by prove_term_check) hNameCodeCheck)
        (code_substitution_spec_check
          (source := data.template_name)
          (boundVariable := boundCode)
          (replacement := x#data.name_id)
          (candidate := x#data.result_id)
          (hSource := hTemplateNameCheck)
          (hBoundVariable := hBoundCodeCheck))
  have hSourceGraphCheck :
      Formula.CheckCertificate sourceGraph := by
    rw [hSourceGraph]
    exact Formula.CheckCertificate.exists_closeFreeAt
      SetSort.set data.name_id hSourceBodyCheck
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [sourceGraph]
  let Δ : Context signature := sourceBody :: Γ
  have hExists :
      Γ ⊢ₘ[code_naming_theory] (∃ₘ[SetSort.set, data.name_id], sourceBody) := by
    exact FirstOrder.Derives.formula_cast hSourceGraph <|
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (hCheck := hSourceGraphCheck)
  have hCase :
      Δ ⊢ₘ[code_naming_theory] conclusion := by
    have hBody :
        Δ ⊢ₘ[code_naming_theory] sourceBody :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (hCheck := hSourceBodyCheck)
    have hNameEquation :
        Δ ⊢ₘ[code_naming_theory]
          x#data.name_id ≐ₘ name_codeₘ(data.template_name) := by
      simpa [sourceBody, fs_diagonal_source_graph_body] using
        FirstOrder.Derives.conjElimLeft hBody
    have hCandidateSpecification :
        Δ ⊢ₘ[code_naming_theory]
          code_substitution_spec
            data.template_name boundCode (x#data.name_id) (x#data.result_id) := by
      simpa [sourceBody, fs_diagonal_source_graph_body, boundCode] using
        FirstOrder.Derives.conjElimRight hBody
    have hCanonicalEquation :
        Δ ⊢ₘ[code_naming_theory]
          data.template_name_code ≐ₘ
            name_codeₘ(data.template_name) :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp)
        data.template_name_code_value_derives
    have hCanonicalSymmetry :
        Δ ⊢ₘ[code_naming_theory]
          name_codeₘ(data.template_name) ≐ₘ
            data.template_name_code :=
      Metatheory.Derives.equality_symm hCanonicalEquation
    have hNameCode :
        Δ ⊢ₘ[code_naming_theory]
          x#data.name_id ≐ₘ data.template_name_code :=
      Metatheory.Derives.equality_trans
        hNameEquation hCanonicalSymmetry
    let candidateBody : SetFormula :=
      code_substitution_spec
        data.template_name boundCode (x#data.name_id) (x#data.result_id)
    have hCandidateSelf :
        Δ ⊢ₘ[code_naming_theory]
          Formula.substituteFree SetSort.set data.name_id (x#data.name_id) candidateBody := by
      simpa only [Formula.substituteFree_self] using (show Δ ⊢ₘ[code_naming_theory] candidateBody from by
          simpa [candidateBody] using hCandidateSpecification)
    have hCandidateTransport :=
      FirstOrder.Derives.eq_subst_m (T := code_naming_theory) (Γ := Δ) (sort := SetSort.set) (eigen := data.name_id) (left := x#data.name_id)
        (right := data.template_name_code) (body := candidateBody)
        hNameCode hCandidateSelf
    have hTransportFresh :
        ReservedIdsFresh [310, 311]
          [data.template_name_code, data.template_name, boundCode,
            x#data.name_id, x#data.result_id] := by
      intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm hReserved
      rcases hTerm with rfl | rfl | rfl | rfl | rfl
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          data.template_name_code reserved
          data.template_name_code_boundary.2
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          data.template_name reserved
          data.h_template_name_freeSupport_nil
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          boundCode reserved (by
            simp [boundCode, named_variable_code_freeSupport])
      · rcases hReserved with rfl | rfl
        · exact fs_reserved_id_fresh_variable
            data.name_id 310 (fs_diagonal_name_ne_310 codeId)
        · exact fs_reserved_id_fresh_variable
            data.name_id 311 (fs_diagonal_name_ne_311 codeId)
      · rcases hReserved with rfl | rfl
        · exact fs_reserved_id_fresh_variable
            data.result_id 310 (fs_diagonal_result_ne_310 codeId)
        · exact fs_reserved_id_fresh_variable
            data.result_id 311 (fs_diagonal_result_ne_311 codeId)
    have hCandidateSubstitution :=
      code_substitution_spec_substituteFree
        data.name_id data.template_name_code
        data.template_name boundCode (x#data.name_id) (x#data.result_id)
        hTransportFresh
    have hCandidateAtCanonical :
        Δ ⊢ₘ[code_naming_theory]
          code_substitution_spec
            data.template_name boundCode
            data.template_name_code (x#data.result_id) := by
      rw [hCandidateSubstitution] at hCandidateTransport
      simpa [candidateBody, Term.substituteFree,
        hFixed data.name_id data.template_name_code
          data.template_name data.template_name_boundary,
        hFixed data.name_id data.template_name_code
          boundCode data.diagonal_variable_code_boundary, (fs_diagonal_name_ne_result codeId).symm] using
        hCandidateTransport
    have hPrecondition :
        Δ ⊢ₘ[code_naming_theory]
          code_substitution_precondition
            data.template_name boundCode data.template_name_code := by
      exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp) (by simpa [boundCode] using
          data.template_substitution_precondition_derives)
    have hFixedSpecification :
        Δ ⊢ₘ[code_naming_theory]
          code_substitution_spec
            data.template_name boundCode
            data.template_name_code data.fixed_point_code := by
      exact FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp) (by simpa [boundCode] using
          data.fixed_point_substitution_spec_derives)
    have hFirstFresh :
        ReservedIdsFresh [310, 311]
          [data.template_name, boundCode, data.template_name_code,
            data.fixed_point_code] := by
      intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
      rcases hTerm with rfl | rfl | rfl | rfl
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          data.template_name reserved
          data.h_template_name_freeSupport_nil
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          boundCode reserved (by
            simp [boundCode, named_variable_code_freeSupport])
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          data.template_name_code reserved
          data.template_name_code_boundary.2
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          data.fixed_point_code reserved data.fixed_point_code_boundary.2
    have hSecondFresh :
        ReservedIdsFresh [310, 311]
          [data.template_name, boundCode, data.template_name_code,
            x#data.result_id] := by
      intro term hTerm reserved hReserved
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm hReserved
      rcases hTerm with rfl | rfl | rfl | rfl
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          data.template_name reserved
          data.h_template_name_freeSupport_nil
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          boundCode reserved (by
            simp [boundCode, named_variable_code_freeSupport])
      · exact fs_reserved_id_fresh_of_freeSupport_nil
          data.template_name_code reserved
          data.template_name_code_boundary.2
      · rcases hReserved with rfl | rfl
        · exact fs_reserved_id_fresh_variable
            data.result_id 310 (fs_diagonal_result_ne_310 codeId)
        · exact fs_reserved_id_fresh_variable
            data.result_id 311 (fs_diagonal_result_ne_311 codeId)
    have hUnique :
        ⊢ₘ[code_naming_theory]
          code_substitution_precondition
              data.template_name boundCode data.template_name_code ⟶ₘ
            code_substitution_spec
                data.template_name boundCode data.template_name_code
                data.fixed_point_code ⟶ₘ
              code_substitution_spec
                  data.template_name boundCode data.template_name_code (x#data.result_id) ⟶ₘ
                data.fixed_point_code ≐ₘ x#data.result_id := by
      apply code_naming_weaken_godel_quotation
      apply gq_weaken_substitution_variable
      exact code_substitution_spec_unique_derives
        data.template_name boundCode data.template_name_code
        data.fixed_point_code (x#data.result_id)
        hFirstFresh hSecondFresh
    have hUniqueAt :
        Δ ⊢ₘ[code_naming_theory]
          code_substitution_precondition
              data.template_name boundCode data.template_name_code ⟶ₘ
            code_substitution_spec
                data.template_name boundCode data.template_name_code
                data.fixed_point_code ⟶ₘ
              code_substitution_spec
                  data.template_name boundCode data.template_name_code (x#data.result_id) ⟶ₘ
                data.fixed_point_code ≐ₘ x#data.result_id :=
      FirstOrder.Derives.context_weaken (Γ := []) (Δ := Δ) (by simp) hUnique
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.impElim hUniqueAt hPrecondition)
        hFixedSpecification)
      hCandidateAtCanonical
  have hTheoryFresh :
      ∀ formula, code_naming_theory formula → (SetSort.set, data.name_id) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rw [(code_naming_theory_sentence hFormula).2]
    intro hMember
    cases hMember
  have hContextFresh :
      ∀ formula, formula ∈ Γ → (SetSort.set, data.name_id) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    rw [hSourceGraph]
    simpa [Formula.freeSupport] using (Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set data.name_id 0 sourceBody)
  have hConclusionFresh : (SetSort.set, data.name_id) ∉ Formula.freeSupport conclusion := by
    simp only [conclusion, Formula.freeSupport,
      data.fixed_point_code_boundary.2, List.nil_append]
    intro hMember
    have hPair : (SetSort.set, data.name_id) = (SetSort.set, data.result_id) :=
      List.mem_singleton.mp hMember
    exact fs_diagonal_name_ne_result codeId (congrArg Prod.snd hPair)
  have hEliminated := FirstOrder.Derives.exists_elim
    hTheoryFresh hContextFresh hConclusionFresh
    hExists hCase
    (hBodyCheck := hSourceBodyCheck)
  simpa [Γ, sourceGraph, conclusion] using hEliminated
/--
自动扩张后的对角理论仍对内部结果变量新鲜。
用户背景理论部分由数据字段保证；编码理论部分先还原为某条原始编码公理，再利用
`code_naming_theory_sentence` 与 Hilbert 归约保持自由支撑这一事实消去。
-/
theorem diagonal_theory_result_fresh
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ∀ formula, fs_diagonal_theory theory formula → (SetSort.set, data.result_id) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  rcases hFormula with hCodeNaming | hTheory
  · rcases hCodeNaming with ⟨source, hSource, rfl⟩
    intro hMember
    have hSourceMember := (Formula.mem_freeSupport_hilbertize_iff (σ := signature) SetSort.set (SetSort.set, data.result_id) source).mp hMember
    rw [(code_naming_theory_sentence hSource).2] at hSourceMember
    cases hSourceMember
  · rw [(data.h_theory_sentence formula hTheory).2]
    exact List.not_mem_nil
/-- 自然演绎中的真实图值证书编译为扩张理论上的内部 Hilbert 图值。 -/
theorem graph_value
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    HilbertDerives (fs_diagonal_theory theory) (hilbert_relation_instance SetSort.set
        data.source_id data.result_id data.core_graph
        data.template_name data.fixed_point_code) := by
  have hCompiled :=
    data.raw_graph_value_derives.to_hilbert SetSort.set
  have hWeakened :
      HilbertDerives (fs_diagonal_theory theory) (Formula.hilbertize SetSort.set (Formula.substituteFree SetSort.set data.result_id
            data.fixed_point_code (Formula.substituteFree SetSort.set data.source_id
              data.template_name data.diagonal_graph))) :=
    hCompiled.theory_weakening (by
      intro formula hFormula
      exact Or.inl (by
        simpa [Theory.hilbertize_context] using hFormula))
  simpa [Theory.hilbertize_context,
    hilbert_relation_instance, core_graph,
    fs_code_diagonal_graph_core, fs_diagonal_target,
    Formula.hilbertize_substituteFree] using hWeakened
/-- 自然演绎中的图唯一性证书编译为扩张理论上的内部 Hilbert 函数性。 -/
theorem graph_unique
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    HilbertDerives (fs_diagonal_theory theory) (Formula.imp (Formula.substituteFree SetSort.set data.source_id
          data.template_name data.core_graph) (data.fixed_point_code ≐ₘ x#data.result_id)) := by
  have hCompiled :=
    data.raw_graph_unique_derives.to_hilbert SetSort.set
  have hWeakened :
      HilbertDerives (fs_diagonal_theory theory) (Formula.hilbertize SetSort.set (Formula.imp (Formula.substituteFree SetSort.set data.source_id
              data.template_name data.diagonal_graph) (data.fixed_point_code ≐ₘ x#data.result_id))) :=
    hCompiled.theory_weakening (by
      intro formula hFormula
      exact Or.inl (by
        simpa [Theory.hilbertize_context] using hFormula))
  simpa [core_graph, fs_code_diagonal_graph_core,
    fs_diagonal_target, Formula.hilbertize,
    Formula.hilbertize_substituteFree] using hWeakened
/-! ## 内部 Hilbert 对角引理 -/
/-- 改名后的目标在固定点编码处等于原目标的直接实例。 -/
theorem diagonal_body_fixed_point_eq
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    Formula.substituteFree SetSort.set data.result_id
        data.fixed_point_code (fs_diagonal_body codeId body) =
      Formula.substituteFree SetSort.set codeId
        data.fixed_point_code (fs_diagonal_target body) := by
  exact Formula.substituteFree_rename
    SetSort.set codeId data.result_id data.fixed_point_code (fs_diagonal_target body) data.target_result_fresh
/-- FormalSystem 扩展签名上的关系图式 Hilbert 固定点定理。 -/
theorem hilbert_fixed_point
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    HilbertDerives (fs_diagonal_theory theory) (Formula.hilbert_iff (fs_diagonal_fixed_point codeId data.template_name body)
        (Formula.substituteFree SetSort.set codeId
          data.fixed_point_code (fs_diagonal_target body))) := by
  have hRelation := HilbertDerives.relational_diagonal_fixed_point (fs_diagonal_source_ne_result codeId)
    data.fixed_point_code_boundary.1.1
    data.h_template_name_admissible.2
    data.fixed_point_code_boundary.1.2 (by rw [data.h_template_name_freeSupport_nil]; simp) (by rw [data.fixed_point_code_boundary.2]; simp)
    data.diagonal_body_source_fresh
    data.diagonal_body_admissible
    data.diagonal_theory_result_fresh
    data.graph_value data.graph_unique
  rw [data.diagonal_body_fixed_point_eq] at hRelation
  exact hRelation
/-- 已处于 Hilbert 片段中的目标得到未归约形式的固定点等价。 -/
theorem hilbert_fixed_point_of_core
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) (hCore : fs_diagonal_target body = body) :
    HilbertDerives (fs_diagonal_theory theory) (Formula.hilbert_iff (fs_diagonal_fixed_point codeId data.template_name body)
        (Formula.substituteFree SetSort.set codeId
          data.fixed_point_code body)) := by
  simpa [hCore] using data.hilbert_fixed_point
/-- 固定点等价拥有以该式为末行的标准有限 Hilbert 证明。 -/
theorem finite_hilbert_proof
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ∃ initial,
      HilbertProof (fs_diagonal_theory theory) (initial ++
          [Formula.hilbert_iff (fs_diagonal_fixed_point codeId
              data.template_name body) (Formula.substituteFree SetSort.set codeId
              data.fixed_point_code (fs_diagonal_target body))]) :=
  hilbert_derives_iff_finite_proof.mp data.hilbert_fixed_point
/-- 句子闭性、真实 quotation 与内部 Hilbert 固定点等价的联合交付接口。 -/
theorem diagonal_lemma
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (data : FsDiagonalizationData theory codeId body) :
    ∃ fixedPoint : SetFormula,
      Formula.Sentence fixedPoint ∧
      Numbered.quote? fixedPoint = some data.fixed_point_code ∧
      HilbertDerives (fs_diagonal_theory theory) (Formula.hilbert_iff fixedPoint (Formula.substituteFree SetSort.set codeId
            data.fixed_point_code (fs_diagonal_target body))) :=
  ⟨fs_diagonal_fixed_point codeId data.template_name body,
    data.fixed_point_sentence,
    data.h_fixed_point_quote,
    data.hilbert_fixed_point⟩
end FsDiagonalizationData
/-! ## 收敛后的公共对角接口 -/
/--
由三个本质条件构造完整对角证书。
模板 quotation、规范名称、固定点 quotation、固定编码项以及所有内部图语法边界
均由已有全定义性定理给出；调用方不再接触 `FsDiagonalizationData` 的内部字段。
-/
theorem fs_diagonalization_data_exists
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (hBodyAdmissible : Formula.Admissible body)
    (hBodyOnlyCodeVariable : fs_only_code_variable_formula codeId body) (hTheorySentence :
      ∀ formula, theory formula → Formula.Sentence formula) :
    Nonempty (FsDiagonalizationData theory codeId body) := by
  rcases canonical_formula_name_data_exists
      (FsDiagonalizationData.fs_diagonal_template_admissible
        codeId body hBodyAdmissible) with
    ⟨templateNaming⟩
  rcases templateNaming.named_instance_code_exists
      (fs_diagonal_source_id codeId) with
    ⟨fixedPointCode, hFixedPointQuote⟩
  exact ⟨{
    h_body_admissible := hBodyAdmissible
    h_body_only_code_variable := hBodyOnlyCodeVariable
    template_naming := templateNaming
    fixed_point_code := fixedPointCode
    h_theory_sentence := hTheorySentence
    h_fixed_point_quote := by
      simpa [fs_diagonal_fixed_point,
        hilbert_relational_diagonal_fixed_point] using
        hFixedPointQuote
  }⟩
/--
在自动生成的编码扩张中构造标准关系图式固定点。
该定理是最终目标理论接口的构造层：它负责生成 quotation 与 Hilbert 固定点，
但暂时保留 `fs_diagonal_theory theory` 作为推导背景。
-/
theorem fs_diagonal_lemma_in_extension
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (hBodyAdmissible : Formula.Admissible body)
    (hBodyOnlyCodeVariable : fs_only_code_variable_formula codeId body) (hTheorySentence :
      ∀ formula, theory formula → Formula.Sentence formula) :
    ∃ fixedPoint : SetFormula, ∃ fixedPointCode : SetTerm,
      Formula.Sentence fixedPoint ∧
      Numbered.quote? fixedPoint = some fixedPointCode ∧
      HilbertDerives (fs_diagonal_theory theory) (Formula.hilbert_iff fixedPoint (Formula.substituteFree SetSort.set codeId
            fixedPointCode (fs_diagonal_target body))) := by
  rcases fs_diagonalization_data_exists hBodyAdmissible
      hBodyOnlyCodeVariable hTheorySentence with
    ⟨data⟩
  rcases data.diagonal_lemma with
    ⟨fixedPoint, hSentence, hQuote, hDerives⟩
  exact ⟨fixedPoint, data.fixed_point_code,
    hSentence, hQuote, hDerives⟩
/--
目标已经处于内部 Hilbert 片段时，构造层直接给出未经再次归约的固定点等价。
-/
theorem fs_diagonal_lemma_of_core_in_extension
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (hBodyAdmissible : Formula.Admissible body)
    (hBodyOnlyCodeVariable : fs_only_code_variable_formula codeId body) (hTheorySentence :
      ∀ formula, theory formula → Formula.Sentence formula) (hCore : Numbered.HilbertCore body) :
    ∃ fixedPoint : SetFormula, ∃ fixedPointCode : SetTerm,
      Formula.Sentence fixedPoint ∧
      Numbered.quote? fixedPoint = some fixedPointCode ∧
      HilbertDerives (fs_diagonal_theory theory) (Formula.hilbert_iff fixedPoint (Formula.substituteFree SetSort.set codeId
            fixedPointCode body)) := by
  rcases fs_diagonalization_data_exists hBodyAdmissible
      hBodyOnlyCodeVariable hTheorySentence with
    ⟨data⟩
  exact ⟨fs_diagonal_fixed_point codeId data.template_name body,
    data.fixed_point_code, data.fixed_point_sentence,
    data.h_fixed_point_quote,
    data.hilbert_fixed_point_of_core (by
      simpa [fs_diagonal_target] using
        hCore.hilbertize_eq_self SetSort.set)⟩
/-! ## 目标理论中的公共对角接口 -/
/--
FormalSystem 扩展签名上的标准内部 Hilbert 对角引理。
对任意良构且至多含代码变量 `codeId` 的目标公式，只要背景理论由句子组成并承载
Gödel quotation 编码理论，就产生一个真实闭句、它的真实 quotation，以及直接位于
目标理论中的 Hilbert 固定点等价。调用方不再看见临时的 `fs_diagonal_theory`。
-/
theorem fs_diagonal_lemma
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (hCodeNaming : fs_extends_code_naming theory) (hBodyAdmissible : Formula.Admissible body)
    (hBodyOnlyCodeVariable : fs_only_code_variable_formula codeId body) (hTheorySentence :
      ∀ formula, theory formula → Formula.Sentence formula) :
    ∃ fixedPoint : SetFormula, ∃ fixedPointCode : SetTerm,
      Formula.Sentence fixedPoint ∧
      Numbered.quote? fixedPoint = some fixedPointCode ∧
      HilbertDerives theory (Formula.hilbert_iff fixedPoint (Formula.substituteFree SetSort.set codeId
            fixedPointCode (fs_diagonal_target body))) := by
  rcases fs_diagonal_lemma_in_extension
      hBodyAdmissible hBodyOnlyCodeVariable hTheorySentence with
    ⟨fixedPoint, fixedPointCode, hSentence, hQuote, hDerives⟩
  exact ⟨fixedPoint, fixedPointCode, hSentence, hQuote,
    fs_diagonal_derives_in_theory hCodeNaming hDerives⟩
/--
目标已处于内部 Hilbert 片段时，公共接口直接在目标理论中给出未再次归约的固定点。
-/
theorem fs_diagonal_lemma_of_core
    {theory : SetTheory} {codeId : FreeVarId} {body : SetFormula} (hCodeNaming : fs_extends_code_naming theory) (hBodyAdmissible : Formula.Admissible body)
    (hBodyOnlyCodeVariable : fs_only_code_variable_formula codeId body) (hTheorySentence :
      ∀ formula, theory formula → Formula.Sentence formula) (hCore : Numbered.HilbertCore body) :
    ∃ fixedPoint : SetFormula, ∃ fixedPointCode : SetTerm,
      Formula.Sentence fixedPoint ∧
      Numbered.quote? fixedPoint = some fixedPointCode ∧
      HilbertDerives theory (Formula.hilbert_iff fixedPoint (Formula.substituteFree SetSort.set codeId
            fixedPointCode body)) := by
  rcases fs_diagonal_lemma_of_core_in_extension
      hBodyAdmissible hBodyOnlyCodeVariable hTheorySentence hCore with
    ⟨fixedPoint, fixedPointCode, hSentence, hQuote, hDerives⟩
  exact ⟨fixedPoint, fixedPointCode, hSentence, hQuote,
    fs_diagonal_derives_in_theory hCodeNaming hDerives⟩
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
