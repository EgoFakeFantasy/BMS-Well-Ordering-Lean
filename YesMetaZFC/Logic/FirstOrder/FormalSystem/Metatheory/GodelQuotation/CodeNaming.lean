import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNumbering
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution
/-!
# 有限 token 序列的规范闭项命名
本模块先固定对角化所需的元层命名约定：给定一个有限自然数 token 序列，使用
`standard_token_sequence` 作为它的规范闭项。随后用通用 quotation 计算这个闭项的
对象语法编码。这里暂不把该变换伪装成对象层可约函数；对象层 `NameCode` 的存在/唯一性
合同将在此元层边界稳定后单独加入。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-! ## 规范闭项 -/
/-- token 序列的规范闭项命名；其对象值就是相应的标准有限 token 序列。 -/
def canonical_name_term (tokens : List Nat) : SetTerm :=
  standard_token_sequence tokens
@[simp]
theorem canonical_name_term_admissible (tokens : List Nat) :
    Term.Admissible (canonical_name_term tokens) SetSort.set := by
  simpa [canonical_name_term] using (standard_token_sequence_admissible tokens)
/-- 规范闭项的纯函数合法性证书。 -/
@[term_check]
theorem canonical_name_term_check (tokens : List Nat) :
    Term.CheckCertificate (canonical_name_term tokens) SetSort.set :=
  Term.check_admissible_complete (canonical_name_term_admissible tokens)
@[simp]
theorem canonical_name_term_freeSupport_nil (tokens : List Nat) :
    Term.freeSupport (canonical_name_term tokens) = [] := by
  simp [canonical_name_term]
/-! ## 规范闭项 token 的显式递归 -/
/-- 一元 FormalSystem 函数应用项的 quotation token 构造。 -/
def unary_name_tokens (function : FunctionSymbol) (argument : List Nat) : List Nat :=
  Numbered.function_application_tokens 0 function.ctorIdx (List.singleton argument)
/-- 二元 FormalSystem 函数应用项的 quotation token 构造。 -/
def binary_name_tokens (function : FunctionSymbol) (left right : List Nat) : List Nat :=
  Numbered.function_application_tokens 1 function.ctorIdx (left :: List.singleton right)
/-- 标准 numeral 项自身的 quotation token。 -/
def numeral_name_tokens : Nat → List Nat
  | 0 =>
      [Numbered.constant_token FunctionSymbol.emptySet.ctorIdx]
  | value + 1 =>
      unary_name_tokens FunctionSymbol.successor (numeral_name_tokens value)
/--
从对象下标 `start` 开始构造标准 token 序列项自身的 quotation token。
递归式逐字反映 `standard_sequence_from` 的
`binaryUnion (singleton (orderedPair ...)) tail` 语法树，因此它不是对 quotation
结果的后验选择，而是之后对象层 `NameCode` 要表示的确定算法。
-/
def canonical_name_tokens_from : Nat → List Nat → List Nat
  | _, [] =>
      [Numbered.constant_token FunctionSymbol.emptySet.ctorIdx]
  | start, token :: rest =>
      binary_name_tokens FunctionSymbol.binaryUnion (unary_name_tokens FunctionSymbol.singleton (binary_name_tokens FunctionSymbol.orderedPair
            (numeral_name_tokens start) (numeral_name_tokens token))) (canonical_name_tokens_from (start + 1) rest)
/-- 标准 token 序列规范闭项自身的总 token 编码函数。 -/
def canonical_name_tokens (tokens : List Nat) : List Nat :=
  canonical_name_tokens_from 0 tokens
/-- 标准 numeral 项的通用 quotation 精确计算为 `numeral_name_tokens`。 -/
@[simp]
theorem quote_finite_numeral_tokens_with? (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (value : Nat) :
    Numbered.quote_term_tokens_with? freeNaming boundNames (numₘ(value)) =
      some (numeral_name_tokens value) := by
  induction value with
  | zero =>
      simp [finite_numeral_term, numeral_name_tokens,
        Numbered.quote_term_tokens_with?]
  | succ value ih =>
      simp [finite_numeral_term, numeral_name_tokens,
        unary_name_tokens, List.singleton,
        Numbered.quote_term_tokens_with?, ih]
/-- 从任意起点生成的标准 token 序列项也满足显式 token 递归式。 -/
theorem quote_standard_token_sequence_from_tokens_with? (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (start : Nat) (tokens : List Nat) :
    Numbered.quote_term_tokens_with? freeNaming boundNames (standard_sequence_from start (tokens.map finite_numeral_term)) =
      some (canonical_name_tokens_from start tokens) := by
  induction tokens generalizing start with
  | nil =>
      simp [standard_sequence_from, canonical_name_tokens_from,
        Numbered.quote_term_tokens_with?]
  | cons token rest ih =>
      simp [standard_sequence_from, canonical_name_tokens_from,
        binary_name_tokens, unary_name_tokens,
        List.singleton, Numbered.quote_term_tokens_with?, ih]
/-- 规范闭项的 token quotation 没有失败分支，并由公开递归函数精确给出。 -/
@[simp]
theorem canonical_name_term_tokens_eq (tokens : List Nat) :
    Numbered.quote_term_tokens_with? free_name [] (canonical_name_term tokens) =
      some (canonical_name_tokens tokens) := by
  simpa [canonical_name_term, standard_token_sequence,
    canonical_name_tokens] using (quote_standard_token_sequence_from_tokens_with?
      free_name [] 0 tokens)
/-! ## 规范闭项的 quotation -/
/-- 规范闭项的通用对象 quotation。 -/
def canonical_name_code? (tokens : List Nat) : Option SetTerm :=
  Numbered.quote_term_with? free_name [] (canonical_name_term tokens)
/-- 每个有限 token 序列都有规范闭项 quotation。 -/
theorem canonical_name_code?_exists (tokens : List Nat) :
    ∃ code, canonical_name_code? tokens = some code := by
  have hScoped :
      TermScoped (Numbered.scope_of_names ([] : List Nat)) (canonical_name_term tokens) := by
    simpa [canonical_name_term, Numbered.scope_of_names] using (canonical_name_term_admissible tokens).2
  exact Numbered.quote_term_with?_exists free_name [] hScoped
/-- 规范闭项 quotation 的成功结果自动满足对象项边界。 -/
theorem canonical_name_code?_boundary
    {tokens : List Nat} {code : SetTerm} (hQuote : canonical_name_code? tokens = some code) :
    Numbered.CodeBoundary code := by
  exact Numbered.quote_term_with?_code_boundary
    free_name [] hQuote
/-- 把规范闭项 quotation 的存在性与其边界打包，供后续对象命名合同消费。 -/
theorem canonical_name_code?_exists_with_boundary (tokens : List Nat) :
    ∃ code,
      canonical_name_code? tokens = some code ∧
        Numbered.CodeBoundary code := by
  rcases canonical_name_code?_exists tokens with ⟨code, hCode⟩
  exact ⟨code, hCode, canonical_name_code?_boundary hCode⟩
/-! ## 对象语言中的规范命名递归 -/
/-- 空集 numeral 项的对象 quotation；它也是两类命名递归的终止值。 -/
abbrev canonical_name_zero_code : SetTerm :=
  const_codeₘ(numₘ(FunctionSymbol.emptySet.ctorIdx))
/-- 用已有项编码构造器引用一个正元函数应用。 -/
def canonical_name_application_code (function : FunctionSymbol) (arguments : List SetTerm) : SetTerm :=
  term_application_code_term (numₘ(arguments.length - 1)) (numₘ(function.ctorIdx)) (standard_sequence arguments)
/-- 所有参数均可采纳时，显式函数应用 quotation 代码仍可采纳。 -/
theorem canonical_name_application_code_admissible (function : FunctionSymbol) (arguments : List SetTerm) (hArguments : ∀ argument, argument ∈ arguments →
      Term.Admissible argument SetSort.set) :
    Term.Admissible (canonical_name_application_code function arguments)
      SetSort.set := by
  exact term_application_code_term_admissible (numₘ(arguments.length - 1)) (numₘ(function.ctorIdx)) (standard_sequence arguments)
    (finite_numeral_term_admissible _) (finite_numeral_term_admissible _) (seq_admissible_m 0 hArguments)
/-- 已知 numeral 代码后构造其后继 numeral 的代码。 -/
def canonical_name_successor_code (code : SetTerm) : SetTerm :=
  canonical_name_application_code FunctionSymbol.successor [code]
/-- numeral quotation 的后继代码构造保持可采纳性。 -/
theorem canonical_name_successor_code_admissible (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    Term.Admissible (canonical_name_successor_code code) SetSort.set := by
  exact canonical_name_application_code_admissible _ _ (by
    intro argument hArgument
    rcases List.mem_singleton.mp hArgument with rfl
    exact hCode)
/-- 后继 quotation 构造器的可组合计算证书。 -/
@[term_check]
theorem canonical_name_successor_code_check (code : SetTerm)
    (hCode : Term.CheckCertificate code SetSort.set) :
    Term.CheckCertificate (canonical_name_successor_code code) SetSort.set :=
  Term.check_admissible_complete
    (canonical_name_successor_code_admissible code hCode.admissible)
/--
后继 quotation 构造器与 locally nameless 的 opening 交换。
这条自然性引理把构造器内部的闭 numeral 直接消去，只把 opening 传给唯一参数。
-/
theorem canonical_name_successor_code_openAt (depth : Nat) (replacement code : SetTerm) :
    Term.openAt SetSort.set depth replacement (canonical_name_successor_code code) =
      canonical_name_successor_code (Term.openAt SetSort.set depth replacement code) := by
  have hNumeralOpen (value : Nat) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  simp [canonical_name_successor_code,
    canonical_name_application_code,
    standard_sequence, standard_sequence_from,
    Term.openAt, hNumeralOpen]
/--
后继 quotation 构造器与自由变量替换交换。
后续所有递归方程的等式运输均复用这一条，而不再展开整棵 quotation 语法树。
-/
theorem canonical_name_successor_code_substituteFree (id : FreeVarId) (replacement code : SetTerm) :
    Term.substituteFree SetSort.set id replacement (canonical_name_successor_code code) =
      canonical_name_successor_code (Term.substituteFree SetSort.set id replacement code) := by
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement (numₘ(value)) (by
        rw [finite_numeral_term_freeSupport value]
        simp)
  simp [canonical_name_successor_code,
    canonical_name_application_code,
    standard_sequence, standard_sequence_from,
    Term.substituteFree, hNumeralFixed]
/--
已知位置、token numeral 与尾序列代码后，构造标准序列当前节点的项代码。
该式逐字对应 `standard_sequence_from` 的
`binaryUnion (singleton (orderedPair ...)) tail` 语法树。
-/
def canonical_name_sequence_step_code (indexCode tokenCode tailCode : SetTerm) : SetTerm :=
  canonical_name_application_code FunctionSymbol.binaryUnion
    [(canonical_name_application_code FunctionSymbol.singleton
      [(canonical_name_application_code FunctionSymbol.orderedPair
        [indexCode, tokenCode])]),
      tailCode]
/-- 序列名称递归步在三个输入代码均可采纳时仍可采纳。 -/
theorem canonical_name_sequence_step_code_admissible (indexCode tokenCode tailCode : SetTerm) (hIndexCode : Term.Admissible indexCode SetSort.set)
    (hTokenCode : Term.Admissible tokenCode SetSort.set) (hTailCode : Term.Admissible tailCode SetSort.set) :
    Term.Admissible (canonical_name_sequence_step_code
        indexCode tokenCode tailCode) SetSort.set := by
  apply canonical_name_application_code_admissible
  intro argument hArgument
  rcases List.mem_cons.mp hArgument with rfl | hArgument
  · apply canonical_name_application_code_admissible
    intro singletonArgument hSingletonArgument
    rcases List.mem_singleton.mp hSingletonArgument with rfl
    apply canonical_name_application_code_admissible
    intro pairArgument hPairArgument
    rcases List.mem_cons.mp hPairArgument with rfl | hPairArgument
    · exact hIndexCode
    · rcases List.mem_singleton.mp hPairArgument with rfl
      exact hTokenCode
  · rcases List.mem_singleton.mp hArgument with rfl
    exact hTailCode
/-- 序列 quotation 递归步的可组合计算证书。 -/
@[term_check]
theorem canonical_name_sequence_step_code_check
    (indexCode tokenCode tailCode : SetTerm)
    (hIndexCode : Term.CheckCertificate indexCode SetSort.set)
    (hTokenCode : Term.CheckCertificate tokenCode SetSort.set)
    (hTailCode : Term.CheckCertificate tailCode SetSort.set) :
    Term.CheckCertificate
      (canonical_name_sequence_step_code indexCode tokenCode tailCode)
      SetSort.set :=
  Term.check_admissible_complete
    (canonical_name_sequence_step_code_admissible
      indexCode tokenCode tailCode hIndexCode.admissible
      hTokenCode.admissible hTailCode.admissible)
/-- 序列名称递归步与 locally nameless 的 opening 交换。 -/
theorem canonical_name_sequence_step_code_openAt (depth : Nat) (replacement indexCode tokenCode tailCode : SetTerm) :
    Term.openAt SetSort.set depth replacement (canonical_name_sequence_step_code
          indexCode tokenCode tailCode) =
      canonical_name_sequence_step_code (Term.openAt SetSort.set depth replacement indexCode) (Term.openAt SetSort.set depth replacement tokenCode)
        (Term.openAt SetSort.set depth replacement tailCode) := by
  have hNumeralOpen (value : Nat) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  simp [canonical_name_sequence_step_code,
    canonical_name_application_code,
    standard_sequence, standard_sequence_from,
    Term.openAt, hNumeralOpen]
/-- 序列名称递归步与自由变量闭包交换。 -/
theorem canonical_name_sequence_step_code_closeFreeAt (id : FreeVarId) (depth : Nat) (indexCode tokenCode tailCode : SetTerm) :
    Term.closeFreeAt SetSort.set id depth (canonical_name_sequence_step_code
          indexCode tokenCode tailCode) =
      canonical_name_sequence_step_code (Term.closeFreeAt SetSort.set id depth indexCode) (Term.closeFreeAt SetSort.set id depth tokenCode)
        (Term.closeFreeAt SetSort.set id depth tailCode) := by
  have hNumeralClose (value : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
        numₘ(value) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(value)) (finite_numeral_term_admissible value).2 (by
        rw [finite_numeral_term_freeSupport value]
        simp)
  simp [canonical_name_sequence_step_code,
    canonical_name_application_code,
    standard_sequence, standard_sequence_from,
    Term.closeFreeAt, hNumeralClose]
/-- 序列名称递归步与自由变量替换交换。 -/
theorem canonical_name_sequence_step_code_substituteFree (id : FreeVarId) (replacement indexCode tokenCode tailCode : SetTerm) :
    Term.substituteFree SetSort.set id replacement (canonical_name_sequence_step_code
          indexCode tokenCode tailCode) =
      canonical_name_sequence_step_code (Term.substituteFree SetSort.set id replacement indexCode) (Term.substituteFree SetSort.set id replacement tokenCode)
        (Term.substituteFree SetSort.set id replacement tailCode) := by
  have hNumeralFixed (value : Nat) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement (numₘ(value)) (by
        rw [finite_numeral_term_freeSupport value]
        simp)
  simp [canonical_name_sequence_step_code,
    canonical_name_application_code,
    standard_sequence, standard_sequence_from,
    Term.substituteFree, hNumeralFixed]
/-- 打开两个定义公理外层 binder 时，递归步内部的局部变量不受源项替换影响。 -/
private theorem cnc_step_code_open_six (replacement : SetTerm) :
    Term.openAt SetSort.set 6 replacement (canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0) =
      canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0 := by
  have hNumeralOpen (value : Nat) :
      Term.openAt SetSort.set 6 replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 6 replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  simp [canonical_name_sequence_step_code,
    canonical_name_application_code,
    standard_sequence, standard_sequence_from,
    Term.openAt, hNumeralOpen]
/-- 打开候选项 binder 时，递归步内部的局部变量同样保持不变。 -/
private theorem cnc_step_code_open_five (replacement : SetTerm) :
    Term.openAt SetSort.set 5 replacement (canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0) =
      canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0 := by
  have hNumeralOpen (value : Nat) :
      Term.openAt SetSort.set 5 replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 5 replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  simp [canonical_name_sequence_step_code,
    canonical_name_application_code,
    standard_sequence, standard_sequence_from,
    Term.openAt, hNumeralOpen]
/-! ## 规范名称的可计算对象值 -/
/-- 标准 numeral 项 quotation 的显式对象代码。 -/
def canonical_numeral_code : Nat → SetTerm
  | 0 => canonical_name_zero_code
  | value + 1 =>
      canonical_name_successor_code (canonical_numeral_code value)
/-- 从任意序列下标开始，显式计算标准序列项自身的 quotation。 -/
def canonical_name_code_value_from : Nat → List Nat → SetTerm
  | _, [] => canonical_name_zero_code
  | start, token :: rest =>
      canonical_name_sequence_step_code (canonical_numeral_code start) (canonical_numeral_code token) (canonical_name_code_value_from (start + 1) rest)
/-- 标准 token 序列项自身 quotation 的显式对象值。 -/
def canonical_name_code_value (tokens : List Nat) : SetTerm :=
  canonical_name_code_value_from 0 tokens
/-- 标准 numeral 的通用 quotation 精确计算为 `canonical_numeral_code`。 -/
@[simp]
theorem quote_finite_numeral_code_with? (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (value : Nat) :
    Numbered.quote_term_with? freeNaming boundNames (numₘ(value)) =
      some (canonical_numeral_code value) := by
  induction value with
  | zero =>
      simp [finite_numeral_term, canonical_numeral_code,
        canonical_name_zero_code, Numbered.quote_term_with?]
  | succ value ih =>
      simp [finite_numeral_term, canonical_numeral_code,
        canonical_name_successor_code,
        canonical_name_application_code,
        Numbered.quote_term_with?, ih]
/-- 从任意起点构造的标准 token 序列项具有显式 quotation 值。 -/
theorem quote_standard_token_sequence_from_code_with? (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (start : Nat) (tokens : List Nat) :
    Numbered.quote_term_with? freeNaming boundNames (standard_sequence_from start (tokens.map finite_numeral_term)) =
      some (canonical_name_code_value_from start tokens) := by
  induction tokens generalizing start with
  | nil =>
      simp [standard_sequence_from, canonical_name_code_value_from,
        canonical_name_zero_code, Numbered.quote_term_with?]
  | cons token rest ih =>
      simp [standard_sequence_from, canonical_name_code_value_from,
        canonical_name_sequence_step_code,
        canonical_name_application_code,
        Numbered.quote_term_with?, ih]
/-- `canonical_name_code?` 没有选择性：其结果正是上述显式递归值。 -/
@[simp]
theorem canonical_name_code?_eq_value (tokens : List Nat) :
    canonical_name_code? tokens =
      some (canonical_name_code_value tokens) := by
  simpa [canonical_name_code?, canonical_name_term,
    standard_token_sequence, canonical_name_code_value] using (quote_standard_token_sequence_from_code_with?
      free_name [] 0 tokens)
/-- 显式规范名称值继承 quotation 的闭项边界。 -/
theorem canonical_name_code_value_boundary (tokens : List Nat) :
    Numbered.CodeBoundary (canonical_name_code_value tokens) :=
  Numbered.quote_term_with?_code_boundary
    free_name [] (canonical_name_code?_eq_value tokens)
/-- 任意起点处的显式后缀名称代码同样满足 quotation 边界。 -/
theorem canonical_name_code_value_from_boundary (start : Nat) (tokens : List Nat) :
    Numbered.CodeBoundary (canonical_name_code_value_from start tokens) :=
  Numbered.quote_term_with?_code_boundary
    free_name [] (quote_standard_token_sequence_from_code_with?
      free_name [] start tokens)
/--
从每个后缀起点读取的显式名称代码列表。
列表第 `i` 项是原 token 串从第 `i` 个位置起的闭项名称代码，最后一项固定为空集
项代码；它正是 `canonical_name_code_spec` 所需有限轨迹的外部见证。
-/
def canonical_name_suffix_codes_from : Nat → List Nat → List SetTerm
  | _, [] => [canonical_name_zero_code]
  | start, token :: rest =>
      canonical_name_code_value_from start (token :: rest) ::
        canonical_name_suffix_codes_from (start + 1) rest
/-- 后缀名称轨迹的长度恰为源 token 长度加一。 -/
theorem canonical_name_suffix_codes_from_length (start : Nat) (tokens : List Nat) : (canonical_name_suffix_codes_from start tokens).length =
      tokens.length + 1 := by
  induction tokens generalizing start with
  | nil =>
      simp [canonical_name_suffix_codes_from]
  | cons token rest ih =>
      simp [canonical_name_suffix_codes_from, ih]
/-- 后缀名称轨迹在有效位置上精确返回相应后缀的显式 quotation 值。 -/
theorem canonical_name_suffix_codes_from_getElem? (start : Nat) (tokens : List Nat) (index : Nat) (hIndex : index ≤ tokens.length) :
    (canonical_name_suffix_codes_from start tokens)[index]? =
      some (canonical_name_code_value_from (start + index) (tokens.drop index)) := by
  induction tokens generalizing start index with
  | nil =>
      have hZero : index = 0 :=
        Nat.eq_zero_of_le_zero (by simpa using hIndex)
      subst index
      simp [canonical_name_suffix_codes_from,
        canonical_name_code_value_from]
  | cons token rest ih =>
      cases index with
      | zero =>
          simp [canonical_name_suffix_codes_from]
      | succ index =>
          have hTail : index ≤ rest.length :=
            Nat.le_of_succ_le_succ (by simpa using hIndex)
          simpa [canonical_name_suffix_codes_from,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ih (start + 1) index hTail)
/-- 后缀轨迹中的每个代码项均可采纳。 -/
theorem canonical_name_suffix_codes_from_admissible (start : Nat) (tokens : List Nat) :
    ∀ code, code ∈ canonical_name_suffix_codes_from start tokens →
      Term.Admissible code SetSort.set := by
  induction tokens generalizing start with
  | nil =>
      intro code hCode
      rcases List.mem_singleton.mp hCode with rfl
      exact (canonical_name_code_value_from_boundary start []).1
  | cons token rest ih =>
      intro code hCode
      rcases List.mem_cons.mp hCode with rfl | hCode
      · exact (canonical_name_code_value_from_boundary
          start (token :: rest)).1
      · exact ih (start + 1) code hCode
/-- 后缀轨迹中的每个 quotation 代码都携带纯函数检查证书。 -/
theorem canonical_name_suffix_codes_from_check (start : Nat) (tokens : List Nat) :
    ∀ code, code ∈ canonical_name_suffix_codes_from start tokens →
      Term.CheckCertificate code SetSort.set := by
  induction tokens generalizing start with
  | nil =>
      intro code hCode
      rcases List.mem_singleton.mp hCode with rfl
      exact
        (canonical_name_code_value_from_boundary
          start []).check_certificate
  | cons token rest ih =>
      intro code hCode
      rcases List.mem_cons.mp hCode with rfl | hCode
      · exact
          (canonical_name_code_value_from_boundary
            start (token :: rest)).check_certificate
      · exact ih (start + 1) code hCode
/-- 后缀 quotation 轨迹组成的标准序列可由成员证书直接计算检查。 -/
@[term_check]
theorem canonical_name_suffix_sequence_check (start : Nat) (tokens : List Nat) :
    Term.CheckCertificate
      (standard_sequence (canonical_name_suffix_codes_from start tokens))
      SetSort.set :=
  standard_sequence_from_check 0
    (canonical_name_suffix_codes_from_check start tokens)
/-- 后缀轨迹中的每个代码项都不含自由对象变量。 -/
theorem canonical_name_suffix_codes_from_freeSupport_nil (start : Nat) (tokens : List Nat) :
    ∀ code, code ∈ canonical_name_suffix_codes_from start tokens →
      Term.freeSupport code = [] := by
  induction tokens generalizing start with
  | nil =>
      intro code hCode
      rcases List.mem_singleton.mp hCode with rfl
      exact (canonical_name_code_value_from_boundary start []).2
  | cons token rest ih =>
      intro code hCode
      rcases List.mem_cons.mp hCode with rfl | hCode
      · exact (canonical_name_code_value_from_boundary
          start (token :: rest)).2
      · exact ih (start + 1) code hCode
/--
标准 numeral quotation 函数的递归方程。
这里使用真正的 de Bruijn 局部 binder，不占用任何全局 free-variable 编号；因此
后续对角关系无需额外携带“避开保留编号”的接口。
-/
def numeral_name_code_definition_axiom : SetFormula := (num_name_codeₘ(numₘ(0)) ≐ₘ canonical_name_zero_code) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ ωₘ) ⟶ₘ
        (num_name_codeₘ(Sₘ(bₛ#0)) ≐ₘ
          canonical_name_successor_code (num_name_codeₘ(bₛ#0))))
/-- 规范序列名称轨迹在一个源位置上的局部递归条件。 -/
def canonical_name_sequence_step_condition (source trace index token current next : SetTerm) :
    SetFormula := (⟨index, token⟩ₘ ∈ₘ source) ∧ₘ (((⟨index, current⟩ₘ ∈ₘ trace) ∧ₘ (⟨Sₘ(index), next⟩ₘ ∈ₘ trace)) ∧ₘ (current ≐ₘ
        canonical_name_sequence_step_code (num_name_codeₘ(index)) (num_name_codeₘ(token)) next))
/-- 单步递归条件与自由变量替换逐参数交换。 -/
theorem canonical_name_sequence_step_condition_substituteFree (id : FreeVarId) (replacement source trace index token current next : SetTerm) :
    Formula.substituteFree SetSort.set id replacement (canonical_name_sequence_step_condition
          source trace index token current next) =
      canonical_name_sequence_step_condition (Term.substituteFree SetSort.set id replacement source) (Term.substituteFree SetSort.set id replacement trace)
        (Term.substituteFree SetSort.set id replacement index) (Term.substituteFree SetSort.set id replacement token)
        (Term.substituteFree SetSort.set id replacement current) (Term.substituteFree SetSort.set id replacement next) := by
  simp [canonical_name_sequence_step_condition,
    Formula.substituteFree, Term.substituteFree,
    canonical_name_sequence_step_code_substituteFree]
/-- 给定源序列、递归轨迹与位置后的三重见证结论。 -/
def canonical_name_code_recurrence (source trace index : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    ∃ₘ[SetSort.set],
      ∃ₘ[SetSort.set],
        canonical_name_sequence_step_condition
          source trace index bₛ#2 bₛ#1 bₛ#0
/-- 三重递归见证结论与自由变量替换交换。 -/
theorem canonical_name_code_recurrence_substituteFree (id : FreeVarId) (replacement source trace index : SetTerm) :
    Formula.substituteFree SetSort.set id replacement (canonical_name_code_recurrence source trace index) =
      canonical_name_code_recurrence (Term.substituteFree SetSort.set id replacement source) (Term.substituteFree SetSort.set id replacement trace)
        (Term.substituteFree SetSort.set id replacement index) := by
  simp [canonical_name_code_recurrence,
    Formula.substituteFree, Term.substituteFree,
    canonical_name_sequence_step_condition_substituteFree]
/--
`candidate` 是 token 串 `source` 的规范闭项代码。
存在量化的轨迹保存从每个后缀起点开始的项代码；末端是空集代码，向前一步按
`canonical_name_sequence_step_code` 唯一重建。所有局部量词均直接使用 de Bruijn
binder，因而规格可安全嵌入任意外层公式。
-/
def canonical_name_code_spec (source candidate : SetTerm) : SetFormula := (source ∈ₘ CodeStrₘ) ∧ₘ (∃ₘ[SetSort.set],
      finite_sequence_condition bₛ#0 ∧ₘ ((domₘ(bₛ#0) ≐ₘ Sₘ(domₘ(source))) ∧ₘ ((⟨domₘ(source), canonical_name_zero_code⟩ₘ ∈ₘ bₛ#0) ∧ₘ
            ((⟨numₘ(0), candidate⟩ₘ ∈ₘ bₛ#0) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(source)) ⟶ₘ
                  canonical_name_code_recurrence
                    source bₛ#4 bₛ#3)))))
/-- 规范名称代码函数的开放定义实例。 -/
def canonical_name_code_definition_instance (source candidate : SetTerm) : SetFormula := (candidate ≐ₘ name_codeₘ(source)) ↔ₘ
    canonical_name_code_spec source candidate
/--
规范名称代码函数的闭定义公理。
该式直接在两个外层 binder 下写出规格，避免借助任意 free-variable 编号再关闭；
其中最深递归步的 de Bruijn 顺序依次为
`next,current,token,index,trace,candidate,source`。
-/
def canonical_name_code_definition_axiom : SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set], (bₛ#0 ≐ₘ name_codeₘ(bₛ#1)) ↔ₘ ((bₛ#1 ∈ₘ CodeStrₘ) ∧ₘ (∃ₘ[SetSort.set],
            finite_sequence_condition bₛ#0 ∧ₘ ((domₘ(bₛ#0) ≐ₘ Sₘ(domₘ(bₛ#2))) ∧ₘ ((⟨domₘ(bₛ#2), canonical_name_zero_code⟩ₘ ∈ₘ bₛ#0) ∧ₘ
                  ((⟨numₘ(0), bₛ#1⟩ₘ ∈ₘ bₛ#0) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(bₛ#3)) ⟶ₘ (∃ₘ[SetSort.set],
                          ∃ₘ[SetSort.set],
                            ∃ₘ[SetSort.set],
                              canonical_name_sequence_step_condition
                                bₛ#6 bₛ#4 bₛ#3 bₛ#2 bₛ#1 bₛ#0)))))))
/-- Gödel quotation 理论加入规范命名递归定义后的稳定入口。 -/
def code_naming_theory : SetTheory :=
  Theory.insert canonical_name_code_definition_axiom (Theory.insert numeral_name_code_definition_axiom
      godel_quotation_theory)
/-- numeral quotation 递归方程是良构闭公式。 -/
theorem numeral_name_code_definition_axiom_admissible :
    Formula.Admissible numeral_name_code_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 规范名称代码定义公理是良构闭公式。 -/
theorem canonical_name_code_definition_axiom_admissible :
    Formula.Admissible canonical_name_code_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
/-- 规范名称代码理论中的每条公理都是句子。 -/
@[derive_close_sentence]
theorem code_naming_theory_sentence
    {formula : SetFormula} (hFormula : code_naming_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · exact ⟨canonical_name_code_definition_axiom_admissible, by native_decide⟩
  · rcases hFormula with rfl | hFormula
    · exact ⟨numeral_name_code_definition_axiom_admissible, by native_decide⟩
    · exact godel_quotation_theory_sentence hFormula
/-- 原 Gödel quotation 理论的推导可直接提升到规范名称代码理论。 -/
theorem code_naming_weaken_godel_quotation
    {formula : SetFormula} (derivation : ⊢ₘ[godel_quotation_theory] formula) :
    ⊢ₘ[code_naming_theory] formula :=
  FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inr (Or.inr hFormula)) derivation
/-- 标准序列语义推导可直接提升到规范名称代码理论。 -/
theorem code_naming_weaken_standard_sequence
    {formula : SetFormula} (derivation : ⊢ₘ[standard_sequence_semantics_theory] formula) :
    ⊢ₘ[code_naming_theory] formula :=
  code_naming_weaken_godel_quotation <|
    FirstOrder.Derives.theory_weaken (fun _ hFormula => Or.inl hFormula) derivation
/-- 规范名称代码函数项保持对象项可采纳性。 -/
theorem canonical_name_code_term_admissible (source : SetTerm) (hSource : Term.Admissible source SetSort.set) :
    Term.Admissible (name_codeₘ(source)) SetSort.set := by
  simpa using
    set_function_application_admissible
      .canonicalNameCode [⟨source, by assumption⟩]
      (by rfl) (by rfl)
/-- numeral quotation 函数项保持对象项可采纳性。 -/
theorem numeral_name_code_term_admissible (number : SetTerm) (hNumber : Term.Admissible number SetSort.set) :
    Term.Admissible (num_name_codeₘ(number)) SetSort.set := by
  simpa using
    set_function_application_admissible
      .numeralNameCode [⟨number, by assumption⟩]
      (by rfl) (by rfl)
/-- 规范名称代码函数定义可在任意两个闭集合项处实例化。 -/
theorem canonical_name_code_definition_instance_derives (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[code_naming_theory]
      canonical_name_code_definition_instance source candidate := by
  have hAxiom :
      ⊢ₘ[code_naming_theory]
        canonical_name_code_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hSourceInstance := FirstOrder.Derives.forall_elim
    (term := source) hAxiom
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hSourceInstance
  have hSourceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term source hSource.2
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  have hZeroAdmissible :
      Term.Admissible canonical_name_zero_code SetSort.set :=
    constant_code_term_admissible _ (finite_numeral_term_admissible _)
  have hZeroOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term canonical_name_zero_code =
        canonical_name_zero_code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term canonical_name_zero_code hZeroAdmissible.2
  have hStepSourceOpen :
      Term.openAt SetSort.set 6 source (canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0) =
        canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0 := by
    exact cnc_step_code_open_six source
  have hStepCandidateOpen :
      Term.openAt SetSort.set 5 candidate (canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0) =
        canonical_name_sequence_step_code (num_name_codeₘ(bₛ#3)) (num_name_codeₘ(bₛ#2)) bₛ#0 := by
    exact cnc_step_code_open_five candidate
  simpa [canonical_name_code_definition_axiom,
    canonical_name_code_definition_instance,
    canonical_name_code_spec,
    canonical_name_sequence_step_condition,
    finite_sequence_condition, is_function_formula,
    finite_numeral_term,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Term.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hSourceOpen, hCandidateOpen,
    hZeroOpen, hStepSourceOpen, hStepCandidateOpen] using
      hCandidateInstance
/-- 规范名称定义右侧对任意两个 admissible 参数自动保持公式边界。 -/
theorem canonical_name_code_spec_admissible (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    Formula.Admissible (canonical_name_code_spec source candidate) :=
  Formula.Admissible.iff_right <| (canonical_name_code_definition_instance_derives
      source candidate hSource hCandidate).admissible
/--
规范名称轨迹在任意 admissible 源、轨迹和位置处的三重递归见证均为 admissible。
该证书从完整名称规格逐层打开轨迹与位置量词后反演得到，因此定义公理、具体
numeral 见证和有限定义域装配共享同一条规格边界。
-/
theorem canonical_name_code_recurrence_admissible (source trace index : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hTrace : Term.Admissible trace SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible (canonical_name_code_recurrence source trace index) := by
  have hSourceOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement source hSource.2
  have hTraceOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement trace = trace :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement trace hTrace.2
  have hSpec :=
    canonical_name_code_spec_admissible
      source source hSource hSource
  rw [canonical_name_code_spec] at hSpec
  have hTraceExistential :=
    Formula.Admissible.conj_right hSpec
  change
    Formula.Admissible ((Formula.existsE SetSort.set _) : SetFormula)
    at hTraceExistential
  have hTraceBody :=
    Formula.Admissible.exists_openAt (body :=
        finite_sequence_condition bₛ#0 ∧ₘ ((domₘ(bₛ#0) ≐ₘ Sₘ(domₘ(source))) ∧ₘ ((⟨domₘ(source), canonical_name_zero_code⟩ₘ ∈ₘ bₛ#0) ∧ₘ
              ((⟨numₘ(0), source⟩ₘ ∈ₘ bₛ#0) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(source)) ⟶ₘ
                    canonical_name_code_recurrence
                      source bₛ#4 bₛ#3)))))
      SetSort.set hTraceExistential hTrace
  have hAfterDomain :=
    Formula.Admissible.conj_right hTraceBody
  have hAfterTerminal :=
    Formula.Admissible.conj_right hAfterDomain
  have hAfterInitial :=
    Formula.Admissible.conj_right hAfterTerminal
  have hPointwise :=
    Formula.Admissible.conj_right hAfterInitial
  have hPointwiseNormalized :
      Formula.Admissible (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(source)) ⟶ₘ
            canonical_name_code_recurrence source trace bₛ#3) := by
    simpa [canonical_name_code_recurrence,
      canonical_name_sequence_step_condition,
      canonical_name_sequence_step_code_openAt,
      Formula.openAt, Term.openAt, Formula.next_depth,
      set_bound_variable, hSourceOpen, hTraceOpen] using
      hPointwise
  have hPointBody :=
    Formula.Admissible.forall_openAt (σ := Nonlogical.BasicSetTheory.signature) (body := (bₛ#0 ∈ₘ domₘ(source)) ⟶ₘ
          canonical_name_code_recurrence source trace bₛ#3) (term := index)
      SetSort.set hPointwiseNormalized hIndex
  have hRecurrence :=
    Formula.Admissible.imp_right hPointBody
  have hZero :
      Term.Admissible canonical_name_zero_code SetSort.set :=
    constant_code_term_admissible _ (finite_numeral_term_admissible _)
  have hZeroOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          canonical_name_zero_code =
        canonical_name_zero_code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement canonical_name_zero_code hZero.2
  have hNumeralOpen (depth : Nat) (replacement : SetTerm) (value : Nat) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  simpa [canonical_name_code_spec,
    Formula.openAt, Formula.next_depth, Term.openAt,
    finite_sequence_condition, is_function_formula,
    canonical_name_code_recurrence,
    canonical_name_sequence_step_condition,
    canonical_name_sequence_step_code_openAt,
    hSourceOpen, hTraceOpen, hZeroOpen, hNumeralOpen] using
    hRecurrence
/-- 规范名称递归公式的检查证书由三个对象项证书组合。 -/
@[formula_check]
theorem canonical_name_code_recurrence_check
    (source trace index : SetTerm)
    (hSource : Term.CheckCertificate source SetSort.set)
    (hTrace : Term.CheckCertificate trace SetSort.set)
    (hIndex : Term.CheckCertificate index SetSort.set) :
    Formula.CheckCertificate
      (canonical_name_code_recurrence source trace index) :=
  Formula.check_admissible_complete <|
    canonical_name_code_recurrence_admissible
      source trace index hSource.admissible hTrace.admissible
      hIndex.admissible
/-! ## numeral quotation 函数的内部求值 -/
/-- numeral quotation 函数在零点的值。 -/
theorem numeral_name_code_zero_derives :
    ⊢ₘ[code_naming_theory]
      num_name_codeₘ(numₘ(0)) ≐ₘ canonical_name_zero_code := by
  exact FirstOrder.Derives.conjElimLeft <|
    FirstOrder.Derives.theory_mem (by exact Or.inr (Or.inl rfl))
/-- numeral quotation 函数在任意自然数后继处满足递归方程。 -/
theorem numeral_name_code_successor_derives (number : SetTerm) (hNumber : Term.Admissible number SetSort.set) :
    ⊢ₘ[code_naming_theory] (number ∈ₘ ωₘ) ⟶ₘ (num_name_codeₘ(Sₘ(number)) ≐ₘ
          canonical_name_successor_code (num_name_codeₘ(number))) := by
  have hAxiom :
      ⊢ₘ[code_naming_theory]
        numeral_name_code_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inr (Or.inl rfl))
  have hRecurrence := FirstOrder.Derives.conjElimRight hAxiom
  have hInstance := FirstOrder.Derives.forall_elim
    (term := number) hRecurrence
  have hNumberOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term number = number :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term number hNumber.2
  simpa [numeral_name_code_definition_axiom,
    Formula.openAt, Term.openAt,
    canonical_name_successor_code_openAt,
    hNumberOpen] using hInstance
/-- 显式后继 quotation 构造尊重已经证明的代码等式。 -/
theorem canonical_name_successor_code_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      canonical_name_successor_code left ≐ₘ
        canonical_name_successor_code right := by
  let parameter := FreshVariable.fresh_id SetSort.set
    [Formula.equal left left]
  let leftSuccessor := canonical_name_successor_code left
  let body : SetFormula :=
    leftSuccessor ≐ₘ
      canonical_name_successor_code (x#parameter)
  have hParameterFreshLeft : (SetSort.set, parameter) ∉ Term.freeSupport left := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m SetSort.set left
  have hLeftFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement left = left :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement left hParameterFreshLeft
  have hReflexive :
      Γ ⊢ₘ[T] body⟪SetSort.set, parameter ↦ left⟫ₘ := by
    simpa [body, leftSuccessor,
      Formula.substituteFree, Term.substituteFree,
      canonical_name_successor_code_substituteFree,
      hLeftFixed, set_variable] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) leftSuccessor)
  have hTransported := FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
    (left := left) (right := right) (body := body)
    hEquality hReflexive
  simpa [body, leftSuccessor,
    Formula.substituteFree, Term.substituteFree,
    canonical_name_successor_code_substituteFree,
    hLeftFixed, set_variable] using hTransported
/--
序列名称递归步同时尊重位置代码与 token 代码的已证等式。
尾代码保持不变；两个坐标依次通过通用 Leibniz 替换运输，避免向等词内核加入
任何专用合同规则。
-/
theorem canonical_name_sequence_step_code_congr_of_equalities
    {T : SetTheory} {Γ : Context signature} (indexLeft indexRight tokenLeft tokenRight tailCode : SetTerm) (hIndexLeft : Term.Admissible indexLeft SetSort.set)
    (hIndexRight : Term.Admissible indexRight SetSort.set) (hTokenLeft : Term.Admissible tokenLeft SetSort.set)
    (hTokenRight : Term.Admissible tokenRight SetSort.set) (hTailCode : Term.Admissible tailCode SetSort.set) (hIndexEquality : Γ ⊢ₘ[T] indexLeft ≐ₘ indexRight)
    (hTokenEquality : Γ ⊢ₘ[T] tokenLeft ≐ₘ tokenRight) :
    Γ ⊢ₘ[T]
      canonical_name_sequence_step_code
          indexLeft tokenLeft tailCode ≐ₘ
        canonical_name_sequence_step_code
          indexRight tokenRight tailCode := by
  let leftStep :=
    canonical_name_sequence_step_code indexLeft tokenLeft tailCode
  let middleStep :=
    canonical_name_sequence_step_code indexRight tokenLeft tailCode
  let indexParameter := FreshVariable.fresh_id SetSort.set
    [leftStep ≐ₘ leftStep, tokenLeft ≐ₘ tokenLeft,
      tailCode ≐ₘ tailCode]
  let indexBody : SetFormula :=
    leftStep ≐ₘ canonical_name_sequence_step_code (x#indexParameter) tokenLeft tailCode
  have hLeftStep :
      Term.Admissible leftStep SetSort.set :=
    canonical_name_sequence_step_code_admissible
      indexLeft tokenLeft tailCode hIndexLeft hTokenLeft hTailCode
  have hMiddleStep :
      Term.Admissible middleStep SetSort.set :=
    canonical_name_sequence_step_code_admissible
      indexRight tokenLeft tailCode hIndexRight hTokenLeft hTailCode
  have hIndexLeftFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexParameter replacement leftStep =
        leftStep := by
    apply Term.substituteFree_eq_self_of_not_mem
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [leftStep ≐ₘ leftStep, tokenLeft ≐ₘ tokenLeft,
          tailCode ≐ₘ tailCode]) (formula := leftStep ≐ₘ leftStep) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hIndexTokenFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexParameter replacement tokenLeft =
        tokenLeft := by
    apply Term.substituteFree_eq_self_of_not_mem
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [leftStep ≐ₘ leftStep, tokenLeft ≐ₘ tokenLeft,
          tailCode ≐ₘ tailCode]) (formula := tokenLeft ≐ₘ tokenLeft) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hIndexTailFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set indexParameter replacement tailCode =
        tailCode := by
    apply Term.substituteFree_eq_self_of_not_mem
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [leftStep ≐ₘ leftStep, tokenLeft ≐ₘ tokenLeft,
          tailCode ≐ₘ tailCode]) (formula := tailCode ≐ₘ tailCode) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hIndexReflexive :
      Γ ⊢ₘ[T]
        indexBody⟪SetSort.set, indexParameter ↦ indexLeft⟫ₘ := by
    simpa [indexBody, Formula.substituteFree, Term.substituteFree,
      canonical_name_sequence_step_code_substituteFree,
      hIndexLeftFixed, hIndexTokenFixed, hIndexTailFixed,
      set_variable] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) leftStep)
  have hIndexTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := indexParameter) (left := indexLeft) (right := indexRight)
      (body := indexBody)
      hIndexEquality hIndexReflexive
  have hMiddleEquality :
      Γ ⊢ₘ[T] leftStep ≐ₘ middleStep := by
    simpa [indexBody, leftStep, middleStep,
      Formula.substituteFree, Term.substituteFree,
      canonical_name_sequence_step_code_substituteFree,
      hIndexLeftFixed, hIndexTokenFixed, hIndexTailFixed,
      set_variable] using hIndexTransport
  let tokenParameter := FreshVariable.fresh_id SetSort.set
    [leftStep ≐ₘ leftStep, middleStep ≐ₘ middleStep,
      indexRight ≐ₘ indexRight, tailCode ≐ₘ tailCode]
  let tokenBody : SetFormula :=
    leftStep ≐ₘ canonical_name_sequence_step_code
      indexRight (x#tokenParameter) tailCode
  have hTokenLeftStepFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set tokenParameter replacement leftStep =
        leftStep := by
    apply Term.substituteFree_eq_self_of_not_mem
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [leftStep ≐ₘ leftStep, middleStep ≐ₘ middleStep,
          indexRight ≐ₘ indexRight, tailCode ≐ₘ tailCode]) (formula := leftStep ≐ₘ leftStep) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hTokenIndexFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set tokenParameter replacement indexRight =
        indexRight := by
    apply Term.substituteFree_eq_self_of_not_mem
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [leftStep ≐ₘ leftStep, middleStep ≐ₘ middleStep,
          indexRight ≐ₘ indexRight, tailCode ≐ₘ tailCode]) (formula := indexRight ≐ₘ indexRight) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hTokenTailFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set tokenParameter replacement tailCode =
        tailCode := by
    apply Term.substituteFree_eq_self_of_not_mem
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas :=
        [leftStep ≐ₘ leftStep, middleStep ≐ₘ middleStep,
          indexRight ≐ₘ indexRight, tailCode ≐ₘ tailCode]) (formula := tailCode ≐ₘ tailCode) (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hTokenSource :
      Γ ⊢ₘ[T]
        tokenBody⟪SetSort.set, tokenParameter ↦ tokenLeft⟫ₘ := by
    simpa [tokenBody, leftStep, middleStep,
      Formula.substituteFree, Term.substituteFree,
      canonical_name_sequence_step_code_substituteFree,
      hTokenLeftStepFixed, hTokenIndexFixed, hTokenTailFixed,
      set_variable] using hMiddleEquality
  have hTokenTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := tokenParameter) (left := tokenLeft) (right := tokenRight)
      (body := tokenBody)
      hTokenEquality hTokenSource
  simpa [tokenBody, leftStep,
    Formula.substituteFree, Term.substituteFree,
    canonical_name_sequence_step_code_substituteFree,
    hTokenLeftStepFixed, hTokenIndexFixed, hTokenTailFixed,
    set_variable] using hTokenTransport
/-- 对每个外部自然数，numeral quotation 对象函数计算为显式语法代码。 -/
theorem numeral_name_code_value_derives (value : Nat) :
    ⊢ₘ[code_naming_theory]
      num_name_codeₘ(numₘ(value)) ≐ₘ canonical_numeral_code value := by
  induction value with
  | zero =>
      simpa [canonical_numeral_code] using
        numeral_name_code_zero_derives
  | succ value ih =>
      let number := numₘ(value)
      let functionCode := num_name_codeₘ(number)
      let explicitCode := canonical_numeral_code value
      let middle := canonical_name_successor_code functionCode
      let result := canonical_name_successor_code explicitCode
      have hNumber : Term.Admissible number SetSort.set :=
        finite_numeral_term_admissible value
      have hFunctionCode : Term.Admissible functionCode SetSort.set :=
        numeral_name_code_term_admissible number hNumber
      have hExplicitCode : Term.Admissible explicitCode SetSort.set := (Numbered.quote_term_with?_code_boundary
          free_name [] (quote_finite_numeral_code_with?
            free_name [] value)).1
      have hRecurrence := FirstOrder.Derives.impElim (numeral_name_code_successor_derives number hNumber) (code_naming_weaken_standard_sequence
          (standard_sequence_finite_numeral_mem_omega value))
      have hCongruence :
          ⊢ₘ[code_naming_theory] middle ≐ₘ result := by
        exact canonical_name_successor_code_congr_of_equality
          functionCode explicitCode hFunctionCode hExplicitCode (by simpa [functionCode, explicitCode, number] using ih)
      have hValue := Metatheory.Derives.equality_trans
        (by simpa [middle, functionCode, number] using hRecurrence) hCongruence
      simpa [finite_numeral_term, canonical_numeral_code,
        number, explicitCode, result] using hValue
/-! ## 规范名称递归的内部正确性 -/
/-- 后缀轨迹的定义域恰比源 token 序列的定义域多一个位置。 -/
theorem canonical_name_trace_domain_derives (tokens : List Nat) :
    ⊢ₘ[code_naming_theory]
      domₘ(standard_sequence (canonical_name_suffix_codes_from 0 tokens)) ≐ₘ
        Sₘ(domₘ(standard_token_sequence tokens)) := by
  let source := standard_token_sequence tokens
  let trace := standard_sequence (canonical_name_suffix_codes_from 0 tokens)
  have hSource : Term.Admissible source SetSort.set :=
    standard_token_sequence_admissible tokens
  have hTrace : Term.Admissible trace SetSort.set :=
    seq_admissible_m 0 (canonical_name_suffix_codes_from_admissible 0 tokens)
  have hSourceDomain :
      ⊢ₘ[code_naming_theory] domₘ(source) ≐ₘ numₘ(tokens.length) :=
    code_naming_weaken_standard_sequence (standard_token_sequence_domain_eq_length tokens)
  have hTraceDomainRaw :=
    code_naming_weaken_standard_sequence (standard_sequence_domain_eq_numeral_length (canonical_name_suffix_codes_from_admissible 0 tokens)
        (stdseq_element_fresh_of_support_nil
          (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens) 0)
        (stdseq_element_fresh_of_support_nil
          (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens) 1))
  have hTraceDomain :
      ⊢ₘ[code_naming_theory] domₘ(trace) ≐ₘ
        Sₘ(numₘ(tokens.length)) := by
    simpa [trace, canonical_name_suffix_codes_from_length,
      finite_numeral_term] using hTraceDomainRaw
  have hDomain : Term.Admissible (domₘ(source)) SetSort.set :=
    domain_term_admissible source hSource
  have hNumeral : Term.Admissible (numₘ(tokens.length)) SetSort.set :=
    finite_numeral_term_admissible _
  have hSuccessorSource :
      ⊢ₘ[code_naming_theory]
        Sₘ(numₘ(tokens.length)) ≐ₘ Sₘ(domₘ(source)) :=
    successor_term_congr_of_equality (numₘ(tokens.length)) (domₘ(source))
      hNumeral hDomain (Metatheory.Derives.equality_symm
        hSourceDomain)
  have hResult := Metatheory.Derives.equality_trans
    hTraceDomain hSuccessorSource
  simpa [source, trace] using hResult
/-- 后缀轨迹的末端位置保存空序列项的 quotation。 -/
theorem canonical_name_trace_terminal_derives (tokens : List Nat) :
    ⊢ₘ[code_naming_theory]
      ⟨domₘ(standard_token_sequence tokens), canonical_name_zero_code⟩ₘ ∈ₘ
        standard_sequence (canonical_name_suffix_codes_from 0 tokens) := by
  let source := standard_token_sequence tokens
  let trace := standard_sequence (canonical_name_suffix_codes_from 0 tokens)
  let numeral := numₘ(tokens.length)
  let zero := canonical_name_zero_code
  have hSource : Term.Admissible source SetSort.set :=
    standard_token_sequence_admissible tokens
  have hNumeral : Term.Admissible numeral SetSort.set :=
    finite_numeral_term_admissible _
  have hZero : Term.Admissible zero SetSort.set :=
    constant_code_term_admissible _ (finite_numeral_term_admissible _)
  have hTrace : Term.Admissible trace SetSort.set :=
    seq_admissible_m 0 (canonical_name_suffix_codes_from_admissible 0 tokens)
  have hSourceDomain :
      ⊢ₘ[code_naming_theory] domₘ(source) ≐ₘ numeral :=
    code_naming_weaken_standard_sequence (standard_token_sequence_domain_eq_length tokens)
  have hGet : (canonical_name_suffix_codes_from 0 tokens)[tokens.length]? =
        some zero := by
    simpa [zero, canonical_name_zero_code] using (canonical_name_suffix_codes_from_getElem?
        0 tokens tokens.length (Nat.le_refl _))
  have hGraphRaw :=
    code_naming_weaken_standard_sequence (standard_sequence_from_getElem?_graph_mem
        0 hGet (canonical_name_suffix_codes_from_admissible 0 tokens)
        hZero)
  have hGraph :
      ⊢ₘ[code_naming_theory]
        ⟨numeral, zero⟩ₘ ∈ₘ trace := by
    simpa [trace, numeral, zero] using hGraphRaw
  let parameter : FreeVarId := 340
  let body : SetFormula :=
    ⟨x#parameter, zero⟩ₘ ∈ₘ trace
  have hZeroFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement zero = zero :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement zero (by
        rw [show Term.freeSupport zero = [] by
          simpa [zero, canonical_name_zero_code,
            canonical_name_code_value_from] using (canonical_name_code_value_from_boundary 0 []).2]
        simp)
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement trace = trace :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement trace (by
        dsimp [trace]
        rw [seq_support_nil_m 0 (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens)]
        simp)
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := code_naming_theory) (Γ := []) (sort := SetSort.set) (eigen := parameter)
      (left := numeral) (right := domₘ(source)) (body := body)
      (Metatheory.Derives.equality_symm hSourceDomain)
  have hTransport :
      ⊢ₘ[code_naming_theory] (⟨numeral, zero⟩ₘ ∈ₘ trace) ↔ₘ (⟨domₘ(source), zero⟩ₘ ∈ₘ trace) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      set_variable, hZeroFixed, hTraceFixed] using hIff
  simpa [source, trace, zero] using
    FirstOrder.Derives.iffElimRight hTransport hGraph
/-- 后缀轨迹的首位置保存整个标准 token 序列项的 quotation。 -/
theorem canonical_name_trace_initial_derives (tokens : List Nat) :
    ⊢ₘ[code_naming_theory]
      ⟨numₘ(0), canonical_name_code_value tokens⟩ₘ ∈ₘ
        standard_sequence (canonical_name_suffix_codes_from 0 tokens) := by
  let trace := standard_sequence (canonical_name_suffix_codes_from 0 tokens)
  let candidate := canonical_name_code_value tokens
  have hCandidate : Term.Admissible candidate SetSort.set := (canonical_name_code_value_boundary tokens).1
  have hGet : (canonical_name_suffix_codes_from 0 tokens)[0]? =
        some candidate := by
    simpa [candidate] using (canonical_name_suffix_codes_from_getElem?
        0 tokens 0 (Nat.zero_le _))
  have hGraph :=
    code_naming_weaken_standard_sequence (standard_sequence_from_getElem?_graph_mem
        0 hGet (canonical_name_suffix_codes_from_admissible 0 tokens)
        hCandidate)
  simpa [trace, candidate] using hGraph
/-- 源序列的一个具体位置满足规范名称轨迹的单步递归条件。 -/
theorem canonical_name_sequence_step_value_derives (tokens : List Nat) (index token : Nat) (hGet : tokens[index]? = some token) :
    ⊢ₘ[code_naming_theory]
      canonical_name_sequence_step_condition (standard_token_sequence tokens) (standard_sequence (canonical_name_suffix_codes_from 0 tokens)) (numₘ(index))
        (numₘ(token)) (canonical_name_code_value_from index (tokens.drop index)) (canonical_name_code_value_from (index + 1) (tokens.drop (index + 1))) := by
  let source := standard_token_sequence tokens
  let trace := standard_sequence (canonical_name_suffix_codes_from 0 tokens)
  let current := canonical_name_code_value_from index (tokens.drop index)
  let next :=
    canonical_name_code_value_from (index + 1) (tokens.drop (index + 1))
  let indexCode := canonical_numeral_code index
  let tokenCode := canonical_numeral_code token
  let functionIndex := num_name_codeₘ(numₘ(index))
  let functionToken := num_name_codeₘ(numₘ(token))
  have hIndex : index < tokens.length := by
    rcases List.getElem?_eq_some_iff.mp hGet with ⟨hIndex, _⟩
    exact hIndex
  have hIndexLe : index ≤ tokens.length := Nat.le_of_lt hIndex
  have hNextLe : index + 1 ≤ tokens.length :=
    Nat.succ_le_iff.mpr hIndex
  have hElements :
      ∀ item, item ∈ tokens.map finite_numeral_term →
        Term.Admissible item SetSort.set := by
    intro item hItem
    rcases List.mem_map.mp hItem with ⟨number, _, rfl⟩
    exact finite_numeral_term_admissible number
  have hSourceGraph :
      ⊢ₘ[code_naming_theory]
        ⟨numₘ(index), numₘ(token)⟩ₘ ∈ₘ source := by
    have hMapped : (tokens.map finite_numeral_term)[index]? =
          some (numₘ(token)) := by
      simpa using congrArg (Option.map finite_numeral_term) hGet
    have hGraph :=
      code_naming_weaken_standard_sequence (standard_sequence_from_getElem?_graph_mem
          0 hMapped hElements (finite_numeral_term_admissible token))
    simpa [source, standard_token_sequence] using hGraph
  have hCurrent : Term.Admissible current SetSort.set := (canonical_name_code_value_from_boundary index (tokens.drop index)).1
  have hNext : Term.Admissible next SetSort.set := (canonical_name_code_value_from_boundary (index + 1) (tokens.drop (index + 1))).1
  have hTraceCurrent :
      ⊢ₘ[code_naming_theory]
        ⟨numₘ(index), current⟩ₘ ∈ₘ trace := by
    have hGetCurrent : (canonical_name_suffix_codes_from 0 tokens)[index]? =
          some current := by
      simpa [current] using (canonical_name_suffix_codes_from_getElem?
          0 tokens index hIndexLe)
    have hGraph :=
      code_naming_weaken_standard_sequence (standard_sequence_from_getElem?_graph_mem
          0 hGetCurrent (canonical_name_suffix_codes_from_admissible 0 tokens)
          hCurrent)
    simpa [trace] using hGraph
  have hTraceNext :
      ⊢ₘ[code_naming_theory]
        ⟨Sₘ(numₘ(index)), next⟩ₘ ∈ₘ trace := by
    have hGetNext : (canonical_name_suffix_codes_from 0 tokens)[index + 1]? =
          some next := by
      simpa [next] using (canonical_name_suffix_codes_from_getElem?
          0 tokens (index + 1) hNextLe)
    have hGraph :=
      code_naming_weaken_standard_sequence (standard_sequence_from_getElem?_graph_mem
          0 hGetNext (canonical_name_suffix_codes_from_admissible 0 tokens)
          hNext)
    simpa [trace, finite_numeral_term] using hGraph
  have hDrop :
      tokens.drop index = token :: tokens.drop (index + 1) := by
    rcases List.getElem?_eq_some_iff.mp hGet with ⟨hIndex, hValue⟩
    simpa [hValue] using (List.drop_eq_getElem_cons (l := tokens) hIndex)
  have hExplicit :
      ⊢ₘ[code_naming_theory]
        current ≐ₘ
          canonical_name_sequence_step_code indexCode tokenCode next := by
    simpa [current, next, indexCode, tokenCode, hDrop,
      canonical_name_code_value_from] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) current)
  have hFunctionIndex : Term.Admissible functionIndex SetSort.set :=
    numeral_name_code_term_admissible (numₘ(index)) (finite_numeral_term_admissible index)
  have hFunctionToken : Term.Admissible functionToken SetSort.set :=
    numeral_name_code_term_admissible (numₘ(token)) (finite_numeral_term_admissible token)
  have hIndexCode : Term.Admissible indexCode SetSort.set := (Numbered.quote_term_with?_code_boundary
      free_name [] (quote_finite_numeral_code_with? free_name [] index)).1
  have hTokenCode : Term.Admissible tokenCode SetSort.set := (Numbered.quote_term_with?_code_boundary
      free_name [] (quote_finite_numeral_code_with? free_name [] token)).1
  have hIndexValue :
      ⊢ₘ[code_naming_theory] functionIndex ≐ₘ indexCode := by
    simpa [functionIndex, indexCode] using
      numeral_name_code_value_derives index
  have hTokenValue :
      ⊢ₘ[code_naming_theory] functionToken ≐ₘ tokenCode := by
    simpa [functionToken, tokenCode] using
      numeral_name_code_value_derives token
  have hStepCongruence :
      ⊢ₘ[code_naming_theory]
        canonical_name_sequence_step_code
            functionIndex functionToken next ≐ₘ
          canonical_name_sequence_step_code
            indexCode tokenCode next :=
    canonical_name_sequence_step_code_congr_of_equalities
      functionIndex indexCode functionToken tokenCode next
      hFunctionIndex hIndexCode hFunctionToken hTokenCode hNext
      hIndexValue hTokenValue
  have hStepBack :
      ⊢ₘ[code_naming_theory]
        canonical_name_sequence_step_code
            indexCode tokenCode next ≐ₘ
          canonical_name_sequence_step_code
            functionIndex functionToken next :=
    Metatheory.Derives.equality_symm hStepCongruence
  have hStep :
      ⊢ₘ[code_naming_theory]
        current ≐ₘ canonical_name_sequence_step_code
          functionIndex functionToken next :=
    Metatheory.Derives.equality_trans hExplicit hStepBack
  exact FirstOrder.Derives.conjIntro hSourceGraph <|
    FirstOrder.Derives.conjIntro (FirstOrder.Derives.conjIntro hTraceCurrent hTraceNext) (by simpa [functionIndex, functionToken] using hStep)
/-- 具体 numeral 位置的单步递归条件可封装成三重对象见证。 -/
private theorem canonical_name_code_recurrence_at_numeral_derives (tokens : List Nat) (index token : Nat) (hGet : tokens[index]? = some token) :
    ⊢ₘ[code_naming_theory]
      canonical_name_code_recurrence (standard_token_sequence tokens) (standard_sequence (canonical_name_suffix_codes_from 0 tokens)) (numₘ(index)) := by
  let current := canonical_name_code_value_from index (tokens.drop index)
  let next :=
    canonical_name_code_value_from (index + 1) (tokens.drop (index + 1))
  have hCurrent : Term.Admissible current SetSort.set := (canonical_name_code_value_from_boundary index (tokens.drop index)).1
  have hNext : Term.Admissible next SetSort.set := (canonical_name_code_value_from_boundary (index + 1) (tokens.drop (index + 1))).1
  have hSourceOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (standard_token_sequence tokens) =
        standard_token_sequence tokens :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (standard_token_sequence tokens) (standard_token_sequence_admissible tokens).2
  have hTraceOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement (standard_sequence (canonical_name_suffix_codes_from 0 tokens)) =
        standard_sequence (canonical_name_suffix_codes_from 0 tokens) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (standard_sequence (canonical_name_suffix_codes_from 0 tokens)) (seq_admissible_m 0
        (canonical_name_suffix_codes_from_admissible 0 tokens)).2
  have hCurrentOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement current = current :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement current hCurrent.2
  have hNextOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement next = next :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement next hNext.2
  have hNumeralOpen (depth : Nat) (replacement : SetTerm) (value : Nat) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  nd_apply FirstOrder.Derives.exists_intro (term := numₘ(token))
  nd_apply FirstOrder.Derives.exists_intro (term := current)
  nd_apply FirstOrder.Derives.exists_intro (term := next)
  simpa [canonical_name_code_recurrence,
    current, next, Formula.openAt, Term.openAt,
    Formula.next_depth, set_bound_variable,
    canonical_name_sequence_step_code_openAt,
    canonical_name_sequence_step_condition,
    hSourceOpen, hTraceOpen, hCurrentOpen, hNextOpen,
    hNumeralOpen] using (canonical_name_sequence_step_value_derives
      tokens index token hGet)
/-- 位置项等于具体 numeral 时，可把具体递归见证运输到该位置项。 -/
private theorem canonical_name_code_recurrence_of_index_equality (tokens : List Nat) (index token : Nat) (point : SetTerm)
    (hPoint : Term.Admissible point SetSort.set) (hGet : tokens[index]? = some token) :
    ⊢ₘ[code_naming_theory] (point ≐ₘ numₘ(index)) ⟶ₘ
        canonical_name_code_recurrence (standard_token_sequence tokens) (standard_sequence (canonical_name_suffix_codes_from 0 tokens))
          point := by
  let source := standard_token_sequence tokens
  let trace := standard_sequence (canonical_name_suffix_codes_from 0 tokens)
  let numeral := numₘ(index)
  let equality : SetFormula := point ≐ₘ numeral
  let Γ : Context signature := [equality]
  let parameter : FreeVarId := 340
  let body : SetFormula :=
    canonical_name_code_recurrence source trace (x#parameter)
  have hSource : Term.Admissible source SetSort.set := by
    simpa [source] using
      standard_token_sequence_admissible tokens
  have hTrace : Term.Admissible trace SetSort.set := by
    simpa [trace] using
      seq_admissible_m 0 (canonical_name_suffix_codes_from_admissible 0 tokens)
  nd_apply FirstOrder.Derives.impIntro
  have hEquality : Γ ⊢ₘ[code_naming_theory] point ≐ₘ numeral := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption (T := code_naming_theory)
        (Γ := Γ) (φ := equality) (by simp [Γ]))
  have hSourceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement source = source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement source (by
        rw [show Term.freeSupport source = [] by
          simp [source]]
        simp)
  have hTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement trace = trace :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set parameter replacement trace (by
        rw [show Term.freeSupport trace = [] by
          simpa [trace] using (seq_support_nil_m 0 (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens))]
        simp)
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality (T := code_naming_theory) (Γ := Γ) (sort := SetSort.set) (eigen := parameter)
      (left := point) (right := numeral) (body := body)
      hEquality
  have hTransport :
      Γ ⊢ₘ[code_naming_theory]
        canonical_name_code_recurrence source trace point ↔ₘ
          canonical_name_code_recurrence source trace numeral := by
    simpa [body, canonical_name_code_recurrence_substituteFree,
      hSourceFixed, hTraceFixed, Formula.substituteFree,
      Term.substituteFree, set_variable] using hIff
  have hNumeralRecurrence :
      Γ ⊢ₘ[code_naming_theory]
        canonical_name_code_recurrence source trace numeral :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by
        simpa [source, trace, numeral] using (canonical_name_code_recurrence_at_numeral_derives
            tokens index token hGet))
  simpa [Γ, equality, source, trace, numeral] using
    FirstOrder.Derives.iffElimLeft hTransport hNumeralRecurrence
/--
有限 numeral 成员条件蕴含相应位置的规范名称递归见证。
归纳只做有限析取的命题拆分；每个叶子仍由上一条具体 quotation 计算定理给出。
-/
private theorem canonical_name_code_recurrence_of_numeral_condition (tokens : List Nat) (count : Nat) (point : SetTerm)
    (hPoint : Term.Admissible point SetSort.set) (hCount : count ≤ tokens.length) :
    ⊢ₘ[code_naming_theory]
      stdseq_numeral_member_condition count point ⟶ₘ
        canonical_name_code_recurrence (standard_token_sequence tokens) (standard_sequence (canonical_name_suffix_codes_from 0 tokens))
          point := by
  let conclusion : SetFormula :=
    canonical_name_code_recurrence (standard_token_sequence tokens) (standard_sequence (canonical_name_suffix_codes_from 0 tokens))
      point
  nd_apply stdseq_numeral_member_condition_elim_of_theory
    count point conclusion
  intro index hIndex
  have hIndexSource : index < tokens.length :=
    Nat.lt_of_lt_of_le hIndex hCount
  let token := tokens[index]
  have hGet : tokens[index]? = some token :=
    List.getElem?_eq_getElem hIndexSource
  simpa [conclusion] using
    canonical_name_code_recurrence_of_index_equality
      tokens index token point hPoint hGet
/-- 源序列定义域中的每个对象位置都满足规范名称递归条款。 -/
private theorem canonical_name_code_recurrence_all_derives (tokens : List Nat) :
    ⊢ₘ[code_naming_theory]
      ∀ₘ[SetSort.set, 340], ((x#340 ∈ₘ domₘ(standard_token_sequence tokens)) ⟶ₘ
          canonical_name_code_recurrence (standard_token_sequence tokens) (standard_sequence (canonical_name_suffix_codes_from 0 tokens)) (x#340)) := by
  let source := standard_token_sequence tokens
  let trace := standard_sequence (canonical_name_suffix_codes_from 0 tokens)
  let point : SetTerm := x#340
  let domainMembership : SetFormula := point ∈ₘ domₘ(source)
  let Γ : Context signature := [domainMembership]
  have hPoint : Term.Admissible point SetSort.set :=
    set_variable_admissible 340
  have hSource : Term.Admissible source SetSort.set :=
    standard_token_sequence_admissible tokens
  have hTrace : Term.Admissible trace SetSort.set :=
    seq_admissible_m 0 (canonical_name_suffix_codes_from_admissible 0 tokens)
  have hDomain : Term.Admissible (domₘ(source)) SetSort.set :=
    domain_term_admissible source hSource
  have hNumeral : Term.Admissible (numₘ(tokens.length)) SetSort.set :=
    finite_numeral_term_admissible tokens.length
  have hSourceDomain :
      ⊢ₘ[code_naming_theory]
        domₘ(source) ≐ₘ numₘ(tokens.length) :=
    code_naming_weaken_standard_sequence (standard_token_sequence_domain_eq_length tokens)
  have hDomainIff :=
    membership_right_iff_of_equality
      point (domₘ(source)) (numₘ(tokens.length))
      hPoint hDomain hNumeral hSourceDomain
  have hNumeralIff :=
    code_naming_weaken_standard_sequence (stdseq_numeral_member_iff tokens.length point hPoint)
  have hCases :=
    canonical_name_code_recurrence_of_numeral_condition
      tokens tokens.length point hPoint (Nat.le_refl _)
  have hPointDerives :
      ⊢ₘ[code_naming_theory]
        domainMembership ⟶ₘ
          canonical_name_code_recurrence source trace point := by
    nd_apply FirstOrder.Derives.impIntro
    have hDomainMembership :
        Γ ⊢ₘ[code_naming_theory] domainMembership :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hNumeralMembership :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) hDomainIff)
        hDomainMembership
    have hCondition :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) hNumeralIff)
        hNumeralMembership
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp) (by simpa [source, trace, point] using hCases))
      hCondition
  derive_close (340) using (by simpa [source, trace, point, domainMembership] using hPointDerives)
/-- 显式 quotation 值满足规范名称函数定义右侧的完整对象规格。 -/
theorem canonical_name_code_spec_derives (tokens : List Nat) :
    ⊢ₘ[code_naming_theory]
      canonical_name_code_spec (standard_token_sequence tokens) (canonical_name_code_value tokens) := by
  let source := standard_token_sequence tokens
  let trace := standard_sequence (canonical_name_suffix_codes_from 0 tokens)
  let candidate := canonical_name_code_value tokens
  have hSourceCode :
      ⊢ₘ[code_naming_theory] source ∈ₘ CodeStrₘ :=
    code_naming_weaken_standard_sequence (standard_token_sequence_mem_code_string tokens)
  have hTrace : Term.Admissible trace SetSort.set :=
    seq_admissible_m 0 (canonical_name_suffix_codes_from_admissible 0 tokens)
  have hSource : Term.Admissible source SetSort.set :=
    standard_token_sequence_admissible tokens
  have hCandidate : Term.Admissible candidate SetSort.set := (canonical_name_code_value_boundary tokens).1
  have hZero : Term.Admissible canonical_name_zero_code SetSort.set :=
    constant_code_term_admissible _ (finite_numeral_term_admissible _)
  have hSourceOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement source hSource.2
  have hCandidateOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement candidate hCandidate.2
  have hZeroOpen (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement
          canonical_name_zero_code =
        canonical_name_zero_code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement canonical_name_zero_code hZero.2
  have hNumeralOpen (depth : Nat) (replacement : SetTerm) (value : Nat) :
      Term.openAt SetSort.set depth replacement (numₘ(value)) =
        numₘ(value) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement (numₘ(value)) (finite_numeral_term_admissible value).2
  have hSourceClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 340 depth source = source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 340 depth source hSource.2 (by
        rw [show Term.freeSupport source = [] by
          simp [source]]
        simp)
  have hTraceClose (depth : Nat) :
      Term.closeFreeAt SetSort.set 340 depth trace = trace :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 340 depth trace hTrace.2 (by
        rw [show Term.freeSupport trace = [] by
          simpa [trace] using (seq_support_nil_m 0 (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens))]
        simp)
  have hFinite :
      ⊢ₘ[code_naming_theory] finite_sequence_condition trace :=
    code_naming_weaken_standard_sequence (standard_sequence_finite_sequence_condition (canonical_name_suffix_codes_from_admissible 0 tokens)
        (stdseq_element_fresh_of_support_nil
          (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens) 0)
        (stdseq_element_fresh_of_support_nil
          (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens) 1)
        (stdseq_element_fresh_of_support_nil
          (canonical_name_suffix_codes_from_freeSupport_nil 0 tokens) 2))
  have hDomain :
      ⊢ₘ[code_naming_theory]
        domₘ(trace) ≐ₘ Sₘ(domₘ(source)) := by
    simpa [source, trace] using
      canonical_name_trace_domain_derives tokens
  have hTerminal :
      ⊢ₘ[code_naming_theory]
        ⟨domₘ(source), canonical_name_zero_code⟩ₘ ∈ₘ trace := by
    simpa [source, trace] using
      canonical_name_trace_terminal_derives tokens
  have hInitial :
      ⊢ₘ[code_naming_theory]
        ⟨numₘ(0), candidate⟩ₘ ∈ₘ trace := by
    simpa [candidate, trace] using
      canonical_name_trace_initial_derives tokens
  have hAll :=
    canonical_name_code_recurrence_all_derives tokens
  have hPacked :
      ⊢ₘ[code_naming_theory]
        finite_sequence_condition trace ∧ₘ ((domₘ(trace) ≐ₘ Sₘ(domₘ(source))) ∧ₘ ((⟨domₘ(source), canonical_name_zero_code⟩ₘ ∈ₘ trace) ∧ₘ
              ((⟨numₘ(0), candidate⟩ₘ ∈ₘ trace) ∧ₘ (∀ₘ[SetSort.set, 340], ((x#340 ∈ₘ domₘ(source)) ⟶ₘ
                    canonical_name_code_recurrence
                      source trace (x#340)))))) :=
    FirstOrder.Derives.conjIntro hFinite <|
      FirstOrder.Derives.conjIntro hDomain <|
        FirstOrder.Derives.conjIntro hTerminal <|
          FirstOrder.Derives.conjIntro hInitial <| (by simpa [source, trace] using hAll)
  apply FirstOrder.Derives.conjIntro
  · simpa [source] using hSourceCode
  · nd_apply FirstOrder.Derives.exists_intro (term := trace)
    simpa [canonical_name_code_spec,
      source, trace, candidate,
      Formula.openAt, Term.openAt, Formula.next_depth,
      Formula.closeFreeAt, Term.closeFreeAt,
      finite_sequence_condition, is_function_formula,
      set_variable, set_bound_variable,
      canonical_name_code_recurrence,
      canonical_name_sequence_step_condition,
      canonical_name_sequence_step_code_openAt,
      canonical_name_sequence_step_code_closeFreeAt,
      hSourceOpen, hCandidateOpen, hZeroOpen,
      hNumeralOpen, hSourceClose, hTraceClose] using hPacked
/-- 规范名称对象函数在每条标准 token 序列上计算为显式 quotation 值。 -/
theorem canonical_name_code_value_derives (tokens : List Nat) :
    ⊢ₘ[code_naming_theory]
      canonical_name_code_value tokens ≐ₘ
        name_codeₘ(standard_token_sequence tokens) := by
  have hDefinition :=
    canonical_name_code_definition_instance_derives (standard_token_sequence tokens) (canonical_name_code_value tokens)
      (standard_token_sequence_admissible tokens) (canonical_name_code_value_boundary tokens).1
  exact FirstOrder.Derives.iffElimLeft hDefinition (canonical_name_code_spec_derives tokens)
/-! ## 公式 quotation 的规范名称数据 -/
/--
把一个 FormalSystem 公式的 token quotation、对象 quotation 与其规范名称 quotation
装入同一个 proof-carrying 数据。`name_term` 由 `tokens` 唯一导出，因而结构中不再
保存一个可能与它不一致的冗余项。
-/
structure CanonicalFormulaNameData (formula : SetFormula) where
  tokens : List Nat
  formula_code : SetTerm
  name_code : SetTerm
  h_formula_admissible : Formula.Admissible formula
  h_formula_tokens : Numbered.quote_tokens? formula = some tokens
  h_formula_code : Numbered.quote? formula = some formula_code
  h_name_code : canonical_name_code? tokens = some name_code
namespace CanonicalFormulaNameData
/-- 公式代码值的规范闭项名称。 -/
def name_term {formula : SetFormula} (data : CanonicalFormulaNameData formula) : SetTerm :=
  canonical_name_term data.tokens
@[simp]
theorem name_term_admissible {formula : SetFormula} (data : CanonicalFormulaNameData formula) :
    Term.Admissible data.name_term SetSort.set :=
  canonical_name_term_admissible data.tokens
@[simp]
theorem name_term_freeSupport_nil {formula : SetFormula} (data : CanonicalFormulaNameData formula) :
    Term.freeSupport data.name_term = [] :=
  canonical_name_term_freeSupport_nil data.tokens
/-- 公式对象 quotation 自动满足 closed、sort 正确的代码边界。 -/
theorem formula_code_boundary {formula : SetFormula} (data : CanonicalFormulaNameData formula) :
    Numbered.CodeBoundary data.formula_code :=
  Numbered.quote?_code_boundary data.h_formula_code
/-- 规范名称自身的对象 quotation 自动满足代码边界。 -/
theorem name_code_boundary {formula : SetFormula} (data : CanonicalFormulaNameData formula) :
    Numbered.CodeBoundary data.name_code :=
  canonical_name_code?_boundary data.h_name_code
/-- 结构中保存的名称 quotation 正是公开的显式递归值。 -/
theorem name_code_eq_value {formula : SetFormula} (data : CanonicalFormulaNameData formula) :
    data.name_code = canonical_name_code_value data.tokens := by
  have hCode := data.h_name_code
  rw [canonical_name_code?_eq_value data.tokens] at hCode
  exact (Option.some.inj hCode).symm
/-- 规范名称项自身的 token quotation 由显式递归函数精确给出。 -/
theorem name_term_tokens {formula : SetFormula} (data : CanonicalFormulaNameData formula) :
    quote_term_tokens? data.name_term =
      some (canonical_name_tokens data.tokens) := by
  simp [quote_term_tokens?, name_term]
/--
把代码变量替换成规范名称后，结果公式的 token quotation 直接化为逐位置替换。
这是对象层 `NameCode` 与 `subst_codeₘ` 最终需要实现的精确元层计算方程。
-/
theorem named_instance_tokens
    {formula : SetFormula} (data : CanonicalFormulaNameData formula) (id : FreeVarId) :
    Numbered.quote_tokens? (Formula.substituteFree SetSort.set id data.name_term formula) =
      some (substitute_tokens data.tokens (variable_token (free_name id)) (canonical_name_tokens data.tokens)) := by
  exact quote_tokens?_substituteFree_some
    data.name_term_admissible.2 data.h_formula_tokens data.name_term_tokens
/-- 规范名称实例仍然 admissible。 -/
theorem named_instance_admissible
    {formula : SetFormula} (data : CanonicalFormulaNameData formula) (id : FreeVarId) :
    Formula.Admissible (Formula.substituteFree SetSort.set id data.name_term formula) :=
  Formula.Admissible.substituteFree SetSort.set id
    data.h_formula_admissible data.name_term_admissible
/-- 规范名称实例的对象 quotation 总能成功。 -/
theorem named_instance_code_exists
    {formula : SetFormula} (data : CanonicalFormulaNameData formula) (id : FreeVarId) :
    ∃ code,
      Numbered.quote? (Formula.substituteFree SetSort.set id data.name_term formula) =
        some code :=
  Numbered.quote?_exists (data.named_instance_admissible id)
end CanonicalFormulaNameData
/-- 每个 admissible FormalSystem 公式都具有完整的规范名称数据。 -/
theorem canonical_formula_name_data_exists
    {formula : SetFormula} (hFormula : Formula.Admissible formula) :
    Nonempty (CanonicalFormulaNameData formula) := by
  rcases Numbered.quote_tokens?_exists hFormula with
    ⟨tokens, hTokens⟩
  rcases Numbered.quote?_exists hFormula with
    ⟨formulaCode, hFormulaCode⟩
  rcases canonical_name_code?_exists tokens with
    ⟨nameCode, hNameCode⟩
  exact ⟨{
    tokens := tokens
    formula_code := formulaCode
    name_code := nameCode
    h_formula_admissible := hFormula
    h_formula_tokens := hTokens
    h_formula_code := hFormulaCode
    h_name_code := hNameCode
  }⟩
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
