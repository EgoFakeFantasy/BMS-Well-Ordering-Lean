import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardSequence
import YesMetaZFC.Logic.FirstOrder.Hilbert.Translation
/-!
# 可编号单排序签名上的通用 Gödel quotation
对象编码要求函数符号和关系符号可注入地编号，并要求签名只有一个对象 sort。
零元函数按常元编码，正元函数按“函数符号—括号—参数列”编码；普通关系使用正元
谓词符号编码。一个签名也可以把其二元原生隶属关系标为专用 `2^7` 编码。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
universe u v w u₁ u₂
/-- 关系符号进入对象公式编码时采用的两种形式。 -/
inductive QuotationRelationKind where
  | membership
  | predicate
  deriving DecidableEq, Repr
/--
可编号单排序签名的 quotation 数据。
注入性保证不同元语言符号不会共享编号；`relation_nonempty` 对应当前对象编码中
普通谓词符号只覆盖正元数谓词的事实。
-/
class QuotationNumbering (σ : Signature.{u, v, w}) where
  objectSort : σ.SortSymbol
  sort_eq_object : ∀ sort, sort = objectSort
  function_number : σ.FuncSymbol → Nat
  relation_number : σ.RelSymbol → Nat
  function_number_injective : Function.Injective function_number
  relation_number_injective : Function.Injective relation_number
  relation_kind : σ.RelSymbol → QuotationRelationKind :=
    fun _ => .predicate
  relation_nonempty : ∀ relation, σ.relDomain relation ≠ []
  membership_domain : ∀ relation,
    relation_kind relation = .membership →
      σ.relDomain relation = [objectSort, objectSort]
  membership_unique : ∀ {left right},
    relation_kind left = .membership →
      relation_kind right = .membership →
        left = right
/-! ## 规范变量编号 -/
/-- 外部自由变量的规范内部编号；偶数域留给自由变量。 -/
def free_name (id : FreeVarId) : Nat :=
  2 * id
/-- 规范 quotation 的 binder 编号；奇数域留给 bound 变量。 -/
def bound_name (depth : Nat) : Nat :=
  2 * depth + 1
theorem free_name_injective : Function.Injective free_name := by
  intro left right hEqual
  unfold free_name at hEqual
  exact Nat.mul_left_cancel (by decide) hEqual
theorem bound_name_injective : Function.Injective bound_name := by
  intro left right hEqual
  unfold bound_name at hEqual
  apply Nat.mul_left_cancel (n := 2) (by decide)
  exact Nat.add_right_cancel hEqual
theorem free_name_ne_bound_name (id depth : Nat) :
    free_name id ≠ bound_name depth := by
  intro hEqual
  have hParity := congrArg (fun value => value % 2) hEqual
  simp [free_name, bound_name] at hParity
/-- 规范 quotation 在深度 `depth` 处实际携带的 binder 环境。 -/
def canonical_bound_names : Nat → List Nat
  | 0 => []
  | depth + 1 => bound_name depth :: canonical_bound_names depth
@[simp]
theorem canonical_bound_names_length (depth : Nat) : (canonical_bound_names depth).length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [canonical_bound_names, ih]
/-- 规范环境中的名字都来自严格更浅的 binder 深度。 -/
theorem mem_canonical_bound_names
    {name depth : Nat} (hName : name ∈ canonical_bound_names depth) :
    ∃ prior, prior < depth ∧ name = bound_name prior := by
  induction depth with
  | zero =>
      simp [canonical_bound_names] at hName
  | succ depth ih =>
      rcases List.mem_cons.mp hName with hCurrent | hPrior
      · exact ⟨depth, Nat.lt_succ_self depth, hCurrent⟩
      · rcases ih hPrior with ⟨prior, hPriorDepth, rfl⟩
        exact ⟨prior, Nat.lt_succ_of_lt hPriorDepth, rfl⟩
/-- 新 binder 的规范名字不与任何外层 binder 重名。 -/
theorem bound_name_not_mem_canonical (depth : Nat) :
    bound_name depth ∉ canonical_bound_names depth := by
  intro hMember
  rcases mem_canonical_bound_names hMember with
    ⟨prior, hPrior, hEqual⟩
  have := bound_name_injective hEqual
  omega
/-- 任意规范自由变量名都不出现在规范 binder 环境中。 -/
theorem free_name_not_mem_canonical (id depth : Nat) :
    free_name id ∉ canonical_bound_names depth := by
  intro hMember
  rcases mem_canonical_bound_names hMember with
    ⟨prior, hPrior, hEqual⟩
  exact free_name_ne_bound_name id prior hEqual
/-- 规范 binder 环境没有重复名字。 -/
theorem canonical_bound_names_nodup (depth : Nat) : (canonical_bound_names depth).Nodup := by
  induction depth with
  | zero =>
      exact .nil
  | succ depth ih =>
      exact List.nodup_cons.mpr
        ⟨bound_name_not_mem_canonical depth, ih⟩
namespace QuotationNumbering
/-- 单排序签名中的任意 sort 都等于规范对象 sort。 -/
theorem sort_eq {σ : Signature.{u, v, w}} [numbering : QuotationNumbering σ] (sort : σ.SortSymbol) : sort = numbering.objectSort :=
  numbering.sort_eq_object sort
/-- 规范对象 sort 也等于任意给定 sort。 -/
theorem object_eq_sort {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] (sort : σ.SortSymbol) :
    numbering.objectSort = sort := (numbering.sort_eq_object sort).symm
end QuotationNumbering
namespace Numbered
/-- 把一个内部变量编号实现为对象语言中的变量符号编码项。 -/
abbrev named_variable_code (name : Nat) : SetTerm :=
  var_codeₘ(numₘ(name))
/-! ## 标准自然数 token -/
/-- 一个逻辑符号的自然数标签。 -/
def logical_token (symbol : LogicalSymbolKind) : Nat :=
  2 ^ logical_symbol_exponent symbol
/-- 文献专用隶属符号的自然数标签。 -/
def membership_token : Nat :=
  2 ^ 7
/-- 第 `name` 个变量符号的自然数标签。 -/
def variable_token (name : Nat) : Nat :=
  3 ^ (name + 1)
/-- 变量名字严格落在其 token 后继给出的有限搜索区间内。 -/
theorem variable_name_lt_token_succ
    (name : Nat) :
    name < variable_token name + 1 := by
  have hPower :
      name < 3 ^ (name + 1) := by
    induction name with
    | zero =>
        decide
    | succ name ih =>
        rw [show name + 1 + 1 = (name + 1) + 1 by omega,
          Nat.pow_succ]
        have hPositive : 0 < 3 ^ (name + 1) :=
          Nat.pow_pos (by decide)
        omega
  simpa [variable_token] using
    Nat.lt_succ_of_lt hPower
/-- 第 `index` 个常元符号的自然数标签。 -/
def constant_token (index : Nat) : Nat :=
  5 ^ (index + 1)
/-- 第 `index` 个给定正元数函数符号的自然数标签。 -/
def function_token (arityPredecessor index : Nat) : Nat :=
  3 ^ (arityPredecessor + 1) * 5 ^ (index + 1)
/-- 第 `index` 个给定正元数谓词符号的自然数标签。 -/
def predicate_token (arityPredecessor index : Nat) : Nat :=
  3 ^ (arityPredecessor + 1) * 7 ^ (index + 1)
/-- 等式原子的标准符号串。 -/
def equality_tokens (left right : List Nat) : List Nat :=
  [logical_token .leftParenthesis] ++ left ++
    [logical_token .equality] ++ right ++
      [logical_token .rightParenthesis]
/-- 隶属原子的标准符号串。 -/
def membership_tokens (left right : List Nat) : List Nat :=
  [logical_token .leftParenthesis] ++ left ++
    [membership_token] ++ right ++
      [logical_token .rightParenthesis]
/-- 正元数函数应用的标准符号串。 -/
def function_application_tokens (arityPredecessor index : Nat) (arguments : List (List Nat)) : List Nat :=
  [function_token arityPredecessor index,
      logical_token .leftParenthesis] ++
    arguments.flatten ++ [logical_token .rightParenthesis]
/-- 普通谓词应用的标准符号串。 -/
def predicate_application_tokens (arityPredecessor index : Nat) (arguments : List (List Nat)) : List Nat :=
  [predicate_token arityPredecessor index,
      logical_token .leftParenthesis] ++
    arguments.flatten ++ [logical_token .rightParenthesis]
/-- 否定公式的标准符号串。 -/
def negation_tokens (body : List Nat) : List Nat :=
  [logical_token .leftParenthesis, logical_token .negation] ++
    body ++ [logical_token .rightParenthesis]
/-- 蕴含公式的标准符号串。 -/
def implication_tokens (left right : List Nat) : List Nat :=
  [logical_token .leftParenthesis] ++ left ++
    [logical_token .implication] ++ right ++
      [logical_token .rightParenthesis]
/-- 全称公式的标准符号串。 -/
def universal_tokens (name : Nat) (body : List Nat) : List Nat :=
  [logical_token .leftParenthesis, logical_token .universal,
    variable_token name] ++ body ++
      [logical_token .rightParenthesis]
/--
存在量词的标准符号串按文献 11.5 展开为 `¬∀¬`。
虽然词法枚举保留了 `existential` 标签以描述原始符号表，Hilbert quotation 不把它作为
公式构造子使用；这里固定采用与 `Formula.hilbertize` 相同的核心展开。
-/
def existential_tokens (name : Nat) (body : List Nat) : List Nat :=
  negation_tokens (universal_tokens name (negation_tokens body))
/--
合取的标准符号串按文献 11.6 展开为 `¬(φ → ¬ψ)`。
这保证派生联结词不会绕开 `¬ / → / ∀` 的公共对象编码闭包。
-/
def conjunction_tokens (left right : List Nat) : List Nat :=
  negation_tokens (implication_tokens left (negation_tokens right))
/-- 显式具名环境下的通用项 token quotation。 -/
@[simp]
def quote_term_tokens_with? {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
    Term σ → Option (List Nat)
  | .var (.bvar _ index) =>
      (boundNames[index]?).map (fun name => [variable_token name])
  | .var (.fvar _ id) =>
      some [variable_token (freeNaming id)]
  | .app function arguments => do
      let codes ← arguments.mapM (quote_term_tokens_with? freeNaming boundNames)
      match codes with
      | [] =>
          pure [constant_token (QuotationNumbering.function_number function)]
      | _ :: _ =>
          pure (function_application_tokens (arguments.length - 1) (QuotationNumbering.function_number function) codes)
termination_by term => term
/-- 显式具名环境下的通用关系原子 token quotation。 -/
@[simp]
def quote_relation_tokens_with? {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (relation : σ.RelSymbol) (arguments : List (Term σ)) :
    Option (List Nat) :=
  match QuotationNumbering.relation_kind relation, arguments with
  | .membership, [left, right] => do
      let leftCode ← quote_term_tokens_with? freeNaming boundNames left
      let rightCode ← quote_term_tokens_with? freeNaming boundNames right
      pure (membership_tokens leftCode rightCode)
  | .predicate, head :: tail => do
      let codes ← (head :: tail).mapM (quote_term_tokens_with? freeNaming boundNames)
      pure (predicate_application_tokens ((head :: tail).length - 1) (QuotationNumbering.relation_number relation) codes)
  | _, _ => none
/-- 显式具名环境下的通用 Hilbert 核 token quotation。 -/
@[simp]
def quote_hilbert_tokens_with? {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) :
    Formula σ → Option (List Nat)
  | .rel relation arguments =>
      quote_relation_tokens_with? freeNaming boundNames relation arguments
  | .equal left right => do
      let leftCode ← quote_term_tokens_with? freeNaming boundNames left
      let rightCode ← quote_term_tokens_with? freeNaming boundNames right
      pure (equality_tokens leftCode rightCode)
  | .neg body => do
      let bodyCode ← quote_hilbert_tokens_with?
        freeNaming binderNaming boundNames depth body
      pure (negation_tokens bodyCode)
  | .imp left right => do
      let leftCode ← quote_hilbert_tokens_with?
        freeNaming binderNaming boundNames depth left
      let rightCode ← quote_hilbert_tokens_with?
        freeNaming binderNaming boundNames depth right
      pure (implication_tokens leftCode rightCode)
  | .forallE _ body => do
      let name := binderNaming depth
      let bodyCode ← quote_hilbert_tokens_with?
        freeNaming binderNaming (name :: boundNames) (depth + 1) body
      pure (universal_tokens name bodyCode)
  | _ => none
/-- 公共公式在显式变量命名下的通用 token quotation。 -/
def quote_tokens_with? {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) (formula : Formula σ) :
    Option (List Nat) :=
  quote_hilbert_tokens_with? freeNaming binderNaming [] 0 (Formula.hilbertize numbering.objectSort formula)
/-- 公共公式在偶/奇变量命名下的规范 token quotation。 -/
def quote_tokens? {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (formula : Formula σ) : Option (List Nat) :=
  quote_tokens_with? free_name bound_name formula
/-- 把参数编码列表实现为对象语言中的标准有限序列。 -/
abbrev argument_sequence (codes : List SetTerm) : SetTerm :=
  standard_sequence codes
/--
在显式 bound 环境下引用任意可编号单排序签名的项。
原始语法允许暂时不匹配 arity；quotation 仍保持可计算，而编码闭包定理在
`Term.Admissible` 边界上消费签名 arity。
-/
@[simp]
def quote_term_with? {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
    Term σ → Option SetTerm
  | .var (.bvar _ index) =>
      (boundNames[index]?).map named_variable_code
  | .var (.fvar _ id) =>
      some (named_variable_code (freeNaming id))
  | .app function arguments => do
      let codes ← arguments.mapM (quote_term_with? freeNaming boundNames)
      match codes with
      | [] =>
          pure (const_codeₘ(numₘ(QuotationNumbering.function_number function)))
      | _ :: _ =>
          pure (term_application_code_term (numₘ(arguments.length - 1)) (numₘ(QuotationNumbering.function_number function)) (argument_sequence codes))
termination_by term => term
/-- 引用一列同签名项。 -/
@[simp]
def quote_terms_with? {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    (terms : List (Term σ)) : Option (List SetTerm) :=
  terms.mapM (quote_term_with? freeNaming boundNames)
/-- 引用一个关系原子；专用隶属符号与普通谓词符号在此处分流。 -/
@[simp]
def quote_relation_with? {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    (relation : σ.RelSymbol) (arguments : List (Term σ)) : Option SetTerm :=
  match QuotationNumbering.relation_kind relation, arguments with
  | .membership, [left, right] => do
      let leftCode ← quote_term_with? freeNaming boundNames left
      let rightCode ← quote_term_with? freeNaming boundNames right
      pure (membership_atomic_formula_code_term leftCode rightCode)
  | .predicate, head :: tail => do
      let codes ← quote_terms_with?
        freeNaming boundNames (head :: tail)
      pure (predicate_application_code_term (numₘ((head :: tail).length - 1)) (numₘ(QuotationNumbering.relation_number relation)) (argument_sequence codes))
  | _, _ => none
/-- 可计算 quotation 使用给定的 binder 名称流。 -/
@[simp]
def quote_hilbert_with? {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) :
    Formula σ → Option SetTerm
  | .rel relation arguments =>
      quote_relation_with? freeNaming boundNames relation arguments
  | .equal left right => do
      let leftCode ← quote_term_with? freeNaming boundNames left
      let rightCode ← quote_term_with? freeNaming boundNames right
      pure (eq_codeₘ(leftCode, rightCode))
  | .neg body => do
      let bodyCode ← quote_hilbert_with?
        freeNaming binderNaming boundNames depth body
      pure (neg_codeₘ(bodyCode))
  | .imp left right => do
      let leftCode ← quote_hilbert_with?
        freeNaming binderNaming boundNames depth left
      let rightCode ← quote_hilbert_with?
        freeNaming binderNaming boundNames depth right
      pure (imp_codeₘ(leftCode, rightCode))
  | .forallE _ body => do
      let name := binderNaming depth
      let bodyCode ← quote_hilbert_with?
        freeNaming binderNaming (name :: boundNames) (depth + 1) body
      pure (forall_codeₘ(named_variable_code name, bodyCode))
  | _ => none
/-- 公共公式在显式变量命名下的 Gödel quotation。 -/
def quote_with? {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) (formula : Formula σ) :
    Option SetTerm :=
  quote_hilbert_with? freeNaming binderNaming [] 0 (Formula.hilbertize numbering.objectSort formula)
/-- 公共公式在偶/奇变量命名下的规范 Gödel quotation。 -/
def quote? {σ : Signature.{u, v, w}} [QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (formula : Formula σ) : Option SetTerm :=
  quote_with? free_name bound_name formula
/-! ## quotation 结果的通用对象项边界 -/
/-- quotation 结果同时满足对象项良构性并且不含对象语言自由变量。 -/
def CodeBoundary (code : SetTerm) : Prop :=
  Term.Admissible code SetSort.set ∧ Term.freeSupport code = []
namespace CodeBoundary
/-- quotation 边界假设可直接供自然演绎规则的项检查器消费。 -/
@[term_check]
theorem check_certificate
    {code : SetTerm} (hCode : CodeBoundary code) :
    Term.CheckCertificate code SetSort.set :=
  Term.check_admissible_complete hCode.1
/-- 闭 quotation 代码项不受 bound opening 影响。 -/
theorem openAt_eq
    {code : SetTerm} (hCode : CodeBoundary code) (depth : Nat) (replacement : SetTerm) :
    Term.openAt SetSort.set depth replacement code = code :=
  Term.openAt_eq_self_of_boundClosed
    SetSort.set depth replacement code hCode.1.2
/-- 闭 quotation 代码项不受任意自由变量代入影响。 -/
theorem substituteFree_eq
    {code : SetTerm} (hCode : CodeBoundary code) (freeId : FreeVarId) (replacement : SetTerm) :
    Term.substituteFree SetSort.set freeId replacement code = code :=
  Term.substituteFree_eq_self_of_not_mem
    SetSort.set freeId replacement code (by
      rw [hCode.2]
      simp)
/-- 闭 quotation 代码项不受任意自由变量关闭影响。 -/
theorem closeFreeAt_eq
    {code : SetTerm} (hCode : CodeBoundary code) (freeId : FreeVarId) (depth : Nat) :
    Term.closeFreeAt SetSort.set freeId depth code = code :=
  Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    SetSort.set freeId depth code hCode.1.2 (by
      rw [hCode.2]
      simp)
end CodeBoundary
/-- 任意可编号签名的项 quotation 都产生 closed、sort 正确的对象编码项。 -/
theorem quote_term_with?_code_boundary
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term σ} {code : SetTerm} (hQuote : quote_term_with? freeNaming boundNames term = some code) :
    CodeBoundary code := by
  refine Term.rec (motive_1 := fun term =>
      ∀ code,
        quote_term_with? freeNaming boundNames term = some code →
          CodeBoundary code) (motive_2 := fun terms =>
      ∀ codes,
        terms.mapM (quote_term_with? freeNaming boundNames) = some codes →
          ∀ code, code ∈ codes → CodeBoundary code)
    ?_ ?_ ?_ ?_ term code hQuote
  · intro sourceVar code hSourceQuote
    cases sourceVar with
    | bvar sort index =>
        cases hName : boundNames[index]? with
        | none =>
            simp [quote_term_with?, hName] at hSourceQuote
        | some name =>
            simp [quote_term_with?, hName] at hSourceQuote
            subst code
            exact ⟨
              variable_code_term_admissible (numₘ(name)) (finite_numeral_term_admissible name),
              by
                simp [Term.freeSupport, Term.freeSupportList,
                  finite_numeral_term_freeSupport]⟩
    | fvar sort id =>
        simp [quote_term_with?] at hSourceQuote
        subst code
        exact ⟨
          variable_code_term_admissible (numₘ(freeNaming id)) (finite_numeral_term_admissible (freeNaming id)),
          by
            simp [Term.freeSupport, Term.freeSupportList,
              finite_numeral_term_freeSupport]⟩
  · intro function arguments ih code hSourceQuote
    cases hCodes :
        arguments.mapM (quote_term_with? freeNaming boundNames) with
    | none =>
        simp [quote_term_with?, hCodes] at hSourceQuote
    | some codes =>
        cases codes with
        | nil =>
            simp [quote_term_with?, hCodes] at hSourceQuote
            subst code
            exact ⟨
              constant_code_term_admissible (numₘ(QuotationNumbering.function_number function)) (finite_numeral_term_admissible
                  (QuotationNumbering.function_number function)),
              by
                simp [Term.freeSupport, Term.freeSupportList,
                  finite_numeral_term_freeSupport]⟩
        | cons head tail =>
            simp [quote_term_with?, hCodes] at hSourceQuote
            subst code
            have hElements := ih (head :: tail) hCodes
            have hArgumentsAdmissible :
                Term.Admissible (argument_sequence (head :: tail))
                  SetSort.set :=
              seq_admissible_m 0 <| by
                intro element hElement
                exact (hElements element hElement).1
            have hArgumentsClosed :
                Term.freeSupport (argument_sequence (head :: tail)) = [] :=
              seq_support_nil_m 0 <| by
                intro element hElement
                exact (hElements element hElement).2
            exact ⟨
              term_application_code_term_admissible (numₘ(arguments.length - 1)) (numₘ(QuotationNumbering.function_number function))
                (argument_sequence (head :: tail)) (finite_numeral_term_admissible (arguments.length - 1)) (finite_numeral_term_admissible
                  (QuotationNumbering.function_number function))
                hArgumentsAdmissible,
              by
                simp [Term.freeSupport, Term.freeSupportList,
                  finite_numeral_term_freeSupport, hArgumentsClosed]⟩
  · intro codes hCodes code hMember
    simp at hCodes
    subst codes
    simp at hMember
  · intro head tail ihHead ihTail codes hCodes code hMember
    cases hHead : quote_term_with? freeNaming boundNames head with
    | none =>
        simp [hHead] at hCodes
    | some headCode =>
        cases hTail :
            tail.mapM (quote_term_with? freeNaming boundNames) with
        | none =>
            simp [hHead, hTail] at hCodes
        | some tailCodes =>
            simp [hHead, hTail] at hCodes
            subst codes
            simp only [List.mem_cons] at hMember
            rcases hMember with hMember | hMember
            · subst code
              exact ihHead _ hHead
            · exact ihTail tailCodes hTail code hMember
/-- 一列成功项 quotation 中的每个编码都满足通用对象项边界。 -/
theorem quote_terms_with?_code_boundary
    {σ : Signature.{u, v, w}} [QuotationNumbering σ] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {terms : List (Term σ)} {codes : List SetTerm} (hQuote : quote_terms_with? freeNaming boundNames terms = some codes) :
    ∀ code, code ∈ codes → CodeBoundary code := by
  change
    terms.mapM (quote_term_with? freeNaming boundNames) = some codes
      at hQuote
  induction terms generalizing codes with
  | nil =>
      simp at hQuote
      subst codes
      simp
  | cons head tail ih =>
      cases hHead : quote_term_with? freeNaming boundNames head with
      | none =>
          simp [hHead] at hQuote
      | some headCode =>
          cases hTail :
              tail.mapM (quote_term_with? freeNaming boundNames) with
          | none =>
              simp [hHead, hTail] at hQuote
          | some tailCodes =>
              simp [hHead, hTail] at hQuote
              subst codes
              intro code hMember
              simp only [List.mem_cons] at hMember
              rcases hMember with hMember | hMember
              · subst code
                exact quote_term_with?_code_boundary
                  freeNaming boundNames hHead
              · exact ih hTail code hMember
/-- Hilbert 核 quotation 的成功结果满足通用对象项边界。 -/
theorem quote_hilbert_with?_code_boundary
    {σ : Signature.{u, v, w}} [numbering : QuotationNumbering σ] (freeNaming binderNaming : Nat → Nat)
    {boundNames : List Nat} {depth : Nat}
    {formula : Formula σ} {code : SetTerm} (hQuote : quote_hilbert_with? freeNaming binderNaming
      boundNames depth formula = some code) :
    CodeBoundary code := by
  induction formula generalizing boundNames depth code with
  | falsum =>
      simp [quote_hilbert_with?] at hQuote
  | truth =>
      simp [quote_hilbert_with?] at hQuote
  | rel relation arguments =>
      cases hKind : numbering.relation_kind relation with
      | membership =>
          cases arguments with
          | nil =>
              simp [quote_hilbert_with?, quote_relation_with?, hKind] at hQuote
          | cons left rest =>
              cases rest with
              | nil =>
                  simp [quote_hilbert_with?, quote_relation_with?, hKind] at hQuote
              | cons right tail =>
                  cases tail with
                  | cons extra tail =>
                      simp [quote_hilbert_with?, quote_relation_with?, hKind] at hQuote
                  | nil =>
                      cases hLeft :
                          quote_term_with? freeNaming boundNames left with
                      | none =>
                          simp [quote_hilbert_with?, quote_relation_with?,
                            hKind, hLeft] at hQuote
                      | some leftCode =>
                          cases hRight :
                              quote_term_with? freeNaming boundNames right with
                          | none =>
                              simp [quote_hilbert_with?, quote_relation_with?,
                                hKind, hLeft, hRight] at hQuote
                          | some rightCode =>
                              simp [quote_hilbert_with?, quote_relation_with?,
                                hKind, hLeft, hRight] at hQuote
                              subst code
                              have hLeftBoundary :=
                                quote_term_with?_code_boundary
                                  freeNaming boundNames hLeft
                              have hRightBoundary :=
                                quote_term_with?_code_boundary
                                  freeNaming boundNames hRight
                              exact ⟨
                                binary_atomic_formula_code_term_admissible
                                  membership_symbol_code_term leftCode rightCode
                                  membership_symbol_code_term_admissible
                                  hLeftBoundary.1 hRightBoundary.1,
                                by
                                  simp [Term.freeSupport, Term.freeSupportList,
                                    finite_numeral_term_freeSupport,
                                    hLeftBoundary.2, hRightBoundary.2]⟩
      | predicate =>
          cases arguments with
          | nil =>
              simp [quote_hilbert_with?, quote_relation_with?, hKind] at hQuote
          | cons head tail =>
              cases hCodes : quote_terms_with?
                  freeNaming boundNames (head :: tail) with
              | none =>
                  change (head :: tail).mapM (quote_term_with? freeNaming boundNames) = none
                      at hCodes
                  simp [quote_hilbert_with?, quote_relation_with?,
                    quote_terms_with?, hKind, hCodes] at hQuote
              | some codes =>
                  change (head :: tail).mapM (quote_term_with? freeNaming boundNames) = some codes
                      at hCodes
                  simp [quote_hilbert_with?, quote_relation_with?,
                    quote_terms_with?, hKind, hCodes] at hQuote
                  subst code
                  have hElements := quote_terms_with?_code_boundary
                    freeNaming boundNames hCodes
                  have hArgumentsAdmissible :
                      Term.Admissible (argument_sequence codes) SetSort.set :=
                    seq_admissible_m 0 <| by
                      intro element hElement
                      exact (hElements element hElement).1
                  have hArgumentsClosed :
                      Term.freeSupport (argument_sequence codes) = [] :=
                    seq_support_nil_m 0 <| by
                      intro element hElement
                      exact (hElements element hElement).2
                  exact ⟨
                    predicate_application_code_term_admissible (numₘ((head :: tail).length - 1)) (numₘ(numbering.relation_number relation))
                      (argument_sequence codes) (finite_numeral_term_admissible ((head :: tail).length - 1)) (finite_numeral_term_admissible
                        (numbering.relation_number relation))
                      hArgumentsAdmissible,
                    by
                      simp [Term.freeSupport, Term.freeSupportList,
                        finite_numeral_term_freeSupport,
                        hArgumentsClosed]⟩
  | equal left right =>
      cases hLeft : quote_term_with? freeNaming boundNames left with
      | none =>
          simp [quote_hilbert_with?, hLeft] at hQuote
      | some leftCode =>
          cases hRight : quote_term_with? freeNaming boundNames right with
          | none =>
              simp [quote_hilbert_with?, hLeft, hRight] at hQuote
          | some rightCode =>
              simp [quote_hilbert_with?, hLeft, hRight] at hQuote
              subst code
              have hLeftBoundary := quote_term_with?_code_boundary
                freeNaming boundNames hLeft
              have hRightBoundary := quote_term_with?_code_boundary
                freeNaming boundNames hRight
              exact ⟨
                equality_formula_code_term_admissible
                  leftCode rightCode hLeftBoundary.1 hRightBoundary.1,
                by
                  simp [Term.freeSupport, Term.freeSupportList,
                    hLeftBoundary.2, hRightBoundary.2]⟩
  | neg body ih =>
      cases hBody : quote_hilbert_with? freeNaming binderNaming
          boundNames depth body with
      | none =>
          simp [quote_hilbert_with?, hBody] at hQuote
      | some bodyCode =>
          simp [quote_hilbert_with?, hBody] at hQuote
          subst code
          have hBodyBoundary := ih hBody
          exact ⟨
            negation_formula_code_term_admissible
              bodyCode hBodyBoundary.1,
            by
              simp [Term.freeSupport, Term.freeSupportList,
                hBodyBoundary.2]⟩
  | conj left right =>
      simp [quote_hilbert_with?] at hQuote
  | disj left right =>
      simp [quote_hilbert_with?] at hQuote
  | imp left right ihLeft ihRight =>
      cases hLeft : quote_hilbert_with? freeNaming binderNaming
          boundNames depth left with
      | none =>
          simp [quote_hilbert_with?, hLeft] at hQuote
      | some leftCode =>
          cases hRight : quote_hilbert_with? freeNaming binderNaming
              boundNames depth right with
          | none =>
              simp [quote_hilbert_with?, hLeft, hRight] at hQuote
          | some rightCode =>
              simp [quote_hilbert_with?, hLeft, hRight] at hQuote
              subst code
              have hLeftBoundary := ihLeft hLeft
              have hRightBoundary := ihRight hRight
              exact ⟨
                implication_formula_code_term_admissible
                  leftCode rightCode hLeftBoundary.1 hRightBoundary.1,
                by
                  simp [Term.freeSupport, Term.freeSupportList,
                    hLeftBoundary.2, hRightBoundary.2]⟩
  | iff left right =>
      simp [quote_hilbert_with?] at hQuote
  | forallE sort body ih =>
      let name := binderNaming depth
      cases hBody : quote_hilbert_with? freeNaming binderNaming (name :: boundNames) (depth + 1) body with
      | none =>
          simp [quote_hilbert_with?, name, hBody] at hQuote
      | some bodyCode =>
          simp [quote_hilbert_with?, name, hBody] at hQuote
          subst code
          have hBodyBoundary := ih hBody
          exact ⟨
            universal_formula_code_term_admissible (named_variable_code name) bodyCode (variable_code_term_admissible
                (numₘ(name)) (finite_numeral_term_admissible name))
              hBodyBoundary.1,
            by
              simp [Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport, hBodyBoundary.2]⟩
  | existsE sort body =>
      simp [quote_hilbert_with?] at hQuote
/-- 任意公共公式的成功规范 quotation 自动满足完整对象项边界。 -/
theorem quote?_code_boundary
    {σ : Signature.{u, v, w}} [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {code : SetTerm} (hQuote : quote? formula = some code) : CodeBoundary code := by
  exact quote_hilbert_with?_code_boundary
    free_name bound_name hQuote
/-- 一个 bound 名称列表对应的单排序 de Bruijn scope。 -/
def scope_of_names {σ : Signature.{u, v, w}} [QuotationNumbering σ] (boundNames : List Nat) : Scope σ :=
  fun _ => boundNames.length
@[simp]
theorem scope_of_names_apply {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] (boundNames : List Nat) (sort : σ.SortSymbol) :
    scope_of_names boundNames sort = boundNames.length :=
  rfl
/-- 压入单排序 binder 与 locally nameless scope 的 `push` 严格对应。 -/
theorem scope_of_names_cons {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (name : Nat) (boundNames : List Nat) (sort : σ.SortSymbol) :
    scope_of_names (name :: boundNames) =
      Scope.push (scope_of_names boundNames) sort := by
  funext target
  have hTarget : target = sort := by
    exact (numbering.sort_eq_object target).trans (numbering.sort_eq_object sort).symm
  simp [scope_of_names, Scope.push, hTarget]
/-! ## 通用 quotation 的全定义性 -/
/-- 任意 Hilbert 核公式只含原子式、等式、否定、蕴含和全称量词。 -/
inductive HilbertCore {σ : Signature.{u, v, w}} : Formula σ → Prop where
  | relation (relation : σ.RelSymbol) (arguments : List (Term σ)) :
      HilbertCore (.rel relation arguments)
  | equality (left right : Term σ) :
      HilbertCore (.equal left right)
  | negation {body : Formula σ} (hBody : HilbertCore body) :
      HilbertCore (.neg body)
  | implication {left right : Formula σ} (hLeft : HilbertCore left) (hRight : HilbertCore right) :
      HilbertCore (.imp left right)
  | universal (sort : σ.SortSymbol) {body : Formula σ} (hBody : HilbertCore body) :
      HilbertCore (.forallE sort body)
namespace HilbertCore
/-- Hilbert 核公式经过 `hilbertize` 后逐构造保持不变。 -/
theorem hilbertize_eq_self
    {σ : Signature.{u, v, w}} {formula : Formula σ} (hCore : HilbertCore formula) (anchorSort : σ.SortSymbol) :
    Formula.hilbertize anchorSort formula = formula := by
  induction hCore with
  | relation relation arguments =>
      rfl
  | equality left right =>
      rfl
  | negation hBody ih =>
      simp [Formula.hilbertize, ih]
  | implication hLeft hRight ihLeft ihRight =>
      simp [Formula.hilbertize, ihLeft, ihRight]
  | universal sort hBody ih =>
      simp [Formula.hilbertize, ih]
end HilbertCore
private theorem option_mapM_exists_of_forall
    {α : Type u₁} {β : Type u₂} (transform : α → Option β) (items : List α) (hTransform : ∀ item, item ∈ items →
      ∃ result, transform item = some result) :
    ∃ results, items.mapM transform = some results := by
  induction items with
  | nil =>
      exact ⟨([] : List β), rfl⟩
  | cons head tail ih =>
      rcases hTransform head (by simp) with ⟨headResult, hHead⟩
      rcases ih (fun item hItem =>
        hTransform item (by simp [hItem])) with
        ⟨tailResults, hTail⟩
      exact ⟨headResult :: tailResults, by simp [hHead, hTail]⟩
/--
一次成功的 `Option.mapM` 会为原列表中的每个元素留下对应的成功计算。
该反演只提取逐项成功性，不要求结果列表与输入列表之间额外携带索引等式。
-/
private theorem option_mapM_eq_some_forall
    {α : Type u₁} {β : Type u₂} (transform : α → Option β)
    {items : List α} {results : List β} (hMap : items.mapM transform = some results) :
    ∀ item, item ∈ items →
      ∃ result, transform item = some result := by
  induction items generalizing results with
  | nil =>
      simp
  | cons head tail ih =>
      cases hHead : transform head with
      | none =>
          simp [hHead] at hMap
      | some headResult =>
          cases hTail : tail.mapM transform with
          | none =>
              simp [hHead, hTail] at hMap
          | some tailResults =>
              intro item hItem
              rcases List.mem_cons.mp hItem with rfl | hTailItem
              · exact ⟨headResult, hHead⟩
              · exact ih hTail item hTailItem
/-- sort 正确的实参列与目标 sort 列等长。 -/
theorem args_well_sorted_length_eq
    {σ : Signature.{u, v, w}} {arguments : List (Term σ)}
    {sorts : List σ.SortSymbol} (hArguments : ArgsWellSorted arguments sorts) :
    arguments.length = sorts.length := by
  induction arguments generalizing sorts with
  | nil =>
      cases hArguments
      rfl
  | cons head tail ih =>
      cases hArguments with
      | cons hHead hTail =>
          simp [ih hTail]
/-! ## quotation 成功性的 scope 反演 -/
/--
项 quotation 成功时，所有 de Bruijn 变量都落在当前名称环境的定义域内。
quotation 本身不检查函数 arity，因此这里只反演 locally nameless scope；良构性仍由
调用方原有的签名证书负责。
-/
theorem quote_term_with?_scoped
    {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
    ∀ {term : Term σ} {code : SetTerm},
      quote_term_with? freeNaming boundNames term = some code →
        TermScoped (scope_of_names boundNames) term
  | .var (.bvar sort index), code, hQuote => by
      cases hName : boundNames[index]? with
      | none =>
          simp [quote_term_with?, hName] at hQuote
      | some name =>
          have hIndex : index < boundNames.length := (List.getElem?_eq_some_iff.mp hName).1
          exact TermScoped.bvar <| by
            simpa [scope_of_names] using hIndex
  | .var (.fvar sort id), code, hQuote =>
      TermScoped.fvar sort id
  | .app function arguments, code, hQuote => by
      cases hCodes :
          arguments.mapM (quote_term_with? freeNaming boundNames) with
      | none =>
          simp [quote_term_with?, hCodes] at hQuote
      | some codes =>
          apply TermScoped.app
          intro argument hArgument
          rcases option_mapM_eq_some_forall (quote_term_with? freeNaming boundNames)
              hCodes argument hArgument with
            ⟨argumentCode, hArgumentQuote⟩
          exact quote_term_with?_scoped
            freeNaming boundNames hArgumentQuote
termination_by term _ _ => term
/-- 成功的关系原子 quotation 逐项恢复参数的 scope。 -/
private theorem quote_relation_with?_arguments_scoped
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {relation : σ.RelSymbol} {arguments : List (Term σ)}
    {code : SetTerm} (hQuote :
      quote_relation_with?
        freeNaming boundNames relation arguments = some code) :
    ∀ argument, argument ∈ arguments →
      TermScoped (scope_of_names boundNames) argument := by
  cases hKind : numbering.relation_kind relation with
  | membership =>
      cases arguments with
      | nil =>
          simp [quote_relation_with?, hKind] at hQuote
      | cons left rest =>
          cases rest with
          | nil =>
              simp [quote_relation_with?, hKind] at hQuote
          | cons right tail =>
              cases tail with
              | cons extra tail =>
                  simp [quote_relation_with?, hKind] at hQuote
              | nil =>
                  cases hLeft :
                      quote_term_with?
                        freeNaming boundNames left with
                  | none =>
                      simp [quote_relation_with?,
                        hKind, hLeft] at hQuote
                  | some leftCode =>
                      cases hRight :
                          quote_term_with?
                            freeNaming boundNames right with
                      | none =>
                          simp [quote_relation_with?,
                            hKind, hLeft, hRight] at hQuote
                      | some rightCode =>
                          intro argument hArgument
                          simp only [List.mem_cons,
                            List.not_mem_nil, or_false] at hArgument
                          rcases hArgument with rfl | rfl
                          · exact quote_term_with?_scoped
                              freeNaming boundNames hLeft
                          · exact quote_term_with?_scoped
                              freeNaming boundNames hRight
  | predicate =>
      cases arguments with
      | nil =>
          simp [quote_relation_with?, hKind] at hQuote
      | cons head tail =>
          cases hArguments : (head :: tail).mapM (quote_term_with?
                  freeNaming boundNames) with
          | none =>
              simp [quote_relation_with?, quote_terms_with?,
                hKind, hArguments] at hQuote
          | some argumentCodes =>
              intro argument hArgument
              rcases option_mapM_eq_some_forall (quote_term_with? freeNaming boundNames)
                  hArguments argument hArgument with
                ⟨argumentCode, hArgumentQuote⟩
              exact quote_term_with?_scoped
                freeNaming boundNames hArgumentQuote
/--
Hilbert quotation 成功时，公式在当前名称环境对应的单排序 scope 中合法。
这给出 quotation 证书所隐含的精确反演信息，使上层可以消去“成功 quotation
之外再额外假设 scoped”的冗余接口。
-/
theorem quote_hilbert_with?_scoped
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ]
    [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) :
    ∀ {boundNames : List Nat} {depth : Nat}
      {formula : Formula σ} {code : SetTerm},
      quote_hilbert_with?
          freeNaming binderNaming boundNames depth formula =
        some code →
      FormulaScoped (scope_of_names boundNames) formula
  | boundNames, depth, .falsum, code, hQuote => by
      simp [quote_hilbert_with?] at hQuote
  | boundNames, depth, .truth, code, hQuote => by
      simp [quote_hilbert_with?] at hQuote
  | boundNames, depth, .rel relation arguments, code, hQuote =>
      FormulaScoped.rel relation arguments <|
        quote_relation_with?_arguments_scoped
          freeNaming boundNames hQuote
  | boundNames, depth, .equal left right, code, hQuote => by
      cases hLeft :
          quote_term_with? freeNaming boundNames left with
      | none =>
          simp [quote_hilbert_with?, hLeft] at hQuote
      | some leftCode =>
          cases hRight :
              quote_term_with? freeNaming boundNames right with
          | none =>
              simp [quote_hilbert_with?, hLeft, hRight] at hQuote
          | some rightCode =>
              exact FormulaScoped.equal (quote_term_with?_scoped
                  freeNaming boundNames hLeft) (quote_term_with?_scoped
                  freeNaming boundNames hRight)
  | boundNames, depth, .neg body, code, hQuote => by
      cases hBody :
          quote_hilbert_with?
            freeNaming binderNaming boundNames depth body with
      | none =>
          simp [quote_hilbert_with?, hBody] at hQuote
      | some bodyCode =>
          exact FormulaScoped.neg <|
            quote_hilbert_with?_scoped
              freeNaming binderNaming hBody
  | boundNames, depth, .conj left right, code, hQuote => by
      simp [quote_hilbert_with?] at hQuote
  | boundNames, depth, .disj left right, code, hQuote => by
      simp [quote_hilbert_with?] at hQuote
  | boundNames, depth, .imp left right, code, hQuote => by
      cases hLeft :
          quote_hilbert_with?
            freeNaming binderNaming boundNames depth left with
      | none =>
          simp [quote_hilbert_with?, hLeft] at hQuote
      | some leftCode =>
          cases hRight :
              quote_hilbert_with?
                freeNaming binderNaming boundNames depth right with
          | none =>
              simp [quote_hilbert_with?, hLeft, hRight] at hQuote
          | some rightCode =>
              exact FormulaScoped.imp (quote_hilbert_with?_scoped
                  freeNaming binderNaming hLeft) (quote_hilbert_with?_scoped
                  freeNaming binderNaming hRight)
  | boundNames, depth, .iff left right, code, hQuote => by
      simp [quote_hilbert_with?] at hQuote
  | boundNames, depth, .forallE sort body, code, hQuote => by
      let name := binderNaming depth
      cases hBody :
          quote_hilbert_with?
            freeNaming binderNaming (name :: boundNames) (depth + 1) body with
      | none =>
          simp [quote_hilbert_with?, name, hBody] at hQuote
      | some bodyCode =>
          have hBodyScoped :=
            quote_hilbert_with?_scoped
              freeNaming binderNaming hBody
          rw [scope_of_names_cons name boundNames sort] at hBodyScoped
          exact FormulaScoped.forallE sort hBodyScoped
  | boundNames, depth, .existsE sort body, code, hQuote => by
      simp [quote_hilbert_with?] at hQuote
termination_by _ _ formula _ _ => formula
/-- scope 中的每个单排序项都有具体 token quotation。 -/
theorem quote_term_tokens_with?_exists {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term σ} (hScoped : TermScoped (scope_of_names boundNames) term) :
    ∃ tokens,
      quote_term_tokens_with? freeNaming boundNames term = some tokens := by
  induction hScoped with
  | bvar hIndex =>
      rename_i context sort index
      have hIndex' : _ := hIndex
      simp [scope_of_names] at hIndex'
      let name : Nat := boundNames[index]
      exact ⟨List.singleton (variable_token name), by
        simp [quote_term_tokens_with?, name, hIndex', List.singleton]⟩
  | fvar sort id =>
      exact ⟨List.singleton (variable_token (freeNaming id)), by
        simp [quote_term_tokens_with?, List.singleton]⟩
  | app function arguments hArguments ih =>
      rcases option_mapM_exists_of_forall (quote_term_tokens_with? freeNaming boundNames) arguments (fun argument hArgument => ih argument hArgument) with
        ⟨codes, hCodes⟩
      cases codes with
      | nil =>
          exact ⟨List.singleton (constant_token (QuotationNumbering.function_number function)), by
            simp [quote_term_tokens_with?, hCodes, List.singleton]⟩
      | cons head tail =>
          exact ⟨function_application_tokens (arguments.length - 1) (QuotationNumbering.function_number function) (head :: tail), by
            simp [quote_term_tokens_with?, hCodes]⟩
/-- Hilbert 核公式在匹配 scope 下必定有具体 token quotation。 -/
theorem quote_hilbert_tokens_with?_exists
    {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat)
    {boundNames : List Nat} {depth : Nat} {formula : Formula σ} (hCore : HilbertCore formula) (hWellFormed : FormulaWellFormed formula)
    (hScoped : FormulaScoped (scope_of_names boundNames) formula) :
    ∃ tokens,
      quote_hilbert_tokens_with? freeNaming binderNaming
        boundNames depth formula = some tokens := by
  induction hCore generalizing boundNames depth with
  | relation relation arguments =>
      cases hWellFormed with
      | rel _ hArgumentsWellFormed =>
          cases hScoped with
          | rel _ _ hArgumentsScoped =>
              cases hKind : numbering.relation_kind relation with
              | membership =>
                  have hDomain := numbering.membership_domain
                    relation hKind
                  have hLength := args_well_sorted_length_eq
                    hArgumentsWellFormed
                  rw [hDomain] at hLength
                  cases arguments with
                  | nil =>
                      simp at hLength
                  | cons left rest =>
                    cases rest with
                    | nil =>
                      simp at hLength
                    | cons right tail =>
                      cases tail with
                      | cons extra tail =>
                        simp at hLength
                      | nil =>
                          rcases quote_term_tokens_with?_exists
                              freeNaming boundNames (hArgumentsScoped left (by simp)) with
                            ⟨leftTokens, hLeftTokens⟩
                          rcases quote_term_tokens_with?_exists
                              freeNaming boundNames (hArgumentsScoped right (by simp)) with
                            ⟨rightTokens, hRightTokens⟩
                          exact ⟨membership_tokens leftTokens rightTokens, by
                            simp [quote_hilbert_tokens_with?,
                              quote_relation_tokens_with?, hKind,
                              hLeftTokens, hRightTokens]⟩
              | predicate =>
                  cases arguments with
                  | nil =>
                      have hLength := args_well_sorted_length_eq
                        hArgumentsWellFormed
                      cases hDomain : σ.relDomain relation with
                      | nil =>
                          exact (numbering.relation_nonempty
                            relation hDomain).elim
                      | cons sort sorts =>
                          rw [hDomain] at hLength
                          simp at hLength
                  | cons head tail =>
                      rcases option_mapM_exists_of_forall (quote_term_tokens_with? freeNaming boundNames) (head :: tail) (fun argument hArgument =>
                            quote_term_tokens_with?_exists
                              freeNaming boundNames (hArgumentsScoped argument hArgument)) with
                        ⟨codes, hCodes⟩
                      exact ⟨predicate_application_tokens ((head :: tail).length - 1) (numbering.relation_number relation) codes, by
                        simp [quote_hilbert_tokens_with?,
                          quote_relation_tokens_with?, hKind, hCodes]⟩
  | equality left right =>
      cases hWellFormed with
      | equal hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | equal hLeftScoped hRightScoped =>
              rcases quote_term_tokens_with?_exists
                  freeNaming boundNames hLeftScoped with
                ⟨leftTokens, hLeftTokens⟩
              rcases quote_term_tokens_with?_exists
                  freeNaming boundNames hRightScoped with
                ⟨rightTokens, hRightTokens⟩
              exact ⟨equality_tokens leftTokens rightTokens, by
                simp [quote_hilbert_tokens_with?,
                  hLeftTokens, hRightTokens]⟩
  | negation hBody ih =>
      cases hWellFormed with
      | neg hBodyWellFormed =>
          cases hScoped with
          | neg hBodyScoped =>
              rcases ih (boundNames := boundNames) (depth := depth)
                  hBodyWellFormed hBodyScoped with
                ⟨bodyTokens, hBodyTokens⟩
              exact ⟨negation_tokens bodyTokens, by
                simp [quote_hilbert_tokens_with?, hBodyTokens]⟩
  | implication hLeft hRight ihLeft ihRight =>
      cases hWellFormed with
      | imp hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | imp hLeftScoped hRightScoped =>
              rcases ihLeft (boundNames := boundNames) (depth := depth)
                  hLeftWellFormed hLeftScoped with
                ⟨leftTokens, hLeftTokens⟩
              rcases ihRight (boundNames := boundNames) (depth := depth)
                  hRightWellFormed hRightScoped with
                ⟨rightTokens, hRightTokens⟩
              exact ⟨implication_tokens leftTokens rightTokens, by
                simp [quote_hilbert_tokens_with?,
                  hLeftTokens, hRightTokens]⟩
  | universal sort hBody ih =>
      cases hWellFormed with
      | forallE _ hBodyWellFormed =>
          cases hScoped with
          | forallE _ hBodyScoped =>
              let name := binderNaming depth
              have hBodyScoped' := hBodyScoped
              rw [← scope_of_names_cons name boundNames sort] at hBodyScoped'
              rcases ih (boundNames := name :: boundNames) (depth := depth + 1) hBodyWellFormed hBodyScoped' with
                ⟨bodyTokens, hBodyTokens⟩
              exact ⟨universal_tokens name bodyTokens, by
                simp [quote_hilbert_tokens_with?, name, hBodyTokens]⟩
/-- scope 中的每个单排序项都有具体 quotation。 -/
theorem quote_term_with?_exists {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term σ} (hScoped : TermScoped (scope_of_names boundNames) term) :
    ∃ code, quote_term_with? freeNaming boundNames term = some code := by
  induction hScoped with
  | bvar hIndex =>
      rename_i context sort index
      have hIndex' : _ := hIndex
      simp [scope_of_names] at hIndex'
      let name : Nat := boundNames[index]
      refine ⟨named_variable_code name, ?_⟩
      simp [quote_term_with?, name, hIndex']
  | fvar sort id =>
      exact ⟨named_variable_code (freeNaming id), by
        simp [quote_term_with?]⟩
  | app function arguments hArguments ih =>
      rcases option_mapM_exists_of_forall (quote_term_with? freeNaming boundNames) arguments (fun argument hArgument => ih argument hArgument) with
        ⟨codes, hCodes⟩
      cases codes with
      | nil =>
          exact ⟨const_codeₘ(numₘ(
              QuotationNumbering.function_number function)), by
            simp [quote_term_with?, hCodes]⟩
      | cons head tail =>
          exact ⟨term_application_code_term (numₘ(arguments.length - 1)) (numₘ(QuotationNumbering.function_number function))
              (argument_sequence (head :: tail)), by
            simp [quote_term_with?, hCodes]⟩
/-- Hilbert 核公式在匹配 scope 下必定可计算引用。 -/
theorem quote_hilbert_with?_exists {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat)
    {boundNames : List Nat} {depth : Nat} {formula : Formula σ} (hCore : HilbertCore formula) (hWellFormed : FormulaWellFormed formula)
    (hScoped : FormulaScoped (scope_of_names boundNames) formula) :
    ∃ code,
      quote_hilbert_with? freeNaming binderNaming
        boundNames depth formula = some code := by
  induction hCore generalizing boundNames depth with
  | relation relation arguments =>
      cases hWellFormed with
      | rel _ hArgumentsWellFormed =>
          cases hScoped with
          | rel _ _ hArgumentsScoped =>
              cases hKind : numbering.relation_kind relation with
              | membership =>
                  have hDomain := numbering.membership_domain
                    relation hKind
                  have hLength := args_well_sorted_length_eq
                    hArgumentsWellFormed
                  rw [hDomain] at hLength
                  cases arguments with
                  | nil =>
                      simp at hLength
                  | cons left rest =>
                    cases rest with
                    | nil =>
                      simp at hLength
                    | cons right tail =>
                      cases tail with
                      | cons extra tail =>
                        simp at hLength
                      | nil =>
                          rcases quote_term_with?_exists
                              freeNaming boundNames (hArgumentsScoped left (by simp)) with
                            ⟨leftCode, hLeftCode⟩
                          rcases quote_term_with?_exists
                              freeNaming boundNames (hArgumentsScoped right (by simp)) with
                            ⟨rightCode, hRightCode⟩
                          exact ⟨membership_atomic_formula_code_term
                              leftCode rightCode, by
                            simp [quote_hilbert_with?,
                              quote_relation_with?, hKind,
                              hLeftCode, hRightCode]⟩
              | predicate =>
                  cases arguments with
                  | nil =>
                      have hLength := args_well_sorted_length_eq
                        hArgumentsWellFormed
                      cases hDomain : σ.relDomain relation with
                      | nil =>
                          exact (numbering.relation_nonempty
                            relation hDomain).elim
                      | cons sort sorts =>
                          rw [hDomain] at hLength
                          simp at hLength
                  | cons head tail =>
                      rcases option_mapM_exists_of_forall (quote_term_with? freeNaming boundNames) (head :: tail) (fun argument hArgument =>
                            quote_term_with?_exists freeNaming boundNames (hArgumentsScoped argument hArgument)) with
                        ⟨codes, hCodes⟩
                      exact ⟨predicate_application_code_term (numₘ((head :: tail).length - 1)) (numₘ(numbering.relation_number relation))
                          (argument_sequence codes), by
                        simp [quote_hilbert_with?, quote_relation_with?,
                          hKind, hCodes]⟩
  | equality left right =>
      cases hWellFormed with
      | equal hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | equal hLeftScoped hRightScoped =>
              rcases quote_term_with?_exists
                  freeNaming boundNames hLeftScoped with
                ⟨leftCode, hLeftCode⟩
              rcases quote_term_with?_exists
                  freeNaming boundNames hRightScoped with
                ⟨rightCode, hRightCode⟩
              exact ⟨eq_codeₘ(leftCode, rightCode), by
                simp [quote_hilbert_with?, hLeftCode, hRightCode]⟩
  | negation hBody ih =>
      cases hWellFormed with
      | neg hBodyWellFormed =>
          cases hScoped with
          | neg hBodyScoped =>
              rcases ih (boundNames := boundNames) (depth := depth)
                  hBodyWellFormed hBodyScoped with
                ⟨bodyCode, hBodyCode⟩
              exact ⟨neg_codeₘ(bodyCode), by
                simp [quote_hilbert_with?, hBodyCode]⟩
  | implication hLeft hRight ihLeft ihRight =>
      cases hWellFormed with
      | imp hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | imp hLeftScoped hRightScoped =>
              rcases ihLeft (boundNames := boundNames) (depth := depth)
                  hLeftWellFormed hLeftScoped with
                ⟨leftCode, hLeftCode⟩
              rcases ihRight (boundNames := boundNames) (depth := depth)
                  hRightWellFormed hRightScoped with
                ⟨rightCode, hRightCode⟩
              exact ⟨imp_codeₘ(leftCode, rightCode), by
                simp [quote_hilbert_with?, hLeftCode, hRightCode]⟩
  | universal sort hBody ih =>
      cases hWellFormed with
      | forallE _ hBodyWellFormed =>
          cases hScoped with
          | forallE _ hBodyScoped =>
              let name := binderNaming depth
              have hBodyScoped' := hBodyScoped
              rw [← scope_of_names_cons name boundNames sort] at hBodyScoped'
              rcases ih (boundNames := name :: boundNames) (depth := depth + 1) hBodyWellFormed hBodyScoped' with
                ⟨bodyCode, hBodyCode⟩
              exact ⟨forall_codeₘ(named_variable_code name, bodyCode), by
                simp [quote_hilbert_with?, name, hBodyCode]⟩
/-- Hilbert 归约保持公式的 locally nameless scope。 -/
theorem hilbertize_scoped {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {scope : Scope σ} {formula : Formula σ} (hScoped : FormulaScoped scope formula) :
    FormulaScoped scope (Formula.hilbertize anchorSort formula) := by
  induction hScoped with
  | falsum =>
      rename_i context
      have hIndex :
          0 < (Scope.push context anchorSort) anchorSort := by
        simp [Scope.push]
      have hVariable :
          TermScoped (Scope.push context anchorSort) (Term.var (.bvar anchorSort 0)) :=
        .bvar hIndex
      have hTruth := FormulaScoped.forallE anchorSort (FormulaScoped.equal hVariable hVariable)
      simpa [Formula.hilbertize, Formula.hilbert_falsum,
        Formula.hilbert_truth] using FormulaScoped.neg hTruth
  | truth =>
      rename_i context
      have hIndex :
          0 < (Scope.push context anchorSort) anchorSort := by
        simp [Scope.push]
      have hVariable :
          TermScoped (Scope.push context anchorSort) (Term.var (.bvar anchorSort 0)) :=
        .bvar hIndex
      have hTruth := FormulaScoped.forallE anchorSort (FormulaScoped.equal hVariable hVariable)
      simpa [Formula.hilbertize, Formula.hilbert_truth] using hTruth
  | rel relation arguments hArguments =>
      exact .rel relation arguments hArguments
  | equal hLeft hRight =>
      exact .equal hLeft hRight
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .neg (.imp ihLeft (.neg ihRight))
  | disj hLeft hRight ihLeft ihRight =>
      exact .imp (.neg ihLeft) ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .neg (.imp (.imp ihLeft ihRight) (.neg (.imp ihRight ihLeft)))
  | forallE sort hBody ih =>
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .neg (.forallE sort (.neg ih))
/-- Hilbert 归约保持公式的 sort/arity 良构性。 -/
theorem hilbertize_well_formed {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) {formula : Formula σ} (hWellFormed : FormulaWellFormed formula) :
    FormulaWellFormed (Formula.hilbertize anchorSort formula) := by
  induction hWellFormed with
  | falsum =>
      exact .neg (.forallE anchorSort (.equal (.bvar anchorSort 0) (.bvar anchorSort 0)))
  | truth =>
      exact .forallE anchorSort (.equal (.bvar anchorSort 0) (.bvar anchorSort 0))
  | rel relation hArguments =>
      exact .rel relation hArguments
  | equal hLeft hRight =>
      exact .equal hLeft hRight
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .neg (.imp ihLeft (.neg ihRight))
  | disj hLeft hRight ihLeft ihRight =>
      exact .imp (.neg ihLeft) ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .neg (.imp (.imp ihLeft ihRight) (.neg (.imp ihRight ihLeft)))
  | forallE sort hBody ih =>
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .neg (.forallE sort (.neg ih))
/-- well-formed 公式的 Hilbert 归约只含可编码的核心构造。 -/
theorem hilbertize_hilbert_core {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) {formula : Formula σ} (hWellFormed : FormulaWellFormed formula) :
    HilbertCore (Formula.hilbertize anchorSort formula) := by
  induction hWellFormed with
  | falsum =>
      exact .negation (.universal anchorSort (.equality _ _))
  | truth =>
      exact .universal anchorSort (.equality _ _)
  | rel relation hArguments =>
      exact .relation relation _
  | equal hLeft hRight =>
      exact .equality _ _
  | neg hBody ih =>
      exact .negation ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .negation (.implication ihLeft (.negation ihRight))
  | disj hLeft hRight ihLeft ihRight =>
      exact .implication (.negation ihLeft) ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .implication ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .negation (.implication (.implication ihLeft ihRight) (.negation (.implication ihRight ihLeft)))
  | forallE sort hBody ih =>
      exact .universal sort ih
  | existsE sort hBody ih =>
      exact .negation (.universal sort (.negation ih))
/-- 每个 admissible 单排序公式在任意显式命名下都有具体 token quotation。 -/
theorem quote_tokens_with?_exists {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) {formula : Formula σ}
    (hFormula : Formula.Admissible formula) :
    ∃ tokens,
      quote_tokens_with? freeNaming binderNaming formula = some tokens := by
  apply quote_hilbert_tokens_with?_exists freeNaming binderNaming
  · exact hilbertize_hilbert_core numbering.objectSort hFormula.1
  · exact hilbertize_well_formed numbering.objectSort hFormula.1
  · exact hilbertize_scoped numbering.objectSort hFormula.2
/-- 每个 admissible 单排序公式的规范 token quotation 都计算成功。 -/
theorem quote_tokens?_exists {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} (hFormula : Formula.Admissible formula) :
    ∃ tokens, quote_tokens? formula = some tokens :=
  quote_tokens_with?_exists free_name bound_name hFormula
/-- 每个 admissible 单排序公式在任意显式命名下都可计算引用。 -/
theorem quote_with?_exists {σ : Signature.{u, v, w}}
    [numbering : QuotationNumbering σ] [DecidableEq σ.SortSymbol] (freeNaming binderNaming : Nat → Nat) {formula : Formula σ}
    (hFormula : Formula.Admissible formula) :
    ∃ code, quote_with? freeNaming binderNaming formula = some code := by
  apply quote_hilbert_with?_exists freeNaming binderNaming
  · exact hilbertize_hilbert_core numbering.objectSort hFormula.1
  · exact hilbertize_well_formed numbering.objectSort hFormula.1
  · exact hilbertize_scoped numbering.objectSort hFormula.2
/-- 每个 admissible 单排序公式的规范 quotation 都计算成功。 -/
theorem quote?_exists {σ : Signature.{u, v, w}}
    [QuotationNumbering σ] [DecidableEq σ.SortSymbol]
    {formula : Formula σ} (hFormula : Formula.Admissible formula) :
    ∃ code, quote? formula = some code :=
  quote_with?_exists free_name bound_name hFormula
end Numbered
end YesMetaZFC.Logic.FirstOrder.FormalSystem.GodelQuotation
