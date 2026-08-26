import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Numbered
import YesMetaZFC.Logic.FirstOrder.Hilbert.Translation
import YesMetaZFC.SetTheory.Language
/-!
# 纯集合论语法的 Gödel quotation
本模块把外部 locally nameless 纯集合论语法具体引用到对象集合论中的形式表达式编码。
自由变量由一个显式编号函数命名；bound 变量则由最内层在前的环境解释。因而 quotation
不会把 de Bruijn 下标误当作内部具名变量，也不会把 binder 命名选择隐藏在全局常量中。
内部公式编码只有隶属、等式、否定、蕴含和全称量词五类构造。公共公式先经
`Formula.hilbertize` 归约，再进入本层。`HilbertQuoted` 记录显式具名构造；其原始关系
允许调用方控制 binder 名，规范 `quote?` 则以“自由变量取偶数名、binder 取奇数名”
保证两类名字不相交。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
namespace GodelQuotation
/-- 纯集合论签名使用文献中的专用隶属符号编码。 -/
instance pure_set_quotation_numbering : QuotationNumbering ℒ where
  objectSort := SetTheory.SetSort.set
  sort_eq_object := by
    intro sort
    cases sort
    rfl
  function_number := fun function => nomatch function
  relation_number
    | SetTheory.RelationSymbol.membership => 0
  function_number_injective := by
    intro function
    exact nomatch function
  relation_number_injective := by
    intro left right hEqual
    cases left
    cases right
    rfl
  relation_kind
    | SetTheory.RelationSymbol.membership => .membership
  relation_nonempty := by
    intro relation
    cases relation
    simp [SetTheory.signature]
  membership_domain := by
    intro relation hKind
    cases relation
    rfl
  membership_unique := by
    intro left right hLeft hRight
    cases left
    cases right
    rfl
@[simp]
theorem pure_set_relation_kind :
    pure_set_quotation_numbering.relation_kind
        SetTheory.RelationSymbol.membership =
      QuotationRelationKind.membership :=
  rfl
@[simp]
theorem pure_set_relation_number :
    pure_set_quotation_numbering.relation_number
        SetTheory.RelationSymbol.membership = 0 :=
  rfl
/-- 把一个内部变量编号实现为对象语言中的变量符号编码项。 -/
abbrev named_variable_code (name : Nat) : SetTerm :=
  Numbered.named_variable_code name
/--
在显式 bound 环境下引用一个纯集合论项。环境按 de Bruijn 顺序存放内部变量编号。
纯集合论没有函数符号，所以合法项只能是变量。
-/
abbrev quote_term_with? (freeNaming : FreeVarId → Nat) (boundNames : List Nat) :
    Term ℒ → Option SetTerm :=
  Numbered.quote_term_with? freeNaming boundNames
/--
内部 Hilbert 公式片段的显式具名构造关系。
该原始关系刻意不固定 binder 名，供量词闭包复用原自由变量名；需要语义 α-解释时，
调用方还应携带相应的新鲜性事实。公开的规范 `quote?` 由偶/奇命名自动满足自由名与
binder 名不相交。
-/
inductive HilbertQuoted (freeNaming : FreeVarId → Nat) :
    List Nat → Formula ℒ → SetTerm → Prop where
  | membership {boundNames : List Nat}
      {left right : Term ℒ} {leftCode rightCode : SetTerm} (hLeft : quote_term_with? freeNaming boundNames left = some leftCode)
      (hRight : quote_term_with? freeNaming boundNames right = some rightCode) :
      HilbertQuoted freeNaming boundNames (.rel SetTheory.RelationSymbol.membership [left, right]) (membership_atomic_formula_code_term leftCode rightCode)
  | equality {boundNames : List Nat}
      {left right : Term ℒ} {leftCode rightCode : SetTerm} (hLeft : quote_term_with? freeNaming boundNames left = some leftCode)
      (hRight : quote_term_with? freeNaming boundNames right = some rightCode) :
      HilbertQuoted freeNaming boundNames (.equal left right) (eq_codeₘ(leftCode, rightCode))
  | negation {boundNames : List Nat}
      {body : Formula ℒ} {bodyCode : SetTerm} (hBody : HilbertQuoted freeNaming boundNames body bodyCode) :
      HilbertQuoted freeNaming boundNames (.neg body) (neg_codeₘ(bodyCode))
  | implication {boundNames : List Nat}
      {left right : Formula ℒ} {leftCode rightCode : SetTerm} (hLeft : HilbertQuoted freeNaming boundNames left leftCode)
      (hRight : HilbertQuoted freeNaming boundNames right rightCode) :
      HilbertQuoted freeNaming boundNames (.imp left right) (imp_codeₘ(leftCode, rightCode))
  | universal {boundNames : List Nat}
      {body : Formula ℒ} {bodyCode : SetTerm} (name : Nat) (hBody : HilbertQuoted freeNaming (name :: boundNames) body bodyCode) :
      HilbertQuoted freeNaming boundNames (.forallE SetTheory.SetSort.set body) (forall_codeₘ(named_variable_code name, bodyCode))
/-- 可计算 quotation 使用给定的 binder 名称流。 -/
abbrev quote_hilbert_with? (freeNaming binderNaming : Nat → Nat) (boundNames : List Nat) (depth : Nat) :
    Formula ℒ → Option SetTerm :=
  Numbered.quote_hilbert_with?
    freeNaming binderNaming boundNames depth
/-- 公共公式的规范 Gödel quotation；先归约到内部 Hilbert 片段。 -/
def quote? (formula : Formula ℒ) : Option SetTerm :=
  Numbered.quote? formula
/-! ## 可计算 quotation 与关系 quotation 的对应 -/
/-- 可计算 quotation 成功时，结果由显式具名构造关系见证。 -/
theorem quote_hilbert_with?_sound (freeNaming binderNaming : Nat → Nat)
    {boundNames : List Nat} {depth : Nat}
    {formula : Formula ℒ} {code : SetTerm} (hQuote : quote_hilbert_with? freeNaming binderNaming
      boundNames depth formula = some code) :
    HilbertQuoted freeNaming boundNames formula code := by
  induction formula generalizing boundNames depth code with
  | falsum =>
      simp [quote_hilbert_with?] at hQuote
  | truth =>
      simp [quote_hilbert_with?] at hQuote
  | rel relation arguments =>
      cases relation
      cases arguments with
      | nil =>
          simp [quote_hilbert_with?] at hQuote
      | cons left rest =>
          cases rest with
          | nil =>
              simp [quote_hilbert_with?] at hQuote
          | cons right tail =>
              cases tail with
              | cons extra tail =>
                  simp [quote_hilbert_with?] at hQuote
              | nil =>
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
                          exact .membership hLeft hRight
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
              exact .equality hLeft hRight
  | neg body ih =>
      cases hBody : quote_hilbert_with? freeNaming binderNaming
          boundNames depth body with
      | none =>
          simp [quote_hilbert_with?, hBody] at hQuote
      | some bodyCode =>
          simp [quote_hilbert_with?, hBody] at hQuote
          subst code
          exact .negation (ih hBody)
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
              exact .implication (ihLeft hLeft) (ihRight hRight)
  | iff left right =>
      simp [quote_hilbert_with?] at hQuote
  | forallE sort body ih =>
      cases sort
      let name := binderNaming depth
      cases hBody : quote_hilbert_with? freeNaming binderNaming (name :: boundNames) (depth + 1) body with
      | none =>
          simp [quote_hilbert_with?, name, hBody] at hQuote
      | some bodyCode =>
          simp [quote_hilbert_with?, name, hBody] at hQuote
          subst code
          exact .universal name (ih hBody)
  | existsE sort body =>
      simp [quote_hilbert_with?] at hQuote
/-! ## 引用结果的对象项良构性 -/
/-- 成功引用的纯集合论项总产生 closed、sort 正确的对象编码项。 -/
theorem quote_term_with?_admissible (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term ℒ} {code : SetTerm} (hQuote : quote_term_with? freeNaming boundNames term = some code) :
    Term.Admissible code SetSort.set := by
  cases term with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          cases hName : boundNames[index]? with
          | none =>
              simp [quote_term_with?, hName] at hQuote
          | some name =>
              simp [quote_term_with?, hName] at hQuote
              subst code
              exact variable_code_term_admissible (numₘ(name)) (finite_numeral_term_admissible name)
      | fvar sort id =>
          cases sort
          simp [quote_term_with?] at hQuote
          subst code
          exact variable_code_term_admissible (numₘ(freeNaming id)) (finite_numeral_term_admissible (freeNaming id))
  | app function arguments =>
      exact nomatch function
/-- 关系 quotation 产生的每个公式编码项都满足对象项 admissibility。 -/
theorem HilbertQuoted.code_admissible
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula : Formula ℒ} {code : SetTerm} (hQuoted : HilbertQuoted freeNaming boundNames formula code) :
    Term.Admissible code SetSort.set := by
  induction hQuoted with
  | membership hLeft hRight =>
      exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term _ _
        membership_symbol_code_term_admissible (quote_term_with?_admissible _ _ hLeft) (quote_term_with?_admissible _ _ hRight)
  | equality hLeft hRight =>
      exact equality_formula_code_term_admissible _ _ (quote_term_with?_admissible _ _ hLeft) (quote_term_with?_admissible _ _ hRight)
  | negation hBody ih =>
      exact negation_formula_code_term_admissible _ ih
  | implication hLeft hRight ihLeft ihRight =>
      exact implication_formula_code_term_admissible _ _ ihLeft ihRight
  | universal name hBody ih =>
      exact universal_formula_code_term_admissible _ _ (variable_code_term_admissible (numₘ(name)) (finite_numeral_term_admissible name))
        ih
/-! ## quotation 对象项的闭编码性质 -/
@[simp]
theorem named_variable_code_freeSupport (name : Nat) :
    Term.freeSupport (named_variable_code name) = [] := by
  simp [Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport]
/-- 成功引用的纯集合论项编码不含任何对象语言自由变量。 -/
theorem quote_term_with?_freeSupport_nil (freeNaming : FreeVarId → Nat) (boundNames : List Nat)
    {term : Term ℒ} {code : SetTerm} (hQuote : quote_term_with? freeNaming boundNames term = some code) :
    Term.freeSupport code = [] := by
  cases term with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          cases hName : boundNames[index]? with
          | none =>
              simp [quote_term_with?, hName] at hQuote
          | some name =>
              simp [quote_term_with?, hName] at hQuote
              subst code
              exact named_variable_code_freeSupport name
      | fvar sort id =>
          cases sort
          simp [quote_term_with?] at hQuote
          subst code
          exact named_variable_code_freeSupport (freeNaming id)
  | app function arguments =>
      exact nomatch function
/-- 显式 Hilbert quotation 产生的对象公式编码不含对象语言自由变量。 -/
theorem HilbertQuoted.code_freeSupport_nil
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula : Formula ℒ} {code : SetTerm} (hQuote : HilbertQuoted freeNaming boundNames formula code) :
    Term.freeSupport code = [] := by
  induction hQuote with
  | membership hLeft hRight =>
      have hLeftSupport := quote_term_with?_freeSupport_nil
        _ _ hLeft
      have hRightSupport := quote_term_with?_freeSupport_nil
        _ _ hRight
      simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport,
        hLeftSupport, hRightSupport]
  | equality hLeft hRight =>
      have hLeftSupport := quote_term_with?_freeSupport_nil
        _ _ hLeft
      have hRightSupport := quote_term_with?_freeSupport_nil
        _ _ hRight
      simp [Term.freeSupport, Term.freeSupportList,
        hLeftSupport, hRightSupport]
  | negation hBody ih =>
      simp [Term.freeSupport, Term.freeSupportList, ih]
  | implication hLeft hRight ihLeft ihRight =>
      simp [Term.freeSupport, Term.freeSupportList,
        ihLeft, ihRight]
  | universal name hBody ih =>
      simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport, ih]
/-! ## admissible 外部语法上的 quotation 全定义性 -/
/-- 每个 admissible 纯集合论公式的规范 quotation 都计算成功。 -/
theorem quote?_exists {formula : Formula ℒ} (hFormula : Formula.Admissible formula) :
    ∃ code, quote? formula = some code :=
  Numbered.quote?_exists hFormula
/-- 规范 quotation 的成功结果同时携带显式具名构造证书。 -/
theorem quote?_sound {formula : Formula ℒ} {code : SetTerm} (hQuote : quote? formula = some code) :
    HilbertQuoted free_name [] (Formula.hilbertize SetTheory.SetSort.set formula) code :=
  quote_hilbert_with?_sound free_name bound_name hQuote
/-- admissible 外部公式的规范 quotation 产生 admissible 对象编码项。 -/
theorem quote?_admissible {formula : Formula ℒ} {code : SetTerm} (hQuote : quote? formula = some code) :
    Term.Admissible code SetSort.set := (quote?_sound hQuote).code_admissible
/-! ## 关闭自由变量与 α-quotation -/
/--
把自由变量关闭在第 `depth` 层，等价于在具名 bound 环境同一位置插入它的内部名字。
这是 locally nameless quotation 与内部具名量词编码之间的关键等式。
-/
theorem quote_term_with?_closeFreeAt (freeNaming : FreeVarId → Nat) (boundNames : List Nat) (id depth : Nat) (term : Term ℒ)
    (hDepth : depth ≤ boundNames.length) :
    quote_term_with? freeNaming (boundNames.insertIdx depth (freeNaming id)) (Term.closeFreeAt SetTheory.SetSort.set id depth term) =
      quote_term_with? freeNaming boundNames term := by
  cases term with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hIndex : depth ≤ index
          · have hStrict : depth < index + 1 := by omega
            simp [Term.closeFreeAt, quote_term_with?, hIndex,
              List.getElem?_insertIdx_of_gt hStrict]
          · have hStrict : index < depth := by omega
            simp [Term.closeFreeAt, quote_term_with?, hIndex,
              List.getElem?_insertIdx_of_lt hStrict]
      | fvar sort freeId =>
          cases sort
          by_cases hId : freeId = id
          · subst freeId
            simp [Term.closeFreeAt, quote_term_with?, hDepth,
              List.getElem?_insertIdx_self]
          · simp [Term.closeFreeAt, quote_term_with?, hId]
  | app function arguments =>
      exact nomatch function
/-- 关系 quotation 穿过任意深度的 `closeFreeAt`，且编码项本身不变。 -/
theorem HilbertQuoted.close_free_at
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula : Formula ℒ} {code : SetTerm} (hQuoted : HilbertQuoted freeNaming boundNames formula code) (id depth : Nat) (hDepth : depth ≤ boundNames.length) :
    HilbertQuoted freeNaming (boundNames.insertIdx depth (freeNaming id)) (Formula.closeFreeAt SetTheory.SetSort.set id depth formula)
      code := by
  induction hQuoted generalizing depth with
  | membership hLeft hRight =>
      apply HilbertQuoted.membership
      · rw [quote_term_with?_closeFreeAt _ _ id depth _ hDepth]
        exact hLeft
      · rw [quote_term_with?_closeFreeAt _ _ id depth _ hDepth]
        exact hRight
  | equality hLeft hRight =>
      apply HilbertQuoted.equality
      · rw [quote_term_with?_closeFreeAt _ _ id depth _ hDepth]
        exact hLeft
      · rw [quote_term_with?_closeFreeAt _ _ id depth _ hDepth]
        exact hRight
  | negation hBody ih =>
      exact .negation (ih depth hDepth)
  | implication hLeft hRight ihLeft ihRight =>
      exact .implication (ihLeft depth hDepth) (ihRight depth hDepth)
  | @universal currentNames body bodyCode name hBody ih =>
      have hDepth' : depth + 1 ≤ (name :: currentNames).length := by
        simp
        omega
      have hBodyClosed := ih (depth + 1) hDepth'
      simpa [Formula.closeFreeAt, Formula.next_depth,
        List.insertIdx] using HilbertQuoted.universal name hBodyClosed
/--
在最外层关闭自由变量并加全称量词时，选择原自由变量的内部名字即可完全复用原编码。
-/
theorem HilbertQuoted.forall_close_free
    {freeNaming : FreeVarId → Nat} {formula : Formula ℒ}
    {code : SetTerm} (hQuoted : HilbertQuoted freeNaming [] formula code) (id : FreeVarId) :
    HilbertQuoted freeNaming [] (Formula.forallE SetTheory.SetSort.set (Formula.closeFreeAt SetTheory.SetSort.set id 0 formula))
      (forall_codeₘ(named_variable_code (freeNaming id), code)) := by
  apply HilbertQuoted.universal (freeNaming id)
  simpa [List.insertIdx] using hQuoted.close_free_at id 0 (by simp)
/-! ## Hilbert 公理构造与内部编码构造的精确对应 -/
namespace HilbertQuoted
/-- 第一类命题公理的 quotation 正是内部第一类公理编码项。 -/
theorem implication_distribution_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {antecedent middle consequent : Formula ℒ}
    {antecedentCode middleCode consequentCode : SetTerm} (hAntecedent : HilbertQuoted freeNaming boundNames
      antecedent antecedentCode) (hMiddle : HilbertQuoted freeNaming boundNames middle middleCode) (hConsequent : HilbertQuoted freeNaming boundNames
      consequent consequentCode) :
    HilbertQuoted freeNaming boundNames (Formula.imp (Formula.imp antecedent (Formula.imp middle consequent)) (Formula.imp (Formula.imp antecedent middle)
          (Formula.imp antecedent consequent))) (implication_distribution_axiom_code_term
        antecedentCode middleCode consequentCode) :=
  .implication (.implication hAntecedent (.implication hMiddle hConsequent)) (.implication (.implication hAntecedent hMiddle)
      (.implication hAntecedent hConsequent))
/-- 第二类命题公理的 quotation。 -/
theorem self_implication_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula : Formula ℒ} {code : SetTerm} (hFormula : HilbertQuoted freeNaming boundNames formula code) :
    HilbertQuoted freeNaming boundNames (Formula.imp formula (Formula.imp formula formula)) (self_implication_axiom_code_term code) :=
  .implication hFormula (.implication hFormula hFormula)
/-- 第三类命题公理的 quotation。 -/
theorem weakening_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula extra : Formula ℒ} {formulaCode extraCode : SetTerm} (hFormula : HilbertQuoted freeNaming boundNames formula formulaCode)
    (hExtra : HilbertQuoted freeNaming boundNames extra extraCode) :
    HilbertQuoted freeNaming boundNames (Formula.imp formula (Formula.imp extra formula)) (weakening_axiom_code_term formulaCode extraCode) :=
  .implication hFormula (.implication hExtra hFormula)
/-- 第四类命题公理的 quotation。 -/
theorem contradiction_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula conclusion : Formula ℒ}
    {formulaCode conclusionCode : SetTerm} (hFormula : HilbertQuoted freeNaming boundNames formula formulaCode)
    (hConclusion : HilbertQuoted freeNaming boundNames
      conclusion conclusionCode) :
    HilbertQuoted freeNaming boundNames (Formula.imp formula (Formula.imp (Formula.neg formula) conclusion))
      (contradiction_axiom_code_term formulaCode conclusionCode) :=
  .implication hFormula (.implication (.negation hFormula) hConclusion)
/-- 第五类命题公理的 quotation。 -/
theorem classical_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula : Formula ℒ} {code : SetTerm} (hFormula : HilbertQuoted freeNaming boundNames formula code) :
    HilbertQuoted freeNaming boundNames (Formula.imp (Formula.imp (Formula.neg formula) formula) formula) (classical_axiom_code_term code) :=
  .implication (.implication (.negation hFormula) hFormula) hFormula
/-- 第六类命题公理的 quotation。 -/
theorem explosion_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula conclusion : Formula ℒ}
    {formulaCode conclusionCode : SetTerm} (hFormula : HilbertQuoted freeNaming boundNames formula formulaCode)
    (hConclusion : HilbertQuoted freeNaming boundNames
      conclusion conclusionCode) :
    HilbertQuoted freeNaming boundNames (Formula.imp (Formula.neg formula) (Formula.imp formula conclusion))
      (explosion_axiom_code_term formulaCode conclusionCode) :=
  .implication (.negation hFormula) (.implication hFormula hConclusion)
/-- 第七类命题公理的 quotation。 -/
theorem case_analysis_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {formula conclusion : Formula ℒ}
    {formulaCode conclusionCode : SetTerm} (hFormula : HilbertQuoted freeNaming boundNames formula formulaCode)
    (hConclusion : HilbertQuoted freeNaming boundNames
      conclusion conclusionCode) :
    HilbertQuoted freeNaming boundNames (Formula.imp (Formula.imp formula conclusion) (Formula.imp (Formula.imp (Formula.neg formula) conclusion)
          conclusion)) (case_analysis_axiom_code_term formulaCode conclusionCode) :=
  .implication (.implication hFormula hConclusion) (.implication (.implication (.negation hFormula) hConclusion)
      hConclusion)
/-- 全称分配公理在同一个显式 binder 名称下精确对应内部编码。 -/
theorem quantifier_distribution_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {antecedent consequent : Formula ℒ}
    {antecedentCode consequentCode : SetTerm} (name : Nat) (hAntecedent : HilbertQuoted freeNaming (name :: boundNames)
      antecedent antecedentCode) (hConsequent : HilbertQuoted freeNaming (name :: boundNames)
      consequent consequentCode) :
    HilbertQuoted freeNaming boundNames (Formula.imp (Formula.forallE SetTheory.SetSort.set (Formula.imp antecedent consequent)) (Formula.imp
          (Formula.forallE SetTheory.SetSort.set antecedent) (Formula.forallE SetTheory.SetSort.set consequent))) (quantifier_distribution_axiom_code_term
        (named_variable_code name) antecedentCode consequentCode) :=
  .implication (.universal name (.implication hAntecedent hConsequent)) (.implication (.universal name hAntecedent) (.universal name hConsequent))
/--
无关量词公理的显式 quotation 组合。
前件与量词体分别携带 quotation 证书；调用方负责证明二者确实来自同一公式在相邻
binder 深度下的规范引用。这里不再错误地假定二者拥有同一个代码项。
-/
theorem vacuous_quantifier_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {antecedent body : Formula ℒ}
    {antecedentCode bodyCode : SetTerm} (name : Nat) (hAntecedent :
      HilbertQuoted freeNaming boundNames
        antecedent antecedentCode) (hBody :
      HilbertQuoted freeNaming (name :: boundNames)
        body bodyCode) :
    HilbertQuoted freeNaming boundNames (Formula.imp antecedent (Formula.forallE SetTheory.SetSort.set body)) (vacuous_quantifier_axiom_code_term
        (named_variable_code name)
        antecedentCode bodyCode) :=
  .implication hAntecedent (.universal name hBody)
/-- 变量恒等律 quotation 正是内部恒等律模式项。 -/
theorem equality_reflexivity_axiom
    {freeNaming : FreeVarId → Nat} {boundNames : List Nat}
    {term : Term ℒ} {termCode : SetTerm} (hTerm : quote_term_with? freeNaming boundNames term = some termCode) :
    HilbertQuoted freeNaming boundNames (Formula.equal term term) (equality_reflexivity_axiom_code_term termCode) :=
  .equality hTerm hTerm
end HilbertQuoted
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
