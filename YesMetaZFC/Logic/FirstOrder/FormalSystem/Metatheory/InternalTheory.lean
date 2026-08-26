import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Diagonal
import YesMetaZFC.SetTheory.Definitional.Project.Syntax
/-!
# 集合论基础理论的内部 FormalSystem 构造器
本模块先为任意 FormalSystem 基础理论提供统一的内部化构造器，再把项目级
`Definitional.Project` 集合论理论正规嵌入 FormalSystem 扩展签名。构造器统一叠加
Gödel quotation 与有限 Hilbert 演绎编码，并对完整联合理论执行 Hilbert 归约，因此
可直接消费 `fs_diagonal_lemma`。
项目公式中的外延等同原子映射到一阶核心等词，子集原子映射到 FormalSystem 的子集
关系符号；Project 适配层显式加入子集定义理论，不依赖编码理论内部的间接包含链。
bound 变量沿单排序 de Bruijn 编号原样嵌入，不借助自由变量改名或其他旁路。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
abbrev FsProjectTerm :=
  _root_.YesMetaZFC.SetTheory.Definitional.Project.Term
abbrev FsProjectFormula :=
  _root_.YesMetaZFC.SetTheory.Definitional.Project.Formula
abbrev FsProjectSentence :=
  _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence
abbrev FsProjectTheory :=
  _root_.YesMetaZFC.SetTheory.Definitional.Project.Theory
/-! ## 项目集合论语法到 FormalSystem 签名 -/
/-- 项目集合论变量项沿单排序 de Bruijn 编号嵌入 FormalSystem。 -/
def fs_embed_project_term {depth : Nat} :
    FsProjectTerm depth → SetTerm
  | .bound entry =>
      Term.var (.bvar SetSort.set entry.val)
  | .free id =>
      Term.var (.fvar SetSort.set id)
/-- 项目集合论公式到 FormalSystem 扩展签名的结构递归嵌入。 -/
def fs_embed_project_formula :
    {availableStage depth : Nat} →
      FsProjectFormula availableStage depth → SetFormula
  | _, _, .falsum =>
      .falsum
  | _, _, .truth =>
      .truth
  | _, _, .mem left right =>
      membership_formula (fs_embed_project_term left) (fs_embed_project_term right)
  | _, _, .atom .extensionalEq _ arguments =>
      Formula.equal (fs_embed_project_term (arguments 0)) (fs_embed_project_term (arguments 1))
  | _, _, .atom .subset _ arguments =>
      subset_formula (fs_embed_project_term (arguments 0)) (fs_embed_project_term (arguments 1))
  | _, _, .neg formula =>
      .neg (fs_embed_project_formula formula)
  | _, _, .conj left right =>
      .conj (fs_embed_project_formula left) (fs_embed_project_formula right)
  | _, _, .disj left right =>
      .disj (fs_embed_project_formula left) (fs_embed_project_formula right)
  | _, _, .imp left right =>
      .imp (fs_embed_project_formula left) (fs_embed_project_formula right)
  | _, _, .iff left right =>
      .iff (fs_embed_project_formula left) (fs_embed_project_formula right)
  | _, _, .forallE body =>
      .forallE SetSort.set (fs_embed_project_formula body)
  | _, _, .existsE body =>
      .existsE SetSort.set (fs_embed_project_formula body)
/-- 嵌入后的项目变量项具有集合 sort。 -/
theorem fs_embed_project_term_well_sorted
    {depth : Nat} (term : FsProjectTerm depth) :
    TermWellSorted (fs_embed_project_term term) SetSort.set := by
  cases term with
  | bound entry =>
      exact TermWellSorted.bvar (σ := signature) SetSort.set entry.val
  | free id =>
      exact TermWellSorted.fvar (σ := signature) SetSort.set id
/-- 当前 raw scope 至少容纳项目深度时，嵌入项保持 scope 正确。 -/
theorem fs_embed_project_term_scoped
    {depth : Nat} (term : FsProjectTerm depth)
    {scope : Scope signature} (hDepth : depth ≤ scope SetSort.set) :
    TermScoped scope (fs_embed_project_term term) := by
  cases term with
  | bound entry =>
      exact TermScoped.bvar (Nat.lt_of_lt_of_le entry.isLt hDepth)
  | free id =>
      exact TermScoped.fvar (σ := signature) SetSort.set id
/-- 项目公式嵌入后满足 FormalSystem 的 sort/arity 边界。 -/
theorem fs_embed_project_formula_well_formed
    {availableStage depth : Nat} (formula : FsProjectFormula availableStage depth) :
    FormulaWellFormed (fs_embed_project_formula formula) := by
  induction formula with
  | falsum =>
      simpa only [fs_embed_project_formula] using (FormulaWellFormed.falsum (σ := signature))
  | truth =>
      simpa only [fs_embed_project_formula] using (FormulaWellFormed.truth (σ := signature))
  | mem left right =>
      have hMembership :
          FormulaWellFormed (membership_formula (fs_embed_project_term left) (fs_embed_project_term right)) :=
        FormulaWellFormed.rel (σ := signature) RelationSymbol.membership <|
          .cons (fs_embed_project_term_well_sorted left) <|
            .cons (fs_embed_project_term_well_sorted right) .nil
      simpa only [fs_embed_project_formula] using hMembership
  | atom symbol hStage arguments =>
      cases symbol with
      | extensionalEq =>
          have hEquality :
              FormulaWellFormed (Formula.equal (fs_embed_project_term (arguments 0)) (fs_embed_project_term (arguments 1))) :=
            .equal (fs_embed_project_term_well_sorted (arguments 0)) (fs_embed_project_term_well_sorted (arguments 1))
          simpa only [fs_embed_project_formula] using hEquality
      | subset =>
          have hSubset :
              FormulaWellFormed (subset_formula (fs_embed_project_term (arguments 0)) (fs_embed_project_term (arguments 1))) :=
            FormulaWellFormed.rel (σ := signature) RelationSymbol.subset <|
              .cons (fs_embed_project_term_well_sorted (arguments 0)) <|
              .cons (fs_embed_project_term_well_sorted (arguments 1))
                .nil
          simpa only [fs_embed_project_formula] using hSubset
  | neg formula ih =>
      simpa only [fs_embed_project_formula] using
        FormulaWellFormed.neg ih
  | conj left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaWellFormed.conj ihLeft ihRight
  | disj left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaWellFormed.disj ihLeft ihRight
  | imp left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaWellFormed.imp ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaWellFormed.iff ihLeft ihRight
  | forallE body ih =>
      simpa only [fs_embed_project_formula] using
        FormulaWellFormed.forallE SetSort.set ih
  | existsE body ih =>
      simpa only [fs_embed_project_formula] using
        FormulaWellFormed.existsE SetSort.set ih
/-- 当前 raw scope 至少容纳项目深度时，公式嵌入保持 scope 正确。 -/
theorem fs_embed_project_formula_scoped
    {availableStage depth : Nat} (formula : FsProjectFormula availableStage depth)
    {scope : Scope signature} (hDepth : depth ≤ scope SetSort.set) :
    FormulaScoped scope (fs_embed_project_formula formula) := by
  induction formula generalizing scope with
  | falsum =>
      simpa only [fs_embed_project_formula] using (FormulaScoped.falsum (ctx := scope))
  | truth =>
      simpa only [fs_embed_project_formula] using (FormulaScoped.truth (ctx := scope))
  | mem left right =>
      have hMembership :
          FormulaScoped scope (membership_formula (fs_embed_project_term left) (fs_embed_project_term right)) := by
        apply FormulaScoped.rel
        intro term hTerm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
        rcases hTerm with rfl | rfl
        · exact fs_embed_project_term_scoped left hDepth
        · exact fs_embed_project_term_scoped right hDepth
      simpa only [fs_embed_project_formula] using hMembership
  | atom symbol hStage arguments =>
      cases symbol with
      | extensionalEq =>
          have hEquality :
              FormulaScoped scope (Formula.equal (fs_embed_project_term (arguments 0)) (fs_embed_project_term (arguments 1))) :=
            .equal (fs_embed_project_term_scoped (arguments 0) hDepth) (fs_embed_project_term_scoped (arguments 1) hDepth)
          simpa only [fs_embed_project_formula] using hEquality
      | subset =>
          have hSubset :
              FormulaScoped scope (subset_formula (fs_embed_project_term (arguments 0)) (fs_embed_project_term (arguments 1))) := by
            apply FormulaScoped.rel
            intro term hTerm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
            rcases hTerm with rfl | rfl
            · exact fs_embed_project_term_scoped (arguments 0) hDepth
            · exact fs_embed_project_term_scoped (arguments 1) hDepth
          simpa only [fs_embed_project_formula] using hSubset
  | neg formula ih =>
      simpa only [fs_embed_project_formula] using
        FormulaScoped.neg (ih hDepth)
  | conj left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaScoped.conj (ihLeft hDepth) (ihRight hDepth)
  | disj left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaScoped.disj (ihLeft hDepth) (ihRight hDepth)
  | imp left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaScoped.imp (ihLeft hDepth) (ihRight hDepth)
  | iff left right ihLeft ihRight =>
      simpa only [fs_embed_project_formula] using
        FormulaScoped.iff (ihLeft hDepth) (ihRight hDepth)
  | forallE body ih =>
      have hBody :
          FormulaScoped (Scope.push scope SetSort.set) (fs_embed_project_formula body) := by
        apply ih
        simpa [Scope.push] using Nat.succ_le_succ hDepth
      simpa only [fs_embed_project_formula] using
        FormulaScoped.forallE SetSort.set hBody
  | existsE body ih =>
      have hBody :
          FormulaScoped (Scope.push scope SetSort.set) (fs_embed_project_formula body) := by
        apply ih
        simpa [Scope.push] using Nat.succ_le_succ hDepth
      simpa only [fs_embed_project_formula] using
        FormulaScoped.existsE SetSort.set hBody
/-- 自由闭合的项目项嵌入后仍没有自由变量。 -/
theorem fs_embed_project_term_free_support_nil
    {depth : Nat} (term : FsProjectTerm depth) (hClosed : term.freeSupport = []) :
    Term.freeSupport (fs_embed_project_term term) = [] := by
  cases term <;>
    simp_all [fs_embed_project_term, Term.freeSupport]
/-- 自由闭合的项目公式嵌入后仍没有自由变量。 -/
theorem fs_embed_project_formula_free_support_nil
    {availableStage depth : Nat} (formula : FsProjectFormula availableStage depth) (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed formula) :
    Formula.freeSupport (fs_embed_project_formula formula) = [] := by
  induction formula with
  | falsum =>
      simp [fs_embed_project_formula, Formula.freeSupport]
  | truth =>
      simp [fs_embed_project_formula, Formula.freeSupport]
  | mem left right =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_embed_project_formula, Formula.freeSupport,
        Term.freeSupportList,
        fs_embed_project_term_free_support_nil left hLeft,
        fs_embed_project_term_free_support_nil right hRight]
  | atom symbol hStage arguments =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,
        _root_.YesMetaZFC.SetTheory.Definitional.TermVector.FreeClosed] at hClosed
      cases symbol with
      | extensionalEq =>
          simp [fs_embed_project_formula, Formula.freeSupport,
            fs_embed_project_term_free_support_nil (arguments 0) (hClosed 0),
            fs_embed_project_term_free_support_nil (arguments 1) (hClosed 1)]
      | subset =>
          simp [fs_embed_project_formula, Formula.freeSupport,
            Term.freeSupportList,
            fs_embed_project_term_free_support_nil (arguments 0) (hClosed 0),
            fs_embed_project_term_free_support_nil (arguments 1) (hClosed 1)]
  | neg formula ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.freeSupport] using
        ih hClosed
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_embed_project_formula, Formula.freeSupport,
        ihLeft hLeft, ihRight hRight]
  | forallE body ih
  | existsE body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_embed_project_formula, Formula.freeSupport] using
        ih hClosed
/-- 项目句子嵌入为 FormalSystem 公式。 -/
def fs_embed_project_sentence (sentence : FsProjectSentence) : SetFormula :=
  fs_embed_project_formula sentence.formula
/-- 每个项目句子的嵌入都是 FormalSystem 的 admissible 闭句。 -/
theorem fs_embed_project_sentence_sentence (sentence : FsProjectSentence) :
    Formula.Sentence (fs_embed_project_sentence sentence) := by
  constructor
  · constructor
    · exact fs_embed_project_formula_well_formed sentence.formula
    · exact fs_embed_project_formula_scoped
        sentence.formula (by simp [Scope.empty])
  · exact fs_embed_project_formula_free_support_nil
      sentence.formula sentence.freeClosed
/-- 项目集合论理论沿句子嵌入取得的 FormalSystem 理论像。 -/
def fs_embed_project_theory (theory : FsProjectTheory) : SetTheory :=
  fun formula =>
    ∃ sentence,
      theory sentence ∧
        formula = fs_embed_project_sentence sentence
/-- 嵌入后的任意项目理论只含 admissible 闭句。 -/
@[derive_close_sentence]
theorem fs_embed_project_theory_sentence
    {theory : FsProjectTheory} {formula : SetFormula} (hFormula : fs_embed_project_theory theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with ⟨sentence, _, rfl⟩
  exact fs_embed_project_sentence_sentence sentence
/-! ## FormalSystem 通用内部理论构造器 -/
/--
 quotation、Gödel 配对编码与 Hilbert 逻辑规则编码的公共支持理论。
这一层与具体基础理论无关，后续算术理论、集合论理论或更强扩张都消费同一个入口。
-/
def fs_internal_encoding_theory : SetTheory :=
  Theory.union
    (Theory.union GodelQuotation.code_naming_theory
      godel_pairing_theory)
    logical_rule_encoding_theory
/-- 公共编码支持理论中的每条公理都是闭句。 -/
@[derive_close_sentence]
theorem fs_internal_encoding_theory_sentence
    {formula : SetFormula} (hFormula : fs_internal_encoding_theory formula) :
    Formula.Sentence formula := by
   rcases hFormula with hEncoding | hLogicalRule
   · rcases hEncoding with hCodeNaming | hPairing
     · exact GodelQuotation.code_naming_theory_sentence hCodeNaming
     · exact godel_pairing_theory_sentence hPairing
   · exact logical_rule_encoding_theory_sentence hLogicalRule
/-- 公共编码支持理论的全部字面公理都满足 admissible 边界。 -/
theorem fs_internal_encoding_theory_admissible :
    Theory.Admissible fs_internal_encoding_theory := by
  intro formula hFormula
  exact (fs_internal_encoding_theory_sentence hFormula).1
/--
公共 quotation 与 Hilbert 逻辑规则编码支持层是有限公理化的。
标准有限序列的良基性已经收缩为单条成员反自反公理；其余各层均由有限次
`insert`/`union` 组成，因此这里用结构自动化一次性关闭完整支持层。
-/
theorem fs_internal_encoding_theory_finitely_axiomatized :
    Theory.FinitelyAxiomatized
      fs_internal_encoding_theory := by
  unfold fs_internal_encoding_theory
  apply Theory.finitely_axiomatized_union
  · apply Theory.finitely_axiomatized_union
    · unfold GodelQuotation.code_naming_theory
      repeat
        first
        | apply Theory.finitely_axiomatized_insert
        | apply Theory.finitely_axiomatized_union
        | exact Theory.finitely_axiomatized_singleton _
        | exact Theory.finitely_axiomatized_empty
        | unfold GodelQuotation.godel_quotation_theory
        | unfold GodelQuotation.standard_sequence_semantics_theory
        | unfold membership_irreflexive_theory
        | unfold finite_sequence_flatten_theory
        | unfold finite_sequence_space_theory
        | unfold infinity_theory
        | unfold empty_set_symbol_theory
        | unfold successor_operator_theory
        | unfold binary_union_operator_theory
        | unfold singleton_operator_theory
        | unfold ordered_pair_operator_theory
        | unfold function_application_theory
        | unfold natural_exponentiation_theory
        | unfold substitution_variable_theory
        | unfold formula_code_theory
        | unfold formula_constructor_theory
        | unfold symbol_code_operator_theory
        | unfold formal_language_encoding_theory
    · unfold godel_pairing_theory
      repeat
        first
        | apply Theory.finitely_axiomatized_insert
        | apply Theory.finitely_axiomatized_union
        | exact Theory.finitely_axiomatized_singleton _
        | exact Theory.finitely_axiomatized_empty
        | unfold omega_pair_order_theory
        | unfold natural_difference_theory
        | unfold omega_recursive_sequence_theory
        | unfold recursive_sequence_space_theory
        | unfold finite_sequence_space_theory
        | unfold cardinality_classification_theory
        | unfold countably_infinite_predicate_theory
        | unfold uncountable_predicate_theory
        | unfold countable_predicate_theory
        | unfold infinite_predicate_theory
        | unfold natural_exponentiation_theory
        | unfold natural_multiplication_theory
        | unfold natural_addition_theory
        | unfold natural_set_theory
        | unfold natural_subset_type_theory
        | unfold natural_order_type_theory
        | unfold bounded_subset_theory
        | unfold unbounded_subset_theory
        | unfold infinity_theory
        | unfold empty_set_theory
        | unfold extensionality_theory
  · unfold logical_rule_encoding_theory
    repeat
      first
      | apply Theory.finitely_axiomatized_insert
      | apply Theory.finitely_axiomatized_union
      | exact Theory.finitely_axiomatized_singleton _
      | exact Theory.finitely_axiomatized_empty
      | unfold logical_axiom_code_theory
      | unfold equality_axiom_schema_theory
      | unfold quantifier_axiom_schema_theory
      | unfold propositional_axiom_schema_theory
      | unfold substitutability_theory
      | unfold expression_encoding_theory
      | unfold occurrence_theory
      | unfold substitution_variable_theory
      | unfold formula_code_theory
      | unfold formula_constructor_theory
      | unfold symbol_code_operator_theory
      | unfold formal_language_encoding_theory
/--
任意 FormalSystem 基础理论与公共编码支持层的未归约联合。
编码理论置于左分支，保证 quotation 承载证明只依赖标准联合消去。
-/
def fs_internal_raw_theory (base : SetTheory) : SetTheory :=
  Theory.union fs_internal_encoding_theory base
/-- 通用内部理论：对完整 raw 联合理论逐公式执行 Hilbert 归约。 -/
def fs_internal_theory (base : SetTheory) : SetTheory :=
  Theory.hilbertize SetSort.set (fs_internal_raw_theory base)
/-- 通用内部理论对再次 Hilbert 归约封闭。 -/
theorem fs_internal_theory_hilbert_closed (base : SetTheory) :
    ∀ formula,
      Theory.hilbertize SetSort.set (fs_internal_theory base) formula →
        fs_internal_theory base formula := by
  simpa [fs_internal_theory] using (Theory.hilbertize_idempotent_subset (anchorSort := SetSort.set) (theory := fs_internal_raw_theory base))
/-- 通用 raw 内部理论中的每条公理都是闭句。 -/
@[derive_close_sentence]
theorem fs_internal_raw_theory_sentence
    {base : SetTheory} (hBaseSentence :
      ∀ formula, base formula → Formula.Sentence formula)
    {formula : SetFormula} (hFormula : fs_internal_raw_theory base formula) :
    Formula.Sentence formula := by
  rcases hFormula with hEncoding | hBase
  · exact fs_internal_encoding_theory_sentence hEncoding
  · exact hBaseSentence formula hBase
/-- Hilbert 归约后的通用内部理论仍只含闭句。 -/
@[derive_close_sentence]
theorem fs_internal_theory_sentence
    {base : SetTheory} (hBaseSentence :
      ∀ formula, base formula → Formula.Sentence formula)
    {formula : SetFormula} (hFormula : fs_internal_theory base formula) :
    Formula.Sentence formula := by
  rcases hFormula with ⟨source, hSource, rfl⟩
  have hSourceSentence :=
    fs_internal_raw_theory_sentence hBaseSentence hSource
  constructor
  · exact
      ⟨GodelQuotation.Numbered.hilbertize_well_formed
          SetSort.set hSourceSentence.1.1,
        GodelQuotation.Numbered.hilbertize_scoped
          SetSort.set hSourceSentence.1.2⟩
  · rw [List.eq_nil_iff_forall_not_mem]
    intro freeVariable hMember
    have hSourceMember := (Formula.mem_freeSupport_hilbertize_iff
        SetSort.set freeVariable source).mp hMember
    rw [hSourceSentence.2] at hSourceMember
    exact List.not_mem_nil hSourceMember
/-- 每个通用内部理论自动承载 quotation 编码理论。 -/
theorem fs_internal_theory_extends_code_naming (base : SetTheory) :
    GodelQuotation.fs_extends_code_naming (fs_internal_theory base) := by
  apply GodelQuotation.fs_extends_code_naming_of_subset
  intro formula hFormula
  rcases hFormula with ⟨source, hSource, rfl⟩
  exact Theory.hilbertize_mem (anchorSort := SetSort.set) (show fs_internal_raw_theory base source from
      Or.inl (Or.inl (Or.inl hSource)))
/--
通用内部理论在 Hilbert 意义下扩张其基础理论的 Hilbert 归约像。
这是后续把基础集合论定理搬入内部元数学理论的统一入口。
-/
theorem fs_internal_theory_extends_base (base : SetTheory) :
    Theory.hilbert_extends (fs_internal_theory base) (Theory.hilbertize SetSort.set base) := by
  apply Theory.hilbert_extends_of_subset
  intro formula hFormula
  rcases hFormula with ⟨source, hSource, rfl⟩
  exact Theory.hilbertize_mem (anchorSort := SetSort.set) (show fs_internal_raw_theory base source from
      Or.inr hSource)
/--
通用内部理论上的标准对角引理。
基础理论实例只需给出公理闭句条件；quotation 编码承载由构造器自动消去。
-/
theorem fs_internal_diagonal_lemma (base : SetTheory) (hBaseSentence :
      ∀ formula, base formula → Formula.Sentence formula)
    {codeId : FreeVarId} {body : SetFormula} (hBodyAdmissible : Formula.Admissible body) (hBodyOnlyCodeVariable :
      GodelQuotation.fs_only_code_variable_formula codeId body) :
    ∃ fixedPoint : SetFormula, ∃ fixedPointCode : SetTerm,
      Formula.Sentence fixedPoint ∧
      GodelQuotation.Numbered.quote? fixedPoint =
        some fixedPointCode ∧
      HilbertDerives (fs_internal_theory base) (Formula.hilbert_iff fixedPoint (Formula.substituteFree SetSort.set codeId
            fixedPointCode (GodelQuotation.fs_diagonal_target body))) :=
  GodelQuotation.fs_diagonal_lemma (fs_internal_theory_extends_code_naming base)
    hBodyAdmissible hBodyOnlyCodeVariable (fun _ hFormula =>
      fs_internal_theory_sentence
        hBaseSentence hFormula)
/-! ## Project 集合论适配层 -/
/--
Project 定义原子的 FormalSystem 解释理论。
外延等同直接进入核心等词；子集进入扩展关系符号，因此显式携带子集定义公理及其
所依赖的外延公理。
-/
def fs_project_definition_theory : SetTheory :=
  subset_theory
/-- Project 定义原子的解释理论只含闭句。 -/
@[derive_close_sentence]
theorem fs_project_definition_theory_sentence
    {formula : SetFormula} (hFormula : fs_project_definition_theory formula) :
    Formula.Sentence formula :=
  subset_theory_sentence hFormula
/-- Project subset 定义适配层是有限公理化的。 -/
theorem fs_project_definition_theory_finitely_axiomatized :
    Theory.FinitelyAxiomatized
      fs_project_definition_theory := by
  repeat
    first
    | apply Theory.finitely_axiomatized_union
    | apply Theory.finitely_axiomatized_insert
    | exact Theory.finitely_axiomatized_singleton _
    | exact Theory.finitely_axiomatized_empty
/-- Project subset 定义适配层的全部公理都满足 admissible 边界。 -/
theorem fs_project_definition_theory_admissible :
    Theory.Admissible fs_project_definition_theory := by
  intro formula hFormula
  exact (fs_project_definition_theory_sentence hFormula).1
/-- Project 基础理论的公式像连同定义原子解释。 -/
def fs_project_base_theory (base : FsProjectTheory) : SetTheory :=
  Theory.union fs_project_definition_theory (fs_embed_project_theory base)
/-- Project 基础理论适配后仍只含闭句。 -/
@[derive_close_sentence]
theorem fs_project_base_theory_sentence
    {base : FsProjectTheory} {formula : SetFormula} (hFormula : fs_project_base_theory base formula) :
    Formula.Sentence formula := by
  rcases hFormula with hDefinition | hBase
  · exact fs_project_definition_theory_sentence hDefinition
  · exact fs_embed_project_theory_sentence hBase
/-- Project 基础理论与全部内部编码定义尚未 Hilbert 归约时的联合理论。 -/
def fs_internal_project_raw_theory (base : FsProjectTheory) : SetTheory :=
  fs_internal_raw_theory (fs_project_base_theory base)
/-- Project 基础理论在 FormalSystem 扩展签名上的内部 Hilbert 理论。 -/
def fs_internal_project_theory (base : FsProjectTheory) : SetTheory :=
  fs_internal_theory (fs_project_base_theory base)
/-- Project 内部理论继承通用构造器的 Hilbert 归约封闭性。 -/
theorem fs_internal_project_theory_hilbert_closed (base : FsProjectTheory) :
    ∀ formula,
      Theory.hilbertize SetSort.set (fs_internal_project_theory base) formula →
        fs_internal_project_theory base formula := by
  simpa [fs_internal_project_theory] using
    fs_internal_theory_hilbert_closed (fs_project_base_theory base)
/-- Project 基础理论的 raw 内部化只含闭句。 -/
@[derive_close_sentence]
theorem fs_internal_project_raw_theory_sentence
    {base : FsProjectTheory} {formula : SetFormula} (hFormula : fs_internal_project_raw_theory base formula) :
    Formula.Sentence formula :=
  fs_internal_raw_theory_sentence (fun _ hBase => fs_project_base_theory_sentence hBase)
    hFormula
/-- Project 基础理论的内部 Hilbert 化只含闭句。 -/
@[derive_close_sentence]
theorem fs_internal_project_theory_sentence
    {base : FsProjectTheory} {formula : SetFormula} (hFormula : fs_internal_project_theory base formula) :
    Formula.Sentence formula :=
  fs_internal_theory_sentence (fun _ hBase => fs_project_base_theory_sentence hBase)
    hFormula
/-- 每个 Project 内部理论自动承载 quotation 编码理论。 -/
theorem fs_internal_project_theory_extends_code_naming (base : FsProjectTheory) :
    GodelQuotation.fs_extends_code_naming (fs_internal_project_theory base) :=
  fs_internal_theory_extends_code_naming (fs_project_base_theory base)
/-- Project 基础理论上的标准内部 Hilbert 对角引理。 -/
theorem fs_internal_project_diagonal_lemma (base : FsProjectTheory)
    {codeId : FreeVarId} {body : SetFormula} (hBodyAdmissible : Formula.Admissible body) (hBodyOnlyCodeVariable :
      GodelQuotation.fs_only_code_variable_formula codeId body) :
    ∃ fixedPoint : SetFormula, ∃ fixedPointCode : SetTerm,
      Formula.Sentence fixedPoint ∧
      GodelQuotation.Numbered.quote? fixedPoint =
        some fixedPointCode ∧
      HilbertDerives (fs_internal_project_theory base) (Formula.hilbert_iff fixedPoint (Formula.substituteFree SetSort.set codeId
            fixedPointCode (GodelQuotation.fs_diagonal_target body))) :=
  fs_internal_diagonal_lemma (fs_project_base_theory base) (fun _ hBase => fs_project_base_theory_sentence hBase)
    hBodyAdmissible hBodyOnlyCodeVariable
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
