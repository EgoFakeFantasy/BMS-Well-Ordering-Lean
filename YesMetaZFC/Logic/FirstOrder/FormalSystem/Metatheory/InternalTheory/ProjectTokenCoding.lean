import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TokenReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofCode
import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Syntax

/-!
# Project 公式的规范 token 编解码

ZFC schema 证书直接携带 Hilbert 核公式的规范 token 序列码。本模块给出该数据层的
唯一正反接口：

* Project 公式先在 Project 语法内归约到 `¬/→/∀/原子` Hilbert 核；
* 自由闭合公式生成规范 binder 命名的原始 token 树；
* token parser 的结果可构造地解回自由闭合 Project Hilbert 核公式；
* 编码后再解码精确恢复 Project Hilbert 核归约。

因此后续对象 verifier 与外部枚举器不再同时维护一份 Project 原始构造码和一份
FormalSystem quotation 码，也不需要额外的双编码一致性假设。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofCode

open _root_.YesMetaZFC.SetTheory
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project
open GodelQuotation

set_option autoImplicit false

/-! ## Project 内部 Hilbert 归约 -/

/-- Project 语法中的闭真 Hilbert 核。 -/
def fs_project_hilbert_truth {depth : Nat} :
    Project.Formula 1 depth :=
  .forallE <|
    Project.Formula.extensionalEq
      (.bound 0) (.bound 0)

/-- Project 语法中的闭假 Hilbert 核。 -/
def fs_project_hilbert_falsum {depth : Nat} :
    Project.Formula 1 depth :=
  .neg fs_project_hilbert_truth

/-- Project 语法中的 Hilbert 合取。 -/
def fs_project_hilbert_conj
    {depth : Nat}
    (left right : Project.Formula 1 depth) :
    Project.Formula 1 depth :=
  .neg (.imp left (.neg right))

/-- Project 语法中的 Hilbert 双条件。 -/
def fs_project_hilbert_iff
    {depth : Nat}
    (left right : Project.Formula 1 depth) :
    Project.Formula 1 depth :=
  fs_project_hilbert_conj
    (.imp left right) (.imp right left)

/-- 把 Project 公式归约到 `¬/→/∀/原子` Hilbert 核。 -/
def fs_project_hilbertize :
    {depth : Nat} →
      Project.Formula 1 depth →
        Project.Formula 1 depth
  | _, .falsum =>
      fs_project_hilbert_falsum
  | _, .truth =>
      fs_project_hilbert_truth
  | _, .mem left right =>
      .mem left right
  | _, .atom symbol hStage arguments =>
      .atom symbol hStage arguments
  | _, .neg body =>
      .neg (fs_project_hilbertize body)
  | _, .conj left right =>
      fs_project_hilbert_conj
        (fs_project_hilbertize left)
        (fs_project_hilbertize right)
  | _, .disj left right =>
      .imp (.neg (fs_project_hilbertize left))
        (fs_project_hilbertize right)
  | _, .imp left right =>
      .imp (fs_project_hilbertize left)
        (fs_project_hilbertize right)
  | _, .iff left right =>
      fs_project_hilbert_iff
        (fs_project_hilbertize left)
        (fs_project_hilbertize right)
  | _, .forallE body =>
      .forallE (fs_project_hilbertize body)
  | _, .existsE body =>
      .neg (.forallE (.neg
        (fs_project_hilbertize body)))

/-- Project Hilbert 归约与 bound 变量替换交换。 -/
theorem fs_project_hilbertize_bind
    {sourceDepth targetDepth : Nat}
    (substitution :
      Fin sourceDepth → Project.Term targetDepth)
    (formula : Project.Formula 1 sourceDepth) :
    fs_project_hilbertize
        (formula.bind substitution) =
      (fs_project_hilbertize formula).bind
        substitution := by
  induction formula generalizing targetDepth with
  | falsum =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_falsum,
        fs_project_hilbert_truth,
        Project.Formula.extensionalEq,
        Project.Formula.pairArguments,
        Definitional.Formula.bind,
        Definitional.TermVector.bind,
        Definitional.Term.bind,
        Definitional.Term.liftSubstitution,
        Definitional.Term.newest,
        Definitional.Term.weaken,
        Definitional.Term.rename]
  | truth =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_truth,
        Project.Formula.extensionalEq,
        Project.Formula.pairArguments,
        Definitional.Formula.bind,
        Definitional.TermVector.bind,
        Definitional.Term.bind,
        Definitional.Term.liftSubstitution,
        Definitional.Term.newest,
        Definitional.Term.weaken,
        Definitional.Term.rename]
  | mem left right =>
      rfl
  | atom symbol hStage arguments =>
      rfl
  | neg body ih =>
      simp [fs_project_hilbertize,
        Definitional.Formula.bind, ih]
  | conj left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_conj,
        Definitional.Formula.bind,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        Definitional.Formula.bind,
        ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        Definitional.Formula.bind,
        ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_iff,
        fs_project_hilbert_conj,
        Definitional.Formula.bind,
        ihLeft, ihRight]
  | forallE body ih =>
      simp [fs_project_hilbertize,
        Definitional.Formula.bind, ih]
  | existsE body ih =>
      simp [fs_project_hilbertize,
        Definitional.Formula.bind, ih]

/-- Project Hilbert 归约与 bound 变量重命名交换。 -/
theorem fs_project_hilbertize_rename
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (formula : Project.Formula 1 sourceDepth) :
    fs_project_hilbertize
        (formula.rename indexMap) =
      (fs_project_hilbertize formula).rename
        indexMap := by
  exact fs_project_hilbertize_bind
    (.bound ∘ indexMap) formula

/-- Project Hilbert 归约已经处于正规形时再次归约不再改变公式。 -/
@[simp]
theorem fs_project_hilbertize_idempotent
    {depth : Nat}
    (formula : Project.Formula 1 depth) :
    fs_project_hilbertize
        (fs_project_hilbertize formula) =
      fs_project_hilbertize formula := by
  induction formula with
  | falsum =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_falsum,
        fs_project_hilbert_truth,
        Project.Formula.extensionalEq]
  | truth =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_truth,
        Project.Formula.extensionalEq]
  | mem left right =>
      rfl
  | atom symbol hStage arguments =>
      rfl
  | neg body ih =>
      simp [fs_project_hilbertize, ih]
  | conj left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_conj,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_iff,
        fs_project_hilbert_conj,
        ihLeft, ihRight]
  | forallE body ih =>
      simp [fs_project_hilbertize, ih]
  | existsE body ih =>
      simp [fs_project_hilbertize, ih]

/- 已归约体经过 bound 重命名后，其再次归约与原体重命名后的归约相同。 -/
theorem fs_project_hilbertize_rename_idempotent
    {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth)
    (formula : Project.Formula 1 sourceDepth) :
    fs_project_hilbertize
        ((fs_project_hilbertize formula).rename indexMap) =
      fs_project_hilbertize (formula.rename indexMap) := by
  rw [fs_project_hilbertize_rename,
    fs_project_hilbertize_idempotent,
    fs_project_hilbertize_rename]

/-- Project Hilbert 归约与全称闭合交换。 -/
theorem fs_project_hilbertize_forallClosure
    {depth : Nat}
    (formula : Project.Formula 1 depth) :
    fs_project_hilbertize
        (Project.Formula.forallClosure depth formula) =
      Project.Formula.forallClosure depth
        (fs_project_hilbertize formula) := by
  induction depth with
  | zero =>
      rfl
  | succ depth ih =>
      simpa [Project.Formula.forallClosure,
        fs_project_hilbertize] using
        ih (.forallE formula)

/-- Project Hilbert 归约与 FormalSystem Hilbert 归约逐构造一致。 -/
theorem fs_embed_project_hilbertize
    {depth : Nat}
    (formula : Project.Formula 1 depth) :
    fs_embed_project_formula
        (fs_project_hilbertize formula) =
      Formula.hilbertize Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_formula formula) := by
  induction formula with
  | falsum =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_falsum,
        fs_project_hilbert_truth,
        Project.Formula.extensionalEq,
        fs_embed_project_formula,
        fs_embed_project_term,
        Formula.hilbertize,
        Formula.hilbert_falsum,
        Formula.hilbert_truth]
  | truth =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_truth,
        Project.Formula.extensionalEq,
        fs_embed_project_formula,
        fs_embed_project_term,
        Formula.hilbertize,
        Formula.hilbert_truth]
  | mem left right =>
      simp [fs_project_hilbertize,
        fs_embed_project_formula,
        Formula.hilbertize]
  | atom symbol hStage arguments =>
      cases symbol <;>
        simp [fs_project_hilbertize,
          fs_embed_project_formula,
          Formula.hilbertize]
  | neg body ih =>
      simp [fs_project_hilbertize,
        fs_embed_project_formula, Formula.hilbertize,
        ih]
  | conj left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_conj,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_conj,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_embed_project_formula, Formula.hilbertize,
        ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_embed_project_formula, Formula.hilbertize,
        ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [fs_project_hilbertize,
        fs_project_hilbert_iff,
        fs_project_hilbert_conj,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_iff, Formula.hilbert_conj,
        ihLeft, ihRight]
  | forallE body ih =>
      simp [fs_project_hilbertize,
        fs_embed_project_formula, Formula.hilbertize,
        ih]
  | existsE body ih =>
      simp [fs_project_hilbertize,
        fs_embed_project_formula, Formula.hilbertize,
        ih]

/-- Project Hilbert 归约保持自由闭合性。 -/
theorem fs_project_hilbertize_freeClosed
    {depth : Nat}
    {formula : Project.Formula 1 depth}
    (hClosed : formula.FreeClosed) :
    (fs_project_hilbertize formula).FreeClosed := by
  induction formula with
  | falsum =>
      simpa only [fs_project_hilbertize,
        fs_project_hilbert_falsum,
        fs_project_hilbert_truth,
        Definitional.Formula.FreeClosed,
        Project.Formula.extensionalEq] using
        Project.Formula.pairArguments_freeClosed
          (.bound 0) (.bound 0) rfl rfl
  | truth =>
      simpa only [fs_project_hilbertize,
        fs_project_hilbert_truth,
        Definitional.Formula.FreeClosed,
        Project.Formula.extensionalEq] using
        Project.Formula.pairArguments_freeClosed
          (.bound 0) (.bound 0) rfl rfl
  | mem left right =>
      simpa [fs_project_hilbertize] using hClosed
  | atom symbol hStage arguments =>
      simpa [fs_project_hilbertize] using hClosed
  | neg body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_project_hilbertize,
        Definitional.Formula.FreeClosed] using
        ih hClosed
  | conj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbertize,
        fs_project_hilbert_conj,
        Definitional.Formula.FreeClosed,
        ihLeft hLeft, ihRight hRight]
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbertize,
        fs_project_hilbert_iff,
        fs_project_hilbert_conj,
        Definitional.Formula.FreeClosed,
        ihLeft hLeft, ihRight hRight]
  | forallE body ih
  | existsE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [fs_project_hilbertize,
        Definitional.Formula.FreeClosed] using
        ih hClosed

/-- 一元 schema 逐体归约到 Project Hilbert 核。 -/
def fs_project_unary_schema_hilbertize
    {parameterCount : Nat}
    (schema : Project.UnarySchema parameterCount) :
    Project.UnarySchema parameterCount where
  body := fs_project_hilbertize schema.body
  freeClosed :=
    fs_project_hilbertize_freeClosed
      schema.freeClosed

/-- 二元 schema 逐体归约到 Project Hilbert 核。 -/
def fs_project_binary_schema_hilbertize
    {parameterCount : Nat}
    (schema : Project.BinarySchema parameterCount) :
    Project.BinarySchema parameterCount where
  body := fs_project_hilbertize schema.body
  freeClosed :=
    fs_project_hilbertize_freeClosed
      schema.freeClosed

/-! ## 规范 token 树 -/

/-- Project bound 变量在当前深度的规范 quotation token。 -/
def fs_project_bound_token :
    {depth : Nat} → Fin depth → Nat
  | depth + 1, entry =>
      Fin.cases
        (GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth))
        (fun previous =>
          fs_project_bound_token previous)
        entry

/-- Project 项忘掉类型后所得的原始 token 树。 -/
def fs_project_term_token_tree :
    {depth : Nat} →
      Project.Term depth →
        GodelQuotation.RawTermTokenTree
  | _, .bound entry =>
      .atom (fs_project_bound_token entry)
  | _, .free id =>
      .atom <|
        GodelQuotation.Numbered.variable_token
          (GodelQuotation.free_name id)

@[simp]
theorem fs_project_bound_token_odd
    {depth : Nat}
    (entry : Fin depth) :
    fs_project_bound_token entry % 2 = 1 := by
  induction depth with
  | zero =>
      exact Fin.elim0 entry
  | succ depth ih =>
      refine Fin.cases ?_ (fun previous => ?_) entry
      · simp [fs_project_bound_token,
          GodelQuotation.variable_token_odd]
      · simpa [fs_project_bound_token] using ih previous

/-- Hilbert 化 Project 公式的规范原始 token 树。 -/
def fs_project_hilbert_token_tree :
    {depth : Nat} →
      Project.Formula 1 depth →
        GodelQuotation.RawHilbertTokenTree
  | depth, .falsum =>
      .negation <|
        .universal
          (GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth))
          (.equality
            (.atom <| GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name depth))
            (.atom <| GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name depth)))
  | depth, .truth =>
      .universal
        (GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth))
        (.equality
          (.atom <| GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth))
          (.atom <| GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth)))
  | _, .mem left right =>
      .membership
        (fs_project_term_token_tree left)
        (fs_project_term_token_tree right)
  | _, .atom .extensionalEq _ arguments =>
      .equality
        (fs_project_term_token_tree (arguments 0))
        (fs_project_term_token_tree (arguments 1))
  | _, .atom .subset _ arguments =>
      .predicate
        (GodelQuotation.Numbered.predicate_token
          1 Nonlogical.BasicSetTheory.RelationSymbol.subset.ctorIdx)
        [fs_project_term_token_tree (arguments 0),
          fs_project_term_token_tree (arguments 1)]
  | _, .neg body =>
      .negation
        (fs_project_hilbert_token_tree body)
  | _, .conj left right =>
      .negation <|
        .implication
          (fs_project_hilbert_token_tree left)
          (.negation
            (fs_project_hilbert_token_tree right))
  | _, .disj left right =>
      .implication
        (.negation
          (fs_project_hilbert_token_tree left))
        (fs_project_hilbert_token_tree right)
  | _, .imp left right =>
      .implication
        (fs_project_hilbert_token_tree left)
        (fs_project_hilbert_token_tree right)
  | _, .iff left right =>
      .negation <|
        .implication
          (.implication
            (fs_project_hilbert_token_tree left)
            (fs_project_hilbert_token_tree right))
          (.negation <|
            .implication
              (fs_project_hilbert_token_tree right)
              (fs_project_hilbert_token_tree left))
  | depth, .forallE body =>
      .universal
        (GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth))
        (fs_project_hilbert_token_tree body)
  | depth, .existsE body =>
      .negation <|
        .universal
          (GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth))
          (.negation
            (fs_project_hilbert_token_tree body))

/-- Project 项 token 树的所有首部均为奇数。 -/
theorem fs_project_term_token_tree_headsOdd
    {depth : Nat}
    (term : Project.Term depth) :
    (fs_project_term_token_tree term).HeadsOdd := by
  cases term with
  | bound entry =>
      simp [fs_project_term_token_tree,
        GodelQuotation.RawTermTokenTree.HeadsOdd,
        fs_project_bound_token_odd]
  | free id =>
      simp [fs_project_term_token_tree,
        GodelQuotation.RawTermTokenTree.HeadsOdd,
        GodelQuotation.variable_token_odd]

/-- Project Hilbert token 树满足通用 parser 的词法分离条件。 -/
theorem fs_project_hilbert_token_tree_lexicallySeparated
    {depth : Nat}
    (formula : Project.Formula 1 depth) :
    (fs_project_hilbert_token_tree formula).LexicallySeparated := by
  induction formula with
  | falsum =>
      simp [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated,
        GodelQuotation.RawTermTokenTree.HeadsOdd,
        GodelQuotation.variable_token_odd]
  | truth =>
      simp [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated,
        GodelQuotation.RawTermTokenTree.HeadsOdd,
        GodelQuotation.variable_token_odd]
  | mem left right =>
      exact ⟨fs_project_term_token_tree_headsOdd left,
        fs_project_term_token_tree_headsOdd right⟩
  | atom symbol hStage arguments =>
      cases symbol with
      | extensionalEq =>
          exact
            ⟨fs_project_term_token_tree_headsOdd
                (arguments 0),
              fs_project_term_token_tree_headsOdd
                (arguments 1)⟩
      | subset =>
          simp [fs_project_hilbert_token_tree,
            GodelQuotation.RawHilbertTokenTree.LexicallySeparated,
            GodelQuotation.RawTermTokenTree.ListHeadsOdd,
            GodelQuotation.predicate_token_odd,
            fs_project_term_token_tree_headsOdd]
  | neg body ih =>
      simpa [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated]
        using ih
  | conj left right ihLeft ihRight =>
      simpa [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated]
        using And.intro ihLeft ihRight
  | disj left right ihLeft ihRight =>
      simpa [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated]
        using And.intro ihLeft ihRight
  | imp left right ihLeft ihRight =>
      simpa [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated]
        using And.intro ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated,
        ihLeft, ihRight]
  | forallE body ih
  | existsE body ih =>
      simpa [fs_project_hilbert_token_tree,
        GodelQuotation.RawHilbertTokenTree.LexicallySeparated]
        using ih

/-- Project bound token 与规范 binder 环境中的同位置名字一致。 -/
theorem fs_project_bound_token_eq
    {depth : Nat}
    (entry : Fin depth) :
    fs_project_bound_token entry =
      GodelQuotation.Numbered.variable_token
        (GodelQuotation.bound_name
          (depth - entry.val - 1)) := by
  induction depth with
  | zero =>
      exact Fin.elim0 entry
  | succ depth ih =>
      refine Fin.cases ?_ (fun previous => ?_) entry
      · simp [fs_project_bound_token]
      · have hArithmetic :
            depth + 1 - (previous.val + 1) - 1 =
              depth - previous.val - 1 := by
          omega
        simpa [fs_project_bound_token,
          hArithmetic] using ih previous

/-- Project 项树的 token 串就是其嵌入项的规范 token quotation。 -/
theorem fs_project_term_token_tree_tokens
    {depth : Nat}
    (term : Project.Term depth)
    (hClosed : term.freeSupport = []) :
    GodelQuotation.Numbered.quote_term_tokens_with?
        GodelQuotation.free_name
        (GodelQuotation.canonical_bound_names depth)
        (fs_embed_project_term term) =
      some (fs_project_term_token_tree term).tokens := by
  cases term with
  | bound entry =>
      have hName :=
        GodelQuotation.canonical_bound_names_getElem?
          depth entry.val entry.isLt
      have hNameValue :
          (GodelQuotation.canonical_bound_names depth)[entry.val] =
            GodelQuotation.bound_name
              (depth - entry.val - 1) := by
        have hIndex :
            entry.val <
              (GodelQuotation.canonical_bound_names depth).length := by
          rw [GodelQuotation.canonical_bound_names_length]
          exact entry.isLt
        have hCanonical := hName
        rw [List.getElem?_eq_getElem hIndex] at hCanonical
        exact Option.some.inj
          hCanonical
      simp [fs_embed_project_term,
        fs_project_term_token_tree,
        fs_project_bound_token_eq,
        GodelQuotation.RawTermTokenTree.tokens,
        hNameValue]
  | free id =>
      simp at hClosed

/-- Project Hilbert token 树的序列化就是嵌入公式 Hilbert 化后的规范 token quotation。 -/
theorem fs_project_hilbert_token_tree_tokens
    {depth : Nat}
    (formula : Project.Formula 1 depth)
    (hClosed : formula.FreeClosed) :
    GodelQuotation.Numbered.quote_hilbert_tokens_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name
        (GodelQuotation.canonical_bound_names depth)
        depth
        (Formula.hilbertize Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_formula formula)) =
      some (fs_project_hilbert_token_tree formula).tokens := by
  induction formula with
  | falsum =>
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_falsum, Formula.hilbert_truth,
        GodelQuotation.Numbered.negation_tokens,
         GodelQuotation.Numbered.universal_tokens,
         GodelQuotation.Numbered.equality_tokens,
         GodelQuotation.RawHilbertTokenTree.tokens,
         GodelQuotation.RawTermTokenTree.tokens]
  | truth =>
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_truth,
         GodelQuotation.Numbered.universal_tokens,
         GodelQuotation.Numbered.equality_tokens,
         GodelQuotation.RawHilbertTokenTree.tokens,
         GodelQuotation.RawTermTokenTree.tokens]
  | mem left right =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.membership_tokens,
        fs_project_term_token_tree_tokens left hLeft,
        fs_project_term_token_tree_tokens right hRight]
  | atom symbol hStage arguments =>
      simp only [Definitional.Formula.FreeClosed,
        Definitional.TermVector.FreeClosed] at hClosed
      cases symbol with
      | extensionalEq =>
          simp [fs_project_hilbert_token_tree,
            fs_embed_project_formula, Formula.hilbertize,
            GodelQuotation.RawHilbertTokenTree.tokens,
            GodelQuotation.Numbered.equality_tokens,
            fs_project_term_token_tree_tokens
              (arguments 0) (hClosed 0),
            fs_project_term_token_tree_tokens
              (arguments 1) (hClosed 1)]
      | subset =>
          simp [fs_project_hilbert_token_tree,
            fs_embed_project_formula, Formula.hilbertize,
            GodelQuotation.Numbered.quote_relation_tokens_with?,
            GodelQuotation.fs_relation_kind_eq_predicate,
            GodelQuotation.RawHilbertTokenTree.tokens,
            GodelQuotation.RawTermTokenTree.list_tokens,
            GodelQuotation.Numbered.predicate_application_tokens,
            fs_project_term_token_tree_tokens
              (arguments 0) (hClosed 0),
            fs_project_term_token_tree_tokens
              (arguments 1) (hClosed 1)]
  | neg body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.negation_tokens,
        ih hClosed]
  | conj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_conj,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.negation_tokens,
        GodelQuotation.Numbered.implication_tokens,
        ihLeft hLeft, ihRight hRight]
  | disj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.negation_tokens,
        GodelQuotation.Numbered.implication_tokens,
        ihLeft hLeft, ihRight hRight]
  | imp left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.implication_tokens,
        ihLeft hLeft, ihRight hRight]
  | iff left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        Formula.hilbert_iff, Formula.hilbert_conj,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.negation_tokens,
        GodelQuotation.Numbered.implication_tokens,
        ihLeft hLeft, ihRight hRight]
  | forallE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      have hBody := ih hClosed
      simp only [GodelQuotation.canonical_bound_names] at hBody
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.universal_tokens,
        hBody]
  | existsE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      have hBody := ih hClosed
      simp only [GodelQuotation.canonical_bound_names] at hBody
      simp [fs_project_hilbert_token_tree,
        fs_embed_project_formula, Formula.hilbertize,
        GodelQuotation.RawHilbertTokenTree.tokens,
        GodelQuotation.Numbered.negation_tokens,
        GodelQuotation.Numbered.universal_tokens,
        hBody]

/-! ## token 树反向解码 -/

/-- 在规范 binder token 表中构造性恢复 Project bound 变量。 -/
def fs_project_bound_term_decode :
    (depth : Nat) → Nat →
      Option (Project.Term depth)
  | 0, _ =>
      none
  | depth + 1, token =>
      if token =
          GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth) then
        some (.bound 0)
      else
        (fs_project_bound_term_decode depth token).bind
          fun term =>
            match term with
            | .bound entry =>
                some (.bound entry.succ)
            | .free _ =>
                none

/-- 原始项树只在它是当前规范 scope 中的 bound 变量时解码成功。 -/
def fs_project_term_token_tree_decode
    (depth : Nat) :
    GodelQuotation.RawTermTokenTree →
      Option (Project.Term depth)
  | .atom token =>
      fs_project_bound_term_decode depth token
  | .application _ _ =>
      none

/-- 原始 Hilbert token 树到自由闭合 Project Hilbert 核公式的解码器。 -/
def fs_project_hilbert_token_tree_decode :
    (depth : Nat) →
      GodelQuotation.RawHilbertTokenTree →
        Option (Project.Formula 1 depth)
  | depth, .equality left right => do
      let leftTerm ←
        fs_project_term_token_tree_decode depth left
      let rightTerm ←
        fs_project_term_token_tree_decode depth right
      pure <| Project.Formula.extensionalEq
        leftTerm rightTerm
  | depth, .membership left right => do
      let leftTerm ←
        fs_project_term_token_tree_decode depth left
      let rightTerm ←
        fs_project_term_token_tree_decode depth right
      pure <| .mem leftTerm rightTerm
  | depth, .predicate head arguments =>
      if head =
          GodelQuotation.Numbered.predicate_token
            1 Nonlogical.BasicSetTheory.RelationSymbol.subset.ctorIdx then
        match arguments with
        | [left, right] => do
            let leftTerm ←
              fs_project_term_token_tree_decode depth left
            let rightTerm ←
              fs_project_term_token_tree_decode depth right
            pure <| Project.Formula.subset
              leftTerm rightTerm
        | _ =>
            none
      else
        none
  | depth, .negation body =>
      (fs_project_hilbert_token_tree_decode
        depth body).map .neg
  | depth, .implication left right => do
      let leftFormula ←
        fs_project_hilbert_token_tree_decode depth left
      let rightFormula ←
        fs_project_hilbert_token_tree_decode depth right
      pure <| .imp leftFormula rightFormula
  | depth, .universal variableToken body =>
      if variableToken =
          GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth) then
        (fs_project_hilbert_token_tree_decode
          (depth + 1) body).map .forallE
      else
        none

/-- 自然数 token 串到 Project Hilbert 核公式的完整解码器。 -/
def fs_project_hilbert_tokens_decode
    (depth : Nat) (tokens : List Nat) :
    Option (Project.Formula 1 depth) := do
  let tree ←
    GodelQuotation.RawHilbertTokenTree.parse? tokens
  fs_project_hilbert_token_tree_decode depth tree

/-- 自然数序列码到 Project Hilbert 核公式的完整解码器。 -/
def fs_project_hilbert_code_decode
    (depth code : Nat) :
    Option (Project.Formula 1 depth) :=
  fs_project_hilbert_tokens_decode depth
    (nat_sequence_decode code)

/-- 规范 bound token 的反向解码精确恢复原 Project 变量。 -/
@[simp]
theorem fs_project_bound_term_decode_encode
    {depth : Nat}
    (entry : Fin depth) :
    fs_project_bound_term_decode depth
        (fs_project_bound_token entry) =
      some (.bound entry) := by
  induction depth with
  | zero =>
      exact Fin.elim0 entry
  | succ depth ih =>
      refine Fin.cases ?_ (fun previous => ?_) entry
      · simp [fs_project_bound_term_decode,
          fs_project_bound_token]
      · have hTokenNe :
            fs_project_bound_token previous ≠
              GodelQuotation.Numbered.variable_token
                (GodelQuotation.bound_name depth) := by
          intro hEqual
          rw [fs_project_bound_token_eq] at hEqual
          have hNames :=
            GodelQuotation.variable_token_injective hEqual
          have hDepths :=
            GodelQuotation.bound_name_injective hNames
          omega
        simp [fs_project_bound_term_decode,
          fs_project_bound_token, hTokenNe,
          ih previous]

@[simp]
theorem fs_project_bound_term_decode_newest
    (depth : Nat) :
    fs_project_bound_term_decode (depth + 1)
        (GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth)) =
      some (.bound (0 : Fin (depth + 1))) := by
  simpa [fs_project_bound_token] using
    (fs_project_bound_term_decode_encode
      (depth := depth + 1) (entry := (0 : Fin (depth + 1))))

/-- 自由闭合 Project 项的 token 树解码回原项。 -/
@[simp]
theorem fs_project_term_token_tree_decode_encode
    {depth : Nat}
    (term : Project.Term depth)
    (hClosed : term.freeSupport = []) :
    fs_project_term_token_tree_decode depth
        (fs_project_term_token_tree term) =
      some term := by
  cases term with
  | bound entry =>
      simp [fs_project_term_token_tree_decode,
        fs_project_term_token_tree]
  | free id =>
      simp at hClosed

private theorem fs_project_term_vector_ext
    {count depth : Nat}
    {left right : TermVector count depth}
    (hTerms : left.terms = right.terms) :
    left = right := by
  cases left with
  | mk leftTerms leftSize =>
      cases right with
      | mk rightTerms rightSize =>
          cases hTerms
          rfl

private theorem fs_project_term_vector_two_ext
    {depth : Nat}
    (arguments : TermVector 2 depth) :
    Project.Formula.pairArguments
        (arguments 0) (arguments 1) =
      arguments := by
  cases arguments with
  | mk terms hSize =>
      have hArray :
          (Project.Formula.pairArguments
              (TermVector.get
                { terms := terms, size_eq := hSize } 0)
              (TermVector.get
                { terms := terms, size_eq := hSize } 1)).terms =
            terms := by
        apply Array.ext
        · exact hSize.symm
        · intro index hLeft hRight
          have hIndex : index < 2 := by
            simpa [hSize] using hRight
          have hCases : index = 0 ∨ index = 1 := by
            omega
          rcases hCases with rfl | rfl <;>
            simp [Project.Formula.pairArguments,
              TermVector.get]
      exact fs_project_term_vector_ext hArray

/-- 编码所得 Hilbert token 树解码回 Project Hilbert 归约。 -/
@[simp]
theorem fs_project_hilbert_token_tree_decode_encode
    {depth : Nat}
    (formula : Project.Formula 1 depth)
    (hClosed : formula.FreeClosed) :
    fs_project_hilbert_token_tree_decode depth
        (fs_project_hilbert_token_tree formula) =
      some (fs_project_hilbertize formula) := by
  induction formula with
  | falsum =>
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        fs_project_hilbert_falsum,
        fs_project_hilbert_truth,
        fs_project_term_token_tree_decode,
        fs_project_bound_term_decode_newest]
  | truth =>
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        fs_project_hilbert_truth,
        fs_project_term_token_tree_decode,
        fs_project_bound_term_decode_newest]
  | mem left right =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        fs_project_term_token_tree_decode_encode
          left hLeft,
        fs_project_term_token_tree_decode_encode
          right hRight]
  | atom symbol hStage arguments =>
      simp only [Definitional.Formula.FreeClosed,
        Definitional.TermVector.FreeClosed] at hClosed
      cases symbol with
      | extensionalEq =>
          have hAtom :
              Project.Formula.extensionalEq
                  (arguments 0) (arguments 1) =
                .atom .extensionalEq hStage arguments := by
            unfold Project.Formula.extensionalEq
            rw [fs_project_term_vector_two_ext arguments]
          simp only [fs_project_hilbertize]
          rw [← hAtom]
          simp [fs_project_hilbert_token_tree_decode,
            fs_project_hilbert_token_tree,
            Project.Formula.extensionalEq,
            fs_project_term_token_tree_decode_encode
              (arguments 0) (hClosed 0),
            fs_project_term_token_tree_decode_encode
              (arguments 1) (hClosed 1)]
      | subset =>
          have hAtom :
              Project.Formula.subset
                  (arguments 0) (arguments 1) =
                .atom .subset hStage arguments := by
            unfold Project.Formula.subset
            rw [fs_project_term_vector_two_ext arguments]
          simp only [fs_project_hilbertize]
          rw [← hAtom]
          simp [fs_project_hilbert_token_tree_decode,
            fs_project_hilbert_token_tree,
            Project.Formula.subset,
            fs_project_term_token_tree_decode_encode
              (arguments 0) (hClosed 0),
            fs_project_term_token_tree_decode_encode
              (arguments 1) (hClosed 1)]
  | neg body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        ih hClosed]
  | conj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        fs_project_hilbert_conj,
        ihLeft hLeft, ihRight hRight]
  | disj left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        ihLeft hLeft, ihRight hRight]
  | imp left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        ihLeft hLeft, ihRight hRight]
  | iff left right ihLeft ihRight =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        fs_project_hilbert_iff,
        fs_project_hilbert_conj,
        ihLeft hLeft, ihRight hRight]
  | forallE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        ih hClosed]
  | existsE body ih =>
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp [fs_project_hilbert_token_tree_decode,
        fs_project_hilbert_token_tree,
        fs_project_hilbertize,
        ih hClosed]

/-- 编码所得 token 串经公共 parser 与 Project 解码器后恢复 Hilbert 归约。 -/
@[simp]
theorem fs_project_hilbert_tokens_decode_encode
    {depth : Nat}
    (formula : Project.Formula 1 depth)
    (hClosed : formula.FreeClosed) :
    fs_project_hilbert_tokens_decode depth
        (fs_project_hilbert_token_tree formula).tokens =
      some (fs_project_hilbertize formula) := by
  simp [fs_project_hilbert_tokens_decode,
    GodelQuotation.RawHilbertTokenTree.parse?_tokens,
    fs_project_hilbert_token_tree_lexicallySeparated,
    fs_project_hilbert_token_tree_decode_encode,
    hClosed]

/-- 编码所得自然数序列码解回 Project Hilbert 归约。 -/
@[simp]
theorem fs_project_hilbert_code_decode_encode
    {depth : Nat}
    (formula : Project.Formula 1 depth)
    (hClosed : formula.FreeClosed) :
    fs_project_hilbert_code_decode depth
        (nat_sequence_code_value
          (fs_project_hilbert_token_tree formula).tokens) =
      some (fs_project_hilbertize formula) := by
  simp [fs_project_hilbert_code_decode,
    nat_sequence_decode_code_value,
    fs_project_hilbert_tokens_decode_encode,
    hClosed]

/-! ## 解码结果边界 -/

/-- bound token 解码成功时结果不含自由变量。 -/
theorem fs_project_bound_term_decode_freeClosed
    {depth token : Nat}
    {term : Project.Term depth}
    (hDecode :
      fs_project_bound_term_decode depth token =
        some term) :
    term.freeSupport = [] := by
  induction depth generalizing token with
  | zero =>
      simp [fs_project_bound_term_decode] at hDecode
  | succ depth ih =>
      simp only [fs_project_bound_term_decode] at hDecode
      split at hDecode
      next =>
        simp at hDecode
        subst term
        rfl
      next =>
        cases hPrevious :
            fs_project_bound_term_decode depth token with
        | none =>
            simp [hPrevious] at hDecode
        | some previous =>
            cases previous with
            | bound entry =>
                simp [hPrevious] at hDecode
                subst term
                rfl
            | free id =>
                simp [hPrevious] at hDecode

/-- 项树解码成功时结果不含自由变量。 -/
theorem fs_project_term_token_tree_decode_freeClosed
    {depth : Nat}
    {tree : GodelQuotation.RawTermTokenTree}
    {term : Project.Term depth}
    (hDecode :
      fs_project_term_token_tree_decode depth tree =
        some term) :
    term.freeSupport = [] := by
  cases tree with
  | atom token =>
      exact fs_project_bound_term_decode_freeClosed
        hDecode
  | application head arguments =>
      simp [fs_project_term_token_tree_decode] at hDecode

/-- Hilbert token 树解码成功时结果自由闭合。 -/
theorem fs_project_hilbert_token_tree_decode_freeClosed
    {depth : Nat}
    {tree : GodelQuotation.RawHilbertTokenTree}
    {formula : Project.Formula 1 depth}
    (hDecode :
      fs_project_hilbert_token_tree_decode depth tree =
        some formula) :
    formula.FreeClosed := by
  revert formula
  induction tree generalizing depth with
  | equality left right =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_project_term_token_tree_decode depth left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_project_term_token_tree_decode depth right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              simp [hLeft, hRight] at hDecode
              subst formula
              simpa only [Project.Formula.extensionalEq,
                Definitional.Formula.FreeClosed] using
                Project.Formula.pairArguments_freeClosed
                  leftTerm rightTerm
                  (fs_project_term_token_tree_decode_freeClosed hLeft)
                  (fs_project_term_token_tree_decode_freeClosed hRight)
  | membership left right =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_project_term_token_tree_decode depth left with
      | none =>
          simp [hLeft] at hDecode
      | some leftTerm =>
          cases hRight :
              fs_project_term_token_tree_decode depth right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightTerm =>
              simp [hLeft, hRight] at hDecode
              subst formula
              simpa only [Definitional.Formula.FreeClosed] using
                And.intro
                  (fs_project_term_token_tree_decode_freeClosed hLeft)
                  (fs_project_term_token_tree_decode_freeClosed hRight)
  | predicate head arguments =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      split at hDecode
      next =>
        cases arguments with
        | nil =>
            simp at hDecode
        | cons first rest =>
            cases rest with
            | nil =>
                simp at hDecode
            | cons second tail =>
                cases tail with
                | nil =>
                    cases hLeft :
                        fs_project_term_token_tree_decode
                          depth first with
                    | none =>
                        simp [hLeft] at hDecode
                    | some leftTerm =>
                        cases hRight :
                            fs_project_term_token_tree_decode
                              depth second with
                        | none =>
                            simp [hLeft, hRight] at hDecode
                        | some rightTerm =>
                            simp [hLeft, hRight] at hDecode
                            subst formula
                            simpa only [Project.Formula.subset,
                              Definitional.Formula.FreeClosed] using
                              Project.Formula.pairArguments_freeClosed
                                leftTerm rightTerm
                                (fs_project_term_token_tree_decode_freeClosed
                                  hLeft)
                                (fs_project_term_token_tree_decode_freeClosed
                                  hRight)
                | cons third tail =>
                    simp at hDecode
      next =>
        simp at hDecode
  | negation body ih =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hBody :
          fs_project_hilbert_token_tree_decode depth body with
      | none =>
          simp [hBody] at hDecode
      | some bodyFormula =>
          simp [hBody] at hDecode
          subst formula
          simpa only [Definitional.Formula.FreeClosed] using
            ih (depth := depth) (formula := bodyFormula) hBody
  | implication left right ihLeft ihRight =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      cases hLeft :
          fs_project_hilbert_token_tree_decode depth left with
      | none =>
          simp [hLeft] at hDecode
      | some leftFormula =>
          cases hRight :
              fs_project_hilbert_token_tree_decode depth right with
          | none =>
              simp [hLeft, hRight] at hDecode
          | some rightFormula =>
              simp [hLeft, hRight] at hDecode
              subst formula
              simpa only [Definitional.Formula.FreeClosed] using
                And.intro
                  (ihLeft (depth := depth)
                    (formula := leftFormula) hLeft)
                  (ihRight (depth := depth)
                    (formula := rightFormula) hRight)
  | universal variableToken body ih =>
      intro formula hDecode
      simp only [fs_project_hilbert_token_tree_decode] at hDecode
      split at hDecode
      next =>
        cases hBody :
            fs_project_hilbert_token_tree_decode
              (depth + 1) body with
        | none =>
            simp [hBody] at hDecode
        | some bodyFormula =>
            simp [hBody] at hDecode
            subst formula
            simpa only [Definitional.Formula.FreeClosed] using
              ih (depth := depth + 1)
                (formula := bodyFormula) hBody
      next =>
        simp at hDecode

/-- token 串解码成功时结果自由闭合。 -/
theorem fs_project_hilbert_tokens_decode_freeClosed
    {depth : Nat}
    {tokens : List Nat}
    {formula : Project.Formula 1 depth}
    (hDecode :
      fs_project_hilbert_tokens_decode depth tokens =
        some formula) :
    formula.FreeClosed := by
  unfold fs_project_hilbert_tokens_decode at hDecode
  cases hParse :
      GodelQuotation.RawHilbertTokenTree.parse? tokens with
  | none =>
      simp [hParse] at hDecode
  | some tree =>
      exact
        fs_project_hilbert_token_tree_decode_freeClosed
          (by simpa [hParse] using hDecode)

/-- 自然数序列码解码成功时结果自由闭合。 -/
theorem fs_project_hilbert_code_decode_freeClosed
    {depth code : Nat}
    {formula : Project.Formula 1 depth}
    (hDecode :
      fs_project_hilbert_code_decode depth code =
        some formula) :
    formula.FreeClosed :=
  fs_project_hilbert_tokens_decode_freeClosed hDecode

/-! ## proof-carrying schema 解码 -/

/-- token 序列码直接解成携带自由闭合证明的一元 schema。 -/
def fs_project_unary_schema_hilbert_decode
    (parameterCount bodyTokenCode : Nat) :
    Option (Project.UnarySchema parameterCount) :=
  match fs_project_hilbert_code_decode
      (parameterCount + 1) bodyTokenCode with
  | none =>
      none
  | some body =>
      if hClosed : body.FreeClosed then
        some {
          body := body
          freeClosed := hClosed
        }
      else
        none

/-- token 序列码直接解成携带自由闭合证明的二元 schema。 -/
def fs_project_binary_schema_hilbert_decode
    (parameterCount bodyTokenCode : Nat) :
    Option (Project.BinarySchema parameterCount) :=
  match fs_project_hilbert_code_decode
      (parameterCount + 2) bodyTokenCode with
  | none =>
      none
  | some body =>
      if hClosed : body.FreeClosed then
        some {
          body := body
          freeClosed := hClosed
        }
      else
        none

/-- 一元 proof-carrying 包装没有额外失败分支。 -/
theorem fs_project_unary_schema_hilbert_decode_eq_none_iff
    (parameterCount bodyTokenCode : Nat) :
    fs_project_unary_schema_hilbert_decode
        parameterCount bodyTokenCode =
      none ↔
    fs_project_hilbert_code_decode
        (parameterCount + 1) bodyTokenCode =
      none := by
  unfold fs_project_unary_schema_hilbert_decode
  cases hDecode :
      fs_project_hilbert_code_decode
        (parameterCount + 1) bodyTokenCode with
  | none =>
      simp
  | some body =>
      have hClosed :
          body.FreeClosed :=
        fs_project_hilbert_code_decode_freeClosed
          hDecode
      simp [hClosed]

/-- 二元 proof-carrying 包装没有额外失败分支。 -/
theorem fs_project_binary_schema_hilbert_decode_eq_none_iff
    (parameterCount bodyTokenCode : Nat) :
    fs_project_binary_schema_hilbert_decode
        parameterCount bodyTokenCode =
      none ↔
    fs_project_hilbert_code_decode
        (parameterCount + 2) bodyTokenCode =
      none := by
  unfold fs_project_binary_schema_hilbert_decode
  cases hDecode :
      fs_project_hilbert_code_decode
        (parameterCount + 2) bodyTokenCode with
  | none =>
      simp
  | some body =>
      have hClosed :
          body.FreeClosed :=
        fs_project_hilbert_code_decode_freeClosed
          hDecode
      simp [hClosed]

/-- 一元 schema 的规范 token 码解回其 Project Hilbert 归约。 -/
@[simp]
theorem fs_project_unary_schema_hilbert_decode_encode
    {parameterCount : Nat}
    (schema : Project.UnarySchema parameterCount) :
    fs_project_unary_schema_hilbert_decode
        parameterCount
      (nat_sequence_code_value
          (fs_project_hilbert_token_tree schema.body).tokens) =
      some (fs_project_unary_schema_hilbertize schema) := by
  unfold fs_project_unary_schema_hilbert_decode
  have hDecode :
      fs_project_hilbert_code_decode
          (parameterCount + 1)
          (nat_sequence_code_value
            (fs_project_hilbert_token_tree schema.body).tokens) =
        some (fs_project_hilbertize schema.body) :=
    fs_project_hilbert_code_decode_encode
      schema.body schema.freeClosed
  simp only [hDecode]
  split
  next hClosed =>
    rfl
  next hNotClosed =>
    exact (hNotClosed
      (fs_project_hilbertize_freeClosed schema.freeClosed)).elim

/-- 二元 schema 的规范 token 码解回其 Project Hilbert 归约。 -/
@[simp]
theorem fs_project_binary_schema_hilbert_decode_encode
    {parameterCount : Nat}
    (schema : Project.BinarySchema parameterCount) :
    fs_project_binary_schema_hilbert_decode
        parameterCount
      (nat_sequence_code_value
          (fs_project_hilbert_token_tree schema.body).tokens) =
      some (fs_project_binary_schema_hilbertize schema) := by
  unfold fs_project_binary_schema_hilbert_decode
  have hDecode :
      fs_project_hilbert_code_decode
          (parameterCount + 2)
          (nat_sequence_code_value
            (fs_project_hilbert_token_tree schema.body).tokens) =
        some (fs_project_hilbertize schema.body) :=
    fs_project_hilbert_code_decode_encode
      schema.body schema.freeClosed
  simp only [hDecode]
  split
  next hClosed =>
    rfl
  next hNotClosed =>
    exact (hNotClosed
      (fs_project_hilbertize_freeClosed schema.freeClosed)).elim

end ProofCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
