import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCollectionCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.Sequence

/-!
# replacement schema 的 checked quotation 基础

本模块把 replacement 独有的两个编码步骤从 collection 公共设施中分离出来：

* 唯一性前件的第二输出由 cutoff `p + 1` 的一次规范 shift 得到；
* 像集 body 由两个规范 bound-name 的三步捕获规避交换得到。

交换定理对任意自由闭合项目公式成立，不依赖 replacement 的具体公式形状。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project

set_option autoImplicit false

/-! ## 规范 bound-name 交换 -/

/-- 交换两个绝对 binder 深度，其他深度保持不变。 -/
def canonical_project_swap_depth
    (first second depth : Nat) : Nat :=
  if depth = first then second
  else if depth = second then first
  else depth

/--
两张项目索引图在规范 quotation 中只相差两个绝对 binder 深度的交换。
-/
def CanonicalProjectIndexSwap
    {originalDepth targetDepth : Nat}
    (first second : Nat)
    (sourceMap targetMap :
      Fin originalDepth → Fin targetDepth) : Prop :=
  ∀ entry,
    canonical_project_swap_depth first second
        (targetDepth - (sourceMap entry).val - 1) =
      targetDepth - (targetMap entry).val - 1

/-- 穿过一个位于交换深度之外的新 binder 时，索引交换合同保持成立。 -/
theorem CanonicalProjectIndexSwap.lift
    {originalDepth targetDepth first second : Nat}
    {sourceMap targetMap :
      Fin originalDepth → Fin targetDepth}
    (hSwap :
      CanonicalProjectIndexSwap
        first second sourceMap targetMap)
    (hFirst : first < targetDepth)
    (hSecond : second < targetDepth) :
    CanonicalProjectIndexSwap first second
      (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift sourceMap)
      (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift targetMap) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · have hFirstNe : targetDepth ≠ first :=
      Nat.ne_of_gt hFirst
    have hSecondNe : targetDepth ≠ second :=
      Nat.ne_of_gt hSecond
    simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
      canonical_project_swap_depth,
      hFirstNe, hSecondNe]
  · have hSource :
        targetDepth + 1 -
              ((sourceMap previous).val + 1) - 1 =
            targetDepth - (sourceMap previous).val - 1 := by
      omega
    have hTarget :
        targetDepth + 1 -
              ((targetMap previous).val + 1) - 1 =
            targetDepth - (targetMap previous).val - 1 := by
      omega
    simpa [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.lift,
      hSource, hTarget] using hSwap previous

/-- 三次 singleton substitution 实现两个规范 bound-name 的交换。 -/
def fs_zfc_swap_bound_tokens
    (first second : Nat)
    (tokens : List Nat) : List Nat :=
  let temporary :=
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.free_name 0)
  let firstToken :=
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name first)
  let secondToken :=
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name second)
  GodelQuotation.substitute_tokens
    (GodelQuotation.substitute_tokens
      (GodelQuotation.substitute_tokens
        tokens firstToken [temporary])
      secondToken [firstToken])
    temporary [secondToken]

theorem fs_zfc_swap_bound_tokens_singleton
    (first second depth : Nat)
    (hDistinct : first ≠ second) :
    fs_zfc_swap_bound_tokens first second
        [GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name depth)] =
      [GodelQuotation.Numbered.variable_token
        (GodelQuotation.bound_name
          (canonical_project_swap_depth
            first second depth))] := by
  have hFirstSecond :
      GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name first) ≠
        GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name second) :=
    GodelQuotation.variable_token_ne_variable_token
      (fun h => hDistinct
        (GodelQuotation.bound_name_injective h))
  have hFirstTemporary :
      GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name first) ≠
        GodelQuotation.Numbered.variable_token
          (GodelQuotation.free_name 0) :=
    GodelQuotation.variable_token_ne_variable_token
      (Ne.symm
        (GodelQuotation.free_name_ne_bound_name 0 first))
  have hSecondTemporary :
      GodelQuotation.Numbered.variable_token
          (GodelQuotation.bound_name second) ≠
        GodelQuotation.Numbered.variable_token
          (GodelQuotation.free_name 0) :=
    GodelQuotation.variable_token_ne_variable_token
      (Ne.symm
        (GodelQuotation.free_name_ne_bound_name 0 second))
  have hSecondFirst := Ne.symm hFirstSecond
  have hTemporarySecond := Ne.symm hSecondTemporary
  by_cases hFirst : depth = first
  · subst depth
    simp [fs_zfc_swap_bound_tokens,
      canonical_project_swap_depth,
      GodelQuotation.substitute_tokens_cons,
      GodelQuotation.substitution_piece_tokens,
      hTemporarySecond]
  · by_cases hSecond : depth = second
    · subst depth
      simp [fs_zfc_swap_bound_tokens,
        canonical_project_swap_depth, hFirst,
        GodelQuotation.substitute_tokens_cons,
        GodelQuotation.substitution_piece_tokens,
        hSecondFirst, hFirstTemporary]
    · have hDepthFirst :
          GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name depth) ≠
            GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name first) :=
        GodelQuotation.variable_token_ne_variable_token
          (fun h => hFirst
            (GodelQuotation.bound_name_injective h))
      have hDepthSecond :
          GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name depth) ≠
            GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name second) :=
        GodelQuotation.variable_token_ne_variable_token
          (fun h => hSecond
            (GodelQuotation.bound_name_injective h))
      have hDepthTemporary :
          GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name depth) ≠
            GodelQuotation.Numbered.variable_token
              (GodelQuotation.free_name 0) :=
        GodelQuotation.variable_token_ne_variable_token
          (Ne.symm
            (GodelQuotation.free_name_ne_bound_name 0 depth))
      simp [fs_zfc_swap_bound_tokens,
        canonical_project_swap_depth, hFirst, hSecond,
        GodelQuotation.substitute_tokens_cons,
        GodelQuotation.substitution_piece_tokens,
        hDepthFirst, hDepthSecond, hDepthTemporary]

/-- 交换与 Hilbert 原子/联结词的 token 构造逐层交换。 -/
private theorem fs_zfc_swap_bound_tokens_negation
    (first second : Nat) (tokens : List Nat) :
    fs_zfc_swap_bound_tokens first second
        (GodelQuotation.Numbered.negation_tokens tokens) =
      GodelQuotation.Numbered.negation_tokens
        (fs_zfc_swap_bound_tokens first second tokens) := by
  simp [fs_zfc_swap_bound_tokens,
    GodelQuotation.substitute_tokens_negation_tokens]

private theorem fs_zfc_swap_bound_tokens_implication
    (first second : Nat)
    (left right : List Nat) :
    fs_zfc_swap_bound_tokens first second
        (GodelQuotation.Numbered.implication_tokens left right) =
      GodelQuotation.Numbered.implication_tokens
        (fs_zfc_swap_bound_tokens first second left)
        (fs_zfc_swap_bound_tokens first second right) := by
  simp [fs_zfc_swap_bound_tokens,
    GodelQuotation.substitute_tokens_implication_tokens]

private theorem fs_zfc_swap_bound_tokens_membership
    (first second : Nat)
    (left right : List Nat) :
    fs_zfc_swap_bound_tokens first second
        (GodelQuotation.Numbered.membership_tokens left right) =
      GodelQuotation.Numbered.membership_tokens
        (fs_zfc_swap_bound_tokens first second left)
        (fs_zfc_swap_bound_tokens first second right) := by
  simp [fs_zfc_swap_bound_tokens,
    GodelQuotation.substitute_tokens_membership_tokens]

private theorem fs_zfc_swap_bound_tokens_equality
    (first second : Nat)
    (left right : List Nat) :
    fs_zfc_swap_bound_tokens first second
        (GodelQuotation.Numbered.equality_tokens left right) =
      GodelQuotation.Numbered.equality_tokens
        (fs_zfc_swap_bound_tokens first second left)
        (fs_zfc_swap_bound_tokens first second right) := by
  simp [fs_zfc_swap_bound_tokens,
    GodelQuotation.substitute_tokens_equality_tokens]

private theorem fs_zfc_swap_bound_tokens_predicate
    (first second arityPredecessor index : Nat)
    (arguments : List (List Nat)) :
    fs_zfc_swap_bound_tokens first second
        (GodelQuotation.Numbered.predicate_application_tokens
          arityPredecessor index arguments) =
      GodelQuotation.Numbered.predicate_application_tokens
        arityPredecessor index
        (arguments.map
          (fs_zfc_swap_bound_tokens first second)) := by
  simp [fs_zfc_swap_bound_tokens,
    GodelQuotation.substitute_tokens_predicate_application_tokens,
    List.map_map, Function.comp_def]
  apply congrArg
    (GodelQuotation.Numbered.predicate_application_tokens
      arityPredecessor index)
  exact List.map_congr_left fun argument _ => rfl

private theorem fs_zfc_swap_bound_tokens_universal
    (first second depth : Nat)
    (tokens : List Nat)
    (hFirst : first ≠ depth)
    (hSecond : second ≠ depth) :
    fs_zfc_swap_bound_tokens first second
        (GodelQuotation.Numbered.universal_tokens
          (GodelQuotation.bound_name depth) tokens) =
      GodelQuotation.Numbered.universal_tokens
        (GodelQuotation.bound_name depth)
        (fs_zfc_swap_bound_tokens first second tokens) := by
  dsimp [fs_zfc_swap_bound_tokens]
  rw [GodelQuotation.substitute_tokens_universal_tokens
    (GodelQuotation.bound_name depth)
    (GodelQuotation.bound_name first) _ _
    (GodelQuotation.bound_name_injective.ne
      (Ne.symm hFirst))]
  rw [GodelQuotation.substitute_tokens_universal_tokens
    (GodelQuotation.bound_name depth)
    (GodelQuotation.bound_name second) _ _
    (GodelQuotation.bound_name_injective.ne
      (Ne.symm hSecond))]
  rw [GodelQuotation.substitute_tokens_universal_tokens
    (GodelQuotation.bound_name depth)
    (GodelQuotation.free_name 0) _ _
    (Ne.symm
      (GodelQuotation.free_name_ne_bound_name 0 depth))]

private theorem fs_raw_hilbert_equality_tokens
    (left right : GodelQuotation.RawTermTokenTree) :
    (GodelQuotation.RawHilbertTokenTree.equality left right).tokens =
      GodelQuotation.Numbered.equality_tokens
        left.tokens right.tokens := rfl

private theorem fs_raw_hilbert_negation_tokens
    (body : GodelQuotation.RawHilbertTokenTree) :
    (GodelQuotation.RawHilbertTokenTree.negation body).tokens =
      GodelQuotation.Numbered.negation_tokens body.tokens := rfl

private theorem fs_raw_hilbert_universal_tokens
    (name : Nat)
    (body : GodelQuotation.RawHilbertTokenTree) :
    (GodelQuotation.RawHilbertTokenTree.universal
        (GodelQuotation.Numbered.variable_token name) body).tokens =
      GodelQuotation.Numbered.universal_tokens
        name body.tokens := rfl

private theorem fs_raw_hilbert_predicate_tokens
    (arityPredecessor index : Nat)
    (arguments : List GodelQuotation.RawTermTokenTree) :
    (GodelQuotation.RawHilbertTokenTree.predicate
        (GodelQuotation.Numbered.predicate_token
          arityPredecessor index)
        arguments).tokens =
      GodelQuotation.Numbered.predicate_application_tokens
        arityPredecessor index
        (arguments.map GodelQuotation.RawTermTokenTree.tokens) := by
  simp [GodelQuotation.RawHilbertTokenTree.tokens,
    GodelQuotation.Numbered.predicate_application_tokens]

/--
自由闭合项目项沿两张交换索引图重命名后，其规范 token quotation 由同一三步
bound-name substitution 连接。
-/
theorem fs_embed_project_renamed_term_quote_swap
    {originalDepth targetDepth first second : Nat}
    (term : FsProjectTerm originalDepth)
    (sourceMap targetMap :
      Fin originalDepth → Fin targetDepth)
    (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Term.freeSupport
        term = [])
    (hSwap :
      CanonicalProjectIndexSwap
        first second sourceMap targetMap)
    (hDistinct : first ≠ second) :
    GodelQuotation.Numbered.quote_term_tokens_with?
        GodelQuotation.free_name
        (GodelQuotation.canonical_bound_names targetDepth)
        (fs_embed_project_term (term.rename targetMap)) =
      (GodelQuotation.Numbered.quote_term_tokens_with?
        GodelQuotation.free_name
        (GodelQuotation.canonical_bound_names targetDepth)
        (fs_embed_project_term (term.rename sourceMap))).map
          (fs_zfc_swap_bound_tokens first second) := by
  cases term with
  | bound entry =>
      have hSourceIndex :
          (sourceMap entry).val < targetDepth :=
        (sourceMap entry).isLt
      have hTargetIndex :
          (targetMap entry).val < targetDepth :=
        (targetMap entry).isLt
      have hSourceName :=
        GodelQuotation.canonical_bound_names_getElem?
          targetDepth (sourceMap entry).val hSourceIndex
      have hTargetName :=
        GodelQuotation.canonical_bound_names_getElem?
          targetDepth (targetMap entry).val hTargetIndex
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Term.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Term.bind,
        Function.comp_apply,
        fs_embed_project_term,
        GodelQuotation.Numbered.quote_term_tokens_with?]
      rw [hSourceName, hTargetName]
      simp only [Option.map_some, Option.some.injEq]
      rw [fs_zfc_swap_bound_tokens_singleton
        first second
        (targetDepth - (sourceMap entry).val - 1)
        hDistinct]
      rw [hSwap entry]
  | free id =>
      simp [
        _root_.YesMetaZFC.SetTheory.Definitional.Term.freeSupport]
        at hClosed

private theorem fs_project_renamed_term_token_tree_swap
    {originalDepth targetDepth first second : Nat}
    (term : FsProjectTerm originalDepth)
    (sourceMap targetMap :
      Fin originalDepth → Fin targetDepth)
    (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Term.freeSupport
        term = [])
    (hSwap :
      CanonicalProjectIndexSwap
        first second sourceMap targetMap)
    (hDistinct : first ≠ second) :
    (fs_project_term_token_tree
        (term.rename targetMap)).tokens =
      fs_zfc_swap_bound_tokens first second
        (fs_project_term_token_tree
          (term.rename sourceMap)).tokens := by
  have hQuote :=
    fs_embed_project_renamed_term_quote_swap
      term sourceMap targetMap hClosed hSwap hDistinct
  rw [
    fs_project_term_token_tree_tokens
      (term.rename targetMap) (by simpa using hClosed),
    fs_project_term_token_tree_tokens
      (term.rename sourceMap) (by simpa using hClosed)]
    at hQuote
  simpa using hQuote

/--
任意自由闭合项目公式沿交换索引图重命名后，Hilbert quotation 由同一三步
bound-name substitution 连接。内部量词的名字严格晚于两个被交换的外层名字。
-/
private theorem fs_project_hilbert_token_tree_rename_swap
    {originalDepth targetDepth first second : Nat}
    (formula : FsProjectFormula 1 originalDepth)
    (sourceMap targetMap :
      Fin originalDepth → Fin targetDepth)
    (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed
        formula)
    (hFirst : first < targetDepth)
    (hSecond : second < targetDepth)
    (hDistinct : first ≠ second)
    (hSwap :
      CanonicalProjectIndexSwap
        first second sourceMap targetMap) :
    (fs_project_hilbert_token_tree
        (formula.rename targetMap)).tokens =
      fs_zfc_swap_bound_tokens first second
        (fs_project_hilbert_token_tree
          (formula.rename sourceMap)).tokens := by
  induction formula generalizing targetDepth with
  | falsum =>
      change
        GodelQuotation.Numbered.negation_tokens
            (GodelQuotation.Numbered.universal_tokens
              (GodelQuotation.bound_name targetDepth)
              (GodelQuotation.Numbered.equality_tokens
                [GodelQuotation.Numbered.variable_token
                  (GodelQuotation.bound_name targetDepth)]
                [GodelQuotation.Numbered.variable_token
                  (GodelQuotation.bound_name targetDepth)])) =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.negation_tokens
              (GodelQuotation.Numbered.universal_tokens
                (GodelQuotation.bound_name targetDepth)
                (GodelQuotation.Numbered.equality_tokens
                  [GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name targetDepth)]
                  [GodelQuotation.Numbered.variable_token
                    (GodelQuotation.bound_name targetDepth)])))
      rw [fs_zfc_swap_bound_tokens_negation,
        fs_zfc_swap_bound_tokens_universal first second targetDepth _
          (Nat.ne_of_lt hFirst) (Nat.ne_of_lt hSecond),
        fs_zfc_swap_bound_tokens_equality,
        fs_zfc_swap_bound_tokens_singleton first second targetDepth
          hDistinct]
      simp [canonical_project_swap_depth,
        Nat.ne_of_gt hFirst, Nat.ne_of_gt hSecond]
  | truth =>
      change
        GodelQuotation.Numbered.universal_tokens
            (GodelQuotation.bound_name targetDepth)
            (GodelQuotation.Numbered.equality_tokens
              [GodelQuotation.Numbered.variable_token
                (GodelQuotation.bound_name targetDepth)]
              [GodelQuotation.Numbered.variable_token
                (GodelQuotation.bound_name targetDepth)]) =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.universal_tokens
              (GodelQuotation.bound_name targetDepth)
              (GodelQuotation.Numbered.equality_tokens
                [GodelQuotation.Numbered.variable_token
                  (GodelQuotation.bound_name targetDepth)]
                [GodelQuotation.Numbered.variable_token
                  (GodelQuotation.bound_name targetDepth)]))
      rw [
        fs_zfc_swap_bound_tokens_universal first second targetDepth _
          (Nat.ne_of_lt hFirst) (Nat.ne_of_lt hSecond),
        fs_zfc_swap_bound_tokens_equality,
        fs_zfc_swap_bound_tokens_singleton first second targetDepth
          hDistinct]
      simp [canonical_project_swap_depth,
        Nat.ne_of_gt hFirst, Nat.ne_of_gt hSecond]
  | mem left right =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hLeft :=
        fs_project_renamed_term_token_tree_swap
          left sourceMap targetMap hClosed.1 hSwap hDistinct
      have hRight :=
        fs_project_renamed_term_token_tree_swap
          right sourceMap targetMap hClosed.2 hSwap hDistinct
      change
        GodelQuotation.Numbered.membership_tokens
            (fs_project_term_token_tree
              (left.rename targetMap)).tokens
            (fs_project_term_token_tree
              (right.rename targetMap)).tokens =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.membership_tokens
              (fs_project_term_token_tree
                (left.rename sourceMap)).tokens
              (fs_project_term_token_tree
                (right.rename sourceMap)).tokens)
      rw [fs_zfc_swap_bound_tokens_membership]
      simp only [hLeft, hRight]
  | atom symbol hStage arguments =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,
        _root_.YesMetaZFC.SetTheory.Definitional.TermVector.FreeClosed]
        at hClosed
      cases symbol with
      | extensionalEq =>
          have hLeft :=
            fs_project_renamed_term_token_tree_swap
              (arguments 0) sourceMap targetMap
              (hClosed 0) hSwap hDistinct
          have hRight :=
            fs_project_renamed_term_token_tree_swap
              (arguments 1) sourceMap targetMap
              (hClosed 1) hSwap hDistinct
          simp only [
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.get_bind,
            fs_project_hilbert_token_tree,
            fs_raw_hilbert_equality_tokens]
          change
            GodelQuotation.Numbered.equality_tokens
                (fs_project_term_token_tree
                  ((arguments 0).rename targetMap)).tokens
                (fs_project_term_token_tree
                  ((arguments 1).rename targetMap)).tokens =
              fs_zfc_swap_bound_tokens first second
                (GodelQuotation.Numbered.equality_tokens
                  (fs_project_term_token_tree
                    ((arguments 0).rename sourceMap)).tokens
                  (fs_project_term_token_tree
                    ((arguments 1).rename sourceMap)).tokens)
          rw [fs_zfc_swap_bound_tokens_equality]
          simp only [hLeft, hRight]
      | subset =>
          have hLeft :=
            fs_project_renamed_term_token_tree_swap
              (arguments 0) sourceMap targetMap
              (hClosed 0) hSwap hDistinct
          have hRight :=
            fs_project_renamed_term_token_tree_swap
              (arguments 1) sourceMap targetMap
              (hClosed 1) hSwap hDistinct
          simp only [
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
            _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
            _root_.YesMetaZFC.SetTheory.Definitional.TermVector.get_bind,
            fs_project_hilbert_token_tree,
            fs_raw_hilbert_predicate_tokens,
            List.map_cons, List.map_nil]
          change
            GodelQuotation.Numbered.predicate_application_tokens
                1 RelationSymbol.subset.ctorIdx
                [(fs_project_term_token_tree
                    ((arguments 0).rename targetMap)).tokens,
                  (fs_project_term_token_tree
                    ((arguments 1).rename targetMap)).tokens] =
              fs_zfc_swap_bound_tokens first second
                (GodelQuotation.Numbered.predicate_application_tokens
                  1 RelationSymbol.subset.ctorIdx
                  [(fs_project_term_token_tree
                      ((arguments 0).rename sourceMap)).tokens,
                    (fs_project_term_token_tree
                      ((arguments 1).rename sourceMap)).tokens])
          rw [fs_zfc_swap_bound_tokens_predicate]
          simp only [List.map_cons, List.map_nil, hLeft, hRight]
  | neg body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hBody :=
        ih sourceMap targetMap hClosed hFirst hSecond hSwap
      change
        GodelQuotation.Numbered.negation_tokens
            (fs_project_hilbert_token_tree
              (body.rename targetMap)).tokens =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.negation_tokens
              (fs_project_hilbert_token_tree
                (body.rename sourceMap)).tokens)
      rw [fs_zfc_swap_bound_tokens_negation]
      simp only [hBody]
  | conj left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hLeft :=
        ihLeft sourceMap targetMap hClosed.1
          hFirst hSecond hSwap
      have hRight :=
        ihRight sourceMap targetMap hClosed.2
          hFirst hSecond hSwap
      change
        GodelQuotation.Numbered.negation_tokens
            (GodelQuotation.Numbered.implication_tokens
              (fs_project_hilbert_token_tree
                (left.rename targetMap)).tokens
              (GodelQuotation.Numbered.negation_tokens
                (fs_project_hilbert_token_tree
                  (right.rename targetMap)).tokens)) =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.negation_tokens
              (GodelQuotation.Numbered.implication_tokens
                (fs_project_hilbert_token_tree
                  (left.rename sourceMap)).tokens
                (GodelQuotation.Numbered.negation_tokens
                  (fs_project_hilbert_token_tree
                    (right.rename sourceMap)).tokens)))
      rw [fs_zfc_swap_bound_tokens_negation,
        fs_zfc_swap_bound_tokens_implication,
        fs_zfc_swap_bound_tokens_negation]
      simp only [hLeft, hRight]
  | disj left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hLeft :=
        ihLeft sourceMap targetMap hClosed.1
          hFirst hSecond hSwap
      have hRight :=
        ihRight sourceMap targetMap hClosed.2
          hFirst hSecond hSwap
      change
        GodelQuotation.Numbered.implication_tokens
            (GodelQuotation.Numbered.negation_tokens
              (fs_project_hilbert_token_tree
                (left.rename targetMap)).tokens)
            (fs_project_hilbert_token_tree
              (right.rename targetMap)).tokens =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.implication_tokens
              (GodelQuotation.Numbered.negation_tokens
                (fs_project_hilbert_token_tree
                  (left.rename sourceMap)).tokens)
              (fs_project_hilbert_token_tree
                (right.rename sourceMap)).tokens)
      rw [fs_zfc_swap_bound_tokens_implication,
        fs_zfc_swap_bound_tokens_negation]
      simp only [hLeft, hRight]
  | imp left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hLeft :=
        ihLeft sourceMap targetMap hClosed.1
          hFirst hSecond hSwap
      have hRight :=
        ihRight sourceMap targetMap hClosed.2
          hFirst hSecond hSwap
      change
        GodelQuotation.Numbered.implication_tokens
            (fs_project_hilbert_token_tree
              (left.rename targetMap)).tokens
            (fs_project_hilbert_token_tree
              (right.rename targetMap)).tokens =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.implication_tokens
              (fs_project_hilbert_token_tree
                (left.rename sourceMap)).tokens
              (fs_project_hilbert_token_tree
                (right.rename sourceMap)).tokens)
      rw [fs_zfc_swap_bound_tokens_implication]
      simp only [hLeft, hRight]
  | iff left right ihLeft ihRight =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hLeft :=
        ihLeft sourceMap targetMap hClosed.1
          hFirst hSecond hSwap
      have hRight :=
        ihRight sourceMap targetMap hClosed.2
          hFirst hSecond hSwap
      change
        GodelQuotation.Numbered.negation_tokens
            (GodelQuotation.Numbered.implication_tokens
              (GodelQuotation.Numbered.implication_tokens
                (fs_project_hilbert_token_tree
                  (left.rename targetMap)).tokens
                (fs_project_hilbert_token_tree
                  (right.rename targetMap)).tokens)
              (GodelQuotation.Numbered.negation_tokens
                (GodelQuotation.Numbered.implication_tokens
                  (fs_project_hilbert_token_tree
                    (right.rename targetMap)).tokens
                  (fs_project_hilbert_token_tree
                    (left.rename targetMap)).tokens))) =
          fs_zfc_swap_bound_tokens first second
            (GodelQuotation.Numbered.negation_tokens
              (GodelQuotation.Numbered.implication_tokens
                (GodelQuotation.Numbered.implication_tokens
                  (fs_project_hilbert_token_tree
                    (left.rename sourceMap)).tokens
                  (fs_project_hilbert_token_tree
                    (right.rename sourceMap)).tokens)
                (GodelQuotation.Numbered.negation_tokens
                  (GodelQuotation.Numbered.implication_tokens
                    (fs_project_hilbert_token_tree
                      (right.rename sourceMap)).tokens
                    (fs_project_hilbert_token_tree
                      (left.rename sourceMap)).tokens))))
      rw [fs_zfc_swap_bound_tokens_negation,
        fs_zfc_swap_bound_tokens_implication,
        fs_zfc_swap_bound_tokens_implication,
        fs_zfc_swap_bound_tokens_negation,
        fs_zfc_swap_bound_tokens_implication]
      simp only [hLeft, hRight]
  | forallE body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hBody :=
        ih
          (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift sourceMap)
          (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift targetMap)
          hClosed (by omega) (by omega)
          (hSwap.lift hFirst hSecond)
      have hBody' := hBody
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        Function.comp_def] at hBody'
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        Function.comp_def,
        project_lift_bound_renaming,
        fs_project_hilbert_token_tree]
      simp only [fs_raw_hilbert_universal_tokens]
      rw [fs_zfc_swap_bound_tokens_universal
        first second targetDepth _
        (Nat.ne_of_lt hFirst) (Nat.ne_of_lt hSecond)]
      exact congrArg
        (GodelQuotation.Numbered.universal_tokens
          (GodelQuotation.bound_name targetDepth))
        hBody'
  | existsE body ih =>
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed]
        at hClosed
      have hBody :=
        ih
          (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift sourceMap)
          (_root_.YesMetaZFC.SetTheory.BoundEmbedding.lift targetMap)
          hClosed (by omega) (by omega)
          (hSwap.lift hFirst hSecond)
      have hBody' := hBody
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        Function.comp_def] at hBody'
      simp only [
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.rename,
        _root_.YesMetaZFC.SetTheory.Definitional.Formula.bind,
        Function.comp_def,
        project_lift_bound_renaming,
        fs_project_hilbert_token_tree]
      simp only [fs_raw_hilbert_negation_tokens,
        fs_raw_hilbert_universal_tokens]
      rw [fs_zfc_swap_bound_tokens_negation,
        fs_zfc_swap_bound_tokens_universal
          first second targetDepth _
          (Nat.ne_of_lt hFirst) (Nat.ne_of_lt hSecond),
        fs_zfc_swap_bound_tokens_negation]
      exact congrArg
        (fun tokens =>
          GodelQuotation.Numbered.negation_tokens
            (GodelQuotation.Numbered.universal_tokens
              (GodelQuotation.bound_name targetDepth)
              (GodelQuotation.Numbered.negation_tokens tokens)))
        hBody'

/--
自由闭合项目公式沿交换索引图重命名后，Hilbert quotation 由同一三步
bound-name substitution 连接。
-/
theorem fs_embed_project_formula_rename_hilbert_quote_swap
    {originalDepth targetDepth first second : Nat}
    (formula : FsProjectFormula 1 originalDepth)
    (sourceMap targetMap :
      Fin originalDepth → Fin targetDepth)
    (hClosed :
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed
        formula)
    (hFirst : first < targetDepth)
    (hSecond : second < targetDepth)
    (hDistinct : first ≠ second)
    (hSwap :
      CanonicalProjectIndexSwap
        first second sourceMap targetMap) :
    GodelQuotation.Numbered.quote_hilbert_tokens_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name
        (GodelQuotation.canonical_bound_names targetDepth)
        targetDepth
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_formula
            (formula.rename targetMap))) =
      (GodelQuotation.Numbered.quote_hilbert_tokens_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name
        (GodelQuotation.canonical_bound_names targetDepth)
        targetDepth
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_formula
            (formula.rename sourceMap)))).map
          (fs_zfc_swap_bound_tokens first second) := by
  rw [
    fs_project_hilbert_token_tree_tokens
      (formula.rename targetMap) (by simpa using hClosed),
    fs_project_hilbert_token_tree_tokens
      (formula.rename sourceMap) (by simpa using hClosed)]
  simp only [Option.map_some, Option.some.injEq]
  exact fs_project_hilbert_token_tree_rename_swap
    formula sourceMap targetMap hClosed hFirst hSecond hDistinct hSwap

/-! ## replacement 的两张具体索引图 -/

theorem fs_zfc_replacement_first_output_index_shift
    (parameterCount : Nat) :
    CanonicalProjectIndexShift
      (originalDepth := parameterCount + 2)
      (sourceDepth := parameterCount + 2)
      (parameterCount + 2)
      (fun entry : Fin (parameterCount + 2) => entry)
      (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
        parameterCount) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · have hFirst :
        (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
          parameterCount) (0 : Fin (parameterCount + 2)) =
          (1 : Fin (parameterCount + 3)) := by
      unfold _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
      apply Fin.ext
      rfl
    simp [hFirst, canonical_project_shift_depth]
  · refine Fin.cases ?_ (fun parameter => ?_) previous
    · have hSecond :
          (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
            parameterCount) (1 : Fin (parameterCount + 2)) =
            (2 : Fin (parameterCount + 3)) := by
        have hInput :
            (1 : Fin (parameterCount + 2)) =
              (⟨1, by omega⟩ :
                Fin (parameterCount + 2)) := by
          apply Fin.ext
          rfl
        unfold _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
        rw [hInput]
        apply Fin.ext
        rfl
      simp [hSecond, canonical_project_shift_depth]
    · have hBelow :
          parameterCount - parameter.val - 1 <
            parameterCount + 2 := by
        omega
      simp [
        _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput,
        canonical_project_shift_depth_of_lt hBelow]

theorem fs_zfc_replacement_second_output_index_shift
    (parameterCount : Nat) :
    CanonicalProjectIndexShift
      (originalDepth := parameterCount + 2)
      (sourceDepth := parameterCount + 2)
      (parameterCount + 1)
      (fun entry : Fin (parameterCount + 2) => entry)
      (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
        parameterCount) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · simp [
      _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput,
      canonical_project_shift_depth]
  · refine Fin.cases ?_ (fun parameter => ?_) previous
    · have hSecond :
          (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
            parameterCount) (1 : Fin (parameterCount + 2)) =
            (2 : Fin (parameterCount + 3)) := by
        have hInput :
            (1 : Fin (parameterCount + 2)) =
              (⟨1, by omega⟩ :
                Fin (parameterCount + 2)) := by
          apply Fin.ext
          rfl
        unfold _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
        rw [hInput]
        apply Fin.ext
        rfl
      simp [hSecond,
        canonical_project_shift_depth]
    · have hParameterLt :
          parameter.val < parameterCount :=
        parameter.isLt
      have hBelow :
          parameterCount - parameter.val - 1 <
            parameterCount + 1 := by
        omega
      simp [
        _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput,
        canonical_project_shift_depth_of_lt hBelow]

theorem fs_zfc_replacement_image_index_swap
    (parameterCount : Nat) :
    CanonicalProjectIndexSwap
      (parameterCount + 3) (parameterCount + 2)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
        parameterCount)
      (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
        parameterCount) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo,
      _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody,
      canonical_project_swap_depth]
  · refine Fin.cases ?_ (fun parameter => ?_) previous
    · have hSource :
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
            parameterCount) (1 : Fin (parameterCount + 2)) =
            (1 : Fin (parameterCount + 4)) := by
        have hInput :
            (1 : Fin (parameterCount + 2)) =
              (⟨1, by omega⟩ :
                Fin (parameterCount + 2)) := by
          apply Fin.ext
          rfl
        unfold _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
        rw [hInput]
        apply Fin.ext
        rfl
      have hTarget :
          (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
            parameterCount) (1 : Fin (parameterCount + 2)) =
            (0 : Fin (parameterCount + 4)) := by
        have hInput :
            (1 : Fin (parameterCount + 2)) =
              (⟨1, by omega⟩ :
                Fin (parameterCount + 2)) := by
          apply Fin.ext
          rfl
        unfold _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
        rw [hInput]
        apply Fin.ext
        rfl
      simp [hSource, hTarget,
        canonical_project_swap_depth]
    · have hParameterLt :
          parameter.val < parameterCount :=
        parameter.isLt
      have hFirstNe :
          parameterCount - parameter.val - 1 ≠
            parameterCount + 3 := by
        omega
      have hSecondNe :
          parameterCount - parameter.val - 1 ≠
            parameterCount + 2 := by
        omega
      simp [
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo,
        _root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody,
        canonical_project_swap_depth,
        hFirstNe, hSecondNe]

/-! ## replacement 的规范 trace 与 shift 组件 -/

/--
replacement 复用 collection 的两次 cutoff shift，并分别生成唯一性前件的第一、
第二输出。四个对象层条件占用 verifier 的 `22`、`30`、`38`、`46` 段。
-/
theorem fs_zfc_replacement_shift_components
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId) :
    ∃ bodyTrace firstOutputTrace secondOutputTrace
        underOneTrace underTwoTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 2)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
                  parameterCount)))) =
        some firstOutputTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
                  parameterCount)))) =
        some secondOutputTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some underOneTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some underTwoTrace ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (Sₘ(Sₘ(numₘ(parameterCount))))
          bodyTrace.rootCode firstOutputTrace.rootCode
          (base + 22) (base + 23) (base + 24)) ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (Sₘ(numₘ(parameterCount)))
          bodyTrace.rootCode secondOutputTrace.rootCode
          (base + 30) (base + 31) (base + 32)) ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (numₘ(parameterCount))
          bodyTrace.rootCode underOneTrace.rootCode
          (base + 38) (base + 39) (base + 40)) ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (numₘ(parameterCount))
          underOneTrace.rootCode underTwoTrace.rootCode
          (base + 46) (base + 47) (base + 48)) := by
  rcases fs_zfc_collection_binary_shift_components
      schema (base + 21) with
    ⟨bodyTrace, underOneTrace, underTwoTrace,
      hBodyTrace, hUnderOneTrace, hUnderTwoTrace,
      hUnderOneShift, hUnderTwoShift⟩
  let bodyFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula schema.body)
  let firstOutputFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
            parameterCount)))
  let secondOutputFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
            parameterCount)))
  have hFirstOutputFormulaShift :
      CanonicalProjectFormulaShift (parameterCount + 2)
        (parameterCount + 2) bodyFormula firstOutputFormula := by
    simpa [bodyFormula, firstOutputFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 2) => entry)
        (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_replacement_first_output_index_shift parameterCount))
  have hSecondOutputFormulaShift :
      CanonicalProjectFormulaShift (parameterCount + 1)
        (parameterCount + 2) bodyFormula secondOutputFormula := by
    simpa [bodyFormula, secondOutputFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 2) => entry)
        (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_replacement_second_output_index_shift parameterCount))
  rcases CanonicalProjectFormulaShift.trace_from?
      hFirstOutputFormulaShift 0 with
    ⟨rawBodyTrace, firstOutputTrace,
      hRawBodyTrace, hFirstOutputTrace, _⟩
  have hBodyTraceEq : rawBodyTrace = bodyTrace :=
    Option.some.inj (hRawBodyTrace.symm.trans hBodyTrace)
  subst rawBodyTrace
  rcases CanonicalProjectFormulaShift.trace_from?
      hSecondOutputFormulaShift 0 with
    ⟨rawBodyTrace', secondOutputTrace,
      hRawBodyTrace', hSecondOutputTrace, _⟩
  have hBodyTraceEq' : rawBodyTrace' = bodyTrace :=
    Option.some.inj (hRawBodyTrace'.symm.trans hBodyTrace)
  subst rawBodyTrace'
  have hBodyQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 2))
          (parameterCount + 2) bodyFormula =
        some bodyTrace.rootCode := by
    simpa [bodyFormula] using
      canonical_project_hilbert_trace_from?_root_quote hBodyTrace
  have hFirstOutputQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) firstOutputFormula =
        some firstOutputTrace.rootCode := by
    simpa [firstOutputFormula] using
      canonical_project_hilbert_trace_from?_root_quote
        hFirstOutputTrace
  have hSecondOutputQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) secondOutputFormula =
        some secondOutputTrace.rootCode := by
    simpa [secondOutputFormula] using
      canonical_project_hilbert_trace_from?_root_quote
        hSecondOutputTrace
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hFirstOutputFormulaShift with
    ⟨bodyTokens, firstOutputTokens,
      hBodyTokens, hFirstOutputTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hSecondOutputFormulaShift with
    ⟨bodyTokens', secondOutputTokens,
      hBodyTokens', hSecondOutputTokens⟩
  have hFirstOutputShift :=
    CanonicalProjectFormulaShift.quote_hilbert_with?_code_condition_with_ids
      hFirstOutputFormulaShift (by omega)
      hBodyTokens hFirstOutputTokens
      hBodyQuote hFirstOutputQuote (base + 22)
  have hSecondOutputShift :=
    CanonicalProjectFormulaShift.quote_hilbert_with?_code_condition_with_ids
      hSecondOutputFormulaShift (by omega)
      hBodyTokens' hSecondOutputTokens
      hBodyQuote hSecondOutputQuote (base + 30)
  exact
    ⟨bodyTrace, firstOutputTrace, secondOutputTrace,
      underOneTrace, underTwoTrace,
      hBodyTrace, hFirstOutputTrace, hSecondOutputTrace,
      hUnderOneTrace, hUnderTwoTrace,
      fs_zfc_support_raw_derives_of_godel_quotation hFirstOutputShift,
      fs_zfc_support_raw_derives_of_godel_quotation hSecondOutputShift,
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hUnderOneShift,
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hUnderTwoShift⟩

/-! ## 三步捕获规避 substitution 组件 -/

private theorem fs_zfc_support_raw_code_substitution_spec_of_tokens
    (sourceCode boundCode replacementCode candidateCode : SetTerm)
    (sourceTokens : List Nat)
    (boundToken : Nat)
    (replacementTokens : List Nat)
    (hSourceCode :
      GodelQuotation.Numbered.CodeBoundary sourceCode)
    (hBoundCode :
      GodelQuotation.Numbered.CodeBoundary boundCode)
    (hReplacementCode :
      GodelQuotation.Numbered.CodeBoundary replacementCode)
    (hCandidateCode :
      GodelQuotation.Numbered.CodeBoundary candidateCode)
    (hSourceEquality :
      Derives fs_zfc_support_raw_theory [] (
        GodelQuotation.standard_token_sequence sourceTokens ≐ₘ
          sourceCode))
    (hBoundEquality :
      Derives fs_zfc_support_raw_theory [] (
        GodelQuotation.standard_token_sequence [boundToken] ≐ₘ
          boundCode))
    (hReplacementEquality :
      Derives fs_zfc_support_raw_theory [] (
        GodelQuotation.standard_token_sequence replacementTokens ≐ₘ
          replacementCode))
    (hCandidateEquality :
      Derives fs_zfc_support_raw_theory [] (
        GodelQuotation.standard_token_sequence
            (GodelQuotation.substitute_tokens
              sourceTokens boundToken replacementTokens) ≐ₘ
          candidateCode)) :
    Derives fs_zfc_support_raw_theory [] (
      code_substitution_spec
        sourceCode boundCode replacementCode candidateCode) := by
  have hStandardBoundary (tokens : List Nat) :
      GodelQuotation.Numbered.CodeBoundary
        (GodelQuotation.standard_token_sequence tokens) :=
    ⟨GodelQuotation.standard_token_sequence_admissible tokens,
      GodelQuotation.standard_token_sequence_freeSupport_nil tokens⟩
  have hStandard :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          (GodelQuotation.standard_token_sequence sourceTokens)
          (GodelQuotation.standard_token_sequence [boundToken])
          (GodelQuotation.standard_token_sequence replacementTokens)
          (GodelQuotation.standard_token_sequence
            (GodelQuotation.substitute_tokens
              sourceTokens boundToken replacementTokens))) :=
    fs_zfc_support_raw_derives_of_godel_quotation <|
      GodelQuotation.gq_weaken_standard_sequence <|
        GodelQuotation.standard_token_sequence_code_substitution_spec
          sourceTokens boundToken replacementTokens
  exact GodelQuotation.code_substitution_spec_congr_of_code_equalities
    (GodelQuotation.standard_token_sequence sourceTokens)
    sourceCode
    (GodelQuotation.standard_token_sequence [boundToken])
    boundCode
    (GodelQuotation.standard_token_sequence replacementTokens)
    replacementCode
    (GodelQuotation.standard_token_sequence
      (GodelQuotation.substitute_tokens
        sourceTokens boundToken replacementTokens))
    candidateCode
    (hStandardBoundary sourceTokens) hSourceCode
    (hStandardBoundary [boundToken]) hBoundCode
    (hStandardBoundary replacementTokens) hReplacementCode
    (hStandardBoundary
      (GodelQuotation.substitute_tokens
        sourceTokens boundToken replacementTokens))
    hCandidateCode
    hSourceEquality hBoundEquality
    hReplacementEquality hCandidateEquality hStandard

private theorem
    fs_zfc_support_raw_standard_bound_token_eq_canonical_binder
    (depth : Nat)
    (indexTerm : SetTerm)
    (hIndexBoundary :
      GodelQuotation.Numbered.CodeBoundary indexTerm)
    (hIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(depth) ≐ₘ indexTerm)) :
    Derives fs_zfc_support_raw_theory [] (
      GodelQuotation.standard_token_sequence
          [GodelQuotation.Numbered.variable_token
            (GodelQuotation.bound_name depth)] ≐ₘ
        canonical_binder_variable_code_term indexTerm) := by
  have hStandardNamed :
      Derives GodelQuotation.godel_quotation_theory [] (
        GodelQuotation.standard_token_sequence
            [GodelQuotation.Numbered.variable_token
              (GodelQuotation.bound_name depth)] ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name depth)) :=
    Metatheory.Derives.equality_symm <|
      GodelQuotation.named_variable_code_eq_standard_token_sequence
        (GodelQuotation.bound_name depth)
  have hNamedCanonical :
      Derives GodelQuotation.godel_quotation_theory [] (
        GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name depth) ≐ₘ
          canonical_binder_variable_code_term (numₘ(depth))) :=
    canonical_binder_variable_code_numeral_derives depth
  have hCanonicalIndex :=
    canonical_binder_variable_code_term_congr_of_equality
      (numₘ(depth)) indexTerm
      (finite_numeral_term_admissible depth)
      hIndexBoundary.1 hIndex
  exact fs_zfc_support_raw_derives_of_godel_quotation <|
    Metatheory.Derives.equality_trans hStandardNamed <|
      Metatheory.Derives.equality_trans
        hNamedCanonical hCanonicalIndex

/--
`binaryUnderTwo` 公式的 token 串按 output→temporary、input→output、
temporary→input 三步替换后，得到 `imageBody` 公式的规范 quotation。
-/
theorem fs_zfc_replacement_substitution_components
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {underTwoTrace : CanonicalProjectTrace}
    (hUnderTwoTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some underTwoTrace) :
    ∃ temporaryCode swappedInputCode imageTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
                  parameterCount)))) =
        some imageTrace ∧
      GodelQuotation.Numbered.CodeBoundary temporaryCode ∧
      GodelQuotation.Numbered.CodeBoundary swappedInputCode ∧
      GodelQuotation.Numbered.CodeBoundary imageTrace.rootCode ∧
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          underTwoTrace.rootCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          temporaryCode) ∧
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          temporaryCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(numₘ(parameterCount)))))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
          swappedInputCode) ∧
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          swappedInputCode
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(numₘ(parameterCount)))))
          imageTrace.rootCode) := by
  let sourceFormula : FsProjectFormula 1 (parameterCount + 4) :=
    schema.body.rename
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
        parameterCount)
  let imageFormula : FsProjectFormula 1 (parameterCount + 4) :=
    schema.body.rename
      (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
        parameterCount)
  let sourceTokens : List Nat :=
    (fs_project_hilbert_token_tree sourceFormula).tokens
  let outputToken : Nat :=
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name (parameterCount + 3))
  let inputToken : Nat :=
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name (parameterCount + 2))
  let temporaryToken : Nat :=
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.free_name 0)
  let temporaryTokens : List Nat :=
    GodelQuotation.substitute_tokens
      sourceTokens outputToken [temporaryToken]
  let swappedInputTokens : List Nat :=
    GodelQuotation.substitute_tokens
      temporaryTokens inputToken [outputToken]
  let imageTokens : List Nat :=
    GodelQuotation.substitute_tokens
      swappedInputTokens temporaryToken [inputToken]
  let temporaryCode : SetTerm :=
    GodelQuotation.standard_token_sequence temporaryTokens
  let swappedInputCode : SetTerm :=
    GodelQuotation.standard_token_sequence swappedInputTokens
  rcases fs_embed_project_formula_hilbert_trace?_exists
      imageFormula (by simpa [imageFormula] using schema.freeClosed) with
    ⟨imageTrace, hImageTrace⟩
  have hImageTokenEquality :
      (fs_project_hilbert_token_tree imageFormula).tokens =
        imageTokens := by
    have hSwap :=
      fs_project_hilbert_token_tree_rename_swap
        schema.body
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
          parameterCount)
        (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
          parameterCount)
        schema.freeClosed (by omega) (by omega) (by omega)
        (fs_zfc_replacement_image_index_swap parameterCount)
    simpa [sourceFormula, imageFormula, sourceTokens,
      temporaryTokens, swappedInputTokens, imageTokens,
      outputToken, inputToken, temporaryToken,
      fs_zfc_swap_bound_tokens] using hSwap
  have hSourceTokens :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (parameterCount + 4))
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula sourceFormula)) =
        some sourceTokens := by
    simpa [sourceTokens] using
      fs_project_hilbert_token_tree_tokens
        sourceFormula
        (by simpa [sourceFormula] using schema.freeClosed)
  have hSourceQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (parameterCount + 4))
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula sourceFormula)) =
        some underTwoTrace.rootCode := by
    simpa [sourceFormula] using
      canonical_project_hilbert_trace_from?_root_quote hUnderTwoTrace
  have hSourceRootEquality :
      Derives fs_zfc_support_raw_theory [] (
        underTwoTrace.rootCode ≐ₘ
          GodelQuotation.standard_token_sequence sourceTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation <|
      GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name GodelQuotation.bound_name
        hSourceTokens hSourceQuote
  have hImageTokens :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (parameterCount + 4))
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula imageFormula)) =
        some (fs_project_hilbert_token_tree imageFormula).tokens :=
    fs_project_hilbert_token_tree_tokens
      imageFormula
      (by simpa [imageFormula] using schema.freeClosed)
  have hImageQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names (parameterCount + 4))
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula imageFormula)) =
        some imageTrace.rootCode := by
    simpa [imageFormula] using
      canonical_project_hilbert_trace_from?_root_quote hImageTrace
  have hImageRootEquality :
      Derives fs_zfc_support_raw_theory [] (
        imageTrace.rootCode ≐ₘ
          GodelQuotation.standard_token_sequence imageTokens) := by
    have hEquality :=
      fs_zfc_support_raw_derives_of_godel_quotation <|
        GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
          GodelQuotation.free_name GodelQuotation.bound_name
          hImageTokens hImageQuote
    simpa [hImageTokenEquality] using hEquality
  have hInputBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(numₘ(parameterCount))))) := by
    constructor
    · exact canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (finite_numeral_term_admissible parameterCount)))
    · simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hOutputBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))) := by
    constructor
    · exact canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (successor_term_admissible _
              (finite_numeral_term_admissible parameterCount))))
    · simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hInputIndexBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (Sₘ(Sₘ(numₘ(parameterCount)))) := by
    constructor
    · exact successor_term_admissible _
        (successor_term_admissible _
          (finite_numeral_term_admissible parameterCount))
    · simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hOutputIndexBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))) := by
    constructor
    · exact successor_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (finite_numeral_term_admissible parameterCount)))
    · simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hTemporaryBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name 0)) :=
    ⟨variable_code_term_admissible
        (numₘ(GodelQuotation.free_name 0))
        (finite_numeral_term_admissible
          (GodelQuotation.free_name 0)),
      GodelQuotation.named_variable_code_freeSupport
        (GodelQuotation.free_name 0)⟩
  have hSourceBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hUnderTwoTrace
  have hImageBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hImageTrace
  have hStandardBoundary (tokens : List Nat) :
      GodelQuotation.Numbered.CodeBoundary
        (GodelQuotation.standard_token_sequence tokens) :=
    ⟨GodelQuotation.standard_token_sequence_admissible tokens,
      GodelQuotation.standard_token_sequence_freeSupport_nil tokens⟩
  have hInputIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 2) ≐ₘ
          Sₘ(Sₘ(numₘ(parameterCount)))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(Sₘ(numₘ(parameterCount)))))
  have hOutputIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 3) ≐ₘ
          Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
  have hInputStandard :=
    fs_zfc_support_raw_standard_bound_token_eq_canonical_binder
      (parameterCount + 2)
      (Sₘ(Sₘ(numₘ(parameterCount))))
      hInputIndexBoundary hInputIndex
  have hOutputStandard :=
    fs_zfc_support_raw_standard_bound_token_eq_canonical_binder
      (parameterCount + 3)
      (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))
      hOutputIndexBoundary hOutputIndex
  have hTemporaryStandard :
      Derives fs_zfc_support_raw_theory [] (
        GodelQuotation.standard_token_sequence [temporaryToken] ≐ₘ
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0)) := by
    exact fs_zfc_support_raw_derives_of_godel_quotation <|
      Metatheory.Derives.equality_symm <| by
        simpa [temporaryToken] using
          GodelQuotation.named_variable_code_eq_standard_token_sequence
            (GodelQuotation.free_name 0)
  have hFirstSpec :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          underTwoTrace.rootCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          temporaryCode) := by
    apply fs_zfc_support_raw_code_substitution_spec_of_tokens
      underTwoTrace.rootCode
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.free_name 0))
      temporaryCode sourceTokens outputToken [temporaryToken]
      hSourceBoundary hOutputBoundary hTemporaryBoundary
      (hStandardBoundary temporaryTokens)
    · exact Metatheory.Derives.equality_symm hSourceRootEquality
    · simpa [outputToken] using hOutputStandard
    · exact hTemporaryStandard
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) temporaryCode
  have hSecondSpec :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          temporaryCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(numₘ(parameterCount)))))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
          swappedInputCode) := by
    apply fs_zfc_support_raw_code_substitution_spec_of_tokens
      temporaryCode
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(numₘ(parameterCount)))))
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
      swappedInputCode temporaryTokens inputToken [outputToken]
      (hStandardBoundary temporaryTokens)
      hInputBoundary hOutputBoundary
      (hStandardBoundary swappedInputTokens)
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) temporaryCode
    · simpa [inputToken] using hInputStandard
    · simpa [outputToken] using hOutputStandard
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) swappedInputCode
  have hThirdSpec :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          swappedInputCode
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(numₘ(parameterCount)))))
          imageTrace.rootCode) := by
    apply fs_zfc_support_raw_code_substitution_spec_of_tokens
      swappedInputCode
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.free_name 0))
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(numₘ(parameterCount)))))
      imageTrace.rootCode swappedInputTokens temporaryToken [inputToken]
      (hStandardBoundary swappedInputTokens)
      hTemporaryBoundary hInputBoundary hImageBoundary
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) swappedInputCode
    · exact hTemporaryStandard
    · simpa [inputToken] using hInputStandard
    · exact Metatheory.Derives.equality_symm hImageRootEquality
  exact
    ⟨temporaryCode, swappedInputCode, imageTrace,
      hImageTrace,
      hStandardBoundary temporaryTokens,
      hStandardBoundary swappedInputTokens,
      hImageBoundary,
      hFirstSpec, hSecondSpec, hThirdSpec⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
