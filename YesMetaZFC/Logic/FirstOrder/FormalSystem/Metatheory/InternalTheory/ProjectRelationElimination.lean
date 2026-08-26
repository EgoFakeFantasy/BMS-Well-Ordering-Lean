import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ProjectFunctionElimination
import YesMetaZFC.SetTheory.Language

/-!
# Project 基础理论的关系符号消去

本模块承接 `ProjectFunctionElimination` 的无函数中间签名，并把公式进一步翻译到
纯集合论语言 `ℒ`：

* 隶属关系原样保留；
* 子集关系展开为 `∀ z, z ∈ x → z ∈ y`；
* 其余关系符号暂时送到假命题，后续由各自的定义插件替换。

为避免子集展开引入的量词捕获源自由变量，目标自由变量 `0` 专作定义见证，源自由
变量 `i` 统一送到 `i + 1`。这一层仍是纯句法翻译，不调用模型、满足关系或完备性。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProjectRelationElimination

open Nonlogical.BasicSetTheory

set_option autoImplicit false

abbrev SourceSignature :=
  ProjectFunctionElimination.signature

abbrev SourceTerm := Term SourceSignature
abbrev SourceFormula := Formula SourceSignature
abbrev SourceTheory := Theory SourceSignature

abbrev PureSignature :=
  YesMetaZFC.SetTheory.PureSetLanguage

abbrev PureTerm := Term PureSignature
abbrev PureFormula := Formula PureSignature
abbrev PureTheory := Theory PureSignature

/-- 把中间签名的单 sort scope 搬到纯集合论签名。 -/
def scope (source : Scope SourceSignature) :
    Scope PureSignature :=
  fun _ => source SetSort.set

@[simp]
theorem scope_push (source : Scope SourceSignature) :
    scope (Scope.push source SetSort.set) =
      Scope.push (scope source)
        YesMetaZFC.SetTheory.SetSort.set := by
  funext sort
  cases sort
  simp [scope, Scope.push]

/-- 纯集合论中的 bound 变量。 -/
def bound (index : Nat) : PureTerm :=
  .var (.bvar YesMetaZFC.SetTheory.SetSort.set index)

/-- 纯集合论中的自由变量。 -/
def free (id : FreeVarId) : PureTerm :=
  .var (.fvar YesMetaZFC.SetTheory.SetSort.set id)

/-- 中间项只含变量；源自由变量整体平移一位。 -/
def term : SourceTerm → PureTerm
  | .var (.bvar _ index) =>
      bound index
  | .var (.fvar _ id) =>
      free (id + 1)
  | .app symbol _ =>
      nomatch symbol

/-- 变量翻译保持 sort。 -/
theorem term_well_sorted
    {source : SourceTerm}
    (hSource : TermWellSorted source SetSort.set) :
    TermWellSorted (term source)
      YesMetaZFC.SetTheory.SetSort.set := by
  cases hSource with
  | bvar _ index =>
      exact TermWellSorted.bvar
        (σ := PureSignature)
        YesMetaZFC.SetTheory.SetSort.set index
  | fvar _ id =>
      exact TermWellSorted.fvar
        (σ := PureSignature)
        YesMetaZFC.SetTheory.SetSort.set (id + 1)
  | app symbol =>
      exact nomatch symbol

/-- 变量翻译保持任意单 sort bound scope。 -/
theorem term_scoped
    {sourceScope : Scope SourceSignature}
    {source : SourceTerm}
    (hSource : TermScoped sourceScope source) :
    TermScoped (scope sourceScope) (term source) := by
  cases hSource with
  | bvar hIndex =>
      exact TermScoped.bvar hIndex
  | fvar _ id =>
      exact TermScoped.fvar
        (σ := PureSignature)
        YesMetaZFC.SetTheory.SetSort.set (id + 1)
  | app symbol =>
      exact nomatch symbol

/-- 变量翻译保持 bound-closed。 -/
theorem term_bound_closed
    {source : SourceTerm}
    (hSource : Term.BoundClosed source) :
    Term.BoundClosed (term source) := by
  simpa [Term.BoundClosed, scope, Scope.empty] using
    term_scoped hSource

/-- 子集定义保留的自由变量 `0` 不出现在任何翻译项中。 -/
theorem term_reserved_fresh (source : SourceTerm) :
    (YesMetaZFC.SetTheory.SetSort.set, 0) ∉
      Term.freeSupport (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          exact List.not_mem_nil
      | fvar sort id =>
          cases sort
          intro hMember
          have hEqual :=
            congrArg Prod.snd
              (List.mem_singleton.mp hMember)
          simp at hEqual
  | app symbol arguments =>
      exact nomatch symbol

/-- 源自由变量的新鲜性在平移后保持。 -/
theorem term_fresh
    (id : FreeVarId) (source : SourceTerm)
    (hFresh :
      (SetSort.set, id) ∉ Term.freeSupport source) :
    (YesMetaZFC.SetTheory.SetSort.set, id + 1) ∉
      Term.freeSupport (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          exact List.not_mem_nil
      | fvar sort sourceId =>
          cases sort
          have hId : sourceId ≠ id := by
            intro hEqual
            subst sourceId
            exact hFresh <| List.mem_singleton.mpr rfl
          intro hMember
          have hEqual :=
            congrArg Prod.snd
              (List.mem_singleton.mp hMember)
          exact hId <|
            (Nat.add_right_cancel hEqual).symm
  | app symbol arguments =>
      exact nomatch symbol

/-- 变量翻译与打开 bound 变量交换。 -/
theorem term_openAt
    (depth : Nat) (replacement source : SourceTerm) :
    term
        (Term.openAt SetSort.set depth replacement source) =
      Term.openAt YesMetaZFC.SetTheory.SetSort.set depth
        (term replacement) (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hEqual : index = depth
          · subst index
            simp [term, bound, Term.openAt]
          · by_cases hAbove : depth < index
            · simp [term, bound, Term.openAt,
                hEqual, hAbove]
            · simp [term, bound, Term.openAt,
                hEqual, hAbove]
      | fvar sort id =>
          cases sort
          simp [term, free, Term.openAt]
  | app symbol arguments =>
      exact nomatch symbol

/-- 变量翻译与关闭源自由变量交换。 -/
theorem term_closeFreeAt
    (id : FreeVarId) (depth : Nat)
    (source : SourceTerm) :
    term
        (Term.closeFreeAt SetSort.set id depth source) =
      Term.closeFreeAt YesMetaZFC.SetTheory.SetSort.set
        (id + 1)
        depth (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hClose : depth ≤ index
          · simp [term, bound, Term.closeFreeAt, hClose]
          · simp [term, bound, Term.closeFreeAt, hClose]
      | fvar sort sourceId =>
          cases sort
          by_cases hId : sourceId = id
          · subst sourceId
            simp [term, bound, free, Term.closeFreeAt]
          · simp [term, free,
              Term.closeFreeAt, hId]
  | app symbol arguments =>
      exact nomatch symbol

/-- 变量翻译与源自由变量替换交换。 -/
theorem term_substituteFree
    (id : FreeVarId)
    (replacement source : SourceTerm) :
    term
        (Term.substituteFree SetSort.set id
          replacement source) =
      Term.substituteFree YesMetaZFC.SetTheory.SetSort.set
        (id + 1)
        (term replacement) (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          simp [term, bound, Term.substituteFree]
      | fvar sort sourceId =>
          cases sort
          by_cases hId : sourceId = id
          · subst sourceId
            simp [term, free, Term.substituteFree]
          · simp [term, free,
              Term.substituteFree, hId]
  | app symbol arguments =>
      exact nomatch symbol

/-- 纯集合论中的隶属原子。 -/
def mem (left right : PureTerm) : PureFormula :=
  .rel YesMetaZFC.SetTheory.RelationSymbol.membership
    [left, right]

/-- 子集关系的纯隶属展开；自由变量 `0` 是局部定义见证。 -/
def subset (left right : PureTerm) : PureFormula :=
  .forallE YesMetaZFC.SetTheory.SetSort.set <|
    Formula.closeFreeAt
      YesMetaZFC.SetTheory.SetSort.set 0 0 <|
      .imp (mem (free 0) left)
        (mem (free 0) right)

/-- 当前基础层的关系翻译。 -/
def atom
    (relation : RelationSymbol)
    (arguments : List SourceTerm) :
    PureFormula :=
  if relation = .membership then
    match arguments with
    | [left, right] => mem (term left) (term right)
    | _ => .falsum
  else if relation = .subset then
    match arguments with
    | [left, right] => subset (term left) (term right)
    | _ => .falsum
  else
    .falsum

/-- 关系公式到纯集合论公式的递归翻译。 -/
def formula : SourceFormula → PureFormula
  | .falsum =>
      .falsum
  | .truth =>
      .truth
  | .rel relation arguments =>
      atom relation arguments
  | .equal left right =>
      .equal (term left) (term right)
  | .neg body =>
      .neg (formula body)
  | .conj left right =>
      .conj (formula left) (formula right)
  | .disj left right =>
      .disj (formula left) (formula right)
  | .imp left right =>
      .imp (formula left) (formula right)
  | .iff left right =>
      .iff (formula left) (formula right)
  | .forallE _ body =>
      .forallE YesMetaZFC.SetTheory.SetSort.set
        (formula body)
  | .existsE _ body =>
      .existsE YesMetaZFC.SetTheory.SetSort.set
        (formula body)

private theorem pair_well_sorted
    (left right : PureTerm)
    (hLeft :
      TermWellSorted left
        YesMetaZFC.SetTheory.SetSort.set)
    (hRight :
      TermWellSorted right
        YesMetaZFC.SetTheory.SetSort.set) :
    ArgsWellSorted [left, right]
      [YesMetaZFC.SetTheory.SetSort.set,
        YesMetaZFC.SetTheory.SetSort.set] :=
  .cons hLeft (.cons hRight .nil)

private theorem pair_scoped
    {targetScope : Scope PureSignature}
    (left right : PureTerm)
    (hLeft : TermScoped targetScope left)
    (hRight : TermScoped targetScope right) :
    ∀ candidate, candidate ∈ [left, right] →
      TermScoped targetScope candidate := by
  intro candidate hCandidate
  rcases List.mem_cons.mp hCandidate with
    rfl | hCandidate
  · exact hLeft
  · have hEqual : candidate = right :=
      List.mem_singleton.mp hCandidate
    subst candidate
    exact hRight

private theorem fresh_append
    {α : Type} {value : α} {left right : List α}
    (hLeft : value ∉ left)
    (hRight : value ∉ right) :
    value ∉ left ++ right := by
  intro hMember
  rcases List.mem_append.mp hMember with
    hMember | hMember
  · exact hLeft hMember
  · exact hRight hMember

private theorem mem_well_formed
    (left right : PureTerm)
    (hLeft :
      TermWellSorted left
        YesMetaZFC.SetTheory.SetSort.set)
    (hRight :
      TermWellSorted right
        YesMetaZFC.SetTheory.SetSort.set) :
    FormulaWellFormed (mem left right) := by
  apply FormulaWellFormed.rel
  simpa [PureSignature,
    YesMetaZFC.SetTheory.PureSetLanguage,
    YesMetaZFC.SetTheory.signature] using
    pair_well_sorted left right hLeft hRight

private theorem mem_scoped
    {targetScope : Scope PureSignature}
    (left right : PureTerm)
    (hLeft : TermScoped targetScope left)
    (hRight : TermScoped targetScope right) :
    FormulaScoped targetScope (mem left right) := by
  unfold mem
  exact FormulaScoped.rel
    YesMetaZFC.SetTheory.RelationSymbol.membership
    [left, right]
    (pair_scoped left right hLeft hRight)

private theorem source_pair
    {arguments : List SourceTerm}
    (hArguments :
      ArgsWellSorted arguments
        [SetSort.set, SetSort.set]) :
    ∃ left right,
      arguments = [left, right] ∧
        TermWellSorted left SetSort.set ∧
        TermWellSorted right SetSort.set := by
  cases hArguments with
  | cons hLeft hTail =>
      cases hTail with
      | cons hRight hNil =>
          cases hNil
          exact ⟨_, _, rfl, hLeft, hRight⟩

/-- 子集展开保持 sort/arity 良构性。 -/
theorem subset_well_formed
    (left right : PureTerm)
    (hLeft :
      TermWellSorted left
        YesMetaZFC.SetTheory.SetSort.set)
    (hRight :
      TermWellSorted right
        YesMetaZFC.SetTheory.SetSort.set) :
    FormulaWellFormed (subset left right) := by
  apply FormulaWellFormed.forallE
  apply Formula.FormulaWellFormed.wf_closeFreeAt
  exact FormulaWellFormed.imp
    (mem_well_formed (free 0) left
      (by
        simpa [free] using
          (TermWellSorted.fvar
            (σ := PureSignature)
            YesMetaZFC.SetTheory.SetSort.set 0))
      hLeft)
    (mem_well_formed (free 0) right
      (by
        simpa [free] using
          (TermWellSorted.fvar
            (σ := PureSignature)
            YesMetaZFC.SetTheory.SetSort.set 0))
      hRight)

/-- 子集展开保持任意单 sort bound scope。 -/
theorem subset_scoped
    {targetScope : Scope PureSignature}
    (left right : PureTerm)
    (hLeft : TermScoped targetScope left)
    (hRight : TermScoped targetScope right) :
    FormulaScoped targetScope (subset left right) := by
  apply FormulaScoped.forallE
  apply Formula.FormulaScoped.sc_closeFreeAt
  · exact FormulaScoped.imp
      (mem_scoped (free 0) left
        (by
          simpa [free] using
            (TermScoped.fvar
              (σ := PureSignature)
              YesMetaZFC.SetTheory.SetSort.set 0 :
                TermScoped targetScope
                  (.var (.fvar
                    YesMetaZFC.SetTheory.SetSort.set 0))))
        hLeft)
      (mem_scoped (free 0) right
        (by
          simpa [free] using
            (TermScoped.fvar
              (σ := PureSignature)
              YesMetaZFC.SetTheory.SetSort.set 0 :
                TermScoped targetScope
                  (.var (.fvar
                    YesMetaZFC.SetTheory.SetSort.set 0))))
        hRight)
  · exact Nat.zero_le _

/-- 当前关系翻译保持良构性。 -/
theorem atom_well_formed
    {relation : RelationSymbol}
    {arguments : List SourceTerm}
    (hArguments :
      ArgsWellSorted arguments
        (SourceSignature.relDomain relation)) :
    FormulaWellFormed (atom relation arguments) := by
  by_cases hMembership : relation = .membership
  · subst relation
    change
      ArgsWellSorted arguments
        [SetSort.set, SetSort.set] at hArguments
    rcases source_pair hArguments with
      ⟨left, right, rfl, hLeft, hRight⟩
    simpa [atom] using
      mem_well_formed (term left) (term right)
        (term_well_sorted hLeft)
        (term_well_sorted hRight)
  · by_cases hSubset : relation = .subset
    · subst relation
      change
        ArgsWellSorted arguments
          [SetSort.set, SetSort.set] at hArguments
      rcases source_pair hArguments with
        ⟨left, right, rfl, hLeft, hRight⟩
      simpa [atom, hMembership] using
        subset_well_formed (term left) (term right)
          (term_well_sorted hLeft)
          (term_well_sorted hRight)
    · simpa [atom, hMembership, hSubset] using
        (FormulaWellFormed.falsum :
          FormulaWellFormed
            (Formula.falsum : PureFormula))

/-- 当前关系翻译保持 bound scope。 -/
theorem atom_scoped
    {sourceScope : Scope SourceSignature}
    (relation : RelationSymbol)
    (arguments : List SourceTerm)
    (hArguments :
      ∀ source, source ∈ arguments →
        TermScoped sourceScope source) :
    FormulaScoped (scope sourceScope)
      (atom relation arguments) := by
  by_cases hMembership : relation = .membership
  · subst relation
    cases arguments with
    | nil =>
        exact FormulaScoped.falsum
    | cons left tail =>
        cases tail with
        | nil =>
            exact FormulaScoped.falsum
        | cons right rest =>
            cases rest with
            | nil =>
                simpa [atom] using
                  mem_scoped (term left) (term right)
                    (term_scoped <|
                      hArguments left (by simp))
                    (term_scoped <|
                      hArguments right (by simp))
            | cons extra rest =>
                exact FormulaScoped.falsum
  · by_cases hSubset : relation = .subset
    · subst relation
      cases arguments with
      | nil =>
          exact FormulaScoped.falsum
      | cons left tail =>
          cases tail with
          | nil =>
              exact FormulaScoped.falsum
          | cons right rest =>
              cases rest with
              | nil =>
                  simpa [atom, hMembership] using
                    subset_scoped (term left) (term right)
                      (term_scoped <|
                        hArguments left (by simp))
                      (term_scoped <|
                        hArguments right (by simp))
              | cons extra rest =>
                  exact FormulaScoped.falsum
    · simpa [atom, hMembership, hSubset] using
        (FormulaScoped.falsum :
          FormulaScoped (scope sourceScope)
            (Formula.falsum : PureFormula))

/-- 关系翻译保持公式的 sort/arity 良构性。 -/
theorem formula_well_formed
    {source : SourceFormula}
    (hSource : FormulaWellFormed source) :
    FormulaWellFormed (formula source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation hArguments =>
      exact atom_well_formed hArguments
  | equal hLeft hRight =>
      exact .equal
        (term_well_sorted hLeft)
        (term_well_sorted hRight)
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .conj ihLeft ihRight
  | disj hLeft hRight ihLeft ihRight =>
      exact .disj ihLeft ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .iff ihLeft ihRight
  | forallE sort hBody ih =>
      exact .forallE
        YesMetaZFC.SetTheory.SetSort.set ih
  | existsE sort hBody ih =>
      exact .existsE
        YesMetaZFC.SetTheory.SetSort.set ih

/-- 关系翻译保持公式的 bound scope。 -/
theorem formula_scoped
    {sourceScope : Scope SourceSignature}
    {source : SourceFormula}
    (hSource : FormulaScoped sourceScope source) :
    FormulaScoped (scope sourceScope)
      (formula source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments hArguments =>
      exact atom_scoped relation arguments hArguments
  | equal hLeft hRight =>
      exact .equal
        (term_scoped hLeft)
        (term_scoped hRight)
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .conj ihLeft ihRight
  | disj hLeft hRight ihLeft ihRight =>
      exact .disj ihLeft ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .iff ihLeft ihRight
  | forallE sort hBody ih =>
      cases sort
      apply FormulaScoped.forallE
      simpa only [scope_push] using ih
  | existsE sort hBody ih =>
      cases sort
      apply FormulaScoped.existsE
      simpa only [scope_push] using ih

/-- 关系翻译保持 proof-layer admissibility。 -/
theorem formula_admissible
    {source : SourceFormula}
    (hSource : Formula.Admissible source) :
    Formula.Admissible (formula source) :=
  ⟨formula_well_formed hSource.1,
    by
      simpa [scope, Scope.empty] using
        formula_scoped hSource.2⟩

/-- 子集展开关闭了局部见证，因此目标自由变量 `0` 新鲜。 -/
theorem subset_reserved_fresh
    (left right : PureTerm) :
    (YesMetaZFC.SetTheory.SetSort.set, 0) ∉
      Formula.freeSupport (subset left right) := by
  simpa [subset, Formula.freeSupport] using
    Formula.not_mem_freeSupport_closeFreeAt
      YesMetaZFC.SetTheory.SetSort.set 0 0
      (.imp (mem (free 0) left)
        (mem (free 0) right))

/-- 每个原子翻译都对局部定义见证 `0` 新鲜。 -/
theorem atom_reserved_fresh
    (relation : RelationSymbol)
    (arguments : List SourceTerm) :
    (YesMetaZFC.SetTheory.SetSort.set, 0) ∉
      Formula.freeSupport (atom relation arguments) := by
  by_cases hMembership : relation = .membership
  · subst relation
    cases arguments with
    | nil =>
        exact List.not_mem_nil
    | cons left tail =>
        cases tail with
        | nil =>
            exact List.not_mem_nil
        | cons right rest =>
            cases rest with
            | nil =>
                rw [show
                  atom .membership [left, right] =
                    mem (term left) (term right) by
                      simp [atom]]
                simp only [mem, Formula.freeSupport,
                  Term.freeSupportList, List.append_nil]
                exact fresh_append
                  (term_reserved_fresh left)
                  (term_reserved_fresh right)
            | cons extra rest =>
                exact List.not_mem_nil
  · by_cases hSubset : relation = .subset
    · subst relation
      cases arguments with
      | nil =>
          exact List.not_mem_nil
      | cons left tail =>
          cases tail with
          | nil =>
              exact List.not_mem_nil
          | cons right rest =>
              cases rest with
              | nil =>
                  simpa [atom, hMembership] using
                    subset_reserved_fresh
                      (term left) (term right)
              | cons extra rest =>
                  exact List.not_mem_nil
    · rw [show
        atom relation arguments =
          (Formula.falsum : PureFormula) by
            simp [atom, hMembership, hSubset]]
      change
        (YesMetaZFC.SetTheory.SetSort.set, 0) ∉ []
      exact List.not_mem_nil

/-- 整个关系翻译对局部定义见证 `0` 新鲜。 -/
theorem formula_reserved_fresh
    (source : SourceFormula) :
    (YesMetaZFC.SetTheory.SetSort.set, 0) ∉
      Formula.freeSupport (formula source) := by
  induction source with
  | falsum =>
      exact List.not_mem_nil
  | truth =>
      exact List.not_mem_nil
  | rel relation arguments =>
      exact atom_reserved_fresh relation arguments
  | equal left right =>
      change
        (YesMetaZFC.SetTheory.SetSort.set, 0) ∉
          Term.freeSupport (term left) ++
            Term.freeSupport (term right)
      exact fresh_append
        (term_reserved_fresh left)
        (term_reserved_fresh right)
  | neg body ih =>
      exact ih
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      change
        (YesMetaZFC.SetTheory.SetSort.set, 0) ∉
          Formula.freeSupport (formula left) ++
            Formula.freeSupport (formula right)
      exact fresh_append ihLeft ihRight
  | forallE sort body ih
  | existsE sort body ih =>
      exact ih

/-! ## 子集定义 binder 的交换律 -/

/--
两个不同自由变量的关闭可交换；先关闭的 binder 位于外层，因此第二次关闭的深度
增加一位。
-/
theorem term_close_close
    (first second : FreeVarId)
    (firstDepth secondDepth : Nat)
    (source : PureTerm)
    (hDistinct : first ≠ second)
    (hDepth : firstDepth ≤ secondDepth) :
    Term.closeFreeAt YesMetaZFC.SetTheory.SetSort.set
        second (secondDepth + 1)
        (Term.closeFreeAt
          YesMetaZFC.SetTheory.SetSort.set
          first firstDepth source) =
      Term.closeFreeAt YesMetaZFC.SetTheory.SetSort.set
        first firstDepth
        (Term.closeFreeAt
          YesMetaZFC.SetTheory.SetSort.set
          second secondDepth source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hFirst : firstDepth ≤ index
          · by_cases hSecond : secondDepth ≤ index
            · have hFirstSucc :
                  firstDepth ≤ index + 1 := by
                omega
              have hSecondSucc :
                  secondDepth + 1 ≤ index + 1 := by
                omega
              simp [Term.closeFreeAt,
                hFirst, hSecond,
                hFirstSucc, hSecondSucc]
            · have hSecondSucc :
                  ¬ secondDepth + 1 ≤ index + 1 := by
                omega
              simp [Term.closeFreeAt,
                hFirst, hSecond, hSecondSucc]
          · have hSecond : ¬ secondDepth ≤ index := by
              omega
            have hSecondOuter :
                ¬ secondDepth + 1 ≤ index := by
              omega
            simp [Term.closeFreeAt,
              hFirst, hSecond, hSecondOuter]
      | fvar sort id =>
          cases sort
          by_cases hFirst : id = first
          · subst id
            have hOuter :
                ¬ secondDepth + 1 ≤ firstDepth := by
              omega
            simp [Term.closeFreeAt,
              hDistinct, hOuter]
          · by_cases hSecond : id = second
            · subst id
              simp [Term.closeFreeAt,
                hFirst, hDepth]
            · simp [Term.closeFreeAt,
                hFirst, hSecond]
  | app symbol arguments =>
      exact nomatch symbol

/--
打开一个内层 binder 与关闭其外侧的新自由变量交换。replacement 必须
bound-closed 且不含被关闭变量，因而不会被外层关闭改写。
-/
theorem term_open_close
    (closedId : FreeVarId)
    (closedDepth openDepth : Nat)
    (replacement source : PureTerm)
    (hDepth : closedDepth ≤ openDepth)
    (hReplacementClosed :
      Term.BoundClosed replacement)
    (hReplacementFresh :
      (YesMetaZFC.SetTheory.SetSort.set, closedId) ∉
        Term.freeSupport replacement) :
    Term.openAt YesMetaZFC.SetTheory.SetSort.set
        (openDepth + 1) replacement
        (Term.closeFreeAt
          YesMetaZFC.SetTheory.SetSort.set
          closedId closedDepth source) =
      Term.closeFreeAt YesMetaZFC.SetTheory.SetSort.set
        closedId closedDepth
        (Term.openAt
          YesMetaZFC.SetTheory.SetSort.set
          openDepth replacement source) := by
  have hReplacementFixed :
      Term.closeFreeAt
          YesMetaZFC.SetTheory.SetSort.set
          closedId closedDepth replacement =
        replacement :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      YesMetaZFC.SetTheory.SetSort.set
      closedId closedDepth replacement
      hReplacementClosed hReplacementFresh
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hClose : closedDepth ≤ index
          · by_cases hEqual : index = openDepth
            · subst index
              simp [Term.closeFreeAt, Term.openAt,
                hClose, hReplacementFixed]
            · by_cases hAbove : openDepth < index
              · have hOuterEqual :
                    index + 1 ≠ openDepth + 1 := by
                  omega
                have hOuterAbove :
                    openDepth + 1 < index + 1 := by
                  omega
                have hReducedClose :
                    closedDepth ≤ index - 1 := by
                  omega
                have hRestore :
                    index - 1 + 1 = index := by
                  omega
                simp [Term.closeFreeAt, Term.openAt,
                  hClose, hEqual, hAbove,
                  hOuterAbove,
                  hReducedClose, hRestore]
              · have hOuterAbove :
                    ¬ openDepth + 1 < index + 1 := by
                  omega
                simp [Term.closeFreeAt, Term.openAt,
                  hClose, hEqual, hAbove,
                  hOuterAbove]
          · have hNotEqual : index ≠ openDepth := by
              omega
            have hNotAbove : ¬ openDepth < index := by
              omega
            have hOuterEqual :
                index ≠ openDepth + 1 := by
              omega
            have hOuterAbove :
                ¬ openDepth + 1 < index := by
              omega
            simp [Term.closeFreeAt, Term.openAt,
              hClose, hNotEqual, hNotAbove,
              hOuterEqual, hOuterAbove]
      | fvar sort id =>
          cases sort
          by_cases hClosed : id = closedId
          · subst id
            have hNotEqual :
                closedDepth ≠ openDepth + 1 := by
              omega
            have hNotAbove :
                ¬ openDepth + 1 < closedDepth := by
              omega
            simp [Term.closeFreeAt, Term.openAt,
              hNotEqual, hNotAbove]
          · simp [Term.closeFreeAt, Term.openAt,
              hClosed]
  | app symbol arguments =>
      exact nomatch symbol

/-- 公式层的双关闭交换律。 -/
theorem formula_close_close
    (first second : FreeVarId)
    (firstDepth secondDepth : Nat)
    (source : PureFormula)
    (hDistinct : first ≠ second)
    (hDepth : firstDepth ≤ secondDepth) :
    Formula.closeFreeAt
        YesMetaZFC.SetTheory.SetSort.set
        second (secondDepth + 1)
        (Formula.closeFreeAt
          YesMetaZFC.SetTheory.SetSort.set
          first firstDepth source) =
      Formula.closeFreeAt
        YesMetaZFC.SetTheory.SetSort.set
        first firstDepth
        (Formula.closeFreeAt
          YesMetaZFC.SetTheory.SetSort.set
          second secondDepth source) := by
  induction source generalizing
      firstDepth secondDepth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.closeFreeAt,
        List.map_map]
      apply congrArg (Formula.rel relation)
      apply List.map_congr_left
      intro argument hArgument
      simpa only [Function.comp_apply] using
        term_close_close first second
          firstDepth secondDepth argument
          hDistinct hDepth
  | equal left right =>
      simp [Formula.closeFreeAt,
        term_close_close first second
          firstDepth secondDepth left
          hDistinct hDepth,
        term_close_close first second
          firstDepth secondDepth right
          hDistinct hDepth]
  | neg body ih =>
      simp [Formula.closeFreeAt,
        ih firstDepth secondDepth hDepth]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [Formula.closeFreeAt,
        ihLeft firstDepth secondDepth hDepth,
        ihRight firstDepth secondDepth hDepth]
  | forallE sort body ih
  | existsE sort body ih =>
      cases sort
      simpa [Formula.closeFreeAt,
        Formula.next_depth, Nat.add_assoc] using
        ih (firstDepth + 1) (secondDepth + 1)
          (Nat.add_le_add_right hDepth 1)

/-- 公式层的打开/外侧关闭交换律。 -/
theorem formula_open_close
    (closedId : FreeVarId)
    (closedDepth openDepth : Nat)
    (replacement : PureTerm)
    (source : PureFormula)
    (hDepth : closedDepth ≤ openDepth)
    (hReplacementClosed :
      Term.BoundClosed replacement)
    (hReplacementFresh :
      (YesMetaZFC.SetTheory.SetSort.set, closedId) ∉
        Term.freeSupport replacement) :
    Formula.openAt YesMetaZFC.SetTheory.SetSort.set
        (openDepth + 1) replacement
        (Formula.closeFreeAt
          YesMetaZFC.SetTheory.SetSort.set
          closedId closedDepth source) =
      Formula.closeFreeAt
        YesMetaZFC.SetTheory.SetSort.set
        closedId closedDepth
        (Formula.openAt
          YesMetaZFC.SetTheory.SetSort.set
          openDepth replacement source) := by
  induction source generalizing
      closedDepth openDepth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.openAt,
        Formula.closeFreeAt, List.map_map]
      apply congrArg (Formula.rel relation)
      apply List.map_congr_left
      intro argument hArgument
      simpa only [Function.comp_apply] using
        term_open_close closedId
          closedDepth openDepth replacement argument
          hDepth hReplacementClosed hReplacementFresh
  | equal left right =>
      simp [Formula.openAt, Formula.closeFreeAt,
        term_open_close closedId
          closedDepth openDepth replacement left
          hDepth hReplacementClosed hReplacementFresh,
        term_open_close closedId
          closedDepth openDepth replacement right
          hDepth hReplacementClosed hReplacementFresh]
  | neg body ih =>
      simp [Formula.openAt, Formula.closeFreeAt,
        ih closedDepth openDepth hDepth]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft closedDepth openDepth hDepth,
        ihRight closedDepth openDepth hDepth]
  | forallE sort body ih
  | existsE sort body ih =>
      cases sort
      simpa [Formula.openAt, Formula.closeFreeAt,
        Formula.next_depth, Nat.add_assoc] using
        ih (closedDepth + 1) (openDepth + 1)
          (Nat.add_le_add_right hDepth 1)

end ProjectRelationElimination
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
