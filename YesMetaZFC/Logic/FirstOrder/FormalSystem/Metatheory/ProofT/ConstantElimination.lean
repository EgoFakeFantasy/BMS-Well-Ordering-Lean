import YesMetaZFC.Logic.FirstOrder.Hilbert.Adequacy
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-!
# ProofT 零元定义常元消去

本模块处理定义扩张保守性中最先可完全闭合的一步：消去一个零元函数符号。

源自由变量 `i` 统一平移到 `i + 1`，被消去的常元统一替换为保留自由变量 `0`。
因此翻译严格交换打开、关闭与自由替换，并逐项保持十二类 Hilbert 逻辑公理。
若基理论证明翻译后定义公理关于保留变量存在一个见证，则扩张理论的矛盾证明可
通过一次对象层存在消去回传到基理论像。

这一层不使用模型扩张、满足关系、完备性或不可计算选择。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ConstantElimination

universe u v w

set_option autoImplicit false

/-- 待消去的零元函数符号及其结果 sort。 -/
structure Data
    (σ : Signature.{u, v, w})
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] where
  symbol : σ.FuncSymbol
  sort : σ.SortSymbol
  domain_nil : σ.funcDomain symbol = []
  codomain_eq : σ.funcCodomain symbol = sort

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

private theorem append_eq_nil_parts
    {α : Type u} {left right : List α}
    (h : left ++ right = []) :
    left = [] ∧ right = [] := by
  constructor
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro value hValue
    have : value ∈ left ++ right :=
      List.mem_append.mpr (Or.inl hValue)
    rw [h] at this
    exact List.not_mem_nil this
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro value hValue
    have : value ∈ left ++ right :=
      List.mem_append.mpr (Or.inr hValue)
    rw [h] at this
    exact List.not_mem_nil this

/-- 保留变量 `0`；源自由变量从 `1` 开始。 -/
def free_shift (sort : σ.SortSymbol) (id : FreeVarId) :
    Term σ :=
  .var (.fvar sort (id + 1))

/-- 将指定零元常元替换为保留变量 `0`。 -/
def term (D : Data σ) : Term σ → Term σ
  | .var (.bvar sort index) =>
      .var (.bvar sort index)
  | .var (.fvar sort id) =>
      free_shift sort id
  | .app function arguments =>
      if function = D.symbol then
        .var (.fvar D.sort 0)
      else
        .app function (arguments.map (term D))

/-- 项列表逐项执行零元常元消去。 -/
def terms (D : Data σ) (source : List (Term σ)) :
    List (Term σ) :=
  source.map (term D)

/-- 一个项不使用待消去常元。 -/
def TermAvoids (D : Data σ) : Term σ → Prop
  | .var _ =>
      True
  | .app function arguments =>
      function ≠ D.symbol ∧
        ∀ argument, argument ∈ arguments →
          TermAvoids D argument

/-- 一个项列表不使用待消去常元。 -/
def TermsAvoid (D : Data σ) (source : List (Term σ)) : Prop :=
  ∀ argument, argument ∈ source →
    TermAvoids D argument

mutual

/-- 零元常元消去保持项的 sort。 -/
theorem term_well_sorted
    (D : Data σ)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : TermWellSorted source sort) :
    TermWellSorted (term D source) sort := by
  cases hSource with
  | bvar sort index =>
      simpa [term] using
        (TermWellSorted.bvar sort index)
  | fvar sort id =>
      simpa [term, free_shift] using
        (TermWellSorted.fvar sort (id + 1))
  | app function hArguments =>
      by_cases hFunction : function = D.symbol
      · subst function
        simpa [term, D.codomain_eq] using
          (TermWellSorted.fvar D.sort 0)
      · simpa [term, hFunction] using
          (TermWellSorted.app function
            (terms_well_sorted D hArguments))

/-- 零元常元消去逐项保持参数列表的 sort。 -/
theorem terms_well_sorted
    (D : Data σ)
    {source : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSource : ArgsWellSorted source sorts) :
    ArgsWellSorted (terms D source) sorts := by
  cases hSource with
  | nil =>
      exact .nil
  | cons hHead hTail =>
      exact .cons
        (term_well_sorted D hHead)
        (terms_well_sorted D hTail)

end

/-- 零元常元消去保持任意 bound scope。 -/
theorem term_scoped
    (D : Data σ)
    {scope : Scope σ} {source : Term σ}
    (hSource : TermScoped scope source) :
    TermScoped scope (term D source) := by
  induction hSource with
  | bvar hIndex =>
      simpa [term] using
        (TermScoped.bvar hIndex)
  | fvar sort id =>
      simpa [term, free_shift] using
        (TermScoped.fvar
          (ctx := scope) sort (id + 1))
  | app function arguments hArguments ih =>
      by_cases hFunction : function = D.symbol
      · subst function
        simpa [term] using
          (TermScoped.fvar
            (ctx := scope) D.sort 0)
      · simpa [term, hFunction] using
          (TermScoped.app function
            (arguments.map (term D)) <| by
            intro target hTarget
            rcases List.mem_map.mp hTarget with
              ⟨source, hSource, rfl⟩
            exact ih source hSource)

/-- 零元常元消去保持 bound-closed 项。 -/
theorem term_bound_closed
    (D : Data σ) {source : Term σ}
    (hSource : Term.BoundClosed source) :
    Term.BoundClosed (term D source) :=
  term_scoped D hSource

/-- 零元常元消去与打开 bound 变量交换。 -/
theorem term_openAt
    (D : Data σ) (target : σ.SortSymbol)
    (depth : Nat) (replacement source : Term σ) :
    term D
        (Term.openAt target depth replacement source) =
      Term.openAt target depth (term D replacement)
        (term D source) := by
  refine Term.rec
    (motive_1 := fun source =>
      term D
          (Term.openAt target depth replacement source) =
        Term.openAt target depth (term D replacement)
          (term D source))
    (motive_2 := fun source =>
      source.map
          (term D ∘
            Term.openAt target depth replacement) =
        source.map
          (Term.openAt target depth (term D replacement) ∘
            term D))
    ?_ ?_ ?_ ?_ source
  · intro value
    cases value with
    | bvar sort index =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hIndex : index = depth
          · subst index
            simp [term, Term.openAt]
          · by_cases hAbove : depth < index
            · simp [term, Term.openAt,
                hIndex, hAbove]
            · simp [term, Term.openAt,
                hIndex, hAbove]
        · simp [term, Term.openAt, hSort]
    | fvar sort id =>
        simp [term, free_shift, Term.openAt]
  · intro function arguments ih
    by_cases hFunction : function = D.symbol
    · simp [term, Term.openAt, hFunction]
    · simpa [term, Term.openAt, hFunction,
        List.map_map, Function.comp_def] using
          congrArg (Term.app function) ih
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

/-- 零元常元消去与关闭源自由变量交换。 -/
theorem term_closeFreeAt
    (D : Data σ) (target : σ.SortSymbol)
    (id : FreeVarId) (depth : Nat) (source : Term σ) :
    term D
        (Term.closeFreeAt target id depth source) =
      Term.closeFreeAt target (id + 1) depth
        (term D source) := by
  refine Term.rec
    (motive_1 := fun source =>
      term D
          (Term.closeFreeAt target id depth source) =
        Term.closeFreeAt target (id + 1) depth
          (term D source))
    (motive_2 := fun source =>
      source.map
          (term D ∘
            Term.closeFreeAt target id depth) =
        source.map
          (Term.closeFreeAt target (id + 1) depth ∘
            term D))
    ?_ ?_ ?_ ?_ source
  · intro value
    cases value with
    | bvar sort index =>
        by_cases hClose : sort = target ∧ depth ≤ index
        · simp [term, Term.closeFreeAt, hClose]
        · simp [term, Term.closeFreeAt, hClose]
    | fvar sort sourceId =>
        by_cases hClose : sort = target ∧ sourceId = id
        · rcases hClose with ⟨rfl, rfl⟩
          simp [term, free_shift, Term.closeFreeAt]
        · have hShift :
              ¬(sort = target ∧ sourceId + 1 = id + 1) := by
            intro h
            exact hClose ⟨h.1,
              Nat.add_right_cancel h.2⟩
          simp [term, free_shift, Term.closeFreeAt,
            hClose]
  · intro function arguments ih
    by_cases hFunction : function = D.symbol
    · have hReserved :
          ¬(D.sort = target ∧ 0 = id + 1) := by
        simp
      simp [term, Term.closeFreeAt,
        hFunction]
    · simpa [term, Term.closeFreeAt, hFunction,
        List.map_map, Function.comp_def] using
          congrArg (Term.app function) ih
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

/-- 零元常元消去与源自由变量替换交换。 -/
theorem term_substituteFree
    (D : Data σ) (target : σ.SortSymbol)
    (id : FreeVarId) (replacement source : Term σ) :
    term D
        (Term.substituteFree target id replacement source) =
      Term.substituteFree target (id + 1)
        (term D replacement) (term D source) := by
  refine Term.rec
    (motive_1 := fun source =>
      term D
          (Term.substituteFree target id replacement source) =
        Term.substituteFree target (id + 1)
          (term D replacement) (term D source))
    (motive_2 := fun source =>
      source.map
          (term D ∘
            Term.substituteFree target id replacement) =
        source.map
          (Term.substituteFree target (id + 1)
              (term D replacement) ∘
            term D))
    ?_ ?_ ?_ ?_ source
  · intro value
    cases value with
    | bvar sort index =>
        simp [term, Term.substituteFree]
    | fvar sort sourceId =>
        by_cases hSubstitute :
            sort = target ∧ sourceId = id
        · rcases hSubstitute with ⟨rfl, rfl⟩
          simp [term, free_shift,
            Term.substituteFree]
        · have hShift :
              ¬(sort = target ∧
                  sourceId + 1 = id + 1) := by
            intro h
            exact hSubstitute ⟨h.1,
              Nat.add_right_cancel h.2⟩
          simp [term, free_shift,
            Term.substituteFree,
            hSubstitute]
  · intro function arguments ih
    by_cases hFunction : function = D.symbol
    · have hReserved :
          ¬(D.sort = target ∧ 0 = id + 1) := by
        simp
      simp [term, Term.substituteFree,
        hFunction]
    · simpa [term, Term.substituteFree, hFunction,
        List.map_map, Function.comp_def] using
          congrArg (Term.app function) ih
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

/-- 不使用待消去常元的项在翻译后不含保留变量。 -/
theorem term_reserved_fresh
    (D : Data σ) (source : Term σ)
    (hAvoids : TermAvoids D source) :
    (D.sort, 0) ∉ Term.freeSupport (term D source) := by
  refine Term.rec
    (motive_1 := fun source =>
      TermAvoids D source →
        (D.sort, 0) ∉
          Term.freeSupport (term D source))
    (motive_2 := fun source =>
      TermsAvoid D source →
        (D.sort, 0) ∉
          Term.freeSupportList (terms D source))
    ?_ ?_ ?_ ?_ source hAvoids
  · intro value _
    cases value with
    | bvar sort index =>
        simp [term, Term.freeSupport]
    | fvar sort id =>
        simp [term, free_shift, Term.freeSupport]
  · intro function arguments ih hAvoids
    have hAvoids' :
        function ≠ D.symbol ∧
          (∀ argument, argument ∈ arguments →
            TermAvoids D argument) := by
      simpa [TermAvoids] using hAvoids
    rcases hAvoids' with
      ⟨hFunction, hArguments⟩
    simpa [term, hFunction] using
      ih hArguments
  · intro _
    exact List.not_mem_nil
  · intro head tail ihHead ihTail hAvoids
    intro hMember
    rcases List.mem_append.mp hMember with
      hHead | hTail
    · exact ihHead
        (hAvoids head (by simp)) hHead
    · exact ihTail
        (by
          intro argument hArgument
          exact hAvoids argument
            (by simp [hArgument]))
        hTail

/-- 不使用待消去常元的项列表在翻译后不含保留变量。 -/
theorem terms_reserved_fresh
    (D : Data σ) (source : List (Term σ))
    (hAvoids : TermsAvoid D source) :
    (D.sort, 0) ∉
      Term.freeSupportList (terms D source) := by
  cases source with
  | nil =>
      exact List.not_mem_nil
  | cons head tail =>
      intro hMember
      rcases List.mem_append.mp hMember with
        hHead | hTail
      · exact term_reserved_fresh D head
          (hAvoids head (by simp)) hHead
      · exact terms_reserved_fresh D tail
          (by
            intro argument hArgument
            exact hAvoids argument
              (by simp [hArgument]))
          hTail

/-- 源自由变量的新鲜性在平移后保持。 -/
theorem term_fresh
    (D : Data σ) (sort : σ.SortSymbol)
    (id : FreeVarId) (source : Term σ)
    (hFresh :
      (sort, id) ∉ Term.freeSupport source) :
    (sort, id + 1) ∉
      Term.freeSupport (term D source) := by
  refine Term.rec
    (motive_1 := fun source =>
      (sort, id) ∉ Term.freeSupport source →
        (sort, id + 1) ∉
          Term.freeSupport (term D source))
    (motive_2 := fun source =>
      (sort, id) ∉ Term.freeSupportList source →
        (sort, id + 1) ∉
          Term.freeSupportList (terms D source))
    ?_ ?_ ?_ ?_ source hFresh
  · intro value hFresh
    cases value with
    | bvar binder index =>
        simp [term, Term.freeSupport]
    | fvar binder sourceId =>
        intro hMember
        have hEqual :
            sort = binder ∧ id = sourceId := by
          simpa [term, free_shift,
            Term.freeSupport] using hMember
        rcases hEqual with ⟨rfl, rfl⟩
        exact hFresh <| by
          simp [Term.freeSupport]
  · intro function arguments ih hFresh
    by_cases hFunction : function = D.symbol
    · subst function
      simp [term, Term.freeSupport]
    · simpa [term, hFunction] using ih hFresh
  · intro _
    exact List.not_mem_nil
  · intro head tail ihHead ihTail hFresh
    have hHead :
        (sort, id) ∉ Term.freeSupport head := by
      intro hMember
      exact hFresh <|
        List.mem_append.mpr (Or.inl hMember)
    have hTail :
        (sort, id) ∉
          Term.freeSupportList tail := by
      intro hMember
      exact hFresh <|
        List.mem_append.mpr (Or.inr hMember)
    intro hMember
    rcases List.mem_append.mp hMember with
      hMember | hMember
    · exact ihHead hHead hMember
    · exact ihTail hTail hMember

/-- 项列表中的源自由变量新鲜性在平移后保持。 -/
theorem terms_fresh
    (D : Data σ) (sort : σ.SortSymbol)
    (id : FreeVarId) (source : List (Term σ))
    (hFresh :
      (sort, id) ∉
        Term.freeSupportList source) :
    (sort, id + 1) ∉
      Term.freeSupportList (terms D source) := by
  induction source with
  | nil =>
      exact List.not_mem_nil
  | cons head tail ih =>
      have hHead :
          (sort, id) ∉ Term.freeSupport head := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inl hMember)
      have hTail :
          (sort, id) ∉
            Term.freeSupportList tail := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inr hMember)
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact term_fresh D sort id head
          hHead hMember
      · exact ih hTail hMember

/--
不含待消去常元且没有自由变量的项在翻译下严格不变。
-/
theorem term_eq_of_closed_avoids
    (D : Data σ) (source : Term σ)
    (hAvoids : TermAvoids D source)
    (hClosed : Term.freeSupport source = []) :
    term D source = source := by
  refine Term.rec
    (motive_1 := fun source =>
      TermAvoids D source →
        Term.freeSupport source = [] →
          term D source = source)
    (motive_2 := fun source =>
      TermsAvoid D source →
        Term.freeSupportList source = [] →
          terms D source = source)
    ?_ ?_ ?_ ?_ source hAvoids hClosed
  · intro value _ hClosed
    cases value with
    | bvar sort index =>
        simp [term]
    | fvar sort id =>
        simp [Term.freeSupport] at hClosed
  · intro function arguments ih hAvoids hClosed
    have hAvoids' :
        function ≠ D.symbol ∧
          TermsAvoid D arguments := by
      simpa [TermAvoids] using hAvoids
    rcases hAvoids' with
      ⟨hFunction, hArguments⟩
    have hArgumentsClosed :
        Term.freeSupportList arguments = [] := by
      simpa [Term.freeSupport] using hClosed
    have hArgumentsEq :=
      ih hArguments hArgumentsClosed
    simpa [term, terms, hFunction] using
      congrArg (Term.app function) hArgumentsEq
  · intro _ _
    rfl
  · intro head tail ihHead ihTail hAvoids hClosed
    have hParts :
        Term.freeSupport head = [] ∧
          Term.freeSupportList tail = [] := by
      exact append_eq_nil_parts <| by
        simpa [Term.freeSupportList] using hClosed
    have hHeadAvoids :
        TermAvoids D head :=
      hAvoids head (by simp)
    have hTailAvoids :
        TermsAvoid D tail := by
      intro argument hArgument
      exact hAvoids argument (by simp [hArgument])
    change term D head :: terms D tail =
      head :: tail
    rw [ihHead hHeadAvoids hParts.1,
      ihTail hTailAvoids hParts.2]

/-- 闭项列表若不含待消去常元，则逐项翻译严格不变。 -/
theorem terms_eq_of_closed_avoids
    (D : Data σ) (source : List (Term σ))
    (hAvoids : TermsAvoid D source)
    (hClosed : Term.freeSupportList source = []) :
    terms D source = source := by
  induction source with
  | nil =>
      rfl
  | cons head tail ih =>
      have hParts :
          Term.freeSupport head = [] ∧
            Term.freeSupportList tail = [] :=
        append_eq_nil_parts <| by
          simpa [Term.freeSupportList] using hClosed
      have hHeadAvoids :
          TermAvoids D head :=
        hAvoids head (by simp)
      have hTailAvoids :
          TermsAvoid D tail := by
        intro argument hArgument
        exact hAvoids argument (by simp [hArgument])
      change term D head :: terms D tail =
        head :: tail
      rw [term_eq_of_closed_avoids D head
          hHeadAvoids hParts.1,
        ih hTailAvoids hParts.2]

/-- 递归翻译公式中的全部项。 -/
def formula (D : Data σ) : Formula σ → Formula σ
  | .falsum =>
      .falsum
  | .truth =>
      .truth
  | .rel relation arguments =>
      .rel relation (terms D arguments)
  | .equal left right =>
      .equal (term D left) (term D right)
  | .neg body =>
      .neg (formula D body)
  | .conj left right =>
      .conj (formula D left) (formula D right)
  | .disj left right =>
      .disj (formula D left) (formula D right)
  | .imp left right =>
      .imp (formula D left) (formula D right)
  | .iff left right =>
      .iff (formula D left) (formula D right)
  | .forallE sort body =>
      .forallE sort (formula D body)
  | .existsE sort body =>
      .existsE sort (formula D body)

/-- 一个公式不使用待消去常元。 -/
def FormulaAvoids (D : Data σ) : Formula σ → Prop
  | .falsum | .truth =>
      True
  | .rel _ arguments =>
      TermsAvoid D arguments
  | .equal left right =>
      TermAvoids D left ∧ TermAvoids D right
  | .neg body =>
      FormulaAvoids D body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      FormulaAvoids D left ∧ FormulaAvoids D right
  | .forallE _ body
  | .existsE _ body =>
      FormulaAvoids D body

/--
不含待消去常元的闭公式在翻译下严格不变。
-/
theorem formula_eq_of_closed_avoids
    (D : Data σ) (source : Formula σ)
    (hAvoids : FormulaAvoids D source)
    (hClosed : Formula.freeSupport source = []) :
    formula D source = source := by
  induction source with
  | falsum | truth =>
      rfl
  | rel relation arguments =>
      simpa [formula] using
        terms_eq_of_closed_avoids D arguments
          hAvoids <| by
            simpa [Formula.freeSupport] using hClosed
  | equal left right =>
      have hParts :
          Term.freeSupport left = [] ∧
            Term.freeSupport right = [] :=
        append_eq_nil_parts <| by
          simpa [Formula.freeSupport] using hClosed
      rcases hAvoids with ⟨hLeft, hRight⟩
      simp [formula,
        term_eq_of_closed_avoids D left
          hLeft hParts.1,
        term_eq_of_closed_avoids D right
          hRight hParts.2]
  | neg body ih =>
      simp [formula, ih hAvoids <| by
        simpa [Formula.freeSupport] using hClosed]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      have hParts :
          Formula.freeSupport left = [] ∧
            Formula.freeSupport right = [] :=
        append_eq_nil_parts <| by
          simpa [Formula.freeSupport] using hClosed
      rcases hAvoids with ⟨hLeft, hRight⟩
      simp [formula,
        ihLeft hLeft hParts.1,
        ihRight hRight hParts.2]
  | forallE sort body ih
  | existsE sort body ih =>
      simp [formula, ih hAvoids <| by
        simpa [Formula.freeSupport] using hClosed]

/-- 零元常元消去保持公式良构性。 -/
theorem formula_well_formed
    (D : Data σ) {source : Formula σ}
    (hSource : FormulaWellFormed source) :
    FormulaWellFormed (formula D source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation hArguments =>
      exact FormulaWellFormed.rel relation
        (terms_well_sorted D hArguments)
  | equal hLeft hRight =>
      exact .equal
        (term_well_sorted D hLeft)
        (term_well_sorted D hRight)
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
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .existsE sort ih

/-- 零元常元消去保持公式 scope。 -/
theorem formula_scoped
    (D : Data σ) {scope : Scope σ}
    {source : Formula σ}
    (hSource : FormulaScoped scope source) :
    FormulaScoped scope (formula D source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments hArguments =>
      exact FormulaScoped.rel relation
        (terms D arguments) <| by
          intro target hTarget
          rcases List.mem_map.mp hTarget with
            ⟨source, hSource, rfl⟩
          exact term_scoped D
            (hArguments source hSource)
  | equal hLeft hRight =>
      exact .equal
        (term_scoped D hLeft)
        (term_scoped D hRight)
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
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .existsE sort ih

/-- 零元常元消去保持 proof-layer admissibility。 -/
theorem formula_admissible
    (D : Data σ) {source : Formula σ}
    (hSource : Formula.Admissible source) :
    Formula.Admissible (formula D source) :=
  ⟨formula_well_formed D hSource.1,
    formula_scoped D hSource.2⟩

/-- 零元常元消去与公式打开交换。 -/
theorem formula_openAt
    (D : Data σ) (target : σ.SortSymbol)
    (depth : Nat) (replacement : Term σ)
    (source : Formula σ) :
    formula D
        (Formula.openAt target depth replacement source) =
      Formula.openAt target depth (term D replacement)
        (formula D source) := by
  induction source generalizing depth with
  | falsum | truth =>
      rfl
  | rel relation arguments =>
      simp [formula, terms, Formula.openAt,
        List.map_map, Function.comp_def,
        term_openAt D]
  | equal left right =>
      simp [formula, Formula.openAt,
        term_openAt D]
  | neg body ih =>
      simp [formula, Formula.openAt, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.openAt,
        ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      simp [formula, Formula.openAt,
        Formula.next_depth, ih]

/-- 零元常元消去与公式关闭交换。 -/
theorem formula_closeFreeAt
    (D : Data σ) (target : σ.SortSymbol)
    (id : FreeVarId) (depth : Nat)
    (source : Formula σ) :
    formula D
        (Formula.closeFreeAt target id depth source) =
      Formula.closeFreeAt target (id + 1) depth
        (formula D source) := by
  induction source generalizing depth with
  | falsum | truth =>
      rfl
  | rel relation arguments =>
      simp [formula, terms, Formula.closeFreeAt,
        List.map_map, Function.comp_def,
        term_closeFreeAt D]
  | equal left right =>
      simp [formula, Formula.closeFreeAt,
        term_closeFreeAt D]
  | neg body ih =>
      simp [formula, Formula.closeFreeAt, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.closeFreeAt,
        ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      simp [formula, Formula.closeFreeAt,
        Formula.next_depth, ih]

/-- 零元常元消去与公式自由替换交换。 -/
theorem formula_substituteFree
    (D : Data σ) (target : σ.SortSymbol)
    (id : FreeVarId) (replacement : Term σ)
    (source : Formula σ) :
    formula D
        (Formula.substituteFree target id
          replacement source) =
      Formula.substituteFree target (id + 1)
        (term D replacement) (formula D source) := by
  induction source with
  | falsum | truth =>
      rfl
  | rel relation arguments =>
      simp [formula, terms,
        Formula.substituteFree,
        List.map_map, Function.comp_def,
        term_substituteFree D]
  | equal left right =>
      simp [formula, Formula.substituteFree,
        term_substituteFree D]
  | neg body ih =>
      simp [formula, Formula.substituteFree, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.substituteFree,
        ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      simp [formula, Formula.substituteFree, ih]

/-- 公式自由变量的新鲜性在平移后保持。 -/
theorem formula_fresh
    (D : Data σ) (sort : σ.SortSymbol)
    (id : FreeVarId) (source : Formula σ)
    (hFresh :
      (sort, id) ∉ Formula.freeSupport source) :
    (sort, id + 1) ∉
      Formula.freeSupport (formula D source) := by
  induction source with
  | falsum | truth =>
      exact List.not_mem_nil
  | rel relation arguments =>
      exact terms_fresh D sort id arguments <| by
        simpa [Formula.freeSupport] using hFresh
  | equal left right =>
      have hLeft :
          (sort, id) ∉ Term.freeSupport left := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inl hMember)
      have hRight :
          (sort, id) ∉ Term.freeSupport right := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inr hMember)
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact term_fresh D sort id left
          hLeft hMember
      · exact term_fresh D sort id right
          hRight hMember
  | neg body ih =>
      simpa [formula, Formula.freeSupport] using
        ih hFresh
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      have hLeft :
          (sort, id) ∉
            Formula.freeSupport left := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inl hMember)
      have hRight :
          (sort, id) ∉
            Formula.freeSupport right := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inr hMember)
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact ihLeft hLeft hMember
      · exact ihRight hRight hMember
  | forallE binder body ih
  | existsE binder body ih =>
      simpa [formula, Formula.freeSupport] using
        ih hFresh

/-- 不使用待消去常元的公式在翻译后不含保留变量。 -/
theorem formula_reserved_fresh
    (D : Data σ) (source : Formula σ)
    (hAvoids : FormulaAvoids D source) :
    (D.sort, 0) ∉
      Formula.freeSupport (formula D source) := by
  induction source with
  | falsum | truth =>
      exact List.not_mem_nil
  | rel relation arguments =>
      simpa [formula, Formula.freeSupport] using
        terms_reserved_fresh D arguments hAvoids
  | equal left right =>
      rcases hAvoids with ⟨hLeft, hRight⟩
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact term_reserved_fresh D left hLeft hMember
      · exact term_reserved_fresh D right hRight hMember
  | neg body ih =>
      exact ih hAvoids
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      rcases hAvoids with ⟨hLeft, hRight⟩
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact ihLeft hLeft hMember
      · exact ihRight hRight hMember
  | forallE sort body ih
  | existsE sort body ih =>
      exact ih hAvoids

/-- 零元常元消去逐项保持十二类基础 Hilbert 公理。 -/
theorem base_axiom
    (D : Data σ) {source : Formula σ}
    (hSource : HilbertBaseAxiom source) :
    HilbertBaseAxiom (formula D source) := by
  cases hSource with
  | implication_distribution antecedent middle consequent =>
      exact .implication_distribution
        (formula D antecedent)
        (formula D middle)
        (formula D consequent)
  | self_implication source =>
      exact .self_implication (formula D source)
  | weakening source extra =>
      exact .weakening
        (formula D source) (formula D extra)
  | contradiction source conclusion =>
      exact .contradiction
        (formula D source) (formula D conclusion)
  | classical source =>
      exact .classical (formula D source)
  | explosion source conclusion =>
      exact .explosion
        (formula D source) (formula D conclusion)
  | case_analysis source conclusion =>
      exact .case_analysis
        (formula D source) (formula D conclusion)
  | forall_specialization sort body source
      hSorted hClosed =>
      simpa [formula, formula_openAt D] using
        (HilbertBaseAxiom.forall_specialization
          sort (formula D body) (term D source)
          (term_well_sorted D hSorted)
          (term_bound_closed D hClosed))
  | forall_distribution sort antecedent consequent =>
      exact .forall_distribution sort
        (formula D antecedent)
        (formula D consequent)
  | vacuous_forall sort eigen source hFresh =>
      have hTranslatedFresh :
          (sort, eigen + 1) ∉
            Formula.freeSupport
              (formula D source) := by
        exact formula_fresh D sort eigen source hFresh
      simpa [formula, formula_closeFreeAt D] using
        (HilbertBaseAxiom.vacuous_forall
          sort (eigen + 1)
          (formula D source) hTranslatedFresh)
  | equality_substitution sort leftId rightId body =>
      simpa [formula, term, free_shift,
        formula_substituteFree D] using
        (HilbertBaseAxiom.equality_substitution
          sort (leftId + 1) (rightId + 1)
          (formula D body))
  | equality_reflexivity sort id =>
      simpa [formula, term, free_shift] using
        (HilbertBaseAxiom.equality_reflexivity
          sort (id + 1))

/-- 零元常元消去保持有限全称闭包后的逻辑公理。 -/
theorem logical_axiom
    (D : Data σ) {source : Formula σ}
    (hSource : HilbertLogicalAxiom source) :
    HilbertLogicalAxiom (formula D source) := by
  induction hSource with
  | base hBase =>
      exact .base (base_axiom D hBase)
  | forall_closure sort eigen hAxiom ih =>
      simpa [formula, formula_closeFreeAt D] using
        (HilbertLogicalAxiom.forall_closure
          sort (eigen + 1) ih)

/-- 源理论在零元常元消去后的公式像。 -/
def theory (D : Data σ) (source : Theory σ) :
    Theory σ :=
  fun target =>
    ∃ sourceFormula,
      source sourceFormula ∧
        target = formula D sourceFormula

/--
若基理论的每条公理都是闭句且不使用待消去常元，则其翻译像严格等于自身。
-/
theorem theory_eq_of_sentence_avoids
    (D : Data σ) {source : Theory σ}
    (hAvoids :
      ∀ φ, source φ → FormulaAvoids D φ)
    (hSentence :
      ∀ φ, source φ → Formula.Sentence φ) :
    theory D source = source := by
  funext φ
  apply propext
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    rw [formula_eq_of_closed_avoids D ψ
      (hAvoids ψ hψ) (hSentence ψ hψ).2]
    exact hψ
  · intro hφ
    exact ⟨φ, hφ,
      (formula_eq_of_closed_avoids D φ
        (hAvoids φ hφ)
        (hSentence φ hφ).2).symm⟩

/-- Hilbert 推导可逐树消去指定零元常元。 -/
theorem hilbert
    (D : Data σ) {sourceTheory : Theory σ}
    {source : Formula σ}
    (hSource :
      HilbertDerives sourceTheory source) :
    HilbertDerives (theory D sourceTheory)
      (formula D source) := by
  induction hSource with
  | logical_axiom hAxiom hAdmissible =>
      exact .logical_axiom
        (logical_axiom D hAxiom)
        (formula_admissible D hAdmissible)
  | theory_axiom hTheory hAdmissible =>
      exact .theory_axiom
        ⟨_, hTheory, rfl⟩
        (formula_admissible D hAdmissible)
  | modus_ponens hAntecedent hImplication
      ihAntecedent ihImplication =>
      exact .modus_ponens ihAntecedent <| by
        simpa [formula] using ihImplication

/--
若基理论证明翻译后定义公理具有一个见证，则加入该零元定义公理不会制造矛盾。

结论保持在自然演绎层，正好对接 `Project.Consistent` 的裸理论一致性定义。
-/
theorem derives_falsum_of_extension
    (D : Data σ) {base : Theory σ}
    {definition : Formula σ}
    (hDefinition :
      Formula.Admissible definition)
    (hBaseAvoids :
      ∀ source, base source →
        FormulaAvoids D source)
    (hExists :
      Derives (theory D base) [] <|
        Formula.existsE D.sort <|
          Formula.closeFreeAt D.sort 0 0
            (formula D definition))
    (hExtension :
      HilbertDerives
        (Theory.insert definition base)
        Formula.falsum) :
    Derives (theory D base) [] Formula.falsum := by
  have hTranslated :
      HilbertDerives
        (theory D
          (Theory.insert definition base))
        Formula.falsum := by
    simpa [formula] using hilbert D hExtension
  have hCase :
      Derives (theory D base)
        [formula D definition] Formula.falsum := by
    apply hTranslated.interpret_m
    intro target hTarget hTargetAdmissible
    rcases hTarget with
      ⟨source, hSource, rfl⟩
    rcases hSource with rfl | hSource
    · exact .assumption (by simp)
    · exact .theoryAxiom
        ⟨source, hSource, rfl⟩
  exact Derives.exists_elim
    (sort := D.sort) (eigen := 0)
    (body := formula D definition)
    (conclusion := Formula.falsum)
    (fun target hTarget => by
      rcases hTarget with
        ⟨source, hSource, rfl⟩
      exact formula_reserved_fresh D source
        (hBaseAvoids source hSource))
    (by simp)
    (by simp [Formula.freeSupport])
    hExists hCase
    (Formula.check_admissible_complete
      (formula_admissible D hDefinition))

/--
一个零元定义常元的完整纯语法消去表示。

接口只记录消去定理真正消费的五项数据；存在见证必须已经在翻译后的基理论中
实现，不能以语义模型或不可计算选择占位。
-/
structure Presentation
    (σ : Signature.{u, v, w})
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] where
  data : Data σ
  base : Theory σ
  definition : Formula σ
  definition_admissible :
    Formula.Admissible definition
  base_avoids :
    ∀ source, base source →
      FormulaAvoids data source
  definition_exists :
    Derives (theory data base) [] <|
      Formula.existsE data.sort <|
        Formula.closeFreeAt data.sort 0 0
          (formula data definition)

namespace Presentation

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

/-- 由表示指定的单步定义扩张。 -/
def extension (P : Presentation σ) :
    Theory σ :=
  Theory.insert P.definition P.base

/-- 完整表示自动把扩张理论的 Hilbert 矛盾回传到翻译后的基理论。 -/
theorem derives_falsum
    (P : Presentation σ)
    (h :
      HilbertDerives P.extension Formula.falsum) :
    Derives (theory P.data P.base) []
      Formula.falsum := by
  exact derives_falsum_of_extension
    P.data P.definition_admissible
    P.base_avoids P.definition_exists h

/-- 翻译后基理论的一致性推出定义扩张的 Hilbert 一致性。 -/
theorem consistent_extension
    (P : Presentation σ)
    (hBase :
      Derives.Consistent
        (theory P.data P.base) []) :
    ¬ HilbertDerives P.extension
      Formula.falsum := by
  intro hExtension
  exact hBase (P.derives_falsum hExtension)

end Presentation

end ConstantElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
