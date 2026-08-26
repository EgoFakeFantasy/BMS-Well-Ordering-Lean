import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
/-!
# 一阶公式的相对 Lévy 层级
本模块只刻画公式的量词骨架，不把具体非逻辑符号的数学绝对性偷渡进语法定义。
给定一个二元“有界关系”符号及其对象 sort，所有原子公式都视为相对 `Delta0`
原子；无界存在量词生成 `Sigma1`，无界全称量词生成 `Pi1`，由该关系限制的量词
不提升层级。
这正是定义扩张语言所需的分层方式：后续模块分别证明扩展函数与关系的绝对性，
而证明码、真值定义及 Rosser 比较可以共用本文件的纯句法内核。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Term
mutual
  /--
  项在指定 sort 上不使用给定 de Bruijn 层。
  有界量词的界项必须不依赖刚引入的第 `0` 个 bound variable；否则
  `∀ x ∈ t(x)` 并不是真正的有界量词。
  -/
  inductive BoundFreeAt
      {σ : Signature.{u, v, w}} (target : σ.SortSymbol) (depth : Nat) :
      Term σ → Prop where
    | bvar (sort : σ.SortSymbol) (index : Nat) (hDifferent :
          sort ≠ target ∨ index ≠ depth) :
        BoundFreeAt target depth (.var (.bvar sort index))
    | fvar (sort : σ.SortSymbol) (id : FreeVarId) :
        BoundFreeAt target depth (.var (.fvar sort id))
    | app (function : σ.FuncSymbol)
        {arguments : List (Term σ)} (hArguments :
          ArgsBoundFreeAt target depth arguments) :
        BoundFreeAt target depth (.app function arguments)
  /-- 项列表逐项不使用指定 de Bruijn 层。 -/
  inductive ArgsBoundFreeAt
      {σ : Signature.{u, v, w}} (target : σ.SortSymbol) (depth : Nat) :
      List (Term σ) → Prop where
    | nil :
        ArgsBoundFreeAt target depth []
    | cons {head : Term σ} {tail : List (Term σ)} (hHead : BoundFreeAt target depth head) (hTail : ArgsBoundFreeAt target depth tail) :
        ArgsBoundFreeAt target depth (head :: tail)
end
@[simp]
theorem bound_free_at_fvar
    {σ : Signature.{u, v, w}} (target sort : σ.SortSymbol) (depth : Nat) (id : FreeVarId) :
    BoundFreeAt target depth (.var (.fvar sort id) : Term σ) :=
  BoundFreeAt.fvar sort id
@[simp]
theorem bound_free_at_bvar_iff
    {σ : Signature.{u, v, w}} (target sort : σ.SortSymbol) (depth index : Nat) :
    BoundFreeAt target depth (.var (.bvar sort index) : Term σ) ↔
      sort ≠ target ∨ index ≠ depth := by
  constructor
  · intro hBound
    cases hBound with
    | bvar _ _ hDifferent =>
        exact hDifferent
  · exact BoundFreeAt.bvar sort index
theorem args_bound_free_at_iff_forall
    {σ : Signature.{u, v, w}} (target : σ.SortSymbol) (depth : Nat) (arguments : List (Term σ)) :
    ArgsBoundFreeAt target depth arguments ↔
      ∀ argument, argument ∈ arguments →
        BoundFreeAt target depth argument := by
  induction arguments with
  | nil =>
      constructor
      · intro _ argument hArgument
        cases hArgument
      · intro _
        exact ArgsBoundFreeAt.nil
  | cons head tail ih =>
      constructor
      · intro hArguments argument hArgument
        cases hArguments with
        | cons hHead hTail =>
            rcases List.mem_cons.mp hArgument with
              rfl | hArgument
            · exact hHead
            · exact ih.mp hTail argument hArgument
      · intro hArguments
        exact ArgsBoundFreeAt.cons (hArguments head (by simp)) (ih.mpr fun argument hArgument =>
            hArguments argument (by simp [hArgument]))
@[simp]
theorem bound_free_at_app_iff
    {σ : Signature.{u, v, w}} (target : σ.SortSymbol) (depth : Nat) (function : σ.FuncSymbol) (arguments : List (Term σ)) :
    BoundFreeAt target depth (.app function arguments) ↔
      ∀ argument, argument ∈ arguments →
        BoundFreeAt target depth argument := by
  constructor
  · intro hBound
    cases hBound with
    | app _ hArguments =>
        exact (args_bound_free_at_iff_forall
            target depth arguments).mp hArguments
  · intro hArguments
    exact BoundFreeAt.app function ((args_bound_free_at_iff_forall
        target depth arguments).mpr hArguments)
/-- Bound-closed 项当然不使用任何指定的 bound 层。 -/
theorem bound_free_at_of_bound_closed
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (depth : Nat) (term : Term σ) (hClosed : term.BoundClosed) :
    BoundFreeAt target depth term := by
  induction hClosed with
  | bvar hIndex =>
      simp [Scope.empty] at hIndex
  | fvar sort id =>
      exact BoundFreeAt.fvar sort id
  | app function arguments hArguments ih =>
      exact BoundFreeAt.app function ((args_bound_free_at_iff_forall
          target depth arguments).mpr ih)
mutual
  /--
  在非受保护位置关闭自由变量，不会让项新依赖受保护的第 `0` 个 binder。
  本定理专门对应有界量词的界项：穿过该量词后，关闭深度在同 sort 情形下至少为
  `1`；不同 sort 时则根本不会触及受保护 binder。
  -/
  theorem BoundFreeAt.closeFreeAt_zero
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {guardedSort target : σ.SortSymbol}
      {id : FreeVarId} {depth : Nat}
      {term : Term σ} (hTerm : BoundFreeAt guardedSort 0 term) (hSafe : target ≠ guardedSort ∨ depth ≠ 0) :
      BoundFreeAt guardedSort 0 (Term.closeFreeAt target id depth term) := by
    cases hTerm with
    | bvar sort index hDifferent =>
        simp only [Term.closeFreeAt]
        split
        next hShift =>
          exact BoundFreeAt.bvar sort (index + 1) (Or.inr (Nat.succ_ne_zero index))
        next _ =>
          exact BoundFreeAt.bvar sort index hDifferent
    | fvar sort variableId =>
        simp only [Term.closeFreeAt]
        split
        next hClose =>
          rcases hSafe with hSort | hDepth
          · exact BoundFreeAt.bvar sort depth (Or.inl (hClose.1 ▸ hSort))
          · exact BoundFreeAt.bvar sort depth (Or.inr hDepth)
        next _ =>
          exact BoundFreeAt.fvar sort variableId
    | app function hArguments =>
        simpa [Term.closeFreeAt] using
          BoundFreeAt.app function (ArgsBoundFreeAt.closeFreeAt_zero (id := id) hArguments hSafe)
  /-- `closeFreeAt_zero` 的参数列表版本。 -/
  theorem ArgsBoundFreeAt.closeFreeAt_zero
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {guardedSort target : σ.SortSymbol}
      {id : FreeVarId} {depth : Nat}
      {arguments : List (Term σ)} (hArguments : ArgsBoundFreeAt guardedSort 0 arguments) (hSafe : target ≠ guardedSort ∨ depth ≠ 0) :
      ArgsBoundFreeAt guardedSort 0 (arguments.map (Term.closeFreeAt target id depth)) := by
    cases hArguments with
    | nil =>
        exact ArgsBoundFreeAt.nil
    | cons hHead hTail =>
        exact ArgsBoundFreeAt.cons (BoundFreeAt.closeFreeAt_zero hHead hSafe) (ArgsBoundFreeAt.closeFreeAt_zero hTail hSafe)
end
/--
穿过一个 binder 后关闭自由变量时，该 binder 自己的第 `0` 个 de Bruijn 变量保持
不变。
-/
@[simp]
theorem closeFreeAt_bvar_zero_after_binder
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (binder target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) :
    Term.closeFreeAt target id (Formula.next_depth target binder depth) (.var (.bvar binder 0) : Term σ) =
      .var (.bvar binder 0) := by
  by_cases hSort : target = binder
  · subst target
    simp [Formula.next_depth, Term.closeFreeAt]
  · have hReverse : binder ≠ target := Ne.symm hSort
    simp [Formula.next_depth, Term.closeFreeAt,
      hReverse]
/--
若目标自由变量不在项中，那么在深度 `0` 关闭该变量后，所得项不会依赖新生成的
第 `0` 个 binder。
-/
theorem bound_free_at_closeFreeAt_zero_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (term : Term σ)
    (hFresh : (target, id) ∉ Term.freeSupport term) :
    BoundFreeAt target 0 (Term.closeFreeAt target id 0 term) := by
  refine Term.rec (motive_1 := fun source =>
      (target, id) ∉ Term.freeSupport source →
        BoundFreeAt target 0 (Term.closeFreeAt target id 0 source)) (motive_2 := fun arguments =>
      (target, id) ∉ Term.freeSupportList arguments →
        ArgsBoundFreeAt target 0 (arguments.map (Term.closeFreeAt target id 0)))
    ?_ ?_ ?_ ?_ term hFresh
  · intro source
    cases source with
    | bvar sort index =>
        intro _
        by_cases hSort : sort = target
        · subst sort
          simp [Term.closeFreeAt]
        · simp [Term.closeFreeAt, hSort]
    | fvar sort variableId =>
        intro hVariable
        have hNoClose :
            ¬ (sort = target ∧ variableId = id) := by
          intro hClose
          apply hVariable
          simp [Term.freeSupport, hClose]
        simp [Term.closeFreeAt, hNoClose]
  · intro function arguments hArguments hFreshArguments
    simpa [Term.closeFreeAt] using
      BoundFreeAt.app function (hArguments hFreshArguments)
  · intro _
    exact ArgsBoundFreeAt.nil
  · intro head tail hHead hTail hFreshArguments
    have hHeadFresh : (target, id) ∉ Term.freeSupport head := by
      intro hMember
      exact hFreshArguments (by
        simp [Term.freeSupportList, hMember])
    have hTailFresh : (target, id) ∉ Term.freeSupportList tail := by
      intro hMember
      exact hFreshArguments (by
        simp [Term.freeSupportList, hMember])
    exact ArgsBoundFreeAt.cons (hHead hHeadFresh) (hTail hTailFresh)
mutual
  /--
  用同样不依赖受保护 binder 的项替换自由变量，保持 `BoundFreeAt`。
  后续 Lévy 层级替换定理以 bound-closed 替换项调用本结论。
  -/
  theorem BoundFreeAt.substituteFree
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {guardedSort targetSort : σ.SortSymbol}
      {targetId : FreeVarId}
      {replacement source : Term σ} (hSource :
        BoundFreeAt guardedSort 0 source) (hReplacement :
        BoundFreeAt guardedSort 0 replacement) :
      BoundFreeAt guardedSort 0 (Term.substituteFree
          targetSort targetId replacement source) := by
    cases hSource with
    | bvar sort index hDifferent =>
        simpa [Term.substituteFree] using
          BoundFreeAt.bvar (target := guardedSort)
            sort index hDifferent
    | fvar sort id =>
        simp only [Term.substituteFree]
        split
        · exact hReplacement
        · exact BoundFreeAt.fvar sort id
    | app function hArguments =>
        simpa [Term.substituteFree] using
          BoundFreeAt.app function (ArgsBoundFreeAt.substituteFree
              hArguments hReplacement)
  /-- `BoundFreeAt.substituteFree` 的项列表版本。 -/
  theorem ArgsBoundFreeAt.substituteFree
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {guardedSort targetSort : σ.SortSymbol}
      {targetId : FreeVarId}
      {replacement : Term σ} {sources : List (Term σ)} (hSources :
        ArgsBoundFreeAt guardedSort 0 sources) (hReplacement :
        BoundFreeAt guardedSort 0 replacement) :
      ArgsBoundFreeAt guardedSort 0 (sources.map (Term.substituteFree
            targetSort targetId replacement)) := by
    cases hSources with
    | nil =>
        exact ArgsBoundFreeAt.nil
    | cons hHead hTail =>
        exact ArgsBoundFreeAt.cons (BoundFreeAt.substituteFree hHead hReplacement) (ArgsBoundFreeAt.substituteFree hTail hReplacement)
end
end Term
namespace Formula
/--
相对 Lévy 层级的有界量词参数。
`relation` 预期是一个在 `sort` 上表示“属于界”的二元关系；其 arity 与语义绝对性
由具体语言实例另行证明。
-/
structure LevyBound (σ : Signature.{u, v, w}) where
  sort : σ.SortSymbol
  relation : σ.RelSymbol
/--
公式体在正位置显式携带当前 bound variable 的成员界。

该证书只沿 conjunction 的正位置传播；因此它保证公式体成立时，见证确实属于
`setTerm`，不会把任意原子条件或析取分支误当作有界量词。
-/
inductive MembershipGuard
    {σ : Signature.{u, v, w}} (bound : LevyBound σ)
    (setTerm : Term σ) : Formula σ → Prop where
  | membership :
      MembershipGuard bound setTerm
        (.rel bound.relation
          [.var (.bvar bound.sort 0), setTerm])
  | conj_left {left right : Formula σ} :
      MembershipGuard bound setTerm left →
      MembershipGuard bound setTerm (.conj left right)
  | conj_right {left right : Formula σ} :
      MembershipGuard bound setTerm right →
      MembershipGuard bound setTerm (.conj left right)
/-- 使用具名自由变量书写的正位置成员界。 -/
inductive FreeMembershipGuard
    {σ : Signature.{u, v, w}} (bound : LevyBound σ)
    (id : FreeVarId) (setTerm : Term σ) :
    Formula σ → Prop where
  | membership :
      FreeMembershipGuard bound id setTerm
        (.rel bound.relation
          [.var (.fvar bound.sort id), setTerm])
  | conj_left {left right : Formula σ} :
      FreeMembershipGuard bound id setTerm left →
      FreeMembershipGuard bound id setTerm (.conj left right)
  | conj_right {left right : Formula σ} :
      FreeMembershipGuard bound id setTerm right →
      FreeMembershipGuard bound id setTerm (.conj left right)
/-- 相对 `Delta0` 公式：仅含布尔联结词与真正的有界量词。 -/
inductive IsDelta0
    {σ : Signature.{u, v, w}} (bound : LevyBound σ) :
    Formula σ → Prop where
  | falsum :
      IsDelta0 bound .falsum
  | truth :
      IsDelta0 bound .truth
  | rel (relation : σ.RelSymbol) (arguments : List (Term σ)) :
      IsDelta0 bound (.rel relation arguments)
  | equal (left right : Term σ) :
      IsDelta0 bound (.equal left right)
  | neg {body : Formula σ} :
      IsDelta0 bound body →
      IsDelta0 bound (.neg body)
  | conj {left right : Formula σ} :
      IsDelta0 bound left →
      IsDelta0 bound right →
      IsDelta0 bound (.conj left right)
  | disj {left right : Formula σ} :
      IsDelta0 bound left →
      IsDelta0 bound right →
      IsDelta0 bound (.disj left right)
  | imp {left right : Formula σ} :
      IsDelta0 bound left →
      IsDelta0 bound right →
      IsDelta0 bound (.imp left right)
  | iff {left right : Formula σ} :
      IsDelta0 bound left →
      IsDelta0 bound right →
      IsDelta0 bound (.iff left right)
  | bounded_forall (setTerm : Term σ) (bodyFormula : Formula σ) (hSet :
        Term.BoundFreeAt bound.sort 0 setTerm) (hBody :
        IsDelta0 bound bodyFormula) :
      IsDelta0 bound (.forallE bound.sort (.imp (.rel bound.relation
              [.var (.bvar bound.sort 0), setTerm])
            bodyFormula))
  | bounded_exists (setTerm : Term σ) (bodyFormula : Formula σ) (hSet :
        Term.BoundFreeAt bound.sort 0 setTerm) (hBody :
        IsDelta0 bound bodyFormula) :
      IsDelta0 bound (.existsE bound.sort (.conj (.rel bound.relation
              [.var (.bvar bound.sort 0), setTerm])
            bodyFormula))
  | guarded_exists (setTerm : Term σ) (bodyFormula : Formula σ) (hSet :
        Term.BoundFreeAt bound.sort 0 setTerm) (hBody :
        IsDelta0 bound bodyFormula) (hGuard :
        MembershipGuard bound setTerm bodyFormula) :
      IsDelta0 bound (.existsE bound.sort bodyFormula)
mutual
  /-- 相对 `Sigma1` 公式。 -/
  inductive IsSigma1
      {σ : Signature.{u, v, w}} (bound : LevyBound σ) :
      Formula σ → Prop where
    | delta0 {formula : Formula σ} :
        IsDelta0 bound formula →
        IsSigma1 bound formula
    | neg {body : Formula σ} :
        IsPi1 bound body →
        IsSigma1 bound (.neg body)
    | conj {left right : Formula σ} :
        IsSigma1 bound left →
        IsSigma1 bound right →
        IsSigma1 bound (.conj left right)
    | disj {left right : Formula σ} :
        IsSigma1 bound left →
        IsSigma1 bound right →
        IsSigma1 bound (.disj left right)
    | imp {left right : Formula σ} :
        IsPi1 bound left →
        IsSigma1 bound right →
        IsSigma1 bound (.imp left right)
    | existsE (sort : σ.SortSymbol)
        {body : Formula σ} :
        IsSigma1 bound body →
        IsSigma1 bound (.existsE sort body)
    | bounded_forall (setTerm : Term σ) (bodyFormula : Formula σ) (hSet :
          Term.BoundFreeAt bound.sort 0 setTerm) (hBody :
          IsSigma1 bound bodyFormula) :
        IsSigma1 bound (.forallE bound.sort (.imp (.rel bound.relation
                [.var (.bvar bound.sort 0), setTerm])
              bodyFormula))
    | bounded_exists (setTerm : Term σ) (bodyFormula : Formula σ) (hSet :
          Term.BoundFreeAt bound.sort 0 setTerm) (hBody :
          IsSigma1 bound bodyFormula) :
        IsSigma1 bound (.existsE bound.sort (.conj (.rel bound.relation
                [.var (.bvar bound.sort 0), setTerm])
              bodyFormula))
  /-- 相对 `Pi1` 公式。 -/
  inductive IsPi1
      {σ : Signature.{u, v, w}} (bound : LevyBound σ) :
      Formula σ → Prop where
    | delta0 {formula : Formula σ} :
        IsDelta0 bound formula →
        IsPi1 bound formula
    | neg {body : Formula σ} :
        IsSigma1 bound body →
        IsPi1 bound (.neg body)
    | conj {left right : Formula σ} :
        IsPi1 bound left →
        IsPi1 bound right →
        IsPi1 bound (.conj left right)
    | disj {left right : Formula σ} :
        IsPi1 bound left →
        IsPi1 bound right →
        IsPi1 bound (.disj left right)
    | imp {left right : Formula σ} :
        IsSigma1 bound left →
        IsPi1 bound right →
        IsPi1 bound (.imp left right)
    | forallE (sort : σ.SortSymbol)
        {body : Formula σ} :
        IsPi1 bound body →
        IsPi1 bound (.forallE sort body)
    | bounded_forall (setTerm : Term σ) (bodyFormula : Formula σ) (hSet :
          Term.BoundFreeAt bound.sort 0 setTerm) (hBody :
          IsPi1 bound bodyFormula) :
        IsPi1 bound (.forallE bound.sort (.imp (.rel bound.relation
                [.var (.bvar bound.sort 0), setTerm])
              bodyFormula))
    | bounded_exists (setTerm : Term σ) (bodyFormula : Formula σ) (hSet :
          Term.BoundFreeAt bound.sort 0 setTerm) (hBody :
          IsPi1 bound bodyFormula) :
        IsPi1 bound (.existsE bound.sort (.conj (.rel bound.relation
                [.var (.bvar bound.sort 0), setTerm])
              bodyFormula))
end
namespace MembershipGuard

/-- 自由变量替换保持正位置成员 guard。 -/
theorem substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} {setTerm : Term σ}
    {formula : Formula σ}
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (hGuard : MembershipGuard bound setTerm formula) :
    MembershipGuard bound
      (Term.substituteFree target id replacement setTerm)
      (Formula.substituteFree target id replacement formula) := by
  induction hGuard with
  | membership =>
      simpa [Formula.substituteFree, Term.substituteFree] using
        (MembershipGuard.membership
          (bound := bound)
          (setTerm :=
            Term.substituteFree target id replacement setTerm))
  | conj_left hLeft ih =>
      simpa [Formula.substituteFree] using
        MembershipGuard.conj_left ih
  | conj_right hRight ih =>
      simpa [Formula.substituteFree] using
        MembershipGuard.conj_right ih

/--
穿过当前有界量词 binder 后关闭自由变量，保持正位置成员 guard。
-/
theorem closeFreeAt_after_binder
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} {setTerm : Term σ}
    {formula : Formula σ}
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (hGuard : MembershipGuard bound setTerm formula) :
    MembershipGuard bound
      (Term.closeFreeAt target id
        (Formula.next_depth target bound.sort depth) setTerm)
      (Formula.closeFreeAt target id
        (Formula.next_depth target bound.sort depth) formula) := by
  induction hGuard with
  | membership =>
      simpa [Formula.closeFreeAt,
        Term.closeFreeAt_bvar_zero_after_binder] using
        (MembershipGuard.membership
          (bound := bound)
          (setTerm :=
            Term.closeFreeAt target id
              (Formula.next_depth target bound.sort depth)
              setTerm))
  | conj_left hLeft ih =>
      simpa [Formula.closeFreeAt] using
        MembershipGuard.conj_left ih
  | conj_right hRight ih =>
      simpa [Formula.closeFreeAt] using
        MembershipGuard.conj_right ih

end MembershipGuard

namespace FreeMembershipGuard

/--
关闭充当见证的自由变量后，自由变量 guard 变成 de Bruijn 第 `0` 层的成员
guard。
-/
theorem closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} {id : FreeVarId}
    {setTerm : Term σ} {formula : Formula σ}
    (hGuard : FreeMembershipGuard bound id setTerm formula) :
    MembershipGuard bound
      (Term.closeFreeAt bound.sort id 0 setTerm)
      (Formula.closeFreeAt bound.sort id 0 formula) := by
  induction hGuard with
  | membership =>
      simpa [Formula.closeFreeAt, Term.closeFreeAt] using
        (MembershipGuard.membership
          (bound := bound)
          (setTerm :=
            Term.closeFreeAt bound.sort id 0 setTerm))
  | conj_left hLeft ih =>
      simpa [Formula.closeFreeAt] using
        MembershipGuard.conj_left ih
  | conj_right hRight ih =>
      simpa [Formula.closeFreeAt] using
        MembershipGuard.conj_right ih

end FreeMembershipGuard
namespace IsDelta0
/-- `Delta0` 公式可直接提升为 `Sigma1`。 -/
theorem to_sigma1
    {σ : Signature.{u, v, w}}
    {bound : LevyBound σ} {formula : Formula σ} (hFormula : IsDelta0 bound formula) :
    IsSigma1 bound formula :=
  IsSigma1.delta0 hFormula
/-- `Delta0` 公式可直接提升为 `Pi1`。 -/
theorem to_pi1
    {σ : Signature.{u, v, w}}
    {bound : LevyBound σ} {formula : Formula σ} (hFormula : IsDelta0 bound formula) :
    IsPi1 bound formula :=
  IsPi1.delta0 hFormula
end IsDelta0
namespace IsDelta0
/--
用 bound-closed 项替换自由变量保持相对 `Delta0` 层级。
bound-closed 条件保证替换项不会进入有界量词的界项后捕获其第 `0` 个 binder。
-/
theorem substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (hReplacement : replacement.BoundClosed)
    (hFormula : IsDelta0 bound formula) :
    IsDelta0 bound (Formula.substituteFree target id replacement formula) := by
  cases hFormula with
  | falsum =>
      exact IsDelta0.falsum
  | truth =>
      exact IsDelta0.truth
  | rel relation arguments =>
      exact IsDelta0.rel relation (arguments.map (Term.substituteFree target id replacement))
  | equal left right =>
      exact IsDelta0.equal (Term.substituteFree target id replacement left) (Term.substituteFree target id replacement right)
  | neg hBody =>
      exact IsDelta0.neg (substituteFree target id replacement hReplacement hBody)
  | conj hLeft hRight =>
      exact IsDelta0.conj (substituteFree target id replacement hReplacement hLeft) (substituteFree target id replacement hReplacement hRight)
  | disj hLeft hRight =>
      exact IsDelta0.disj (substituteFree target id replacement hReplacement hLeft) (substituteFree target id replacement hReplacement hRight)
  | imp hLeft hRight =>
      exact IsDelta0.imp (substituteFree target id replacement hReplacement hLeft) (substituteFree target id replacement hReplacement hRight)
  | iff hLeft hRight =>
      exact IsDelta0.iff (substituteFree target id replacement hReplacement hLeft) (substituteFree target id replacement hReplacement hRight)
  | bounded_forall setTerm bodyFormula hSet hBody =>
      simpa [Formula.substituteFree, Term.substituteFree] using
        IsDelta0.bounded_forall (Term.substituteFree target id replacement setTerm) (Formula.substituteFree target id replacement bodyFormula)
          (Term.BoundFreeAt.substituteFree hSet (Term.bound_free_at_of_bound_closed
              bound.sort 0 replacement hReplacement)) (substituteFree target id replacement hReplacement hBody)
  | bounded_exists setTerm bodyFormula hSet hBody =>
      simpa [Formula.substituteFree, Term.substituteFree] using
        IsDelta0.bounded_exists (Term.substituteFree target id replacement setTerm) (Formula.substituteFree target id replacement bodyFormula)
          (Term.BoundFreeAt.substituteFree hSet (Term.bound_free_at_of_bound_closed
              bound.sort 0 replacement hReplacement)) (substituteFree target id replacement hReplacement hBody)
  | guarded_exists setTerm bodyFormula hSet hBody hGuard =>
      simpa [Formula.substituteFree] using
        IsDelta0.guarded_exists
          (Term.substituteFree target id replacement setTerm)
          (Formula.substituteFree target id replacement bodyFormula)
          (Term.BoundFreeAt.substituteFree hSet
            (Term.bound_free_at_of_bound_closed
              bound.sort 0 replacement hReplacement))
          (substituteFree target id replacement hReplacement hBody)
          (MembershipGuard.substituteFree
            target id replacement hGuard)
/-- 关闭自由变量保持相对 `Delta0` 层级。 -/
theorem closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (hFormula : IsDelta0 bound formula) :
    IsDelta0 bound (Formula.closeFreeAt target id depth formula) := by
  cases hFormula with
  | falsum =>
      exact IsDelta0.falsum
  | truth =>
      exact IsDelta0.truth
  | rel relation arguments =>
      exact IsDelta0.rel relation (arguments.map (Term.closeFreeAt target id depth))
  | equal left right =>
      exact IsDelta0.equal (Term.closeFreeAt target id depth left) (Term.closeFreeAt target id depth right)
  | neg hBody =>
      exact IsDelta0.neg (closeFreeAt target id depth hBody)
  | conj hLeft hRight =>
      exact IsDelta0.conj (closeFreeAt target id depth hLeft) (closeFreeAt target id depth hRight)
  | disj hLeft hRight =>
      exact IsDelta0.disj (closeFreeAt target id depth hLeft) (closeFreeAt target id depth hRight)
  | imp hLeft hRight =>
      exact IsDelta0.imp (closeFreeAt target id depth hLeft) (closeFreeAt target id depth hRight)
  | iff hLeft hRight =>
      exact IsDelta0.iff (closeFreeAt target id depth hLeft) (closeFreeAt target id depth hRight)
  | bounded_forall setTerm bodyFormula hSet hBody =>
      have hSafe :
          target ≠ bound.sort ∨
            Formula.next_depth target bound.sort depth ≠ 0 := by
        by_cases hSort : target = bound.sort
        · right
          simp [Formula.next_depth, hSort]
        · exact Or.inl hSort
      simpa [Formula.closeFreeAt] using
        IsDelta0.bounded_forall (Term.closeFreeAt target id (Formula.next_depth target bound.sort depth)
            setTerm) (Formula.closeFreeAt target id (Formula.next_depth target bound.sort depth)
            bodyFormula) (Term.BoundFreeAt.closeFreeAt_zero hSet hSafe) (closeFreeAt target id (Formula.next_depth target bound.sort depth)
            hBody)
  | bounded_exists setTerm bodyFormula hSet hBody =>
      have hSafe :
          target ≠ bound.sort ∨
            Formula.next_depth target bound.sort depth ≠ 0 := by
        by_cases hSort : target = bound.sort
        · right
          simp [Formula.next_depth, hSort]
        · exact Or.inl hSort
      simpa [Formula.closeFreeAt] using
        IsDelta0.bounded_exists (Term.closeFreeAt target id (Formula.next_depth target bound.sort depth)
            setTerm) (Formula.closeFreeAt target id (Formula.next_depth target bound.sort depth)
            bodyFormula) (Term.BoundFreeAt.closeFreeAt_zero hSet hSafe) (closeFreeAt target id (Formula.next_depth target bound.sort depth)
            hBody)
  | guarded_exists setTerm bodyFormula hSet hBody hGuard =>
      have hSafe :
          target ≠ bound.sort ∨
            Formula.next_depth target bound.sort depth ≠ 0 := by
        by_cases hSort : target = bound.sort
        · right
          simp [Formula.next_depth, hSort]
        · exact Or.inl hSort
      simpa [Formula.closeFreeAt] using
        IsDelta0.guarded_exists
          (Term.closeFreeAt target id
            (Formula.next_depth target bound.sort depth) setTerm)
          (Formula.closeFreeAt target id
            (Formula.next_depth target bound.sort depth) bodyFormula)
          (Term.BoundFreeAt.closeFreeAt_zero hSet hSafe)
          (closeFreeAt target id
            (Formula.next_depth target bound.sort depth) hBody)
          (MembershipGuard.closeFreeAt_after_binder
            target id depth hGuard)
/--
以新鲜自由变量书写的有界全称量词保持 `Delta0`。
该接口直接对应 `∀ₘ[sort, id], (x#id ∈ bound) → body` 的表面记号。
-/
theorem bounded_forall_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} (id : FreeVarId) (setTerm : Term σ)
    {body : Formula σ} (hFresh : (bound.sort, id) ∉ Term.freeSupport setTerm) (hBody : IsDelta0 bound body) :
    IsDelta0 bound (.forallE bound.sort (Formula.closeFreeAt bound.sort id 0 (.imp (.rel bound.relation
              [.var (.fvar bound.sort id), setTerm])
            body))) := by
  simpa [Formula.closeFreeAt, Term.closeFreeAt] using
    IsDelta0.bounded_forall (Term.closeFreeAt bound.sort id 0 setTerm) (Formula.closeFreeAt bound.sort id 0 body)
      (Term.bound_free_at_closeFreeAt_zero_of_not_mem
        bound.sort id setTerm hFresh) (hBody.closeFreeAt bound.sort id 0)
/--
以新鲜自由变量书写的有界存在量词保持 `Delta0`。
-/
theorem bounded_exists_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} (id : FreeVarId) (setTerm : Term σ)
    {body : Formula σ} (hFresh : (bound.sort, id) ∉ Term.freeSupport setTerm) (hBody : IsDelta0 bound body) :
    IsDelta0 bound (.existsE bound.sort (Formula.closeFreeAt bound.sort id 0 (.conj (.rel bound.relation
              [.var (.fvar bound.sort id), setTerm])
            body))) := by
  simpa [Formula.closeFreeAt, Term.closeFreeAt] using
    IsDelta0.bounded_exists (Term.closeFreeAt bound.sort id 0 setTerm) (Formula.closeFreeAt bound.sort id 0 body)
      (Term.bound_free_at_closeFreeAt_zero_of_not_mem
        bound.sort id setTerm hFresh) (hBody.closeFreeAt bound.sort id 0)

/--
具名自由变量的成员 guard 可以直接形成非正规结合形态的有界存在量词。
-/
theorem guarded_exists_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} (id : FreeVarId)
    (setTerm : Term σ) {body : Formula σ}
    (hFresh :
      (bound.sort, id) ∉ Term.freeSupport setTerm)
    (hBody : IsDelta0 bound body)
    (hGuard :
      FreeMembershipGuard bound id setTerm body) :
    IsDelta0 bound
      (.existsE bound.sort
        (Formula.closeFreeAt bound.sort id 0 body)) := by
  exact
    IsDelta0.guarded_exists
      (Term.closeFreeAt bound.sort id 0 setTerm)
      (Formula.closeFreeAt bound.sort id 0 body)
      (Term.bound_free_at_closeFreeAt_zero_of_not_mem
        bound.sort id setTerm hFresh)
      (hBody.closeFreeAt bound.sort id 0)
      hGuard.closeFreeAt
end IsDelta0
mutual
  /-- 用 bound-closed 项替换自由变量保持相对 `Sigma1` 层级。 -/
  theorem IsSigma1.substituteFree
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {bound : LevyBound σ} {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (hReplacement : replacement.BoundClosed)
      (hFormula : IsSigma1 bound formula) :
      IsSigma1 bound (Formula.substituteFree target id replacement formula) := by
    cases hFormula with
    | delta0 hDelta =>
        exact IsSigma1.delta0 (IsDelta0.substituteFree
            target id replacement hReplacement hDelta)
    | neg hBody =>
        exact IsSigma1.neg (IsPi1.substituteFree
            target id replacement hReplacement hBody)
    | conj hLeft hRight =>
        exact IsSigma1.conj (IsSigma1.substituteFree
            target id replacement hReplacement hLeft) (IsSigma1.substituteFree
            target id replacement hReplacement hRight)
    | disj hLeft hRight =>
        exact IsSigma1.disj (IsSigma1.substituteFree
            target id replacement hReplacement hLeft) (IsSigma1.substituteFree
            target id replacement hReplacement hRight)
    | imp hLeft hRight =>
        exact IsSigma1.imp (IsPi1.substituteFree
            target id replacement hReplacement hLeft) (IsSigma1.substituteFree
            target id replacement hReplacement hRight)
    | existsE sort hBody =>
        simpa [Formula.substituteFree] using
          IsSigma1.existsE sort (IsSigma1.substituteFree
              target id replacement hReplacement hBody)
    | bounded_forall setTerm bodyFormula hSet hBody =>
        simpa [Formula.substituteFree, Term.substituteFree] using
          IsSigma1.bounded_forall (Term.substituteFree target id replacement setTerm) (Formula.substituteFree target id replacement bodyFormula)
            (Term.BoundFreeAt.substituteFree hSet (Term.bound_free_at_of_bound_closed
                bound.sort 0 replacement hReplacement)) (IsSigma1.substituteFree
              target id replacement hReplacement hBody)
    | bounded_exists setTerm bodyFormula hSet hBody =>
        simpa [Formula.substituteFree, Term.substituteFree] using
          IsSigma1.bounded_exists (Term.substituteFree target id replacement setTerm) (Formula.substituteFree target id replacement bodyFormula)
            (Term.BoundFreeAt.substituteFree hSet (Term.bound_free_at_of_bound_closed
                bound.sort 0 replacement hReplacement)) (IsSigma1.substituteFree
              target id replacement hReplacement hBody)
  /-- 用 bound-closed 项替换自由变量保持相对 `Pi1` 层级。 -/
  theorem IsPi1.substituteFree
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {bound : LevyBound σ} {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (hReplacement : replacement.BoundClosed)
      (hFormula : IsPi1 bound formula) :
      IsPi1 bound (Formula.substituteFree target id replacement formula) := by
    cases hFormula with
    | delta0 hDelta =>
        exact IsPi1.delta0 (IsDelta0.substituteFree
            target id replacement hReplacement hDelta)
    | neg hBody =>
        exact IsPi1.neg (IsSigma1.substituteFree
            target id replacement hReplacement hBody)
    | conj hLeft hRight =>
        exact IsPi1.conj (IsPi1.substituteFree
            target id replacement hReplacement hLeft) (IsPi1.substituteFree
            target id replacement hReplacement hRight)
    | disj hLeft hRight =>
        exact IsPi1.disj (IsPi1.substituteFree
            target id replacement hReplacement hLeft) (IsPi1.substituteFree
            target id replacement hReplacement hRight)
    | imp hLeft hRight =>
        exact IsPi1.imp (IsSigma1.substituteFree
            target id replacement hReplacement hLeft) (IsPi1.substituteFree
            target id replacement hReplacement hRight)
    | forallE sort hBody =>
        simpa [Formula.substituteFree] using
          IsPi1.forallE sort (IsPi1.substituteFree
              target id replacement hReplacement hBody)
    | bounded_forall setTerm bodyFormula hSet hBody =>
        simpa [Formula.substituteFree, Term.substituteFree] using
          IsPi1.bounded_forall (Term.substituteFree target id replacement setTerm) (Formula.substituteFree target id replacement bodyFormula)
            (Term.BoundFreeAt.substituteFree hSet (Term.bound_free_at_of_bound_closed
                bound.sort 0 replacement hReplacement)) (IsPi1.substituteFree
              target id replacement hReplacement hBody)
    | bounded_exists setTerm bodyFormula hSet hBody =>
        simpa [Formula.substituteFree, Term.substituteFree] using
          IsPi1.bounded_exists (Term.substituteFree target id replacement setTerm) (Formula.substituteFree target id replacement bodyFormula)
            (Term.BoundFreeAt.substituteFree hSet (Term.bound_free_at_of_bound_closed
                bound.sort 0 replacement hReplacement)) (IsPi1.substituteFree
              target id replacement hReplacement hBody)
end
mutual
  /-- 关闭自由变量保持相对 `Sigma1` 层级。 -/
  theorem IsSigma1.closeFreeAt
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {bound : LevyBound σ} {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (hFormula : IsSigma1 bound formula) :
      IsSigma1 bound (Formula.closeFreeAt target id depth formula) := by
    cases hFormula with
    | delta0 hDelta =>
        exact IsSigma1.delta0 (IsDelta0.closeFreeAt target id depth hDelta)
    | neg hBody =>
        exact IsSigma1.neg (IsPi1.closeFreeAt target id depth hBody)
    | conj hLeft hRight =>
        exact IsSigma1.conj (IsSigma1.closeFreeAt target id depth hLeft) (IsSigma1.closeFreeAt target id depth hRight)
    | disj hLeft hRight =>
        exact IsSigma1.disj (IsSigma1.closeFreeAt target id depth hLeft) (IsSigma1.closeFreeAt target id depth hRight)
    | imp hLeft hRight =>
        exact IsSigma1.imp (IsPi1.closeFreeAt target id depth hLeft) (IsSigma1.closeFreeAt target id depth hRight)
    | existsE sort hBody =>
        simpa [Formula.closeFreeAt] using
          IsSigma1.existsE sort (IsSigma1.closeFreeAt target id (Formula.next_depth target sort depth) hBody)
    | bounded_forall setTerm bodyFormula hSet hBody =>
        have hSafe :
            target ≠ bound.sort ∨
              Formula.next_depth target bound.sort depth ≠ 0 := by
          by_cases hSort : target = bound.sort
          · right
            simp [Formula.next_depth, hSort]
          · exact Or.inl hSort
        simpa [Formula.closeFreeAt] using
          IsSigma1.bounded_forall (Term.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              setTerm) (Formula.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              bodyFormula) (Term.BoundFreeAt.closeFreeAt_zero hSet hSafe) (IsSigma1.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              hBody)
    | bounded_exists setTerm bodyFormula hSet hBody =>
        have hSafe :
            target ≠ bound.sort ∨
              Formula.next_depth target bound.sort depth ≠ 0 := by
          by_cases hSort : target = bound.sort
          · right
            simp [Formula.next_depth, hSort]
          · exact Or.inl hSort
        simpa [Formula.closeFreeAt] using
          IsSigma1.bounded_exists (Term.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              setTerm) (Formula.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              bodyFormula) (Term.BoundFreeAt.closeFreeAt_zero hSet hSafe) (IsSigma1.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              hBody)
  /-- 关闭自由变量保持相对 `Pi1` 层级。 -/
  theorem IsPi1.closeFreeAt
      {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
      {bound : LevyBound σ} {formula : Formula σ} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (hFormula : IsPi1 bound formula) :
      IsPi1 bound (Formula.closeFreeAt target id depth formula) := by
    cases hFormula with
    | delta0 hDelta =>
        exact IsPi1.delta0 (IsDelta0.closeFreeAt target id depth hDelta)
    | neg hBody =>
        exact IsPi1.neg (IsSigma1.closeFreeAt target id depth hBody)
    | conj hLeft hRight =>
        exact IsPi1.conj (IsPi1.closeFreeAt target id depth hLeft) (IsPi1.closeFreeAt target id depth hRight)
    | disj hLeft hRight =>
        exact IsPi1.disj (IsPi1.closeFreeAt target id depth hLeft) (IsPi1.closeFreeAt target id depth hRight)
    | imp hLeft hRight =>
        exact IsPi1.imp (IsSigma1.closeFreeAt target id depth hLeft) (IsPi1.closeFreeAt target id depth hRight)
    | forallE sort hBody =>
        simpa [Formula.closeFreeAt] using
          IsPi1.forallE sort (IsPi1.closeFreeAt target id (Formula.next_depth target sort depth) hBody)
    | bounded_forall setTerm bodyFormula hSet hBody =>
        have hSafe :
            target ≠ bound.sort ∨
              Formula.next_depth target bound.sort depth ≠ 0 := by
          by_cases hSort : target = bound.sort
          · right
            simp [Formula.next_depth, hSort]
          · exact Or.inl hSort
        simpa [Formula.closeFreeAt] using
          IsPi1.bounded_forall (Term.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              setTerm) (Formula.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              bodyFormula) (Term.BoundFreeAt.closeFreeAt_zero hSet hSafe) (IsPi1.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              hBody)
    | bounded_exists setTerm bodyFormula hSet hBody =>
        have hSafe :
            target ≠ bound.sort ∨
              Formula.next_depth target bound.sort depth ≠ 0 := by
          by_cases hSort : target = bound.sort
          · right
            simp [Formula.next_depth, hSort]
          · exact Or.inl hSort
        simpa [Formula.closeFreeAt] using
          IsPi1.bounded_exists (Term.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              setTerm) (Formula.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              bodyFormula) (Term.BoundFreeAt.closeFreeAt_zero hSet hSafe) (IsPi1.closeFreeAt target id (Formula.next_depth target bound.sort depth)
              hBody)
end
namespace IsSigma1
/--
以自由变量书写的无界存在量词保持 `Sigma1`。
该接口直接对应 `∃ₘ[sort, id], body` 的表面记号；关闭自由变量只改变项中的变量
表示，不改变 Lévy 层级。
-/
theorem exists_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} (sort : σ.SortSymbol) (id : FreeVarId)
    {body : Formula σ} (hBody : IsSigma1 bound body) :
    IsSigma1 bound (.existsE sort (Formula.closeFreeAt sort id 0 body)) :=
  IsSigma1.existsE sort (hBody.closeFreeAt sort id 0)
/--
以新鲜自由变量书写的有界全称量词保持 `Sigma1`。
该接口直接对应 `∀ₘ[sort, id], (x#id ∈ bound) → body` 一类表面记号。
-/
theorem bounded_forall_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} (id : FreeVarId) (setTerm : Term σ)
    {body : Formula σ} (hFresh : (bound.sort, id) ∉ Term.freeSupport setTerm) (hBody : IsSigma1 bound body) :
    IsSigma1 bound (.forallE bound.sort (Formula.closeFreeAt bound.sort id 0 (.imp (.rel bound.relation
              [.var (.fvar bound.sort id), setTerm])
            body))) := by
  simpa [Formula.closeFreeAt, Term.closeFreeAt] using
    IsSigma1.bounded_forall (Term.closeFreeAt bound.sort id 0 setTerm) (Formula.closeFreeAt bound.sort id 0 body)
      (Term.bound_free_at_closeFreeAt_zero_of_not_mem
        bound.sort id setTerm hFresh) (hBody.closeFreeAt bound.sort id 0)
/-- 以新鲜自由变量书写的有界存在量词保持 `Sigma1`。 -/
theorem bounded_exists_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ} (id : FreeVarId) (setTerm : Term σ)
    {body : Formula σ} (hFresh : (bound.sort, id) ∉ Term.freeSupport setTerm) (hBody : IsSigma1 bound body) :
    IsSigma1 bound (.existsE bound.sort (Formula.closeFreeAt bound.sort id 0 (.conj (.rel bound.relation
              [.var (.fvar bound.sort id), setTerm])
            body))) := by
  simpa [Formula.closeFreeAt, Term.closeFreeAt] using
    IsSigma1.bounded_exists (Term.closeFreeAt bound.sort id 0 setTerm) (Formula.closeFreeAt bound.sort id 0 body)
      (Term.bound_free_at_closeFreeAt_zero_of_not_mem
        bound.sort id setTerm hFresh) (hBody.closeFreeAt bound.sort id 0)
end IsSigma1
end Formula
end FirstOrder
end Logic
end YesMetaZFC
