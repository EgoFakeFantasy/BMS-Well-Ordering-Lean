import YesMetaZFC.Logic.FreeVariableSupport.Basic
/-!
# 一阶公式的新鲜自由变量
自由变量编号取自然数，因此任意有限支持都能计算出一个 canonical 新鲜编号。
该接口属于通用语法基础：量词推导、Henkin 见证和后续语法编码都可以共同消费，
不把新鲜变量选择绑定到某个具体完备性构造。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FreshVariable
universe u v w
/--
一个自由变量支持相对于指定 sort 的严格上界。
结果严格大于支持中该 sort 的每个编号，因此结果本身就是新鲜编号。
-/
def support_bound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) : FreeVariable.Support σ → Nat
  | [] => 0
  | (entrySort, id) :: rest =>
      Nat.max (if entrySort = sort then id + 1 else 0) (support_bound sort rest)
/-- 支持成员的编号严格小于 `support_bound`。 -/
theorem support_id_lt_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol} {id : FreeVarId}
    {support : FreeVariable.Support σ} (hMember : (sort, id) ∈ support) :
    id < support_bound sort support := by
  induction support with
  | nil =>
      cases hMember
  | cons head tail ih =>
      rcases head with ⟨entrySort, entryId⟩
      rcases List.mem_cons.mp hMember with hHead | hTail
      · cases hHead
        have hBound :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self id) (Nat.le_max_left (id + 1) (support_bound sort tail))
        simpa [support_bound] using hBound
      · have hBound := ih hTail
        simp only [support_bound]
        exact Nat.lt_of_lt_of_le hBound (Nat.le_max_right _ _)
/-- 单个公式相对于指定 sort 的自由变量编号上界。 -/
def formula_bound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (formula : Formula σ) : Nat :=
  support_bound sort (Formula.freeSupport formula)
/-- 公式支持中的编号严格小于 `formula_bound`。 -/
theorem formula_id_lt_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol} {id : FreeVarId}
    {formula : Formula σ} (hMember : (sort, id) ∈ Formula.freeSupport formula) :
    id < formula_bound sort formula :=
  support_id_lt_m hMember
/-- 有限公式列表相对于指定 sort 的统一自由变量编号上界。 -/
def formulas_bound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) : List (Formula σ) → Nat
  | [] => 0
  | formula :: rest =>
      Nat.max (formula_bound sort formula) (formulas_bound sort rest)
/-- 列表成员支持中的编号严格小于统一上界。 -/
theorem formulas_id_lt_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol} {id : FreeVarId}
    {formula : Formula σ} {formulas : List (Formula σ)} (hFormula : formula ∈ formulas) (hMember : (sort, id) ∈ Formula.freeSupport formula) :
    id < formulas_bound sort formulas := by
  induction formulas with
  | nil =>
      cases hFormula
  | cons head tail ih =>
      rcases List.mem_cons.mp hFormula with rfl | hTail
      · have hBound := formula_id_lt_m hMember
        simp only [formulas_bound]
        exact Nat.lt_of_lt_of_le hBound (Nat.le_max_left _ _)
      · have hBound := ih hTail
        simp only [formulas_bound]
        exact Nat.lt_of_lt_of_le hBound (Nat.le_max_right _ _)
/-- 对有限公式列表选择的 canonical 新鲜自由变量编号。 -/
def fresh_id {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (formulas : List (Formula σ)) : FreeVarId :=
  formulas_bound sort formulas
/-- `fresh_id` 对列表中的每个公式都新鲜。 -/
theorem fresh_id_not_mem_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol}
    {formulas : List (Formula σ)} {formula : Formula σ} (hFormula : formula ∈ formulas) : (sort, fresh_id sort formulas) ∉ Formula.freeSupport formula := by
  intro hMember
  have hLt := formulas_id_lt_m hFormula hMember
  exact Nat.lt_irrefl _ hLt
/-- 用项的自反等式选择的新鲜编号不在该项的自由变量支持中。 -/
theorem fresh_term_not_mem_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (term : Term σ) : (sort, fresh_id sort [Formula.equal term term]) ∉
      Term.freeSupport term := by
  have hFresh :=
    fresh_id_not_mem_m (sort := sort) (formulas := [Formula.equal term term]) (formula := Formula.equal term term) (by simp)
  simpa [Formula.freeSupport] using hFresh
end FreshVariable
end FirstOrder
end Logic
end YesMetaZFC
