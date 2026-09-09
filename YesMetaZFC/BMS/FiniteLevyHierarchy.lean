import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Logic.FirstOrder.FormulaComplexity
import YesMetaZFC.Logic.Semantics

/-!
# 任意有限层的 Lévy 量词层级

Hunter Lemma 2.6 需要在任意有限 `Sigma (n+1)` 层反射一个有限关系图。
这里在新版内在良构语法上定义累积的有限层级；bound/free 上下文是类型索引，
因而量词构造和有限合取都保持排序及作用域正确。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace Formula

mutual
  /-- 累积的 `Sigma_level` 语法类。 -/
  inductive IsSigmaFinite {σ : Signature.{u, v, w}}
      (ℬ : LevyBound σ) : Nat → {bound free : SortContext σ} →
        Formula σ bound free → Prop where
    | delta0 {level bound free} {formula : Formula σ bound free} :
        IsDelta0 ℬ formula → IsSigmaFinite ℬ level formula
    | neg {level bound free} {body : Formula σ bound free} :
        IsPiFinite ℬ level body → IsSigmaFinite ℬ level (.neg body)
    | conj {level bound free} {left right : Formula σ bound free} :
        IsSigmaFinite ℬ level left → IsSigmaFinite ℬ level right →
          IsSigmaFinite ℬ level (.conj left right)
    | disj {level bound free} {left right : Formula σ bound free} :
        IsSigmaFinite ℬ level left → IsSigmaFinite ℬ level right →
          IsSigmaFinite ℬ level (.disj left right)
    | imp {level bound free} {left right : Formula σ bound free} :
        IsPiFinite ℬ level left → IsSigmaFinite ℬ level right →
          IsSigmaFinite ℬ level (.imp left right)
    | existsE {level bound free} (sort : σ.SortSymbol)
        {body : Formula σ (sort :: bound) free} :
        IsSigmaFinite ℬ level body →
          IsSigmaFinite ℬ level (.existsE sort body)
    | lift {level bound free} {formula : Formula σ bound free} :
        IsSigmaFinite ℬ level formula →
          IsSigmaFinite ℬ (level + 1) formula
    | ofPi {level bound free} {formula : Formula σ bound free} :
        IsPiFinite ℬ level formula →
          IsSigmaFinite ℬ (level + 1) formula

  /-- 累积的 `Pi_level` 语法类。 -/
  inductive IsPiFinite {σ : Signature.{u, v, w}}
      (ℬ : LevyBound σ) : Nat → {bound free : SortContext σ} →
        Formula σ bound free → Prop where
    | delta0 {level bound free} {formula : Formula σ bound free} :
        IsDelta0 ℬ formula → IsPiFinite ℬ level formula
    | neg {level bound free} {body : Formula σ bound free} :
        IsSigmaFinite ℬ level body → IsPiFinite ℬ level (.neg body)
    | conj {level bound free} {left right : Formula σ bound free} :
        IsPiFinite ℬ level left → IsPiFinite ℬ level right →
          IsPiFinite ℬ level (.conj left right)
    | disj {level bound free} {left right : Formula σ bound free} :
        IsPiFinite ℬ level left → IsPiFinite ℬ level right →
          IsPiFinite ℬ level (.disj left right)
    | imp {level bound free} {left right : Formula σ bound free} :
        IsSigmaFinite ℬ level left → IsPiFinite ℬ level right →
          IsPiFinite ℬ level (.imp left right)
    | forallE {level bound free} (sort : σ.SortSymbol)
        {body : Formula σ (sort :: bound) free} :
        IsPiFinite ℬ level body →
          IsPiFinite ℬ level (.forallE sort body)
    | lift {level bound free} {formula : Formula σ bound free} :
        IsPiFinite ℬ level formula →
          IsPiFinite ℬ (level + 1) formula
    | ofSigma {level bound free} {formula : Formula σ bound free} :
        IsSigmaFinite ℬ level formula →
          IsPiFinite ℬ (level + 1) formula
end

/-- 右结合有限合取保持 `Sigma_level`。 -/
theorem IsSigmaFinite.conjunctionList {σ : Signature.{u, v, w}}
    {ℬ : LevyBound σ} {level : Nat} {bound free : SortContext σ}
    {formulas : List (Formula σ bound free)}
    (hFormulas : ∀ formula ∈ formulas, IsSigmaFinite ℬ level formula) :
    IsSigmaFinite ℬ level (Formula.conjunctionList formulas) := by
  induction formulas with
  | nil => exact IsSigmaFinite.delta0 IsDelta0.truth
  | cons formula rest ih =>
      cases rest with
      | nil => simpa [Formula.conjunctionList] using hFormulas formula (by simp)
      | cons next tail =>
          apply IsSigmaFinite.conj
          · exact hFormulas formula (by simp)
          · apply ih
            intro member hMember
            exact hFormulas member (by simp [hMember])

/-- 以 `Fin count` 为索引的有限合取。 -/
def conjunctionFin {σ : Signature.{u, v, w}} {bound free : SortContext σ}
    {count : Nat} (formula : Fin count → Formula σ bound free) :
    Formula σ bound free :=
  Formula.conjunctionList (List.ofFn formula)

/-- `Fin` 索引的有限合取保持同一 `Sigma` 层级。 -/
theorem IsSigmaFinite.conjunctionFin {σ : Signature.{u, v, w}}
    {ℬ : LevyBound σ} {level count : Nat} {bound free : SortContext σ}
    {formula : Fin count → Formula σ bound free}
    (hFormula : ∀ index, IsSigmaFinite ℬ level (formula index)) :
    IsSigmaFinite ℬ level (Formula.conjunctionFin formula) := by
  apply IsSigmaFinite.conjunctionList
  intro member hMember
  simp only [List.mem_ofFn] at hMember
  rcases hMember with ⟨index, rfl⟩
  exact hFormula index

/-- 按元层命题选取公式或 `truth` 保持有限 `Sigma` 层级。 -/
theorem IsSigmaFinite.ite_truth {σ : Signature.{u, v, w}}
    {ℬ : LevyBound σ} {level : Nat} {bound free : SortContext σ}
    (condition : Prop) [Decidable condition]
    {formula : Formula σ bound free}
    (hFormula : IsSigmaFinite ℬ level formula) :
    IsSigmaFinite ℬ level (if condition then formula else .truth) := by
  by_cases hCondition : condition
  · simpa [hCondition] using hFormula
  · rw [if_neg hCondition]
    exact .delta0 .truth

/-- 有限合取的语义等价于逐项成立。 -/
@[simp]
theorem satisfies_conjunctionFin_iff {σ : Signature.{u, v, w}}
    {M : FirstOrder.Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : FirstOrder.Env M bound free)
    {count : Nat} (formula : Fin count → Formula σ bound free) :
    FirstOrder.Formula.satisfies env (Formula.conjunctionFin formula) ↔
      ∀ index, FirstOrder.Formula.satisfies env (formula index) := by
  unfold Formula.conjunctionFin
  rw [FirstOrder.Formula.satisfies_conjunctionList_iff]
  simp only [List.mem_ofFn]
  constructor
  · intro hAll index
    exact hAll (formula index) ⟨index, rfl⟩
  · intro hAll member hMember
    rcases hMember with ⟨index, rfl⟩
    exact hAll index

/-- `Sigma` 层级上升一层。 -/
theorem IsSigmaFinite.step {σ : Signature.{u, v, w}}
    {ℬ : LevyBound σ} {level : Nat} {bound free : SortContext σ}
    {formula : Formula σ bound free}
    (hFormula : IsSigmaFinite ℬ level formula) :
    IsSigmaFinite ℬ (level + 1) formula :=
  IsSigmaFinite.lift hFormula

/-- `Pi` 层级上升一层。 -/
theorem IsPiFinite.step {σ : Signature.{u, v, w}}
    {ℬ : LevyBound σ} {level : Nat} {bound free : SortContext σ}
    {formula : Formula σ bound free}
    (hFormula : IsPiFinite ℬ level formula) :
    IsPiFinite ℬ (level + 1) formula :=
  IsPiFinite.lift hFormula

/-- `Sigma` 层级对级别单调。 -/
theorem IsSigmaFinite.mono {σ : Signature.{u, v, w}}
    {ℬ : LevyBound σ} {lowerLevel upperLevel : Nat}
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsSigmaFinite ℬ lowerLevel formula)
    (hLevels : lowerLevel ≤ upperLevel) :
    IsSigmaFinite ℬ upperLevel formula := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le hLevels
  induction difference with
  | zero => simpa using hFormula
  | succ difference ih =>
      have hPrior := ih (Nat.le_add_right lowerLevel difference)
      simpa [Nat.add_assoc] using hPrior.step

/-- `Pi` 层级对级别单调。 -/
theorem IsPiFinite.mono {σ : Signature.{u, v, w}}
    {ℬ : LevyBound σ} {lowerLevel upperLevel : Nat}
    {bound free : SortContext σ} {formula : Formula σ bound free}
    (hFormula : IsPiFinite ℬ lowerLevel formula)
    (hLevels : lowerLevel ≤ upperLevel) :
    IsPiFinite ℬ upperLevel formula := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le hLevels
  induction difference with
  | zero => simpa using hFormula
  | succ difference ih =>
      have hPrior := ih (Nat.le_add_right lowerLevel difference)
      simpa [Nat.add_assoc] using hPrior.step

end Formula
end FirstOrder
end Logic
end YesMetaZFC
