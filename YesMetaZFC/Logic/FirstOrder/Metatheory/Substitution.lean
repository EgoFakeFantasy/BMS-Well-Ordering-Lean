import YesMetaZFC.Logic.FirstOrder.Admissibility
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Semantics
/-!
# 一阶替换的统一正确性合同
本模块把底层已经分别证明的 sort 保持、scope 保持和解释换元定理组合成两个公共
接口。替换项必须 admissible；其中的空 bound scope 条件正是避免穿越量词时捕获
de Bruijn 变量所需的条件。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w x
/-- 项替换同时保持 admissibility，并等价于环境中的自由变量单点更新。 -/
theorem term_substitution_correct
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {term replacement : Term σ} {termSort targetSort : σ.SortSymbol} (targetId : FreeVarId) (hTerm : Term.Admissible term termSort)
    (hReplacement : Term.Admissible replacement targetSort) :
    Term.Admissible (Term.substituteFree targetSort targetId replacement term)
        termSort ∧
      ∀ {M : Structure.{u, v, w, x} σ} (env : Env M),
        Term.eval env (Term.substituteFree targetSort targetId replacement term) =
          Term.eval (env.setFree targetSort targetId (Term.eval env replacement) (Term.eval_sort_of_wellSorted hReplacement.1))
            term := by
  constructor
  · exact
      ⟨TermWellSorted.substituteFree targetId hTerm.1 hReplacement.1,
        Term.substituteFree_scoped hTerm.2 hReplacement.2⟩
  · intro M env
    exact Term.eval_substituteFree env targetSort targetId replacement
      hReplacement.1 term
/-- 公式替换同时保持 admissibility，并满足标准替换引理。 -/
theorem formula_substitution_correct
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {replacement : Term σ} (targetSort : σ.SortSymbol) (targetId : FreeVarId) (hFormula : Formula.Admissible formula)
    (hReplacement : Term.Admissible replacement targetSort) :
    Formula.Admissible (Formula.substituteFree targetSort targetId replacement formula) ∧
      ∀ {M : Structure.{u, v, w, x} σ} (env : Env M),
        Formula.satisfies env (Formula.substituteFree targetSort targetId replacement formula) ↔
          Formula.satisfies (env.setFree targetSort targetId (Term.eval env replacement) (Term.eval_sort_of_wellSorted hReplacement.1))
            formula := by
  constructor
  · exact Formula.Admissible.substituteFree targetSort targetId
      hFormula hReplacement
  · intro M env
    exact Formula.satisfies_substituteFree env targetSort targetId replacement
      hReplacement.1 hReplacement.2 formula
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
