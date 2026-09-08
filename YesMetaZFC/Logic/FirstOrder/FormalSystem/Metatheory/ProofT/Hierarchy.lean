import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodeDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicFormulaTemplate

/-!
# `ProofT` 的 Lévy 层级接口

本模块只处理证明图与可证性谓词的量词骨架。所有量词都直接使用内在 bound
上下文，证明码与结论的排序及作用域由类型索引保证，不再需要自由变量编号、关闭
自由变量或新鲜性旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- Rosser 比较所使用的纯句法码域。 -/
structure Delta0CodeDomain where
  condition : FormulaTemplate.Unary
  delta0 :
    ∀ {bound free : SetContext} (point : SetTerm bound free),
      Formula.IsDelta0 set_levy_bound (condition point)

/-- 二元对象证明图的纯句法接口。 -/
structure Delta0ProofGraph where
  condition : FormulaTemplate.Binary
  delta0 :
    ∀ {bound free : SetContext}
      (proofCode conclusion : SetTerm bound free),
      Formula.IsDelta0 set_levy_bound
        (condition proofCode conclusion)

/-- `Sigma1ProofGraph` 只记录正向证明图的 `Sigma1` 分类。 -/
structure Sigma1ProofGraph where
  condition : FormulaTemplate.Binary
  sigma1 :
    ∀ {bound free : SetContext}
      (proofCode conclusion : SetTerm bound free),
      Formula.IsSigma1 set_levy_bound
        (condition proofCode conclusion)

namespace Delta0ProofGraph

/-- `Delta0` proof graph 的 `Sigma1` 投影。 -/
def toSigma1 (G : Delta0ProofGraph) : Sigma1ProofGraph where
  condition := G.condition
  sigma1 proofCode conclusion :=
    (G.delta0 proofCode conclusion).to_sigma1

/-- `Delta0` proof graph 的正公式自动提升为 `Sigma1`。 -/
theorem condition_sigma1
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (G.condition proofCode conclusion) :=
  (G.delta0 proofCode conclusion).to_sigma1

/-- `Delta0` proof graph 的同一公式自动提升为 `Pi1`。 -/
theorem condition_pi1
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (G.condition proofCode conclusion) :=
  (G.delta0 proofCode conclusion).to_pi1

/-- proof graph 的补关系由一个 `Pi1` 公式给出。 -/
theorem neg_condition_pi1
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.condition proofCode conclusion) :=
  Formula.IsLevel1.neg (G.condition_sigma1 proofCode conclusion)

/-- 普通一元可证性谓词。 -/
def provability
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (conclusion : SetTerm bound free) : SetFormula bound free :=
  Formula.existsE SetSort.set
    (G.condition
      (bₘ[.here])
      (conclusion.weakenBound SetSort.set))

/-- `∃ p, Proof(p,c)` 的正式 `Sigma1` 分类。 -/
theorem provability_sigma1
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (conclusion : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (G.provability conclusion) := by
  simpa [provability] using
    Formula.IsLevel1.existsE (ℬ := set_levy_bound) SetSort.set
      (G.condition_sigma1
        (bₘ[.here])
        (conclusion.weakenBound SetSort.set))

/-- 普通不可证性谓词 `¬∃ p, Proof(p,c)` 的正式 `Pi1` 分类。 -/
theorem neg_provability_pi1
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (conclusion : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.provability conclusion) :=
  Formula.IsLevel1.neg
    (G.provability_sigma1 conclusion)

/-- 在给定证明码以下不存在右侧公式的证明。 -/
def no_smaller
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (proofBound conclusion : SetTerm bound free) :
    SetFormula bound free :=
  set_levy_bound.boundedForall proofBound
    (¬ₘ G.condition
      (bₘ[.here])
      (conclusion.weakenBound SetSort.set))

/-- `no_smaller` 沿 free 上下文弱化逐项作用。 -/
@[simp] theorem no_smaller_weakenFree
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (introduced : SetSort)
    (proofBound conclusion : SetTerm bound free) :
    (G.no_smaller proofBound conclusion).weakenFree introduced =
      G.no_smaller (proofBound.weakenFree introduced)
        (conclusion.weakenFree introduced) := by
  simp [no_smaller, Formula.LevyBound.boundedForall,
    Term.weakenFree_weakenBound]

/-- 顶部证明码变量实例化后直接恢复普通 `no_smaller`。 -/
@[simp] theorem no_smaller_instantiateTop_bvar
    (G : Delta0ProofGraph)
    {free : SetContext}
    (conclusion replacement : SetOpenTerm free) :
    Formula.instantiateTop replacement
        (G.no_smaller (.bvar .here)
          (conclusion.weakenBound SetSort.set)) =
      G.no_smaller replacement conclusion := by
  have hConclusionNested :
      (Term.weakenBound SetSort.set
        (Term.weakenBound SetSort.set conclusion)).substituteMapped
          (VariableSubstitution.liftBound SetSort.set
            (VariableSubstitution.instantiateTop replacement))
          VariableSubstitution.freeId =
        Term.weakenBound SetSort.set conclusion := by
    simp []
  simp [no_smaller, Formula.LevyBound.boundedForall,
    Formula.instantiateTop, Formula.substitute,
    Substitution.instantiateTop, Formula.substituteMapped,
    Term.substituteMapped,
    FormulaTemplate.apply_two_substituteMapped,
    VariableSubstitution.liftBound,
    VariableSubstitution.instantiateTop,
    hConclusionNested]

/-- 有限初始段上的否定搜索仍然是 `Delta0`。 -/
theorem no_smaller_delta0
    (G : Delta0ProofGraph)
    {bound free : SetContext}
    (proofBound conclusion : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (G.no_smaller proofBound conclusion) := by
  simpa [no_smaller] using
    Formula.IsDelta0.bounded_forall proofBound
      (Formula.IsDelta0.neg
        (G.delta0
          (bₘ[.here])
          (conclusion.weakenBound SetSort.set)))

/-- 左侧有证明，且在该证明码以下没有右侧证明。 -/
def comparison
    (G : Delta0ProofGraph)
    (D : Delta0CodeDomain)
    {bound free : SetContext}
    (left right : SetTerm bound free) : SetFormula bound free :=
  Formula.existsE SetSort.set
    (D.condition (bₘ[.here]) ∧ₘ
      (G.condition
          (bₘ[.here])
          (left.weakenBound SetSort.set) ∧ₘ
        G.no_smaller
          (bₘ[.here])
          (right.weakenBound SetSort.set)))

/-- Rosser 有限比较的正式 `Sigma1` 分类。 -/
theorem comparison_sigma1
    (G : Delta0ProofGraph)
    (D : Delta0CodeDomain)
    {bound free : SetContext}
    (left right : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (G.comparison D left right) := by
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (D.condition (bₘ[.here]) ∧ₘ
          (G.condition
              (bₘ[.here])
              (left.weakenBound SetSort.set) ∧ₘ
            G.no_smaller
              (bₘ[.here])
              (right.weakenBound SetSort.set))) :=
    Formula.IsDelta0.conj
      (D.delta0 (bₘ[.here]))
      (Formula.IsDelta0.conj
        (G.delta0
          (bₘ[.here])
          (left.weakenBound SetSort.set))
        (G.no_smaller_delta0
          (bₘ[.here])
          (right.weakenBound SetSort.set)))
  simpa [comparison] using
    Formula.IsLevel1.existsE (ℬ := set_levy_bound) SetSort.set hBody.to_sigma1

/-- Rosser 有限比较之否定的正式 `Pi1` 分类。 -/
theorem neg_comparison_pi1
    (G : Delta0ProofGraph)
    (D : Delta0CodeDomain)
    {bound free : SetContext}
    (left right : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.comparison D left right) :=
  Formula.IsLevel1.neg
    (G.comparison_sigma1 D left right)

/-- 把右侧固定为左侧否定码得到 Rosser 可证性谓词。 -/
def rosser_provability
    (G : Delta0ProofGraph)
    (D : Delta0CodeDomain)
    {bound free : SetContext}
    (code : SetTerm bound free) : SetFormula bound free :=
  G.comparison D code (neg_codeₘ(code))

/-- Rosser 可证性谓词的正式 `Sigma1` 分类。 -/
theorem rosser_provability_sigma1
    (G : Delta0ProofGraph)
    (D : Delta0CodeDomain)
    {bound free : SetContext}
    (code : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (G.rosser_provability D code) := by
  simpa [rosser_provability] using
    G.comparison_sigma1 D code (neg_codeₘ(code))

/-- Rosser 不可证性谓词的正式 `Pi1` 分类。 -/
theorem neg_rosser_provability_pi1
    (G : Delta0ProofGraph)
    (D : Delta0CodeDomain)
    {bound free : SetContext}
    (code : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.rosser_provability D code) :=
  Formula.IsLevel1.neg
    (G.rosser_provability_sigma1 D code)

end Delta0ProofGraph

namespace Sigma1ProofGraph

/-- `Sigma1` proof graph 的正向条件分类。 -/
theorem condition_sigma1
    (G : Sigma1ProofGraph)
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (G.condition proofCode conclusion) :=
  G.sigma1 proofCode conclusion

/-- 普通一元可证性谓词。 -/
def provability
    (G : Sigma1ProofGraph)
    {bound free : SetContext}
    (conclusion : SetTerm bound free) : SetFormula bound free :=
  Formula.existsE SetSort.set
    (G.condition
      (bₘ[.here])
      (conclusion.weakenBound SetSort.set))

/-- `∃ p, Proof(p,c)` 的正式 `Sigma1` 分类。 -/
theorem provability_sigma1
    (G : Sigma1ProofGraph)
    {bound free : SetContext}
    (conclusion : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (G.provability conclusion) := by
  simpa [provability] using
    Formula.IsLevel1.existsE (ℬ := set_levy_bound) SetSort.set
      (G.condition_sigma1
        (bₘ[.here])
        (conclusion.weakenBound SetSort.set))

/-- 普通不可证性谓词的正式 `Pi1` 分类。 -/
theorem neg_provability_pi1
    (G : Sigma1ProofGraph)
    {bound free : SetContext}
    (conclusion : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.provability conclusion) :=
  Formula.IsLevel1.neg
    (G.provability_sigma1 conclusion)

end Sigma1ProofGraph
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
