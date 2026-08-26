import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncoding
import YesMetaZFC.Logic.FirstOrder.LevyHierarchy

/-!
# `ProofT` 的 Lévy 层级接口

本模块只处理证明图与可证性谓词的量词骨架。具体 replay 如何构造证明图、以及
对象理论如何证明该图正确，仍由各 presentation 自行提供。

核心约定如下：

* 二元 proof graph 若是 `Delta0`，则它同时可作 `Sigma1` 与 `Pi1` 公式使用；
* 普通可证性谓词 `∃ p, Proof(p,c)` 是 `Sigma1`，其否定是 `Pi1`；
* Rosser 的“小于当前证明码不存在反证”仍是 `Delta0`；
* 因而 Rosser 比较谓词是 `Sigma1`，其否定是 `Pi1`。

这些结论完全是句法性的，不引入对象理论公理，也不把任意展开式伪装成
`Delta0`。具体 presentation 必须交付真实的 `IsDelta0` 证明图证据。
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

/-- 纯集合论语言中由成员关系给出的标准 Lévy 有界量词参数。 -/
def set_levy_bound : Formula.LevyBound signature where
  sort := SetSort.set
  relation := RelationSymbol.membership

/-! ## 编码层常用有界公式 -/

/-- 子串逐点条件只在 segment 的有限定义域上量化。 -/
theorem code_substring_at_delta0
    (whole segment start : SetTerm)
    (hSegmentFresh :
      (SetSort.set, 320) ∉
        Term.freeSupport segment) :
    Formula.IsDelta0 set_levy_bound
      (code_substring_at_condition whole segment start) := by
  have hDomainFresh :
      (SetSort.set, 320) ∉
        Term.freeSupport (domₘ(segment)) := by
    simpa [Term.freeSupport, Term.freeSupportList] using
      hSegmentFresh
  have hPoint :
      Formula.IsDelta0 set_levy_bound
        ((((x#320 +ₘ start) ∈ₘ domₘ(whole)) ∧ₘ
          ((whole ·ₘ (x#320 +ₘ start)) ≐ₘ
            (segment ·ₘ x#320)))) :=
    Formula.IsDelta0.conj
      (Formula.IsDelta0.rel
        RelationSymbol.membership
        [x#320 +ₘ start, domₘ(whole)])
      (Formula.IsDelta0.equal
        (whole ·ₘ (x#320 +ₘ start))
        (segment ·ₘ x#320))
  have hBounded :
      Formula.IsDelta0 set_levy_bound
        (∀ₘ[SetSort.set, 320],
          (x#320 ∈ₘ domₘ(segment)) ⟶ₘ
            ((((x#320 +ₘ start) ∈ₘ domₘ(whole)) ∧ₘ
              ((whole ·ₘ (x#320 +ₘ start)) ≐ₘ
                (segment ·ₘ x#320))))) :=
    Formula.IsDelta0.bounded_forall_closeFreeAt
      320 (domₘ(segment)) hDomainFresh hPoint
  exact Formula.IsDelta0.conj
    (Formula.IsDelta0.rel RelationSymbol.membership
      [start, ωₘ])
    (by
      simpa [code_substring_at_condition] using hBounded)

/-- 二元对象证明图的纯句法接口。 -/
structure Delta0ProofGraph where
  condition : SetTerm → SetTerm → SetFormula
  delta0 :
    ∀ proofCode conclusion,
      Formula.IsDelta0 set_levy_bound
        (condition proofCode conclusion)

/-!
`Sigma1ProofGraph` 只记录正向 proof graph 的 `Sigma1` 分类。

它足以导出一元可证性谓词的 `Sigma1` 与其否定的 `Pi1` 分类，但不承诺
Rosser 有限比较所需的 `Delta0` 反证体；后者仍必须使用
`Delta0ProofGraph`。
-/
structure Sigma1ProofGraph where
  condition : SetTerm → SetTerm → SetFormula
  sigma1 :
    ∀ proofCode conclusion,
      Formula.IsSigma1 set_levy_bound
        (condition proofCode conclusion)

namespace Delta0ProofGraph

/-- `Delta0` proof graph 的 `Sigma1` 投影。 -/
def toSigma1
    (G : Delta0ProofGraph) : Sigma1ProofGraph where
  condition := G.condition
  sigma1 proofCode conclusion :=
    (G.delta0 proofCode conclusion).to_sigma1

/-- `Delta0` proof graph 的正公式自动提升为 `Sigma1`。 -/
theorem condition_sigma1
    (G : Delta0ProofGraph)
    (proofCode conclusion : SetTerm) :
    Formula.IsSigma1 set_levy_bound
      (G.condition proofCode conclusion) :=
  (G.delta0 proofCode conclusion).to_sigma1

/-- `Delta0` proof graph 的同一公式自动提升为 `Pi1`。 -/
theorem condition_pi1
    (G : Delta0ProofGraph)
    (proofCode conclusion : SetTerm) :
    Formula.IsPi1 set_levy_bound
      (G.condition proofCode conclusion) :=
  (G.delta0 proofCode conclusion).to_pi1

/-- proof graph 的补关系由一个 `Pi1` 公式给出。 -/
theorem neg_condition_pi1
    (G : Delta0ProofGraph)
    (proofCode conclusion : SetTerm) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.condition proofCode conclusion) :=
  Formula.IsPi1.neg (G.condition_sigma1 proofCode conclusion)

/-- 普通一元可证性谓词。 -/
def provability
    (G : Delta0ProofGraph)
    (conclusion : SetTerm)
    (proofCodeId : FreeVarId) : SetFormula :=
  ∃ₘ[SetSort.set, proofCodeId],
    G.condition (x#proofCodeId) conclusion

/-- `∃ p, Proof(p,c)` 的正式 `Sigma1` 分类。 -/
theorem provability_sigma1
    (G : Delta0ProofGraph)
    (conclusion : SetTerm)
    (proofCodeId : FreeVarId) :
    Formula.IsSigma1 set_levy_bound
      (G.provability conclusion proofCodeId) := by
  simpa [provability] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set proofCodeId
      (G.condition_sigma1 (x#proofCodeId) conclusion)

/-- 普通不可证性谓词 `¬∃ p, Proof(p,c)` 的正式 `Pi1` 分类。 -/
theorem neg_provability_pi1
    (G : Delta0ProofGraph)
    (conclusion : SetTerm)
    (proofCodeId : FreeVarId) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.provability conclusion proofCodeId) :=
  Formula.IsPi1.neg
    (G.provability_sigma1 conclusion proofCodeId)

/-- 在给定证明码以下不存在右侧公式的证明。 -/
def no_smaller
    (G : Delta0ProofGraph)
    (bound conclusion : SetTerm)
    (smallerCodeId : FreeVarId) : SetFormula :=
  ∀ₘ[SetSort.set, smallerCodeId],
    (x#smallerCodeId ∈ₘ bound) ⟶ₘ
      ¬ₘ G.condition (x#smallerCodeId) conclusion

/-- 有限初始段上的否定搜索仍然是 `Delta0`。 -/
theorem no_smaller_delta0
    (G : Delta0ProofGraph)
    (bound conclusion : SetTerm)
    (smallerCodeId : FreeVarId)
    (hBoundFresh :
      (SetSort.set, smallerCodeId) ∉
        Term.freeSupport bound) :
    Formula.IsDelta0 set_levy_bound
      (G.no_smaller bound conclusion smallerCodeId) := by
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (¬ₘ G.condition (x#smallerCodeId) conclusion) :=
    Formula.IsDelta0.neg
      (G.delta0 (x#smallerCodeId) conclusion)
  simpa [no_smaller] using
    Formula.IsDelta0.bounded_forall_closeFreeAt
      smallerCodeId bound hBoundFresh hBody

/-- 左侧有证明，且在该证明码以下没有右侧证明。 -/
def comparison
    (G : Delta0ProofGraph)
    (left right : SetTerm)
    (proofCodeId smallerCodeId : FreeVarId) : SetFormula :=
  ∃ₘ[SetSort.set, proofCodeId],
    G.condition (x#proofCodeId) left ∧ₘ
      G.no_smaller
        (x#proofCodeId) right smallerCodeId

/-- Rosser 有限比较的正式 `Sigma1` 分类。 -/
theorem comparison_sigma1
    (G : Delta0ProofGraph)
    (left right : SetTerm)
    (proofCodeId smallerCodeId : FreeVarId)
    (hIds : proofCodeId ≠ smallerCodeId) :
    Formula.IsSigma1 set_levy_bound
      (G.comparison left right proofCodeId smallerCodeId) := by
  have hProofFresh :
      (SetSort.set, smallerCodeId) ∉
        Term.freeSupport (x#proofCodeId) := by
    intro hMember
    have hPair :
        (SetSort.set, smallerCodeId) =
          (SetSort.set, proofCodeId) :=
      List.mem_singleton.mp hMember
    cases hPair
    exact hIds rfl
  have hBody :
      Formula.IsDelta0 set_levy_bound
        (G.condition (x#proofCodeId) left ∧ₘ
          G.no_smaller
            (x#proofCodeId) right smallerCodeId) :=
    Formula.IsDelta0.conj
      (G.delta0 (x#proofCodeId) left)
      (G.no_smaller_delta0
        (x#proofCodeId) right smallerCodeId hProofFresh)
  simpa [comparison] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set proofCodeId hBody.to_sigma1

/-- Rosser 有限比较之否定的正式 `Pi1` 分类。 -/
theorem neg_comparison_pi1
    (G : Delta0ProofGraph)
    (left right : SetTerm)
    (proofCodeId smallerCodeId : FreeVarId)
    (hIds : proofCodeId ≠ smallerCodeId) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.comparison
        left right proofCodeId smallerCodeId) :=
  Formula.IsPi1.neg
    (G.comparison_sigma1
      left right proofCodeId smallerCodeId hIds)

/-- 把右侧固定为左侧否定码得到 Rosser 可证性谓词。 -/
def rosser_provability
    (G : Delta0ProofGraph)
    (code : SetTerm)
    (proofCodeId smallerCodeId : FreeVarId) : SetFormula :=
  G.comparison
    code (neg_codeₘ(code))
    proofCodeId smallerCodeId

/-- Rosser 可证性谓词的正式 `Sigma1` 分类。 -/
theorem rosser_provability_sigma1
    (G : Delta0ProofGraph)
    (code : SetTerm)
    (proofCodeId smallerCodeId : FreeVarId)
    (hIds : proofCodeId ≠ smallerCodeId) :
    Formula.IsSigma1 set_levy_bound
      (G.rosser_provability
        code proofCodeId smallerCodeId) := by
  simpa [rosser_provability] using
    G.comparison_sigma1
      code (neg_codeₘ(code))
      proofCodeId smallerCodeId hIds

/-- Rosser 不可证性谓词的正式 `Pi1` 分类。 -/
theorem neg_rosser_provability_pi1
    (G : Delta0ProofGraph)
    (code : SetTerm)
    (proofCodeId smallerCodeId : FreeVarId)
    (hIds : proofCodeId ≠ smallerCodeId) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.rosser_provability
        code proofCodeId smallerCodeId) :=
  Formula.IsPi1.neg
    (G.rosser_provability_sigma1
      code proofCodeId smallerCodeId hIds)

end Delta0ProofGraph

namespace Sigma1ProofGraph

/-- `Sigma1` proof graph 的正向条件分类。 -/
theorem condition_sigma1
    (G : Sigma1ProofGraph)
    (proofCode conclusion : SetTerm) :
    Formula.IsSigma1 set_levy_bound
      (G.condition proofCode conclusion) :=
  G.sigma1 proofCode conclusion

/-- 普通一元可证性谓词。 -/
def provability
    (G : Sigma1ProofGraph)
    (conclusion : SetTerm)
    (proofCodeId : FreeVarId) : SetFormula :=
  ∃ₘ[SetSort.set, proofCodeId],
    G.condition (x#proofCodeId) conclusion

/-- `∃ p, Proof(p,c)` 的正式 `Sigma1` 分类。 -/
theorem provability_sigma1
    (G : Sigma1ProofGraph)
    (conclusion : SetTerm)
    (proofCodeId : FreeVarId) :
    Formula.IsSigma1 set_levy_bound
      (G.provability conclusion proofCodeId) := by
  simpa [provability] using
    Formula.IsSigma1.exists_closeFreeAt
      SetSort.set proofCodeId
      (G.condition_sigma1 (x#proofCodeId) conclusion)

/-- 普通不可证性谓词的正式 `Pi1` 分类。 -/
theorem neg_provability_pi1
    (G : Sigma1ProofGraph)
    (conclusion : SetTerm)
    (proofCodeId : FreeVarId) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ G.provability conclusion proofCodeId) :=
  Formula.IsPi1.neg
    (G.provability_sigma1 conclusion proofCodeId)

end Sigma1ProofGraph
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
