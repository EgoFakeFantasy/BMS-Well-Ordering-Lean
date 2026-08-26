import YesMetaZFC.Logic.Signature
import YesMetaZFC.Logic.Syntax
import YesMetaZFC.Logic.Semantics
import YesMetaZFC.Logic.Theory
import YesMetaZFC.Logic.FirstOrder.FreshVariable
import YesMetaZFC.Logic.FirstOrder.Derivation
import YesMetaZFC.Logic.FirstOrder.Hilbert
import YesMetaZFC.Logic.FirstOrder.Hilbert.Derived
import YesMetaZFC.Logic.FirstOrder.Hilbert.Translation
import YesMetaZFC.Logic.FirstOrder.Hilbert.Propositional
import YesMetaZFC.Logic.FirstOrder.Hilbert.Quantifier
import YesMetaZFC.Logic.FirstOrder.Hilbert.Substitution
import YesMetaZFC.Logic.FirstOrder.Hilbert.Equality
import YesMetaZFC.Logic.FirstOrder.Hilbert.Diagonal
import YesMetaZFC.Logic.FirstOrder.Hilbert.Compilation
import YesMetaZFC.Logic.FirstOrder.Hilbert.Adequacy
import YesMetaZFC.Logic.FirstOrder.Hilbert.Equivalence
import YesMetaZFC.Logic.FirstOrder.Hilbert.Encoding
import YesMetaZFC.Logic.FirstOrder.Hilbert.Hilbertization
import YesMetaZFC.Logic.FirstOrder.Hilbert.StrongAdequacy
import YesMetaZFC.Logic.FirstOrder.Admissibility
import YesMetaZFC.Logic.FirstOrder.FormulaComplexity
import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Logic.FirstOrder.LevyAbsoluteness
import YesMetaZFC.Logic.FirstOrder.Completeness
/-!
# 一阶语义与 Derives 核聚合入口
新 Automation 的 Formula/Theory/Derives 与完备性证明层统一从这里消费，而不是恢复
旧 MF1。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
end FirstOrder
end Logic
end YesMetaZFC
