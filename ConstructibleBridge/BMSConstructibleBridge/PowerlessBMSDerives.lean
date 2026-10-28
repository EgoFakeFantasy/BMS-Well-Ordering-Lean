import BMSConstructibleBridge.PowerlessBMSMatrixTransfer
import BMSConstructibleBridge.SecondOrderCompleteness

/-!
# 从逐候选源模型覆盖得到固定高度的对象推导

将条件式矩阵迁移与已有强完备性连接起来。唯一的主要输入是：对每个满足
`theory_m` 的二阶结构及其中每个集合候选，都能提供相应的
`candidate_source_l`。本文件保留以源模型族为假设的条件式 `Derives` 接口。
无额外源假设的终局另由 `SecondOrderHereditaryCandidateSource.exists_l` 逐候选给出
`Nonempty` 证书，经 `PowerlessBMSNonemptyTransfer` 接入
`SecondOrderHereditaryBMSWellOrder.derives_m`，不要求抽取 Type 层源族。源数据中的
`sourceModels` 当前要求完整 `PowerlessTheory.theory_m`（包括全部 Separation 与
Collection 实例），并非已弱化到某个有限片段。

本文件的语义蕴涵显式取 `.{0, 0, 0, 0}`：模型载体固定在 `Type 0`，但仍对该宇宙
中所有结构量化。各定理中的 `hM` 只用于把 `hSources` 限定到满足 `theory_m` 的目标模型；
矩阵迁移证明本身使用源模型字段和对应关系，不直接消费 `hM` 的对象公理。故本文件
只在本接口中保留逐候选 `hSources` 假设；最终遗传源构造使用目标侧公理，并在
`SecondOrderHereditaryBMSWellOrder` 消去该额外前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSDerives

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

/-- 若每个满足对象理论的模型都具备逐候选源模型，则固定高度闭句在所有模型中成立。

这是从候选源结构到完备性前提的适配层；源模型覆盖仍是显式假设。
-/
theorem semantically_entails_of_candidate_sources_l (H : Nat)
    (hSources : ∀ {M : FirstOrder.Structure.{0, 0, 0, 0} signature_m},
      Theory.Models M SecondOrderArithmetic.theory_m →
        ∀ X : M.Carrier .set,
          PowerlessBMSMatrixTransfer.candidate_source_l (M := M) X) :
    Theory.SemanticallyEntails.{0, 0, 0, 0} SecondOrderArithmetic.theory_m
      (SecondOrderConcreteFormula.closed_m H) := by
  intro M hM
  exact PowerlessBMSMatrixTransfer.closed_from_candidate_sources_l H
    (hSources (M := M) hM)

/-- 将逐候选源模型覆盖与强完备性组合为固定高度闭句的对象推导。 -/
theorem derives_of_candidate_sources_m (H : Nat)
    (hSources : ∀ {M : FirstOrder.Structure.{0, 0, 0, 0} signature_m},
      Theory.Models M SecondOrderArithmetic.theory_m →
        ∀ X : M.Carrier .set,
          PowerlessBMSMatrixTransfer.candidate_source_l (M := M) X) :
    Derives SecondOrderArithmetic.theory_m [] (SecondOrderConcreteFormula.closed_m H) :=
  SecondOrderCompleteness.derives_m
    (semantically_entails_of_candidate_sources_l H hSources)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSDerives
