import BMSConstructibleBridge.PowerlessBMSQuotientFunctions
import BMSConstructibleBridge.PowerlessBMSQuotientMapSpec
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor
import BMSConstructibleBridge.SecondOrderRelations

/-!
# Z₂ 内部后继关系实数与其 quotient 后继映射

目标模型的后继函数符号本身没有对应的二阶集合；本文件用二阶算术自己的纯后继等式
公式经理解公理构造出这张关系实数 `S`，并证明其配对图逐点满足
`relation_l S a b ↔ b = succ_l a`。随后把 `S` 送入
`PowerlessBMSQuotientFunctions.exists_map_l`（仅得全函数图）与
`exists_map_with_spec_l`（同时得逐点成员规格），再用 `value_iff_relation_l` 把
规格折回逐点值对应：`numberCode_l a ↦ numberCode_l (succ_l a)`。每个像点都满足既有
`successorFunction_graph_l` 的集合论后继关系，故本模块同时声明这两条到后继的路径
（关系实数提升 vs. 数码双射搬运）在同一商结构上相容。

端点范围是目标模型的全部内部数（含非标准数），未假设模型标准，也不把宿主 `Nat`
的后继当作模型后继；本文件不构造加法或乘法。 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSuccessorMap

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

/-- quotient 内部 ω 上的数。 -/
abbrev qnum_l (C : PowerlessBMSQuotientCoding.source_coding_l hM) :=
  PowerlessArithmetic.num_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega

/-- 数码双射在商对象层面的逐点还原：`numberCode_l (numberEquiv_l x) = x`。 -/
theorem numberCode_numberEquiv_l
    (C : PowerlessBMSQuotientCoding.source_coding_l hM) (x : qnum_l C) :
    (PowerlessBMSQuotientCoding.numberCode_l C
      (PowerlessBMSQuotientCoding.numberEquiv_l C x)).val = x.val :=
  congrArg Subtype.val
    (Equiv.apply_symm_apply (Equiv.ofBijective
      (PowerlessBMSQuotientCoding.numberCode_l C)
      ⟨PowerlessBMSQuotientCoding.numberCode_injective_l C,
        PowerlessBMSQuotientCoding.numberCode_surjective_l C⟩) x)

/-- 后继图的纯算术模板：第二个自由坐标等于第一个自由坐标的后继项。 -/
def successorFormula_m : Formula signature_m [] [.num, .num] :=
  .equal (Term.app (σ := signature_m) .succ (.cons (.fvar .here) .nil)) (.fvar (.there .here))

/-- 模板只使用签名自带的后继函数符号与数等式，属于 Z₂ 纯语言。 -/
theorem successorFormula_pure_m : language_m successorFormula_m = true :=
  rfl

/-- 模板在两端点环境中的真值恰为模型自身的后继方程。 -/
theorem successorFormula_l (a b : SecondOrderModel.num_l M) :
    Formula.satisfies (((Env.empty (M := M)).pushFree b).pushFree a) successorFormula_m ↔
      b = SecondOrderModel.succ_l a := by
  change SecondOrderModel.succ_l a = b ↔ b = SecondOrderModel.succ_l a
  exact eq_comm

/-- 任意 Z₂ 模型中，后继函数自己的图是一张内部二阶关系实数；由对象理解公理构造，
不是假设给出的外部集合。 -/
theorem successorRelation_exists_l (hℳ : Theory.Models M SecondOrderArithmetic.theory_m) :
    ∃ S : SecondOrderModel.set_l M, ∀ a b, SecondOrderPairing.relation_l S a b ↔
      b = SecondOrderModel.succ_l a := by
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ successorFormula_m
    successorFormula_pure_m (Env.empty (M := M))
  refine ⟨S, fun a b => (hS a b).trans (successorFormula_l a b)⟩

/-- 后继实数对每个内部数都有输出；这是 `exists_map_l` 的输入前提，此处是证出的。 -/
theorem successorRelation_total_l (S : SecondOrderModel.set_l M)
    (hS : ∀ a b, SecondOrderPairing.relation_l S a b ↔ b = SecondOrderModel.succ_l a)
    (a : SecondOrderModel.num_l M) :
    ∃ b, SecondOrderPairing.relation_l S a b :=
  ⟨SecondOrderModel.succ_l a, (hS _ _).mpr rfl⟩

/-- 后继实数对每个内部数至多一个输出；同样由构造出的规格推出。 -/
theorem successorRelation_unique_l (S : SecondOrderModel.set_l M)
    (hS : ∀ a b, SecondOrderPairing.relation_l S a b ↔ b = SecondOrderModel.succ_l a)
    (a b c : SecondOrderModel.num_l M)
    (hb : SecondOrderPairing.relation_l S a b)
    (hc : SecondOrderPairing.relation_l S a c) : b = c :=
  ((hS _ _).mp hb).trans (((hS _ _).mp hc).symm)

/-- 后继实数满足 `exists_map_l` 的两条前提，故 quotient 内部 ω 上有全函数图。 -/
theorem successorMap_l (C : PowerlessBMSQuotientCoding.source_coding_l hM) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega := by
  obtain ⟨S, hS⟩ := successorRelation_exists_l hM
  exact PowerlessBMSQuotientFunctions.exists_map_l C S
    (successorRelation_total_l S hS) (successorRelation_unique_l S hS)

/-- 同一条实数经 `exists_map_with_spec_l` 提升，同时保留像集合的逐点成员规格。 -/
theorem successorMapSpec_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (S : SecondOrderModel.set_l M)
    (hS : ∀ a b, SecondOrderPairing.relation_l S a b ↔ b = SecondOrderModel.succ_l a) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM)
        f C.omega C.omega ∧
        ∀ p, SecondOrderQuotient.mem_l hM p f ↔
          ∃ a b, SecondOrderPairing.relation_l S a b ∧
            SecondOrderPairObjects.ordered_l hM
              (PowerlessBMSQuotientCoding.numberCode_l C a).val
              (PowerlessBMSQuotientCoding.numberCode_l C b).val p :=
  PowerlessBMSQuotientFunctions.exists_map_with_spec_l C S
    (successorRelation_total_l S hS) (successorRelation_unique_l S hS)

/-- 规格像的逐点值 iff：`numberCode_l a ↦ numberCode_l b` 当且仅当 `b = succ_l a`。 -/
theorem successorValue_iff_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (S : SecondOrderModel.set_l M)
    (hS : ∀ a b, SecondOrderPairing.relation_l S a b ↔ b = SecondOrderModel.succ_l a)
    (f : SecondOrderQuotient.type_l hM)
    (hSpec : ∀ p, SecondOrderQuotient.mem_l hM p f ↔
      ∃ a b, SecondOrderPairing.relation_l S a b ∧
        SecondOrderPairObjects.ordered_l hM
          (PowerlessBMSQuotientCoding.numberCode_l C a).val
          (PowerlessBMSQuotientCoding.numberCode_l C b).val p)
    (a b : SecondOrderModel.num_l M) :
    ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM)
      f (PowerlessBMSQuotientCoding.numberCode_l C a).val
        (PowerlessBMSQuotientCoding.numberCode_l C b).val ↔
      b = SecondOrderModel.succ_l a :=
  (PowerlessBMSQuotientFunctions.value_iff_relation_l C S f hSpec a b).trans (hS a b)

/-- 主出口：存在 quotient 内部 ω 上的全函数图，其逐点值恰为
`a ↦ numberCode_l (succ_l a)`，并且每个像点都满足既有 `successorFunction_graph_l`
的集合论后继关系。 -/
theorem successorMapGraph_l (C : PowerlessBMSQuotientCoding.source_coding_l hM) :
    ∃ f : SecondOrderQuotient.type_l hM,
      ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hM) f C.omega C.omega ∧
        ∀ x : qnum_l C,
          ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM) f x.val
            (PowerlessBMSQuotientSuccessor.successorFunction_l C x).val ∧
            PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hM) x.val
              (PowerlessBMSQuotientSuccessor.successorFunction_l C x).val := by
  obtain ⟨S, hS⟩ := successorRelation_exists_l hM
  obtain ⟨f, hmap, hspec⟩ := successorMapSpec_l C S hS
  refine ⟨f, hmap, fun x => ⟨?_,
    PowerlessBMSQuotientSuccessor.successorFunction_graph_l C x⟩⟩
  let a := PowerlessBMSQuotientCoding.numberEquiv_l C x
  rw [← numberCode_numberEquiv_l C x]
  show ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hM)
    f (PowerlessBMSQuotientCoding.numberCode_l C a).val
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.succ_l a)).val
  exact (successorValue_iff_l C S hS f hspec a (SecondOrderModel.succ_l a)).mpr rfl

#print axioms numberCode_numberEquiv_l
#print axioms successorFormula_pure_m
#print axioms successorFormula_l
#print axioms successorRelation_exists_l
#print axioms successorMap_l
#print axioms successorMapSpec_l
#print axioms successorValue_iff_l
#print axioms successorMapGraph_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSuccessorMap
