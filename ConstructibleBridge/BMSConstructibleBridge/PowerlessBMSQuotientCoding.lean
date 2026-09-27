import BMSConstructibleBridge.PowerlessArithmetic
import BMSConstructibleBridge.PowerlessBMSQuotientOmega
import BMSConstructibleBridge.SecondOrderNaturalSubsets

/-!
# 任意 Z₂ 模型的图商自然数与 real 候选编码

在 `SecondOrderQuotient` 中，目标模型的每个内部自然数都有一张对应的 von Neumann
根码；所有这些根组成图商的 ω。目标模型的任意集合对象则由
`SecondOrderNaturalSubsets` 表示为该 ω 的 quotient 子集。这里尚不构造
`PowerlessTheory` 的 Collection，也不声称已定义完纯算术迁移所需的加乘运算。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientCoding

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

/-- 把目标模型数域的 `<` 图及其全部根码、quotient ω 一起打包。 -/
structure source_coding_l
    {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hM : Theory.Models M SecondOrderArithmetic.theory_m) where
  less : SecondOrderModel.set_l M
  less_spec : ∀ a b, relation_l less a b ↔ SecondOrderOrder.lt_l a b
  omega_graph : SecondOrderGraph.code_l M
  omega_graph_spec : ∀ A, SecondOrderGraph.mem_l A omega_graph ↔
    ∃ n, SecondOrderGraph.eq_l A (SecondOrderNaturalGraph.code_l hM less less_spec n)
  omega : SecondOrderQuotient.type_l hM
  omega_eq : omega = SecondOrderQuotient.mk_l hM omega_graph
  omega_spec : SecondOrderOmega.omega_l hM omega

/-- 任意 Z₂ 模型都生成上述编码；其 ω 存在性不使用 Collection。 -/
theorem exists_l
    {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hM : Theory.Models M SecondOrderArithmetic.theory_m) :
    Nonempty (source_coding_l hM) := by
  obtain ⟨R, hR⟩ := SecondOrderNaturalGraph.relation_exists_l hM
  obtain ⟨Ω, hΩ⟩ := SecondOrderNaturalNumbers.range_l hM R hR
  refine ⟨⟨R, hR, Ω, hΩ, SecondOrderQuotient.mk_l hM Ω, rfl,
    SecondOrderOmega.range_l hM R hR Ω hΩ⟩⟩

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

/-- 把目标模型的每个数映到其 von Neumann 根码所代表的 quotient 数。 -/
def numberCode_l (C : source_coding_l hM) (n : SecondOrderModel.num_l M) :
    PowerlessArithmetic.num_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega := by
  refine ⟨SecondOrderQuotient.mk_l hM
    (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n), ?_⟩
  change (SecondOrderQuotient.structure_l hM).relInterp .membership
    (.cons (SecondOrderQuotient.mk_l hM
      (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n))
      (.cons C.omega .nil))
  rw [C.omega_eq]
  simp only [SecondOrderQuotient.structure_l]
  exact (SecondOrderQuotient.mem_iff_l hM
    (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n) C.omega_graph).mpr
      ((C.omega_graph_spec _).mpr ⟨n, SecondOrderGraph.refl_l hM _⟩)

/-- 目标数的根码相等，当且仅当原模型数相等。 -/
theorem numberCode_injective_l (C : source_coding_l hM) :
    Function.Injective (numberCode_l C) := by
  intro n m h
  apply (SecondOrderNaturalNumbers.eq_l hM C.less C.less_spec n m).mp
  apply (SecondOrderQuotient.eq_iff_l hM
    (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n)
    (SecondOrderNaturalGraph.code_l hM C.less C.less_spec m)).mp
  exact congrArg Subtype.val h

/-- 两个目标数码之间的 quotient 成员关系准确解释目标模型的 `<`。 -/
theorem numberCode_mem_iff_lt_l (C : source_coding_l hM)
    (n m : SecondOrderModel.num_l M) :
    SecondOrderQuotient.mem_l hM (numberCode_l C n).val (numberCode_l C m).val ↔
      SecondOrderOrder.lt_l n m := by
  change SecondOrderQuotient.mem_l hM
      (SecondOrderQuotient.mk_l hM
        (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n))
      (SecondOrderQuotient.mk_l hM
        (SecondOrderNaturalGraph.code_l hM C.less C.less_spec m)) ↔ _
  exact (SecondOrderQuotient.mem_iff_l hM _ _).trans
    (SecondOrderNaturalNumbers.mem_l hM C.less C.less_spec n m)

/-- quotient ω 的每个成员都来自目标模型中的某个内部自然数。 -/
theorem numberCode_surjective_l (C : source_coding_l hM) :
    Function.Surjective (numberCode_l C) := by
  intro a
  obtain ⟨A, hA⟩ := SecondOrderQuotient.surj_l hM a.val
  have hMem : SecondOrderQuotient.mem_l hM (SecondOrderQuotient.mk_l hM A) C.omega := by
    rw [hA]
    exact a.property
  rw [C.omega_eq] at hMem
  have hGraph := (SecondOrderQuotient.mem_iff_l hM A C.omega_graph).mp hMem
  obtain ⟨n, hn⟩ := (C.omega_graph_spec A).mp hGraph
  refine ⟨n, ?_⟩
  apply Subtype.ext
  change SecondOrderQuotient.mk_l hM
      (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n) = a.val
  rw [← hA]
  apply (SecondOrderQuotient.eq_iff_l hM _ _).mpr
  exact SecondOrderGraph.symm_l hM hn

/-- 源 quotient 数与目标模型数之间的实际双射。 -/
noncomputable def numberEquiv_l (C : source_coding_l hM) :
    PowerlessArithmetic.num_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega ≃
      SecondOrderModel.num_l M :=
  (Equiv.ofBijective (numberCode_l C)
    ⟨numberCode_injective_l C, numberCode_surjective_l C⟩).symm

/-- 把 quotient 子集与目标集合候选作逐数成员对应。 -/
def setRel_l (C : source_coding_l hM)
    (A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega)
    (X : SecondOrderModel.set_l M) : Prop :=
  ∀ n, SecondOrderQuotient.mem_l hM (numberCode_l C n).val A.val ↔
    SecondOrderModel.mem_l n X

/-- 每个目标二阶对象都有一个 quotient 子集代表，且代表具有逐数成员规格。 -/
theorem representative_exists_l (C : source_coding_l hM) (X : SecondOrderModel.set_l M) :
    ∃ A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hM) C.omega,
      setRel_l C A X := by
  obtain ⟨d, hd⟩ := SecondOrderNaturalSubsets.exists_l hM C.less C.less_spec X
  refine ⟨⟨d, ?_⟩, ?_⟩
  · intro x hx
    change SecondOrderQuotient.mem_l hM x d at hx
    change SecondOrderQuotient.mem_l hM x C.omega
    obtain ⟨n, hn, rfl⟩ := (hd x).mp hx
    rw [C.omega_eq]
    exact (SecondOrderQuotient.mem_iff_l hM
      (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n) C.omega_graph).mpr
        ((C.omega_graph_spec _).mpr ⟨n, SecondOrderGraph.refl_l hM _⟩)
  · intro n
    change SecondOrderQuotient.mem_l hM
      (SecondOrderQuotient.mk_l hM
        (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n)) d ↔
      SecondOrderModel.mem_l n X
    rw [hd (SecondOrderQuotient.mk_l hM
      (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n))]
    constructor
    · rintro ⟨m, hm, hEq⟩
      have hCode := (SecondOrderQuotient.eq_iff_l hM
        (SecondOrderNaturalGraph.code_l hM C.less C.less_spec n)
        (SecondOrderNaturalGraph.code_l hM C.less C.less_spec m)).mp hEq
      have hnm := (SecondOrderNaturalNumbers.eq_l hM C.less C.less_spec n m).mp hCode
      subst m
      exact hm
    · intro hn
      exact ⟨n, hn, rfl⟩

#print axioms exists_l
#print axioms numberCode_injective_l
#print axioms numberCode_surjective_l
#print axioms numberEquiv_l
#print axioms numberCode_mem_iff_lt_l
#print axioms representative_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientCoding
