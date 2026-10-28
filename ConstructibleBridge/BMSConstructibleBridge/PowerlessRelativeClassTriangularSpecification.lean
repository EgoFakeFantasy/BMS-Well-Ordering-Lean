import BMSConstructibleBridge.PowerlessRelativeClassTriangular
import BMSConstructibleBridge.PowerlessRelativeClassInduction
import BMSConstructibleBridge.PowerlessRelativeClassFunctionProperties
import BMSConstructibleBridge.PowerlessRelativeClassAdditionAbsolute
import BMSConstructibleBridge.PowerlessBMSQuotientPairingBounds

/-! # 给定类内三角图的同编码原算术规格

对实际纯公式 agreement_m 使用类内公式归纳，证明两张满足三角递推的图
在全部内部自然数处输出一致。再与同一 K 下已构造的规范图比较，将算术
规格传给原来的 T；辅助图仅用于比较，不替换给定图或其既有层界。
不假设相对类满足完整 PowerlessTheory，也不对任意宿主谓词作归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTriangularSpecification

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassInduction (number_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

/-- 复用已有纯比较模板，其语义可在相对类结构中直接读取。 -/
theorem agreement_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (T U n : carrier_l 𝒩) :
    PowerlessBMSQuotientRecursion.agreement_m.satisfies
      ((((Env.empty (M := 𝒩)).pushFree U).pushFree T).pushFree n) ↔
      ∀ x y, value_l (ℳ := 𝒩) T n x → value_l (ℳ := 𝒩) U n y → x = y := by
  simp only [PowerlessBMSQuotientRecursion.agreement_m, Formula.satisfies, value_formula_l]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

/-- 原三角递推确定每个内部数处的输出；归纳对象是实际纯公式。 -/
theorem agreement_l (K : source_coding_l hℳ) {ω e T U : type_l hℳ B}
    (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hT : PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T)
    (hU : PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e U)
    (n : SecondOrderModel.num_l ℳ) (x y : type_l hℳ B)
    (hx : value_l (ℳ := structure_l hℳ B hBase) T (number_l (hBase := hBase) K n) x)
    (hy : value_l (ℳ := structure_l hℳ B hBase) U (number_l (hBase := hBase) K n) y) : x = y := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set] := ((Env.empty).pushFree U).pushFree T
  have h := PowerlessRelativeClassInduction.induction_l K
    PowerlessBMSQuotientRecursion.agreement_m η ?_ ?_ n
  · exact (agreement_formula_l (𝒩 := structure_l hℳ B hBase) T U (number_l (hBase := hBase) K n)).mp h x y hx hy
  · apply (agreement_formula_l (𝒩 := structure_l hℳ B hBase) T U
      (number_l (hBase := hBase) K (SecondOrderModel.zero_l ℳ))).mpr
    intro x y hx hy
    have hZero : number_l (hBase := hBase) K (SecondOrderModel.zero_l ℳ) = e :=
      Subtype.ext he.symm
    rw [hZero] at hx hy
    exact (PowerlessRelativeClassFunctionProperties.value_unique_l hT.1 hx hT.2.1).trans
      (PowerlessRelativeClassFunctionProperties.value_unique_l hU.1 hy hU.2.1).symm
  · intro k hk
    apply (agreement_formula_l (𝒩 := structure_l hℳ B hBase) T U
      (number_l (hBase := hBase) K (SecondOrderModel.succ_l k))).mpr
    intro x y hx hy
    have hkω : mem_l hℳ (number_l (hBase := hBase) K k).val ω.val :=
      hω.symm ▸ (numberCode_l K k).property
    have hSucc : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase)
        (number_l (hBase := hBase) K k)
        (number_l (hBase := hBase) K (SecondOrderModel.succ_l k)) :=
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase)
        (number_l (hBase := hBase) K k)
        (number_l (hBase := hBase) K (SecondOrderModel.succ_l k))).mpr
          (PowerlessBMSQuotientSuccessor.successor_l K k)
    obtain ⟨v, hv, _⟩ := hT.1.2 (number_l (hBase := hBase) K k) hkω
    obtain ⟨w, hw, _⟩ := hU.1.2 (number_l (hBase := hBase) K k) hkω
    have hvw := (agreement_formula_l (𝒩 := structure_l hℳ B hBase) T U (number_l (hBase := hBase) K k)).mp hk v w hv.2 hw.2
    subst w
    have hAddX := hT.2.2 (number_l (hBase := hBase) K k)
      (number_l (hBase := hBase) K (SecondOrderModel.succ_l k)) v x hkω hSucc hv.2 hx
    have hAddY := hU.2.2 (number_l (hBase := hBase) K k)
      (number_l (hBase := hBase) K (SecondOrderModel.succ_l k)) v y hkω hSucc hw.2 hy
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨v.val, hω ▸ hv.1⟩
    have hvCode : v.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
    have hxCode := (PowerlessRelativeClassAdditionAbsolute.instance_l
      (hBase := hBase) (ω := ω) (e := e) (a := v)
      (b := number_l (hBase := hBase) K (SecondOrderModel.succ_l k)) (c := x)
      (i := i) (j := SecondOrderModel.succ_l k) K hω he hvCode rfl).mp hAddX
    have hyCode := (PowerlessRelativeClassAdditionAbsolute.instance_l
      (hBase := hBase) (ω := ω) (e := e) (a := v)
      (b := number_l (hBase := hBase) K (SecondOrderModel.succ_l k)) (c := y)
      (i := i) (j := SecondOrderModel.succ_l k) K hω he hvCode rfl).mp hAddY
    exact Subtype.ext (hxCode.trans hyCode.symm)

/-- 从给定 T 的纯三角规格得到同一 K 的算术读数，结论仍关于原 T。 -/
theorem spec_l (K : source_coding_l hℳ) {ω e N T : type_l hℳ B}
    (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N.val)
    (hT : PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T) :
    PowerlessBMSQuotientPairingBounds.spec_l K T.val := by
  obtain ⟨U, hU, hSpecU⟩ := PowerlessRelativeClassTriangular.exists_spec_l (hBase := hBase) K ω e N hω he hN
  intro i j
  let n := number_l (hBase := hBase) K i
  let t := number_l (hBase := hBase) K j
  have hnω : mem_l hℳ n.val ω.val := hω.symm ▸ (numberCode_l K i).property
  have hRead : value_l (ℳ := structure_l hℳ B hBase) T n t ↔
      value_l (ℳ := structure_l hℳ B hBase) U n t := by
    constructor
    · intro hValue
      obtain ⟨y, hy, _⟩ := hU.1.2 n hnω
      have hEq : t = y := agreement_l K hω he hT hU i t y hValue hy.2
      exact hEq.symm ▸ hy.2
    · intro hValue
      obtain ⟨x, hx, _⟩ := hT.1.2 n hnω
      have hEq : x = t := agreement_l K hω he hT hU i x t hx.2 hValue
      exact hEq ▸ hx.2
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) T n t).symm.trans
    (hRead.trans ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) U n t).trans (hSpecU i j)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTriangularSpecification
