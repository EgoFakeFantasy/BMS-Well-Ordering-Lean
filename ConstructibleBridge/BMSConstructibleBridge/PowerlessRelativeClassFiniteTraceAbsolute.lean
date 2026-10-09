import BMSConstructibleBridge.PowerlessAdditionTraceBounded
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteAddition
import BMSConstructibleBridge.PowerlessRelativeClassBounded

/-! # 有限轨迹在相对类与原商之间绝对

先用实际自然数后继界证明 Δ₀ 检查式与原轨迹等价，再应用传递类的
有界绝对性。没有假定类是完整源理论模型，也没有把无界公式直接相对化为等价。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteTraceAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem ambient_equiv_l {ω e a n g : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hn : mem_l hℳ n ω) :
    PowerlessAdditionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω e a n g ↔
      PowerlessAdditionFinite.trace_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω e a n g := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  apply PowerlessAdditionTraceBounded.equiv_l
  · intro m hm
    obtain ⟨m', hm'ω, hm'⟩ := hω.1.2 n hn
    exact (PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) (a := n) (b := m') (c := m) hm' hm) ▸ hm'ω
  · intro m hm k l hk hl
    exact (hm l).mpr (SecondOrderNaturalBounds.bound_l K (hωEq ▸ hn) k l hk hl)
  · intro m hm x y hxy
    exact PowerlessBMSQuotientRecursion.value_mem_l (hM := hℳ) hm hxy

variable {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem class_equiv_l {ω e a n g : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hn : mem_l hℳ n.val ω.val) :
    PowerlessAdditionTraceBounded.trace_l (𝒩 := structure_l hℳ B hBase) ω e a n g ↔
      PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  apply PowerlessAdditionTraceBounded.equiv_l
  · intro m hm
    obtain ⟨m', hm'ω, hm'⟩ := ((PowerlessNatural.inductive_iff_l
      (ℳ := structure_l hℳ B hBase) ω).mp hω.1).2 n hn
    have hEq : m'.val = m.val := PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ)
      (a := n.val) (b := m'.val) (c := m.val)
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) n m').mp hm')
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) n m).mp hm)
    change mem_l hℳ m.val ω.val
    exact hEq ▸ hm'ω
  · intro m hm k l hk hl
    have hBound := SecondOrderNaturalBounds.bound_l K (hωEq ▸ hn) k.val l.val hk
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) k l).mp hl)
    exact (hm l).mpr ((or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩).mp hBound)
  · intro m hm x y hxy
    exact SecondOrderFunctionProperties.value_mem_l hℳ
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g m ω).mp hm)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g x y).mp hxy)

theorem trace_l {ω e a n g : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hn : mem_l hℳ n.val ω.val) :
    PowerlessAdditionFinite.trace_l (ℳ := structure_l hℳ B hBase) ω e a n g ↔
      PowerlessAdditionFinite.trace_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val e.val a.val n.val g.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree g).pushFree n).pushFree a).pushFree e).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let z : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let b : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let k : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let f : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  have hAbs := PowerlessRelativeClassBounded.formula_l (hBase := hBase)
    (PowerlessAdditionTraceBounded.delta_l w z b k f) η
  have hRead := (PowerlessAdditionTraceBounded.formula_l η w z b k f).symm.trans
    (hAbs.trans (PowerlessAdditionTraceBounded.formula_l (PowerlessRelativeClassRelativization.env_l η) w z b k f))
  exact (class_equiv_l hω hn).symm.trans (hRead.trans (ambient_equiv_l
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) hn))

#print axioms trace_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteTraceAbsolute
