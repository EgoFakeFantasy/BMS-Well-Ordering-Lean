import BMSConstructibleBridge.SecondOrderSubsetLayer

/-! # 相容选择图的切片对象与原根谓词精确一致 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetExact

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem mem_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) (F G : set_l ℳ)
    (hG : SecondOrderSubsetLayer.spec_l A.real F A.root G)
    (hF : ∀ i n m, relation_l A.real n A.root → relation_l A.real m A.root →
      SecondOrderBisimulation.eq_l A.real A.real n m → (relation_l F i n ↔ relation_l F i m))
    (i n : num_l ℳ) (hn : relation_l A.real n A.root) :
    SecondOrderGraph.mem_l (SecondOrderGraph.child_l hℳ A n hn) (SecondOrderSubsetLayer.code_l hℳ A F G hG i) ↔
      relation_l F i n := by
  rw [SecondOrderSubsetLayer.mem_l hℳ A F G hG i]
  constructor
  · rintro ⟨m, hm, h, hnm⟩
    exact (hF i n m hn hm hnm).mpr h
  · intro h
    exact ⟨n, hn, h, SecondOrderBisimulation.refl_l hℳ A.real n⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubsetExact
