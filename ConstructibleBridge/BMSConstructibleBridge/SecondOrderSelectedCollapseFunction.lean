import BMSConstructibleBridge.SecondOrderSelectedCollapseGraph
import BMSConstructibleBridge.SecondOrderCollapseFunction
import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-! # 保留全部选点和孤立根的实际原坍缩函数

原 Z₂ 任意模型中的接线辅助构造。实际选点 P 的前驱封闭与全部原根域
证书产生精确传递值域 T、完整集合函数 H、满射及原递归方程。
H 的每个值仍是同一 S 的图商根，不从宿主函数收集图，不预供 H/T。
这个辅助接口尚未代替最终固定行高 BMS 的原对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSelectedCollapseFunction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing PowerlessBMSQuotientCoding

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

theorem exists_l (K : source_coding_l hℳ) (S P : set_l ℳ)
    (hS : ∀ n, SecondOrderDomain.wf_l S n)
    (hClosed : ∀ a, mem_l a P → ∀ b, relation_l S b a → mem_l b P)
    (A D : SecondOrderQuotient.type_l hℳ)
    (hA : ∀ a b, relation_l S a b ↔ SecondOrderFunctionObjects.value_l hℳ A
      (numberCode_l K a).val (numberCode_l K b).val)
    (hD : ∀ x, SecondOrderQuotient.mem_l hℳ x D ↔
      ∃ n, mem_l n P ∧ x = (numberCode_l K n).val) :
    ∃ T H, SecondOrderCollapseFunction.spec_l hℳ A D T H ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ H x y ↔
        ∃ n, mem_l n P ∧ x = (numberCode_l K n).val ∧
          y = SecondOrderQuotient.mk_l hℳ (SecondOrderCollapseGraph.code_l S hS n) := by
  let N (n : num_l ℳ) := (numberCode_l K n).val
  let C (n : num_l ℳ) := SecondOrderQuotient.mk_l hℳ (SecondOrderCollapseGraph.code_l S hS n)
  obtain ⟨U, hU, hTrans⟩ := SecondOrderSelectedCollapseGraph.range_l hℳ S P hS hClosed
  have hRange (x : SecondOrderQuotient.type_l hℳ) :
      SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ U) ↔ ∃ n, mem_l n P ∧ x = C n := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hU X).trans (exists_congr (fun n => and_congr Iff.rfl
      (SecondOrderQuotient.eq_iff_l hℳ X (SecondOrderCollapseGraph.code_l S hS n)).symm))
  have hMembers (x : SecondOrderQuotient.type_l hℳ) (n : num_l ℳ) :
      SecondOrderQuotient.mem_l hℳ x (C n) ↔ ∃ m, relation_l S m n ∧ x = C m := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    change (∃ m, relation_l S m n ∧ SecondOrderBisimulation.eq_l X.real S X.root m) ↔ _
    exact exists_congr (fun m => and_congr Iff.rfl
      (SecondOrderQuotient.eq_iff_l hℳ X (SecondOrderCollapseGraph.code_l S hS m)).symm)
  have hInject (n m : num_l ℳ) (h : N n = N m) : n = m :=
    numberCode_injective_l K (Subtype.ext h)
  obtain ⟨H, hH⟩ := SecondOrderSelectedCollapseGraph.graph_l hℳ K.less S P K.less_spec hS
  have hValue (x y : SecondOrderQuotient.type_l hℳ) :
      SecondOrderFunctionObjects.value_l hℳ H x y ↔ ∃ n, mem_l n P ∧ x = N n ∧ y = C n := by
    constructor
    · rintro ⟨p, hp, hPair⟩
      obtain ⟨n, hn, hPair'⟩ := (hH p).mp hp
      exact ⟨n, hn, (SecondOrderPairObjects.ordered_eq_l hℳ hPair hPair').mp rfl⟩
    · rintro ⟨n, hn, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (N n) (C n)
      exact ⟨p, (hH p).mpr ⟨n, hn, hp⟩, hp⟩
  refine ⟨SecondOrderQuotient.mk_l hℳ U, H, ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩, hValue⟩
  · intro b c hb hc
    obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
    obtain ⟨C, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
    exact hTrans B C hb hc
  · intro p hp
    obtain ⟨n, hn, hPair⟩ := (hH p).mp hp
    exact ⟨N n, C n, (hD _).mpr ⟨n, hn, rfl⟩, (hRange _).mpr ⟨n, hn, rfl⟩, hPair⟩
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := (hD x).mp hx
    refine ⟨C n, ⟨(hRange _).mpr ⟨n, hn, rfl⟩, (hValue _ _).mpr ⟨n, hn, rfl, rfl⟩⟩, ?_⟩
    rintro y ⟨_, hy⟩
    obtain ⟨m, _hm, h, hy⟩ := (hValue _ _).mp hy
    exact hy.trans (congrArg C (hInject n m h).symm)
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := (hRange y).mp hy
    exact ⟨N n, (hD _).mpr ⟨n, hn, rfl⟩, (hValue _ _).mpr ⟨n, hn, rfl, rfl⟩⟩
  · intro k y _hk hy x
    obtain ⟨n, hn, rfl, rfl⟩ := (hValue k y).mp hy
    rw [hMembers]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hmP := hClosed n hn m hm
      exact ⟨N m, (hD _).mpr ⟨m, hmP, rfl⟩, (hA m n).mp hm, (hValue _ _).mpr ⟨m, hmP, rfl, rfl⟩⟩
    · rintro ⟨j, _hj, hEdge, hX⟩
      obtain ⟨m, _hm, rfl, rfl⟩ := (hValue j x).mp hX
      exact ⟨m, (hA m n).mpr hEdge, rfl⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSelectedCollapseFunction
