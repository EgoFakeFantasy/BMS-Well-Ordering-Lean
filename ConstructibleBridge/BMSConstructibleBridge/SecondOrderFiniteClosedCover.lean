import BMSConstructibleBridge.SecondOrderFiniteEnumerationRoots
import BMSConstructibleBridge.PowerlessFiniteClosureSyntax

/-!
# 任意商内集合的实际有限子集闭合超集

用基础图的有效根及新增有限构造根组成统一图。全部根的像为传递集合；商内
有限子集的双射枚举经统一根关系转成精确成员根，故该像有限子集闭合。
这里只构造超集；最小有限闭包随后由原分离模式取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteClosedCover

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic
open PowerlessBMSQuotientCoding SecondOrderFiniteExtensionGraph

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

theorem range_l (hℳ : Theory.Models ℳ theory_m)
    (G : SecondOrderModel.set_l ℳ) (hG : ∀ n, SecondOrderDomain.wf_l G n) :
    ∃ H : SecondOrderGraph.code_l ℳ, ∀ B,
      SecondOrderGraph.mem_l B H ↔ ∃ n, SecondOrderGraph.eq_l B ⟨G, n, hG n⟩ := by
  obtain ⟨P, hP⟩ := SecondOrderModel.comprehension_l hℳ .truth rfl (Env.empty (M := ℳ))
  obtain ⟨H, hH⟩ := SecondOrderGraftSemantics.exists_l hℳ G P (fun n _ => hG n)
  refine ⟨H, fun B => (hH B).trans ?_⟩
  exact ⟨fun ⟨n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, (hP n).mpr True.intro, h⟩⟩

theorem exists_l (C : source_coding_l hℳ) (x : SecondOrderQuotient.type_l hℳ) :
    ∃ b : SecondOrderQuotient.type_l hℳ,
      ThirdOrderSemantics.subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) x b ∧
      PowerlessFiniteClosureSyntax.closed_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega b := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  obtain ⟨E, hE⟩ := SecondOrderBinaryPowers.exists_l hℳ
  obtain ⟨S, hS⟩ := SecondOrderValidRootGraph.exists_l hℳ A.real
  have hSW := SecondOrderValidRootGraph.wf_l hS
  obtain ⟨G, hG⟩ := SecondOrderFiniteExtensionGraph.exists_l hℳ S E hE
  have hGW := wf_l hℳ hG hSW
  obtain ⟨H, hH⟩ := range_l hℳ G hGW
  have hRange y : SecondOrderQuotient.mem_l hℳ y (SecondOrderQuotient.mk_l hℳ H) ↔
      ∃ n, y = SecondOrderQuotient.mk_l hℳ (code_l hℳ hG hSW n) := by
    obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
    exact (hH Y).trans (exists_congr (fun n => (SecondOrderQuotient.eq_iff_l hℳ Y _).symm))
  have hTrans a b (ha : SecondOrderQuotient.mem_l hℳ a (SecondOrderQuotient.mk_l hℳ H))
      (hba : SecondOrderQuotient.mem_l hℳ b a) :
      SecondOrderQuotient.mem_l hℳ b (SecondOrderQuotient.mk_l hℳ H) := by
    obtain ⟨n, rfl⟩ := (hRange a).mp ha
    obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ b
    obtain ⟨m, _, hBm⟩ := hba
    exact (hRange _).mpr ⟨m, (SecondOrderQuotient.eq_iff_l hℳ B _).mpr hBm⟩
  have hA : SecondOrderQuotient.mem_l hℳ (SecondOrderQuotient.mk_l hℳ A)
      (SecondOrderQuotient.mk_l hℳ H) := by
    apply (hRange _).mpr
    refine ⟨SecondOrderPairing.value_l (SecondOrderModel.zero_l ℳ) A.root,
      (SecondOrderQuotient.eq_iff_l hℳ A _).mpr ?_⟩
    exact SecondOrderBisimulation.trans_l hℳ A.real S G A.root A.root _
      (SecondOrderValidRootGraph.agrees_l hℳ hS A.root A.wf)
      (SecondOrderPairSet.tag_eq_l hℳ _ S G (fiber_l hℳ hG) A.root)
  refine ⟨SecondOrderQuotient.mk_l hℳ H, fun y hy => hTrans _ y hA hy, ?_⟩
  rintro d ⟨k, hk, f, hf, hCover, _⟩ hd
  obtain ⟨i, hi⟩ := numberCode_surjective_l C ⟨k, hk⟩
  have hik : (numberCode_l C i).val = k := congrArg Subtype.val hi
  change SecondOrderFunctionObjects.map_l hℳ f k d at hf
  change ∀ y, SecondOrderQuotient.mem_l hℳ y d → ∃ z,
    SecondOrderQuotient.mem_l hℳ z k ∧ SecondOrderFunctionObjects.value_l hℳ f z y at hCover
  obtain ⟨c, hc⟩ := SecondOrderFiniteEnumerationRoots.exists_l C hG hSW i f d
    (hik.symm ▸ hf) (hik.symm ▸ hCover) (fun y hy => (hRange y).mp (hd y hy))
  exact (hRange d).mpr ⟨_, hc.symm⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteClosedCover
