import BMSConstructibleBridge.SecondOrderFiniteRootRepresentatives
import BMSConstructibleBridge.SecondOrderGraphFormulaGuard
import BMSConstructibleBridge.SecondOrderObjectSyntax
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-!
# 商内有限枚举到统一内部根代表关系

函数 f 是商内实际集合函数，定义域为一个内部自然数序数 k。其值若由给定
扩展图的根表示，则原理解产生统一根关系；双模拟单值性由 f 的函数性推出。
内部最小根选择及有限数值界给出精确像。k 可为非标准数，不要求外部有限性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteEnumerationRoots

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic
open SecondOrderFiniteExtensionGraph PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

theorem member_number_l (C : source_coding_l hℳ) (k : SecondOrderModel.num_l ℳ)
    (x : SecondOrderQuotient.type_l hℳ)
    (hx : SecondOrderQuotient.mem_l hℳ x (numberCode_l C k).val) :
    ∃ i, SecondOrderOrder.lt_l i k ∧ (numberCode_l C i).val = x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  change SecondOrderGraph.mem_l X (SecondOrderNaturalGraph.code_l hℳ C.less C.less_spec k) at hx
  obtain ⟨i, hi, hXi⟩ := hx
  exact ⟨i, (C.less_spec i k).mp hi, (SecondOrderQuotient.eq_iff_l hℳ _ X).mpr
    (SecondOrderGraph.symm_l hℳ hXi)⟩

theorem relation_exists_l (C : source_coding_l hℳ) {S E G : SecondOrderModel.set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) (f : SecondOrderQuotient.type_l hℳ) :
    ∃ R : SecondOrderModel.set_l ℳ, ∀ i n, SecondOrderPairing.relation_l R i n ↔
      SecondOrderFunctionObjects.value_l hℳ f (numberCode_l C i).val
        (SecondOrderQuotient.mk_l hℳ (code_l hℳ hG hS n)) := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.fvar .here) (.fvar (.there .here))
  obtain ⟨R, hR⟩ := SecondOrderGraphFormulaGuard.exists_l hℳ φ
    ((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree f) C.less G
  refine ⟨R, fun i n => (hR i n).trans ?_⟩
  simp only [φ, SecondOrderObjectSyntax.value_l]
  change (∃ (hi : SecondOrderDomain.wf_l C.less i) (hn : SecondOrderDomain.wf_l G n),
    SecondOrderFunctionObjects.value_l hℳ f (numberCode_l C i).val
      (SecondOrderQuotient.mk_l hℳ (code_l hℳ hG hS n))) ↔ _
  exact ⟨fun ⟨_, _, h⟩ => h, fun h =>
    ⟨SecondOrderNaturalGraph.wf_l hℳ C.less C.less_spec i, wf_l hℳ hG hS n, h⟩⟩

theorem exists_l (C : source_coding_l hℳ) {S E G : SecondOrderModel.set_l ℳ}
    {hE : SecondOrderBinaryPowers.spec_l E} (hG : spec_l S E hE G)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) (k : SecondOrderModel.num_l ℳ)
    (f d : SecondOrderQuotient.type_l hℳ)
    (hf : SecondOrderFunctionObjects.map_l hℳ f (numberCode_l C k).val d)
    (hCover : ∀ y, SecondOrderQuotient.mem_l hℳ y d → ∃ x,
      SecondOrderQuotient.mem_l hℳ x (numberCode_l C k).val ∧
        SecondOrderFunctionObjects.value_l hℳ f x y)
    (hRoots : ∀ y, SecondOrderQuotient.mem_l hℳ y d → ∃ n,
      y = SecondOrderQuotient.mk_l hℳ (code_l hℳ hG hS n)) :
    ∃ c, SecondOrderQuotient.mk_l hℳ
      (code_l hℳ hG hS (SecondOrderPairing.value_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) c)) = d := by
  obtain ⟨R, hR⟩ := relation_exists_l C hG hS f
  have hTotal i (hi : SecondOrderOrder.lt_l i k) : ∃ n, SecondOrderPairing.relation_l R i n := by
    obtain ⟨y, hy, _⟩ := hf.2 (numberCode_l C i).val ((numberCode_mem_iff_lt_l C i k).mpr hi)
    obtain ⟨n, rfl⟩ := hRoots y hy.1
    exact ⟨n, (hR i n).mpr hy.2⟩
  have hUnique i (_ : SecondOrderOrder.lt_l i k) n m
      (hn : SecondOrderPairing.relation_l R i n) (hm : SecondOrderPairing.relation_l R i m) :
      SecondOrderGraph.eq_l (code_l hℳ hG hS n) (code_l hℳ hG hS m) :=
    (SecondOrderQuotient.eq_iff_l hℳ _ _).mp
      (SecondOrderFunctionLaws.value_unique_l hℳ hf ((hR i n).mp hn) ((hR i m).mp hm))
  obtain ⟨c, hc⟩ := SecondOrderFiniteRootRepresentatives.exists_l hℳ hG hS R k hTotal hUnique
  refine ⟨c, SecondOrderQuotient.ext_l hℳ _ d (fun y => ?_)⟩
  obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
  change SecondOrderGraph.mem_l Y _ ↔ _
  rw [hc Y]
  constructor
  · rintro ⟨i, n, _, hIn, hYn⟩
    have hy := (SecondOrderFunctionLaws.value_mem_l hℳ hf ((hR i n).mp hIn)).2
    have hEq := (SecondOrderQuotient.eq_iff_l hℳ Y (code_l hℳ hG hS n)).mpr hYn
    exact hEq.symm ▸ hy
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hCover _ hy
    obtain ⟨i, hik, hix⟩ := member_number_l C k x hx
    obtain ⟨n, hn⟩ := hRoots _ hy
    refine ⟨i, n, hik,
      (hR i n).mpr ?_, (SecondOrderQuotient.eq_iff_l hℳ Y _).mp hn⟩
    exact hix.symm ▸ hn ▸ hxy

#print axioms relation_exists_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteEnumerationRoots
