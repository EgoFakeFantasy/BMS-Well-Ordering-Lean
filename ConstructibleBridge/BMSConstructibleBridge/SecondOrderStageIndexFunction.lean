import BMSConstructibleBridge.SecondOrderRootCorrespondence
import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.PowerlessBMSQuotientCoding
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 规范阶段根指标到实际阶段对象的集合双射

最小根代表域的 ω 子集是实际定义域。混合有序对像把每个编号直接接到
对应成员对象，不选逆枚举。规范代表的覆盖和单射给出实际双射；序数
阶段的内部前驱良基性继续复用原根前驱图，不在这里重造拉回关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageIndexFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    {Q D R : SecondOrderModel.set_l ℳ} (h : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (I : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (hI : setRel_l K I D) :
    ∃ J : type_l hℳ, map_l (ℳ := 𝒱) J I.val (SecondOrderQuotient.mk_l hℳ A) ∧
      (∀ y, mem_l hℳ y (SecondOrderQuotient.mk_l hℳ A) →
        ∃ x, mem_l hℳ x I.val ∧ value_l (ℳ := 𝒱) J x y) ∧
      injective_l (ℳ := 𝒱) J ∧
      ∀ x y, value_l (ℳ := 𝒱) J x y ↔
        ∃ n, ∃ hn : SecondOrderModel.mem_l n D,
          x = (numberCode_l K n).val ∧
          y = SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn) := by
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num, .set] :=
    .conj (.equal (.fvar .here) (.fvar (.there .here)))
      (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil)))
  obtain ⟨E, hE⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (SecondOrderArithmetic.pure_language_m _ rfl) (Env.empty.pushFree D)
  have hRead n a : SecondOrderPairing.relation_l E n a ↔ n = a ∧ SecondOrderModel.mem_l n D := by
    refine (hE n a).trans ?_
    simp only [φ, Formula.satisfies]
    rfl
  have hRoots n a (he : SecondOrderPairing.relation_l E n a) :
      SecondOrderDomain.wf_l K.less n ∧ SecondOrderDomain.wf_l A.real a := by
    obtain ⟨rfl, hn⟩ := (hRead n a).mp he
    exact ⟨SecondOrderNaturalGraph.wf_l hℳ K.less K.less_spec n,
      SecondOrderDomain.child_l hℳ A.real A.root n A.wf ((h.representatives n).mp hn).1⟩
  obtain ⟨J, hJ⟩ := SecondOrderMixedImage.exists_l hℳ K.less A.real E hRoots
  have hGraph (p : type_l hℳ) : mem_l hℳ p J ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D,
        SecondOrderPairObjects.ordered_l hℳ (numberCode_l K n).val
          (SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn)) p := by
    refine (hJ p).trans ⟨?_, ?_⟩
    · rintro ⟨n, a, he, hp⟩
      obtain ⟨rfl, hn⟩ := (hRead n a).mp he
      exact ⟨n, hn, hp⟩
    · rintro ⟨n, hn, hp⟩
      exact ⟨n, n, (hRead n n).mpr ⟨rfl, hn⟩, hp⟩
  have hValue (x y : type_l hℳ) : value_l (ℳ := 𝒱) J x y ↔
      ∃ n, ∃ hn : SecondOrderModel.mem_l n D, x = (numberCode_l K n).val ∧
        y = SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn) := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨n, hn, hp'⟩ := (hGraph p).mp hp
      exact ⟨n, hn, (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl⟩
    · rintro ⟨n, hn, rfl, rfl⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ (numberCode_l K n).val
        (SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn))
      exact ⟨p, (hGraph p).mpr ⟨n, hn, hp⟩, hp⟩
  have hMap : map_l (ℳ := 𝒱) J I.val (SecondOrderQuotient.mk_l hℳ A) := by
    constructor
    · intro p hp
      obtain ⟨n, hn, hxy⟩ := (hGraph p).mp hp
      exact ⟨(numberCode_l K n).val,
        SecondOrderQuotient.mk_l hℳ (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn), (hI n).mpr hn,
        SecondOrderGraph.child_mem_l hℳ A n ((h.representatives n).mp hn).1, hxy⟩
    · intro x hx
      obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, I.property x hx⟩
      have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
      have hnD : SecondOrderModel.mem_l n D := (hI n).mp (hn'.symm ▸ hx)
      let N := SecondOrderRootCorrespondence.member_code_l hℳ A h n hnD
      refine ⟨SecondOrderQuotient.mk_l hℳ N, ⟨SecondOrderGraph.child_mem_l hℳ A n
        ((h.representatives n).mp hnD).1, (hValue x _).mpr ⟨n, hnD, hn'.symm, rfl⟩⟩, ?_⟩
      rintro y ⟨_, hxy⟩
      obtain ⟨m, hm, hxm, hym⟩ := (hValue x y).mp hxy
      have hNum : m = n := numberCode_injective_l K (Subtype.ext (hxm.symm.trans hn'.symm))
      subst m
      exact hym
  refine ⟨J, hMap, ?_, ?_, hValue⟩
  · intro y hy
    obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
    obtain ⟨a, ha, hYa⟩ := hy
    obtain ⟨n, hn, hNa⟩ := SecondOrderRootRepresentatives.covers_l hℳ h.equality h.representatives ha
    let N := SecondOrderRootCorrespondence.member_code_l hℳ A h n hn
    have hYN : SecondOrderQuotient.mk_l hℳ Y = SecondOrderQuotient.mk_l hℳ N :=
      (SecondOrderQuotient.eq_iff_l hℳ Y N).mpr (SecondOrderBisimulation.trans_l hℳ
        Y.real A.real A.real Y.root a n hYa (SecondOrderBisimulation.symm_l hℳ A.real A.real n a hNa))
    exact ⟨(numberCode_l K n).val, (hI n).mpr hn, (hValue _ _).mpr ⟨n, hn, rfl, hYN⟩⟩
  · intro x y z hxz hyz
    obtain ⟨n, hn, hxn, hzn⟩ := (hValue x z).mp hxz
    obtain ⟨m, hm, hym, hzm⟩ := (hValue y z).mp hyz
    have hNM := (SecondOrderQuotient.eq_iff_l hℳ
      (SecondOrderRootCorrespondence.member_code_l hℳ A h n hn)
      (SecondOrderRootCorrespondence.member_code_l hℳ A h m hm)).mp (hzn.symm.trans hzm)
    have hNum := SecondOrderRootRepresentatives.injective_l hℳ h.equality h.representatives hn hm hNM
    subst m
    exact hxn.trans hym.symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderStageIndexFunction
