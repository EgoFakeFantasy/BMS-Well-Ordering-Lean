import BMSConstructibleBridge.SecondOrderMemberDefProperties

/-! # 两个母集成员的无序对属于 Def

用母集内部的等式析取公式取得精确切片，再以外延性对齐实际无序对。
这里只用两个已给参数，不要求母集模型满足配对公理，也不调用 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefPair

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem member_l (hℳ : Theory.Models ℳ theory_m) {C D x y p : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ C D) (hx : mem_l hℳ x C) (hy : mem_l hℳ y C)
    (hp : SecondOrderPairObjects.pair_l hℳ x y p) : mem_l hℳ p D := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ C
  obtain ⟨a, ha, _⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hx
  let η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) [] [.set, .set] :=
    Env.empty (M := SecondOrderMemberStructure.structure_l hℳ A a ha)
      |>.pushFree (sort := SetTheory.SetSort.set) ⟨y, hy⟩ |>.pushFree (sort := SetTheory.SetSort.set) ⟨x, hx⟩
  let φ : Formula ℒ [.set] [.set, .set] :=
    .disj (.equal (.bvar .here) (.fvar .here)) (.equal (.bvar .here) (.fvar (.there .here)))
  obtain ⟨z, hz, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A a ha hDef η φ
  have hValue n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      (SecondOrderMemberStructure.value_l hℳ A a ha n).val = mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
    change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = _
    rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
  have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
        mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) = x ∨ mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) = y := by
    have h := hRead n hn
    change mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
      SecondOrderMemberStructure.value_l hℳ A a ha n = ⟨x, hx⟩ ∨
        SecondOrderMemberStructure.value_l hℳ A a ha n = ⟨y, hy⟩ at h
    refine h.trans (or_congr ?_ ?_)
    · exact ⟨fun he => (hValue n hn).symm.trans (congrArg Subtype.val he),
        fun he => Subtype.ext ((hValue n hn).trans he)⟩
    · exact ⟨fun he => (hValue n hn).symm.trans (congrArg Subtype.val he),
        fun he => Subtype.ext ((hValue n hn).trans he)⟩
  have hzp : z = p := by
    apply SecondOrderQuotient.ext_l hℳ
    intro w
    constructor
    · intro hw
      obtain ⟨n, hn, rfl⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A
        (SecondOrderMemberDefProperties.subset_l hℳ hDef hz w hw)
      exact (hp _).mpr ((hRead' n hn).mp hw)
    · intro hw
      have hwC : mem_l hℳ w (mk_l hℳ A) := by
        rcases (hp w).mp hw with rfl | rfl
        · exact hx
        · exact hy
      obtain ⟨n, hn, rfl⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hwC
      exact (hRead' n hn).mpr ((hp _).mp hw)
  exact hzp ▸ hz

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefPair
