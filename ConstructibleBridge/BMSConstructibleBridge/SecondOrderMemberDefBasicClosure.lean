import BMSConstructibleBridge.SecondOrderMemberDefPair
import BMSConstructibleBridge.SecondOrderUnion

/-! # Def 中的空对象与成员并集

切片公式只在母集成员域求值。并集证明显式验证传递母集中的见证仍在域内，
不能把内部量词直接替换为环境量词而省略绝对性检查。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefBasicClosure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem empty_l (hℳ : Theory.Models ℳ theory_m) {C D e : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ C D) (he : ∀ z, ¬mem_l hℳ z e) : mem_l hℳ e D := by
  rcases hDef with ⟨hC, hPair⟩ | hDef
  · have heC : e = C := SecondOrderQuotient.ext_l hℳ e C
      (fun z => ⟨fun hz => False.elim (he z hz), fun hz => False.elim (hC z hz)⟩)
    exact (hPair e).mpr (Or.inl heC)
  · obtain ⟨A, a, ha, V, E, D₀, Q, R, T, F, H, hAC, P, hHD⟩ := hDef
    have h : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) D :=
      Or.inr ⟨A, a, ha, V, E, D₀, Q, R, T, F, H, rfl, P, hHD⟩
    obtain ⟨z, hz, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A a ha h
      (Env.empty (M := SecondOrderMemberStructure.structure_l hℳ A a ha)) Formula.falsum
    have hze : z = e := by
      apply SecondOrderQuotient.ext_l hℳ
      intro w
      constructor
      · intro hw
        obtain ⟨n, hn, rfl⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A
          (SecondOrderMemberDefProperties.subset_l hℳ h hz w hw)
        exact False.elim ((hRead n hn).mp hw)
      · intro hw
        exact False.elim (he w hw)
    exact hze ▸ hz

theorem union_l (hℳ : Theory.Models ℳ theory_m) {C D X U : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ C D) (hX : mem_l hℳ X C)
    (hTrans : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hU : ∀ w, mem_l hℳ w U ↔ ∃ y, mem_l hℳ y X ∧ mem_l hℳ w y) : mem_l hℳ U D := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ C
  obtain ⟨a, ha, _⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hX
  let η := (Env.empty (M := SecondOrderMemberStructure.structure_l hℳ A a ha)).pushFree
    (sort := SetTheory.SetSort.set) ⟨X, hX⟩
  let φ : Formula ℒ [.set] [.set] := .existsE .set <|
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))
  obtain ⟨z, hz, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A a ha hDef η φ
  have hValue n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      (SecondOrderMemberStructure.value_l hℳ A a ha n).val = mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
    change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = _
    rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
  have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
      mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
        ∃ y, mem_l hℳ y X ∧ mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) y := by
    have h := hRead n hn
    change mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
      ∃ y : SecondOrderMemberStructure.type_l hℳ A, mem_l hℳ y.val X ∧
        mem_l hℳ (SecondOrderMemberStructure.value_l hℳ A a ha n).val y.val at h
    rw [hValue n hn] at h
    refine h.trans ⟨?_, ?_⟩
    · rintro ⟨y, hy, hwy⟩
      exact ⟨y.val, hy, hwy⟩
    · rintro ⟨y, hy, hwy⟩
      exact ⟨⟨y, hTrans X hX y hy⟩, hy, hwy⟩
  have hzU : z = U := by
    apply SecondOrderQuotient.ext_l hℳ
    intro w
    constructor
    · intro hw
      obtain ⟨n, hn, rfl⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A
        (SecondOrderMemberDefProperties.subset_l hℳ hDef hz w hw)
      exact (hU _).mpr ((hRead' n hn).mp hw)
    · intro hw
      obtain ⟨y, hyX, hwy⟩ := (hU w).mp hw
      obtain ⟨n, hn, rfl⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A
        (hTrans y (hTrans X hX y hyX) w hwy)
      exact (hRead' n hn).mpr ⟨y, hyX, hwy⟩
  exact hzU ▸ hz

#print axioms empty_l
#print axioms union_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefBasicClosure
