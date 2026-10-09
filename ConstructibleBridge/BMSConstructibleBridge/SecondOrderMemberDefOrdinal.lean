import BMSConstructibleBridge.SecondOrderMemberBounded
import BMSConstructibleBridge.SecondOrderMemberDefProperties
import BMSConstructibleBridge.SecondOrderOrdinalComparison

/-! # 传递母集所包含序数的 Def 覆盖

若序数 α 已是母集成员，Def 保留它；否则 α 恰为母集中全部序数的切片。
该切片使用已核验的 Δ₀ 判定与母域绝对性，不要求全分离或收集在母域成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefOrdinal

open Logic FirstOrder
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {C D α : type_l hℳ}
    (hDef : SecondOrderMemberDef.spec_l hℳ C D)
    (hTrans : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (SecondOrderQuotient.structure_l hℳ)) α)
    (hSubset : ∀ x, mem_l hℳ x α → mem_l hℳ x C) : mem_l hℳ α D := by
  classical
  by_cases hαC : mem_l hℳ α C
  · exact SecondOrderMemberDefProperties.contains_l hℳ hDef (fun x y hx hy => hTrans x hx y hy) α hαC
  rcases hDef with ⟨hEmpty, hPair⟩ | hDef
  · have hαEq : α = C := SecondOrderQuotient.ext_l hℳ α C
      (fun x => ⟨fun hx => False.elim (hEmpty x (hSubset x hx)), fun hx => False.elim (hEmpty x hx)⟩)
    exact (hPair α).mpr (Or.inl hαEq)
  · obtain ⟨A, a, ha, V, E, D₀, Q, R, T, F, H, hAC, P, hHD⟩ := hDef
    rw [← hAC] at hαC hTrans hSubset
    have h : SecondOrderMemberDef.spec_l hℳ (mk_l hℳ A) D :=
      Or.inr ⟨A, a, ha, V, E, D₀, Q, R, T, F, H, rfl, P, hHD⟩
    let η := Env.empty (M := SecondOrderMemberStructure.structure_l hℳ A a ha)
    let φ : Formula ℒ [.set] [] := PowerlessOrdinalBounded.ordinal_m (.bvar .here)
    obtain ⟨z, hz, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A a ha h η φ
    have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
        mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
          SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
            (SecondOrderQuotient.structure_l hℳ)) (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) := by
      have hOrd := SecondOrderMemberBounded.ordinal_l hTrans
        (η.pushBound (SecondOrderMemberStructure.value_l hℳ A a ha n)) (.bvar .here)
      have hValue : (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
          mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
        change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = _
        rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
      have h' := (hRead n hn).trans hOrd
      change mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
        SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
          (SecondOrderQuotient.structure_l hℳ)) (SecondOrderMemberStructure.value_l hℳ A a ha n).val at h'
      rw [hValue] at h'
      exact h'
    have hzα : z = α := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx
        have hxC := SecondOrderMemberDefProperties.subset_l hℳ h hz x hx
        obtain ⟨n, hn, rfl⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hxC
        have hX := (hRead' n hn).mp hx
        rcases SecondOrderOrdinalComparison.compare_l hℳ hX hα with hEq | hMem | hMem
        · exact False.elim (hαC (hEq ▸ hxC))
        · exact hMem
        · exact False.elim (hαC (hTrans _ hxC α hMem))
      · intro hx
        have hX : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
            (SecondOrderQuotient.structure_l hℳ)) x := by
          apply SetTheory.Structure.IsOrdinal.mem hα
          exact hx
        obtain ⟨n, hn, rfl⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A (hSubset x hx)
        exact (hRead' n hn).mpr hX
    exact hzα ▸ hz

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefOrdinal
