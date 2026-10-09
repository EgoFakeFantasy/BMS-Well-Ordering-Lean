import BMSConstructibleBridge.SecondOrderMemberBounded
import BMSConstructibleBridge.SecondOrderMemberDefBasicClosure

/-! # 传递母集上的有界可定义子集属于 Def

全部参数明确属于母集。给定环境中的 Δ₀ 公式与精确子集规格，通过成员
子结构绝对性核验实际切片，不要求母集模型满足完整分离或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefBoundedSlice

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SecondOrderMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C D Z : type_l hℳ} (hDef : SecondOrderMemberDef.spec_l hℳ C D)
    (hTrans : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C)
    (hZ : ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x C ∧ φ.satisfies (η.pushFree x)) : mem_l hℳ Z D := by
  classical
  by_cases hEmpty : ∀ x, ¬mem_l hℳ x C
  · exact SecondOrderMemberDefBasicClosure.empty_l hℳ hDef (fun x hx => hEmpty x ((hZ x).mp hx).1)
  · obtain ⟨x, hx⟩ := not_forall.mp hEmpty
    have hxC := Classical.not_not.mp hx
    obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ C
    obtain ⟨a, ha, _⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hxC
    let ξ : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) [] Δ :=
      { boundVal := fun v => nomatch v
        freeVal := fun v => ⟨η.freeVal v, hParams _ v⟩ }
    obtain ⟨z, hz, hRead⟩ := SecondOrderMemberDefProperties.coverage_l hℳ A a ha hDef ξ φ.abstractFreeTop
    have hRead' n (hn : SecondOrderPairing.relation_l A.real n A.root) :
        mem_l hℳ (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) z ↔
          φ.satisfies (η.pushFree (sort := SetTheory.SetSort.set) (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn))) := by
      have hValue : (SecondOrderMemberStructure.value_l hℳ A a ha n).val =
          mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn) := by
        change mk_l hℳ (SecondOrderMemberNormalizer.code_l hℳ A a ha n) = _
        rw [SecondOrderMemberNormalizer.code_fixed_l hℳ A a ha n hn]
      have hEnv : SecondOrderMemberBounded.env_l
          (ξ.pushFree (sort := SetTheory.SetSort.set) (SecondOrderMemberStructure.value_l hℳ A a ha n)) =
            η.pushFree (sort := SetTheory.SetSort.set) (mk_l hℳ (SecondOrderGraph.child_l hℳ A n hn)) := by
        apply Env.ext
        · intro _ v; nomatch v
        · intro s v
          cases s
          cases v with
          | here => exact hValue
          | there v => rfl
      have hSource := SecondOrderMemberBounded.formula_l hTrans hφ
        (ξ.pushFree (sort := SetTheory.SetSort.set) (SecondOrderMemberStructure.value_l hℳ A a ha n))
      rw [hEnv] at hSource
      exact (hRead n hn).trans ((Formula.satisfies_abstractFreeTop _ _ φ).trans hSource)
    have hEq : z = Z := by
      apply SecondOrderQuotient.ext_l hℳ
      intro y
      constructor
      · intro hy
        have hyC := SecondOrderMemberDefProperties.subset_l hℳ hDef hz y hy
        obtain ⟨n, hn, hEq⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hyC
        rw [hEq] at hy hyC ⊢
        exact (hZ _).mpr ⟨hyC, (hRead' n hn).mp hy⟩
      · intro hy
        have hy' := (hZ y).mp hy
        obtain ⟨n, hn, hEq⟩ := SecondOrderMemberDefProperties.member_root_l hℳ A hy'.1
        rw [hEq] at hy' ⊢
        exact (hRead' n hn).mpr hy'.2
    exact hEq ▸ hz

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefBoundedSlice
