import BMSConstructibleBridge.SecondOrderOrdinalTailOrdinal
import BMSConstructibleBridge.SecondOrderOrdinalTailRange

/-! # ω 尾包络为高于基础序数的非零极限序数

包络成员按基础成员、基础根、尾节点三类穷尽。逐成员序数性与原模型数序
给出隶属线序；正则给出集合意义下的良序，不要求外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailLimit

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem properties_l (hℳ : Theory.Models ℳ theory_m) {S G : SecondOrderModel.set_l ℳ} {r : num_l ℳ}
    (hG : SecondOrderOrdinalTailGraph.spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ ⟨S, r, hS r⟩))
    (C : SecondOrderGraph.code_l ℳ)
    (hC : ∀ X : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l X C ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          ∃ n, SecondOrderGraph.eq_l X (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n)) :
    SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ C) ∧
      mem_l hℳ (mk_l hℳ ⟨S, r, hS r⟩) (mk_l hℳ C) ∧
        ∀ x : type_l hℳ, mem_l hℳ x (mk_l hℳ C) → ∃ y : type_l hℳ,
          mem_l hℳ y (mk_l hℳ C) ∧ mem_l hℳ x y := by
  let A : type_l hℳ := mk_l hℳ ⟨S, r, hS r⟩
  let T (n : num_l ℳ) : type_l hℳ := mk_l hℳ (SecondOrderOrdinalTailGraph.code_l hℳ hG hS n)
  have hRead (x : type_l hℳ) : mem_l hℳ x (mk_l hℳ C) ↔
      mem_l hℳ x A ∨ x = A ∨ ∃ n, x = T n := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hC X).trans (or_congr Iff.rfl (or_congr
      (SecondOrderQuotient.eq_iff_l hℳ _ _).symm
      (exists_congr (fun _ => (SecondOrderQuotient.eq_iff_l hℳ _ _).symm))))
  have hTailRead (n : num_l ℳ) (x : type_l hℳ) : mem_l hℳ x (T n) ↔
      mem_l hℳ x A ∨ x = A ∨ ∃ m, SecondOrderOrder.lt_l m n ∧ x = T m := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (SecondOrderOrdinalTailMembers.members_l hℳ hG hS n X).trans
      (or_congr Iff.rfl (or_congr (SecondOrderQuotient.eq_iff_l hℳ _ _).symm
        (exists_congr (fun _ => and_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ _ _).symm))))
  have hTailOrdinal := SecondOrderOrdinalTailOrdinal.ordinal_l hℳ hG hS hα
  have hMemberOrdinal (x : type_l hℳ) (hx : mem_l hℳ x (mk_l hℳ C)) :
      SetTheory.Structure.IsOrdinal (quotient_l hℳ) x := by
    rcases (hRead x).mp hx with hx | rfl | ⟨n, rfl⟩
    · exact SetTheory.Structure.IsOrdinal.mem hα hx
    · exact hα
    · exact hTailOrdinal n
  have hTrans (x : type_l hℳ) (hx : mem_l hℳ x (mk_l hℳ C))
      (y : type_l hℳ) (hy : mem_l hℳ y x) : mem_l hℳ y (mk_l hℳ C) := by
    apply (hRead y).mpr
    rcases (hRead x).mp hx with hx | rfl | ⟨n, rfl⟩
    · exact Or.inl (hα.transitive x hx y hy)
    · exact Or.inl hy
    · rcases (hTailRead n y).mp hy with hy | hy | ⟨m, _, hy⟩
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr ⟨m, hy⟩)
  refine ⟨?_, (hRead A).mpr (Or.inr (Or.inl rfl)), ?_⟩
  · apply SecondOrderOrdinalSuccessor.ordinal_of_linear_l hℳ C
    · exact fun X Y hX hY => hTrans (mk_l hℳ X) hX (mk_l hℳ Y) hY
    · constructor
      · intro x _ hx
        obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
        exact SecondOrderFoundation.irrefl_l hℳ X hx
      · intro x _ y _ z hz hxy hyz
        exact (hMemberOrdinal z hz).transitive y hyz x hxy
      · intro x hx y hy
        rcases (hRead x).mp hx with hx | rfl | ⟨n, rfl⟩
        · rcases (hRead y).mp hy with hy | rfl | ⟨m, rfl⟩
          · exact hα.wellOrder.linear.compare x hx y hy
          · exact Or.inr (Or.inl hx)
          · exact Or.inr (Or.inl ((hTailRead m x).mpr (Or.inl hx)))
        · rcases (hRead y).mp hy with hy | rfl | ⟨m, rfl⟩
          · exact Or.inr (Or.inr hy)
          · exact Or.inl (fun _ => Iff.rfl)
          · exact Or.inr (Or.inl ((hTailRead m A).mpr (Or.inr (Or.inl rfl))))
        · rcases (hRead y).mp hy with hy | rfl | ⟨m, rfl⟩
          · exact Or.inr (Or.inr ((hTailRead n y).mpr (Or.inl hy)))
          · exact Or.inr (Or.inr ((hTailRead n A).mpr (Or.inr (Or.inl rfl))))
          · rcases SecondOrderOrder.trichotomy_l hℳ n m with hnm | rfl | hmn
            · exact Or.inr (Or.inl ((hTailRead m (T n)).mpr (Or.inr (Or.inr ⟨n, hnm, rfl⟩))))
            · exact Or.inl (fun _ => Iff.rfl)
            · exact Or.inr (Or.inr ((hTailRead n (T m)).mpr (Or.inr (Or.inr ⟨m, hmn, rfl⟩))))
  · intro x hx
    rcases (hRead x).mp hx with hx | rfl | ⟨n, rfl⟩
    · exact ⟨T (zero_l ℳ), (hRead _).mpr (Or.inr (Or.inr ⟨zero_l ℳ, rfl⟩)),
        (hTailRead _ x).mpr (Or.inl hx)⟩
    · exact ⟨T (zero_l ℳ), (hRead _).mpr (Or.inr (Or.inr ⟨zero_l ℳ, rfl⟩)),
        (hTailRead _ A).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨T (succ_l n), (hRead _).mpr (Or.inr (Or.inr ⟨succ_l n, rfl⟩)),
        (hTailRead _ (T n)).mpr (Or.inr (Or.inr ⟨n,
          (SecondOrderOrdinalTailMembers.lt_succ_l hℳ n n).mpr (Or.inr rfl), rfl⟩))⟩

#print axioms properties_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalTailLimit
