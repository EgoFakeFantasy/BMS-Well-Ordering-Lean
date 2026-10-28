import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailOrder
import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailRange
import BMSConstructibleBridge.SecondOrderOrdinalTailMembers
import BMSConstructibleBridge.SecondOrderTriangularMonotone
import BMSConstructibleBridge.PowerlessRelativeCofinalLimitBounds

/-! # 内部 ω² 包络中非零极限阶段共尾

每个后继块的起点包含前面全部完整块，因而无最大成员。所有尾节点均被
下一块起点严格支配；基础根及成员也在首个非零块起点之下。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailCofinal

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderOrdinalDoubleTailGraph SecondOrderOrdinalDoubleTailOrder
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeHierarchySemantics (limit_l)
open PowerlessRelativeCofinalLimitBounds (cofinal_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

private theorem lt_successor_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) :
    SecondOrderOrder.lt_l n (succ_l n) :=
  (SecondOrderOrdinalTailMembers.lt_succ_l hℳ n n).mpr (Or.inr rfl)

variable (hℳ : Theory.Models ℳ theory_m) {S G : SecondOrderModel.set_l ℳ} {r : num_l ℳ}
  (hG : spec_l S r G) (hS : ∀ a, SecondOrderDomain.wf_l S a)

theorem block_limit_l (n : num_l ℳ) :
    limit_l hℳ (tail_l hℳ hG hS (succ_l n) (zero_l ℳ)) := by
  refine ⟨⟨base_l hℳ hS r, (reading_l hℳ hG hS _ _ _).mpr (Or.inr (Or.inl rfl))⟩, ?_⟩
  intro x hx
  rcases (reading_l hℳ hG hS _ _ x).mp hx with hx | rfl | ⟨i, j, hij, rfl⟩
  · refine ⟨tail_l hℳ hG hS (zero_l ℳ) (zero_l ℳ), ?_, ?_⟩
    · exact (reading_l hℳ hG hS _ _ _).mpr
        (Or.inr (Or.inr ⟨_, _, Or.inl (SecondOrderOrder.zero_succ_l hℳ n), rfl⟩))
    · exact (reading_l hℳ hG hS _ _ x).mpr (Or.inl hx)
  · refine ⟨tail_l hℳ hG hS (zero_l ℳ) (zero_l ℳ), ?_, ?_⟩
    · exact (reading_l hℳ hG hS _ _ _).mpr
        (Or.inr (Or.inr ⟨_, _, Or.inl (SecondOrderOrder.zero_succ_l hℳ n), rfl⟩))
    · exact (reading_l hℳ hG hS _ _ _).mpr (Or.inr (Or.inl rfl))
  · have hi : SecondOrderOrder.lt_l i (succ_l n) := by
      rcases hij with hi | ⟨_, hj⟩
      · exact hi
      · exact (SecondOrderTriangularMonotone.zero_bound_l hℳ j hj).elim
    refine ⟨tail_l hℳ hG hS i (succ_l j), ?_, ?_⟩
    · exact (reading_l hℳ hG hS _ _ _).mpr (Or.inr (Or.inr ⟨_, _, Or.inl hi, rfl⟩))
    · exact (reading_l hℳ hG hS _ _ _).mpr
        (Or.inr (Or.inr ⟨i, j, Or.inr ⟨rfl, lt_successor_l hℳ j⟩, rfl⟩))

theorem properties_l
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (base_l hℳ hS r))
    (C : SecondOrderGraph.code_l ℳ)
    (hC : ∀ X : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l X C ↔
      SecondOrderGraph.mem_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
        SecondOrderGraph.eq_l X (⟨S, r, hS r⟩ : SecondOrderGraph.code_l ℳ) ∨
          ∃ n m, SecondOrderGraph.eq_l X (code_l hℳ hG hS n m)) :
    SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ C) ∧
      mem_l hℳ (base_l hℳ hS r) (mk_l hℳ C) ∧
        limit_l hℳ (mk_l hℳ C) ∧ cofinal_l (mk_l hℳ C) := by
  have hRead (x : type_l hℳ) : mem_l hℳ x (mk_l hℳ C) ↔
      mem_l hℳ x (base_l hℳ hS r) ∨ x = base_l hℳ hS r ∨
        ∃ n m, x = tail_l hℳ hG hS n m := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hC X).trans (or_congr Iff.rfl (or_congr (SecondOrderQuotient.eq_iff_l hℳ _ _).symm
      (exists_congr (fun _ => exists_congr (fun _ => (SecondOrderQuotient.eq_iff_l hℳ _ _).symm)))))
  have hTrans (x : type_l hℳ) (hx : mem_l hℳ x (mk_l hℳ C))
      (y : type_l hℳ) (hy : mem_l hℳ y x) : mem_l hℳ y (mk_l hℳ C) := by
    apply (hRead y).mpr
    rcases (hRead x).mp hx with hx | rfl | ⟨n, m, rfl⟩
    · exact Or.inl (hα.transitive x hx y hy)
    · exact Or.inl hy
    · rcases (reading_l hℳ hG hS n m y).mp hy with hy | hy | ⟨i, j, _, hy⟩
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr ⟨i, j, hy⟩)
  have hCofinal : cofinal_l (mk_l hℳ C) := by
    intro x hx
    rcases (hRead x).mp hx with hx | rfl | ⟨n, m, rfl⟩
    · refine ⟨tail_l hℳ hG hS (succ_l (zero_l ℳ)) (zero_l ℳ), ?_, ?_,
        block_limit_l hℳ hG hS (zero_l ℳ)⟩
      · exact (hRead _).mpr (Or.inr (Or.inr ⟨_, _, rfl⟩))
      · exact (reading_l hℳ hG hS _ _ x).mpr (Or.inl hx)
    · refine ⟨tail_l hℳ hG hS (succ_l (zero_l ℳ)) (zero_l ℳ), ?_, ?_,
        block_limit_l hℳ hG hS (zero_l ℳ)⟩
      · exact (hRead _).mpr (Or.inr (Or.inr ⟨_, _, rfl⟩))
      · exact (reading_l hℳ hG hS _ _ _).mpr (Or.inr (Or.inl rfl))
    · refine ⟨tail_l hℳ hG hS (succ_l n) (zero_l ℳ), ?_, ?_, block_limit_l hℳ hG hS n⟩
      · exact (hRead _).mpr (Or.inr (Or.inr ⟨_, _, rfl⟩))
      · exact (reading_l hℳ hG hS _ _ _).mpr
          (Or.inr (Or.inr ⟨n, m, Or.inl (lt_successor_l hℳ n), rfl⟩))
  have hMember := (hRead (base_l hℳ hS r)).mpr (Or.inr (Or.inl rfl))
  refine ⟨?_, hMember, ⟨⟨_, hMember⟩, ?_⟩, hCofinal⟩
  · exact SecondOrderOrdinalSuccessor.ordinal_of_linear_l hℳ C
      (fun X Y hX hY => hTrans (mk_l hℳ X) hX (mk_l hℳ Y) hY)
      (linear_l hℳ hG hS hα _ (fun x hx => (hRead x).mp hx))
  · intro x hx
    obtain ⟨γ, hγ, hxγ, _⟩ := hCofinal x hx
    exact ⟨γ, hγ, hxγ⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalDoubleTailCofinal
