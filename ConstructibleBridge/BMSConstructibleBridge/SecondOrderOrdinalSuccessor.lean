import BMSConstructibleBridge.SecondOrderUnion
import BMSConstructibleBridge.SecondOrderFoundation
import BMSConstructibleBridge.SecondOrderOrdinalHistoryCoherence

/-! # 无 Collection 的实际商序数后继

配对和并集给出后继图。隶属线序的最小元直接由已验证的正则公理取得，
避免调用带有整个 KP／ZF 模型前提的上游后继定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalSuccessor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem ordinal_of_linear_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hTrans : SecondOrderTransitiveSuperset.transitive_l A)
    (hLinear : SetTheory.Structure.MembershipLinearOrder (quotient_l hℳ) (SecondOrderQuotient.mk_l hℳ A)) :
    SetTheory.Structure.IsOrdinal (quotient_l hℳ) (SecondOrderQuotient.mk_l hℳ A) := by
  refine ⟨?_, hLinear, ?_⟩
  · intro x hx y hy
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
    exact hTrans X Y hx hy
  · intro s hSubset hNonempty
    obtain ⟨S, rfl⟩ := SecondOrderQuotient.surj_l hℳ s
    have hStart : ∃ X, SecondOrderGraph.mem_l X S := by
      obtain ⟨x, hx⟩ := hNonempty
      obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
      exact ⟨X, hx⟩
    obtain ⟨C, hC, hMin⟩ := SecondOrderFoundation.exists_l hℳ S hStart
    refine ⟨SecondOrderQuotient.mk_l hℳ C, hC, ?_⟩
    intro x hx
    rcases hLinear.compare (SecondOrderQuotient.mk_l hℳ C)
      (hSubset (SecondOrderQuotient.mk_l hℳ C) hC) x (hSubset x hx) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
      exact False.elim (hMin X h hx)

theorem graph_exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) :
    ∃ U : SecondOrderGraph.code_l ℳ, ∀ X,
      SecondOrderGraph.mem_l X U ↔ SecondOrderGraph.mem_l X A ∨ SecondOrderGraph.eq_l X A := by
  obtain ⟨S, hS⟩ := SecondOrderPairSet.exists_l hℳ A A
  obtain ⟨T, hT⟩ := SecondOrderPairSet.exists_l hℳ A S
  obtain ⟨U, hU⟩ := SecondOrderUnion.exists_l hℳ T
  refine ⟨U, fun X => (hU X).trans ?_⟩
  constructor
  · rintro ⟨C, hC, hXC⟩
    rcases (hT C).mp hC with hCA | hCS
    · exact Or.inl ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ X) hCA).mp hXC)
    · have hXS := (SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ X) hCS).mp hXC
      exact Or.inr (((hS X).mp hXS).elim id id)
  · rintro (hXA | hXA)
    · exact ⟨A, (hT A).mpr (Or.inl (SecondOrderGraph.refl_l hℳ A)), hXA⟩
    · exact ⟨S, (hT S).mpr (Or.inr (SecondOrderGraph.refl_l hℳ S)), (hS X).mpr (Or.inl hXA)⟩

theorem ordinal_l (hℳ : Theory.Models ℳ theory_m) (A U : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (SecondOrderQuotient.mk_l hℳ A))
    (hU : ∀ X, SecondOrderGraph.mem_l X U ↔ SecondOrderGraph.mem_l X A ∨ SecondOrderGraph.eq_l X A) :
    SetTheory.Structure.IsOrdinal (quotient_l hℳ) (SecondOrderQuotient.mk_l hℳ U) := by
  have hSucc (x : SecondOrderQuotient.type_l hℳ) :
      SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ U) ↔
      SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A) ∨ x = SecondOrderQuotient.mk_l hℳ A := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact (hU X).trans (or_congr Iff.rfl (SecondOrderQuotient.eq_iff_l hℳ X A).symm)
  apply ordinal_of_linear_l hℳ U
  · intro X Y hX hY
    apply (hU Y).mpr
    rcases (hU X).mp hX with hXA | hXA
    · exact Or.inl (SecondOrderOrdinalHistoryCoherence.ordinal_transitive_l hℳ A hα X Y hXA hY)
    · exact Or.inl ((SecondOrderGraph.mem_congr_l hℳ (SecondOrderGraph.refl_l hℳ Y) hXA).mp hY)
  · constructor
    · intro x _ hx
      obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
      exact SecondOrderFoundation.irrefl_l hℳ X hx
    · intro x _ y _ z hz hxy hyz
      rcases (hSucc z).mp hz with hzA | rfl
      · have hyA := hα.transitive z hzA y hyz
        have hxA := hα.transitive y hyA x hxy
        exact hα.wellOrder.linear.trans x hxA y hyA z hzA hxy hyz
      · exact hα.transitive y hyz x hxy
    · intro x hx y hy
      rcases (hSucc x).mp hx with hxA | rfl
      · rcases (hSucc y).mp hy with hyA | rfl
        · exact hα.wellOrder.linear.compare x hxA y hyA
        · exact Or.inr (Or.inl hxA)
      · rcases (hSucc y).mp hy with hyA | rfl
        · exact Or.inr (Or.inr hyA)
        · exact Or.inl (fun _ => Iff.rfl)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (SecondOrderQuotient.mk_l hℳ A)) :
    ∃ U : SecondOrderGraph.code_l ℳ,
      SetTheory.Structure.IsOrdinal (quotient_l hℳ) (SecondOrderQuotient.mk_l hℳ U) ∧
      SecondOrderGraph.mem_l A U ∧
      ∀ X, SecondOrderGraph.mem_l X U ↔ SecondOrderGraph.mem_l X A ∨ SecondOrderGraph.eq_l X A := by
  obtain ⟨U, hU⟩ := graph_exists_l hℳ A
  exact ⟨U, ordinal_l hℳ A U hα hU, (hU A).mpr (Or.inr (SecondOrderGraph.refl_l hℳ A)), hU⟩

theorem empty_exists_l (hℳ : Theory.Models ℳ theory_m) : ∃ A : SecondOrderGraph.code_l ℳ,
    SetTheory.Structure.IsOrdinal (quotient_l hℳ) (SecondOrderQuotient.mk_l hℳ A) ∧
    ∀ X, ¬SecondOrderGraph.mem_l X A := by
  obtain ⟨A, hA⟩ := SecondOrderGraph.empty_l hℳ
  have hEmpty (x : SecondOrderQuotient.type_l hℳ) : ¬SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A) := by
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact hA X
  refine ⟨A, ?_, hA⟩
  apply ordinal_of_linear_l hℳ A (fun X _ hX _ => False.elim (hA X hX))
  exact ⟨fun x hx => False.elim (hEmpty x hx), fun x hx => False.elim (hEmpty x hx),
    fun x hx => False.elim (hEmpty x hx)⟩

#print axioms exists_l
#print axioms empty_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalSuccessor
