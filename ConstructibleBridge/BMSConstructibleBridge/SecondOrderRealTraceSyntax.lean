import BMSConstructibleBridge.PowerlessBMSQuotientReals
import BMSConstructibleBridge.GraphTranslation

/-! # 原二阶实数与纯集合代表的逐数迹公式

less 是实际内部自然数序图，A/a 是一个内部良基根码，X 是原实数变量。
迹公式只读取所有内部自然数，不能单独排除 A 中的非自然数成员。
代表唯一性必须另行给出 ω 子集守卫；没有用图码唯一性代替商对象唯一性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRealTraceSyntax

open Logic FirstOrder SecondOrderSyntax PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

def formula_m {Γ Δ : SortContext signature_m}
    (less A : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num)
    (X : Term signature_m Γ Δ .set) : Formula signature_m Γ Δ :=
  .forallE .num <| .iff
    (GraphTranslation.atom_m GraphSyntax.mem_m (up less) (up A) (.bvar .here) (up a))
    (.rel .mem (.cons (.bvar .here) (.cons (up X) .nil)))

theorem pure_m {Γ Δ : SortContext signature_m}
    (less A : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num)
    (X : Term signature_m Γ Δ .set) (hLess : pure_term_m less = true)
    (hA : pure_term_m A = true) (ha : pure_term_m a = true) (hX : pure_term_m X = true) :
    SecondOrderArithmetic.language_m (formula_m less A a X) = true := by
  have hGraph : SecondOrderArithmetic.language_m GraphSyntax.mem_m = true := by
    change SecondOrderArithmetic.language_m GraphSyntax.mem_matrix_m = true
    exact SecondOrderArithmetic.pure_language_m _ GraphSyntax.mem_matrix_pure_m
  have hMem := GraphTranslation.atom_pure_m GraphSyntax.mem_m (up less) (up A) (.bvar .here) (up a) hGraph
    ((PrimitiveFormulas.weaken_l less).trans hLess) ((PrimitiveFormulas.weaken_l A).trans hA)
    rfl ((PrimitiveFormulas.weaken_l a).trans ha)
  change (SecondOrderArithmetic.language_m _ && (pure_term_m (up X) && true)) = true
  rw [hMem, PrimitiveFormulas.weaken_l, hX]
  rfl

def trace_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (less A : SecondOrderModel.set_l ℳ) (a : SecondOrderModel.num_l ℳ)
    (X : SecondOrderModel.set_l ℳ) : Prop :=
  ∀ n, (∃ b, SecondOrderPairing.relation_l A b a ∧ SecondOrderBisimulation.eq_l less A n b) ↔
    SecondOrderModel.mem_l n X

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m} {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (less A : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num)
    (X : Term signature_m Γ Δ .set) :
    (formula_m less A a X).satisfies η ↔ trace_l (less.eval η) (A.eval η) (a.eval η) (X.eval η) := by
  simp only [formula_m, trace_l, Formula.satisfies, SecondOrderInterpretation.mem_l,
    up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem reading_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (hA : ThirdOrderSemantics.subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ A) K.omega)
    (X : SecondOrderModel.set_l ℳ) :
    trace_l K.less A.real A.root X ↔ setRel_l K ⟨SecondOrderQuotient.mk_l hℳ A, hA⟩ X := Iff.rfl

/-- ω 子集接口上的实数迹总唯一性；守卫还用于反向的代表唯一性。 -/
theorem exists_unique_l (K : source_coding_l hℳ) (A : SecondOrderGraph.code_l ℳ)
    (hA : ThirdOrderSemantics.subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ A) K.omega) :
    ∃! X : SecondOrderModel.set_l ℳ, trace_l K.less A.real A.root X := by
  obtain ⟨X, hX⟩ := PowerlessBMSQuotientReals.trace_exists_l K ⟨SecondOrderQuotient.mk_l hℳ A, hA⟩
  exact ⟨X, (reading_l K A hA X).mpr hX, fun Y hY =>
    PowerlessBMSQuotientReals.trace_unique_l K ((reading_l K A hA Y).mp hY) hX⟩

theorem representative_l (K : source_coding_l hℳ) (X : SecondOrderModel.set_l ℳ) :
    ∃ A : SecondOrderGraph.code_l ℳ,
      ThirdOrderSemantics.subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ A) K.omega ∧
      trace_l K.less A.real A.root X := by
  obtain ⟨S, hS⟩ := representative_exists_l K X
  obtain ⟨A, hA⟩ := SecondOrderQuotient.surj_l hℳ S.val
  have hSubset := hA.symm ▸ S.property
  let T : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨SecondOrderQuotient.mk_l hℳ A, hSubset⟩
  have hTS : T = S := Subtype.ext hA
  have hT : setRel_l K T X := by
    rw [hTS]
    exact hS
  exact ⟨A, hSubset, (reading_l K A hSubset X).mpr hT⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRealTraceSyntax
