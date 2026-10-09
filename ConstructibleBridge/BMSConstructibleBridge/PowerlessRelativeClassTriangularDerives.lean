import BMSConstructibleBridge.PowerlessRelativeClassTriangular

/-! # 原三角递推图类内存在的对象推导

序列参数由已经证明的类内全有限序列公理实际构造，不留为隐藏前提。
结论保留原三角递推与原加法关系，而非仅给多项式图或另一个配数系统。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTriangularDerives

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (ω e T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  .conj (SecondOrderObjectSyntax.map_m T ω ω) <| .conj (SecondOrderObjectSyntax.value_m T e e) <|
    .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
      .imp (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (w ω)) <|
      .imp (PowerlessNaturalStep.successor_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))) <|
        .imp (SecondOrderObjectSyntax.value_m (w T) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))) <|
          .imp (SecondOrderObjectSyntax.value_m (w T) (.bvar (.there (.there .here))) (.bvar .here))
            (PowerlessAdditionSyntax.addition_m (w ω) (w e) (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here))

theorem body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e T : Term ℒ Γ Δ .set) :
    (body_m ω e T).satisfies η ↔ PowerlessTriangular.triangular_l (ℳ := 𝒩) (ω.eval η) (e.eval η) (T.eval η) := by
  simp only [body_m, PowerlessTriangular.triangular_l, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessNaturalStep.successor_formula_l, PowerlessAdditionSyntax.addition_formula_l,
    SecondOrderObjectSyntax.member_m, up, Term.eval_weakenBound, Arguments.eval, Term.eval]
  rfl

def sentence_m : Sentence ℒ := .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
  .forallE .set <| .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))) <|
    .existsE .set (body_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

theorem sentence_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} : sentence_m.TrueIn 𝒩 ↔
    ∀ ω : carrier_l 𝒩, omega_l (ℳ := 𝒩) ω → ∀ e, PowerlessNatural.zero_l (ℳ := 𝒩) e →
      ∃ T, PowerlessTriangular.triangular_l (ℳ := 𝒩) ω e T := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l, body_l,
    PowerlessNatural.zero_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  rfl

theorem exists_ambient_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {ω e : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e) :
    ∃ K : source_coding_l hℳ, ∃ T : type_l hℳ B,
      ω.val = K.omega ∧ e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
      PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T ∧
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega ∧
      ∀ i j : SecondOrderModel.num_l ℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val (numberCode_l K i).val (numberCode_l K j).val ↔
          SecondOrderTriangularArithmetic.relation_l i j := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have heEq := SecondOrderQuotient.ext_l hℳ _ _ (fun x => iff_of_false
    ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x)
    (PowerlessBMSQuotientSuccessor.zero_l K x))
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (hBase := hBase) (X := ω) hω
  rw [hωEq] at hS
  obtain ⟨T, hT, hSpec⟩ := PowerlessRelativeClassTriangular.exists_spec_l K ω e S hωEq heEq hS
  refine ⟨K, T, hωEq, heEq, hT, ?_, hSpec⟩
  simpa only [ThirdOrderSemantics.map_l, ThirdOrderSemantics.member_l, ThirdOrderSemantics.value_l,
    ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l, SecondOrderQuotient.structure_l,
    SecondOrderFunctionObjects.map_l, SecondOrderFunctionObjects.value_l,
    SecondOrderPairObjects.ordered_l, SecondOrderPairObjects.pair_l, hωEq]
    using (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) T ω ω).mp hT.1

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {ω e : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e) :
    ∃ T : type_l hℳ B, PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T := by
  obtain ⟨_, T, _, _, hT, _, _⟩ := exists_ambient_l (hBase := hBase) hω he
  exact ⟨T, hT⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) := by
  apply PowerlessRelativeClassRelativization.derives_m
  intro ℳ hℳ B hBase
  exact sentence_l.mpr (fun _ hω _ he => exists_l (hBase := hBase) hω he)

#print axioms exists_ambient_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTriangularDerives
