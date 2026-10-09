import BMSConstructibleBridge.SecondOrderFiniteAdditionEndpoint
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation

/-! # 相对类内的内部倍数图

同一极限层界定全部有限加法轨迹，使 n↦n+n 的图成为有界关系图。
这里的 n 是模型内部自然数；未调用完整源模型或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDoubling

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let n : Term ℒ [.set] [.set, .set, .set, .set, .set] .set := .fvar .here
  let y : Term ℒ [.set] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let ω : Term ℒ [.set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let e : Term ℒ [.set] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  membershipLevyBound.boundedExists (.fvar (.there (.there .here))) <| .conj
    (PowerlessAdditionTraceBounded.formula_m ω e n n (.bvar .here))
    (PowerlessValueBounded.formula_m (.bvar .here) n y)

theorem delta_l : Formula.IsDelta0 membershipLevyBound formula_m :=
  .bounded_exists _ (.conj (PowerlessAdditionTraceBounded.delta_l _ _ _ _ _)
    (PowerlessValueBounded.delta_l _ _ _))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (C ω e n y : 𝒩.Carrier .set) :
    formula_m.satisfies (((((Env.empty (M := 𝒩)).pushFree e).pushFree ω).pushFree C).pushFree y |>.pushFree n) ↔
      ∃ g, member_l 𝒩 g C ∧ PowerlessAdditionTraceBounded.trace_l (𝒩 := 𝒩) ω e n n g ∧
        value_l (ℳ := 𝒩) g n y := by
  simp only [formula_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessAdditionTraceBounded.formula_l, PowerlessValueBounded.formula_l, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

theorem exists_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {β C : SecondOrderQuotient.type_l hℳ}
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β) (hωC : mem_l hℳ K.omega C) :
    ∃ F : type_l hℳ B, ∃ ω : type_l hℳ B, ω.val = K.omega ∧
      map_l (ℳ := structure_l hℳ B hBase) F ω ω ∧
      ∀ i : SecondOrderModel.num_l ℳ,
        SecondOrderFunctionObjects.value_l hℳ F.val (numberCode_l K i).val
          (numberCode_l K (SecondOrderModel.add_l i i)).val := by
  have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hC
  have hωClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hωC
  let C' : type_l hℳ B := ⟨C, hCClass⟩
  let ω : type_l hℳ B := ⟨K.omega, hωClass⟩
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    ((Env.empty.pushFree e).pushFree ω).pushFree C'
  have hRead (n y : type_l hℳ B) : formula_m.satisfies ((η.pushFree y).pushFree n) ↔
      ∃ g, mem_l hℳ g C ∧ PowerlessAdditionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega e.val n.val n.val g ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g n.val y.val := by
    have hAbs := PowerlessRelativeClassBounded.formula_l (hBase := hBase) delta_l ((η.pushFree y).pushFree n)
    let η' : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set] :=
      ((((Env.empty.pushFree e.val).pushFree K.omega).pushFree C).pushFree y.val).pushFree n.val
    have hη : PowerlessRelativeClassRelativization.env_l
        ((η.pushFree (sort := SetTheory.SetSort.set) y).pushFree (sort := SetTheory.SetSort.set) n) =
        η' := by
      apply Env.ext
      · intro s v; nomatch v
      · intro s v
        match s, v with
        | .set, .here => rfl
        | .set, .there .here => rfl
        | .set, .there (.there .here) => rfl
        | .set, .there (.there (.there .here)) => rfl
        | .set, .there (.there (.there (.there .here))) => rfl
    rw [hη] at hAbs
    exact hAbs.trans
      (formula_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C K.omega e.val n.val y.val)
  have hEnd (n y : type_l hℳ B) {i : SecondOrderModel.num_l ℳ}
      (hi : n.val = (numberCode_l K i).val)
      (hφ : formula_m.satisfies ((η.pushFree y).pushFree n)) :
      y.val = (numberCode_l K (SecondOrderModel.add_l i i)).val := by
    obtain ⟨g, _, hg, hy⟩ := (hRead n y).mp hφ
    have hg' := (PowerlessRelativeClassFiniteTraceAbsolute.ambient_equiv_l K.omega_spec
      (hi.symm ▸ (numberCode_l K i).property)).mp hg
    rw [hi] at hg' hy
    exact SecondOrderFiniteAdditionEndpoint.value_l K hg' hy
  have hTotal (n : type_l hℳ B) (hn : mem_l hℳ n.val ω.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val ω.val ∧ formula_m.satisfies ((η.pushFree y).pushFree n) := by
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hn⟩
    have hi' : n.val = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
    obtain ⟨g, hgC, hg⟩ := PowerlessRelativeLimitFiniteAdditionDerives.exists_l hBase hC hLimit
      K.omega_spec (PowerlessBMSQuotientSuccessor.zero_l K) hn hωC n.val hn
    have hg' := (PowerlessRelativeClassFiniteTraceAbsolute.ambient_equiv_l K.omega_spec hn).mp hg
    obtain ⟨T, hT, hMap, _, _⟩ := hg'
    obtain ⟨z, hz, _⟩ := hMap.2 n.val ((hT n.val).mpr (Or.inr rfl))
    let y : type_l hℳ B := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass hz.1⟩
    have hyφ := (hRead n y).mpr ⟨g, hgC, hg, hz.2⟩
    refine ⟨y, ⟨hz.1, hyφ⟩, fun v hv => Subtype.ext ?_⟩
    exact (hEnd n v hi' hv.2).trans (hEnd n y hi' hyφ).symm
  obtain ⟨F, hMap, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l delta_l η ω ω hTotal
  refine ⟨F, ω, rfl, hMap, fun i => ?_⟩
  let n : type_l hℳ B := ⟨(numberCode_l K i).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass (numberCode_l K i).property⟩
  obtain ⟨y, hy, _⟩ := hTotal n (numberCode_l K i).property
  have hNy := (hValue n y).mpr ⟨(numberCode_l K i).property, hy⟩
  have hEq := hEnd n y rfl hy.2
  have hNy' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F n y).mp hNy
  exact hEq ▸ hNy'

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDoubling
