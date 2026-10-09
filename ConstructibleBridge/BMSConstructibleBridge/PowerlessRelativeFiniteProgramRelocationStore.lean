import BMSConstructibleBridge.PowerlessRelativeFiniteProgramRelocationComputed
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStore

/-! # 父坐标平移与实际存储更新相容

已有读数逐父坐标对应时，两条对应指令计算同一实际值，精确单点
更新后继续对应。坐标图的单射性是明确前提，后续由内部加法图消去；
不是预设整段执行相等，也不选择一个 Type 层的重编号函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocationStore

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (injective_m)
open PowerlessRelativeFiniteProgramRelocationComputed (reading_m reading_l reading_formula_l)
open PowerlessRelativeFiniteProgramStore (store_m store_l store_formula_l)
open PowerlessRelativeFiniteProgramInstruction (functional_m functional_l tags_m)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem append_reading_l {A ω f g j i y f' g' : type_l hℳ}
    (hA : map_l (ℳ := 𝒱) A ω ω) (hInjective : injective_l (ℳ := 𝒱) A)
    (hji : value_l (ℳ := 𝒱) A j i) (hRead : reading_l A f g)
    (hF : ∀ k x, value_l (ℳ := 𝒱) f' k x ↔ value_l (ℳ := 𝒱) f k x ∨ k = j ∧ x = y)
    (hG : ∀ k x, value_l (ℳ := 𝒱) g' k x ↔ value_l (ℳ := 𝒱) g k x ∨ k = i ∧ x = y) :
    reading_l A f' g' := by
  intro k l hkl x
  have hEq : k = j ↔ l = i := by
    constructor
    · intro hkj
      subst k
      exact SecondOrderFunctionProperties.value_unique_l hℳ hA hkl hji
    · intro hli
      subst l
      exact hInjective k j i hkl hji
  exact (hF k x).trans ((or_congr (hRead k l hkl x) (and_congr hEq Iff.rfl)).trans (hG l x).symm)

theorem stores_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C ω A D E f g j i t₀ t₁ t₂ q r S D' f' T E' g' : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f j D) (hA : map_l (ℳ := 𝒱) A ω ω)
    (hInjective : injective_l (ℳ := 𝒱) A) (hji : value_l (ℳ := 𝒱) A j i)
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) (hFunctional : functional_l φ η B)
    (hRelocation : PowerlessRelativeFiniteProgramRelocation.relation_l C ω A t₀ t₁ t₂ q r)
    (hRead : reading_l A f g)
    (hF : store_l φ η B C j D f j t₀ t₁ t₂ q S D' f')
    (hG : store_l φ η B C i E g i t₀ t₁ t₂ r T E' g') : reading_l A f' g' := by
  obtain ⟨y, hy, _, _, _, _, _, _, hFRead⟩ := hF
  obtain ⟨z, hz, _, _, _, _, _, _, hGRead⟩ := hG
  have hzOld := (PowerlessRelativeFiniteProgramRelocationComputed.computed_congr_l
    φ η hTags hRelocation hRead z).mpr hz
  obtain ⟨v, _, hv⟩ := PowerlessRelativeFiniteProgramInstruction.exists_unique_l
    φ η hBase hC hD hf hTags hFunctional q
  have hyz := (hv y hy).trans (hv z hzOld).symm
  subst z
  exact append_reading_l hA hInjective hji hRead hFRead hGRead

def result_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D E f g j i t₀ t₁ t₂ q r : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      let S : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let D' := .bvar (.there (.there (.there (.there .here))))
      let f' := .bvar (.there (.there (.there .here)))
      let T := .bvar (.there (.there .here))
      let E' := .bvar (.there .here)
      let g' := .bvar .here
      .imp (store_m φ (up₆ B) (up₆ C) (up₆ j) (up₆ D) (up₆ f) (up₆ j)
        (up₆ t₀) (up₆ t₁) (up₆ t₂) (up₆ q) S D' f') <|
        .imp (store_m φ (up₆ B) (up₆ C) (up₆ i) (up₆ E) (up₆ g) (up₆ i)
          (up₆ t₀) (up₆ t₁) (up₆ t₂) (up₆ r) T E' g') (reading_m (up₆ A) f' g')

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω A D E f g j i t₀ t₁ t₂ q r : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
        .imp (SecondOrderObjectSyntax.map_m f j D) <|
          .imp (SecondOrderObjectSyntax.map_m A ω ω) <| .imp (injective_m A) <|
            .imp (SecondOrderObjectSyntax.value_m A j i) <| .imp (tags_m t₀ t₁ t₂) <|
              .imp (functional_m φ B) <|
                .imp (PowerlessRelativeFiniteProgramRelocation.formula_m C ω A t₀ t₁ t₂ q r) <|
                  .imp (reading_m A f g) (result_m φ B C A D E f g j i t₀ t₁ t₂ q r)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω A D E f g j i t₀ t₁ t₂ q r : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω A D E f g j i t₀ t₁ t₂ q r)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C ω A D E f g j i t₀ t₁ t₂ q r : Term ℒ [] Δ .set) :
    (sentence_m φ B C ω A D E f g j i t₀ t₁ t₂ q r).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, result_m, tags_m, functional_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l, value_formula_l,
    injective_formula_l, PowerlessRelativeFiniteProgramRelocation.formula_l, reading_formula_l,
    store_formula_l K, PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    parameters_pushBound_l, parameters_empty_l, up₆, up₃, up₂, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hD hf hA hInjective hji hTags hFunctional hRelocation hRead S D' f' T E' g' hF hG
  exact stores_l φ η hBase hC hD hf hA hInjective hji hTags hFunctional hRelocation hRead hF hG

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω A D E f g j i t₀ t₁ t₂ q r : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω A D E f g j i t₀ t₁ t₂ q r)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω A D E f g j i t₀ t₁ t₂ q r)

#print axioms stores_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocationStore
