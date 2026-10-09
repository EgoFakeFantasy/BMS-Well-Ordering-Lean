import BMSConstructibleBridge.PowerlessRelativeCutoffCollectionStages
import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure

/-! # 实际类内序数函数的精确值域之并

纯隶属 ℒ、原 Z₂。已有实际 G:ω→Ω 时，在证明内生成精确值域 C
及 δ=⋃C；C 可数，δ 属于 Class、是序数且 δ⊆Ω。
没有把 C 的可数性传给 δ，也没有把 δ⊆Ω 写成 δ∈Ω。
这给共同阶段界留下一个明确的原对象义务，而非预供一个较小界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalRangeUnion

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def union_m {Γ Δ : SortContext ℒ} (C δ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up δ)) <|
    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ C))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

theorem union_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (C δ : Term ℒ Γ Δ .set) :
    (union_m C δ).satisfies η ↔ ∀ x, mem_l hℳ x (δ.eval η) ↔
      ∃ a, mem_l hℳ a (C.eval η) ∧ mem_l hℳ x a := by
  simp only [union_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 值域与其并集都真正构造；这里只得非严格的 Ω 界。 -/
theorem exists_l (K : source_coding_l hℳ) {B ω Ω : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : Ordinal Ω)
    (G : PowerlessRelativeClassStructure.type_l hℳ B) (hG : map_l (ℳ := 𝒱) G.val ω Ω) :
    ∃ C δ : PowerlessRelativeClassStructure.type_l hℳ B,
      PowerlessRelativeOrdinalCutoff.countable_l B ω C.val ∧
        (∀ a, mem_l hℳ a C.val ↔ ∃ x, value_l (ℳ := 𝒱) G.val x a) ∧
          (∀ x, mem_l hℳ x δ.val ↔ ∃ a, mem_l hℳ a C.val ∧ mem_l hℳ x a) ∧
            Ordinal δ.val ∧ ∀ x, mem_l hℳ x δ.val → mem_l hℳ x Ω := by
  obtain ⟨C, hCount, hRange⟩ := PowerlessRelativeCutoffWitnessStageGraph.range_l K hBase hω G hG
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ C : Raw, ∃ δ : Raw, ∀ x, mem_l hℳ x δ ↔
    ∃ a, mem_l hℳ a C ∧ mem_l hℳ x a at hUnion
  obtain ⟨δ, hδ⟩ := hUnion C.val
  have hCΩ (a : Raw) (ha : mem_l hℳ a C.val) : mem_l hℳ a Ω := by
    obtain ⟨x, hxa⟩ := (hRange a).mp ha
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hG hxa).2
  have hSub (x : Raw) (hx : mem_l hℳ x δ) : mem_l hℳ x Ω := by
    obtain ⟨a, ha, hxa⟩ := (hδ x).mp hx
    exact hΩ.transitive a (hCΩ a ha) x hxa
  have hMembers (x : Raw) (hx : mem_l hℳ x Ω) : Ordinal x := by
    apply SetTheory.Structure.IsOrdinal.mem hΩ
    exact hx
  have hOrd : Ordinal δ := SecondOrderOrdinalBounded.of_transitive_l hℳ
    (fun x hx y hy => by
      obtain ⟨a, ha, hxa⟩ := (hδ x).mp hx
      exact (hδ y).mpr ⟨a, ha, (hMembers a (hCΩ a ha)).transitive x hxa y hy⟩)
    (fun x hx y hy z hz => (hMembers x (hSub x hx)).transitive y hy z hz)
    (fun x y hx hy => by
      rcases SecondOrderOrdinalComparison.compare_l hℳ
        (hMembers x (hSub x hx)) (hMembers y (hSub y hy)) with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h))
  exact ⟨C, ⟨δ, PowerlessRelativeClassBasicClosure.union_l hℳ hBase C.property hδ⟩,
    hCount, hRange, hδ, hOrd, hSub⟩

def conclusion_m {Γ Δ : SortContext ℒ} (B ω Ω G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    let C := .bvar (.there .here)
    let δ := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) C) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) δ) <|
        .conj (PowerlessRelativeOrdinalCutoff.countable_m (up₂ B) (up₂ ω) C) <|
          .conj (PowerlessRelativeCutoffCollectionStages.range_m (up₂ G) C) <|
            .conj (union_m C δ) <|
              .conj (PowerlessRelativeHierarchySyntax.ordinal_m δ) (ThirdOrderTheory.subset_m δ (up₂ Ω))

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  let G := .fvar (.there (.there (.there .here)))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.ordinal_m Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
          .imp (SecondOrderObjectSyntax.map_m G ω Ω) (conclusion_m B ω Ω G)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderObjectSyntax.map_l h𝒩]
  intro η hBase hω hΩ hClass hG
  obtain ⟨C, δ, hCount, hRange, hUnion, hδ, hSub⟩ := exists_l K hBase hω hΩ ⟨_, hClass⟩ hG
  simp only [conclusion_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, PowerlessRelativeCutoffCollectionStages.range_formula_l,
    union_formula_l, PowerlessRelativeHierarchySemantics.ordinal_formula_l, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l, up₂, up, Term.eval_weakenBound, Term.eval]
  exact ⟨C.val, δ.val, C.property, δ.property, hCount, hRange, hUnion, hδ, hSub⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalRangeUnion
