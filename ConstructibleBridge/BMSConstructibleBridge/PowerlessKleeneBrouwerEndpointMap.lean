import BMSConstructibleBridge.PowerlessKleeneBrouwerReachable
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation

/-! # 路径到实际可达末节点域的类内满射

纯隶属 ℒ，原 Z₂。末节点有实际内部有限坐标且唯一，Δ₀ 函数图构造给出
Class F:S→D；其原映射、满射与全部 raw 坐标读数同时成立。
不预供枚举或选择函数，不假定 S/D 属于遗传域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerEndpointMap

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerEndpoint (endpoint_l endpoint_m endpoint_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def reading_m {Γ Δ : SortContext ℒ} (ω I S D F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (PowerlessValueBounded.formula_m (up (up F)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up S))) <|
        .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up D)))
          (endpoint_m (up (up ω)) (up (up I)) (.bvar (.there .here)) (.bvar .here))

def onto_m {Γ Δ : SortContext ℒ} (S D F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall D <| membershipLevyBound.boundedExists (up S)
    (PowerlessValueBounded.formula_m (up (up F)) (.bvar .here) (.bvar (.there .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (ω I S D F : Raw) : Prop :=
  ∀ f a, value_l (ℳ := 𝒱) F f a ↔ mem_l hℳ f S ∧ mem_l hℳ a D ∧ endpoint_l ω I f a

def onto_l (S D F : Raw) : Prop :=
  ∀ a, mem_l hℳ a D → ∃ f, mem_l hℳ f S ∧ value_l (ℳ := 𝒱) F f a

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω I S D F : Term ℒ Γ Δ .set) :
    (reading_m ω I S D F).satisfies η ↔
      reading_l (ω.eval η) (I.eval η) (S.eval η) (D.eval η) (F.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    SecondOrderObjectSyntax.member_m, endpoint_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem onto_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (S D F : Term ℒ Γ Δ .set) :
    (onto_m S D F).satisfies η ↔ onto_l (S.eval η) (D.eval η) (F.eval η) := by
  simp only [onto_m, onto_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {B ω I A z r S D : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hSClass : PowerlessRelativeClassCorrespondence.member_l hℳ B S)
    (hDClass : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D) :
    ∃ F, PowerlessRelativeClassCorrespondence.member_l hℳ B F ∧
      map_l (ℳ := 𝒱) F S D ∧ onto_l S D F ∧ reading_l ω I S D F := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, hωClass⟩
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨I, hI⟩
  let S₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨S, hSClass⟩
  let D₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨D, hDClass⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set] := endpoint_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar .here) (.fvar (.there .here))
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set] :=
    Env.empty |>.pushFree I₀ |>.pushFree O
  have hδ : Formula.IsDelta0 membershipLevyBound φ := PowerlessKleeneBrouwerEndpoint.endpoint_delta_l _ _ _ _
  have hφ (f a : PowerlessRelativeClassStructure.type_l hℳ B) :
      φ.satisfies ((η.pushFree a).pushFree f) ↔ endpoint_l ω I f.val a.val :=
    (PowerlessRelativeClassBounded.formula_l hδ ((η.pushFree a).pushFree f)).trans
      (endpoint_formula_l (PowerlessRelativeClassRelativization.env_l ((η.pushFree a).pushFree f)) _ _ _ _)
  obtain ⟨F, hF, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l hδ η S₀ D₀ (by
    intro f hf
    obtain ⟨a, ha, hEnd⟩ := PowerlessKleeneBrouwerEndpoint.exists_l hω ((hS f.val).mp hf)
    let a₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hI ha⟩
    refine ⟨a₀, ⟨(hD a).mpr ⟨ha, f.val, hf, hEnd⟩, (hφ f a₀).mpr hEnd⟩, ?_⟩
    intro b hb
    exact Subtype.ext (PowerlessKleeneBrouwerEndpoint.unique_l ((hφ f b).mp hb.2) hEnd))
  have hMap := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F S₀ D₀).mp hF
  have hRead : reading_l ω I S D F.val := by
    intro f a
    constructor
    · intro hfa
      obtain ⟨hfS, haD⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hMap hfa
      let f₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
        ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hSClass hfS⟩
      let a₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
        ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hDClass haD⟩
      have hBody := ((hValue f₀ a₀).mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F f₀ a₀).mpr hfa)).2.2
      exact ⟨hfS, haD, (hφ f₀ a₀).mp hBody⟩
    · rintro ⟨hfS, haD, hEnd⟩
      let f₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
        ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hSClass hfS⟩
      let a₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
        ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hDClass haD⟩
      exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F f₀ a₀).mp
        ((hValue f₀ a₀).mpr ⟨hfS, haD, (hφ f₀ a₀).mpr hEnd⟩)
  refine ⟨F.val, F.property, hMap, ?_, hRead⟩
  intro a ha
  obtain ⟨_haI, f, hfS, hEnd⟩ := (hD a).mp ha
  exact ⟨f, hfS, (hRead f a).mpr ⟨hfS, ha, hEnd⟩⟩

def schema_m {Δ : SortContext ℒ} (B ω I A z r S D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B I) <| .imp (PowerlessRelativeHierarchySyntax.class_m B S) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
        .imp (PowerlessKleeneBrouwerPathClass.reading_m ω I A z r S) <|
          .imp (PowerlessKleeneBrouwerReachable.reading_m ω I S D) <|
            .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
              .conj (PowerlessMapBounded.formula_m (.bvar .here) (up S) (up D)) <|
                .conj (onto_m (up S) (up D) (.bvar .here))
                  (reading_m (up ω) (up I) (up S) (up D) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B ω I A z r S D : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r S D)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r S D : Term ℒ [] Δ .set) : (sentence_m B ω I A z r S D).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessKleeneBrouwerPathClass.reading_formula_l, PowerlessKleeneBrouwerReachable.reading_formula_l,
    PowerlessMapBounded.formula_l, onto_formula_l, reading_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r S D : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I A z r S D)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r S D)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerEndpointMap
