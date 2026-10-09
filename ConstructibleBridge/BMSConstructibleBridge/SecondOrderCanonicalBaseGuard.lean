import BMSConstructibleBridge.SecondOrderEnumerationAmbientWellOrder
import BMSConstructibleBridge.SecondOrderMemberEnumerationDerives
import BMSConstructibleBridge.SecondOrderCanonicalLevelDerives
import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderSlices

/-! # 实际传递基集的完整初始良序守卫

先由内部 ω 枚举得到环境良序，再清理为精确 B×B 上的关系图。
最小元条款量化全部环境子集，不将类内良序误当环境良序。
同时返回原对象句的推导；不要求完整源理论或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalBaseGuard

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l guard_m guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Ambient" => SecondOrderQuotient.structure_l hℳ

theorem omega_l (K : source_coding_l hℳ) : ThirdOrderSemantics.omega_l (ℳ := Ambient) K.omega := by
  let η : Env Ambient [] [.set] := Env.empty.pushFree K.omega
  exact (ThirdOrderSemantics.omega_formula_l η (.fvar .here)).mp
    ((SecondOrderOmegaSyntax.omega_l hℳ η (.fvar .here)).mpr K.omega_spec)

theorem exists_l (K : source_coding_l hℳ) {B : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hB : ∃ x, mem_l hℳ x B) : ∃ P₀, guard_l B P₀ := by
  obtain ⟨G, hG, hOnto⟩ := SecondOrderMemberEnumerationDerives.exists_l
    hℳ K.omega B K.omega_spec hB
  have hMap : map_l (ℳ := Ambient) G K.omega B := by
    change SecondOrderFunctionObjects.map_l hℳ G K.omega B
    exact hG
  have hSurj : ∀ y, mem_l hℳ y B → ∃ i, mem_l hℳ i K.omega ∧
      value_l (ℳ := Ambient) G i y := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := hOnto y hy
    exact ⟨i, hi, hiy⟩
  obtain ⟨R, hR⟩ := SecondOrderEnumerationAmbientWellOrder.exists_l (hℳ := hℳ)
    (ω := K.omega) (G := G) (X := B) (omega_l K) hMap hSurj
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env Ambient [] [.set] := Env.empty.pushFree R
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔ value_l (ℳ := Ambient) R x y :=
    PowerlessValueBounded.formula_l _ _ _ _
  obtain ⟨P₀, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η B B
  have hRead p : mem_l hℳ p P₀ ↔ ∃ x y, mem_l hℳ x B ∧ mem_l hℳ y B ∧
      value_l (ℳ := Ambient) R x y ∧ SecondOrderPairObjects.ordered_l hℳ x y p :=
    (hP p).trans (exists_congr (fun x => exists_congr (fun y => and_congr Iff.rfl
      (and_congr Iff.rfl (and_congr (hφ x y) Iff.rfl)))))
  have hValue x y (hx : mem_l hℳ x B) (hy : mem_l hℳ y B) :
      value_l (ℳ := Ambient) P₀ x y ↔ value_l (ℳ := Ambient) R x y := by
    change SecondOrderFunctionObjects.value_l hℳ P₀ x y ↔
      SecondOrderFunctionObjects.value_l hℳ R x y
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨a, b, _, _, hab, hPair⟩ := (hRead p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hPair).mp rfl
      exact hab
    · intro hxy
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hRead p).mpr ⟨x, y, hx, hy, hxy, hp⟩, hp⟩
  refine ⟨P₀, hB, (fun x y hx hy => hBase x hx y hy), ?_, ?_⟩
  · exact PowerlessRelativeClassSequenceOrderSlices.wellOrder_congr_l hR
      (fun x hx y hy => (hValue x y hx hy).symm)
  · intro p hp
    obtain ⟨x, y, hx, hy, _, hxy⟩ := (hRead p).mp hp
    exact ⟨x, y, hx, hy, hxy⟩

def sentence_m : Sentence ℒ :=
  .forallE .set <| .imp (PowerlessRelativeHierarchyDerives.transitive_m (.bvar .here)) <|
    .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))) <|
      .existsE .set (guard_m (.bvar (.there .here)) (.bvar .here))

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval, guard_formula_l]
  intro B hBase hB
  exact exists_l K hBase hB

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalBaseGuard
