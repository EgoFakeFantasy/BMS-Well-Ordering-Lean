import BMSConstructibleBridge.SecondOrderCanonicalBaseGuard

/-! # 给定实际 Class 基底枚举的 Class 环境初始良序

同一实际相对 Class 内构造最小编号单射，拉回内部 ω 的环境良序，然后
清理为精确基底有序对关系图。任意 raw 子集的最小元由原完整分离证明，
不只证明类内良序；既有 Class 枚举是明确输入，不把 raw 枚举升级 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAmbientBaseGuard

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (G : type_l hℳ B) (hG : map_l (ℳ := 𝒱) G.val K.omega B)
    (hOnto : ∀ y, mem_l hℳ y B → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) G.val i y)
    (hB : ∃ b, mem_l hℳ b B) :
    ∃ P₀ : type_l hℳ B, SecondOrderCanonicalLevelDerives.guard_l B P₀.val := by
  let ω : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let B' : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let 𝒩 := structure_l hℳ B hBase
  have hω : omega_l (ℳ := 𝒩) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr K.omega_spec
  have hMap : map_l (ℳ := 𝒩) G ω B' :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G ω B').mpr hG
  have hSurj : ∀ y : type_l hℳ B, mem_l hℳ y.val B →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) G i y :=
    (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) G ω B').mpr hOnto
  obtain ⟨J, hJ, hSection⟩ := PowerlessRelativeClassEnumerationSection.exists_l
    (G := G) (X := B') hω hSurj
  have hInject : injective_l (ℳ := 𝒩) J := by
    intro x y i hxi hyi
    exact PowerlessRelativeClassFunctionProperties.value_unique_l hMap
      ((hSection x i).mp hxi).2.2.1 ((hSection y i).mp hyi).2.2.1
  obtain ⟨N, _hNClassOrder, hN⟩ := PowerlessRelativeClassOmegaWellOrder.exists_l hω
  obtain ⟨R, hR, _hReadR⟩ := PowerlessRelativeClassWellOrderPullbackAmbient.exists_l
    hJ hInject (PowerlessRelativeClassOmegaAmbientOrder.of_comparison_l hω hN)
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set] := Env.empty.pushFree R
  obtain ⟨P₀, hP₀⟩ := PowerlessRelativeClassRelation.exists_l
    (φ := φ) (PowerlessValueBounded.delta_l _ _ _) η B' B'
  have hRead (p : type_l hℳ B) : mem_l hℳ p.val P₀.val ↔ ∃ x y : type_l hℳ B,
      mem_l hℳ x.val B ∧ mem_l hℳ y.val B ∧ ordered_l (ℳ := 𝒩) x y p ∧
        value_l (ℳ := 𝒩) R x y := by
    exact (hP₀ p).trans (exists_congr (fun x => exists_congr (fun y =>
      and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
        (PowerlessValueBounded.formula_l ((η.pushFree y).pushFree x) _ _ _))))))
  have hClean p (hp : mem_l hℳ p P₀.val) : ∃ x y,
      mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
    let p' : type_l hℳ B := ⟨p,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P₀.property hp⟩
    obtain ⟨x, y, hx, hy, hPair, _hValue⟩ := (hRead p').mp hp
    exact ⟨x.val, y.val, hx, hy,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p').mp hPair⟩
  have hValue x y (hx : mem_l hℳ x B) (hy : mem_l hℳ y B) :
      value_l (ℳ := 𝒱) P₀.val x y ↔ value_l (ℳ := 𝒱) R.val x y := by
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hy⟩
    constructor
    · rintro ⟨p, hp, hxy⟩
      let p' : type_l hℳ B := ⟨p,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase P₀.property hp⟩
      obtain ⟨a, b, _ha, _hb, hPair, hab⟩ := (hRead p').mp hp
      obtain ⟨hxa, hyb⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy
        ((PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) a b p').mp hPair)).mp rfl
      exact hxa.symm ▸ hyb.symm ▸
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R a b).mp hab)
    · intro hxy
      obtain ⟨p, hPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase
        x'.property y'.property hPair⟩
      exact ⟨p, (hRead p').mpr ⟨x', y', hx, hy,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x' y' p').mpr hPair,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R x' y').mpr hxy⟩, hPair⟩
  exact ⟨P₀, hB, (fun x y hx hy => hBase x hx y hy),
    PowerlessRelativeClassSequenceOrderSlices.wellOrder_congr_l hR
      (fun x hx y hy => (hValue x y hx hy).symm), hClean⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let G : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let ω := .fvar (.there .here)
  let B := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (up B))) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
          .imp (SecondOrderObjectSyntax.map_m G ω B) <|
            .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω B) <|
              .existsE .set <|
                .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
                  (SecondOrderCanonicalLevelDerives.guard_m (up B) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    SecondOrderCanonicalLevelDerives.guard_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hB hω hGClass hMap hOnto
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  obtain ⟨P₀, hP₀⟩ := exists_l K hBase ⟨_, hGClass⟩ (hωEq ▸ hMap) (hωEq ▸ hOnto) hB
  exact ⟨P₀.val, P₀.property, hP₀⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAmbientBaseGuard
