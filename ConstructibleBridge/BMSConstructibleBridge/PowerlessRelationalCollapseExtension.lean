import BMSConstructibleBridge.PowerlessRelationalCollapseOutput
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRangeExtension

/-! # 同一关系坍缩的类内局部解单点扩展

纯隶属 ℒ，原 Z₂。先在类内构造原值 y，再用实际单点图扩展 G。
新源恰为 E∪{x}，新图在全部 raw 坐标上恰为同一原 H 的限制；
原 T 无需类内身份。此步不替代无穷前驱族的共同预算构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseExtension

open Logic FirstOrder StabilityFrame ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def state_m {Γ Δ : SortContext ℒ} (E H x S F W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set <| .iff (member_m (.bvar .here) (up S))
    (.disj (member_m (.bvar .here) (up E)) (.equal (.bvar .here) (up x)))) <|
      .conj (SecondOrderObjectSyntax.map_m F S W) <| .forallE .set <| .forallE .set <|
        .iff (SecondOrderObjectSyntax.value_m (up (up F)) (.bvar (.there .here)) (.bvar .here))
          (.conj (member_m (.bvar (.there .here)) (up (up S)))
            (SecondOrderObjectSyntax.value_m (up (up H)) (.bvar (.there .here)) (.bvar .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : type_l hℳ}
  {hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B}

local notation "Raw" => type_l hℳ
local notation "Class" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "𝒩" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def state_l (E H x S F W : Raw) : Prop :=
  (∀ a, mem_l hℳ a S ↔ mem_l hℳ a E ∨ a = x) ∧
    SecondOrderFunctionObjects.map_l hℳ F S W ∧
      ∀ a b, SecondOrderFunctionObjects.value_l hℳ F a b ↔
        mem_l hℳ a S ∧ SecondOrderFunctionObjects.value_l hℳ H a b

theorem state_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (E H x S F W : Term ℒ Γ Δ .set) : (state_m E H x S F W).satisfies η ↔
      state_l (E.eval η) (H.eval η) (x.eval η) (S.eval η) (F.eval η) (W.eval η) := by
  simp only [state_m, state_l, Formula.satisfies, SecondOrderObjectSyntax.map_l,
    SecondOrderObjectSyntax.value_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

include hBase in
theorem exists_l {A I E T H C G x y : Raw}
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hE : PowerlessRelativeClassCorrespondence.member_l hℳ B E)
    (hGClass : PowerlessRelativeClassCorrespondence.member_l hℳ B G)
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E C G)
    (hCover : ∀ a, mem_l hℳ a I → SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E)
    (hxI : mem_l hℳ x I) (hxy : SecondOrderFunctionObjects.value_l hℳ H x y)
    (hNew : ¬mem_l hℳ x E) :
    ∃ S F W, PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B F ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B W ∧ state_l E H x S F W := by
  let E₀ : Class := ⟨E, hE⟩
  let G₀ : Class := ⟨G, hGClass⟩
  let x₀ : Class := ⟨x, hx⟩
  let y₀ : Class := ⟨y, PowerlessRelationalCollapseOutput.output_l (hBase := hBase)
    hA hE hGClass hx hC hH hG hCover hxI hxy⟩
  obtain ⟨R, hR⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase E₀ G₀ (q := C) (by exact hG.2.2.1)
  have hGR : SecondOrderFunctionObjects.map_l hℳ G E R.val := by
    constructor
    · intro p hp
      obtain ⟨a, b, ha, _, hab⟩ := hG.2.2.1.1 p hp
      exact ⟨a, b, ha, (hR b).mpr ⟨a, ⟨p, hp, hab⟩⟩, hab⟩
    · intro a ha
      obtain ⟨b, hb, _⟩ := hG.2.2.1.2 a ha
      exact ⟨b, ⟨(hR b).mpr ⟨a, hb.2⟩, hb.2⟩,
        fun z hz => SecondOrderFunctionProperties.value_unique_l hℳ hG.2.2.1 hz.2 hb.2⟩
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ x x
  let P₀ : Class := ⟨P, PowerlessRelativeClassPair.pair_l hℳ hBase hx hx hP⟩
  obtain ⟨S, hUnion⟩ := PowerlessRelativeClassBinaryUnion.exists_l (hBase := hBase) E₀ P₀
  have hS (a : Class) : mem_l hℳ a.val S.val ↔ mem_l hℳ a.val E ∨ a = x₀ := by
    refine (hUnion a).trans ⟨?_, ?_⟩
    · rintro (ha | ha)
      · exact Or.inl ha
      · exact Or.inr (Subtype.ext (((hP a.val).mp ha).elim id id))
    · rintro (ha | ha)
      · exact Or.inl ha
      · exact Or.inr ((hP a.val).mpr (Or.inl (congrArg Subtype.val ha)))
  obtain ⟨W, F, _, hF, hRead⟩ := PowerlessRelativeClassFunctionRangeExtension.exists_l
    (c := x₀) (d := y₀)
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G₀ E₀ R).mpr hGR)
    hNew hS
  have hSRaw (a : Raw) : mem_l hℳ a S.val ↔ mem_l hℳ a E ∨ a = x := by
    constructor
    · intro ha
      let a₀ : Class := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property ha⟩
      exact ((hS a₀).mp ha).elim Or.inl (fun he => Or.inr (congrArg Subtype.val he))
    · rintro (ha | rfl)
      · let a₀ : Class := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase E₀.property ha⟩
        exact (hS a₀).mpr (Or.inl ha)
      · exact (hS x₀).mpr (Or.inr rfl)
  have hFRaw (a b : Raw) : SecondOrderFunctionObjects.value_l hℳ F.val a b ↔
      SecondOrderFunctionObjects.value_l hℳ G a b ∨ a = x ∧ b = y := by
    constructor
    · intro hab
      obtain ⟨ha, hb⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase F hab
      let a₀ : Class := ⟨a, ha⟩
      let b₀ : Class := ⟨b, hb⟩
      rcases (hRead a₀ b₀).mp ((PowerlessRelativeClassFunctionAbsolute.value_l F a₀ b₀).mpr hab) with hOld | hNew
      · exact Or.inl ((PowerlessRelativeClassFunctionAbsolute.value_l G₀ a₀ b₀).mp hOld)
      · exact Or.inr ⟨congrArg Subtype.val hNew.1, congrArg Subtype.val hNew.2⟩
    · rintro (hab | ⟨haX, hbY⟩)
      · obtain ⟨ha, hb⟩ := PowerlessRelativeClassValueCoordinates.value_l hBase G₀ hab
        let a₀ : Class := ⟨a, ha⟩
        let b₀ : Class := ⟨b, hb⟩
        exact (PowerlessRelativeClassFunctionAbsolute.value_l F a₀ b₀).mp
          ((hRead a₀ b₀).mpr (Or.inl ((PowerlessRelativeClassFunctionAbsolute.value_l G₀ a₀ b₀).mpr hab)))
      · have hNewValue := (PowerlessRelativeClassFunctionAbsolute.value_l F x₀ y₀).mp
          ((hRead x₀ y₀).mpr (Or.inr ⟨rfl, rfl⟩))
        exact haX.symm ▸ hbY.symm ▸ hNewValue
  refine ⟨S.val, F.val, W.val, S.property, F.property, W.property,
    hSRaw, (PowerlessRelativeClassFunctionAbsolute.map_l F S W).mp hF, fun a b => ?_⟩
  rw [hFRaw a b]
  constructor
  · rintro (hab | ⟨haX, hbY⟩)
    · have haE := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 hab).1
      exact ⟨(hSRaw a).mpr (Or.inl haE), (PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mp hab⟩
    · exact ⟨(hSRaw a).mpr (Or.inr haX), haX.symm ▸ hbY.symm ▸ hxy⟩
  · rintro ⟨haS, hab⟩
    rcases (hSRaw a).mp haS with haE | haX
    · exact Or.inl ((PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mpr hab)
    · exact Or.inr ⟨haX, SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 (haX ▸ hab) hxy⟩

def result_m {Γ Δ : SortContext ℒ} (B E H x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up t))
    let S : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let F : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let W : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (w B) S) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (w B) F) <|
        .conj (PowerlessRelativeHierarchySyntax.class_m (w B) W) (state_m (w E) (w H) (w x) S F W)

theorem result_formula_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (B E H x : Term ℒ Γ Δ .set) :
    (result_m B E H x).satisfies η ↔ ∃ S F W,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) S ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) F ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) W ∧
        state_l (E.eval η) (H.eval η) (x.eval η) S F W := by
  simp only [result_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    state_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B E) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B x) <|
            .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
              .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
                .imp (PowerlessRelationalCollapsePartial.partial_m A I E C G) <|
                  .imp (PowerlessRelationalCollapseOutput.covered_m A I E x) <| .imp (member_m x I) <|
                    .imp (SecondOrderObjectSyntax.value_m H x y) <| .imp (.neg (member_m x E)) (result_m B E H x)

def sentence_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B A I E T H C G x y)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B A I E T H C G x y : Term ℒ [] Δ .set) : (sentence_m B A I E T H C G x y).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, result_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelationalCollapsePartial.formula_l, PowerlessRelationalCollapseOutput.covered_formula_l,
    SecondOrderObjectSyntax.value_l, member_m, Arguments.eval]
  exact fun hBase hA hE hG hx hC hH hPartial hCover hxI hxy hNew =>
    exists_l (hBase := hBase) hA hE hG hx hC hH hPartial hCover hxI hxy hNew

theorem derives_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B A I E T H C G x y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B A I E T H C G x y)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseExtension
