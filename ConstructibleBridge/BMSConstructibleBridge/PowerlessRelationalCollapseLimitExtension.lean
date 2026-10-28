import BMSConstructibleBridge.PowerlessRelationalCollapseLimitOutput
import BMSConstructibleBridge.PowerlessRelationalCollapseExtensionBound
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionExtension

/-! # 在指定极限层内扩展原关系坍缩

纯隶属 ℒ，原 Z₂。原源 E、局部图 G、A/x 属于指定非零极限层 L，
且 G 覆盖 x 的全部前驱时，在同一 L 内构造 S=E∪{x} 与扩展图 F。
F 在所有原坐标上仍恰为同一 H 的限制，满足原关系的局部递归规格。
后继预算不会因本步骤事后重选层；无限族的统一预算仍须另行构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseLimitExtension

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem adjoin_exists_l {B β L E x : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hL : PowerlessRelativeHierarchySemantics.level_l hℳ B β L)
    (hEL : mem_l hℳ E L) (hxL : mem_l hℳ x L) :
    ∃ S, mem_l hℳ S L ∧ ∀ a, mem_l hℳ a S ↔ mem_l hℳ a E ∨ a = x := by
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ x x
  have hPL := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hL hxL hxL hP
  obtain ⟨Q, hQ⟩ := SecondOrderPairObjects.pair_exists_l hℳ E P
  have hQL := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hL hEL hPL hQ
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : Raw, ∃ S, ∀ z, mem_l hℳ z S ↔ ∃ w, mem_l hℳ w a ∧ mem_l hℳ z w at hUnion
  obtain ⟨S, hS⟩ := hUnion Q
  refine ⟨S, PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hL hQL hS, fun a => ?_⟩
  rw [hS]
  constructor
  · rintro ⟨w, hw, haw⟩
    rcases (hQ w).mp hw with rfl | rfl
    · exact Or.inl haw
    · exact Or.inr (((hP a).mp haw).elim id id)
  · rintro (ha | ha)
    · exact ⟨E, (hQ E).mpr (Or.inl rfl), ha⟩
    · exact ⟨P, (hQ P).mpr (Or.inr rfl), (hP a).mpr (Or.inl ha)⟩

theorem exists_l {B β L A I E T H C G x y : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hL : PowerlessRelativeHierarchySemantics.level_l hℳ B β L)
    (hAL : mem_l hℳ A L) (hEL : mem_l hℳ E L)
    (hGL : mem_l hℳ G L) (hxL : mem_l hℳ x L)
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E C G)
    (hCover : ∀ a, mem_l hℳ a I → SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E)
    (hxI : mem_l hℳ x I) (hxy : SecondOrderFunctionObjects.value_l hℳ H x y)
    (hNew : ¬mem_l hℳ x E) :
    ∃ S F, mem_l hℳ S L ∧ mem_l hℳ F L ∧
      PowerlessRelationalCollapsePartial.partial_l A I S L F ∧
        ∀ a, mem_l hℳ a S ↔ mem_l hℳ a E ∨ a = x := by
  have hyL := PowerlessRelationalCollapseLimitOutput.output_l
    hBase hLimit hL hAL hEL hGL hxL hC hH hG hCover hxI hxy
  have hValue (a b : Raw) (hab : SecondOrderFunctionObjects.value_l hℳ G a b) : mem_l hℳ b L :=
    PowerlessRelativeLimitFunctionRange.value_member_l hBase hLimit hL
      hEL hGL (q := C) (by exact hG.2.2.1) (by exact hab)
  have hGLMap : SecondOrderFunctionObjects.map_l hℳ G E L := by
    constructor
    · intro p hp
      obtain ⟨a, b, ha, _, hab⟩ := hG.2.2.1.1 p hp
      exact ⟨a, b, ha, hValue a b ⟨p, hp, hab⟩, hab⟩
    · intro a ha
      obtain ⟨b, hb, _⟩ := hG.2.2.1.2 a ha
      exact ⟨b, ⟨hValue a b hb.2, hb.2⟩,
        fun z hz => SecondOrderFunctionProperties.value_unique_l hℳ hG.2.2.1 hz.2 hb.2⟩
  obtain ⟨S, hSL, hS⟩ := adjoin_exists_l hBase hLimit hL hEL hxL
  obtain ⟨F, hFL, hF, hFValue⟩ := PowerlessRelativeLimitFunctionExtension.exists_l hℳ
    hBase hLimit hL hGL hxL hyL hGLMap hNew hyL hS
  have hSub (a : Raw) (ha : mem_l hℳ a S) : mem_l hℳ a I :=
    ((hS a).mp ha).elim (hG.1 a) (fun he => he.symm ▸ hxI)
  have hClosed (a : Raw) (ha : mem_l hℳ a S) (b : Raw) (hb : mem_l hℳ b I)
      (hba : SecondOrderFunctionObjects.value_l hℳ A b a) : mem_l hℳ b S := by
    apply (hS b).mpr
    apply Or.inl
    rcases (hS a).mp ha with haE | haX
    · exact hG.2.1 a haE b hb hba
    · exact hCover b hb (haX ▸ hba)
  have hRead (a b : Raw) : SecondOrderFunctionObjects.value_l hℳ F a b ↔
      mem_l hℳ a S ∧ SecondOrderFunctionObjects.value_l hℳ H a b := by
    rw [hFValue a b]
    constructor
    · rintro (hab | ⟨haX, hbY⟩)
      · have haE := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 hab).1
        exact ⟨(hS a).mpr (Or.inl haE), (PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mp hab⟩
      · exact ⟨(hS a).mpr (Or.inr haX), haX.symm ▸ hbY.symm ▸ hxy⟩
    · rintro ⟨haS, hab⟩
      rcases (hS a).mp haS with haE | haX
      · exact Or.inl ((PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mpr hab)
      · exact Or.inr ⟨haX, SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 (haX ▸ hab) hxy⟩
  exact ⟨S, F, hSL, hFL,
    PowerlessRelationalCollapseExtensionBound.restriction_l hH hSub hClosed hF hRead, hS⟩

def result_m {Γ Δ : SortContext ℒ} (A I E x L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up t)
    let S : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let F : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    .conj (member_m S (w L)) <| .conj (member_m F (w L)) <|
      .conj (PowerlessRelationalCollapsePartial.partial_m (w A) (w I) S (w L) F)
        (PowerlessRelationalCollapseExtensionBound.adjoin_m (w E) (w x) S)

theorem result_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I E x L : Term ℒ Γ Δ .set) : (result_m A I E x L).satisfies η ↔
      ∃ S F, mem_l hℳ S (L.eval η) ∧ mem_l hℳ F (L.eval η) ∧
        PowerlessRelationalCollapsePartial.partial_l (A.eval η) (I.eval η) S (L.eval η) F ∧
          ∀ a, mem_l hℳ a S ↔ mem_l hℳ a (E.eval η) ∨ a = x.eval η := by
  simp only [result_m, PowerlessRelationalCollapseExtensionBound.adjoin_m, Formula.satisfies,
    PowerlessRelationalCollapsePartial.formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β L) <|
        .imp (member_m A L) <| .imp (member_m E L) <| .imp (member_m G L) <| .imp (member_m x L) <|
          .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
            .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
              .imp (PowerlessRelationalCollapsePartial.partial_m A I E C G) <|
                .imp (PowerlessRelationalCollapseOutput.covered_m A I E x) <| .imp (member_m x I) <|
                  .imp (SecondOrderObjectSyntax.value_m H x y) <| .imp (.neg (member_m x E))
                    (result_m A I E x L)

def sentence_m {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β L A I E T H C G x y)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) :
    (sentence_m B β L A I E T H C G x y).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, result_formula_l,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelationalCollapsePartial.formula_l, PowerlessRelationalCollapseOutput.covered_formula_l,
    SecondOrderObjectSyntax.value_l, member_m, Arguments.eval]
  exact fun hBase hLimit hL hA hE hG hx hC hH hPartial hCover hxI hxy hNew =>
    exists_l hBase hLimit hL hA hE hG hx hC hH hPartial hCover hxI hxy hNew

theorem derives_m {Δ : SortContext ℒ}
    (B β L A I E T H C G x y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β L A I E T H C G x y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β L A I E T H C G x y)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseLimitExtension
