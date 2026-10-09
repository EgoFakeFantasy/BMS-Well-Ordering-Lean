import BMSConstructibleBridge.PowerlessRelationalCollapseExtension
import BMSConstructibleBridge.PowerlessRelativeClassLimitParameterBounds

/-! # 单点局部解的实际共同层界

纯隶属 ℒ，原 Z₂。新源与图已由实际单点扩展构造，有限参数共同
极限层界把 A/I/新源/新图置于同一层，并证明原关系局部递归规格。
这里真的构造层见证，不把成员界填入假设；仍未处理无限前驱族。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseExtensionBound

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def adjoin_m {Γ Δ : SortContext ℒ} (E x S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up S))
    (.disj (member_m (.bvar .here) (up E)) (.equal (.bvar .here) (up x)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : type_l hℳ}
  {hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B}

local notation "Raw" => type_l hℳ
local notation "Class" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "𝒩" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem restriction_l {A I T H S F D : Raw}
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hSub : ∀ a, mem_l hℳ a S → mem_l hℳ a I)
    (hClosed : ∀ a, mem_l hℳ a S → ∀ b, mem_l hℳ b I →
      SecondOrderFunctionObjects.value_l hℳ A b a → mem_l hℳ b S)
    (hF : SecondOrderFunctionObjects.map_l hℳ F S D)
    (hRead : ∀ a b, SecondOrderFunctionObjects.value_l hℳ F a b ↔
      mem_l hℳ a S ∧ SecondOrderFunctionObjects.value_l hℳ H a b) :
    PowerlessRelationalCollapsePartial.partial_l A I S D F := by
  refine ⟨hSub, hClosed, hF, ?_⟩
  intro a ha b _hab hFab z _hzD
  rw [hH.2.2.2 a b (hSub a ha) ((hRead a b).mp hFab).2 z]
  constructor
  · rintro ⟨c, hcI, hca, hcz⟩
    have hcS := hClosed a ha c hcI hca
    exact ⟨c, hcS, hca, (hRead c z).mpr ⟨hcS, hcz⟩⟩
  · rintro ⟨c, hcS, hca, hcz⟩
    exact ⟨c, hSub c hcS, hca, ((hRead c z).mp hcz).2⟩

def result_l (B A I E x : Raw) : Prop :=
  ∃ S F β D, PowerlessRelativeHierarchySemantics.limit_l hℳ β ∧
    PowerlessRelativeHierarchySemantics.level_l hℳ B β D ∧
      mem_l hℳ A D ∧ mem_l hℳ I D ∧ mem_l hℳ S D ∧ mem_l hℳ F D ∧
        PowerlessRelationalCollapsePartial.partial_l A I S D F ∧
          ∀ a, mem_l hℳ a S ↔ mem_l hℳ a E ∨ a = x

include hBase in
theorem exists_l {A I E T H C G x y : Raw}
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hE : PowerlessRelativeClassCorrespondence.member_l hℳ B E)
    (hGClass : PowerlessRelativeClassCorrespondence.member_l hℳ B G)
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E C G)
    (hCover : ∀ a, mem_l hℳ a I → SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E)
    (hxI : mem_l hℳ x I) (hxy : SecondOrderFunctionObjects.value_l hℳ H x y)
    (hNew : ¬mem_l hℳ x E) : result_l B A I E x := by
  obtain ⟨S, F, W, hSClass, hFClass, hWClass, hAdjoin, hF, hRead⟩ :=
    PowerlessRelationalCollapseExtension.exists_l (hBase := hBase)
      hA hE hGClass hx hC hH hG hCover hxI hxy hNew
  let A₀ : Class := ⟨A, hA⟩
  let I₀ : Class := ⟨I, hI⟩
  let S₀ : Class := ⟨S, hSClass⟩
  let F₀ : Class := ⟨F, hFClass⟩
  let W₀ : Class := ⟨W, hWClass⟩
  let η : Env 𝒩 [] [.set, .set, .set, .set] := Env.empty |>.pushFree A₀ |>.pushFree I₀ |>.pushFree S₀ |>.pushFree F₀
  obtain ⟨β, D, hLimit, hD, hWD, hParams⟩ := PowerlessRelativeClassLimitParameterBounds.exists_l η W₀
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hD
  have hSub (a : Raw) (ha : mem_l hℳ a S) : mem_l hℳ a I :=
    ((hAdjoin a).mp ha).elim (hG.1 a) (fun he => he.symm ▸ hxI)
  have hClosed (a : Raw) (ha : mem_l hℳ a S) (b : Raw) (hb : mem_l hℳ b I)
      (hba : SecondOrderFunctionObjects.value_l hℳ A b a) : mem_l hℳ b S := by
    apply (hAdjoin b).mpr
    apply Or.inl
    rcases (hAdjoin a).mp ha with haE | haX
    · exact hG.2.1 a haE b hb hba
    · exact hCover b hb (haX ▸ hba)
  have hFD : SecondOrderFunctionObjects.map_l hℳ F S D := by
    constructor
    · intro p hp
      obtain ⟨a, b, ha, hb, hab⟩ := hF.1 p hp
      exact ⟨a, b, ha, hTrans W hWD b hb, hab⟩
    · intro a ha
      obtain ⟨b, hb, _⟩ := hF.2 a ha
      exact ⟨b, ⟨hTrans W hWD b hb.1, hb.2⟩,
        fun z hz => SecondOrderFunctionProperties.value_unique_l hℳ hF hz.2 hb.2⟩
  exact ⟨S, F, β, D, hLimit, hD, hParams .set (.there (.there (.there .here))),
    hParams .set (.there (.there .here)), hParams .set (.there .here), hParams .set .here,
    restriction_l hH hSub hClosed hFD hRead, hAdjoin⟩

def result_m {Γ Δ : SortContext ℒ} (B A I E x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
    let S : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let F : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let β : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let D : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m (w B) β D) <|
        .conj (member_m (w A) D) <| .conj (member_m (w I) D) <|
          .conj (member_m S D) <| .conj (member_m F D) <|
            .conj (PowerlessRelationalCollapsePartial.partial_m (w A) (w I) S D F) (adjoin_m (w E) (w x) S)

theorem result_formula_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (B A I E x : Term ℒ Γ Δ .set) :
    (result_m B A I E x).satisfies η ↔ result_l (B.eval η) (A.eval η) (I.eval η) (E.eval η) (x.eval η) := by
  simp only [result_m, result_l, adjoin_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelationalCollapsePartial.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B E) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B x) <|
              .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
                .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
                  .imp (PowerlessRelationalCollapsePartial.partial_m A I E C G) <|
                    .imp (PowerlessRelationalCollapseOutput.covered_m A I E x) <| .imp (member_m x I) <|
                      .imp (SecondOrderObjectSyntax.value_m H x y) <|
                        .imp (.neg (member_m x E)) (result_m B A I E x)

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
  exact fun hBase hA hI hE hG hx hC hH hPartial hCover hxI hxy hNew =>
    exists_l (hBase := hBase) hA hI hE hG hx hC hH hPartial hCover hxI hxy hNew

theorem derives_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B A I E T H C G x y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B A I E T H C G x y)

#print axioms restriction_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseExtensionBound
