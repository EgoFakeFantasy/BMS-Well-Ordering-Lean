import BMSConstructibleBridge.PowerlessRelationalCollapsePartial
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRange
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation

/-! # 已覆盖前驱的实际坍缩值在类内构造

纯隶属 ℒ，原 Z₂。局部图 G 已在类内且覆盖 x 的全部源前驱时，
原递归值 y 是 G 的精确实际值域上的有界切片。全图 H 和未知 T
不进入类内分离的参数环境，不假定 y 已有资格或完整 Collection。
这是局部预算的单步构造，不证明全部局部解的共同界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOutput

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (A E G x z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists E <| .conj
    (PowerlessValueBounded.formula_m (up A) (.bvar .here) (up x))
    (PowerlessValueBounded.formula_m (up G) (.bvar .here) (up z))

theorem body_delta_m {Γ Δ : SortContext ℒ} (A E G x z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m A E G x z) :=
  .bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _))

def covered_m {Γ Δ : SortContext ℒ} (A I E x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall I <| .imp
    (PowerlessValueBounded.formula_m (up A) (.bvar .here) (up x)) (member_m (.bvar .here) (up E))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : type_l hℳ}
  {hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B}

local notation "Raw" => type_l hℳ
local notation "Class" => PowerlessRelativeClassStructure.type_l hℳ B
local notation "𝒩" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem body_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A E G x z : Term ℒ Γ Δ .set) : (body_m A E G x z).satisfies η ↔
      ∃ a, mem_l hℳ a (E.eval η) ∧
        SecondOrderFunctionObjects.value_l hℳ (A.eval η) a (x.eval η) ∧
        SecondOrderFunctionObjects.value_l hℳ (G.eval η) a (z.eval η) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem covered_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (A I E x : Term ℒ Γ Δ .set) : (covered_m A I E x).satisfies η ↔
      ∀ a, mem_l hℳ a (I.eval η) →
        SecondOrderFunctionObjects.value_l hℳ (A.eval η) a (x.eval η) → mem_l hℳ a (E.eval η) := by
  simp only [covered_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

include hBase in
theorem output_l {A I E T H C G x y : Raw}
    (hAClass : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hEClass : PowerlessRelativeClassCorrespondence.member_l hℳ B E)
    (hGClass : PowerlessRelativeClassCorrespondence.member_l hℳ B G)
    (hxClass : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E C G)
    (hCover : ∀ a, mem_l hℳ a I → SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E)
    (hxI : mem_l hℳ x I) (hxy : SecondOrderFunctionObjects.value_l hℳ H x y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  let A₀ : Class := ⟨A, hAClass⟩
  let E₀ : Class := ⟨E, hEClass⟩
  let G₀ : Class := ⟨G, hGClass⟩
  let x₀ : Class := ⟨x, hxClass⟩
  obtain ⟨R, hR⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase E₀ G₀ (q := C) (by exact hG.2.2.1)
  let η : Env 𝒩 [] [.set, .set, .set, .set] := Env.empty |>.pushFree A₀ |>.pushFree G₀ |>.pushFree E₀ |>.pushFree x₀
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := body_m
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.fvar .here)
  have hφ : Formula.IsDelta0 membershipLevyBound φ := body_delta_m _ _ _ _ _
  have hBody (z : Class) : φ.satisfies (η.pushFree z) ↔
      ∃ a, mem_l hℳ a E ∧ SecondOrderFunctionObjects.value_l hℳ A a x ∧
        SecondOrderFunctionObjects.value_l hℳ G a z.val :=
    (PowerlessRelativeClassBounded.formula_l hφ (η.pushFree z)).trans
      (body_formula_l (PowerlessRelativeClassRelativization.env_l (η.pushFree z)) _ _ _ _ _)
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hφ η R
  have hEq : y = Y.val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro z
    constructor
    · intro hzy
      obtain ⟨a, haI, hax, haz⟩ := (hH.2.2.2 x y hxI hxy z).mp hzy
      have haE := hCover a haI hax
      have hGaz := (PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mpr haz
      have hzR := (hR z).mpr ⟨a, hGaz⟩
      let z₀ : Class := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase R.property hzR⟩
      exact (hY z₀).mpr ⟨hzR, (hBody z₀).mpr ⟨a, haE, hax, hGaz⟩⟩
    · intro hzY
      let z₀ : Class := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hzY⟩
      obtain ⟨a, haE, hax, haz⟩ := (hBody z₀).mp ((hY z₀).mp hzY).2
      exact (hH.2.2.2 x y hxI hxy z).mpr ⟨a, hG.1 a haE, hax,
        (PowerlessRelationalCollapsePartial.value_l hH hC hG haE).mp haz⟩
  exact hEq.symm ▸ Y.property

def schema_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B E) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B x) <|
            .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
              .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
                .imp (PowerlessRelationalCollapsePartial.partial_m A I E C G) <|
                  .imp (covered_m A I E x) <| .imp (member_m x I) <|
                    .imp (SecondOrderObjectSyntax.value_m H x y) (PowerlessRelativeHierarchySyntax.class_m B y)

def sentence_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B A I E T H C G x y)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B A I E T H C G x y : Term ℒ [] Δ .set) : (sentence_m B A I E T H C G x y).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelationalCollapsePartial.formula_l, covered_formula_l, SecondOrderObjectSyntax.value_l,
    member_m, Arguments.eval]
  exact fun hBase hA hE hG hx hC hH hPartial hCover hxI hxy =>
    output_l (hBase := hBase) hA hE hG hx hC hH hPartial hCover hxI hxy

theorem derives_m {Δ : SortContext ℒ} (B A I E T H C G x y : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B A I E T H C G x y)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B A I E T H C G x y)

#print axioms body_delta_m
#print axioms output_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOutput
