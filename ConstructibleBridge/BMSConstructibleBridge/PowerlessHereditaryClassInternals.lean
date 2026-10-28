import BMSConstructibleBridge.PowerlessHereditaryClass
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassRelativization

/-! # 遗传类定义确实表示类内可数传递包络

包络公式本身不重复加入相对类谓词：在实际子模型中，其量词已经只遍历
类内对象。核验满射图、ω 和传递性后，给出原 Z₂ 的双向定义对应推导。
这不证明任意参数具有包络，也不证明遗传类满足 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryClassInternals

open Logic FirstOrder SecondOrderObjectSyntax
open ThirdOrderSemantics (carrier_l)
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (X T f w : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m X T) <| .conj (PowerlessRelativeHierarchyDerives.transitive_m T) <|
    .conj (SecondOrderOmegaSyntax.omega_m w) <| .conj (map_m f w T)
      (PowerlessMemberDefSyntax.onto_m w T f)

def envelope_m {Γ Δ : SortContext ℒ} (X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    body_m (up (up (up X))) (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def envelope_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (X : carrier_l 𝒩) : Prop :=
  ∃ T f w : carrier_l 𝒩, ThirdOrderSemantics.member_l 𝒩 X T ∧
    (∀ x, ThirdOrderSemantics.member_l 𝒩 x T → ∀ y, ThirdOrderSemantics.member_l 𝒩 y x →
      ThirdOrderSemantics.member_l 𝒩 y T) ∧ ThirdOrderSemantics.omega_l w ∧
      ThirdOrderSemantics.map_l f w T ∧ ∀ y, ThirdOrderSemantics.member_l 𝒩 y T →
        ∃ x, ThirdOrderSemantics.member_l 𝒩 x w ∧ ThirdOrderSemantics.value_l f x y

theorem transitive_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (T : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchyDerives.transitive_m T).satisfies η ↔
      ∀ x, ThirdOrderSemantics.member_l 𝒩 x (T.eval η) → ∀ y,
        ThirdOrderSemantics.member_l 𝒩 y x → ThirdOrderSemantics.member_l 𝒩 y (T.eval η) := by
  simp only [PowerlessRelativeHierarchyDerives.transitive_m, Formula.satisfies,
    member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem onto_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (w T f : Term ℒ Γ Δ .set) :
    (PowerlessMemberDefSyntax.onto_m w T f).satisfies η ↔
      ∀ y, ThirdOrderSemantics.member_l 𝒩 y (T.eval η) → ∃ x,
        ThirdOrderSemantics.member_l 𝒩 x (w.eval η) ∧ ThirdOrderSemantics.value_l (f.eval η) x y := by
  simp only [PowerlessMemberDefSyntax.onto_m, Formula.satisfies, member_m, Arguments.eval,
    ThirdOrderSemantics.value_formula_l, Term.eval_weakenBound, Term.eval]
  rfl

theorem envelope_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (X : Term ℒ Γ Δ .set) :
    (envelope_m X).satisfies η ↔ envelope_l (X.eval η) := by
  simp only [envelope_m, up, body_m, Formula.satisfies, member_m, Arguments.eval,
    transitive_formula_l, ThirdOrderSemantics.omega_formula_l, ThirdOrderSemantics.map_formula_l,
    onto_formula_l, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
theorem transitive_l (T : type_l hℳ B) :
    (∀ x : type_l hℳ B, mem_l hℳ x.val T.val → ∀ y : type_l hℳ B,
      mem_l hℳ y.val x.val → mem_l hℳ y.val T.val) ↔
    ∀ x, mem_l hℳ x T.val → ∀ y, mem_l hℳ y x → mem_l hℳ y T.val := by
  constructor
  · intro h x hx y hy
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase T.property hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase x'.property hy⟩
    exact h x' hx y' hy
  · exact fun h x hx y hy => h x.val hx y.val hy

theorem correspondence_l (X : type_l hℳ B) :
    PowerlessHereditaryClass.member_l hℳ B X.val ↔
      envelope_l (𝒩 := structure_l hℳ B hBase) X := by
  constructor
  · rintro ⟨T, f, w, hT, hf, hXT, hTrans, hω, hMap, hOnto⟩
    obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
    have hwClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
    let T' : type_l hℳ B := ⟨T, hT⟩
    let f' : type_l hℳ B := ⟨f, hf⟩
    let w' : type_l hℳ B := ⟨w, hwClass⟩
    exact ⟨T', f', w', hXT, (transitive_l (hBase := hBase) T').mpr hTrans,
      (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) w').mpr hω,
      (PowerlessRelativeClassFunctionAbsolute.map_l f' w' T').mpr hMap,
      (PowerlessRelativeClassFunctionAbsolute.onto_l f' w' T').mpr hOnto⟩
  · rintro ⟨T, f, w, hXT, hTrans, hω, hMap, hOnto⟩
    exact ⟨T.val, f.val, w.val, T.property, f.property, hXT,
      (transitive_l (hBase := hBase) T).mp hTrans,
      (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) w).mp hω,
      (PowerlessRelativeClassFunctionAbsolute.map_l f w T).mp hMap,
      (PowerlessRelativeClassFunctionAbsolute.onto_l f w T).mp hOnto⟩

def template_m : Formula ℒ [] [.set] := envelope_m (.fvar .here)

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m (.fvar .here) (.fvar (.there .here))) <|
      .iff (PowerlessHereditaryClass.formula_m (.fvar .here) (.fvar (.there .here)))
        (PowerlessRelativeClassRelativization.formula_m template_m)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hTrans hClass
  have hBase := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hTrans
  have hX := (PowerlessRelativeHierarchySemantics.class_formula_l K η (.fvar .here)
    (.fvar (.there .here))).mp hClass
  let X : type_l hℳ (η.freeVal .here) := ⟨η.freeVal (.there .here), hX⟩
  let η' := (Env.empty (M := structure_l hℳ (η.freeVal .here) hBase)).pushFree (sort := SetTheory.SetSort.set) X
  have hη : (PowerlessRelativeClassRelativization.env_l η').pushFree (sort := SetTheory.SetSort.set) (η.freeVal .here) = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      rcases v with _ | _ | v
      all_goals first | rfl | nomatch v
  exact (PowerlessHereditaryClass.formula_l K η (.fvar .here) (.fvar (.there .here))).trans <|
    (correspondence_l (hBase := hBase) X).trans <|
      (envelope_formula_l η' (.fvar .here)).symm.trans <|
        (by simpa only [hη, template_m] using
          (PowerlessRelativeClassRelativization.formula_l K template_m η').symm)

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryClassInternals
