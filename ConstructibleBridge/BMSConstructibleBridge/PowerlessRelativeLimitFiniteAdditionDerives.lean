import BMSConstructibleBridge.PowerlessRelativeClassFiniteTraceAbsolute

/-! # 全部内部有限加法轨迹的共同界：原 Z₂ 对象出口

对象语言为纯隶属语言，守卫是传递基集、固定非零极限层、ω 与空对象。
结论使用已经证明等价及绝对的 Δ₀ 轨迹检查式，原图翻译在原推导核中可推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteAdditionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySyntax (up)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_l {B β C ω e a : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hω : SecondOrderOmega.omega_l hℳ ω) (he : ∀ x, ¬mem_l hℳ x e)
    (ha : mem_l hℳ a ω) (hωC : mem_l hℳ ω C) :
    ∀ n, mem_l hℳ n ω → ∃ g, mem_l hℳ g C ∧
      PowerlessAdditionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω e a n g := by
  have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hC
  have hωClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hωC
  obtain ⟨e₀, he₀, he₀ω⟩ := hω.1.1
  have heEq : e₀ = e := SecondOrderQuotient.ext_l hℳ e₀ e (fun x => iff_of_false (he₀ x) (he x))
  have heω : mem_l hℳ e ω := heEq ▸ he₀ω
  let C' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨C, hCClass⟩
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, hωClass⟩
  let e' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨e, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass heω⟩
  let a' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass ha⟩
  have hω' := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  intro n hn
  let n' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass hn⟩
  obtain ⟨g, hgC, hg⟩ := PowerlessRelativeLimitFiniteAddition.exists_l (hBase := hBase) (C := C')
    (ω := ω') (e := e') (a := a') hLimit hC hωC hω' (fun x => he x.val) ha n' hn
  have hgAmbient := (PowerlessRelativeClassFiniteTraceAbsolute.trace_l hω' hn).mp hg
  exact ⟨g.val, hgC, (PowerlessRelativeClassFiniteTraceAbsolute.ambient_equiv_l hω hn).mpr hgAmbient⟩

def conclusion_m {Γ Δ : SortContext ℒ} (C ω e a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    membershipLevyBound.boundedExists (up C) <|
      PowerlessAdditionTraceBounded.formula_m (up (up ω)) (up (up e)) (up (up a))
        (.bvar (.there .here)) (.bvar .here)

theorem conclusion_formula_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (C ω e a : Term ℒ Γ Δ .set) :
    (conclusion_m C ω e a).satisfies η ↔ ∀ n, mem_l hℳ n (ω.eval η) →
      ∃ g, mem_l hℳ g (C.eval η) ∧ PowerlessAdditionTraceBounded.trace_l
        (𝒩 := SecondOrderQuotient.structure_l hℳ) (ω.eval η) (e.eval η) (a.eval η) n g := by
  simp only [conclusion_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessAdditionTraceBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let β : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let C : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let ω : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let e : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (PowerlessRelativeHierarchySyntax.empty_m e) <|
          .imp (member_m a ω) <| .imp (member_m ω C) (conclusion_m C ω e a)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit hω he ha hωC
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l (hℳ := hℳ) η (.fvar (.there .here))).mp hLimit
  have hω' := (ThirdOrderSemantics.omega_formula_l η (.fvar (.there (.there (.there .here))))).mp hω
  have he' := (PowerlessRelativeHierarchySemantics.empty_formula_l (hℳ := hℳ) η
    (.fvar (.there (.there (.there (.there .here)))))).mp he
  exact (conclusion_formula_l (hℳ := hℳ) η (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))).mpr
      (exists_l hBase' hC' hLimit' hω' he' ha hωC)

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteAdditionDerives
