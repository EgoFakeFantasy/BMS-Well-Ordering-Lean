import BMSConstructibleBridge.PowerlessHereditaryExtension

/-! # 任意传递基集上的遗传类都包含 ω

ω 已属于相对并类。有界等式关系给出类内恒等图，再作单点包络扩张，
将 ω 作为对象放进传递可数包络。不存在任意实数覆盖的附加前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOmega

open Logic FirstOrder PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) : PowerlessHereditaryClass.member_l hℳ B ω := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  let O : type_l hℳ B := ⟨ω, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)⟩
  let φ : Formula ℒ [] [.set, .set] := .equal (.fvar .here) (.fvar (.there .here))
  have hφ : Formula.IsDelta0 membershipLevyBound φ := .equal _ _
  let η := Env.empty (M := structure_l hℳ B hBase)
  have hTotal (x : type_l hℳ B) (hx : mem_l hℳ x.val O.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val O.val ∧ φ.satisfies ((η.pushFree y).pushFree x) :=
    ⟨x, ⟨hx, rfl⟩, fun _ hz => hz.2.symm⟩
  obtain ⟨f, hMap, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l hφ η O O hTotal
  have hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val O.val → ∃ x : type_l hℳ B,
      mem_l hℳ x.val O.val ∧ ThirdOrderSemantics.value_l (ℳ := structure_l hℳ B hBase) f x y :=
    fun y hy => ⟨y, hy, (hValue y y).mpr ⟨hy, hy, rfl⟩⟩
  have hTrans := (PowerlessHereditaryClassInternals.transitive_l (hBase := hBase) O).mpr
    (fun x hx y hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
  exact (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) O).mpr
    (PowerlessHereditaryExtension.exists_l O O O f
      ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω)
      hTrans (fun _ hx => hx) hMap hOnto)

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (SecondOrderOmegaSyntax.omega_m (.fvar (.there .here)))
      (PowerlessHereditaryClass.formula_m (.fvar .here) (.fvar (.there .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω
  exact (PowerlessHereditaryClass.formula_l K η (.fvar .here) (.fvar (.there .here))).mpr
    (member_l hℳ ((PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase)
      ((SecondOrderOmegaSyntax.omega_l hℳ η (.fvar (.there .here))).mp hω))

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOmega
