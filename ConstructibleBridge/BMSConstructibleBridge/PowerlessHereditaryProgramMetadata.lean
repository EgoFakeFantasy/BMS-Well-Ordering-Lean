import BMSConstructibleBridge.PowerlessHereditaryPairing
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStep
import BMSConstructibleBridge.PowerlessRelativeFiniteNumeralTags

/-! # 同一原有限程序元数据的遗传资格

纯隶属 ℒ，原 Z₂ 背景及原 Derives 核。对实际无序对、有序对和记录
逐次合并遗传包络；原对象不更换。原空记录和实际 numeral 标签据此
获得遗传资格，不预供 Class 枚举，不要求整个 Class 可数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramMetadata

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

include hBase in
theorem pair_l {x y p : SecondOrderQuotient.type_l hℳ}
    (hx : PowerlessHereditaryClass.member_l hℳ B x)
    (hy : PowerlessHereditaryClass.member_l hℳ B y)
    (hp : SecondOrderPairObjects.pair_l hℳ x y p) :
    PowerlessHereditaryClass.member_l hℳ B p := by
  have hxC := PowerlessHereditaryClass.contained_l hℳ hBase hx
  have hyC := PowerlessHereditaryClass.contained_l hℳ hBase hy
  let X : M := ⟨x, hxC⟩
  let Y : M := ⟨y, hyC⟩
  let P : M := ⟨p, PowerlessRelativeClassPair.pair_l hℳ hBase hxC hyC hp⟩
  have hPair (z : M) : mem_l hℳ z.val P.val ↔ z = X ∨ z = Y :=
    (hp z.val).trans (or_congr
      ⟨fun h => Subtype.ext (show z.val = X.val from h), fun h => congrArg Subtype.val h⟩
      ⟨fun h => Subtype.ext (show z.val = Y.val from h), fun h => congrArg Subtype.val h⟩)
  have hX := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X).mp hx
  have hY := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) Y).mp hy
  exact (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) P).mpr
    (PowerlessHereditaryPairEnvelope.exists_l hX hY hPair)

include hBase in
theorem ordered_l {x y p : SecondOrderQuotient.type_l hℳ}
    (hx : PowerlessHereditaryClass.member_l hℳ B x)
    (hy : PowerlessHereditaryClass.member_l hℳ B y)
    (hp : SecondOrderPairObjects.ordered_l hℳ x y p) :
    PowerlessHereditaryClass.member_l hℳ B p := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  exact pair_l (hBase := hBase) (pair_l (hBase := hBase) hx hx hs)
    (pair_l (hBase := hBase) hx hy ht) hp

include hBase in
theorem record_l {i D f a : SecondOrderQuotient.type_l hℳ}
    (hi : PowerlessHereditaryClass.member_l hℳ B i)
    (hD : PowerlessHereditaryClass.member_l hℳ B D)
    (hf : PowerlessHereditaryClass.member_l hℳ B f)
    (ha : PowerlessRelativeFiniteProgramStep.record_l i D f a) :
    PowerlessHereditaryClass.member_l hℳ B a := by
  obtain ⟨p, hp, ha⟩ := ha
  exact ordered_l (hBase := hBase) hi (ordered_l (hBase := hBase) hD hf hp) ha

include hBase in
theorem initial_l {ω e a : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (he : ∀ x, ¬mem_l hℳ x e)
    (ha : PowerlessRelativeFiniteProgramStep.record_l e e e a) :
    PowerlessHereditaryClass.member_l hℳ B e ∧ PowerlessHereditaryClass.member_l hℳ B a := by
  obtain ⟨e', he', heω⟩ := hω.1.1
  have hEq : e = e' := SecondOrderQuotient.ext_l hℳ e e' (fun x =>
    ⟨fun h => (he x h).elim, fun h => (he' x h).elim⟩)
  have heHC := PowerlessHereditaryClass.transitive_l hℳ
    (PowerlessHereditaryOmega.member_l hℳ hBase hω) (hEq ▸ heω)
  exact ⟨heHC, record_l (hBase := hBase) heHC heHC heHC ha⟩

include hBase in
theorem numeral_l (K : source_coding_l hℳ) {ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (k : Nat) :
    PowerlessHereditaryClass.member_l hℳ B (PowerlessRelativeFiniteNumeralTags.value_l K k) :=
  PowerlessHereditaryClass.transitive_l hℳ
    (PowerlessHereditaryOmega.member_l hℳ hBase hω)
    (PowerlessRelativeFiniteNumeralTags.member_l K hω k)

def schema_m {Δ : SortContext ℒ} (B ω e a : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
        .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
          .conj (PowerlessHereditaryClass.formula_m B e) (PowerlessHereditaryClass.formula_m B a)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (B ω e a : Term ℒ [] Δ .set) :
    (Metatheory.Formula.forall_close (schema_m B ω e a)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω he ha
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩 η B).mp hBase
  have hω' := (SecondOrderOmegaSyntax.omega_l h𝒩 η ω).mp hω
  have he' := (PowerlessDefinableFiniteTraceDerives.zero_formula_l η e).mp he
  have ha' := (PowerlessRelativeFiniteProgramStep.record_formula_l η e e e a).mp ha
  simp only [Formula.satisfies, PowerlessHereditaryClass.formula_l K]
  exact initial_l (hBase := hBase') hω' he' ha'

theorem derives_m {Δ : SortContext ℒ} (B ω e a : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m B ω e a))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω e a)

#print axioms pair_l
#print axioms record_l
#print axioms initial_l
#print axioms numeral_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryProgramMetadata
