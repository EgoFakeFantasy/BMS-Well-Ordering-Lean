import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomain
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassProductEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassOntoCountability
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionIndexEnumeration

/-! # 原实际程序码域的类内枚举与可数性

字母表的实际 Class 内 ω 满射给出全部内部有限词的枚举，再与 ω 恒等
枚举做积。用精确序列及积规格识别原码域，不另建一个近似程序集合。
空词和所有输出坐标均保留；内部长度不要求外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramDomainEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

theorem exists_l (K : source_coding_l hℳ) {ω Q G : type_l hℳ B}
    {S P : SecondOrderQuotient.type_l hℳ}
    (hω : omega_l (ℳ := 𝒩) ω)
    (hG : map_l (ℳ := 𝒩) G ω Q)
    (hOnto : ∀ q : type_l hℳ B, mem_l hℳ q.val Q.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) G i q)
    (hDomain : PowerlessRelativeFiniteProgramDomain.domain_l B ω.val Q.val S P) :
    ∃ U : type_l hℳ B, map_l (ℳ := 𝒱) U.val ω.val P ∧
      (∀ p, mem_l hℳ p P → ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := 𝒱) U.val i p) ∧
      PowerlessRelativeOrdinalCutoff.countable_l B ω.val P := by
  let A : type_l hℳ B := ⟨S, hDomain.1⟩
  let D : type_l hℳ B := ⟨P, hDomain.2.2.1⟩
  have hA : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω Q A := fun f =>
    (hDomain.2.1 f.val).trans
      (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l (hBase := hBase) ω Q f).symm
  obtain ⟨A₀, hA₀, T, hT, hTOnto⟩ :=
    PowerlessRelativeClassFiniteSequenceEnumeration.exists_l hω hG hOnto
  have hEq : A₀ = A := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    intro f
    exact (hA₀ f).trans (hA f).symm
  rw [hEq] at hT hTOnto
  obtain ⟨J, hJ, hRead⟩ :=
    PowerlessRelativeClassSatisfactionIndexEnumeration.identity_l (hBase := hBase) ω
  have hJOnto : ∀ j : type_l hℳ B, mem_l hℳ j.val ω.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) J i j :=
    fun j hj => ⟨j, hj, (hRead j j).mpr ⟨hj, rfl⟩⟩
  have hD (p : type_l hℳ B) : mem_l hℳ p.val D.val ↔
      ∃ w k : type_l hℳ B, mem_l hℳ w.val A.val ∧ mem_l hℳ k.val ω.val ∧
        ordered_l (ℳ := 𝒩) w k p := by
    constructor
    · intro hp
      obtain ⟨w, k, hw, hk, hCode⟩ := (hDomain.2.2.2 p.val).mp hp
      let w' : type_l hℳ B := ⟨w,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hw⟩
      let k' : type_l hℳ B := ⟨k,
        PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hk⟩
      exact ⟨w', k', hw, hk,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l w' k' p).mpr hCode⟩
    · rintro ⟨w, k, hw, hk, hCode⟩
      exact (hDomain.2.2.2 p.val).mpr ⟨w.val, k.val, hw, hk,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l w k p).mp hCode⟩
  obtain ⟨U, hU, hUOnto⟩ := PowerlessRelativeClassProductEnumeration.exists_l
    hω hT hJ hTOnto hJOnto hD
  have hMap := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) U ω D).mp hU
  have hCover := (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) U ω D).mp hUOnto
  exact ⟨U, hMap, hCover, PowerlessRelativeClassOntoCountability.countable_l (hBase := hBase)
    K ((PowerlessRelativeClassOmegaAbsolute.omega_l ω).mp hω) D.property U.property hMap hCover⟩

def schema_m {Δ : SortContext ℒ} (B ω Q G S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
            .imp (SecondOrderObjectSyntax.map_m G ω Q) <|
              .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω Q) <|
                .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P)
                  (PowerlessRelativeOrdinalCutoff.countable_m B ω P)

def sentence_m {Δ : SortContext ℒ} (B ω Q G S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω Q G S P)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω Q G S P : Term ℒ [] Δ .set) :
    (sentence_m B ω Q G S P).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l, PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K]
  intro η hBase hω hωC hQ hG hMap hOnto hDomain
  let O : type_l h𝒩 (B.eval η) := ⟨ω.eval η, hωC⟩
  let A : type_l h𝒩 (B.eval η) := ⟨Q.eval η, hQ⟩
  let F : type_l h𝒩 (B.eval η) := ⟨G.eval η, hG⟩
  obtain ⟨_, _, _, hCount⟩ := exists_l (hBase := hBase) K
    ((PowerlessRelativeClassOmegaAbsolute.omega_l O).mpr hω)
    ((PowerlessRelativeClassFunctionAbsolute.map_l F O A).mpr hMap)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l F O A).mpr hOnto) hDomain
  exact hCount

theorem derives_m {Δ : SortContext ℒ} (B ω Q G S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω Q G S P)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω Q G S P)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramDomainEnumeration
