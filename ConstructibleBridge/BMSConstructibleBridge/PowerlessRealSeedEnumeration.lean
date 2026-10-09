import BMSConstructibleBridge.PowerlessRealSeed
import BMSConstructibleBridge.PowerlessHereditaryClassInternals
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessSuccessorBounded
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 实数基集具有相对类内的实际 ω 满射

关系规定零数映到 R，后继 n+1 映到 n。所有内部自然数都由原模型前驱
公理覆盖；关系图在相对类内由 Δ₀ 图模式构造。由此证明 R 确实属于
以 ω ∪ {R} 为基集的遗传类，并给出原 Z₂ 对象存在句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRealSeedEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def enum_m : Formula ℒ [] [.set, .set, .set, .set] :=
  .disj (.conj (.equal (.fvar .here) (.fvar (.there (.there (.there .here)))))
    (.equal (.fvar (.there .here)) (.fvar (.there (.there .here)))))
    (PowerlessSuccessorBounded.formula_m (.fvar (.there .here)) (.fvar .here))

theorem enum_delta_l : Formula.IsDelta0 membershipLevyBound enum_m :=
  .disj (.conj (.equal _ _) (.equal _ _)) (PowerlessSuccessorBounded.delta_l _ _)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private def enum_l (K : source_coding_l hℳ) (R n y : SecondOrderQuotient.type_l hℳ) : Prop :=
  (n = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧ y = R) ∨
    PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ) y n

private theorem unique_l (K : source_coding_l hℳ) {R n y z : SecondOrderQuotient.type_l hℳ}
    (hy : enum_l K R n y) (hz : enum_l K R n z) : y = z := by
  rcases hy with ⟨hn, hy⟩ | hy
  · rcases hz with ⟨_, hz⟩ | hz
    · exact hy.trans hz.symm
    · have hMem := (hz z).mpr (Or.inr rfl)
      rw [hn] at hMem
      exact (PowerlessBMSQuotientSuccessor.zero_l K z hMem).elim
  · rcases hz with ⟨hn, _⟩ | hz
    · have hMem := (hy y).mpr (Or.inr rfl)
      rw [hn] at hMem
      exact (PowerlessBMSQuotientSuccessor.zero_l K y hMem).elim
    · exact SecondOrderNaturalCases.successor_injective_l hℳ hy hz

theorem enumeration_l (K : source_coding_l hℳ) (R B : SecondOrderQuotient.type_l hℳ)
    (hSpec : ∀ x, mem_l hℳ x B ↔ mem_l hℳ x K.omega ∨ x = R)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    ∃ f, PowerlessRelativeClassCorrespondence.member_l hℳ B f ∧
      SecondOrderFunctionObjects.map_l hℳ f K.omega B ∧ ∀ y, mem_l hℳ y B →
        ∃ n, mem_l hℳ n K.omega ∧ SecondOrderFunctionObjects.value_l hℳ f n y := by
  let T : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let R' : type_l hℳ B := ⟨R, PowerlessRelativeClassCorrespondence.base_l hℳ hBase ((hSpec R).mpr (Or.inr rfl))⟩
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  let η := (Env.empty (M := structure_l hℳ B hBase)).pushFree (sort := SetTheory.SetSort.set) e
    |>.pushFree (sort := SetTheory.SetSort.set) R'
  have hRead (n y : type_l hℳ B) : enum_m.satisfies
      ((η.pushFree (sort := SetTheory.SetSort.set) y).pushFree (sort := SetTheory.SetSort.set) n) ↔ enum_l K R n.val y.val := by
    simp only [enum_m, Formula.satisfies, PowerlessSuccessorBounded.formula_l, Term.eval]
    change ((n = e ∧ y = R') ∨ PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) y n) ↔ _
    exact or_congr (and_congr
      ⟨congrArg Subtype.val, fun h => Subtype.ext (show n.val = e.val from h)⟩
      ⟨congrArg Subtype.val, fun h => Subtype.ext (show y.val = R'.val from h)⟩)
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) y n)
  have hTotal (n : type_l hℳ B) (hn : mem_l hℳ n.val O.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val T.val ∧ enum_m.satisfies ((η.pushFree y).pushFree n) := by
    have hWitness : ∃ y : type_l hℳ B, mem_l hℳ y.val T.val ∧ enum_l K R n.val y.val := by
      rcases SecondOrderNaturalCases.cases_l K hn with hZero | ⟨a, ha, hSucc⟩
      · exact ⟨R', (hSpec R).mpr (Or.inr rfl), Or.inl ⟨hZero, rfl⟩⟩
      · let a' : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase O.property ha⟩
        exact ⟨a', (hSpec a).mpr (Or.inl ha), Or.inr hSucc⟩
    obtain ⟨y, hy, hny⟩ := hWitness
    refine ⟨y, ⟨hy, (hRead n y).mpr hny⟩, ?_⟩
    intro z hz
    exact Subtype.ext (unique_l K ((hRead n z).mp hz.2) hny)
  obtain ⟨f, hMap, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l enum_delta_l η O T hTotal
  have hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val T.val → ∃ n : type_l hℳ B,
      mem_l hℳ n.val O.val ∧ value_l (ℳ := structure_l hℳ B hBase) f n y := by
    intro y hy
    rcases (hSpec y.val).mp hy with hyω | hyR
    · have hωClass := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr K.omega_spec
      obtain ⟨n, hn, hSucc⟩ := ((PowerlessNatural.inductive_iff_l
        (ℳ := structure_l hℳ B hBase) O).mp hωClass.1).2 y hyω
      refine ⟨n, hn, (hValue n y).mpr ⟨hn, hy, (hRead n y).mpr (Or.inr ?_)⟩⟩
      exact (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) y n).mp hSucc
    · have heω : mem_l hℳ e.val O.val := (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
      exact ⟨e, heω, (hValue e y).mpr ⟨heω, hy, (hRead e y).mpr (Or.inl ⟨rfl, hyR⟩)⟩⟩
  exact ⟨f.val, f.property, (PowerlessRelativeClassFunctionAbsolute.map_l f O T).mp hMap,
    (PowerlessRelativeClassFunctionAbsolute.onto_l f O T).mp hOnto⟩

theorem coverage_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (ω R : SecondOrderQuotient.type_l hℳ) (hω : SecondOrderOmega.omega_l hℳ ω)
    (hR : ∀ x, mem_l hℳ x R → mem_l hℳ x ω) : ∃ B,
      (∀ x, mem_l hℳ x B ↔ mem_l hℳ x ω ∨ x = R) ∧ PowerlessHereditaryClass.member_l hℳ B R := by
  obtain ⟨B, hSpec, hBase⟩ := PowerlessRealSeed.exists_l hℳ ω R hω hR
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hSpec' : ∀ x, mem_l hℳ x B ↔ mem_l hℳ x K.omega ∨ x = R := by
    simpa only [hEq] using hSpec
  obtain ⟨f, hf, hMap, hOnto⟩ := enumeration_l K R B hSpec' hBase
  exact ⟨B, hSpec, B, f, K.omega, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase,
    hf, (hSpec R).mpr (Or.inr rfl), hBase, K.omega_spec, hMap, hOnto⟩

def schema_m : Formula ℒ [] [.set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar .here)) <|
    .imp (ThirdOrderTheory.subset_m (.fvar (.there .here)) (.fvar .here)) <|
      .existsE .set <| .conj (PowerlessRealSeed.spec_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
        (PowerlessHereditaryClass.formula_m (.bvar .here) (.fvar (.there .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω hR
  obtain ⟨B, hSpec, hHereditary⟩ := coverage_l hℳ (η.freeVal .here) (η.freeVal (.there .here))
    ((SecondOrderOmegaSyntax.omega_l hℳ η (.fvar .here)).mp hω)
    ((ThirdOrderSemantics.subset_formula_l η (.fvar (.there .here)) (.fvar .here)).mp hR)
  exact ⟨B, (PowerlessRealSeed.spec_formula_l (η.pushBound B) (.fvar .here) (.fvar (.there .here)) (.bvar .here)).mpr hSpec,
    (PowerlessHereditaryClass.formula_l K (η.pushBound B) (.bvar .here) (.fvar (.there .here))).mpr hHereditary⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms enumeration_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRealSeedEnumeration
