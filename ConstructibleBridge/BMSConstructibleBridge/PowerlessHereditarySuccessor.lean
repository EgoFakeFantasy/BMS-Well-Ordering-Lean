import BMSConstructibleBridge.PowerlessHereditaryPairing
import BMSConstructibleBridge.PowerlessHereditaryBasicAxioms

/-! # 遗传域的实际后继封闭

在遗传子模型中依次构造单点集、配对和并集。遗传传递性将子模型
成员规格提升到全部环境对象，故所得对象是原纯语言中的后继，
而非只对子模型载体成立的后继。证明不使用完整源 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySuccessor

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_l {B a : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (ha : PowerlessHereditaryClass.member_l hℳ B a) :
    ∃ b, PowerlessHereditaryClass.member_l hℳ B b ∧
      PowerlessRelativeHierarchySemantics.successor_l hℳ a b := by
  let A : PowerlessHereditaryStructure.type_l hℳ B := ⟨a, ha⟩
  have hPair := PowerlessHereditaryPairing.models_l hℳ B hBase
  change ∀ x y : PowerlessHereditaryStructure.type_l hℳ B,
    ∃ p : PowerlessHereditaryStructure.type_l hℳ B,
      ∀ z : PowerlessHereditaryStructure.type_l hℳ B,
        mem_l hℳ z.val p.val ↔ z = x ∨ z = y at hPair
  obtain ⟨P, hP⟩ := hPair A A
  obtain ⟨Q, hQ⟩ := hPair A P
  have hUnion := PowerlessHereditaryBasicAxioms.union_l hℳ B hBase
  change ∀ q : PowerlessHereditaryStructure.type_l hℳ B,
    ∃ b : PowerlessHereditaryStructure.type_l hℳ B,
      ∀ z : PowerlessHereditaryStructure.type_l hℳ B,
        mem_l hℳ z.val b.val ↔ ∃ y : PowerlessHereditaryStructure.type_l hℳ B,
          mem_l hℳ y.val q.val ∧ mem_l hℳ z.val y.val at hUnion
  obtain ⟨C, hC⟩ := hUnion Q
  refine ⟨C.val, C.property, fun z => ⟨?_, ?_⟩⟩
  · intro hz
    let Z : PowerlessHereditaryStructure.type_l hℳ B :=
      ⟨z, PowerlessHereditaryClass.transitive_l hℳ C.property hz⟩
    obtain ⟨Y, hY, hZY⟩ := (hC Z).mp hz
    rcases (hQ Y).mp hY with rfl | rfl
    · exact Or.inl hZY
    · exact Or.inr (congrArg Subtype.val (((hP Z).mp hZY).elim id id))
  · rintro (hz | rfl)
    · let Z : PowerlessHereditaryStructure.type_l hℳ B :=
        ⟨z, PowerlessHereditaryClass.transitive_l hℳ ha hz⟩
      exact (hC Z).mpr ⟨A, (hQ A).mpr (Or.inl rfl), hz⟩
    · exact (hC A).mpr ⟨P, (hQ P).mpr (Or.inr rfl), (hP A).mpr (Or.inl rfl)⟩

def schema_m : Formula ℒ [] [.set, .set] :=
  let B : Term ℒ [] [.set, .set] .set := .fvar .here
  let a := .fvar (.there .here)
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessHereditaryClass.formula_m B a) <| .existsE .set <|
      .conj (PowerlessHereditaryClass.formula_m (B.weakenBound SetTheory.SetSort.set) (.bvar .here))
        (PowerlessRelativeHierarchySyntax.successor_m (a.weakenBound SetTheory.SetSort.set) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessHereditaryClass.formula_l K, PowerlessRelativeHierarchySemantics.successor_formula_l,
    Term.eval, Term.eval_weakenBound]
  exact fun hBase ha => exists_l hBase ha

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySuccessor
