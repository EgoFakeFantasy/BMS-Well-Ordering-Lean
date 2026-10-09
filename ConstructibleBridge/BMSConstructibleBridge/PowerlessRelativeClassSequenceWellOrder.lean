import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderMinimum

/-! # 类内良序母集上的全部内部有限序列良序

统一长度优先关系先按内部长度、再按首差异比较。定长良序由实际内部
公式归纳得到，非空子集先取最小长度，再取该切片最小元。正式出口在
原 Z₂ 推导核中，同时保留全部序列载体和关系图的精确规格。
此通用工具不等于最终 BMS 良序定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceWellOrder

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem of_graph_l {ω X R L S : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hR : wellOrder_l (ℳ := ClassModel) X R)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω X S)
    (hRead : ∀ f g, value_l (ℳ := ClassModel) L f g ↔ shortlex_l (ℳ₀ := ClassModel) ω X R f g) :
    wellOrder_l (ℳ := ClassModel) S L := by
  obtain ⟨hIrr, hTrans, hCompare⟩ := PowerlessRelativeClassSequenceOrderLinear.linear_l hω hR hS hRead
  exact ⟨hIrr, hTrans, hCompare, PowerlessRelativeClassSequenceOrderMinimum.minimum_l hω hR hS hRead⟩

theorem exists_l {ω X R : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hR : wellOrder_l (ℳ := ClassModel) X R) :
    ∃ S L : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω X S ∧
      wellOrder_l (ℳ := ClassModel) S L ∧
      ∀ f g, value_l (ℳ := ClassModel) L f g ↔ shortlex_l (ℳ₀ := ClassModel) ω X R f g := by
  obtain ⟨S, hS⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_l (hBase := hBase) (X := X) hω
  obtain ⟨L, hRead⟩ := PowerlessRelativeClassSequenceOrderGraph.exists_l (hBase := hBase) (R := R) hS
  exact ⟨S, L, hS, of_graph_l hω hR hS hRead, hRead⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def specification_m {Γ Δ : SortContext ℒ} (ω X R S L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessFiniteSequencesSyntax.spec_m ω X S) <|
    .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m S L)
      (PowerlessRelativeClassSequenceOrderGraph.specification_m ω X R L)

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω X R S L : Term ℒ Γ Δ .set) :
    (specification_m ω X R S L).satisfies η ↔
      PowerlessFiniteSequencesSyntax.spec_l (ω.eval η) (X.eval η) (S.eval η) ∧
      wellOrder_l (S.eval η) (L.eval η) ∧
      ∀ f g, value_l (L.eval η) f g ↔ shortlex_l (ω.eval η) (X.eval η) (R.eval η) f g := by
  simp only [specification_m, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelativeClassSequenceOrderGraph.specification_formula_l]

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let R : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m X R) <|
      .existsE .set <| .existsE .set <|
        specification_m (up (up ω)) (up (up X)) (up (up R)) (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    specification_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hR => exists_l (hBase := hBase) hω hR

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m
    (fun _ hℳ B hBase => models_l hℳ B hBase)

#print axioms of_graph_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceWellOrder
