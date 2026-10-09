import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderStep
import BMSConstructibleBridge.PowerlessRelativeClassInduction
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor

/-! # 同一长度优先关系在全部内部定长切片上良序

归纳性质是实际纯公式：每个精确定长切片由给定的同一关系 L 良序。
使用原 Z₂ 图翻译归纳覆盖整个内部自然数域，不要求模型外部标准；
出口包含该性质全部内部长度实例的正式对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderInduction

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def template_m {Γ Δ : SortContext ℒ} (n X L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (PowerlessRelativeClassSequenceSlices.spec_m (up n) (up X) (.bvar .here))
    (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (.bvar .here) (up L))

theorem template_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (n X L : Term ℒ Γ Δ .set) :
    (template_m n X L).satisfies η ↔ ∀ P,
      PowerlessRelativeClassSequenceSlices.spec_l (n.eval η) (X.eval η) P →
        wellOrder_l P (L.eval η) := by
  simp only [template_m, Formula.satisfies, PowerlessRelativeClassSequenceSlices.spec_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem all_l {ω X R L : type_l hℳ B} (hω : omega_l (ℳ := ClassModel) ω)
    (hR : wellOrder_l (ℳ := ClassModel) X R)
    (hRead : ∀ f g, value_l (ℳ := ClassModel) L f g ↔ shortlex_l (ℳ₀ := ClassModel) ω X R f g) :
    ∀ n : type_l hℳ B, member_l ClassModel n ω → ∀ P,
      PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P →
        wellOrder_l (ℳ := ClassModel) P L := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωRaw := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hωRaw K.omega_spec
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hωRaw
  let N : SecondOrderModel.num_l ℳ → type_l hℳ B :=
    PowerlessRelativeClassInduction.number_l (hBase := hBase) K
  have hNum (i : SecondOrderModel.num_l ℳ) : member_l ClassModel (N i) ω := by
    change mem_l hℳ (numberCode_l K i).val ω.val
    rw [hωEq]
    exact (numberCode_l K i).property
  have hIrr (n : type_l hℳ B) (hn : member_l ClassModel n ω) : ¬member_l ClassModel n n :=
    hOrd.wellOrder.linear.irrefl n.val hn
  have hTrans (n : type_l hℳ B) (hn : member_l ClassModel n ω) :
      ∀ i : type_l hℳ B, member_l ClassModel i n →
        ∀ j : type_l hℳ B, member_l ClassModel j i → member_l ClassModel j n := by
    have hnOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) n.val := by
      apply hOrd.mem
      exact hn
    exact fun i hi j hj => hnOrd.transitive i.val hi j.val hj
  let φ : Formula ℒ [] [.set, .set, .set] :=
    template_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  let η : Env ClassModel [] [.set, .set] := ((Env.empty).pushFree L).pushFree X
  have hFormula (n : type_l hℳ B) : φ.satisfies (η.pushFree n) ↔ ∀ P,
      PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P →
        wellOrder_l (ℳ := ClassModel) P L := template_formula_l _ _ _ _
  have hAll := PowerlessRelativeClassInduction.induction_l K φ η ?_ ?_
  · intro n hn
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.val, hωEq ▸ hn⟩
    have hVal : (numberCode_l K i).val = n.val := congrArg Subtype.val hi
    have hEq : N i = n := Subtype.ext hVal
    exact hEq ▸ ((hFormula (N i)).mp (hAll i))
  · apply (hFormula (N (SecondOrderModel.zero_l ℳ))).mpr
    intro P hP
    exact PowerlessRelativeClassSequenceOrderSlices.zero_l (hNum (SecondOrderModel.zero_l ℳ))
      (fun x => PowerlessBMSQuotientSuccessor.zero_l K x.val) hP hRead
  · intro i hi
    apply (hFormula (N (SecondOrderModel.succ_l i))).mpr
    intro Q hQ
    obtain ⟨P, hP⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (hBase := hBase) (X := X) hω (hNum i)
    have hSucc := (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase)
      (N i) (N (SecondOrderModel.succ_l i))).mpr (PowerlessBMSQuotientSuccessor.successor_l K i)
    exact PowerlessRelativeClassSequenceOrderStep.step_l
      (hNum i) (hNum (SecondOrderModel.succ_l i)) (hIrr _ (hNum i))
      (hIrr _ (hNum (SecondOrderModel.succ_l i))) hSucc (hTrans _ (hNum i))
      hP hQ hRead hR ((hFormula (N i)).mp hi P hP)

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set] .set := .fvar .here
  let X : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let R : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let L : Term ℒ [] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m X R) <|
      .imp (PowerlessRelativeClassSequenceOrderGraph.specification_m ω X R L) <|
        .forallE .set (.imp (member_m (.bvar .here) (up ω)) (template_m (.bvar .here) (up X) (up L)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelativeClassSequenceOrderGraph.specification_formula_l,
    member_m, Arguments.eval, template_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hR hRead => all_l (hBase := hBase) hω hR hRead

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m
    (fun _ hℳ B hBase => models_l hℳ B hBase)

#print axioms all_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderInduction
