import BMSConstructibleBridge.PowerlessRelationalCollapseOrderReading
import BMSConstructibleBridge.PowerlessRelativeHierarchyStep

/-! # 原序数索引初段的指定层界

纯隶属 ℒ，原 Z₂。P 可以仍是 raw 图：a<α 时先用其满射取
实际 p，再用同一类内 J/p 定义初段；a=α 时初段恰为 I。
所以 P 不成为类内分离参数。后继初段的单点等式、A 前驱封闭
和给定极限层中的成员界均针对同一实际源集合，而非替代源。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrdinalCut

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def cut_m {Γ Δ : SortContext ℒ} (I P a E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up E)) <|
    .conj (member_m (.bvar .here) (up I)) <| membershipLevyBound.boundedExists (up a)
      (PowerlessValueBounded.formula_m (up (up P)) (.bvar (.there .here)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

def cut_l (I P a E : Raw) : Prop :=
  ∀ x, mem_l hℳ x E ↔ mem_l hℳ x I ∧ ∃ b, mem_l hℳ b a ∧ SecondOrderFunctionObjects.value_l hℳ P x b

theorem cut_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I P a E : Term ℒ Γ Δ .set) : (cut_m I P a E).satisfies η ↔
      cut_l (I.eval η) (P.eval η) (a.eval η) (E.eval η) := by
  simp only [cut_m, cut_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem point_l {I J α P a p E : Raw}
    (hJ : wellOrder_l (ℳ := 𝒱) I J) (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P)
    (hpa : SecondOrderFunctionObjects.value_l hℳ P p a) (hE : cut_l I P a E) :
    PowerlessRelationalCollapseOrderedCut.cut_l I J p E := by
  intro x
  constructor
  · intro hx
    obtain ⟨hxI, b, hba, hxb⟩ := (hE x).mp hx
    exact ⟨hxI, (PowerlessRelationalCollapseOrderReading.reads_l hJ hP x p b a hxb hpa).mpr hba⟩
  · rintro ⟨hxI, hxp⟩
    obtain ⟨b, hb, _⟩ := hP.2.1.2 x hxI
    exact (hE x).mpr ⟨hxI, b,
      (PowerlessRelationalCollapseOrderReading.reads_l hJ hP x p b a hb.2 hpa).mp hxp, hb.2⟩

theorem of_point_l {I J α P a p E : Raw}
    (hJ : wellOrder_l (ℳ := 𝒱) I J) (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P)
    (hpa : SecondOrderFunctionObjects.value_l hℳ P p a)
    (hE : PowerlessRelationalCollapseOrderedCut.cut_l I J p E) : cut_l I P a E := by
  intro x
  constructor
  · intro hx
    obtain ⟨hxI, hxp⟩ := (hE x).mp hx
    obtain ⟨b, hb, _⟩ := hP.2.1.2 x hxI
    exact ⟨hxI, b,
      (PowerlessRelationalCollapseOrderReading.reads_l hJ hP x p b a hb.2 hpa).mp hxp, hb.2⟩
  · rintro ⟨hxI, b, hba, hxb⟩
    exact (hE x).mpr ⟨hxI,
      (PowerlessRelationalCollapseOrderReading.reads_l hJ hP x p b a hxb hpa).mpr hba⟩

theorem end_l {I J α P E : Raw}
    (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P) (hE : cut_l I P α E) : E = I := by
  apply SecondOrderQuotient.ext_l hℳ
  intro x
  constructor
  · exact fun hx => ((hE x).mp hx).1
  · intro hx
    obtain ⟨a, ha, _⟩ := hP.2.1.2 x hx
    exact (hE x).mpr ⟨hx, a, ha⟩

theorem closed_l {A I J α P a E : Raw}
    (hJ : wellOrder_l (ℳ := 𝒱) I J) (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P)
    (hExtends : PowerlessRelationalCollapseOrderedCut.extends_l I A J)
    (ha : Ordinal a) (hE : cut_l I P a E) :
    ∀ x, mem_l hℳ x E → ∀ y, mem_l hℳ y I →
      SecondOrderFunctionObjects.value_l hℳ A y x → mem_l hℳ y E := by
  intro x hx y hy hyx
  obtain ⟨hxI, b, hb, hxb⟩ := (hE x).mp hx
  obtain ⟨c, hc, _⟩ := hP.2.1.2 y hy
  have hcb := (PowerlessRelationalCollapseOrderReading.reads_l hJ hP y x c b hc.2 hxb).mp
    (hExtends y hy x hxI hyx)
  exact (hE y).mpr ⟨hy, c, ha.transitive b hb c hcb, hc.2⟩

theorem successor_l {I J α P a b q E D : Raw}
    (hJ : wellOrder_l (ℳ := 𝒱) I J) (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ b a)
    (hqb : SecondOrderFunctionObjects.value_l hℳ P q b)
    (hE : cut_l I P a E) (hD : cut_l I P b D) :
    ∀ x, mem_l hℳ x E ↔ mem_l hℳ x D ∨ x = q := by
  intro x
  constructor
  · intro hx
    obtain ⟨hxI, c, hc, hxc⟩ := (hE x).mp hx
    rcases (hSucc c).mp hc with hcb | hcb
    · exact Or.inl ((hD x).mpr ⟨hxI, c, hcb, hxc⟩)
    · exact Or.inr (PowerlessRelationalCollapseOrderReading.inject_l hJ hP x q b (hcb ▸ hxc) hqb)
  · rintro (hx | hxq)
    · obtain ⟨hxI, c, hc, hxc⟩ := (hD x).mp hx
      exact (hE x).mpr ⟨hxI, c, (hSucc c).mpr (Or.inl hc), hxc⟩
    · have hqI := (SecondOrderFunctionProperties.value_mem_l hℳ hP.2.1 hqb).1
      exact hxq.symm ▸ (hE q).mpr ⟨hqI, b, PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc, hqb⟩

theorem member_l {B β L A I J α P a E : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hL : PowerlessRelativeHierarchySemantics.level_l hℳ B β L)
    (hIL : mem_l hℳ I L) (hJL : mem_l hℳ J L)
    (hJ : wellOrder_l (ℳ := 𝒱) I J) (hP : SecondOrderCollapseFunction.spec_l hℳ J I α P)
    (hExtends : PowerlessRelationalCollapseOrderedCut.extends_l I A J)
    (hStage : mem_l hℳ a α ∨ a = α) (hE : cut_l I P a E) : mem_l hℳ E L := by
  rcases hStage with ha | rfl
  · obtain ⟨p, hpI, hpa⟩ := hP.2.2.1 a ha
    have hpL := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hL I hIL p hpI
    obtain ⟨D, hDL, hD, _, _, _⟩ := PowerlessRelationalCollapseOrderedCut.exists_l
      hBase hLimit hL hIL hJL hpL hpI hJ.2.1 hJ.1 hExtends
    have hPoint := point_l hJ hP hpa hE
    have hEq : E = D := SecondOrderQuotient.ext_l hℳ E D (fun x => (hPoint x).trans (hD x).symm)
    exact hEq.symm ▸ hDL
  · exact (end_l hP hE).symm ▸ hIL

def schema_m {Δ : SortContext ℒ} (B β L A I J α P a E : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m B β L) <|
        .imp (member_m I L) <| .imp (member_m J L) <|
          .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
            .imp (SecondOrderCollapseSyntax.formula_m J I α P) <|
              .imp (PowerlessRelationalCollapseOrderedCut.extends_m I A J) <|
                .imp (.disj (member_m a α) (.equal a α)) <| .imp (cut_m I P a E) (member_m E L)

def sentence_m {Δ : SortContext ℒ} (B β L A I J α P a E : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B β L A I J α P a E)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B β L A I J α P a E : Term ℒ [] Δ .set) : (sentence_m B β L A I J α P a E).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelationalCollapseOrderedCut.extends_formula_l, cut_formula_l, member_m, Arguments.eval]
  exact fun hBase hLimit hL hI hJ hOrder hP hExtends hStage hE =>
    member_l (hℳ := hℳ) hBase hLimit hL hI hJ hOrder hP hExtends hStage hE

theorem derives_m {Δ : SortContext ℒ} (B β L A I J α P a E : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B β L A I J α P a E)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B β L A I J α P a E)

#print axioms point_l
#print axioms of_point_l
#print axioms end_l
#print axioms closed_l
#print axioms successor_l
#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseOrdinalCut
