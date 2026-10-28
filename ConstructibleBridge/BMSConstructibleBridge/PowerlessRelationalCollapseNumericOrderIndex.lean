import BMSConstructibleBridge.PowerlessRelationalCollapseOrderReading
import BMSConstructibleBridge.SecondOrderMostowski
import BMSConstructibleBridge.SecondOrderRelationSyntax

/-! # 数码良序的实际原序数索引

纯隶属 ℒ，原 Z₂。关系的全部坐标属于实际 I⊆ω；良序的最小元
量化全部 raw 子集。非平凡载体的关系域域恰为 I，故原 Mostowski
构造可直接使用；空载体与单点载体另作实际图，不能丢弃孤立点。
本模块只消去预供坍缩 P 的前提，不构造前驱优先良序 J。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumericOrderIndex

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {ω I J : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : ∀ x, mem_l hℳ x I → mem_l hℳ x ω)
    (hRelation : SecondOrderRegularRelation.relation_l hℳ J I)
    (hJ : wellOrder_l (ℳ := 𝒱) I J) :
    ∃ α P, SecondOrderCollapseFunction.spec_l hℳ J I α P := by
  classical
  by_cases hMany : ∃ a b, mem_l hℳ a I ∧ mem_l hℳ b I ∧ a ≠ b
  · have hEndpoints {x y : Raw} (hxy : SecondOrderFunctionObjects.value_l hℳ J x y) :
        mem_l hℳ x I ∧ mem_l hℳ y I :=
      SecondOrderRegularRelation.endpoints_l hℳ J I x y hRelation hxy
    have hField (x : Raw) : SecondOrderRegularRelation.domain_l hℳ J x ↔ mem_l hℳ x I := by
      constructor
      · rintro ⟨y, hxy | hyx⟩
        · exact (hEndpoints hxy).1
        · exact (hEndpoints hyx).2
      · intro hx
        obtain ⟨a, b, ha, hb, hab⟩ := hMany
        have hOther : ∃ y, mem_l hℳ y I ∧ x ≠ y := by
          by_cases hxa : x = a
          · exact ⟨b, hb, hxa ▸ hab⟩
          · exact ⟨a, ha, hxa⟩
        obtain ⟨y, hy, hxy⟩ := hOther
        rcases hJ.2.2.1 x y ⟨hx, hy⟩ with hlt | heq | hgt
        · exact ⟨y, Or.inl hlt⟩
        · exact (hxy heq).elim
        · exact ⟨y, Or.inr hgt⟩
    have hRelationω : SecondOrderRegularRelation.relation_l hℳ J ω := by
      intro p hp
      obtain ⟨x, y, hx, hy, hPair⟩ := hRelation p hp
      exact ⟨x, y, hI x hx, hI y hy, hPair⟩
    have hRegular : SecondOrderRegularRelation.regular_l hℳ J ω := by
      intro D hNonempty hSub
      exact hJ.2.2.2 D ⟨fun x hx => (hField x).mp
        ((SecondOrderRegularRelation.field_iff_l hℳ J ω hRelationω x).mp (hSub x hx)),
        hNonempty⟩
    obtain ⟨D, α, P, hD, hP⟩ := SecondOrderMostowski.exists_l hℳ J ω hω hRegular
    have hEq : D = I := SecondOrderQuotient.ext_l hℳ D I (fun x =>
      (hD x).trans ((SecondOrderRegularRelation.field_iff_l hℳ J ω hRelationω x).trans (hField x)))
    subst D
    exact ⟨α, P, hP⟩
  · by_cases hNonempty : ∃ x, mem_l hℳ x I
    · obtain ⟨x₀, hx₀⟩ := hNonempty
      have hOne (x : Raw) (hx : mem_l hℳ x I) : x = x₀ := by
        by_contra hNe
        exact hMany ⟨x, x₀, hx, hx₀, hNe⟩
      obtain ⟨z, hz⟩ := SecondOrderQuotient.empty_l hℳ
      obtain ⟨α, hα⟩ := SecondOrderPairObjects.pair_exists_l hℳ z z
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x₀ z
      obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ p p
      have hPair (q : Raw) (hq : mem_l hℳ q P) : q = p := ((hP q).mp hq).elim id id
      have hValue (x y : Raw) : SecondOrderFunctionObjects.value_l hℳ P x y ↔ x = x₀ ∧ y = z := by
        constructor
        · rintro ⟨q, hq, hxy⟩
          have hEq := hPair q hq
          subst q
          exact (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp).mp rfl
        · rintro ⟨rfl, rfl⟩
          exact ⟨p, (hP p).mpr (Or.inl rfl), hp⟩
      have hzα : mem_l hℳ z α := (hα z).mpr (Or.inl rfl)
      have hαOne (x : Raw) (hx : mem_l hℳ x α) : x = z := ((hα x).mp hx).elim id id
      refine ⟨α, P, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
      · intro x y hx hy
        exact (hz y (hαOne x hx ▸ hy)).elim
      · intro q hq
        have hEq := hPair q hq
        subst q
        exact ⟨x₀, z, hx₀, hzα, hp⟩
      · intro x hx
        have hEq := hOne x hx
        subst x
        exact ⟨z, ⟨hzα, (hValue x₀ z).mpr ⟨rfl, rfl⟩⟩,
          fun y hy => hαOne y hy.1⟩
      · intro y hy
        have hEq := hαOne y hy
        subst y
        exact ⟨x₀, hx₀, (hValue x₀ z).mpr ⟨rfl, rfl⟩⟩
      · intro x y hx hxy w
        have hxEq := hOne x hx
        have hyEq := ((hValue x y).mp hxy).2
        subst x
        subst y
        constructor
        · exact fun hw => (hz w hw).elim
        · rintro ⟨a, ha, hax, _haw⟩
          have hEq := hOne a ha
          subst a
          exact (hJ.1 x₀ hx₀ hax).elim
    · have hEmpty (x : Raw) (hx : mem_l hℳ x I) : False := hNonempty ⟨x, hx⟩
      refine ⟨I, I, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact fun x _y hx _hy => (hEmpty x hx).elim
      · exact fun p hp => (hEmpty p hp).elim
      · exact fun x hx => (hEmpty x hx).elim
      · exact fun y hy => (hEmpty y hy).elim
      · exact fun x _y hx _hxy _z => (hEmpty x hx).elim

def schema_m {Δ : SortContext ℒ} (ω I J : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m I ω) <|
      .imp (SecondOrderRelationSyntax.relation_m J I) <|
        .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m I J) <|
          .existsE .set <| .existsE .set <|
            SecondOrderCollapseSyntax.formula_m (up (up J)) (up (up I))
              (.bvar (.there .here)) (.bvar .here)

def sentence_m {Δ : SortContext ℒ} (ω I J : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I J)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I J : Term ℒ [] Δ .set) : (sentence_m ω I J).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, SecondOrderRelationSyntax.relation_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderCollapseSyntax.formula_l, up, Term.eval_weakenBound, Term.eval]
  exact fun hω hI hRelation hJ => exists_l (hℳ := hℳ) hω hI hRelation hJ

theorem derives_m {Δ : SortContext ℒ} (ω I J : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I J)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I J)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseNumericOrderIndex
