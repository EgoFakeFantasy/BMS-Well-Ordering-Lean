import BMSConstructibleBridge.SecondOrderComparisonStagePreservation

/-! # 同一实际比较历史的良序与前驱初段不变量公式

不变量读取既有 J、T、G，要求当前阶段良序且每个更早阶段为其初段。
归纳用原 Z₂ 分离构造反例集，再用原商正则性取反例极小元，不假定
模型外部良基。真正三分支的归纳步还须装配，不能以归纳接口代替该证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonInvariant

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (value_m member_m)
open SecondOrderQuotient (type_l mem_l)
open SecondOrderWellOrderCoherentUnion (stage_l extension_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def earlier_m {Γ Δ : SortContext ℒ} (J a i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (value_m (up J) (up i) (.bvar .here))
    (member_m (.bvar .here) (up a))

def at_m {Γ Δ : SortContext ℒ} (I J T G a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let i : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let X := .bvar (.there .here)
    let P := .bvar .here
    .imp (.conj (SecondOrderWellOrderCoherentUnion.stage_m (up₃ I) (up₃ T) (up₃ G) i X P)
      (value_m (up₃ J) i (up₃ a))) <|
      .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m X P) <|
        .forallE .set <| .forallE .set <| .forallE .set <|
          let j : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there .here))
          let Y := .bvar (.there .here)
          let Q := .bvar .here
          .imp (.conj (SecondOrderWellOrderCoherentUnion.stage_m (up₃ (up₃ I))
            (up₃ (up₃ T)) (up₃ (up₃ G)) j Y Q) (earlier_m (up₃ (up₃ J)) (up₃ (up₃ a)) j))
            (SecondOrderWellOrderCoherentUnionDerives.extension_m Y Q (up₃ X) (up₃ P))

def at_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I J T G a : carrier_l 𝒩) : Prop :=
  ∀ i X P, stage_l (ℳ₀ := 𝒩) I T G i X P ∧ value_l (ℳ := 𝒩) J i a →
    wellOrder_l (ℳ := 𝒩) X P ∧ ∀ j Y Q,
      stage_l (ℳ₀ := 𝒩) I T G j Y Q ∧
        (∃ b, value_l (ℳ := 𝒩) J j b ∧ member_l 𝒩 b a) →
      extension_l (ℳ₀ := 𝒩) Y Q X P

theorem at_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (I J T G a : Term ℒ Γ Δ .set) :
    (at_m I J T G a).satisfies η ↔ at_l (I.eval η) (J.eval η) (T.eval η) (G.eval η) (a.eval η) := by
  simp only [at_m, at_l, earlier_m, Formula.satisfies,
    SecondOrderWellOrderCoherentUnion.stage_formula_l, value_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderWellOrderCoherentUnionDerives.extension_formula_l, member_m, Arguments.eval,
    up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  at_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem induction_l {A I J T G : type_l hℳ}
    (hTrans : ∀ a, mem_l hℳ a A → ∀ b, mem_l hℳ b a → mem_l hℳ b A)
    (hStep : ∀ a, mem_l hℳ a A →
      (∀ b, mem_l hℳ b a → at_l (𝒩 := 𝒱) I J T G b) → at_l (𝒩 := 𝒱) I J T G a) :
    ∀ a, mem_l hℳ a A → at_l (𝒩 := 𝒱) I J T G a := by
  classical
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree G).pushFree T).pushFree J).pushFree I
  have hFormula a : formula_m.satisfies (η.pushFree a) ↔ at_l (𝒩 := 𝒱) I J T G a :=
    at_formula_l _ _ _ _ _ _
  obtain ⟨S, hS⟩ := (SecondOrderSeparationAxiom.schema_l hℳ (.neg formula_m) η).mp
    (SecondOrderSeparationAxiom.models_l hℳ (.neg formula_m) η) A
  have hRead a : mem_l hℳ a S ↔ mem_l hℳ a A ∧ ¬at_l (𝒩 := 𝒱) I J T G a :=
    (hS a).trans (and_congr Iff.rfl (not_congr (hFormula a)))
  intro a ha
  by_contra hBad
  have hFoundation := SecondOrderFoundation.models_l hℳ
  change ∀ S : type_l hℳ, (∃ x, mem_l hℳ x S) →
    ∃ x, mem_l hℳ x S ∧ ∀ y, mem_l hℳ y x → ¬mem_l hℳ y S at hFoundation
  obtain ⟨x, hx, hMin⟩ := hFoundation S ⟨a, (hRead a).mpr ⟨ha, hBad⟩⟩
  obtain ⟨hxA, hxBad⟩ := (hRead x).mp hx
  apply hxBad
  apply hStep x hxA
  intro y hy
  by_contra hyBad
  exact hMin y hy ((hRead y).mpr ⟨hTrans x hxA y hy, hyBad⟩)

#print axioms at_formula_l
#print axioms induction_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonInvariant
