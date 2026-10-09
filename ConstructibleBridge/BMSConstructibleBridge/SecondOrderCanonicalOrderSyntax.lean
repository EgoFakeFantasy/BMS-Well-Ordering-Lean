import BMSConstructibleBridge.SecondOrderCanonicalIndexUnique
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalOrderStep

/-! # 规范候选及完整扩张步骤的纯对象语言

候选中的指标、查询、行族、比较图、包含关系和良序均量化完整模型。
相对类构造通过已证绝对性进入该关系，不把类守卫偷偷留在对象句中。
本文件给出精确语义对应；步骤存在与历史构造仍另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderSyntax

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up (up (up t)))))

def queryRead_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A S I R J Q : carrier_l ℳ₀) : Prop :=
  ∀ t x, value_l Q t x ↔ member_l ℳ₀ t J ∧ member_l ℳ₀ x A ∧
    PowerlessRelativeClassSatisfactionAllSlots.query_l ω A S I R t x

def queryRead_m {Γ Δ : SortContext ℒ} (ω A S I R J Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .forallE .set <| .forallE .set <|
    .iff (value_m (w Q) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (w J)) <|
        .conj (member_m (.bvar .here) (w A)) <|
          PowerlessRelativeClassSatisfactionAllSlots.query_m
            (w ω) (w A) (w S) (w I) (w R) (.bvar (.there .here)) (.bvar .here)

theorem queryRead_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A S I R J Q : Term ℒ Γ Δ .set) :
    (queryRead_m ω A S I R J Q).satisfies η ↔
      queryRead_l (ω.eval η) (A.eval η) (S.eval η) (I.eval η) (R.eval η) (J.eval η) (Q.eval η) := by
  simp only [queryRead_m, queryRead_l, Formula.satisfies, value_formula_l,
    PowerlessRelativeClassSatisfactionAllSlots.query_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def candidate_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P R D L : carrier_l ℳ₀) : Prop :=
  ∃ S I J U Q Y, PowerlessRelativeClassSatisfactionIndexCanonical.spec_l ω A P S I J U ∧
    queryRead_l ω A S I R J Q ∧ PowerlessRelativeClassRowOrderCanonical.family_l J A Q Y ∧
    PowerlessRelativeClassRowOrderCanonical.graph_l J U A Q Y L ∧ subset_l D Y ∧ wellOrder_l Y L

def candidate_m {Γ Δ : SortContext ℒ} (ω A P R D L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let I := .bvar (.there (.there (.there (.there .here))))
      let J := .bvar (.there (.there (.there .here)))
      let U := .bvar (.there (.there .here))
      let Q := .bvar (.there .here)
      let Y := .bvar .here
      .conj (PowerlessCanonicalIndexSyntax.spec_m (up₆ ω) (up₆ A) (up₆ P) S I J U) <|
        .conj (queryRead_m (up₆ ω) (up₆ A) S I (up₆ R) J Q) <|
          .conj (SecondOrderRowOrderCanonical.family_m J (up₆ A) Q Y) <|
            .conj (SecondOrderRowOrderCanonical.graph_m J U (up₆ A) Q Y (up₆ L)) <|
              .conj (ThirdOrderTheory.subset_m (up₆ D) Y)
                (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m Y (up₆ L))

theorem candidate_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A P R D L : Term ℒ Γ Δ .set) :
    (candidate_m ω A P R D L).satisfies η ↔
      candidate_l (ω.eval η) (A.eval η) (P.eval η) (R.eval η) (D.eval η) (L.eval η) := by
  simp only [candidate_m, candidate_l, Formula.satisfies, PowerlessCanonicalIndexSyntax.spec_formula_l,
    queryRead_formula_l, SecondOrderRowOrderCanonical.family_formula_l,
    SecondOrderRowOrderCanonical.graph_formula_l, subset_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    up₆, up, Term.eval_weakenBound, Term.eval]
  rfl

def step_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A P R D E : carrier_l ℳ₀) : Prop :=
  ∃ L, candidate_l ω A P R D L ∧ SecondOrderWellOrderEndExtensionUnique.graph_l A D P L E

def step_m {Γ Δ : SortContext ℒ} (ω A P R D E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
    .conj (candidate_m (up ω) (up A) (up P) (up R) (up D) (.bvar .here))
      (SecondOrderWellOrderEndExtensionUnique.graph_m (up A) (up D) (up P) (.bvar .here) (up E))

theorem step_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A P R D E : Term ℒ Γ Δ .set) :
    (step_m ω A P R D E).satisfies η ↔
      step_l (ω.eval η) (A.eval η) (P.eval η) (R.eval η) (D.eval η) (E.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, candidate_formula_l,
    SecondOrderWellOrderEndExtensionUnique.graph_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem candidate_ambient_l {ω A P R D L : PowerlessRelativeClassStructure.type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒞) ω)
    (h : PowerlessRelativeClassCanonicalOrderStep.candidate_l (hBase := hBase) ω A P R D L) :
    candidate_l (ℳ₀ := 𝒱) ω.val A.val P.val R.val D.val L.val := by
  obtain ⟨S, I, J, U, Q, Y, hIndex, hRead, hFamily, hGraph, hSubset, hOrder⟩ := h
  exact ⟨S.val, I.val, J.val, U.val, Q.val, Y.val,
    PowerlessCanonicalIndexAbsolute.spec_absolute_l hΩ hIndex, hRead,
    SecondOrderRowOrderCanonical.family_ambient_l hFamily, hGraph, hSubset, hOrder⟩

theorem step_ambient_l {ω A P R D E : PowerlessRelativeClassStructure.type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒞) ω)
    (h : PowerlessRelativeClassCanonicalOrderStep.step_l (hBase := hBase) ω A P R D E) :
    step_l (ℳ₀ := 𝒱) ω.val A.val P.val R.val D.val E.val := by
  obtain ⟨L, hL, hGraph⟩ := h
  exact ⟨L.val, candidate_ambient_l hΩ hL, hGraph⟩

#print axioms candidate_formula_l
#print axioms step_formula_l
#print axioms step_ambient_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderSyntax
