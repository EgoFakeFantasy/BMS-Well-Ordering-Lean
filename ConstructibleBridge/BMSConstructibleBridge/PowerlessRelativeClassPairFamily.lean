import BMSConstructibleBridge.PowerlessRelativeClassProduct
import BMSConstructibleBridge.PowerlessRelativeClassBasicAxioms

/-! # 类参数上全部无序对的实际集合

无序对族等于 Kuratowski 笛卡尔积的并集；单元素集合也由对角无序对
覆盖。因此不需要幂集、Collection 或额外的函数像公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPairFamily

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (X p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists X <| membershipLevyBound.boundedExists (up X) <|
    PowerlessPairBounded.pair_m (.bvar (.there .here)) (.bvar .here) (up (up p))

theorem delta_l {Γ Δ : SortContext ℒ} (X p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m X p) :=
  .bounded_exists X (.bounded_exists (up X) (PowerlessPairBounded.pair_delta_l _ _ _))

theorem body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (X p : Term ℒ Γ Δ .set) : (body_m X p).satisfies η ↔
      ∃ a b, member_l 𝒩 a (X.eval η) ∧ member_l 𝒩 b (X.eval η) ∧
        pair_l (ℳ := 𝒩) a b (p.eval η) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.pair_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨a, ha, b, hb, hp⟩ => ⟨a, b, ha, hb, hp⟩,
    fun ⟨a, b, ha, hb, hp⟩ => ⟨a, ha, b, hb, hp⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem pair_unique_l {a b p q : type_l hℳ B}
    (hp : pair_l (ℳ := structure_l hℳ B hBase) a b p)
    (hq : pair_l (ℳ := structure_l hℳ B hBase) a b q) : p = q :=
  Subtype.ext (SecondOrderPairObjects.pair_unique_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) a b p).mp hp)
    ((PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) a b q).mp hq))

theorem exists_l (X : type_l hℳ B) : ∃ Q : type_l hℳ B, ∀ p : type_l hℳ B,
    mem_l hℳ p.val Q.val ↔ ∃ a b : type_l hℳ B,
      mem_l hℳ a.val X.val ∧ mem_l hℳ b.val X.val ∧ pair_l (ℳ := structure_l hℳ B hBase) a b p := by
  obtain ⟨P, hP⟩ := PowerlessRelativeClassProduct.exists_l hBase X X
  have hUnion := PowerlessRelativeClassBasicAxioms.union_l hℳ B hBase
  change ∀ A : type_l hℳ B, ∃ U : type_l hℳ B, ∀ z : type_l hℳ B,
    mem_l hℳ z.val U.val ↔ ∃ y : type_l hℳ B, mem_l hℳ y.val A.val ∧ mem_l hℳ z.val y.val at hUnion
  obtain ⟨Q, hQ⟩ := hUnion P
  refine ⟨Q, fun p => (hQ p).trans ⟨?_, ?_⟩⟩
  · rintro ⟨r, hr, hpr⟩
    obtain ⟨a, b, ha, hb, s, t, hs, ht, hrPair⟩ := (hP r).mp hr
    rcases (hrPair p).mp hpr with rfl | rfl
    · exact ⟨a, a, ha, ha, hs⟩
    · exact ⟨a, b, ha, hb, ht⟩
  · rintro ⟨a, b, ha, hb, hp⟩
    obtain ⟨r, hr⟩ := SecondOrderPairObjects.ordered_exists_l hℳ a.val b.val
    let r' : type_l hℳ B := ⟨r, PowerlessRelativeClassPair.ordered_l hℳ hBase a.property b.property hr⟩
    have hr' := (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) a b r').mpr hr
    have hrP := (hP r').mpr ⟨a, b, ha, hb, hr'⟩
    obtain ⟨s, t, _, ht, hrPair⟩ := hr'
    have htp := pair_unique_l ht hp
    exact ⟨r', hrP, (hrPair p).mpr (Or.inr htp.symm)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPairFamily
