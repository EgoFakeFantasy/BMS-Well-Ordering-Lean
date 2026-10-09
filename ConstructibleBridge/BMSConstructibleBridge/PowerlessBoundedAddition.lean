import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequences
import BMSConstructibleBridge.SecondOrderFiniteAdditionAgreement
import BMSConstructibleBridge.SecondOrderFunctionRestriction
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 以全部有限自然数序列集为界的加法关系

统一参数 S 只含有限图，无须收集所有初值的无限加法图。Δ₀ 检查式仍精确
读取原 Z₂ 加法，有限长度与候选输出均不要求外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedAddition

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω e S a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists S <| .conj
    (PowerlessAdditionTraceBounded.formula_m (up ω) (up e) (up a) (up b) (.bvar .here))
    (PowerlessValueBounded.formula_m (.bvar .here) (up b) (up c))

theorem delta_l {Γ Δ : SortContext ℒ} (ω e S a b c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e S a b c) :=
  .bounded_exists S (.conj (PowerlessAdditionTraceBounded.delta_l _ _ _ _ _)
    (PowerlessValueBounded.delta_l _ _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S a b c : carrier_l 𝒩) : Prop :=
  ∃ g, member_l 𝒩 g S ∧ PowerlessAdditionTraceBounded.trace_l (𝒩 := 𝒩) ω e a b g ∧
    value_l (ℳ := 𝒩) g b c

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S a b c : Term ℒ Γ Δ .set) : (formula_m ω e S a b c).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (S.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessAdditionTraceBounded.formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem restriction_l (K : source_coding_l hℳ) {a F : type_l hℳ}
    (hF : PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a F)
    (hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F K.omega K.omega)
    (n : SecondOrderModel.num_l ℳ) : ∃ g,
      PowerlessAdditionTraceBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a (numberCode_l K n).val g ∧
      ∀ x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g x y ↔
        mem_l hℳ x (numberCode_l K (SecondOrderModel.succ_l n)).val ∧
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x y := by
  let e := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  let m := (numberCode_l K (SecondOrderModel.succ_l n)).val
  obtain ⟨g, hg, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ (S := m) hMap
    (fun x hx => SecondOrderOmegaTransitive.member_l hℳ (k := m) K.omega_spec
      (numberCode_l K (SecondOrderModel.succ_l n)).property hx)
  have hg' : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g m K.omega := hg
  have hRead' (x y : type_l hℳ) : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g x y ↔
      mem_l hℳ x m ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x y := hRead x y
  obtain ⟨_, _, h₀, hStep⟩ := hF
  refine ⟨g, ⟨m, (numberCode_l K (SecondOrderModel.succ_l n)).property,
    PowerlessBMSQuotientSuccessor.successor_l K n, hg', ?_, ?_⟩, hRead'⟩
  · exact (hRead' e a).mpr ⟨(numberCode_mem_iff_lt_l K _ _).mpr (SecondOrderOrder.zero_succ_l hℳ n), h₀⟩
  · intro k hk l _ x _ y _ hkl hx hy
    apply (PowerlessAddition.step_formula_l K.omega x y).mp
    exact hStep k l x y
      (SecondOrderOmegaTransitive.member_l hℳ (k := (numberCode_l K n).val) K.omega_spec
        (numberCode_l K n).property hk) hkl ((hRead' k x).mp hx).2 ((hRead' l y).mp hy).2

theorem instance_l (K : source_coding_l hℳ) {S : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (i j : SecondOrderModel.num_l ℳ) (c : type_l hℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val S (numberCode_l K i).val (numberCode_l K j).val c ↔
        c = (numberCode_l K (SecondOrderModel.add_l i j)).val := by
  obtain ⟨F, hF, hMap⟩ := PowerlessBMSQuotientArithmetic.additionIteration_exists_l K i
  constructor
  · rintro ⟨g, _, hg, hc⟩
    have hg' := (PowerlessRelativeClassFiniteTraceAbsolute.ambient_equiv_l
      (n := (numberCode_l K j).val) (g := g) K.omega_spec
      (numberCode_l K j).property).mp hg
    exact (PowerlessBMSQuotientRecursion.addition_iff_l K i j c).mp
      ⟨F, hF, SecondOrderFiniteAdditionAgreement.value_l K hF (numberCode_l K j).property hg' hc⟩
  · rintro rfl
    obtain ⟨g, hg, hRead⟩ := restriction_l K hF hMap j
    have hgS : member_l (SecondOrderQuotient.structure_l hℳ) g S := by
      obtain ⟨m, hmω, _, hgMap, _, _⟩ := hg
      exact (hS g).mpr ⟨m, hmω, hgMap⟩
    obtain ⟨y, hy, _⟩ := hMap.2 (numberCode_l K j).val (numberCode_l K j).property
    have hyEq := (PowerlessBMSQuotientRecursion.addition_iff_l K i j y).mp ⟨F, hF, hy.2⟩
    refine ⟨g, hgS, hg, (hRead _ _).mpr ⟨?_, hyEq ▸ hy.2⟩⟩
    exact (PowerlessBMSQuotientSuccessor.successor_l K j (numberCode_l K j).val).mpr (Or.inr rfl)

#print axioms instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedAddition
