import BMSConstructibleBridge.PowerlessHierarchyLightHistoryUnique
import BMSConstructibleBridge.PowerlessWeakSetInduction

/-! # 任意单值后继图的内部历史相容性

背景仍为原 Z₂，历史采用既有纯 Δ₀ 检查器。后继只消费同一图的单值性，
不要求它读出 Def；零值相同、极限值为精确并。归纳性质沿用原纯公式，
不对模型内部序数作宿主良基归纳，不抽取 Type 层函数或见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionHistoryAgreement

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchyStep (successor_member_l successor_unique_l successor_not_limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def functional_m {Γ Δ : SortContext ℒ} (D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .imp
    (.conj (SecondOrderObjectSyntax.value_m (up (up (up D)))
      (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (SecondOrderObjectSyntax.value_m (up (up (up D)))
        (.bvar (.there (.there .here))) (.bvar .here)))
    (.equal (.bvar (.there .here)) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

def functional_l (D : type_l hℳ) : Prop :=
  ∀ x y z, value_l (ℳ := 𝒱) D x y → value_l (ℳ := 𝒱) D x z → y = z

theorem functional_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (D : Term ℒ Γ Δ .set) :
    (functional_m D).satisfies η ↔ functional_l hℳ (D.eval η) := by
  simp only [functional_m, functional_l, Formula.satisfies, value_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  constructor
  · intro h x y z hxy hxz
    exact h x y z ⟨hxy, hxz⟩
  · intro h x y z hh
    exact h x y z hh.1 hh.2

/-- 图的后继值一致是三分支确定性所需的全部算子条件。 -/
theorem step_l {X D a f g y z : type_l hℳ} (hD : functional_l hℳ D)
    (ha : Ordinal a)
    (hTotalF : ∀ b, mem_l hℳ b a → ∃ d, SecondOrderFunctionObjects.value_l hℳ f b d)
    (hTotalG : ∀ b, mem_l hℳ b a → ∃ d, SecondOrderFunctionObjects.value_l hℳ g b d)
    (hPast : ∀ b, mem_l hℳ b a → ∀ d e,
      SecondOrderFunctionObjects.value_l hℳ f b d →
        SecondOrderFunctionObjects.value_l hℳ g b e → d = e)
    (hy : PowerlessHierarchyLightHistory.step_l hℳ X D f a y)
    (hz : PowerlessHierarchyLightHistory.step_l hℳ X D g a z) : y = z := by
  rcases hy with ⟨hEmpty, hy⟩ | ⟨b, d, hb, hd, hDy⟩ | ⟨hLimit, hUnion⟩
  · rcases hz with ⟨_, hz⟩ | ⟨b, _, hb, _, _⟩ | ⟨hLimit, _⟩
    · exact hy.trans hz.symm
    · exact False.elim (hEmpty b (successor_member_l hℳ hb))
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
  · rcases hz with ⟨hEmpty, _⟩ | ⟨c, e, hc, he, hDz⟩ | ⟨hLimit, _⟩
    · exact False.elim (hEmpty b (successor_member_l hℳ hb))
    · have hbc := successor_unique_l hℳ ha hb hc
      subst c
      have hde := hPast b (successor_member_l hℳ hb) d e hd he
      subst e
      exact hD d y z hDy hDz
    · exact False.elim (successor_not_limit_l hℳ ha hb hLimit)
  · rcases hz with ⟨hEmpty, _⟩ | ⟨b, _, hb, _, _⟩ | ⟨_, hUnion'⟩
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
    · exact False.elim (successor_not_limit_l hℳ ha hb hLimit)
    · apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx
        obtain ⟨b, d, hb, hd, hxd⟩ := (hUnion x).mp hx
        obtain ⟨e, he⟩ := hTotalG b hb
        have hde := hPast b hb d e hd he
        exact (hUnion' x).mpr ⟨b, e, hb, he, hde ▸ hxd⟩
      · intro hx
        obtain ⟨b, e, hb, he, hxe⟩ := (hUnion' x).mp hx
        obtain ⟨d, hd⟩ := hTotalF b hb
        have hde := hPast b hb d e hd he
        exact (hUnion x).mpr ⟨b, d, hb, hd, hde.symm ▸ hxe⟩

/-- 母序数与陪域均可不同；比较覆盖任意共同内部阶段。 -/
theorem agreement_l {X D A A' f g C C' : type_l hℳ}
    (hD : functional_l hℳ D) (hA : Ordinal A) (hA' : Ordinal A')
    (hf : PowerlessHierarchyLightHistory.history_l hℳ X D A C f)
    (hg : PowerlessHierarchyLightHistory.history_l hℳ X D A' C' g) :
    ∀ a, PowerlessRelativeHierarchyAgreement.point_l hℳ A A' f g a := by
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree g |>.pushFree f |>.pushFree A' |>.pushFree A
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    PowerlessRelativeHierarchyAgreement.induction_m η
    (fun a ih => (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ A A' f g a).mpr (by
      rintro ⟨haA, haA'⟩ y z ⟨hy, hz⟩
      have ha : Ordinal a := SetTheory.Structure.IsOrdinal.mem hA haA
      have hTotalF b (hb : mem_l hℳ b a) : ∃ d, SecondOrderFunctionObjects.value_l hℳ f b d := by
        obtain ⟨d, ⟨_, hd⟩, _⟩ := hf.1.2 b (hA.transitive a haA b hb)
        exact ⟨d, hd⟩
      have hTotalG b (hb : mem_l hℳ b a) : ∃ d, SecondOrderFunctionObjects.value_l hℳ g b d := by
        obtain ⟨d, ⟨_, hd⟩, _⟩ := hg.1.2 b (hA'.transitive a haA' b hb)
        exact ⟨d, hd⟩
      have hPast b (hb : mem_l hℳ b a) d e
          (hd : SecondOrderFunctionObjects.value_l hℳ f b d)
          (he : SecondOrderFunctionObjects.value_l hℳ g b e) : d = e :=
        (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ A A' f g b).mp (ih b hb)
          ⟨hA.transitive a haA b hb, hA'.transitive a haA' b hb⟩ d e ⟨hd, he⟩
      exact step_l hℳ hD ha hTotalF hTotalG hPast
        (hf.2 a y ⟨haA, hy⟩) (hg.2 a z ⟨haA', hz⟩)))
  exact fun a => (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ A A' f g a).mp (hAll a)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionHistoryAgreement
