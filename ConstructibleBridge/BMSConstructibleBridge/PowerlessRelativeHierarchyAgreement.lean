import BMSConstructibleBridge.PowerlessRelativeHierarchyStep
import BMSConstructibleBridge.PowerlessWeakSetInduction

/-! # 任意纯集合历史在共同阶段上相容

归纳性质是实际纯隶属公式。只使用已验证的弱集合论集合归纳模式，比较
任意两张集合函数图；母序数和输出界可以不同，不假定宿主外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyAgreement

open Logic FirstOrder SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) := SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (A A' f g a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (.conj (member_m a A) (member_m a A')) <|
    .forallE .set <| .forallE .set <| .imp
      (.conj (value_m (up (up f)) (up (up a)) (.bvar (.there .here)))
        (value_m (up (up g)) (up (up a)) (.bvar .here)))
      (.equal (.bvar (.there .here)) (.bvar .here))

def point_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (A A' f g a : type_l hℳ) : Prop :=
  mem_l hℳ a A ∧ mem_l hℳ a A' → ∀ y z,
    SecondOrderFunctionObjects.value_l hℳ f a y ∧ SecondOrderFunctionObjects.value_l hℳ g a z → y = z

theorem point_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (quotient_l hℳ) Γ Δ) (A A' f g a : Term ℒ Γ Δ .set) :
    (point_m A A' f g a).satisfies η ↔ point_l hℳ (A.eval η) (A'.eval η) (f.eval η) (g.eval η) (a.eval η) := by
  simp only [point_m, up, Formula.satisfies, SecondOrderObjectSyntax.value_l hℳ,
    member_m, Arguments.eval, Term.eval, Term.eval_weakenBound]
  rfl

def induction_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  point_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)

theorem induction_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (A A' f g a : type_l hℳ) :
    induction_m.satisfies (Env.empty (M := quotient_l hℳ) |>.pushFree g |>.pushFree f
      |>.pushFree A' |>.pushFree A |>.pushFree a) ↔ point_l hℳ A A' f g a :=
  point_formula_l hℳ _ _ _ _ _ _

theorem agree_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B A A' f g r r' : type_l hℳ}
    (hA : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) A)
    (hA' : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) A')
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B A f r)
    (hg : PowerlessRelativeHierarchySemantics.history_l hℳ B A' g r') : ∀ a, point_l hℳ A A' f g a := by
  let η : Env (quotient_l hℳ) [] [.set, .set, .set, .set] :=
    Env.empty (M := quotient_l hℳ) |>.pushFree g |>.pushFree f |>.pushFree A' |>.pushFree A
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) induction_m η
    (fun a ih => (induction_formula_l hℳ A A' f g a).mpr (by
      rintro ⟨haA, haA'⟩ y z ⟨hy, hz⟩
      have ha : SetTheory.Structure.IsOrdinal
          (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (quotient_l hℳ)) a := by
        apply SetTheory.Structure.IsOrdinal.mem hA
        exact haA
      have hTotalF b (hb : mem_l hℳ b a) : ∃ d, SecondOrderFunctionObjects.value_l hℳ f b d := by
        obtain ⟨d, ⟨_, hd⟩, _⟩ := hf.1.2 b (hA.transitive a haA b hb)
        exact ⟨d, hd⟩
      have hTotalG b (hb : mem_l hℳ b a) : ∃ d, SecondOrderFunctionObjects.value_l hℳ g b d := by
        obtain ⟨d, ⟨_, hd⟩, _⟩ := hg.1.2 b (hA'.transitive a haA' b hb)
        exact ⟨d, hd⟩
      have hPast b (hb : mem_l hℳ b a) d e
          (hd : SecondOrderFunctionObjects.value_l hℳ f b d) (he : SecondOrderFunctionObjects.value_l hℳ g b e) : d = e :=
        (induction_formula_l hℳ A A' f g b).mp (ih b hb)
          ⟨hA.transitive a haA b hb, hA'.transitive a haA' b hb⟩ d e ⟨hd, he⟩
      exact PowerlessRelativeHierarchyStep.unique_l hℳ ha hTotalF hTotalG hPast
        (hf.2 a y ⟨haA, hy⟩) (hg.2 a z ⟨haA', hz⟩)))
  intro a
  exact (induction_formula_l hℳ A A' f g a).mp (hAll a)

theorem level_unique_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B a y z : type_l hℳ}
    (hy : PowerlessRelativeHierarchySemantics.level_l hℳ B a y)
    (hz : PowerlessRelativeHierarchySemantics.level_l hℳ B a z) : y = z := by
  obtain ⟨A, f, r, hA, ha, hf, hy⟩ := hy
  obtain ⟨A', g, r', hA', ha', hg, hz⟩ := hz
  exact agree_l hℳ hA hA' hf hg a ⟨ha, ha'⟩ y z ⟨hy, hz⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeHierarchyAgreement
