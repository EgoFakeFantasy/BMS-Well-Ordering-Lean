import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseOrdinals
import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.SecondOrderOrdinalComparison

/-! # 同一实际成员坍缩不增大序数

纯公式的内部集合归纳证明 H(α)⊆α，不假定 I 传递或覆盖 α 的全部成员。
归纳对象及比较均在任意原 Z₂ 模型的图商中；不用模型外部良基性、
ClassH、Collection 或 Type 选择。保留原 H，并回接原对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseOrdinalBound

open Logic FirstOrder
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (I H α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (member_m α I) <| .imp (PowerlessRelativeHierarchySyntax.ordinal_m α) <|
    .forallE .set <| .imp (value_m (up H) (up α) (.bvar .here))
      (ThirdOrderTheory.subset_m (.bvar .here) (up α))

def point_l (I H α : type_l hℳ) : Prop :=
  mem_l hℳ α I →
    SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (SecondOrderQuotient.structure_l hℳ)) α →
      ∀ β, SecondOrderFunctionObjects.value_l hℳ H α β →
        ∀ x, mem_l hℳ x β → mem_l hℳ x α

theorem point_formula_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (I H α : Term ℒ Γ Δ .set) :
    (point_m I H α).satisfies η ↔ point_l (I.eval η) (H.eval η) (α.eval η) := by
  simp only [point_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    SecondOrderObjectSyntax.value_l, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l, up, Term.eval_weakenBound]
  rfl

/-- 首自由槽为归纳对象，另外两槽保持同一个 I/H。 -/
def induction_m : Formula ℒ [] [.set, .set, .set] :=
  point_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)

theorem subset_l {I T H α β : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hαI : mem_l hℳ α I) (hαβ : SecondOrderFunctionObjects.value_l hℳ H α β)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (SecondOrderQuotient.structure_l hℳ)) α) : ∀ x, mem_l hℳ x β → mem_l hℳ x α := by
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] :=
    Env.empty |>.pushFree H |>.pushFree I
  have hAll : ∀ a, induction_m.satisfies (η.pushFree a) := by
    apply PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    intro a ih
    apply (point_formula_l (η.pushFree a) _ _ _).mpr
    intro haI ha b hab x hxb
    obtain ⟨c, hcI, hca, hcx⟩ := (hH.2.2.2.1 a b haI hab x).mp hxb
    have hc : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) c := by
      apply SetTheory.Structure.IsOrdinal.mem ha
      exact hca
    have hx := PowerlessRelativeMembershipCollapseOrdinals.ordinal_l hH hcI hcx hc
    have hxc := (point_formula_l (η.pushFree c) _ _ _).mp (ih c hca) hcI hc x hcx
    rcases SecondOrderOrdinalComparison.compare_l hℳ hx hc with h | h | h
    · exact h.symm ▸ hca
    · exact ha.transitive c hca x h
    · have hcc := hxc c h
      exact False.elim (hc.wellOrder.linear.irrefl c hcc hcc)
  exact (point_formula_l (η.pushFree α) _ _ _).mp (hAll α) hαI hα β hαβ

/-- 原序数像不超过源序数；等号可能成立，不能无故强化成严格小于。 -/
theorem le_l {I T H α β : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hαI : mem_l hℳ α I) (hαβ : SecondOrderFunctionObjects.value_l hℳ H α β)
    (hα : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (SecondOrderQuotient.structure_l hℳ)) α) : β = α ∨ mem_l hℳ β α := by
  have hβ := PowerlessRelativeMembershipCollapseOrdinals.ordinal_l hH hαI hαβ hα
  rcases SecondOrderOrdinalComparison.compare_l hℳ hβ hα with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hαα := subset_l hH hαI hαβ hα α h
    exact False.elim (hα.wellOrder.linear.irrefl α hαα hαα)

def schema_m {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
    .imp (member_m α I) <| .imp (value_m H α β) <|
      .imp (PowerlessRelativeHierarchySyntax.ordinal_m α)
        (.conj (ThirdOrderTheory.subset_m β α) (.disj (.equal β α) (member_m β α)))

def sentence_m {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m I T H α β)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) :
    (sentence_m I T H α β).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeMembershipCollapse.spec_formula_l,
    SecondOrderObjectSyntax.value_l, member_m, Arguments.eval,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l]
  exact fun hH hαI hαβ hα => ⟨subset_l hH hαI hαβ hα, le_l hH hαI hαβ hα⟩

theorem derives_m {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m I T H α β)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ I T H α β)

#print axioms point_formula_l
#print axioms subset_l
#print axioms le_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseOrdinalBound
