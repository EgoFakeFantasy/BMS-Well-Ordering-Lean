import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseSubdomain
import BMSConstructibleBridge.PowerlessBMSQuotientAxioms

/-! # 同一实际成员坍缩的内部序数像

源序数的像不必等于源序数，也不要求源序数的全部成员都在 I 中。
成员递归式运输传递性和原隶属线序。任意 raw 非空子集的原像由
原 Z₂ 图商中的完整公式分离取得，再消费源内部良序的最小元。
没有使用模型外部良基性、I 传递性、Class 资格或源 Collection。
纯对象守卫句另回接原 Derives Z₂，供原历史的阶段资格装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseOrdinals

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  (SecondOrderQuotient.structure_l hℳ)

/-- 最小元覆盖全部内部子集，不仅是已有源类或 I 内的子集。 -/
theorem ordinal_l {I T H α β : type_l hℳ}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hαI : mem_l hℳ α I) (hαβ : SecondOrderFunctionObjects.value_l hℳ H α β)
    (hα : SetTheory.Structure.IsOrdinal 𝒱 α) : SetTheory.Structure.IsOrdinal 𝒱 β := by
  have hRec := hH.2.2.2.1
  have hMember := hH.2.2.2.2.2
  have hSame {a b x y : type_l hℳ}
      (hax : SecondOrderFunctionObjects.value_l hℳ H a x)
      (hby : SecondOrderFunctionObjects.value_l hℳ H b y)
      (hab : SetTheory.Structure.SameMembers 𝒱 a b) :
      SetTheory.Structure.SameMembers 𝒱 x y := by
    have hEq : a = b := SecondOrderQuotient.ext_l hℳ a b hab
    have hxy : x = y := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 (hEq ▸ hax) hby
    subst y
    exact fun _ => Iff.rfl
  have hTrans := PowerlessRelativeMembershipCollapseSubdomain.transitive_l hRec hαI hαβ
    (fun x y hx hy => hα.transitive x hx y hy)
  refine ⟨(fun x hx y hy => hTrans x y hx hy), ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx hxx
      obtain ⟨a, haI, haα, hax⟩ := (hRec α β hαI hαβ x).mp hx
      exact hα.wellOrder.linear.irrefl a haα ((hMember a a x x haI haI hax hax).mpr hxx)
    · intro x hx y hy z hz hxy hyz
      obtain ⟨a, haI, haα, hax⟩ := (hRec α β hαI hαβ x).mp hx
      obtain ⟨b, hbI, hbα, hby⟩ := (hRec α β hαI hαβ y).mp hy
      obtain ⟨c, hcI, hcα, hcz⟩ := (hRec α β hαI hαβ z).mp hz
      exact (hMember a c x z haI hcI hax hcz).mp
        (hα.wellOrder.linear.trans a haα b hbα c hcα
          ((hMember a b x y haI hbI hax hby).mpr hxy)
          ((hMember b c y z hbI hcI hby hcz).mpr hyz))
    · intro x hx y hy
      obtain ⟨a, haI, haα, hax⟩ := (hRec α β hαI hαβ x).mp hx
      obtain ⟨b, hbI, hbα, hby⟩ := (hRec α β hαI hαβ y).mp hy
      rcases hα.wellOrder.linear.compare a haα b hbα with hab | hab | hba
      · exact Or.inl (hSame hax hby hab)
      · exact Or.inr (Or.inl ((hMember a b x y haI hbI hax hby).mp hab))
      · exact Or.inr (Or.inr ((hMember b a y x hbI haI hby hax).mp hba))
  · intro S hSub hNonempty
    let η : Env (SecondOrderQuotient.structure_l hℳ) [.set, .set, .set] [] :=
      Env.empty |>.pushBound I |>.pushBound H |>.pushBound S
    let φ : Formula ℒ [.set, .set, .set, .set] [] :=
      .conj (member_m (.bvar .here) (.bvar (.there (.there (.there .here))))) <|
        .existsE .set <| .conj (member_m (.bvar .here) (.bvar (.there (.there .here))))
          (value_m (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here))
    have hBody (a : type_l hℳ) : φ.satisfies (η.pushBound a) ↔
        mem_l hℳ a I ∧ ∃ x, mem_l hℳ x S ∧ SecondOrderFunctionObjects.value_l hℳ H a x := by
      simp only [φ, Formula.satisfies, SecondOrderObjectSyntax.value_l, member_m, Arguments.eval,
        Term.eval, η, Env.pushBound_bound_here, Env.pushBound_bound_there, SecondOrderQuotient.structure_l]
    obtain ⟨P, hP⟩ := PowerlessBMSQuotientAxioms.separation_l hℳ φ η α
    have hRead (a : type_l hℳ) : mem_l hℳ a P ↔
        mem_l hℳ a α ∧ mem_l hℳ a I ∧
          ∃ x, mem_l hℳ x S ∧ SecondOrderFunctionObjects.value_l hℳ H a x :=
      (hP a).trans (and_congr Iff.rfl (hBody a))
    have hNonemptyP : ∃ a, mem_l hℳ a P := by
      obtain ⟨x, hx⟩ := hNonempty
      obtain ⟨a, haI, haα, hax⟩ := (hRec α β hαI hαβ x).mp (hSub x hx)
      exact ⟨a, (hRead a).mpr ⟨haα, haI, x, hx, hax⟩⟩
    obtain ⟨a, haP, hLeast⟩ := hα.wellOrder.least P (fun b hb => ((hRead b).mp hb).1) hNonemptyP
    obtain ⟨_, haI, x, hx, hax⟩ := (hRead a).mp haP
    refine ⟨x, hx, ?_⟩
    intro y hy
    obtain ⟨b, hbI, hbα, hby⟩ := (hRec α β hαI hαβ y).mp (hSub y hy)
    rcases hLeast b ((hRead b).mpr ⟨hbα, hbI, y, hy, hby⟩) with hab | hab
    · exact Or.inl (hSame hax hby hab)
    · exact Or.inr ((hMember a b x y haI hbI hax hby).mp hab)

def schema_m {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
    .imp (member_m α I) <| .imp (value_m H α β) <|
      .imp (PowerlessRelativeHierarchySyntax.ordinal_m α) (PowerlessRelativeHierarchySyntax.ordinal_m β)

def sentence_m {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m I T H α β)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) :
    (sentence_m I T H α β).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeMembershipCollapse.spec_formula_l,
    SecondOrderObjectSyntax.value_l, member_m, Arguments.eval,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l]
  exact fun hH hαI hαβ hα => ordinal_l hH hαI hαβ hα

theorem derives_m {Δ : SortContext ℒ} (I T H α β : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m I T H α β)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ I T H α β)

#print axioms ordinal_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseOrdinals
