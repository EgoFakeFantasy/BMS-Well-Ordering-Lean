import BMSConstructibleBridge.PowerlessRelativeLimitFunctionExtension
import BMSConstructibleBridge.SecondOrderFunctionRestriction
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 任意内部有限函数图的共同极限层界

归纳公式量化全部原商图，不预设图属于相对类。每一步先限制到前驱域，
用归纳假设取得旧图的层界，再在同一极限层添加末项。
归纳来自原 Z₂ 的实际公式实例，覆盖非标准内部长度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteMaps

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

def template_m : Formula ℒ [] [.set, .set, .set] := .forallE .set (.imp
  (SecondOrderObjectSyntax.map_m (.bvar .here) (.fvar .here) (.fvar (.there (.there .here))))
  (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here))))

theorem template_formula_l (n C X : type_l hℳ) : template_m.satisfies
    ((((Env.empty (M := quotient_l)).pushFree X).pushFree C).pushFree n) ↔
      ∀ f, map_l (ℳ := quotient_l) f n X → mem_l hℳ f C := by
  simp only [template_m, Formula.satisfies, map_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval]
  rfl

/-- 陪域只须包含于极限层；不要求陪域自身也是该层成员。 -/
theorem subset_member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (K : source_coding_l hℳ) (hωC : mem_l hℳ K.omega C)
    (hXC : ∀ x, mem_l hℳ x X → mem_l hℳ x C)
    {n f : type_l hℳ} (hn : mem_l hℳ n K.omega) (hf : map_l (ℳ := quotient_l) f n X) :
    mem_l hℳ f C := by
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  let η : Env quotient_l [] [.set, .set] := ((Env.empty).pushFree X).pushFree C
  have h := PowerlessBMSQuotientInduction.induction_l K template_m η ?_ ?_
  · obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n, hn⟩
    have hi' : (numberCode_l K i).val = n := congrArg Subtype.val hi
    exact (template_formula_l n C X).mp (hi' ▸ h i) f hf
  · apply (template_formula_l _ C X).mpr
    intro f hf
    have he := PowerlessBMSQuotientSuccessor.zero_l K
    have hEq : f = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val :=
      SecondOrderQuotient.ext_l hℳ _ _ fun p => iff_of_false
        (fun hp => by obtain ⟨x, _, hx, _, _⟩ := hf.1 p hp; exact he x hx) (he p)
    exact hEq.symm ▸ hTrans K.omega hωC _ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  · intro i hi
    apply (template_formula_l _ C X).mpr
    intro f hf
    let n := (numberCode_l K i).val
    let m := (numberCode_l K (SecondOrderModel.succ_l i)).val
    have hm : PowerlessNatural.successor_l (ℳ := quotient_l) n m :=
      PowerlessBMSQuotientSuccessor.successor_l K i
    obtain ⟨g, hg, hValue⟩ := SecondOrderFunctionRestriction.exists_l hℳ hf
      (fun x hx => (hm x).mpr (Or.inl hx))
    have hgC := (template_formula_l n C X).mp hi g hg
    obtain ⟨d, hd, _⟩ := hf.2 n ((hm n).mpr (Or.inr rfl))
    obtain ⟨g', hg'C, hg', hValue'⟩ := PowerlessRelativeLimitFunctionExtension.exists_l hℳ
      hBase hLimit hC hgC (hTrans K.omega hωC n (numberCode_l K i).property)
      (hXC d hd.1) hg (fun hnn => SecondOrderNaturalCases.asymmetry_l hℳ hnn hnn) hd.1 hm
    have hg'' : map_l (ℳ := quotient_l) g' m X := hg'
    have hEq : f = g' := PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ)
      (A := m) (B := X) (D := X) hf hg'' (by
      intro x y
      change SecondOrderFunctionObjects.value_l hℳ f x y ↔ SecondOrderFunctionObjects.value_l hℳ g' x y
      rw [hValue' x y]
      constructor
      · intro hxy
        rcases (hm x).mp (SecondOrderFunctionProperties.value_mem_l hℳ hf hxy).1 with hx | hx
        · exact Or.inl ((hValue x y).mpr ⟨hx, hxy⟩)
        · subst x
          exact Or.inr ⟨rfl, SecondOrderFunctionProperties.value_unique_l hℳ hf hxy hd.2⟩
      · rintro (hxy | ⟨rfl, rfl⟩)
        · exact ((hValue x y).mp hxy).2
        · exact hd.2)
    exact hEq.symm ▸ hg'C

/-- 保留原成员陪域接口，作为更一般的子集陪域定理的推论。 -/
theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (K : source_coding_l hℳ) (hωC : mem_l hℳ K.omega C) (hXC : mem_l hℳ X C)
    {n f : type_l hℳ} (hn : mem_l hℳ n K.omega) (hf : map_l (ℳ := quotient_l) f n X) :
    mem_l hℳ f C :=
  subset_member_l hℳ hBase hLimit hC K hωC
    (fun x hx => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC X hXC x hx) hn hf

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteMaps
