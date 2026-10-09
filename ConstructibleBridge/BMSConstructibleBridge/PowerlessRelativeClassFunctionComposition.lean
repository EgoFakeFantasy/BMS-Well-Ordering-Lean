import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 相对类中集合函数图的复合

中间量词由陪域界定，因而实际复合图使用类内 Δ₀ 关系图接口构造。
没有对宿主函数进行选择，也不要求类模型满足完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionComposition

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem value_unique_l {F A D x y z : type_l hℳ B}
    (hF : map_l (ℳ := structure_l hℳ B hBase) F A D)
    (hy : value_l (ℳ := structure_l hℳ B hBase) F x y)
    (hz : value_l (ℳ := structure_l hℳ B hBase) F x z) : y = z :=
  Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F A D).mp hF)
    ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F x y).mp hy)
    ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F x z).mp hz))

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  membershipLevyBound.boundedExists (.fvar (.there (.there .here))) (.conj
    (PowerlessValueBounded.formula_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.bvar .here))
    (PowerlessValueBounded.formula_m (.fvar (.there (.there (.there (.there .here))))) (.bvar .here) (.fvar (.there .here))))

theorem delta_l : Formula.IsDelta0 membershipLevyBound formula_m :=
  .bounded_exists _ (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _))

theorem formula_l (F G D x y : type_l hℳ B) : formula_m.satisfies
    ((((((Env.empty (M := structure_l hℳ B hBase)).pushFree G).pushFree F).pushFree D).pushFree y).pushFree x) ↔
      ∃ z : type_l hℳ B, mem_l hℳ z.val D.val ∧
        value_l (ℳ := structure_l hℳ B hBase) F x z ∧ value_l (ℳ := structure_l hℳ B hBase) G z y := by
  simp only [formula_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
  rfl

theorem exists_l {F G A D E : type_l hℳ B}
    (hF : map_l (ℳ := structure_l hℳ B hBase) F A D)
    (hG : map_l (ℳ := structure_l hℳ B hBase) G D E) :
    ∃ H : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) H A E ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) H x y ↔
        mem_l hℳ x.val A.val ∧ mem_l hℳ y.val E.val ∧ ∃ z : type_l hℳ B,
          mem_l hℳ z.val D.val ∧ value_l (ℳ := structure_l hℳ B hBase) F x z ∧
            value_l (ℳ := structure_l hℳ B hBase) G z y := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    (((Env.empty).pushFree G).pushFree F).pushFree D
  obtain ⟨H, hH, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l (hBase := hBase) delta_l η A E (by
    intro x hx
    obtain ⟨z, hz, _⟩ := hF.2 x hx
    obtain ⟨y, hy, _⟩ := hG.2 z hz.1
    refine ⟨y, ⟨hy.1, (formula_l F G D x y).mpr ⟨z, hz.1, hz.2, hy.2⟩⟩, ?_⟩
    intro y' hy'
    obtain ⟨z', _, hz', hzy'⟩ := (formula_l F G D x y').mp hy'.2
    have hEq : z' = z := value_unique_l hF hz' hz.2
    subst z'
    exact value_unique_l hG hzy' hy.2)
  exact ⟨H, hH, fun x y => (hRead x y).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (formula_l F G D x y)))⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionComposition
