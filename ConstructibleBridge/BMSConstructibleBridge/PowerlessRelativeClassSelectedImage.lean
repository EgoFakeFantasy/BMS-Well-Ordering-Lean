import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 类内索引集合的有界选取像

索引 S、图 f 和目标界 X 都必须属于实际相对类。对 X 做 Δ₀ 分离即可
取得 f 在 S 上的选取像；规格覆盖环境中的全部元素，而不只类内元素。
不要求 f 是总函数，也不把环境索引集合自动认作类内对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSelectedImage

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def formula_m {Γ Δ : SortContext ℒ} (f S y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists S (PowerlessValueBounded.formula_m
    (f.weakenBound SetTheory.SetSort.set) (.bvar .here) (y.weakenBound SetTheory.SetSort.set))

theorem delta_l {Γ Δ : SortContext ℒ} (f S y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m f S y) :=
  .bounded_exists S (PowerlessValueBounded.delta_l _ _ _)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (f S y : Term ℒ Γ Δ .set) :
    (formula_m f S y).satisfies η ↔ ∃ n,
      ThirdOrderSemantics.member_l 𝒩 n (S.eval η) ∧
        ThirdOrderSemantics.value_l (f.eval η) n (y.eval η) := by
  simp only [formula_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
/-- 类内索引的有界像确实属于类，且拥有环境全元素上的精确规格。 -/
theorem exists_l (f S X : type_l hℳ B) : ∃ Y : type_l hℳ B, ∀ y,
    mem_l hℳ y Y.val ↔ mem_l hℳ y X.val ∧ ∃ n,
      mem_l hℳ n S.val ∧ SecondOrderFunctionObjects.value_l hℳ f.val n y := by
  let ξ : Env (structure_l hℳ B hBase) [] [.set, .set] :=
    ((Env.empty (M := structure_l hℳ B hBase)).pushFree S).pushFree f
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    (delta_l (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)) ξ X
  have hFormula (y : type_l hℳ B) := formula_l (ξ.pushFree y)
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  simp only [ξ, Term.eval] at hFormula
  refine ⟨Y, fun y => ?_⟩
  constructor
  · intro hy
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    obtain ⟨hyX, hBody⟩ := (hY y').mp hy
    obtain ⟨n, hn, hValue⟩ := (hFormula y').mp hBody
    exact ⟨hyX, n.val, hn, (PowerlessRelativeClassFunctionAbsolute.value_l f n y').mp hValue⟩
  · rintro ⟨hyX, n, hn, hValue⟩
    let y' : type_l hℳ B := ⟨y,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hyX⟩
    let n' : type_l hℳ B := ⟨n,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property hn⟩
    exact (hY y').mpr ⟨hyX, (hFormula y').mpr
      ⟨n', hn, (PowerlessRelativeClassFunctionAbsolute.value_l f n' y').mpr hValue⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSelectedImage
