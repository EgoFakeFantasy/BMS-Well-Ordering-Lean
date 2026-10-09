import BMSConstructibleBridge.SecondOrderFunctionRestriction
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.PowerlessBMSQuotientRecursion
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionRange

/-! # 同一原比较图的纯前缀及实际值界

前缀是实际干净函数图，不是宿主限制函数。原陪域 q 可以留在 raw 环境；
完整读数直接指定原图的全部坐标。极限前缀的逐值母界由较早前缀的真实
成员界及同层值域封闭取得，不预设当前前缀已属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderRawPrefix

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (G q α f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessMapBounded.formula_m f α q) <| .forallE .set <| .forallE .set <|
    .iff (PowerlessValueBounded.formula_m (up (up f)) (.bvar (.there .here)) (.bvar .here))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up α)))
        (PowerlessValueBounded.formula_m (up (up G)) (.bvar (.there .here)) (.bvar .here)))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (G q α f : carrier_l 𝒩) : Prop :=
  map_l (ℳ := 𝒩) f α q ∧ ∀ a P, value_l (ℳ := 𝒩) f a P ↔
    member_l 𝒩 a α ∧ value_l (ℳ := 𝒩) G a P

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (G q α f : Term ℒ Γ Δ .set) :
    (formula_m G q α f).satisfies η ↔ holds_l
      (G.eval η) (q.eval η) (α.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessValueBounded.formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {G A q α : type_l hℳ} (hG : map_l (ℳ := 𝒱) G A q)
    (hαA : ∀ a, mem_l hℳ a α → mem_l hℳ a A) :
    ∃ f, holds_l (𝒩 := 𝒱) G q α f := by
  obtain ⟨f, hf, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hG hαA
  exact ⟨f, hf, hRead⟩

theorem unique_l {G q q' α f f' : type_l hℳ}
    (hf : holds_l (𝒩 := 𝒱) G q α f) (hf' : holds_l (𝒩 := 𝒱) G q' α f') : f = f' :=
  PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ) hf.1 hf'.1
    (fun a P => (hf.2 a P).trans (hf'.2 a P).symm)

/-- 前缀总性与原图源界实际给出序数域包含，不预设当前阶段在原域内。 -/
theorem subset_l {G q q' δ α f : type_l hℳ}
    (hG : map_l (ℳ := 𝒱) G δ q) (hf : holds_l (𝒩 := 𝒱) G q' α f) :
    ∀ a, mem_l hℳ a α → mem_l hℳ a δ := by
  intro a ha
  obtain ⟨P, hP, _⟩ := hf.1.2 a ha
  exact (SecondOrderFunctionProperties.value_mem_l hℳ hG ((hf.2 a P).mp hP.2).2).1

/-- 陪域更换只依据同一实际图的全 raw 输出界，不要求旧陪域包含于新界。 -/
theorem codomain_l {f A q C : type_l hℳ} (hf : map_l (ℳ := 𝒱) f A q)
    (hBound : ∀ a P, value_l (ℳ := 𝒱) f a P → mem_l hℳ P C) :
    map_l (ℳ := 𝒱) f A C := by
  constructor
  · intro p hp
    obtain ⟨a, P, ha, _hP, hPair⟩ := hf.1 p hp
    exact ⟨a, P, ha, hBound a P ⟨p, hp, hPair⟩, hPair⟩
  · intro a ha
    obtain ⟨P, hP, _⟩ := hf.2 a ha
    exact ⟨P, ⟨hBound a P hP.2, hP.2⟩,
      fun Q hQ => SecondOrderFunctionProperties.value_unique_l hℳ hf hQ.2 hP.2⟩

theorem limit_codomain_l {B ξ C G q α f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimitC : PowerlessRelativeHierarchySemantics.limit_l hℳ ξ)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B ξ C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ α)
    (hαC : mem_l hℳ α C) (hf : holds_l (𝒩 := 𝒱) G q α f)
    (hCover : ∀ β, mem_l hℳ β α → ∃ p, mem_l hℳ p C ∧ holds_l (𝒩 := 𝒱) G q β p) :
    map_l (ℳ := 𝒱) f α C := by
  apply codomain_l hℳ hf.1
  intro a P hP
  obtain ⟨ha, hGP⟩ := (hf.2 a P).mp hP
  obtain ⟨β, hβ, haβ⟩ := hLimit.2 a ha
  obtain ⟨p, hpC, hp⟩ := hCover β hβ
  have hβC := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC α hαC β hβ
  exact PowerlessRelativeLimitFunctionRange.value_member_l hBase hLimitC hC hβC hpC hp.1
    ((hp.2 a P).mpr ⟨haβ, hGP⟩)

#print axioms formula_l
#print axioms exists_l
#print axioms unique_l
#print axioms subset_l
#print axioms codomain_l
#print axioms limit_codomain_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderRawPrefix
