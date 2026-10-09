import BMSConstructibleBridge.PowerlessRelativeClassFunctionSpecifications

/-! # 同一 Class 函数图的完整逐行规格绝对性

原 Z₂、纯隶属 ℒ。只要求实际矩阵逐坐标绝对；完整函数图的无界
输入输出由其干净 Map 守卫收回同一 Class 定义域与陪域。矩阵可为
Δ₀，但整张图规格不被误分类为 Δ₀，也不构造 Type 选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassGraphSpecificationAbsolute

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (G A R : carrier_l 𝒩) (P : carrier_l 𝒩 → carrier_l 𝒩 → Prop) : Prop :=
  map_l (ℳ := 𝒩) G A R ∧ ∀ a r, value_l (ℳ := 𝒩) G a r ↔
    member_l 𝒩 a A ∧ member_l 𝒩 r R ∧ P a r

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "M" => type_l hℳ B

/-- 不要求任意 raw 候选已经属于 Class；资格由 Map 或成员守卫推得。 -/
theorem graph_l (G A R : M) (P : M → M → Prop) (Q : Raw → Raw → Prop)
    (hMatrix : ∀ a r, P a r ↔ Q a.val r.val) :
    spec_l (𝒩 := 𝒩₀) G A R P ↔ spec_l (𝒩 := 𝒱) G.val A.val R.val Q := by
  constructor
  · rintro ⟨hMap, hRead⟩
    have hMap' := (PowerlessRelativeClassFunctionAbsolute.map_l G A R).mp hMap
    refine ⟨hMap', fun a r => ?_⟩
    constructor
    · intro hValue
      obtain ⟨ha, hr⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hMap' hValue
      let a₀ : M := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property ha⟩
      let r₀ : M := ⟨r, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase R.property hr⟩
      have hRow := (hRead a₀ r₀).mp ((PowerlessRelativeClassFunctionAbsolute.value_l G a₀ r₀).mpr hValue)
      exact ⟨ha, hr, (hMatrix a₀ r₀).mp hRow.2.2⟩
    · rintro ⟨ha, hr, hRow⟩
      let a₀ : M := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property ha⟩
      let r₀ : M := ⟨r, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase R.property hr⟩
      exact (PowerlessRelativeClassFunctionAbsolute.value_l G a₀ r₀).mp
        ((hRead a₀ r₀).mpr ⟨ha, hr, (hMatrix a₀ r₀).mpr hRow⟩)
  · rintro ⟨hMap, hRead⟩
    refine ⟨(PowerlessRelativeClassFunctionAbsolute.map_l G A R).mpr hMap, fun a r => ?_⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l G a r).trans
      ((hRead a.val r.val).trans (and_congr Iff.rfl (and_congr Iff.rfl (hMatrix a r).symm)))

/-- 给定原规范 Sat 函数图完整读回，不换 G、U 或任何数码。 -/
theorem satisfaction_l (ω e t₁ t₂ t₃ P N F U G : M) :
    PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ P N F U G ↔
      PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒱)
        ω.val e.val t₁.val t₂.val t₃.val P.val N.val F.val U.val G.val := by
  apply graph_l G U U
  intro a r
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree F |>.pushFree t₃ |>.pushFree t₂ |>.pushFree t₁
      |>.pushFree U |>.pushFree U |>.pushFree P |>.pushFree N |>.pushFree e
      |>.pushFree a |>.pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessSatisfactionNormalizedMatrix.formula_m
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
  have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) (φ := φ)
    (PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _) η
  simpa only [φ, PowerlessSatisfactionNormalizedMatrix.formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, PowerlessRelativeClassRelativization.env_l, η] using h

/-- 双向的是原有界 Def 检查器函数规格，不是未经证明的原 global_m。 -/
theorem def_l (ω e N Q U G D : M) :
    PowerlessMemberDefFunctionAbsolute.spec_l (𝒩 := 𝒩₀) ω e N Q U G D ↔
      PowerlessMemberDefFunctionAbsolute.spec_l (𝒩 := 𝒱)
        ω.val e.val N.val Q.val U.val G.val D.val := by
  apply graph_l D U U
  intro a r
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree a |>.pushFree G |>.pushFree U
      |>.pushFree Q |>.pushFree N |>.pushFree e |>.pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    PowerlessMemberDefImageBounded.formula_m
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
  have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase) (φ := φ)
    (PowerlessMemberDefImageBounded.delta_l _ _ _ _ _ _ _ _) η
  simpa only [φ, PowerlessMemberDefImageBounded.formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, PowerlessRelativeClassRelativization.env_l, η] using h

#print axioms graph_l
#print axioms satisfaction_l
#print axioms def_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassGraphSpecificationAbsolute
