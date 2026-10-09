import BMSConstructibleBridge.PowerlessCanonicalOrderLightHistoryUnique
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice
import BMSConstructibleBridge.SecondOrderSeparationAxiom

/-! # 规范序前缀的精确极限收集及三次 Def 界

检查器以 C₀ 为有限证书母界，故 C₀ 是矩阵真实参数。不能直接在 C₀
内应用 Def 分离：那会暗用 C₀∈C₀。实际在 C₁=Def(C₀) 中筛选，
前缀族属于 C₂=Def(C₁)，精确成员并属于 C₃=Def(C₂)。

hCover 仅是内部预算归纳的局部前缀覆盖，仍须由实际归纳构造；本文件
不预设统一枚举、Collection、外部良基性或前缀族存在公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryLimitPrefix

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ}
    (C W ω F G P₀ α g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists α <|
    PowerlessCanonicalOrderLightHistory.formula_m (up C) (up W) (up ω)
      (up F) (up G) (up P₀) (.bvar .here) (up g)

theorem body_delta_l {Γ Δ : SortContext ℒ}
    (C W ω F G P₀ α g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m C W ω F G P₀ α g) :=
  .bounded_exists _ (PowerlessCanonicalOrderLightHistory.delta_l _ _ _ _ _ _ _ _)

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (C W ω F G P₀ α g : Term ℒ Γ Δ .set) :
    (body_m C W ω F G P₀ α g).satisfies η ↔
      ∃ β, member_l 𝒩 β (α.eval η) ∧ PowerlessCanonicalOrderLightHistory.holds_l
        (𝒩 := 𝒩) (C.eval η) (W.eval η) (ω.eval η) (F.eval η) (G.eval η)
          (P₀.eval η) β (g.eval η) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessCanonicalOrderLightHistory.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

private abbrev parameters_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

theorem exists_l {C₀ C₁ C₂ C₃ W ω F G P₀ α δ f : type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F δ W) (hG : map_l (ℳ := 𝒱) G W W)
    (hCoverage : ∀ A, mem_l hℳ A W → ∀ g,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A g → mem_l hℳ g C₀)
    (hα : Ordinal α) (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ α)
    (hf : PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C₀ W ω F G P₀ α f)
    (hTrans : ∀ x, mem_l hℳ x C₀ → ∀ y, mem_l hℳ y x → mem_l hℳ y C₀)
    (hDef₀₁ : SecondOrderMemberDef.spec_l hℳ C₀ C₁)
    (hDef₁₂ : SecondOrderMemberDef.spec_l hℳ C₁ C₂)
    (hDef₂₃ : SecondOrderMemberDef.spec_l hℳ C₂ C₃)
    (hParams : mem_l hℳ C₀ C₁ ∧ mem_l hℳ W C₁ ∧ mem_l hℳ ω C₁ ∧
      mem_l hℳ F C₁ ∧ mem_l hℳ G C₁ ∧ mem_l hℳ P₀ C₁ ∧ mem_l hℳ α C₁)
    (hCover : ∀ β, mem_l hℳ β α → ∃ g, mem_l hℳ g C₀ ∧
      PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C₀ W ω F G P₀ β g) :
    ∃ H, mem_l hℳ H C₂ ∧
      (∀ g, mem_l hℳ g H ↔ ∃ β, mem_l hℳ β α ∧
        PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C₀ W ω F G P₀ β g) ∧
      (∀ p, mem_l hℳ p f ↔ ∃ g, mem_l hℳ g H ∧ mem_l hℳ p g) ∧
      mem_l hℳ f C₃ := by
  let η : Env 𝒱 [] parameters_m :=
    Env.empty |>.pushFree α |>.pushFree P₀ |>.pushFree G |>.pushFree F
      |>.pushFree ω |>.pushFree W |>.pushFree C₀
  let φ : Formula ℒ [] (.set :: parameters_m) := body_m
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.fvar .here)
  have hFormula g : φ.satisfies (η.pushFree g) ↔ ∃ β, mem_l hℳ β α ∧
      PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C₀ W ω F G P₀ β g :=
    body_formula_l (η.pushFree g) _ _ _ _ _ _ _ _
  obtain ⟨H, hH⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) C₁
  have hHRead g : mem_l hℳ g H ↔ mem_l hℳ g C₁ ∧ ∃ β, mem_l hℳ β α ∧
      PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C₀ W ω F G P₀ β g :=
    (hH g).trans (and_congr Iff.rfl (hFormula g))
  have hTrans₁ := SecondOrderMemberDefProperties.transitive_l hℳ hDef₀₁
    (fun x y hx hy => hTrans x hx y hy)
  have hSub := SecondOrderMemberDefProperties.contains_l hℳ hDef₀₁
    (fun x y hx hy => hTrans x hx y hy)
  have hHC₂ : mem_l hℳ H C₂ := by
    apply SecondOrderMemberDefBoundedSlice.member_l (φ := φ) hℳ hDef₁₂
      (fun x hx y hy => hTrans₁ x y hx hy)
      (body_delta_l _ _ _ _ _ _ _ _) η
    · intro s v
      cases s
      cases v with
      | here => exact hParams.1
      | there v => cases v with
        | here => exact hParams.2.1
        | there v => cases v with
          | here => exact hParams.2.2.1
          | there v => cases v with
            | here => exact hParams.2.2.2.1
            | there v => cases v with
              | here => exact hParams.2.2.2.2.1
              | there v => cases v with
                | here => exact hParams.2.2.2.2.2.1
                | there v => cases v with
                  | here => exact hParams.2.2.2.2.2.2
                  | there v => nomatch v
    · exact hH
  have hExact g : mem_l hℳ g H ↔ ∃ β, mem_l hℳ β α ∧
      PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C₀ W ω F G P₀ β g := by
    constructor
    · intro hg
      exact ((hHRead g).mp hg).2
    · rintro ⟨β, hβ, hg⟩
      obtain ⟨g', hg'C₀, hg'⟩ := hCover β hβ
      have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
      have hEq := PowerlessCanonicalOrderLightHistoryUnique.unique_l hℳ
        hF hG hCoverage hCoverage hβOrd hg hg'
      exact (hHRead g).mpr ⟨hEq.symm ▸ hSub g' hg'C₀, β, hβ, hg⟩
  have hUnion p : mem_l hℳ p f ↔ ∃ g, mem_l hℳ g H ∧ mem_l hℳ p g := by
    constructor
    · intro hp
      obtain ⟨a, E, ha, _hE, hPair⟩ := hf.1.1 p hp
      obtain ⟨β, hβ, haβ⟩ := hLimit.2 a ha
      obtain ⟨g, _hgC, hg⟩ := hCover β hβ
      obtain ⟨E', hE', _⟩ := hg.1.2 a haβ
      have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
      have hEq := PowerlessCanonicalOrderLightHistoryUnique.agreement_l hℳ
        hF hG hCoverage hCoverage hα hβOrd
        hf hg a ⟨ha, haβ⟩ E E' ⟨⟨p, hp, hPair⟩, hE'.2⟩
      obtain ⟨q, hq, hPair'⟩ := hE'.2
      have hqp : q = p := SecondOrderPairObjects.ordered_unique_l hℳ
        (hEq.symm ▸ hPair') hPair
      exact ⟨g, (hExact g).mpr ⟨β, hβ, hg⟩, hqp ▸ hq⟩
    · rintro ⟨g, hgH, hpg⟩
      obtain ⟨β, hβ, hg⟩ := (hExact g).mp hgH
      obtain ⟨a, E, haβ, _hE, hPair⟩ := hg.1.1 p hpg
      have ha := hα.transitive β hβ a haβ
      obtain ⟨E', hE', _⟩ := hf.1.2 a ha
      have hβOrd : Ordinal β := SetTheory.Structure.IsOrdinal.mem hα hβ
      have hEq := PowerlessCanonicalOrderLightHistoryUnique.agreement_l hℳ
        hF hG hCoverage hCoverage hα hβOrd
        hf hg a ⟨ha, haβ⟩ E' E ⟨hE'.2, ⟨p, hpg, hPair⟩⟩
      obtain ⟨q, hq, hPair'⟩ := hE'.2
      have hqp : q = p := SecondOrderPairObjects.ordered_unique_l hℳ (hEq ▸ hPair') hPair
      exact hqp ▸ hq
  have hTrans₂ := SecondOrderMemberDefProperties.transitive_l hℳ hDef₁₂ hTrans₁
  exact ⟨H, hHC₂, hExact, hUnion,
    SecondOrderMemberDefBasicClosure.union_l hℳ hDef₂₃ hHC₂
      (fun x hx y hy => hTrans₂ x y hx hy) hUnion⟩

#print axioms body_delta_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryLimitPrefix
