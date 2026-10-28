import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderLinear

/-! # 内部有限序列非空子集的长度优先最小元

长度集与定长交集均由实际类内 Δ₀ 分离取得。正则性给出最小出现长度，
全部内部长度的定长良序定理再给出该长度内的最小元。
不抽取 Type 层选择函数，也不把内部自然数域换成外部标准长度。
本模块为统一序列良序对象结论提供最小元语义步骤。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderMinimum

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem minimum_l {ω X R L S : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hR : wellOrder_l (ℳ := ClassModel) X R)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω X S)
    (hRead : ∀ f g : type_l hℳ B, value_l (ℳ := ClassModel) L f g ↔
      shortlex_l (ℳ₀ := ClassModel) ω X R f g) :
    ∀ U : type_l hℳ B, subset_l (ℳ := ClassModel) U S ∧
      (∃ f : type_l hℳ B, member_l ClassModel f U) →
      ∃ f : type_l hℳ B, member_l ClassModel f U ∧
        ∀ g : type_l hℳ B, member_l ClassModel g U → ¬value_l (ℳ := ClassModel) L g f := by
  intro U hU
  let φ : Formula ℒ [] [.set, .set, .set] :=
    membershipLevyBound.boundedExists (.fvar (.there .here)) <|
      PowerlessMapBounded.formula_m (.bvar .here) (.fvar .here) (.fvar (.there (.there .here)))
  let η : Env ClassModel [] [.set, .set] := ((Env.empty).pushFree X).pushFree U
  have hφ : Formula.IsDelta0 membershipLevyBound φ :=
    .bounded_exists _ (PowerlessMapBounded.delta_l _ _ _)
  have hφRead (n : type_l hℳ B) : φ.satisfies (η.pushFree n) ↔
      ∃ f : type_l hℳ B, member_l ClassModel f U ∧ map_l (ℳ := ClassModel) f n X := by
    simp only [φ, η, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l, Arguments.eval, Term.eval]
    rfl
  obtain ⟨D, hD⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hφ η ω
  have hDRead (n : type_l hℳ B) : member_l ClassModel n D ↔ member_l ClassModel n ω ∧
      ∃ f : type_l hℳ B, member_l ClassModel f U ∧ map_l (ℳ := ClassModel) f n X :=
    (hD n).trans (and_congr Iff.rfl (hφRead n))
  obtain ⟨f₀, hf₀⟩ := hU.2
  obtain ⟨n₀, hn₀, hfn₀⟩ := (hS f₀).mp (hU.1 f₀ hf₀)
  have hFoundation := PowerlessRelativeClassStructure.foundation_l hℳ B hBase
  change ∀ D : type_l hℳ B, (∃ n : type_l hℳ B, member_l ClassModel n D) →
    ∃ n : type_l hℳ B, member_l ClassModel n D ∧ ∀ m : type_l hℳ B,
      member_l ClassModel m n → ¬member_l ClassModel m D at hFoundation
  obtain ⟨n, hnD, hMinLength⟩ := hFoundation D ⟨n₀, (hDRead n₀).mpr ⟨hn₀, f₀, hf₀, hfn₀⟩⟩
  obtain ⟨hn, f, hfU, hfn⟩ := (hDRead n).mp hnD
  obtain ⟨P, hP⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (hBase := hBase) (X := X) hω hn
  let ψ : Formula ℒ [] [.set, .set] := member_m (.fvar .here) (.fvar (.there .here))
  let ξ : Env ClassModel [] [.set] := (Env.empty).pushFree P
  have hψ : Formula.IsDelta0 membershipLevyBound ψ := .rel _ _
  have hψRead (g : type_l hℳ B) : ψ.satisfies (ξ.pushFree g) ↔ member_l ClassModel g P := Iff.rfl
  obtain ⟨V, hV⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hψ ξ U
  have hVRead (g : type_l hℳ B) : member_l ClassModel g V ↔
      member_l ClassModel g U ∧ member_l ClassModel g P :=
    (hV g).trans (and_congr Iff.rfl (hψRead g))
  have hWO := PowerlessRelativeClassSequenceOrderInduction.all_l hω hR hRead n hn P hP
  obtain ⟨x, hxV, hMin⟩ := hWO.2.2.2 V
    ⟨fun g hg => ((hVRead g).mp hg).2, f, (hVRead f).mpr ⟨hfU, (hP f).mpr hfn⟩⟩
  obtain ⟨hxU, hxP⟩ := (hVRead x).mp hxV
  have hxMap := (hP x).mp hxP
  refine ⟨x, hxU, ?_⟩
  intro g hgU hgx
  obtain ⟨m, hm, hgm⟩ := (hS g).mp (hU.1 g hgU)
  rcases (PowerlessRelativeClassSequenceOrderLinear.comparison_l hm hn hgm hxMap hRead).mp hgx with
    hmn | ⟨hmn, _⟩
  · exact hMinLength m hmn ((hDRead m).mpr ⟨hm, g, hgU, hgm⟩)
  · subst m
    exact hMin g ((hVRead g).mpr ⟨hgU, (hP g).mpr hgm⟩) hgx

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderMinimum
