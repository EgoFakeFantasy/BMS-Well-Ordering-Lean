import BMSConstructibleBridge.PowerlessRelativeClassAmbientWellOrder
import BMSConstructibleBridge.SecondOrderSeparationAxiom

/-! # 同一类内单射拉回图的环境良序

目标良序须在环境商中成立。对于任意环境子集 U，以原 Z₂ 完整分离
在目标集上构造实际像，再将其环境最小元拉回 U。U 和其像都没有
类成员前提；已有类内工具只负责构造同一个比较关系图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderPullbackAmbient

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassWellOrderPullback (comparison_l)
open SecondOrderObjectSyntax (member_m)
open StabilityFrame (membershipLevyBound)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {X Y F R : type_l hℳ B}
    (hF : map_l (ℳ := 𝒩) F X Y) (hInject : injective_l (ℳ := 𝒩) F)
    (hR : wellOrder_l (ℳ := 𝒱) Y.val R.val) :
    ∃ L : type_l hℳ B, wellOrder_l (ℳ := 𝒱) X.val L.val ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := 𝒩) L x y ↔
        SecondOrderQuotient.mem_l hℳ x.val X.val ∧ SecondOrderQuotient.mem_l hℳ y.val X.val ∧
          comparison_l (ℳ₀ := 𝒩) Y F R x y := by
  obtain ⟨L, _, hRead⟩ := PowerlessRelativeClassWellOrderPullback.exists_l
    hF hInject (PowerlessRelativeClassAmbientWellOrder.restrict_l hR)
  have hFRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F X Y).mp hF
  let lift (Z : type_l hℳ B) (x : SecondOrderQuotient.type_l hℳ)
      (hx : SecondOrderQuotient.mem_l hℳ x Z.val) : type_l hℳ B :=
    ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hx⟩
  have hCompare (x y : type_l hℳ B) : comparison_l (ℳ₀ := 𝒩) Y F R x y ↔
      comparison_l (ℳ₀ := 𝒱) Y.val F.val R.val x.val y.val := by
    constructor
    · rintro ⟨a, b, ha, hb, hxa, hyb, hab⟩
      exact ⟨a.val, b.val, ha, hb,
        (PowerlessRelativeClassFunctionAbsolute.value_l F x a).mp hxa,
        (PowerlessRelativeClassFunctionAbsolute.value_l F y b).mp hyb,
        (PowerlessRelativeClassFunctionAbsolute.value_l R a b).mp hab⟩
    · rintro ⟨a, b, ha, hb, hxa, hyb, hab⟩
      exact ⟨lift Y a ha, lift Y b hb, ha, hb,
        (PowerlessRelativeClassFunctionAbsolute.value_l F x (lift Y a ha)).mpr hxa,
        (PowerlessRelativeClassFunctionAbsolute.value_l F y (lift Y b hb)).mpr hyb,
        (PowerlessRelativeClassFunctionAbsolute.value_l R (lift Y a ha) (lift Y b hb)).mpr hab⟩
  have hEdge (x y : SecondOrderQuotient.type_l hℳ)
      (hx : SecondOrderQuotient.mem_l hℳ x X.val) (hy : SecondOrderQuotient.mem_l hℳ y X.val) :
      value_l (ℳ := 𝒱) L.val x y ↔ comparison_l (ℳ₀ := 𝒱) Y.val F.val R.val x y :=
    (PowerlessRelativeClassFunctionAbsolute.value_l L (lift X x hx) (lift X y hy)).symm.trans
      ((hRead (lift X x hx) (lift X y hy)).trans
        ((and_iff_right hx).trans ((and_iff_right hy).trans (hCompare _ _))))
  have hUnique {x a b : SecondOrderQuotient.type_l hℳ}
      (ha : value_l (ℳ := 𝒱) F.val x a) (hb : value_l (ℳ := 𝒱) F.val x b) : a = b :=
    SecondOrderFunctionProperties.value_unique_l hℳ hFRaw ha hb
  refine ⟨L, ⟨?_, ?_, ?_, ?_⟩, hRead⟩
  · intro x hx hxx
    obtain ⟨a, b, ha, _, hxa, hxb, hab⟩ := (hEdge x x hx hx).mp hxx
    have hEq := hUnique hxa hxb
    subst b
    exact hR.1 a ha hab
  · intro x y z hxyz hxy hyz
    obtain ⟨a, b, ha, hb, hxa, hyb, hab⟩ := (hEdge x y hxyz.1 hxyz.2.1).mp hxy
    obtain ⟨b', c, _, hc, hyb', hzc, hbc⟩ := (hEdge y z hxyz.2.1 hxyz.2.2).mp hyz
    have hEq := hUnique hyb' hyb
    subst b'
    exact (hEdge x z hxyz.1 hxyz.2.2).mpr
      ⟨a, c, ha, hc, hxa, hzc, hR.2.1 a b c ⟨ha, hb, hc⟩ hab hbc⟩
  · intro x y hxy
    obtain ⟨a, ⟨ha, hxa⟩, _⟩ := hFRaw.2 x hxy.1
    obtain ⟨b, ⟨hb, hyb⟩, _⟩ := hFRaw.2 y hxy.2
    rcases hR.2.2.1 a b ⟨ha, hb⟩ with hab | rfl | hba
    · exact Or.inl ((hEdge x y hxy.1 hxy.2).mpr ⟨a, b, ha, hb, hxa, hyb, hab⟩)
    · have hClassEq := hInject (lift X x hxy.1) (lift X y hxy.2) (lift Y a ha)
        ((PowerlessRelativeClassFunctionAbsolute.value_l F _ _).mpr hxa)
        ((PowerlessRelativeClassFunctionAbsolute.value_l F _ _).mpr hyb)
      exact Or.inr (Or.inl (congrArg Subtype.val hClassEq))
    · exact Or.inr (Or.inr ((hEdge y x hxy.2 hxy.1).mpr ⟨b, a, hb, ha, hyb, hxa, hba⟩))
  · intro U hU
    let ψ : Formula ℒ [] [.set, .set, .set] := membershipLevyBound.boundedExists (.fvar (.there .here))
      (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))
    let η : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree F.val).pushFree U
    have hψ (a : SecondOrderQuotient.type_l hℳ) : ψ.satisfies (η.pushFree a) ↔
        ∃ x, SecondOrderQuotient.mem_l hℳ x U ∧ value_l (ℳ := 𝒱) F.val x a := by
      simp only [ψ, η, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
        membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
      rfl
    obtain ⟨V, hV⟩ := (SecondOrderSeparationAxiom.schema_l hℳ ψ η).mp
      (SecondOrderSeparationAxiom.models_l hℳ ψ η) Y.val
    have hVRead a : SecondOrderQuotient.mem_l hℳ a V ↔
        SecondOrderQuotient.mem_l hℳ a Y.val ∧
          ∃ x, SecondOrderQuotient.mem_l hℳ x U ∧ value_l (ℳ := 𝒱) F.val x a :=
      (hV a).trans (and_congr Iff.rfl (hψ a))
    obtain ⟨x, hx⟩ := hU.2
    obtain ⟨a, ⟨ha, hxa⟩, _⟩ := hFRaw.2 x (hU.1 x hx)
    obtain ⟨b, hbV, hMin⟩ := hR.2.2.2 V
      ⟨fun c hc => ((hVRead c).mp hc).1, a, (hVRead a).mpr ⟨ha, x, hx, hxa⟩⟩
    obtain ⟨_, y, hy, hyb⟩ := (hVRead b).mp hbV
    refine ⟨y, hy, ?_⟩
    intro z hz hzy
    obtain ⟨c, b', hc, _, hzc, hyb', hcb⟩ := (hEdge z y (hU.1 z hz) (hU.1 y hy)).mp hzy
    have hEq := hUnique hyb' hyb
    subst b'
    exact hMin c ((hVRead c).mpr ⟨hc, z, hz, hzc⟩) hcb

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderPullbackAmbient
