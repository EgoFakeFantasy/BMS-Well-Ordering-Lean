import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullbackAmbient
import BMSConstructibleBridge.PowerlessRelativeClassLexicographicWellOrder

/-! # 同一字典序积图的环境最小元

两因子须给出环境良序。对环境任意非空子集，原 Z₂ 分离产生其
第一坐标投影和最小第一坐标的纤维，再分别取环境最小元。子集、
投影和纤维均不预设属于类，类内工具只构造同一实际积和关系图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLexicographicAmbient

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassLexicographicWellOrder

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {X Y R S : type_l hℳ B}
    (hR : wellOrder_l (ℳ := 𝒱) X.val R.val) (hS : wellOrder_l (ℳ := 𝒱) Y.val S.val) :
    ∃ P L : type_l hℳ B,
      (∀ p : type_l hℳ B, SecondOrderQuotient.mem_l hℳ p.val P.val ↔
        ∃ x y : type_l hℳ B, SecondOrderQuotient.mem_l hℳ x.val X.val ∧
          SecondOrderQuotient.mem_l hℳ y.val Y.val ∧ ordered_l (ℳ := 𝒩) x y p) ∧
      wellOrder_l (ℳ := 𝒱) P.val L.val ∧
      ∀ p q : type_l hℳ B, value_l (ℳ := 𝒩) L p q ↔ lex_l (ℳ₀ := 𝒩) X Y R S p q := by
  obtain ⟨P, L, hP, hL, hRead⟩ := PowerlessRelativeClassLexicographicWellOrder.exists_l
    (PowerlessRelativeClassAmbientWellOrder.restrict_l hR)
    (PowerlessRelativeClassAmbientWellOrder.restrict_l hS)
  let lift (Z : type_l hℳ B) (x : SecondOrderQuotient.type_l hℳ)
      (hx : SecondOrderQuotient.mem_l hℳ x Z.val) : type_l hℳ B :=
    ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hx⟩
  refine ⟨P, L, hP, PowerlessRelativeClassAmbientWellOrder.of_minimum_l hL ?_, hRead⟩
  intro U hU
  let φ : Formula ℒ [] [.set, .set, .set] :=
    projection_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  let η : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree U).pushFree Y.val
  obtain ⟨V, hV⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) X.val
  have hVRead a : SecondOrderQuotient.mem_l hℳ a V ↔
      SecondOrderQuotient.mem_l hℳ a X.val ∧ ∃ b, SecondOrderQuotient.mem_l hℳ b Y.val ∧
        ∃ p, SecondOrderQuotient.mem_l hℳ p U ∧ ordered_l (ℳ := 𝒱) a b p :=
    (hV a).trans (and_congr Iff.rfl (projection_formula_l (η.pushFree a) _ _ _))
  obtain ⟨p₀, hp₀⟩ := hU.2
  obtain ⟨x₀, y₀, hx₀, hy₀, hPair₀⟩ := (hP (lift P p₀ (hU.1 p₀ hp₀))).mp (hU.1 p₀ hp₀)
  obtain ⟨a, haV, hMinA⟩ := hR.2.2.2 V
    ⟨fun x hx => ((hVRead x).mp hx).1, x₀.val,
      (hVRead x₀.val).mpr ⟨hx₀, y₀.val, hy₀, p₀, hp₀,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l _ _ _).mp hPair₀⟩⟩
  obtain ⟨haX, b₀, hb₀, p₁, hp₁, hPair₁⟩ := (hVRead a).mp haV
  let ψ : Formula ℒ [] [.set, .set, .set] :=
    fiber_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  let ξ : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree a).pushFree U
  obtain ⟨W, hW⟩ := (SecondOrderSeparationAxiom.schema_l hℳ ψ ξ).mp
    (SecondOrderSeparationAxiom.models_l hℳ ψ ξ) Y.val
  have hWRead b : SecondOrderQuotient.mem_l hℳ b W ↔
      SecondOrderQuotient.mem_l hℳ b Y.val ∧
        ∃ p, SecondOrderQuotient.mem_l hℳ p U ∧ ordered_l (ℳ := 𝒱) a b p :=
    (hW b).trans (and_congr Iff.rfl (fiber_formula_l (ξ.pushFree b) _ _ _))
  obtain ⟨b, hbW, hMinB⟩ := hS.2.2.2 W
    ⟨fun y hy => ((hWRead y).mp hy).1, b₀, (hWRead b₀).mpr ⟨hb₀, p₁, hp₁, hPair₁⟩⟩
  obtain ⟨hbY, p, hp, hPair⟩ := (hWRead b).mp hbW
  let p' := lift P p (hU.1 p hp)
  have hPair' : ordered_l (ℳ := 𝒩) (lift X a haX) (lift Y b hbY) p' :=
    (PowerlessRelativeClassFunctionAbsolute.ordered_l _ _ _).mpr hPair
  refine ⟨p, hp, ?_⟩
  intro z hz hzp
  let z' := lift P z (hU.1 z hz)
  obtain ⟨x, y, a', b', hx, hy, _, _, hPairZ, hPairP, hCompare⟩ := (hRead z' p').mp
    ((PowerlessRelativeClassFunctionAbsolute.value_l L z' p').mpr hzp)
  have hCoordinates := (SecondOrderPairObjects.ordered_eq_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.ordered_l _ _ _).mp hPairP) hPair).mp rfl
  have hPairZRaw := (PowerlessRelativeClassFunctionAbsolute.ordered_l _ _ _).mp hPairZ
  rcases hCompare with hLess | ⟨hEq, hLess⟩
  · have hxa := (PowerlessRelativeClassFunctionAbsolute.value_l R x a').mp hLess
    rw [hCoordinates.1] at hxa
    exact hMinA x.val ((hVRead x.val).mpr ⟨hx, y.val, hy, z, hz, hPairZRaw⟩) hxa
  · have hxa : x.val = a := (congrArg Subtype.val hEq).trans hCoordinates.1
    have hyb := (PowerlessRelativeClassFunctionAbsolute.value_l S y b').mp hLess
    rw [hCoordinates.2] at hyb
    rw [hxa] at hPairZRaw
    exact hMinB y.val ((hWRead y.val).mpr ⟨hy, z, hz, hPairZRaw⟩) hyb

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLexicographicAmbient
