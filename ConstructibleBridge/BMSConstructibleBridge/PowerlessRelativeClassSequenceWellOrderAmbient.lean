import BMSConstructibleBridge.PowerlessRelativeClassSequenceWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderInductionAmbient

/-! # 全部内部有限序列的环境良序

对任意环境子集分离长度集和定长交集，两个子集均不预设属于类。
正则性取得最小内部长度；环境公式归纳取得该切片的最小元。
同一类内短字典序图的线序条款经成员提升传输，最小元条款独立证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceWellOrderAmbient

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem of_graph_l {ω X R L S : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hR : wellOrder_l (ℳ := 𝒱) X.val R.val)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω X S)
    (hRead : ∀ f g, value_l (ℳ := 𝒩) L f g ↔ shortlex_l (ℳ₀ := 𝒩) ω X R f g) :
    wellOrder_l (ℳ := 𝒱) S.val L.val := by
  have hClass := PowerlessRelativeClassSequenceWellOrder.of_graph_l hω
    (PowerlessRelativeClassAmbientWellOrder.restrict_l hR) hS hRead
  apply PowerlessRelativeClassAmbientWellOrder.of_minimum_l hClass
  intro U hU
  let lift (Z : type_l hℳ B) (f : SecondOrderQuotient.type_l hℳ)
      (hf : mem_l hℳ f Z.val) : type_l hℳ B :=
    ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hf⟩
  let φ : Formula ℒ [] [.set, .set, .set] :=
    membershipLevyBound.boundedExists (.fvar (.there .here)) <|
      PowerlessMapBounded.formula_m (.bvar .here) (.fvar .here) (.fvar (.there (.there .here)))
  let η : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree X.val).pushFree U
  have hφRead (n : SecondOrderQuotient.type_l hℳ) : φ.satisfies (η.pushFree n) ↔
      ∃ f, mem_l hℳ f U ∧ map_l (ℳ := 𝒱) f n X.val := by
    simp only [φ, η, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l, Arguments.eval, Term.eval]
    rfl
  obtain ⟨D, hD⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) ω.val
  have hDRead n : mem_l hℳ n D ↔ mem_l hℳ n ω.val ∧
      ∃ f, mem_l hℳ f U ∧ map_l (ℳ := 𝒱) f n X.val :=
    (hD n).trans (and_congr Iff.rfl (hφRead n))
  obtain ⟨f₀, hf₀⟩ := hU.2
  obtain ⟨n₀, hn₀, hfn₀⟩ := (hS (lift S f₀ (hU.1 f₀ hf₀))).mp (hU.1 f₀ hf₀)
  have hFoundation := SecondOrderFoundation.models_l hℳ
  change ∀ D : SecondOrderQuotient.type_l hℳ, (∃ n, mem_l hℳ n D) →
    ∃ n, mem_l hℳ n D ∧ ∀ m, mem_l hℳ m n → ¬mem_l hℳ m D at hFoundation
  obtain ⟨n, hnD, hMinLength⟩ := hFoundation D
    ⟨n₀.val, (hDRead n₀.val).mpr ⟨hn₀, f₀, hf₀,
      (PowerlessRelativeClassFunctionAbsolute.map_l _ _ _).mp hfn₀⟩⟩
  obtain ⟨hn, f, hfU, hfn⟩ := (hDRead n).mp hnD
  let n' := lift ω n hn
  obtain ⟨P, hP⟩ := PowerlessRelativeClassSequenceSlices.of_omega_l (n := n') (X := X) hω hn
  let ψ : Formula ℒ [] [.set, .set] := member_m (.fvar .here) (.fvar (.there .here))
  let ξ : Env 𝒱 [] [.set] := (Env.empty).pushFree P.val
  obtain ⟨V, hV⟩ := (SecondOrderSeparationAxiom.schema_l hℳ ψ ξ).mp
    (SecondOrderSeparationAxiom.models_l hℳ ψ ξ) U
  have hVRead g : mem_l hℳ g V ↔ mem_l hℳ g U ∧ mem_l hℳ g P.val := hV g
  have hPRaw := PowerlessRelativeClassSequenceSlicesAbsolute.spec_l hω (n := n') hn hP
  have hWO := PowerlessRelativeClassSequenceOrderInductionAmbient.all_l hω hR hRead n' hn P.val hPRaw
  obtain ⟨x, hxV, hMin⟩ := hWO.2.2.2 V
    ⟨fun g hg => ((hVRead g).mp hg).2, f, (hVRead f).mpr ⟨hfU, (hPRaw f).mpr hfn⟩⟩
  obtain ⟨hxU, hxP⟩ := (hVRead x).mp hxV
  let x' := lift S x (hU.1 x hxU)
  have hxMap : map_l (ℳ := 𝒩) x' n' X :=
    (PowerlessRelativeClassFunctionAbsolute.map_l _ _ _).mpr ((hPRaw x).mp hxP)
  refine ⟨x, hxU, ?_⟩
  intro g hgU hgx
  let g' := lift S g (hU.1 g hgU)
  obtain ⟨m, hm, hgm⟩ := (hS g').mp (hU.1 g hgU)
  have hEdge : value_l (ℳ := 𝒩) L g' x' :=
    (PowerlessRelativeClassFunctionAbsolute.value_l L g' x').mpr hgx
  rcases (PowerlessRelativeClassSequenceOrderLinear.comparison_l (m := n') hm hn hgm hxMap hRead).mp hEdge with
    hmn | ⟨hmn, _⟩
  · exact hMinLength m.val hmn ((hDRead m.val).mpr ⟨hm, g, hgU,
      (PowerlessRelativeClassFunctionAbsolute.map_l _ _ _).mp hgm⟩)
  · subst m
    exact hMin g ((hVRead g).mpr ⟨hgU, (hPRaw g).mpr
      ((PowerlessRelativeClassFunctionAbsolute.map_l _ _ _).mp hgm)⟩) hgx

theorem exists_l {ω X R : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hR : wellOrder_l (ℳ := 𝒱) X.val R.val) :
    ∃ S L : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω X S ∧
      wellOrder_l (ℳ := 𝒱) S.val L.val ∧
      ∀ f g, value_l (ℳ := 𝒩) L f g ↔ shortlex_l (ℳ₀ := 𝒩) ω X R f g := by
  obtain ⟨S, hS⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_l (X := X) hω
  obtain ⟨L, hRead⟩ := PowerlessRelativeClassSequenceOrderGraph.exists_l (R := R) hS
  exact ⟨S, L, hS, of_graph_l hω hR hS hRead, hRead⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceWellOrderAmbient
