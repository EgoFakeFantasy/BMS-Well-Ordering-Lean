import BMSConstructibleBridge.PowerlessCanonicalIndexSyntax
import BMSConstructibleBridge.PowerlessRelativeClassRelationReadAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassSequenceAbsolute

/-! # 完整规范指标规格的环境传输

有限赋值用全环境序列规格提升，积编码用实际坐标闭包提升。
辅助比较的全部环境读值由同一图传输；不把类内全称量词无条件扩张。
这是对象规范步骤需要的中间对应，并非对象步骤可推导性本身。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalIndexAbsolute

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSatisfactionIndexCanonical (product_l proper_l spec_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l shortlex_m shortlex_delta_l shortlex_formula_l)
open PowerlessRelativeClassLexicographicWellOrder (lex_l lex_m lex_delta_l lex_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem product_absolute_l {X Y Z : type_l hℳ B} (h : product_l (ℳ₀ := 𝒞) X Y Z) :
    product_l (ℳ₀ := 𝒱) X.val Y.val Z.val := by
  intro p
  constructor
  · intro hp
    let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hp⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := (h p').mp hp
    exact ⟨x.val, y.val, hx, hy, (PowerlessRelativeClassFunctionAbsolute.ordered_l x y p').mp hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x'.property y'.property hxy⟩
    exact (h p').mpr ⟨x', y', hx, hy, (PowerlessRelativeClassFunctionAbsolute.ordered_l x' y' p').mpr hxy⟩

theorem proper_absolute_l {R : type_l hℳ B} (h : proper_l (ℳ₀ := 𝒞) R) :
    proper_l (ℳ₀ := 𝒱) R.val := by
  intro p hp
  let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase R.property hp⟩
  obtain ⟨x, y, hxy⟩ := h p' hp
  exact ⟨x.val, y.val, (PowerlessRelativeClassFunctionAbsolute.ordered_l x y p').mp hxy⟩

theorem omegaRead_l {ω N : type_l hℳ B}
    (h : ∀ x y, value_l (ℳ := 𝒞) N x y ↔ SecondOrderQuotient.mem_l hℳ x.val ω.val ∧
      SecondOrderQuotient.mem_l hℳ y.val ω.val ∧ SecondOrderQuotient.mem_l hℳ x.val y.val) :
    ∀ x y, value_l (ℳ := 𝒱) N.val x y ↔ SecondOrderQuotient.mem_l hℳ x ω.val ∧
      SecondOrderQuotient.mem_l hℳ y ω.val ∧ SecondOrderQuotient.mem_l hℳ x y := by
  let φ : Formula ℒ [] [.set, .set] := SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here))
  exact PowerlessRelativeClassRelationReadAbsolute.read_l (φ := φ) (.rel _ _) Env.empty
    (X := ω) (Y := ω) (R := N) h

theorem shortlexRead_l {ω A P S T : type_l hℳ B} (hΩ : omega_l (ℳ := 𝒞) ω)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒞) ω A S)
    (h : ∀ f g, value_l (ℳ := 𝒞) T f g ↔ shortlex_l (ℳ₀ := 𝒞) ω A P f g) :
    ∀ f g, value_l (ℳ := 𝒱) T.val f g ↔ shortlex_l (ℳ₀ := 𝒱) ω.val A.val P.val f g := by
  let η : Env 𝒞 [] [.set, .set, .set] := ((Env.empty.pushFree P).pushFree A).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := shortlex_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  have hClassφ f g : φ.satisfies ((η.pushFree g).pushFree f) ↔ shortlex_l (ℳ₀ := 𝒞) ω A P f g :=
    shortlex_formula_l _ _ _ _ _ _
  have hRawφ f g : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree g).pushFree f) ↔
      shortlex_l (ℳ₀ := 𝒱) ω.val A.val P.val f g := shortlex_formula_l _ _ _ _ _ _
  have hBound f g : value_l (ℳ := 𝒞) T f g ↔ SecondOrderQuotient.mem_l hℳ f.val S.val ∧
      SecondOrderQuotient.mem_l hℳ g.val S.val ∧ φ.satisfies ((η.pushFree g).pushFree f) := by
    constructor
    · intro hValue
      have hLex := (h f g).mp hValue
      have hCopy := hLex
      obtain ⟨n, m, hn, hm, hf, hg, _⟩ := hCopy
      exact ⟨(hS f).mpr ⟨n, hn, hf⟩, (hS g).mpr ⟨m, hm, hg⟩, (hClassφ f g).mpr hLex⟩
    · exact fun hValue => (h f g).mpr ((hClassφ f g).mp hValue.2.2)
  have hRaw := PowerlessRelativeClassRelationReadAbsolute.read_l
    (shortlex_delta_l _ _ _ _ _) η (X := S) (Y := S) (R := T) hBound
  have hRawS := PowerlessRelativeClassSequenceAbsolute.spec_l hΩ hS
  intro f g
  refine ((hRaw f g).trans (and_congr Iff.rfl (and_congr Iff.rfl (hRawφ f g)))).trans ?_
  constructor
  · exact fun hValue => hValue.2.2
  · intro hLex
    have hCopy := hLex
    obtain ⟨n, m, hn, hm, hf, hg, _⟩ := hCopy
    exact ⟨(hRawS f).mpr ⟨n, hn, hf⟩, (hRawS g).mpr ⟨m, hm, hg⟩, hLex⟩

theorem lexRead_l {X Y Z R S T : type_l hℳ B}
    (hZ : product_l (ℳ₀ := 𝒞) X Y Z)
    (h : ∀ p q, value_l (ℳ := 𝒞) T p q ↔ lex_l (ℳ₀ := 𝒞) X Y R S p q) :
    ∀ p q, value_l (ℳ := 𝒱) T.val p q ↔ lex_l (ℳ₀ := 𝒱) X.val Y.val R.val S.val p q := by
  let η : Env 𝒞 [] [.set, .set, .set, .set] := (((Env.empty.pushFree S).pushFree R).pushFree Y).pushFree X
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := lex_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.fvar (.there .here))
  have hClassφ p q : φ.satisfies ((η.pushFree q).pushFree p) ↔ lex_l (ℳ₀ := 𝒞) X Y R S p q :=
    lex_formula_l _ _ _ _ _ _ _
  have hRawφ p q : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree q).pushFree p) ↔
      lex_l (ℳ₀ := 𝒱) X.val Y.val R.val S.val p q := lex_formula_l _ _ _ _ _ _ _
  have hBound p q : value_l (ℳ := 𝒞) T p q ↔ SecondOrderQuotient.mem_l hℳ p.val Z.val ∧
      SecondOrderQuotient.mem_l hℳ q.val Z.val ∧ φ.satisfies ((η.pushFree q).pushFree p) := by
    constructor
    · intro hValue
      have hLex := (h p q).mp hValue
      have hCopy := hLex
      obtain ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, _⟩ := hCopy
      exact ⟨(hZ p).mpr ⟨x, y, hx, hy, hp⟩, (hZ q).mpr ⟨a, b, ha, hb, hq⟩, (hClassφ p q).mpr hLex⟩
    · exact fun hValue => (h p q).mpr ((hClassφ p q).mp hValue.2.2)
  have hRaw := PowerlessRelativeClassRelationReadAbsolute.read_l
    (lex_delta_l _ _ _ _ _ _) η (X := Z) (Y := Z) (R := T) hBound
  have hRawZ := product_absolute_l hZ
  intro p q
  refine ((hRaw p q).trans (and_congr Iff.rfl (and_congr Iff.rfl (hRawφ p q)))).trans ?_
  constructor
  · exact fun hValue => hValue.2.2
  · intro hLex
    have hCopy := hLex
    obtain ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, _⟩ := hCopy
    exact ⟨(hRawZ p).mpr ⟨x, y, hx, hy, hp⟩, (hRawZ q).mpr ⟨a, b, ha, hb, hq⟩, hLex⟩

theorem spec_absolute_l {ω A P S I J U : type_l hℳ B} (hΩ : omega_l (ℳ := 𝒞) ω)
    (h : spec_l (ℳ₀ := 𝒞) ω A P S I J U) : spec_l (ℳ₀ := 𝒱) ω.val A.val P.val S.val I.val J.val U.val := by
  obtain ⟨hS, hI, hJ, hProper, N, T, K, hN, hT, hK, hU⟩ := h
  exact ⟨PowerlessRelativeClassSequenceAbsolute.spec_l hΩ hS, product_absolute_l hI, product_absolute_l hJ,
    proper_absolute_l hProper, N.val, T.val, K.val, omegaRead_l hN, shortlexRead_l hΩ hS hT,
    lexRead_l hI hK, lexRead_l hJ hU⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalIndexAbsolute
