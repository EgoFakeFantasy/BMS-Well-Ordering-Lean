import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsAmbient
import BMSConstructibleBridge.PowerlessRelativeClassRelationAmbientMembers

/-! # 全槽表示空间及其指标序的规范性

序列集和两次积载体由精确规格固定。辅助 ω 序、短字典序和中间积序
只通过读值进入最终积序；最终图另外排除非有序对成员，所以它本身唯一。
不要求辅助图对象唯一，也不从良序谓词推出图无垃圾。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionIndexCanonical

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassLexicographicWellOrder (lex_l lex_m lex_delta_l lex_formula_l)
open PowerlessRelativeClassSequenceOrderGraph (shortlex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def product_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (X Y Z : carrier_l ℳ₀) : Prop :=
  ∀ p, member_l ℳ₀ p Z ↔ ∃ x y, member_l ℳ₀ x X ∧ member_l ℳ₀ y Y ∧ ordered_l x y p

def proper_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (R : carrier_l ℳ₀) : Prop :=
  ∀ p, member_l ℳ₀ p R → ∃ x y, ordered_l x y p

def spec_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A P S I J U : carrier_l ℳ₀) : Prop :=
  PowerlessFiniteSequencesSyntax.spec_l ω A S ∧ product_l ω S I ∧ product_l ω I J ∧ proper_l U ∧
    ∃ N T K, (∀ x y, value_l N x y ↔ member_l ℳ₀ x ω ∧ member_l ℳ₀ y ω ∧ member_l ℳ₀ x y) ∧
      (∀ f g, value_l T f g ↔ shortlex_l ω A P f g) ∧
      (∀ p q, value_l K p q ↔ lex_l ω S N T p q) ∧
      (∀ p q, value_l U p q ↔ lex_l ω I N K p q)

theorem lex_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {X Y R R' S S' : carrier_l ℳ₀}
    (hR : ∀ x y, value_l (ℳ := ℳ₀) R x y ↔ value_l (ℳ := ℳ₀) R' x y)
    (hS : ∀ x y, value_l (ℳ := ℳ₀) S x y ↔ value_l (ℳ := ℳ₀) S' x y) (p q : carrier_l ℳ₀) :
    lex_l (ℳ₀ := ℳ₀) X Y R S p q ↔ lex_l (ℳ₀ := ℳ₀) X Y R' S' p q :=
  exists_congr fun x => exists_congr fun y => exists_congr fun a => exists_congr fun b =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr Iff.rfl (and_congr Iff.rfl (or_congr (hR x a) (and_congr Iff.rfl (hS y b))))))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem proper_unique_l {R S : type_l hℳ B} (hR : proper_l (ℳ₀ := 𝒞) R)
    (hS : proper_l (ℳ₀ := 𝒞) S) (hRead : ∀ x y, value_l (ℳ := 𝒞) R x y ↔ value_l (ℳ := 𝒞) S x y) :
    R = S := by
  have transfer {P Q : type_l hℳ B} (hP : proper_l (ℳ₀ := 𝒞) P)
      (h : ∀ x y, value_l (ℳ := 𝒞) P x y ↔ value_l (ℳ := 𝒞) Q x y)
      (p : type_l hℳ B) (hp : SecondOrderQuotient.mem_l hℳ p.val P.val) :
      SecondOrderQuotient.mem_l hℳ p.val Q.val := by
    obtain ⟨x, y, hxy⟩ := hP p hp
    obtain ⟨q, hq, hqPair⟩ := (h x y).mp ⟨p, hp, hxy⟩
    have hEq : q = p := Subtype.ext ((SecondOrderPairObjects.ordered_eq_l hℳ
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y q).mp hqPair)
      ((PowerlessRelativeClassFunctionAbsolute.ordered_l x y p).mp hxy)).mpr ⟨rfl, rfl⟩)
    exact hEq ▸ hq
  apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
  exact fun p => ⟨transfer hR hRead p, transfer hS (fun x y => (hRead x y).symm) p⟩

theorem unique_l {ω A P S I J U S' I' J' U' : type_l hℳ B}
    (h : spec_l (ℳ₀ := 𝒞) ω A P S I J U) (h' : spec_l (ℳ₀ := 𝒞) ω A P S' I' J' U') :
    S = S' ∧ I = I' ∧ J = J' ∧ U = U' := by
  obtain ⟨hS, hI, hJ, hProper, N, T, K, hN, hT, hK, hU⟩ := h
  obtain ⟨hS', hI', hJ', hProper', N', T', K', hN', hT', hK', hU'⟩ := h'
  have hSEq : S' = S := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    exact fun f => (hS' f).trans (hS f).symm
  subst S'
  have hIEq : I' = I := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    exact fun p => (hI' p).trans (hI p).symm
  subst I'
  have hJEq : J' = J := by
    apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
    exact fun p => (hJ' p).trans (hJ p).symm
  subst J'
  have hNValues x y := (hN x y).trans (hN' x y).symm
  have hTValues f g := (hT f g).trans (hT' f g).symm
  have hKValues p q := (hK p q).trans ((lex_congr_l hNValues hTValues p q).trans (hK' p q).symm)
  have hUValues p q := (hU p q).trans ((lex_congr_l hNValues hKValues p q).trans (hU' p q).symm)
  exact ⟨rfl, rfl, rfl, proper_unique_l hProper hProper' hUValues⟩

theorem exists_l {ω A P : type_l hℳ B} (hω : omega_l (ℳ := 𝒞) ω)
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val) :
    ∃ S I J U : type_l hℳ B, spec_l (ℳ₀ := 𝒞) ω A P S I J U ∧ wellOrder_l (ℳ := 𝒱) J.val U.val := by
  obtain ⟨S, T, hS, hT, hTRead⟩ := PowerlessRelativeClassSequenceWellOrderAmbient.exists_l hω hP
  obtain ⟨N, _, hNRead⟩ := PowerlessRelativeClassOmegaWellOrder.exists_l hω
  have hN := PowerlessRelativeClassOmegaAmbientOrder.of_comparison_l hω hNRead
  obtain ⟨I, K, hI, hK, hKRead⟩ := PowerlessRelativeClassLexicographicAmbient.exists_l hN hT
  obtain ⟨J, U₀, hJ, hU₀, hU₀Read⟩ := PowerlessRelativeClassLexicographicAmbient.exists_l hN hK
  let η : Env 𝒞 [] [.set, .set, .set, .set] := (((Env.empty.pushFree K).pushFree N).pushFree I).pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := lex_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨U, hMembers, hRead⟩ := PowerlessRelativeClassRelationAmbientMembers.exists_spec_l
    (lex_delta_l _ _ _ _ _ _) η J J
  have hφ (p q : type_l hℳ B) : φ.satisfies ((η.pushFree q).pushFree p) ↔
      lex_l (ℳ₀ := 𝒞) ω I N K p q := lex_formula_l _ _ _ _ _ _ _
  have hNewRead p q : value_l (ℳ := 𝒞) U p q ↔ lex_l (ℳ₀ := 𝒞) ω I N K p q := by
    refine ((hRead p q).trans (and_congr Iff.rfl (and_congr Iff.rfl (hφ p q)))).trans ?_
    constructor
    · exact fun h => h.2.2
    · intro hLex
      have hBounds := hLex
      obtain ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, _⟩ := hBounds
      exact ⟨(hJ p).mpr ⟨x, y, hx, hy, hp⟩, (hJ q).mpr ⟨a, b, ha, hb, hq⟩, hLex⟩
  have hProper : proper_l (ℳ₀ := 𝒞) U := by
    intro p hp
    obtain ⟨x, y, hx, hy, hxy, _⟩ := (hMembers p.val).mp hp
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J.property hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J.property hy⟩
    exact ⟨x', y', (PowerlessRelativeClassFunctionAbsolute.ordered_l x' y' p).mpr hxy⟩
  have hOrder : wellOrder_l (ℳ := 𝒱) J.val U.val := by
    apply PowerlessRelativeClassSequenceOrderSlices.wellOrder_congr_l hU₀
    intro p hp q hq
    let p' : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J.property hp⟩
    let q' : type_l hℳ B := ⟨q, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J.property hq⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l U₀ p' q').symm.trans
      (((hU₀Read p' q').trans (hNewRead p' q').symm).trans
        (PowerlessRelativeClassFunctionAbsolute.value_l U p' q'))
  exact ⟨S, I, J, U, ⟨hS, hI, hJ, hProper, N, T, K, hNRead, hTRead, hKRead, hNewRead⟩, hOrder⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionIndexCanonical
