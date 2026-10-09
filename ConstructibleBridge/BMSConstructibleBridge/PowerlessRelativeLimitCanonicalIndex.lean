import BMSConstructibleBridge.PowerlessRelativeLimitFiniteSequencesDirect
import BMSConstructibleBridge.PowerlessRelativeLimitRelationalGraph
import BMSConstructibleBridge.SecondOrderCanonicalIndexUnique

/-! # 指定非零极限层内的完整规范指标包

实际 ω、母集 A 和父比较图 P 均属于同一真实极限层 C。完整内部有限
序列、两个积以及四个无垃圾比较图全部仍在 C 中；没有把 C 换成
Def²(C)，也不要求 A 可数或预先给出统一历史。

新图的规格量化全部原商对象。环境良序性另由已有规范指标存在性与
全 raw 唯一性恢复，不把良序性误塞入 Δ₀ 正文。本模块是后继证书的
实际模型装配，不声称已经完成规范序长历史或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalIndex

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 精确图成员规格；不同于仅 Value 一致，此规格明确排除垃圾成员。 -/
def graph_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (X Y R : carrier_l 𝒩) (χ : carrier_l 𝒩 → carrier_l 𝒩 → Prop) : Prop :=
  ∀ p, member_l 𝒩 p R ↔ ∃ x y, member_l 𝒩 x X ∧ member_l 𝒩 y Y ∧
    ordered_l (ℳ := 𝒩) x y p ∧ χ x y

private theorem graph_values_l {X Y R : type_l hℳ} {χ : type_l hℳ → type_l hℳ → Prop}
    (hR : graph_l (𝒩 := 𝒱) X Y R χ) :
    ∀ x y, value_l (ℳ := 𝒱) R x y ↔ mem_l hℳ x X ∧ mem_l hℳ y Y ∧ χ x y := by
  intro x y
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hb, hab, hχ⟩ := (hR p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hab).mp rfl
    exact ⟨ha, hb, hχ⟩
  · rintro ⟨hx, hy, hχ⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (hR p).mpr ⟨x, y, hx, hy, hp, hχ⟩, hp⟩

private theorem clean_exists_l {B β C X Y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒱 [] Δ)
    (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C)
    (χ : type_l hℳ → type_l hℳ → Prop)
    (hRead : ∀ x y, φ.satisfies ((η.pushFree y).pushFree x) ↔ χ x y) :
    ∃ R, mem_l hℳ R C ∧ graph_l (𝒩 := 𝒱) X Y R χ := by
  obtain ⟨R, hRC, hR⟩ := PowerlessRelativeLimitRelationalGraph.exists_member_l
    hBase hLimit hC hφ η hX hY hParams
  exact ⟨R, hRC, fun p => (hR p).trans (exists_congr fun x => exists_congr fun y =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (hRead x y))))⟩

/-- 四个比较图均取精确成员版本；辅助图也不附带任意垃圾。 -/
def spec_l (ω A P S I J N T K U : type_l hℳ) : Prop :=
  PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A S ∧
  PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) ω S I ∧
  PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) ω I J ∧
  graph_l (𝒩 := 𝒱) ω ω N (fun x y => mem_l hℳ x y) ∧
  graph_l (𝒩 := 𝒱) S S T
    (PowerlessRelativeClassSequenceOrderGraph.shortlex_l (ℳ₀ := 𝒱) ω A P) ∧
  graph_l (𝒩 := 𝒱) I I K
    (PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω S N T) ∧
  graph_l (𝒩 := 𝒱) J J U
    (PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω I N K)

private theorem lex_values_l {X Y Z R T K : type_l hℳ}
    (hZ : PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) X Y Z)
    (hK : graph_l (𝒩 := 𝒱) Z Z K
      (PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) X Y R T)) :
    ∀ p q, value_l (ℳ := 𝒱) K p q ↔
      PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) X Y R T p q := by
  intro p q
  constructor
  · exact fun h => ((graph_values_l hK p q).mp h).2.2
  · intro hLex
    have hCopy := hLex
    obtain ⟨x, y, a, b, hx, hy, ha, hb, hp, hq, _⟩ := hCopy
    exact (graph_values_l hK p q).mpr
      ⟨(hZ p).mpr ⟨x, y, hx, hy, hp⟩, (hZ q).mpr ⟨a, b, ha, hb, hq⟩, hLex⟩

/-- 全 raw 读数；短序和字典序自带坐标合法性，故可消去额外母域守卫。 -/
theorem reading_l {ω A P S I J N T K U : type_l hℳ}
    (h : spec_l ω A P S I J N T K U) :
    (∀ x y, value_l (ℳ := 𝒱) N x y ↔
      mem_l hℳ x ω ∧ mem_l hℳ y ω ∧ mem_l hℳ x y) ∧
    (∀ f g, value_l (ℳ := 𝒱) T f g ↔
      PowerlessRelativeClassSequenceOrderGraph.shortlex_l (ℳ₀ := 𝒱) ω A P f g) ∧
    (∀ p q, value_l (ℳ := 𝒱) K p q ↔
      PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω S N T p q) ∧
    (∀ p q, value_l (ℳ := 𝒱) U p q ↔
      PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω I N K p q) := by
  obtain ⟨hS, hI, hJ, hN, hT, hK, hU⟩ := h
  refine ⟨graph_values_l hN, ?_, lex_values_l hI hK, lex_values_l hJ hU⟩
  intro f g
  constructor
  · exact fun h => ((graph_values_l hT f g).mp h).2.2
  · intro hLex
    have hCopy := hLex
    obtain ⟨n, m, hn, hm, hf, hg, _⟩ := hCopy
    exact (graph_values_l hT f g).mpr
      ⟨(hS f).mpr ⟨n, hn, hf⟩, (hS g).mpr ⟨m, hm, hg⟩, hLex⟩

/-- 原规范指标规格保持不变；只有内部辅助比较图选择了无垃圾版本。 -/
theorem to_index_l {ω A P S I J N T K U : type_l hℳ}
    (h : spec_l ω A P S I J N T K U) :
    PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒱) ω A P S I J U := by
  obtain ⟨hN, hT, hK, hU⟩ := reading_l h
  have hProper : PowerlessRelativeClassSatisfactionIndexCanonical.proper_l (ℳ₀ := 𝒱) U := by
    intro p hp
    obtain ⟨x, y, _, _, hxy, _⟩ := (h.2.2.2.2.2.2 p).mp hp
    exact ⟨x, y, hxy⟩
  exact ⟨h.1, h.2.1, h.2.2.1, hProper, N, T, K, hN, hT, hK, hU⟩

section

variable (hℳ)
include hℳ

/-- 真实同层构造；最后的环境良序由既有规范指标唯一性恢复。 -/
theorem exists_l
    {B β C ω A P : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωC : mem_l hℳ ω C) (hAC : mem_l hℳ A C) (hPC : mem_l hℳ P C)
    (hP : wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) A P) :
    ∃ S I J N T K U : type_l hℳ,
      mem_l hℳ S C ∧ mem_l hℳ I C ∧ mem_l hℳ J C ∧ mem_l hℳ N C ∧
      mem_l hℳ T C ∧ mem_l hℳ K C ∧ mem_l hℳ U C ∧
      spec_l ω A P S I J N T K U ∧
      PowerlessRelativeClassSatisfactionIndexCanonical.spec_l
        (ℳ₀ := SecondOrderQuotient.structure_l hℳ) ω A P S I J U ∧
      wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) J U := by
  -- 完整序列与积先各自在固定 C 内构造，不要求存在严格较早极限层。
  obtain ⟨S, hSC, hS⟩ := PowerlessRelativeLimitFiniteSequencesDirect.exists_l
    hBase hLimit hC hω hωC hAC
  obtain ⟨I, hI₀⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty ω S
  have hI : PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) ω S I := by
    simpa only [PowerlessRelativeClassSatisfactionIndexCanonical.product_l,
      ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l, ThirdOrderSemantics.member_l,
      SecondOrderPairObjects.ordered_l, SecondOrderPairObjects.pair_l,
      SecondOrderQuotient.structure_l, Formula.satisfies, true_and] using hI₀
  have hIC := PowerlessRelativeLimitProduct.member_l hBase hLimit hC hωC hSC hI
  obtain ⟨J, hJ₀⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty ω I
  have hJ : PowerlessRelativeClassSatisfactionIndexCanonical.product_l (ℳ₀ := 𝒱) ω I J := by
    simpa only [PowerlessRelativeClassSatisfactionIndexCanonical.product_l,
      ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l, ThirdOrderSemantics.member_l,
      SecondOrderPairObjects.ordered_l, SecondOrderPairObjects.pair_l,
      SecondOrderQuotient.structure_l, Formula.satisfies, true_and] using hJ₀
  have hJC := PowerlessRelativeLimitProduct.member_l hBase hLimit hC hωC hIC hJ
  let φN : Formula ℒ [] [.set, .set] := SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨N, hNC, hN⟩ := clean_exists_l hBase hLimit hC (φ := φN) (.rel _ _) Env.empty
    hωC hωC (by intro s v; nomatch v) (fun x y => mem_l hℳ x y) (by intro x y; rfl)
  let φT : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    PowerlessRelativeClassSequenceOrderGraph.shortlex_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let ηT : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree P).pushFree A).pushFree ω
  have hParamsT : ∀ s (v : Variable
      [SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (ηT.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact hAC
      | there v => cases v with
        | here => exact hPC
        | there v => nomatch v
  obtain ⟨T, hTC, hT⟩ := clean_exists_l hBase hLimit hC (φ := φT)
    (PowerlessRelativeClassSequenceOrderGraph.shortlex_delta_l _ _ _ _ _) ηT hSC hSC hParamsT
    (PowerlessRelativeClassSequenceOrderGraph.shortlex_l (ℳ₀ := 𝒱) ω A P)
    (fun _ _ => PowerlessRelativeClassSequenceOrderGraph.shortlex_formula_l _ _ _ _ _ _)
  let φK : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassLexicographicWellOrder.lex_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.fvar (.there .here))
  let ηK : Env 𝒱 [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree T).pushFree N).pushFree S).pushFree ω
  have hParamsK : ∀ s (v : Variable
      [SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (ηK.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact hSC
      | there v => cases v with
        | here => exact hNC
        | there v => cases v with
          | here => exact hTC
          | there v => nomatch v
  obtain ⟨K, hKC, hK⟩ := clean_exists_l hBase hLimit hC (φ := φK)
    (PowerlessRelativeClassLexicographicWellOrder.lex_delta_l _ _ _ _ _ _) ηK hIC hIC hParamsK
    (PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω S N T)
    (fun _ _ => PowerlessRelativeClassLexicographicWellOrder.lex_formula_l _ _ _ _ _ _ _)
  let ηU : Env 𝒱 [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree K).pushFree N).pushFree I).pushFree ω
  have hParamsU : ∀ s (v : Variable
      [SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (ηU.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact hIC
      | there v => cases v with
        | here => exact hNC
        | there v => cases v with
          | here => exact hKC
          | there v => nomatch v
  obtain ⟨U, hUC, hU⟩ := clean_exists_l hBase hLimit hC (φ := φK)
    (PowerlessRelativeClassLexicographicWellOrder.lex_delta_l _ _ _ _ _ _) ηU hJC hJC hParamsU
    (PowerlessRelativeClassLexicographicWellOrder.lex_l (ℳ₀ := 𝒱) ω I N K)
    (fun _ _ => PowerlessRelativeClassLexicographicWellOrder.lex_formula_l _ _ _ _ _ _ _)
  have hSpec : spec_l ω A P S I J N T K U := ⟨hS, hI, hJ, hN, hT, hK, hU⟩
  have hIndex := to_index_l hSpec
  -- 原类内包只用于给出已经证明的环境良序；不要求其辅助垃圾图有层界。
  have hCClass := PowerlessRelativeLevelClosure.class_l hℳ hBase hC
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hωC⟩
  let A' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨A, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hAC⟩
  let P' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨P, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hCClass hPC⟩
  have hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  obtain ⟨S₀, I₀, J₀, U₀, hIndex₀, hOrder₀⟩ :=
    PowerlessRelativeClassSatisfactionIndexCanonical.exists_l (hBase := hBase)
      (A := A') (P := P') hΩ hP
  have hRawIndex₀ := PowerlessCanonicalIndexAbsolute.spec_absolute_l (hBase := hBase) hΩ hIndex₀
  have hEqual := SecondOrderCanonicalIndexUnique.unique_l hIndex hRawIndex₀
  have hOrder : wellOrder_l (ℳ := 𝒱) J U := by
    rw [hEqual.2.2.1, hEqual.2.2.2]
    exact hOrder₀
  exact ⟨S, I, J, N, T, K, U, hSC, hIC, hJC, hNC, hTC, hKC, hUC, hSpec, hIndex, hOrder⟩

end

#print axioms reading_l
#print axioms to_index_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitCanonicalIndex
