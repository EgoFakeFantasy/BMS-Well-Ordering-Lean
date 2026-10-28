import BMSConstructibleBridge.PowerlessRelativeClassRowFamily
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullbackAmbient
import BMSConstructibleBridge.PowerlessRelativeClassRelationAmbientMembers
import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderSlices

/-! # 行像集的规范最小表示序

比较正文只读取指标集、其良序、母集和查询关系，不含辅助行函数或截面。
实际行族统一界保证图存在；环境最小元条款来自已证单射拉回。
精确图成员规格另外排除垃圾，故规范图唯一性是对象相等而非仅逐值一致。
本模块仍不提供跨层历史的存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowOrderCanonical

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassRowFamily (row_l row_m row_delta_l row_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def minimal_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I U A Q y i : carrier_l ℳ₀) : Prop :=
  row_l A Q i y ∧ ∀ j, member_l ℳ₀ j I → row_l A Q j y → ¬value_l U j i

def minimal_m {Γ Δ : SortContext ℒ} (I U A Q y i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (row_m A Q i y) <| membershipLevyBound.boundedForall I <|
    .imp (row_m (up A) (up Q) (.bvar .here) (up y))
      (.neg (PowerlessValueBounded.formula_m (up U) (.bvar .here) (up i)))

theorem minimal_delta_l {Γ Δ : SortContext ℒ} (I U A Q y i : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (minimal_m I U A Q y i) :=
  .conj (row_delta_l _ _ _ _) (.bounded_forall _
    (.imp (row_delta_l _ _ _ _) (.neg (PowerlessValueBounded.delta_l _ _ _))))

theorem minimal_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I U A Q y i : Term ℒ Γ Δ .set) :
    (minimal_m I U A Q y i).satisfies η ↔
      minimal_l (I.eval η) (U.eval η) (A.eval η) (Q.eval η) (y.eval η) (i.eval η) := by
  simp only [minimal_m, minimal_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, row_formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def comparison_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I U A Q x y : carrier_l ℳ₀) : Prop :=
  ∃ i j, member_l ℳ₀ i I ∧ member_l ℳ₀ j I ∧
    minimal_l I U A Q x i ∧ minimal_l I U A Q y j ∧ value_l U i j

def comparison_m {Γ Δ : SortContext ℒ} (I U A Q x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <| membershipLevyBound.boundedExists (up I) <|
    .conj (minimal_m (up (up I)) (up (up U)) (up (up A)) (up (up Q))
      (up (up x)) (.bvar (.there .here))) <|
      .conj (minimal_m (up (up I)) (up (up U)) (up (up A)) (up (up Q))
        (up (up y)) (.bvar .here))
        (PowerlessValueBounded.formula_m (up (up U)) (.bvar (.there .here)) (.bvar .here))

theorem comparison_delta_l {Γ Δ : SortContext ℒ} (I U A Q x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (comparison_m I U A Q x y) :=
  .bounded_exists _ (.bounded_exists _ (.conj (minimal_delta_l _ _ _ _ _ _)
    (.conj (minimal_delta_l _ _ _ _ _ _) (PowerlessValueBounded.delta_l _ _ _))))

theorem comparison_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I U A Q x y : Term ℒ Γ Δ .set) :
    (comparison_m I U A Q x y).satisfies η ↔
      comparison_l (I.eval η) (U.eval η) (A.eval η) (Q.eval η) (x.eval η) (y.eval η) := by
  simp only [comparison_m, comparison_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, minimal_formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨i, hi, j, hj, hx, hy, h⟩ => ⟨i, j, hi, hj, hx, hy, h⟩,
    fun ⟨i, j, hi, hj, hx, hy, h⟩ => ⟨i, hi, j, hj, hx, hy, h⟩⟩

def graph_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I U A Q Y L : carrier_l ℳ₀) : Prop :=
  ∀ p, member_l ℳ₀ p L ↔ ∃ x y, member_l ℳ₀ x Y ∧ member_l ℳ₀ y Y ∧
    ordered_l x y p ∧ comparison_l I U A Q x y

def family_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I A Q Y : carrier_l ℳ₀) : Prop :=
  ∀ y, member_l ℳ₀ y Y ↔ ∃ i, member_l ℳ₀ i I ∧ row_l A Q i y

/-- 辅助查询图可以不同；只需全部相关读值相同。 -/
theorem row_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A Q R : carrier_l ℳ₀}
    (hQ : ∀ i x, value_l (ℳ := ℳ₀) Q i x ↔ value_l (ℳ := ℳ₀) R i x) (i y : carrier_l ℳ₀) :
    row_l (ℳ₀ := ℳ₀) A Q i y ↔ row_l (ℳ₀ := ℳ₀) A R i y :=
  forall_congr' fun x => iff_congr Iff.rfl (and_congr Iff.rfl (hQ i x))

theorem minimal_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {I U V A Q R : carrier_l ℳ₀}
    (hU : ∀ i j, value_l (ℳ := ℳ₀) U i j ↔ value_l (ℳ := ℳ₀) V i j)
    (hQ : ∀ i x, value_l (ℳ := ℳ₀) Q i x ↔ value_l (ℳ := ℳ₀) R i x) (y i : carrier_l ℳ₀) :
    minimal_l (ℳ₀ := ℳ₀) I U A Q y i ↔ minimal_l (ℳ₀ := ℳ₀) I V A R y i := by
  constructor
  · rintro ⟨hRow, hLeast⟩
    exact ⟨(row_congr_l hQ i y).mp hRow,
      fun j hj hRow' hji => hLeast j hj ((row_congr_l hQ j y).mpr hRow') ((hU j i).mpr hji)⟩
  · rintro ⟨hRow, hLeast⟩
    exact ⟨(row_congr_l hQ i y).mpr hRow,
      fun j hj hRow' hji => hLeast j hj ((row_congr_l hQ j y).mp hRow') ((hU j i).mp hji)⟩

theorem comparison_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {I U V A Q R : carrier_l ℳ₀}
    (hU : ∀ i j, value_l (ℳ := ℳ₀) U i j ↔ value_l (ℳ := ℳ₀) V i j)
    (hQ : ∀ i x, value_l (ℳ := ℳ₀) Q i x ↔ value_l (ℳ := ℳ₀) R i x) (x y : carrier_l ℳ₀) :
    comparison_l (ℳ₀ := ℳ₀) I U A Q x y ↔ comparison_l (ℳ₀ := ℳ₀) I V A R x y :=
  exists_congr fun i => exists_congr fun j => and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr (minimal_congr_l hU hQ x i) (and_congr (minimal_congr_l hU hQ y j) (hU i j))))

theorem graph_congr_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {I U V A Q R Y L : carrier_l ℳ₀}
    (hU : ∀ i j, value_l (ℳ := ℳ₀) U i j ↔ value_l (ℳ := ℳ₀) V i j)
    (hQ : ∀ i x, value_l (ℳ := ℳ₀) Q i x ↔ value_l (ℳ := ℳ₀) R i x)
    (hL : graph_l (ℳ₀ := ℳ₀) I U A Q Y L) : graph_l (ℳ₀ := ℳ₀) I V A R Y L :=
  fun p => (hL p).trans (exists_congr fun x => exists_congr fun y =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (comparison_congr_l hU hQ x y))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem graph_unique_l {I U A Q Y L T : SecondOrderQuotient.type_l hℳ}
    (hL : graph_l (ℳ₀ := 𝒱) I U A Q Y L) (hT : graph_l (ℳ₀ := 𝒱) I U A Q Y T) : L = T :=
  SecondOrderQuotient.ext_l hℳ L T (fun p => (hL p).trans (hT p).symm)

theorem family_unique_l {I A Q Y Z : type_l hℳ B}
    (hY : family_l (ℳ₀ := 𝒞) I A Q Y) (hZ : family_l (ℳ₀ := 𝒞) I A Q Z) : Y = Z := by
  apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
  intro y
  exact (hY y).trans (hZ y).symm

theorem exists_l (I A Q U : type_l hℳ B) (hU : wellOrder_l (ℳ := 𝒱) I.val U.val) :
    ∃ Y L : type_l hℳ B, family_l (ℳ₀ := 𝒞) I A Q Y ∧
      graph_l (ℳ₀ := 𝒱) I.val U.val A.val Q.val Y.val L.val ∧ wellOrder_l (ℳ := 𝒱) Y.val L.val := by
  obtain ⟨Y, F, hF, hOnto, hFRead, hFamily⟩ := PowerlessRelativeClassRowFamily.exists_l I A Q
  obtain ⟨G, hG, hInject, hGRead⟩ := PowerlessRelativeClassWellOrderSection.exists_l hF
    (PowerlessRelativeClassAmbientWellOrder.restrict_l hU) hOnto
  obtain ⟨L₀, hL₀, hL₀Read⟩ := PowerlessRelativeClassWellOrderPullbackAmbient.exists_l hG hInject hU
  have hMin (y i : type_l hℳ B) (hi : mem_l hℳ i.val I.val) :
      PowerlessRelativeClassWellOrderSection.minimal_l (ℳ₀ := 𝒞) I U F y i ↔
        minimal_l (ℳ₀ := 𝒞) I U A Q y i := by
    constructor
    · rintro ⟨hValue, hLeast⟩
      exact ⟨((hFRead i y).mp hValue).2,
        fun j hj hRow => hLeast j hj ((hFRead j y).mpr ⟨hj, hRow⟩)⟩
    · rintro ⟨hRow, hLeast⟩
      exact ⟨(hFRead i y).mpr ⟨hi, hRow⟩,
        fun j hj hValue => hLeast j hj ((hFRead j y).mp hValue).2⟩
  have hCompare (x y : type_l hℳ B) (hx : mem_l hℳ x.val Y.val) (hy : mem_l hℳ y.val Y.val) :
      PowerlessRelativeClassWellOrderPullback.comparison_l (ℳ₀ := 𝒞) I G U x y ↔
        comparison_l (ℳ₀ := 𝒞) I U A Q x y := by
    constructor
    · rintro ⟨i, j, hi, hj, hxi, hyj, hij⟩
      exact ⟨i, j, hi, hj, (hMin x i hi).mp ((hGRead x i).mp hxi).2.2,
        (hMin y j hj).mp ((hGRead y j).mp hyj).2.2, hij⟩
    · rintro ⟨i, j, hi, hj, hxi, hyj, hij⟩
      exact ⟨i, j, hi, hj, (hGRead x i).mpr ⟨hx, hi, (hMin x i hi).mpr hxi⟩,
        (hGRead y j).mpr ⟨hy, hj, (hMin y j hj).mpr hyj⟩, hij⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := comparison_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒞 [] [.set, .set, .set, .set] := (((Env.empty.pushFree Q).pushFree A).pushFree U).pushFree I
  obtain ⟨L, hMembers, hRead⟩ := PowerlessRelativeClassRelationAmbientMembers.exists_spec_l
    (comparison_delta_l _ _ _ _ _ _) η Y Y
  have hRawφ x y : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) ↔
      comparison_l (ℳ₀ := 𝒱) I.val U.val A.val Q.val x y := comparison_formula_l _ _ _ _ _ _ _
  have hClassφ (x y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree x) ↔
      comparison_l (ℳ₀ := 𝒞) I U A Q x y := comparison_formula_l _ _ _ _ _ _ _
  have hClassRead (x y : type_l hℳ B) : value_l (ℳ := 𝒞) L x y ↔
      mem_l hℳ x.val Y.val ∧ mem_l hℳ y.val Y.val ∧ comparison_l (ℳ₀ := 𝒞) I U A Q x y :=
    (hRead x y).trans (and_congr Iff.rfl (and_congr Iff.rfl (hClassφ x y)))
  have hClassEq (x y : type_l hℳ B) (hx : mem_l hℳ x.val Y.val) (hy : mem_l hℳ y.val Y.val) :
      value_l (ℳ := 𝒞) L₀ x y ↔ value_l (ℳ := 𝒞) L x y :=
    (hL₀Read x y).trans ((and_iff_right hx).trans ((and_iff_right hy).trans
      ((hCompare x y hx hy).trans
        ((hClassRead x y).trans ((and_iff_right hx).trans (and_iff_right hy))).symm)))
  have hOrder : wellOrder_l (ℳ := 𝒱) Y.val L.val := by
    apply PowerlessRelativeClassSequenceOrderSlices.wellOrder_congr_l hL₀
    intro x hx y hy
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hx⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) L₀ x' y').symm.trans
      ((hClassEq x' y' hx hy).trans (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) L x' y'))
  exact ⟨Y, L, hFamily, fun p => (hMembers p).trans (exists_congr fun x => exists_congr fun y =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (hRawφ x y)))), hOrder⟩

theorem exists_unique_l (I A Q U : type_l hℳ B) (hU : wellOrder_l (ℳ := 𝒱) I.val U.val) :
    ∃! Y : type_l hℳ B, family_l (ℳ₀ := 𝒞) I A Q Y ∧
      ∃! L : type_l hℳ B, graph_l (ℳ₀ := 𝒱) I.val U.val A.val Q.val Y.val L.val ∧
        wellOrder_l (ℳ := 𝒱) Y.val L.val := by
  obtain ⟨Y, L, hFamily, hGraph, hOrder⟩ := exists_l I A Q U hU
  exact ⟨Y, ⟨hFamily, L, ⟨hGraph, hOrder⟩,
    fun T hT => Subtype.ext (graph_unique_l hT.1 hGraph)⟩,
    fun Z hZ => family_unique_l hZ.1 hFamily⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRowOrderCanonical
