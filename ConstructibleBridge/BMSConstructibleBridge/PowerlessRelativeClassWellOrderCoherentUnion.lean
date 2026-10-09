import BMSConstructibleBridge.PowerlessRelativeClassRelationAmbientMembers
import BMSConstructibleBridge.SecondOrderWellOrderCoherentUnionDerives

/-! # 相容历史的完整并集序图仍属于原相对类

历史的阶段、载体值和序图值由实际集合函数的母集界住，比较正文因此
是实际 Δ₀ 公式。类内分离给出完整图，环境图唯一性将它与已证明的
环境良序图对齐。这不构造整条历史，也不增加一般 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderCoherentUnion

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderWellOrderCoherentUnion (stage_l edge_l graph_l coherent_l cover_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def bounded_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (I F G X Y x y : carrier_l ℳ₀) : Prop :=
  ∃ i, member_l ℳ₀ i I ∧ ∃ A, member_l ℳ₀ A X ∧ ∃ R, member_l ℳ₀ R Y ∧
    value_l F i A ∧ value_l G i R ∧ member_l ℳ₀ x A ∧ member_l ℳ₀ y A ∧ value_l R x y

def bounded_m {Γ Δ : SortContext ℒ} (I F G X Y x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <|
    membershipLevyBound.boundedExists (up X) <|
      membershipLevyBound.boundedExists (up (up Y)) <|
        .conj (PowerlessValueBounded.formula_m (up (up (up F)))
          (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
          .conj (PowerlessValueBounded.formula_m (up (up (up G)))
            (.bvar (.there (.there .here))) (.bvar .here)) <|
            .conj (member_m (up (up (up x))) (.bvar (.there .here))) <|
              .conj (member_m (up (up (up y))) (.bvar (.there .here)))
                (PowerlessValueBounded.formula_m (.bvar .here) (up (up (up x))) (up (up (up y))))

theorem bounded_delta_l {Γ Δ : SortContext ℒ} (I F G X Y x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (bounded_m I F G X Y x y) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.conj (PowerlessValueBounded.delta_l _ _ _)
        (.conj (.rel _ _) (.conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)))))))

theorem bounded_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I F G X Y x y : Term ℒ Γ Δ .set) :
    (bounded_m I F G X Y x y).satisfies η ↔
      bounded_l (I.eval η) (F.eval η) (G.eval η) (X.eval η) (Y.eval η) (x.eval η) (y.eval η) := by
  simp only [bounded_m, bounded_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

theorem bounded_edge_l {I F G X Y x y : SecondOrderQuotient.type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F I X) (hG : map_l (ℳ := 𝒱) G I Y) :
    bounded_l (ℳ₀ := 𝒱) I F G X Y x y ↔ edge_l (ℳ₀ := 𝒱) I F G x y := by
  constructor
  · rintro ⟨i, hi, A, _, R, _, hiA, hiR, hx, hy, hxy⟩
    exact ⟨i, A, R, ⟨hi, hiA, hiR⟩, hx, hy, hxy⟩
  · rintro ⟨i, A, R, hi, hx, hy, hxy⟩
    exact ⟨i, hi.1, A, (SecondOrderFunctionLaws.value_mem_l hℳ hF hi.2.1).2,
      R, (SecondOrderFunctionLaws.value_mem_l hℳ hG hi.2.2).2, hi.2.1, hi.2.2, hx, hy, hxy⟩

include hBase

theorem exists_l {C I F G X Y : type_l hℳ B} {J : SecondOrderQuotient.type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I.val J)
    (hF : map_l (ℳ := 𝒱) F.val I.val X.val) (hG : map_l (ℳ := 𝒱) G.val I.val Y.val)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I.val J F.val G.val)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I.val F.val G.val i A R → wellOrder_l (ℳ := 𝒱) A R)
    (hCover : cover_l (ℳ₀ := 𝒱) C.val I.val F.val) :
    ∃ L : type_l hℳ B, graph_l (ℳ₀ := 𝒱) I.val F.val G.val L.val ∧
      wellOrder_l (ℳ := 𝒱) C.val L.val := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := bounded_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒩 [] [.set, .set, .set, .set, .set] :=
    ((((Env.empty.pushFree Y).pushFree X).pushFree G).pushFree F).pushFree I
  have hφ x y : φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) ↔
      edge_l (ℳ₀ := 𝒱) I.val F.val G.val x y :=
    (bounded_formula_l _ _ _ _ _ _ _ _).trans (bounded_edge_l hF hG)
  obtain ⟨L, hL⟩ := PowerlessRelativeClassRelationAmbientMembers.exists_l
    (bounded_delta_l _ _ _ _ _ _ _) η C C
  have hGraph : graph_l (ℳ₀ := 𝒱) I.val F.val G.val L.val := by
    intro p
    refine (hL p).trans ?_
    constructor
    · rintro ⟨x, y, _, _, hp, h⟩
      exact ⟨x, y, (hφ x y).mp h, hp⟩
    · rintro ⟨x, y, hEdge, hp⟩
      have hBody := (hφ x y).mpr hEdge
      obtain ⟨i, A, R, hi, hx, hy, _⟩ := hEdge
      exact ⟨x, y, (hCover x).mpr ⟨i, A, hi.1, hi.2.1, hx⟩,
        (hCover y).mpr ⟨i, A, hi.1, hi.2.1, hy⟩, hp, hBody⟩
  obtain ⟨T, hT, hOrder, _⟩ :=
    SecondOrderWellOrderCoherentUnion.graph_exists_l hJ hF hG hCoherent hStages hCover
  have hEq : T = L.val := SecondOrderWellOrderCoherentUnion.graph_unique_l hT hGraph
  exact ⟨L, hGraph, hEq ▸ hOrder⟩

theorem exists_unique_l {C I F G X Y : type_l hℳ B} {J : SecondOrderQuotient.type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I.val J)
    (hF : map_l (ℳ := 𝒱) F.val I.val X.val) (hG : map_l (ℳ := 𝒱) G.val I.val Y.val)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I.val J F.val G.val)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I.val F.val G.val i A R → wellOrder_l (ℳ := 𝒱) A R)
    (hCover : cover_l (ℳ₀ := 𝒱) C.val I.val F.val) :
    ∃! L : type_l hℳ B, graph_l (ℳ₀ := 𝒱) I.val F.val G.val L.val ∧
      wellOrder_l (ℳ := 𝒱) C.val L.val := by
  obtain ⟨L, hGraph, hL⟩ := exists_l (hBase := hBase) hJ hF hG hCoherent hStages hCover
  exact ⟨L, ⟨hGraph, hL⟩, fun T hT =>
    Subtype.ext (SecondOrderWellOrderCoherentUnion.graph_unique_l hT.1 hGraph)⟩

#print axioms exists_l
#print axioms exists_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderCoherentUnion
