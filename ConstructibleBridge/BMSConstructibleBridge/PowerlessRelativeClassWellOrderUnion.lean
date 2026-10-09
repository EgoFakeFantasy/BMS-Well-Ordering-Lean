import BMSConstructibleBridge.PowerlessRelativeClassOrdinalOrder
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRange
import BMSConstructibleBridge.SecondOrderWellOrderCoherentUnion

/-! # 实际 Class 相容历史的环境良序并集

定义域、层历史、序图历史和载体均为实际 Class 对象。原序图历史的 raw
陪域不必是 Class：先取得其精确 Class 值域，再把阶段边关系写为 Δ₀。
环境良序的最小元仍对全部 raw 子集成立；不假设 cutoff Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderUnion

open Logic FirstOrder ThirdOrderSemantics StabilityFrame SecondOrderObjectSyntax
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def edgeBounded_m {Γ Δ : SortContext ℒ}
    (I F G X R x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <|
    membershipLevyBound.boundedExists (up X) <|
      membershipLevyBound.boundedExists (up (up R)) <|
        .conj (PowerlessValueBounded.formula_m (up₃ F)
          (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
          .conj (PowerlessValueBounded.formula_m (up₃ G)
            (.bvar (.there (.there .here))) (.bvar .here)) <|
            .conj (member_m (up₃ x) (.bvar (.there .here))) <|
              .conj (member_m (up₃ y) (.bvar (.there .here)))
                (PowerlessValueBounded.formula_m (.bvar .here) (up₃ x) (up₃ y))

theorem edgeBounded_delta_l {Γ Δ : SortContext ℒ}
    (I F G X R x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (edgeBounded_m I F G X R x y) :=
  .bounded_exists _ <| .bounded_exists _ <| .bounded_exists _ <|
    .conj (PowerlessValueBounded.delta_l _ _ _) <|
      .conj (PowerlessValueBounded.delta_l _ _ _) <|
        .conj (.rel _ _) <| .conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)

theorem edgeBounded_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (I F G X R x y : Term ℒ Γ Δ .set) :
    (edgeBounded_m I F G X R x y).satisfies η ↔
      ∃ i, member_l 𝒩 i (I.eval η) ∧ ∃ A, member_l 𝒩 A (X.eval η) ∧
        ∃ P, member_l 𝒩 P (R.eval η) ∧ value_l (ℳ := 𝒩) (F.eval η) i A ∧
          value_l (ℳ := 𝒩) (G.eval η) i P ∧ member_l 𝒩 (x.eval η) A ∧
            member_l 𝒩 (y.eval η) A ∧ value_l (ℳ := 𝒩) P (x.eval η) (y.eval η) := by
  simp only [edgeBounded_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (I F G C X : type_l hℳ B) {q : SecondOrderQuotient.type_l hℳ}
    (hI : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) I.val)
    (hF : map_l (ℳ := 𝒱) F.val I.val X.val) (hG : map_l (ℳ := 𝒱) G.val I.val q)
    (hCoherent : ∀ i j A P D S,
      SecondOrderWellOrderCoherentUnion.stage_l (ℳ₀ := 𝒱) I.val F.val G.val i A P →
      SecondOrderWellOrderCoherentUnion.stage_l (ℳ₀ := 𝒱) I.val F.val G.val j D S →
      mem_l hℳ i j → SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D S)
    (hStages : ∀ i A P,
      SecondOrderWellOrderCoherentUnion.stage_l (ℳ₀ := 𝒱) I.val F.val G.val i A P →
      wellOrder_l (ℳ := 𝒱) A P)
    (hCover : SecondOrderWellOrderCoherentUnion.cover_l (ℳ₀ := 𝒱) C.val I.val F.val) :
    ∃ L : type_l hℳ B, wellOrder_l (ℳ := 𝒱) C.val L.val ∧ ∀ x y,
      value_l (ℳ := 𝒱) L.val x y ↔
        SecondOrderWellOrderCoherentUnion.edge_l (ℳ₀ := 𝒱) I.val F.val G.val x y := by
  obtain ⟨J, hJ, hJRead⟩ := PowerlessRelativeClassOrdinalOrder.exists_l hBase I hI
  obtain ⟨R, hR⟩ := PowerlessRelativeClassFunctionRange.exists_l hBase I G hG
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree R |>.pushFree X |>.pushFree G |>.pushFree F |>.pushFree I
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    edgeBounded_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar .here) (.fvar (.there .here))
  have hBody x y :
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) ↔
        SecondOrderWellOrderCoherentUnion.edge_l (ℳ₀ := 𝒱) I.val F.val G.val x y := by
    rw [edgeBounded_formula_l]
    change (∃ i, mem_l hℳ i I.val ∧ ∃ A, mem_l hℳ A X.val ∧
      ∃ P, mem_l hℳ P R.val ∧ value_l (ℳ := 𝒱) F.val i A ∧
        value_l (ℳ := 𝒱) G.val i P ∧ mem_l hℳ x A ∧ mem_l hℳ y A ∧
          value_l (ℳ := 𝒱) P x y) ↔ _
    constructor
    · rintro ⟨i, hi, A, _hA, P, _hP, hiA, hiP, hx, hy, hxy⟩
      exact ⟨i, A, P, ⟨hi, hiA, hiP⟩, hx, hy, hxy⟩
    · rintro ⟨i, A, P, hi, hx, hy, hxy⟩
      exact ⟨i, hi.1, A, (SecondOrderFunctionProperties.value_mem_l hℳ hF hi.2.1).2,
        P, (hR P).mpr ⟨i, hi.2.2⟩, hi.2.1, hi.2.2, hx, hy, hxy⟩
  obtain ⟨L, hL⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (hBase := hBase) (edgeBounded_delta_l _ _ _ _ _ _ _) η C C
  have hRead x y : value_l (ℳ := 𝒱) L.val x y ↔
      SecondOrderWellOrderCoherentUnion.edge_l (ℳ₀ := 𝒱) I.val F.val G.val x y := by
    constructor
    · exact fun h => (hBody x y).mp ((hL x y).mp h).2.2
    · intro hEdge
      have hBodyEdge := (hBody x y).mpr hEdge
      obtain ⟨i, A, P, hi, hx, hy, _hxy⟩ := hEdge
      exact (hL x y).mpr ⟨(hCover x).mpr ⟨i, A, hi.1, hi.2.1, hx⟩,
        (hCover y).mpr ⟨i, A, hi.1, hi.2.1, hy⟩, hBodyEdge⟩
  have hCompatible : SecondOrderWellOrderCoherentUnion.coherent_l
      (ℳ₀ := 𝒱) I.val J.val F.val G.val := by
    intro i j A P D S hi hj hij
    exact hCoherent i j A P D S hi hj ((hJRead i j).mp hij).2.2
  exact ⟨L, SecondOrderWellOrderCoherentUnion.of_graph_l
    hJ hF hG hCompatible hStages hCover hRead, hRead⟩

#print axioms edgeBounded_formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassWellOrderUnion
