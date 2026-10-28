import BMSConstructibleBridge.SecondOrderComparisonEncodeSyntax
import BMSConstructibleBridge.SecondOrderWellOrderCoherentUnionDerives
import BMSConstructibleBridge.SecondOrderComparisonHistoryDecode

/-! # 任意前驱比较历史的纯极限行

完整并图的存在和行唯一性不要求历史已经良序或相容，只须层成员有集合界。
良序保持另行消费原相容并集定理。局部性只比较指定前驱域 I 上的历史值，
不检查未来行；因此非法历史也不会破坏该分支的总性或局部性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonLimitSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderWellOrderCoherentUnion (stage_l edge_l graph_l cover_l)
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def output_m {Γ Δ : SortContext ℒ} (ω e I F G f W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj
    (SecondOrderWellOrderCoherentUnionDerives.graph_m (up I) (up F) (up G) (.bvar .here))
    (SecondOrderComparisonEncodeSyntax.formula_m (up ω) (up e) (up W) (up f) (.bvar .here))

def output_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e I F G f W : carrier_l 𝒩) : Prop :=
  ∃ L, graph_l (ℳ₀ := 𝒩) I F G L ∧ SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒩) ω e W f L

theorem output_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e I F G f W : Term ℒ Γ Δ .set) :
    (output_m ω e I F G f W).satisfies η ↔
      output_l (ω.eval η) (e.eval η) (I.eval η) (F.eval η) (G.eval η) (f.eval η) (W.eval η) := by
  simp only [output_m, output_l, Formula.satisfies, SecondOrderWellOrderCoherentUnionDerives.graph_formula_l,
    SecondOrderComparisonEncodeSyntax.formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 指定域上的全部历史值相同，足以保持并图；域外值不参与。 -/
theorem edge_congr_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {I F G H : carrier_l 𝒩}
    (h : ∀ i, member_l 𝒩 i I → ∀ R, value_l (ℳ := 𝒩) G i R ↔ value_l (ℳ := 𝒩) H i R)
    (x y : carrier_l 𝒩) : edge_l (ℳ₀ := 𝒩) I F G x y ↔ edge_l (ℳ₀ := 𝒩) I F H x y := by
  constructor
  · rintro ⟨i, A, R, hi, hx, hy, hxy⟩
    exact ⟨i, A, R, ⟨hi.1, hi.2.1, (h i hi.1 R).mp hi.2.2⟩, hx, hy, hxy⟩
  · rintro ⟨i, A, R, hi, hx, hy, hxy⟩
    exact ⟨i, A, R, ⟨hi.1, hi.2.1, (h i hi.1 R).mpr hi.2.2⟩, hx, hy, hxy⟩

theorem graph_congr_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {I F G H : carrier_l 𝒩}
    (h : ∀ i, member_l 𝒩 i I → ∀ R, value_l (ℳ := 𝒩) G i R ↔ value_l (ℳ := 𝒩) H i R)
    (L : carrier_l 𝒩) : graph_l (ℳ₀ := 𝒩) I F G L ↔ graph_l (ℳ₀ := 𝒩) I F H L := by
  unfold graph_l
  exact forall_congr' (fun _ => iff_congr Iff.rfl
    (exists_congr (fun x => exists_congr (fun y => and_congr (edge_congr_l h x y) Iff.rfl))))

theorem local_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {ω e I F G H f W : carrier_l 𝒩}
    (h : ∀ i, member_l 𝒩 i I → ∀ R, value_l (ℳ := 𝒩) G i R ↔ value_l (ℳ := 𝒩) H i R) :
    output_l (𝒩 := 𝒩) ω e I F G f W ↔ output_l (𝒩 := 𝒩) ω e I F H f W :=
  exists_congr (fun L => and_congr (graph_congr_l h L) Iff.rfl)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原历史在前驱实数行上的局部性，经实际图解码传给纯极限输出。 -/
theorem history_local_l (K : source_coding_l hℳ)
    (I : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) {E H H' : SecondOrderModel.set_l ℳ}
    (hI : setRel_l K I E) {C f F G G' W : type_l hℳ}
    (hG : ∀ i P, value_l (ℳ := 𝒱) G (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hG' : ∀ i P, value_l (ℳ := 𝒱) G' (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H' i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hPast : ∀ i, SecondOrderModel.mem_l i E → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t) :
    output_l (𝒩 := 𝒱) K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val I.val F G f W ↔
      output_l (𝒩 := 𝒱) K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val I.val F G' f W :=
  local_l (SecondOrderComparisonHistoryDecode.value_congr_l K I hI hG hG' hPast)

/-- 载体覆盖使完整并图为集合；总性没有相容、良序或映射前提。 -/
theorem graph_total_l {C I F G : type_l hℳ} (hCover : cover_l (ℳ₀ := 𝒱) C I F) :
    ∃ L : type_l hℳ, graph_l (ℳ₀ := 𝒱) I F G L := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := SecondOrderWellOrderCoherentUnion.edge_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree G).pushFree F).pushFree I
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔ edge_l (ℳ₀ := 𝒱) I F G x y :=
    SecondOrderWellOrderCoherentUnion.edge_formula_l _ _ _ _ _ _
  obtain ⟨L, hL⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η C C
  refine ⟨L, fun p => (hL p).trans ⟨?_, ?_⟩⟩
  · rintro ⟨x, y, _, _, hxy, hp⟩
    exact ⟨x, y, (hφ x y).mp hxy, hp⟩
  · rintro ⟨x, y, hEdge, hp⟩
    obtain ⟨i, A, R, hi, hx, hy, hxy⟩ := hEdge
    exact ⟨x, y, (hCover x).mpr ⟨i, A, hi.1, hi.2.1, hx⟩,
      (hCover y).mpr ⟨i, A, hi.1, hi.2.1, hy⟩,
      (hφ x y).mpr ⟨i, A, R, hi, hx, hy, hxy⟩, hp⟩

theorem exists_unique_l (K : source_coding_l hℳ) {C I F G f : type_l hℳ}
    (hCover : cover_l (ℳ₀ := 𝒱) C I F) :
    ∃! S : type_l hℳ, output_l (𝒩 := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val I F G f S := by
  obtain ⟨L, hGraph⟩ := graph_total_l (G := G) hCover
  obtain ⟨W, hW, _⟩ := SecondOrderComparisonReal.exists_unique_l K f L
  obtain ⟨S, hS⟩ := representative_exists_l K W
  have hEncoded := (SecondOrderComparisonEncodeSyntax.reading_l K S W hS f L).mpr hW
  refine ⟨S.val, ⟨L, hGraph, hEncoded⟩, ?_⟩
  rintro X ⟨L', hGraph', hEncoded'⟩
  have hEq := SecondOrderWellOrderCoherentUnion.graph_unique_l hGraph' hGraph
  subst L'
  let X' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega :=
    ⟨X, SecondOrderComparisonEncodeSyntax.guard_l hEncoded'⟩
  obtain ⟨U, hU⟩ := PowerlessBMSQuotientReals.trace_exists_l K X'
  have hUW : U = W := SecondOrderComparisonReal.unique_l K
    ((SecondOrderComparisonEncodeSyntax.reading_l K X' U hU f L).mp hEncoded') hW
  exact congrArg Subtype.val (PowerlessBMSQuotientReals.representative_unique_l K (hUW ▸ hU) hS)

/-- 良序保持独立消费真正相容的实际历史，不参与上面的非法输入总性。 -/
theorem order_l {C I J F G X Y L : type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I J) (hF : map_l (ℳ := 𝒱) F I X) (hG : map_l (ℳ := 𝒱) G I Y)
    (hCoherent : SecondOrderWellOrderCoherentUnion.coherent_l (ℳ₀ := 𝒱) I J F G)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R → wellOrder_l (ℳ := 𝒱) A R)
    (hCover : cover_l (ℳ₀ := 𝒱) C I F) (hL : graph_l (ℳ₀ := 𝒱) I F G L) :
    wellOrder_l (ℳ := 𝒱) C L := by
  obtain ⟨T, hT, hOrder, _⟩ := SecondOrderWellOrderCoherentUnion.graph_exists_l hJ hF hG hCoherent hStages hCover
  exact SecondOrderWellOrderCoherentUnion.graph_unique_l hT hL ▸ hOrder

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonLimitSyntax
