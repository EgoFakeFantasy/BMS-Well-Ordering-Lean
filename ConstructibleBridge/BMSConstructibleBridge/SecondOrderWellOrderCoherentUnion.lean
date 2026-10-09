import BMSConstructibleBridge.SecondOrderWellOrderEndExtension
import BMSConstructibleBridge.SecondOrderFunctionLaws
import BMSConstructibleBridge.SecondOrderUnion

/-! # 已给定相容历史的良序并集

历史 F、G 是模型内部的实际集合函数，不是宿主索引族。极限载体 C
由 F 的实际取值覆盖。任意非空环境子集先取其中一个成员所在的阶段，
在该阶段分离并取最小元；初段性排除任何更早的阶段外成员。
这不证明历史自身存在，也不借模型外部的序数良基或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderCoherentUnion

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def stage_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (I F G i A R : carrier_l ℳ₀) : Prop :=
  member_l ℳ₀ i I ∧ value_l F i A ∧ value_l G i R

def extension_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (A R D S : carrier_l ℳ₀) : Prop :=
  subset_l A D ∧
    (∀ x y, member_l ℳ₀ x A → member_l ℳ₀ y A → (value_l S x y ↔ value_l R x y)) ∧
    (∀ x y, member_l ℳ₀ x A → member_l ℳ₀ y D → value_l S y x → member_l ℳ₀ y A)

def coherent_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (I J F G : carrier_l ℳ₀) : Prop :=
  ∀ i j A R D S, stage_l I F G i A R → stage_l I F G j D S →
    value_l J i j → extension_l A R D S

def cover_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C I F : carrier_l ℳ₀) : Prop :=
  ∀ x, member_l ℳ₀ x C ↔ ∃ i A, member_l ℳ₀ i I ∧ value_l F i A ∧ member_l ℳ₀ x A

def edge_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (I F G x y : carrier_l ℳ₀) : Prop :=
  ∃ i A R, stage_l I F G i A R ∧ member_l ℳ₀ x A ∧ member_l ℳ₀ y A ∧ value_l R x y

/-- 完整成员规格排除不被比较值读取的非有序对垃圾。 -/
def graph_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (I F G L : carrier_l ℳ₀) : Prop :=
  ∀ p, member_l ℳ₀ p L ↔ ∃ x y, edge_l I F G x y ∧ ordered_l x y p

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem graph_unique_l {I F G L T : type_l hℳ}
    (hL : graph_l (ℳ₀ := 𝒱) I F G L) (hT : graph_l (ℳ₀ := 𝒱) I F G T) : L = T :=
  SecondOrderQuotient.ext_l hℳ L T (fun p => (hL p).trans (hT p).symm)

theorem carrier_unique_l {C D I F : type_l hℳ}
    (hC : cover_l (ℳ₀ := 𝒱) C I F) (hD : cover_l (ℳ₀ := 𝒱) D I F) : C = D :=
  SecondOrderQuotient.ext_l hℳ C D (fun x => (hC x).trans (hD x).symm)

theorem carrier_exists_l {I F X : type_l hℳ} (hF : map_l (ℳ := 𝒱) F I X) :
    ∃ C : type_l hℳ, cover_l (ℳ₀ := 𝒱) C I F := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .existsE .set <| .conj (member_m (.bvar .here) (.fvar (.there .here)))
      (value_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here))
  let η : Env 𝒱 [] [.set, .set] := (Env.empty.pushFree F).pushFree I
  obtain ⟨V, hV⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) X
  have hVRead A : mem_l hℳ A V ↔ mem_l hℳ A X ∧
      ∃ i, mem_l hℳ i I ∧ value_l (ℳ := 𝒱) F i A := by
    refine (hV A).trans (and_congr Iff.rfl ?_)
    simp only [φ, Formula.satisfies, value_formula_l, member_m, Arguments.eval, Term.eval]
    rfl
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : type_l hℳ, ∃ C, ∀ x, mem_l hℳ x C ↔ ∃ A, mem_l hℳ A a ∧ mem_l hℳ x A at hUnion
  obtain ⟨C, hC⟩ := hUnion V
  refine ⟨C, fun x => (hC x).trans ?_⟩
  constructor
  · rintro ⟨A, hA, hx⟩
    obtain ⟨i, hi, hiA⟩ := ((hVRead A).mp hA).2
    exact ⟨i, A, hi, hiA, hx⟩
  · rintro ⟨i, A, hi, hiA, hx⟩
    exact ⟨A, (hVRead A).mpr ⟨(SecondOrderFunctionLaws.value_mem_l hℳ hF hiA).2,
      i, hi, hiA⟩, hx⟩

/-- 历史两函数的值唯一性用于同一阶段，不能仅由序图的比较值推断图相等。 -/
theorem restrict_l {I J F G Y i A R x y : type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hG : map_l (ℳ := 𝒱) G I Y)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I J F G)
    (hi : stage_l (ℳ₀ := 𝒱) I F G i A R)
    (hx : mem_l hℳ x A) (hy : mem_l hℳ y A) :
    edge_l (ℳ₀ := 𝒱) I F G x y ↔ value_l (ℳ := 𝒱) R x y := by
  constructor
  · rintro ⟨j, D, S, hj, hxD, hyD, hxy⟩
    rcases hJ.2.2.1 i j ⟨hi.1, hj.1⟩ with hij | hij | hji
    · exact ((hCoherent i j A R D S hi hj hij).2.1 x y hx hy).mp hxy
    · subst j
      have hR : R = S := SecondOrderFunctionLaws.value_unique_l hℳ hG hi.2.2 hj.2.2
      simpa only [hR] using hxy
    · exact ((hCoherent j i D S A R hj hi hji).2.1 x y hxD hyD).mpr hxy
  · exact fun h => ⟨i, A, R, hi, hx, hy, h⟩

theorem initial_l {I J F G X i A R x y : type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hF : map_l (ℳ := 𝒱) F I X)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I J F G)
    (hi : stage_l (ℳ₀ := 𝒱) I F G i A R) (hx : mem_l hℳ x A)
    (hyx : edge_l (ℳ₀ := 𝒱) I F G y x) : mem_l hℳ y A := by
  obtain ⟨j, D, S, hj, hyD, _, hyx⟩ := hyx
  rcases hJ.2.2.1 i j ⟨hi.1, hj.1⟩ with hij | hij | hji
  · exact (hCoherent i j A R D S hi hj hij).2.2 x y hx hyD hyx
  · subst j
    have hA : A = D := SecondOrderFunctionLaws.value_unique_l hℳ hF hi.2.1 hj.2.1
    change member_l 𝒱 y A
    rw [hA]
    exact hyD
  · exact (hCoherent j i D S A R hj hi hji).1 y hyD

theorem stage_of_member_l {C I F G Y x : type_l hℳ}
    (hG : map_l (ℳ := 𝒱) G I Y) (hCover : cover_l (ℳ₀ := 𝒱) C I F)
    (hx : mem_l hℳ x C) :
    ∃ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R ∧ mem_l hℳ x A := by
  obtain ⟨i, A, hi, hiA, hxA⟩ := (hCover x).mp hx
  obtain ⟨R, hR, _⟩ := hG.2 i hi
  exact ⟨i, A, R, ⟨hi, hiA, hR.2⟩, hxA⟩

theorem of_graph_l {C I J F G X Y L : type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hF : map_l (ℳ := 𝒱) F I X) (hG : map_l (ℳ := 𝒱) G I Y)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I J F G)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R → wellOrder_l (ℳ := 𝒱) A R)
    (hCover : cover_l (ℳ₀ := 𝒱) C I F)
    (hRead : ∀ x y, value_l (ℳ := 𝒱) L x y ↔ edge_l (ℳ₀ := 𝒱) I F G x y) :
    wellOrder_l (ℳ := 𝒱) C L := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxx
    obtain ⟨i, A, R, hi, hxA⟩ := stage_of_member_l hG hCover hx
    exact (hStages i A R hi).1 x hxA
      ((restrict_l hJ hG hCoherent hi hxA hxA).mp ((hRead x x).mp hxx))
  · intro x y z hxyz hxy hyz
    obtain ⟨i, A, R, hi, hzA⟩ := stage_of_member_l hG hCover hxyz.2.2
    have hyA := initial_l hJ hF hCoherent hi hzA ((hRead y z).mp hyz)
    have hxA := initial_l hJ hF hCoherent hi hyA ((hRead x y).mp hxy)
    apply (hRead x z).mpr
    apply (restrict_l hJ hG hCoherent hi hxA hzA).mpr
    exact (hStages i A R hi).2.1 x y z ⟨hxA, hyA, hzA⟩
      ((restrict_l hJ hG hCoherent hi hxA hyA).mp ((hRead x y).mp hxy))
      ((restrict_l hJ hG hCoherent hi hyA hzA).mp ((hRead y z).mp hyz))
  · intro x y hxy
    obtain ⟨i, A, R, hi, hxA⟩ := stage_of_member_l hG hCover hxy.1
    obtain ⟨j, D, S, hj, hyD⟩ := stage_of_member_l hG hCover hxy.2
    have compare {k E T} (hk : stage_l (ℳ₀ := 𝒱) I F G k E T)
        (hxE : mem_l hℳ x E) (hyE : mem_l hℳ y E) :
        value_l (ℳ := 𝒱) L x y ∨ x = y ∨ value_l (ℳ := 𝒱) L y x := by
      rcases (hStages k E T hk).2.2.1 x y ⟨hxE, hyE⟩ with h | h | h
      · exact Or.inl ((hRead x y).mpr ⟨k, E, T, hk, hxE, hyE, h⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hRead y x).mpr ⟨k, E, T, hk, hyE, hxE, h⟩))
    rcases hJ.2.2.1 i j ⟨hi.1, hj.1⟩ with hij | hij | hji
    · exact compare hj ((hCoherent i j A R D S hi hj hij).1 x hxA) hyD
    · subst j
      have hA : A = D := SecondOrderFunctionLaws.value_unique_l hℳ hF hi.2.1 hj.2.1
      exact compare hi hxA (hA.symm ▸ hyD)
    · exact compare hi hxA ((hCoherent j i D S A R hj hi hji).1 y hyD)
  · intro U hU
    obtain ⟨x₀, hx₀U⟩ := hU.2
    obtain ⟨i, A, R, hi, hx₀A⟩ := stage_of_member_l hG hCover (hU.1 x₀ hx₀U)
    let φ : Formula ℒ [] [.set, .set] := member_m (.fvar .here) (.fvar (.there .here))
    let η : Env 𝒱 [] [.set] := Env.empty.pushFree A
    obtain ⟨V, hV⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
      (SecondOrderSeparationAxiom.models_l hℳ φ η) U
    have hVRead x : mem_l hℳ x V ↔ mem_l hℳ x U ∧ mem_l hℳ x A := hV x
    obtain ⟨x, hxV, hMin⟩ := (hStages i A R hi).2.2.2 V
      ⟨fun y hy => ((hVRead y).mp hy).2, x₀, (hVRead x₀).mpr ⟨hx₀U, hx₀A⟩⟩
    obtain ⟨hxU, hxA⟩ := (hVRead x).mp hxV
    refine ⟨x, hxU, ?_⟩
    intro y hyU hyx
    have hEdge := (hRead y x).mp hyx
    have hyA := initial_l hJ hF hCoherent hi hxA hEdge
    exact hMin y ((hVRead y).mpr ⟨hyU, hyA⟩)
      ((restrict_l hJ hG hCoherent hi hyA hxA).mp hEdge)

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def stage_m {Γ Δ : SortContext ℒ} (I F G i A R : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m i I) (.conj (value_m F i A) (value_m G i R))

def edge_m {Γ Δ : SortContext ℒ} (I F G x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .conj (stage_m (up (up (up I))) (up (up (up F))) (up (up (up G)))
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (up (up (up x))) (.bvar (.there .here))) <|
        .conj (member_m (up (up (up y))) (.bvar (.there .here)))
          (value_m (.bvar .here) (up (up (up x))) (up (up (up y))))

theorem stage_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I F G i A R : Term ℒ Γ Δ .set) :
    (stage_m I F G i A R).satisfies η ↔
      stage_l (I.eval η) (F.eval η) (G.eval η) (i.eval η) (A.eval η) (R.eval η) := by
  simp only [stage_m, stage_l, Formula.satisfies, value_formula_l, member_m, Arguments.eval]
  rfl

theorem edge_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (I F G x y : Term ℒ Γ Δ .set) :
    (edge_m I F G x y).satisfies η ↔
      edge_l (I.eval η) (F.eval η) (G.eval η) (x.eval η) (y.eval η) := by
  simp only [edge_m, edge_l, Formula.satisfies, stage_formula_l, value_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem graph_exists_l {C I J F G X Y : type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hF : map_l (ℳ := 𝒱) F I X) (hG : map_l (ℳ := 𝒱) G I Y)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I J F G)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R → wellOrder_l (ℳ := 𝒱) A R)
    (hCover : cover_l (ℳ₀ := 𝒱) C I F) :
    ∃ L : type_l hℳ, graph_l (ℳ₀ := 𝒱) I F G L ∧ wellOrder_l (ℳ := 𝒱) C L ∧
      ∀ x y, value_l (ℳ := 𝒱) L x y ↔ edge_l (ℳ₀ := 𝒱) I F G x y := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := edge_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree G).pushFree F).pushFree I
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔ edge_l (ℳ₀ := 𝒱) I F G x y :=
    edge_formula_l _ _ _ _ _ _
  obtain ⟨L, hL⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η C C
  have hRead x y : value_l (ℳ := 𝒱) L x y ↔ edge_l (ℳ₀ := 𝒱) I F G x y := by
    constructor
    · rintro ⟨p, hp, hxy⟩
      obtain ⟨a, b, _, _, hab, hp'⟩ := (hL p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hp').mp rfl
      exact (hφ x y).mp hab
    · intro h
      have hEdge := h
      obtain ⟨i, A, R, hi, hx, hy, _⟩ := h
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hL p).mpr ⟨x, y, (hCover x).mpr ⟨i, A, hi.1, hi.2.1, hx⟩,
        (hCover y).mpr ⟨i, A, hi.1, hi.2.1, hy⟩, (hφ x y).mpr hEdge, hp⟩, hp⟩
  have hGraph : graph_l (ℳ₀ := 𝒱) I F G L := by
    intro p
    refine (hL p).trans ?_
    constructor
    · rintro ⟨x, y, _, _, h, hp⟩
      exact ⟨x, y, (hφ x y).mp h, hp⟩
    · rintro ⟨x, y, hEdge, hp⟩
      obtain ⟨i, A, R, hi, hx, hy, hxy⟩ := hEdge
      exact ⟨x, y, (hCover x).mpr ⟨i, A, hi.1, hi.2.1, hx⟩,
        (hCover y).mpr ⟨i, A, hi.1, hi.2.1, hy⟩,
        (hφ x y).mpr ⟨i, A, R, hi, hx, hy, hxy⟩, hp⟩
  exact ⟨L, hGraph, of_graph_l hJ hF hG hCoherent hStages hCover hRead, hRead⟩

theorem exists_l {C I J F G X Y : type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hF : map_l (ℳ := 𝒱) F I X) (hG : map_l (ℳ := 𝒱) G I Y)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I J F G)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R → wellOrder_l (ℳ := 𝒱) A R)
    (hCover : cover_l (ℳ₀ := 𝒱) C I F) :
    ∃ L : type_l hℳ, wellOrder_l (ℳ := 𝒱) C L ∧
      ∀ x y, value_l (ℳ := 𝒱) L x y ↔ edge_l (ℳ₀ := 𝒱) I F G x y := by
  obtain ⟨L, _, hL⟩ := graph_exists_l hJ hF hG hCoherent hStages hCover
  exact ⟨L, hL⟩

theorem history_exists_l {I J F G X Y : type_l hℳ}
    (hJ : wellOrder_l (ℳ := 𝒱) I J)
    (hF : map_l (ℳ := 𝒱) F I X) (hG : map_l (ℳ := 𝒱) G I Y)
    (hCoherent : coherent_l (ℳ₀ := 𝒱) I J F G)
    (hStages : ∀ i A R, stage_l (ℳ₀ := 𝒱) I F G i A R → wellOrder_l (ℳ := 𝒱) A R) :
    ∃ C L : type_l hℳ, cover_l (ℳ₀ := 𝒱) C I F ∧ graph_l (ℳ₀ := 𝒱) I F G L ∧
      wellOrder_l (ℳ := 𝒱) C L ∧
        ∀ x y, value_l (ℳ := 𝒱) L x y ↔ edge_l (ℳ₀ := 𝒱) I F G x y := by
  obtain ⟨C, hC⟩ := carrier_exists_l hF
  obtain ⟨L, hGraph, hL⟩ := graph_exists_l hJ hF hG hCoherent hStages hC
  exact ⟨C, L, hC, hGraph, hL⟩

#print axioms restrict_l
#print axioms initial_l
#print axioms of_graph_l
#print axioms exists_l
#print axioms graph_unique_l
#print axioms carrier_unique_l
#print axioms history_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellOrderCoherentUnion
