import BMSConstructibleBridge.SecondOrderCanonicalLevel

/-! # 规范层序的可定义类并与候选最小化

全局比较只断言存在某一共同层，不收集全体层或任意集合族的阶段界。
初段性将一个候选的所有前驱压回同一集合层；对实际纯公式分离后，
层良序给出整个可定义候选类的最小元。没有 Collection 或外部下降链选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalClassOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m value_m)
open SecondOrderQuotient (type_l mem_l)
open SecondOrderCanonicalLevelSyntax (level_m level_l level_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def edge_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let a : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let X := .bvar (.there .here)
    let P := .bvar .here
    .conj (level_m (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃) (up₃ Pair)
      (up₃ Valid) (up₃ B) (up₃ P₀) a X P) <|
      .conj (member_m (up₃ x) X) <| .conj (member_m (up₃ y) X) (value_m P (up₃ x) (up₃ y))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

def edge_l (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : type_l hℳ) : Prop :=
  ∃ a X P, level_l ω e t₁ t₂ t₃ Pair Valid B P₀ a X P ∧
    mem_l hℳ x X ∧ mem_l hℳ y X ∧ value_l (ℳ := 𝒱) P x y

theorem edge_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) :
    (edge_m ω e t₁ t₂ t₃ Pair Valid B P₀ x y).satisfies η ↔
      edge_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (B.eval η) (P₀.eval η) (x.eval η) (y.eval η) := by
  simp only [edge_m, edge_l, Formula.satisfies, level_formula_l K, member_m, value_formula_l,
    up₃, up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

variable (K : source_coding_l hℳ) {t₁ t₂ t₃ Pair Valid B P₀ : type_l hℳ}
  (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)

include hCoding in
theorem restrict_l {a X P x y : type_l hℳ}
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hx : mem_l hℳ x X) (hy : mem_l hℳ y X) :
    edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x y ↔ value_l (ℳ := 𝒱) P x y := by
  constructor
  · rintro ⟨b, Y, Q, hQ, hxY, hyY, hxy⟩
    rcases SecondOrderOrdinalComparison.compare_l hℳ
      (PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hP))
      (PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hQ)) with h | h | h
    · subst b
      obtain ⟨_, hPQ⟩ := SecondOrderCanonicalLevel.unique_l K hCoding hP hQ
      exact hPQ.symm ▸ hxy
    · exact ((SecondOrderCanonicalLevel.extension_l K hCoding h hP hQ).2.1 x y hx hy).mp hxy
    · exact ((SecondOrderCanonicalLevel.extension_l K hCoding h hQ hP).2.1 x y hxY hyY).mpr hxy
  · exact fun hxy => ⟨a, X, P, hP, hx, hy, hxy⟩

include hCoding in
theorem initial_l {a X P x y : type_l hℳ}
    (hP : level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P)
    (hx : mem_l hℳ x X)
    (hyx : edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y x) : mem_l hℳ y X := by
  obtain ⟨b, Y, Q, hQ, hyY, _, hyx⟩ := hyx
  rcases SecondOrderOrdinalComparison.compare_l hℳ
    (PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hP))
    (PowerlessRelativeLevelClosure.ordinal_l hℳ (SecondOrderCanonicalLevel.hierarchy_l hQ)) with h | h | h
  · subst b
    exact (SecondOrderCanonicalLevel.unique_l K hCoding hQ hP).1 ▸ hyY
  · exact (SecondOrderCanonicalLevel.extension_l K hCoding h hP hQ).2.2 x y hx hyY hyx
  · exact (SecondOrderCanonicalLevel.extension_l K hCoding h hQ hP).1 y hyY

theorem irrefl_l (x : type_l hℳ) : ¬edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x x := by
  rintro ⟨_, _, _, hP, hx, _, hxx⟩
  exact (SecondOrderCanonicalLevel.order_l hP).1 x hx hxx

include hCoding in
theorem trans_l {x y z : type_l hℳ}
    (hxy : edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x y)
    (hyz : edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y z) :
    edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x z := by
  obtain ⟨a, X, P, hP, hy, hz, hyz⟩ := hyz
  have hx := initial_l K hCoding hP hy hxy
  exact ⟨a, X, P, hP, hx, hz, (SecondOrderCanonicalLevel.order_l hP).2.1 x y z ⟨hx, hy, hz⟩
    ((restrict_l K hCoding hP hx hy).mp hxy) hyz⟩

variable (hB : ∃ b, mem_l hℳ b B)
  (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
  (hOrder : wellOrder_l (ℳ := SecondOrderQuotient.structure_l hℳ) B P₀)
  (hBound : ∀ p, mem_l hℳ p P₀ → ∃ x y,
    mem_l hℳ x B ∧ mem_l hℳ y B ∧ SecondOrderPairObjects.ordered_l hℳ x y p)

include hCoding hB hBase hOrder hBound in
theorem compare_l {x y : type_l hℳ}
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x)
    (hy : PowerlessRelativeClassCorrespondence.member_l hℳ B y) :
    edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ x y ∨ x = y ∨
      edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y x := by
  obtain ⟨a, X, hX, hxX, hyX⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase hx hy
  obtain ⟨P, hP, _⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding hB hBase hOrder hBound hX
  rcases (SecondOrderCanonicalLevel.order_l hP).2.2.1 x y ⟨hxX, hyX⟩ with hxy | hEq | hyx
  · exact Or.inl ⟨a, X, P, hP, hxX, hyX, hxy⟩
  · exact Or.inr (Or.inl hEq)
  · exact Or.inr (Or.inr ⟨a, X, P, hP, hyX, hxX, hyx⟩)

include hCoding hB hBase hOrder hBound in
/-- 对实际公式分离，只需一个已有候选所在的层，不收集候选类。 -/
theorem minimum_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Δ)
    (hSome : ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧ φ.satisfies (η.pushFree x)) :
    ∃ x, PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧ φ.satisfies (η.pushFree x) ∧
      ∀ y, φ.satisfies (η.pushFree y) → ¬edge_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ y x := by
  obtain ⟨x₀, ⟨a, X, hX, hx₀⟩, hφ₀⟩ := hSome
  obtain ⟨P, hP, _⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding hB hBase hOrder hBound hX
  obtain ⟨U, hU⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) X
  obtain ⟨x, hx, hMin⟩ := (SecondOrderCanonicalLevel.order_l hP).2.2.2 U
    ⟨fun y hy => ((hU y).mp hy).1, x₀, (hU x₀).mpr ⟨hx₀, hφ₀⟩⟩
  obtain ⟨hxX, hφx⟩ := (hU x).mp hx
  refine ⟨x, ⟨a, X, hX, hxX⟩, hφx, ?_⟩
  intro y hφy hyx
  have hyX := initial_l K hCoding hP hxX hyx
  exact hMin y ((hU y).mpr ⟨hyX, hφy⟩) ((restrict_l K hCoding hP hyX hxX).mp hyx)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalClassOrder
