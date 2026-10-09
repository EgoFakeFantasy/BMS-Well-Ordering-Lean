import BMSConstructibleBridge.PowerlessRelativeClassFunctionAppend
import BMSConstructibleBridge.PowerlessRelativeClassDefinableFiniteTraceDerives

/-! # 内部有限程序的实际指令求值

指令依次编码为 (常量标签, 常量)、(算子标签, 旧坐标)、
(配对标签, (左旧坐标, 右旧坐标))。只读取同一干净存储图；
非法指令、缺失坐标或无 Class 算子输出时缺省为 B。
全部原 AST、参数和内部对象保持不变，不用 Type 选择函数。
本模块不预设程序长度为外部标准自然数，也尚不构造整段执行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInstruction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (ordered_m member_m value_m map_m)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₃ t)

def good_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.existsE .set <| .conj (ordered_m (up t₀) (.bvar .here) (up q)) <|
      .conj (member_m (.bvar .here) (up C)) (.equal (up y) (.bvar .here))) <|
    .disj (.existsE .set <| .existsE .set <|
      .conj (ordered_m (up₂ t₁) (.bvar (.there .here)) (up₂ q)) <|
        .conj (value_m (up₂ f) (.bvar (.there .here)) (.bvar .here)) <|
          .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (up₂ y))
            (at_m φ (.bvar .here) (up₂ y))) <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        .existsE .set <| .existsE .set <|
          let p : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there (.there .here))))
          let k := .bvar (.there (.there (.there .here)))
          let l := .bvar (.there (.there .here))
          let x := .bvar (.there .here)
          let z := .bvar .here
          .conj (ordered_m (up₅ t₂) p (up₅ q)) <|
            .conj (ordered_m k l p) <| .conj (value_m (up₅ f) k x) <|
              .conj (value_m (up₅ f) l z) (ordered_m x z (up₅ y))

def computed_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B y) <| .disj
    (good_m φ B C f t₀ t₁ t₂ q y)
    (.conj (.neg (.existsE .set (good_m φ (up B) (up C) (up f) (up t₀)
      (up t₁) (up t₂) (up q) (.bvar .here)))) (.equal y B))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def good_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C f t₀ t₁ t₂ q y : type_l hℳ) : Prop :=
  (∃ a, ordered_l (ℳ := 𝒱) t₀ a q ∧ mem_l hℳ a C ∧ y = a) ∨
    (∃ k x, ordered_l (ℳ := 𝒱) t₁ k q ∧ value_l (ℳ := 𝒱) f k x ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
        φ.satisfies ((η.pushFree x).pushFree y)) ∨
      ∃ p k l x z, ordered_l (ℳ := 𝒱) t₂ p q ∧ ordered_l (ℳ := 𝒱) k l p ∧
        value_l (ℳ := 𝒱) f k x ∧ value_l (ℳ := 𝒱) f l z ∧ ordered_l (ℳ := 𝒱) x z y

def computed_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C f t₀ t₁ t₂ q y : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
    (good_l φ η B C f t₀ t₁ t₂ q y ∨
      ((¬∃ z, good_l φ η B C f t₀ t₁ t₂ q z) ∧ y = B))

theorem good_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) :
    (good_m φ B C f t₀ t₁ t₂ q y).satisfies η ↔
      good_l φ (parameters_l η) (B.eval η) (C.eval η) (f.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (y.eval η) := by
  simp only [good_m, good_l, Formula.satisfies, ordered_formula_l, value_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, at_formula_l,
    parameters_pushBound_l, member_m, Arguments.eval, up₅, up₃, up₂, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem computed_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) :
    (computed_m φ B C f t₀ t₁ t₂ q y).satisfies η ↔
      computed_l φ (parameters_l η) (B.eval η) (C.eval η) (f.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (y.eval η) := by
  simp only [computed_m, computed_l, Formula.satisfies, good_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, parameters_pushBound_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def functional_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B : type_l hℳ) : Prop :=
  ∀ x y z, PowerlessRelativeClassCorrespondence.member_l hℳ B x →
    PowerlessRelativeClassCorrespondence.member_l hℳ B y →
      PowerlessRelativeClassCorrespondence.member_l hℳ B z →
        φ.satisfies ((η.pushFree x).pushFree y) →
          φ.satisfies ((η.pushFree x).pushFree z) → y = z

theorem good_class_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f t₀ t₁ t₂ q y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hy : good_l φ η B C f t₀ t₁ t₂ q y) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  rcases hy with ⟨a, _, ha, rfl⟩ | ⟨_, _, _, _, hy, _⟩ |
    ⟨_, k, l, x, z, _, _, hx, hz, hy⟩
  · exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hC ha
  · exact hy
  · exact PowerlessRelativeClassPair.ordered_l hℳ hBase
      (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hD
        (SecondOrderFunctionProperties.value_mem_l hℳ hf hx).2)
      (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hD
        (SecondOrderFunctionProperties.value_mem_l hℳ hf hz).2) hy

theorem good_unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f t₀ t₁ t₂ q y z : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ w, mem_l hℳ w x → mem_l hℳ w B)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : functional_l φ η B)
    (hy : good_l φ η B C f t₀ t₁ t₂ q y)
    (hz : good_l φ η B C f t₀ t₁ t₂ q z) : y = z := by
  rcases hy with ⟨a, hqa, _, hya⟩ | ⟨k, x, hqk, hx, hyC, hy⟩ |
    ⟨p, k, l, x, w, hqp, hkl, hx, hw, hy⟩
  · rcases hz with ⟨b, hqb, _, hzb⟩ | ⟨j, _, hqj, _⟩ | ⟨p, _, _, _, _, hqp, _⟩
    · exact hya.trans (((SecondOrderPairObjects.ordered_eq_l hℳ hqa hqb).mp rfl).2.trans hzb.symm)
    · exact (hTags.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqa hqj).mp rfl).1).elim
    · exact (hTags.2.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqa hqp).mp rfl).1).elim
  · rcases hz with ⟨a, hqa, _⟩ | ⟨j, w, hqj, hw, hzC, hz⟩ | ⟨p, _, _, _, _, hqp, _⟩
    · exact (hTags.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqk hqa).mp rfl).1.symm).elim
    · obtain ⟨_, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hqk hqj).mp rfl
      have hxw := SecondOrderFunctionProperties.value_unique_l hℳ hf hx hw
      subst w
      exact hFunctional x y z
        (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hD
          (SecondOrderFunctionProperties.value_mem_l hℳ hf hx).2) hyC hzC hy hz
    · exact (hTags.2.2 ((SecondOrderPairObjects.ordered_eq_l hℳ hqk hqp).mp rfl).1).elim
  · rcases hz with ⟨a, hqa, _⟩ | ⟨j, _, hqj, _⟩ |
      ⟨p', k', l', x', w', hqp', hkl', hx', hw', hz⟩
    · exact (hTags.2.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqp hqa).mp rfl).1.symm).elim
    · exact (hTags.2.2 ((SecondOrderPairObjects.ordered_eq_l hℳ hqp hqj).mp rfl).1.symm).elim
    · obtain ⟨_, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hqp hqp').mp rfl
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hkl hkl').mp rfl
      have hxx := SecondOrderFunctionProperties.value_unique_l hℳ hf hx hx'
      have hww := SecondOrderFunctionProperties.value_unique_l hℳ hf hw hw'
      subst x'; subst w'
      exact SecondOrderPairObjects.ordered_unique_l hℳ hy hz

theorem exists_unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f t₀ t₁ t₂ : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : functional_l φ η B) (q : type_l hℳ) :
    ∃! y, computed_l φ η B C f t₀ t₁ t₂ q y := by
  classical
  by_cases hSome : ∃ y, good_l φ η B C f t₀ t₁ t₂ q y
  · obtain ⟨y, hy⟩ := hSome
    refine ⟨y, ⟨good_class_l φ η hBase hC hD hf hy, Or.inl hy⟩, ?_⟩
    intro z hz
    rcases hz.2 with hz | hz
    · exact good_unique_l φ η hBase hD hf hTags hFunctional hz hy
    · exact (hz.1 ⟨y, hy⟩).elim
  · refine ⟨B, ⟨PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase,
      Or.inr ⟨hSome, rfl⟩⟩, ?_⟩
    intro z hz
    rcases hz.2 with hz | hz
    · exact (hSome ⟨z, hz⟩).elim
    · exact hz.2

theorem computed_good_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f t₀ t₁ t₂ q y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hSome : ∃ z, good_l φ η B C f t₀ t₁ t₂ q z) :
    computed_l φ η B C f t₀ t₁ t₂ q y ↔ good_l φ η B C f t₀ t₁ t₂ q y := by
  constructor
  · rintro ⟨_, hy | hy⟩
    · exact hy
    · exact (hy.1 hSome).elim
  · intro hy
    exact ⟨good_class_l φ η hBase hC hD hf hy, Or.inl hy⟩

theorem constant_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f t₀ t₁ t₂ q a y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hqa : ordered_l (ℳ := 𝒱) t₀ a q) (ha : mem_l hℳ a C) :
    computed_l φ η B C f t₀ t₁ t₂ q y ↔ y = a := by
  have hSome : ∃ z, good_l φ η B C f t₀ t₁ t₂ q z :=
    ⟨a, Or.inl ⟨a, hqa, ha, rfl⟩⟩
  rw [computed_good_l φ η hBase hC hD hf hSome]
  constructor
  · rintro (⟨b, hqb, _, hyb⟩ | ⟨k, _, hqk, _⟩ | ⟨p, _, _, _, _, hqp, _⟩)
    · exact hyb.trans ((SecondOrderPairObjects.ordered_eq_l hℳ hqb hqa).mp rfl).2
    · exact (hTags.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqa hqk).mp rfl).1).elim
    · exact (hTags.2.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqa hqp).mp rfl).1).elim
  · intro hya; exact Or.inl ⟨a, hqa, ha, hya⟩

theorem call_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f t₀ t₁ t₂ q k x y : type_l hℳ}
    (hBase : ∀ a, mem_l hℳ a B → ∀ z, mem_l hℳ z a → mem_l hℳ z B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hqk : ordered_l (ℳ := 𝒱) t₁ k q) (hx : value_l (ℳ := 𝒱) f k x)
    (hOutput : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      φ.satisfies ((η.pushFree x).pushFree z)) :
    computed_l φ η B C f t₀ t₁ t₂ q y ↔
      PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
        φ.satisfies ((η.pushFree x).pushFree y) := by
  obtain ⟨z, hzC, hz⟩ := hOutput
  have hSome : ∃ z, good_l φ η B C f t₀ t₁ t₂ q z :=
    ⟨z, Or.inr (Or.inl ⟨k, x, hqk, hx, hzC, hz⟩)⟩
  rw [computed_good_l φ η hBase hC hD hf hSome]
  constructor
  · rintro (⟨a, hqa, _⟩ | ⟨j, w, hqj, hw, hyC, hy⟩ | ⟨p, _, _, _, _, hqp, _⟩)
    · exact (hTags.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqa hqk).mp rfl).1).elim
    · obtain ⟨_, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hqk hqj).mp rfl
      have hxw := SecondOrderFunctionProperties.value_unique_l hℳ hf hx hw
      subst w
      exact ⟨hyC, hy⟩
    · exact (hTags.2.2 ((SecondOrderPairObjects.ordered_eq_l hℳ hqk hqp).mp rfl).1).elim
  · rintro ⟨hyC, hy⟩; exact Or.inr (Or.inl ⟨k, x, hqk, hx, hyC, hy⟩)

theorem pair_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {B C A D f t₀ t₁ t₂ q p k l x z y : type_l hℳ}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ B C)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hf : map_l (ℳ := 𝒱) f A D) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hqp : ordered_l (ℳ := 𝒱) t₂ p q) (hkl : ordered_l (ℳ := 𝒱) k l p)
    (hx : value_l (ℳ := 𝒱) f k x) (hz : value_l (ℳ := 𝒱) f l z) :
    computed_l φ η B C f t₀ t₁ t₂ q y ↔ ordered_l (ℳ := 𝒱) x z y := by
  obtain ⟨v, hv⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x z
  have hSome : ∃ w, good_l φ η B C f t₀ t₁ t₂ q w :=
    ⟨v, Or.inr (Or.inr ⟨p, k, l, x, z, hqp, hkl, hx, hz, hv⟩)⟩
  rw [computed_good_l φ η hBase hC hD hf hSome]
  constructor
  · rintro (⟨a, hqa, _⟩ | ⟨j, _, hqj, _⟩ | ⟨p', k', l', x', z', hqp', hkl', hx', hz', hy⟩)
    · exact (hTags.2.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hqa hqp).mp rfl).1).elim
    · exact (hTags.2.2 ((SecondOrderPairObjects.ordered_eq_l hℳ hqj hqp).mp rfl).1).elim
    · obtain ⟨_, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hqp hqp').mp rfl
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hkl hkl').mp rfl
      have hxx := SecondOrderFunctionProperties.value_unique_l hℳ hf hx hx'
      have hzz := SecondOrderFunctionProperties.value_unique_l hℳ hf hz hz'
      subst x'; subst z'
      exact hy
  · intro hy; exact Or.inr (Or.inr ⟨p, k, l, x, z, hqp, hkl, hx, hz, hy⟩)

def functional_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let x : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let y := .bvar (.there .here)
    let z := .bvar .here
    .imp (PowerlessRelativeHierarchySyntax.class_m (up₃ B) x) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (up₃ B) y) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m (up₃ B) z) <|
          .imp (at_m φ x y) <| .imp (at_m φ x z) (.equal y z)

def tags_m {Γ Δ : SortContext ℒ} (t₀ t₁ t₂ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.neg (.equal t₀ t₁)) (.conj (.neg (.equal t₀ t₂)) (.neg (.equal t₁ t₂)))

theorem functional_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (B : Term ℒ Γ Δ .set) :
    (functional_m φ B).satisfies η ↔ functional_l φ (parameters_l η) (B.eval η) := by
  simp only [functional_m, functional_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, at_formula_l,
    parameters_pushBound_l, up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def property_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C f t₀ t₁ t₂ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .existsE .set <|
    let q : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let y := .bvar .here
    .conj (computed_m φ (up₂ B) (up₂ C) (up₂ f) (up₂ t₀) (up₂ t₁) (up₂ t₂) q y) <|
      .forallE .set <|
        .imp (computed_m φ (up₃ B) (up₃ C) (up₃ f) (up₃ t₀) (up₃ t₁) (up₃ t₂)
          (up q) (.bvar .here)) (.equal (.bvar .here) (up y))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
        .imp (map_m f A D) <| .imp (tags_m t₀ t₁ t₂) <|
          .imp (functional_m φ B) (property_m φ B C f t₀ t₁ t₂)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C A D f t₀ t₁ t₂)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B C A D f t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m φ B C A D f t₀ t₁ t₂).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, tags_m, functional_m, property_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    computed_formula_l K, at_formula_l, parameters_pushBound_l, parameters_empty_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hC hD hf hTags hFunctional q
  exact exists_unique_l φ η hBase hC hD hf hTags hFunctional q

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C A D f t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C A D f t₀ t₁ t₂)

#print axioms good_formula_l
#print axioms good_unique_l
#print axioms call_l
#print axioms pair_l
#print axioms exists_unique_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramInstruction
