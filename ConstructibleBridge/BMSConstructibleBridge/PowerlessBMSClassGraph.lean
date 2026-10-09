import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.PowerlessBMSSetTransitiveImage

/-!
# 已得到精确值域后，可定义类映射的图也是集合

复用任意两个给定集合之间的实际关系像。分别组合子集有界、传递类像两种
替换结论；不将对象公式 AST 或仅有宿主函数当成模型内的集合图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassGraph

open Logic FirstOrder

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

def range_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d r : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ y, SecondOrderQuotient.mem_l hℳ y r ↔
    ∃ x, SecondOrderQuotient.mem_l hℳ x d ∧ φ.satisfies ((η.pushFree x).pushFree y)

def graph_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d f : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔ ∃ x y,
    SecondOrderQuotient.mem_l hℳ x d ∧ φ.satisfies ((η.pushFree x).pushFree y) ∧
      SecondOrderPairObjects.ordered_l hℳ x y p

theorem exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d r : SecondOrderQuotient.type_l hℳ)
    (hRange : range_l hℳ φ η d r) : ∃ f, graph_l hℳ φ η d f := by
  obtain ⟨f, hf⟩ := SecondOrderDefinableRelationImage.exists_l hℳ
    (PowerlessBMSClassCollapse.converse_m φ) η d r
  refine ⟨f, fun p => (hf p).trans ?_⟩
  constructor
  · rintro ⟨x, y, hx, _, hφ, hp⟩
    exact ⟨x, y, hx, (PowerlessBMSClassCollapse.converse_formula_l φ η x y).mp hφ, hp⟩
  · rintro ⟨x, y, hx, hφ, hp⟩
    exact ⟨x, y, hx, (hRange y).mpr ⟨x, hx, hφ⟩,
      (PowerlessBMSClassCollapse.converse_formula_l φ η x y).mpr hφ, hp⟩

theorem value_iff_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d f : SecondOrderQuotient.type_l hℳ)
    (hf : graph_l hℳ φ η d f) (x y : SecondOrderQuotient.type_l hℳ) :
    SecondOrderFunctionObjects.value_l hℳ f x y ↔
      SecondOrderQuotient.mem_l hℳ x d ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hφ, hab⟩ := (hf p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hab).mp rfl
    exact ⟨ha, hφ⟩
  · rintro ⟨hx, hφ⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (hf p).mpr ⟨x, y, hx, hφ, hp⟩, hp⟩

theorem map_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d r f : SecondOrderQuotient.type_l hℳ)
    (hRange : range_l hℳ φ η d r) (hf : graph_l hℳ φ η d f)
    (hTotal : ∀ x, SecondOrderQuotient.mem_l hℳ x d → ∃ y, φ.satisfies ((η.pushFree x).pushFree y))
    (hUnique : ∀ x y z, SecondOrderQuotient.mem_l hℳ x d →
      φ.satisfies ((η.pushFree x).pushFree y) → φ.satisfies ((η.pushFree x).pushFree z) → y = z) :
    SecondOrderFunctionObjects.map_l hℳ f d r := by
  constructor
  · intro p hp
    obtain ⟨x, y, hx, hφ, hp⟩ := (hf p).mp hp
    exact ⟨x, y, hx, (hRange y).mpr ⟨x, hx, hφ⟩, hp⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hTotal x hx
    refine ⟨y, ⟨(hRange y).mpr ⟨x, hx, hy⟩, (value_iff_l hℳ φ η d f hf x y).mpr ⟨hx, hy⟩⟩, ?_⟩
    intro z hz
    exact hUnique x z y hx ((value_iff_l hℳ φ η d f hf x z).mp hz.2).2 hy

theorem bounded_exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d a : SecondOrderQuotient.type_l hℳ)
    (hUnique : ∀ x y z, SecondOrderQuotient.mem_l hℳ x d →
      φ.satisfies ((η.pushFree x).pushFree y) → φ.satisfies ((η.pushFree x).pushFree z) → y = z)
    (hBound : ∀ x y, SecondOrderQuotient.mem_l hℳ x d → φ.satisfies ((η.pushFree x).pushFree y) →
      ∀ z, SecondOrderQuotient.mem_l hℳ z y → SecondOrderQuotient.mem_l hℳ z a) :
    ∃ r f, range_l hℳ φ η d r ∧ graph_l hℳ φ η d f := by
  obtain ⟨r, hr⟩ := PowerlessBMSQuotientBoundedImage.exists_l hℳ φ η d a hUnique hBound
  obtain ⟨f, hf⟩ := exists_l hℳ φ η d r hr
  exact ⟨r, f, hr, hf⟩

theorem transitive_exists_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) (d : SecondOrderQuotient.type_l hℳ)
    (hUnique : ∀ x y z, SecondOrderQuotient.mem_l hℳ x d →
      φ.satisfies ((η.pushFree x).pushFree y) → φ.satisfies ((η.pushFree x).pushFree z) → y = z)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x d → φ.satisfies ((η.pushFree x).pushFree y) →
      ∀ z, SecondOrderQuotient.mem_l hℳ z y →
        ∃ w, SecondOrderQuotient.mem_l hℳ w d ∧ φ.satisfies ((η.pushFree w).pushFree z)) :
    ∃ r f, range_l hℳ φ η d r ∧ graph_l hℳ φ η d f := by
  obtain ⟨r, hr⟩ := PowerlessBMSSetTransitiveImage.exists_l hℳ φ η d hUnique hTrans
  obtain ⟨f, hf⟩ := exists_l hℳ φ η d r hr
  exact ⟨r, f, hr, hf⟩

#print axioms bounded_exists_l
#print axioms transitive_exists_l
#print axioms map_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassGraph
