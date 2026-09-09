import YesMetaZFC.BMS.FiniteLevyHierarchy
import YesMetaZFC.Logic.FirstOrder.LevyAbsoluteness

/-!
# 有限 Lévy 层级的初等嵌入接口

本文件只固定 Stage 3 需要的精确语义合同。具体的可构造层级实例必须
另行证明该合同，不把初等性伪装成嵌入的定义字段。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x y z

namespace Formula

namespace Values

/-- 异质值列上的逐点映射满足复合律。 -/
theorem map_comp {S : Type u} {First : S → Type x}
    {Second : S → Type y} {Third : S → Type z}
    (right : ∀ sort, Second sort → Third sort)
    (left : ∀ sort, First sort → Second sort) :
    {sorts : List S} → (values : FirstOrder.Values First sorts) →
      FirstOrder.Values.map (fun sort value => right sort (left sort value)) values =
        FirstOrder.Values.map right (FirstOrder.Values.map left values)
  | _, .nil => rfl
  | _, .cons value rest => by
      simp [FirstOrder.Values.map, map_comp right left rest]

end Values

/-- 两个 Lévy 嵌入的复合。新版核心不再提供旧兼容别名，BMS 在此保留所需的
最小数学接口。 -/
def LevyEmbedding.comp
    {σ : Signature.{u, v, w}} {bound : LevyBound σ}
    {first : Structure.{u, v, w, x} σ}
    {second : Structure.{u, v, w, y} σ}
    {third : Structure.{u, v, w, z} σ}
    (right : LevyEmbedding bound second third)
    (left : LevyEmbedding bound first second) :
    LevyEmbedding bound first third where
  map := fun sort value => right.map sort (left.map sort value)
  map_injective := fun sort =>
    right.map_injective sort |>.comp (left.map_injective sort)
  function_eq := by
    intro function arguments
    rw [left.function_eq, right.function_eq]
    congr 1
    exact (Values.map_comp _ _ arguments).symm
  relation_iff := by
    intro relation arguments
    rw [left.relation_iff, right.relation_iff]
    rw [← Values.map_comp right.map left.map arguments]
  bounded_preimage := by
    intro set element hElement
    rcases right.bounded_preimage (left.map bound.sort set) element hElement with
      ⟨middleElement, hMiddleImage⟩
    have hMiddle : bound.Holds second middleElement
        (left.map bound.sort set) := by
      apply (right.holds_iff middleElement (left.map bound.sort set)).mpr
      simpa [hMiddleImage] using hElement
    rcases left.bounded_preimage set middleElement hMiddle with
      ⟨sourceElement, hSourceImage⟩
    exact ⟨sourceElement, by simp [hSourceImage, hMiddleImage]⟩

/-- 一个 Lévy 嵌入在固定有限 `Sigma` 级别上保真且反映真值。 -/
def IsSigmaFiniteElementaryAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (embedding : LevyEmbedding bound source target) (level : Nat) : Prop :=
  ∀ {boundContext freeContext : SortContext σ}
      {formula : Formula σ boundContext freeContext},
    IsSigmaFinite bound level formula →
      ∀ env : Env source boundContext freeContext,
        satisfies env formula ↔ satisfies (embedding.mapEnv env) formula

/-- 在所有有限 `Sigma` 级别上初等。 -/
def IsSigmaFiniteElementary
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    (embedding : LevyEmbedding bound source target) : Prop :=
  ∀ level, IsSigmaFiniteElementaryAt embedding level

/-- 有限 `Sigma` 初等性的反射方向。 -/
theorem IsSigmaFiniteElementaryAt.reflect
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    {embedding : LevyEmbedding bound source target} {level : Nat}
    (hElementary : IsSigmaFiniteElementaryAt embedding level)
    {boundContext freeContext : SortContext σ}
    {formula : Formula σ boundContext freeContext}
    (hFormula : IsSigmaFinite bound level formula)
    (env : Env source boundContext freeContext)
    (hTarget : satisfies (embedding.mapEnv env) formula) :
    satisfies env formula :=
  (hElementary hFormula env).mpr hTarget

/-- 有限 `Sigma` 初等性的保真方向。 -/
theorem IsSigmaFiniteElementaryAt.preserve
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {source : Structure.{u, v, w, x} σ}
    {target : Structure.{u, v, w, y} σ}
    {embedding : LevyEmbedding bound source target} {level : Nat}
    (hElementary : IsSigmaFiniteElementaryAt embedding level)
    {boundContext freeContext : SortContext σ}
    {formula : Formula σ boundContext freeContext}
    (hFormula : IsSigmaFinite bound level formula)
    (env : Env source boundContext freeContext)
    (hSource : satisfies env formula) :
    satisfies (embedding.mapEnv env) formula :=
  (hElementary hFormula env).mp hSource

/-- 固定有限 `Sigma` 层的初等嵌入在复合下封闭。 -/
theorem IsSigmaFiniteElementaryAt.comp
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {bound : LevyBound σ}
    {first : Structure.{u, v, w, x} σ}
    {second : Structure.{u, v, w, y} σ}
    {third : Structure.{u, v, w, z} σ}
    {left : LevyEmbedding bound first second}
    {right : LevyEmbedding bound second third}
    {level : Nat}
    (hRight : IsSigmaFiniteElementaryAt right level)
    (hLeft : IsSigmaFiniteElementaryAt left level) :
    IsSigmaFiniteElementaryAt (right.comp left) level := by
  intro boundContext freeContext formula hFormula env
  rw [hLeft hFormula env]
  have hMapped := hRight hFormula (left.mapEnv env)
  simpa only [LevyEmbedding.comp, LevyEmbedding.mapEnv,
    Function.comp_apply] using hMapped

end Formula
end FirstOrder
end Logic
end YesMetaZFC
