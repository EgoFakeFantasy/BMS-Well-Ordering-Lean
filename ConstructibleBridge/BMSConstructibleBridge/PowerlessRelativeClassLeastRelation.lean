import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassAmbientWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 已有有界关系的实际 Class 最小见证函数

使用指定环境良序，不选择宿主 Type 数据。逐输入的关系切片由 Δ₀ 分离
构造，最小见证唯一性使整张图一次存在。输出是实际 Class 图；不宣称
其属于某个 cutoff，也不把逐点 Class 见证误当作已有共同母界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLeastRelation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame SecondOrderObjectSyntax
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def least_m {Γ Δ : SortContext ℒ} (E R Y x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessValueBounded.formula_m E x y) <|
    membershipLevyBound.boundedForall Y <|
      .imp (PowerlessValueBounded.formula_m (up E) (up x) (.bvar .here))
        (.neg (PowerlessValueBounded.formula_m (up R) (.bvar .here) (up y)))

theorem least_delta_l {Γ Δ : SortContext ℒ} (E R Y x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (least_m E R Y x y) :=
  .conj (PowerlessValueBounded.delta_l _ _ _) <| .bounded_forall _ <|
    .imp (PowerlessValueBounded.delta_l _ _ _) (.neg (PowerlessValueBounded.delta_l _ _ _))

def least_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (E R Y x y : carrier_l 𝒩) : Prop :=
  value_l (ℳ := 𝒩) E x y ∧ ∀ z, member_l 𝒩 z Y → value_l (ℳ := 𝒩) E x z →
    ¬value_l (ℳ := 𝒩) R z y

theorem least_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (E R Y x y : Term ℒ Γ Δ .set) :
    (least_m E R Y x y).satisfies η ↔ least_l (E.eval η) (R.eval η) (Y.eval η)
      (x.eval η) (y.eval η) := by
  simp only [least_m, least_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

theorem least_absolute_l (E R Y x y : type_l hℳ B) :
    least_l («𝒩» := 𝒩) E R Y x y ↔ least_l («𝒩» := 𝒱) E.val R.val Y.val x.val y.val := by
  have hE := PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) E
  have hR := PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R
  constructor
  · rintro ⟨hxy, hMin⟩
    refine ⟨(hE x y).mp hxy, fun z hz hxz hzy => ?_⟩
    let z' : type_l hℳ B :=
      ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hz⟩
    exact hMin z' hz ((hE x z').mpr hxz) ((hR z' y).mpr hzy)
  · rintro ⟨hxy, hMin⟩
    exact ⟨(hE x y).mpr hxy, fun z hz hxz hzy =>
      hMin z.val hz ((hE x z).mp hxz) ((hR z y).mp hzy)⟩

include hBase in
theorem exists_l (A Y E R : type_l hℳ B)
    (hR : wellOrder_l (ℳ := 𝒱) Y.val R.val)
    (hSome : ∀ x, mem_l hℳ x A.val → ∃ y, mem_l hℳ y Y.val ∧
      value_l (ℳ := 𝒱) E.val x y) :
    ∃ J : type_l hℳ B, map_l (ℳ := 𝒱) J.val A.val Y.val ∧ ∀ x y,
      value_l (ℳ := 𝒱) J.val x y ↔ mem_l hℳ x A.val ∧ mem_l hℳ y Y.val ∧
        least_l («𝒩» := 𝒱) E.val R.val Y.val x y := by
  have hOrder := PowerlessRelativeClassAmbientWellOrder.restrict_l (hBase := hBase) hR
  let η : Env 𝒩 [] [.set, .set, .set] := Env.empty |>.pushFree Y |>.pushFree R |>.pushFree E
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := least_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  have hφ (x y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree x) ↔
      least_l («𝒩» := 𝒩) E R Y x y := least_formula_l _ _ _ _ _ _
  obtain ⟨J, hJ, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (hBase := hBase) (least_delta_l _ _ _ _ _) η A Y (by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hSome x.val hx
      let y' : type_l hℳ B :=
        ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩
      let ξ : Env 𝒩 [] [.set, .set] := Env.empty |>.pushFree E |>.pushFree x
      let ψ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
        (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
      have hψ z : ψ.satisfies (ξ.pushFree z) ↔ value_l (ℳ := 𝒩) E x z :=
        PowerlessValueBounded.formula_l _ _ _ _
      obtain ⟨U, hU⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
        (hBase := hBase) (PowerlessValueBounded.delta_l _ _ _) ξ Y
      have hURead z : mem_l hℳ z.val U.val ↔ mem_l hℳ z.val Y.val ∧
          value_l (ℳ := 𝒩) E x z := (hU z).trans (and_congr Iff.rfl (hψ z))
      obtain ⟨m, hm, hMin⟩ := hOrder.2.2.2 U ⟨fun z hz => ((hURead z).mp hz).1,
        y', (hURead y').mpr ⟨hy,
          (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) E x y').mpr hxy⟩⟩
      obtain ⟨hmY, hxm⟩ := (hURead m).mp hm
      have hLeast : least_l («𝒩» := 𝒩) E R Y x m :=
        ⟨hxm, fun z hz hxz => hMin z ((hURead z).mpr ⟨hz, hxz⟩)⟩
      refine ⟨m, ⟨hmY, (hφ x m).mpr hLeast⟩, ?_⟩
      rintro z ⟨hzY, hz⟩
      have hzLeast := (hφ x z).mp hz
      rcases hOrder.2.2.1 z m ⟨hzY, hmY⟩ with hlt | hEq | hgt
      · exact False.elim (hLeast.2 z hzY hzLeast.1 hlt)
      · exact hEq
      · exact False.elim (hzLeast.2 m hmY hLeast.1 hgt))
  have hRaw : map_l (ℳ := 𝒱) J.val A.val Y.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) J A Y).mp hJ
  have hClassRead (x y : type_l hℳ B) : value_l (ℳ := 𝒱) J.val x.val y.val ↔
      mem_l hℳ x.val A.val ∧ mem_l hℳ y.val Y.val ∧
        least_l («𝒩» := 𝒱) E.val R.val Y.val x.val y.val :=
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) J x y).symm.trans
      ((hRead x y).trans (and_congr Iff.rfl (and_congr Iff.rfl
        ((hφ x y).trans (least_absolute_l (hBase := hBase) E R Y x y)))))
  refine ⟨J, hRaw, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨hx, hy⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hRaw hxy
    exact (hClassRead
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx⟩
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩).mp hxy
  · rintro ⟨hx, hy, hLeast⟩
    exact (hClassRead
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hx⟩
      ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hy⟩).mpr ⟨hx, hy, hLeast⟩

#print axioms least_formula_l
#print axioms least_absolute_l
#print axioms exists_l

include hBase in
/-- 实际有界公式直接产生最小见证图；关系图在证明内构造，不是额外输入。 -/
theorem of_formula_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env 𝒩 [] Δ)
    (A Y R : type_l hℳ B) (hR : wellOrder_l (ℳ := 𝒱) Y.val R.val)
    (hSome : ∀ x, mem_l hℳ x A.val → ∃ y, mem_l hℳ y Y.val ∧
      φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x)) :
    ∃ J : type_l hℳ B, map_l (ℳ := 𝒱) J.val A.val Y.val ∧ ∀ x y,
      value_l (ℳ := 𝒱) J.val x y ↔ mem_l hℳ x A.val ∧ mem_l hℳ y Y.val ∧
        φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree y).pushFree x) ∧
        ∀ z, mem_l hℳ z Y.val →
          φ.satisfies (((PowerlessRelativeClassRelativization.env_l η).pushFree z).pushFree x) →
            ¬value_l (ℳ := 𝒱) R.val z y := by
  obtain ⟨E, hE⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l hφ η A Y
  obtain ⟨J, hJ, hRead⟩ := exists_l (hBase := hBase) A Y E R hR (by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hSome x hx
    exact ⟨y, hy, (hE x y).mpr ⟨hx, hy, hxy⟩⟩)
  refine ⟨J, hJ, fun x y => (hRead x y).trans ?_⟩
  constructor
  · rintro ⟨hx, hy, hxy, hMin⟩
    exact ⟨hx, hy, ((hE x y).mp hxy).2.2,
      fun z hz hxz => hMin z hz ((hE x z).mpr ⟨hx, hz, hxz⟩)⟩
  · rintro ⟨hx, hy, hxy, hMin⟩
    exact ⟨hx, hy, (hE x y).mpr ⟨hx, hy, hxy⟩,
      fun z hz hxz => hMin z hz ((hE x z).mp hxz).2.2⟩

#print axioms of_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLeastRelation
