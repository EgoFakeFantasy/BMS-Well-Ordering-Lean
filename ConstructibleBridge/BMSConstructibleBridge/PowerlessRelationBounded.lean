import BMSConstructibleBridge.PowerlessRelativeClassRelation
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 精确关系图的纯有界检查

逐值规格不排除非有序对垃圾。本模块同时检查每个图成员的合法坐标，
以及两个指定母集上的完整逐值读数；两部分都是纯隶属 Δ₀ 条件。
在原 Z₂ 商中，有序对存在性与唯一性恢复全部 raw 成员规格。
这里只给通用检查器与语义桥，原对象推导由实际规范历史的调用端装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 所有图成员都必须是指定两个母集上的实际有序对。 -/
def clean_m {Γ Δ : SortContext ℒ} (R X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall R <|
    membershipLevyBound.boundedExists (up X) <|
      membershipLevyBound.boundedExists (up (up Y)) <|
        PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here)
          (.bvar (.there (.there .here)))

theorem clean_delta_l {Γ Δ : SortContext ℒ} (R X Y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (clean_m R X Y) :=
  .bounded_forall R (.bounded_exists (up X) (.bounded_exists (up (up Y))
    (PowerlessPairBounded.ordered_delta_l _ _ _)))

def clean_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (R X Y : carrier_l 𝒩) : Prop :=
  ∀ p, member_l 𝒩 p R → ∃ x y,
    member_l 𝒩 x X ∧ member_l 𝒩 y Y ∧ ordered_l (ℳ := 𝒩) x y p

theorem clean_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (R X Y : Term ℒ Γ Δ .set) :
    (clean_m R X Y).satisfies η ↔ clean_l (R.eval η) (X.eval η) (Y.eval η) := by
  simp only [clean_m, clean_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun h p hp => by
    obtain ⟨x, hx, y, hy, hxy⟩ := h p hp
    exact ⟨x, y, hx, hy, hxy⟩,
    fun h p hp => by
      obtain ⟨x, y, hx, hy, hxy⟩ := h p hp
      exact ⟨x, hx, y, hy, hxy⟩⟩

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: .set :: Δ) [.set, .set] (.set :: .set :: .set :: Δ)
  | _, .here => .bvar (.there .here)
  | _, .there .here => .bvar .here
  | _, .there (.there v) => .fvar (.there (.there (.there v)))

private def inner_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [.set, .set] (.set :: .set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ)
    [.set, .set] (.set :: .set :: .set :: Δ) from .map (fun v => nomatch v) insert_m)

/-- 自由变量依次是 R、X、Y，再接原矩阵参数；不把坐标全域量词混入检查器。 -/
def formula_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  .conj (clean_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))) <|
    membershipLevyBound.boundedForall (.fvar (.there .here)) <|
      membershipLevyBound.boundedForall (.fvar (.there (.there .here))) <|
        .iff (PowerlessValueBounded.formula_m (.fvar .here)
          (.bvar (.there .here)) (.bvar .here)) (inner_m φ)

theorem delta_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Formula.IsDelta0 membershipLevyBound (formula_m φ) :=
  .conj (clean_delta_l _ _ _) (.bounded_forall _ (.bounded_forall _
    (.iff (PowerlessValueBounded.delta_l _ _ _) (hφ.substituteMapped
      (show VariableSubstitution ℒ [] [.set, .set] (.set :: .set :: .set :: Δ)
        from fun v => nomatch v) insert_m))))

private theorem inner_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (X Y R x y : carrier_l 𝒩) :
    (inner_m φ).satisfies (((((η.pushFree Y).pushFree X).pushFree R).pushBound x).pushBound y) ↔
      φ.satisfies ((η.pushFree y).pushFree x) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (X Y R : carrier_l 𝒩) : Prop :=
  clean_l (𝒩 := 𝒩) R X Y ∧ ∀ x, member_l 𝒩 x X → ∀ y, member_l 𝒩 y Y →
    (value_l (ℳ := 𝒩) R x y ↔ φ.satisfies ((η.pushFree y).pushFree x))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (X Y R : carrier_l 𝒩) :
    (formula_m φ).satisfies (((η.pushFree Y).pushFree X).pushFree R) ↔
      holds_l φ η X Y R := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    clean_formula_l, PowerlessValueBounded.formula_l, inner_formula_l,
    Arguments.eval, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 两个有界条件恢复全 raw 成员规格，反向不遗漏合法有序对的任何编码。 -/
theorem spec_iff_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (X Y R : SecondOrderQuotient.type_l hℳ) :
    holds_l φ η X Y R ↔ ∀ p, SecondOrderQuotient.mem_l hℳ p R ↔
      ∃ x y, SecondOrderQuotient.mem_l hℳ x X ∧ SecondOrderQuotient.mem_l hℳ y Y ∧
        ordered_l (ℳ := 𝒱) x y p ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  constructor
  · rintro ⟨hClean, hRead⟩ p
    constructor
    · intro hp
      obtain ⟨x, y, hx, hy, hxy⟩ := hClean p hp
      exact ⟨x, y, hx, hy, hxy, (hRead x hx y hy).mp ⟨p, hp, hxy⟩⟩
    · rintro ⟨x, y, hx, hy, hxy, hφxy⟩
      obtain ⟨q, hq, hxq⟩ := (hRead x hx y hy).mpr hφxy
      have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hxq hxy
      exact hEq ▸ hq
  · intro hSpec
    constructor
    · intro p hp
      obtain ⟨x, y, hx, hy, hxy, _⟩ := (hSpec p).mp hp
      exact ⟨x, y, hx, hy, hxy⟩
    · intro x hx y hy
      constructor
      · rintro ⟨p, hp, hxy⟩
        obtain ⟨a, b, _, _, hab, hφab⟩ := (hSpec p).mp hp
        obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hab hxy).mp rfl
        exact hφab
      · intro hφxy
        obtain ⟨p, hxy⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
        exact ⟨p, (hSpec p).mpr ⟨x, y, hx, hy, hxy, hφxy⟩, hxy⟩

/-- 干净成员条件也恢复域外坐标为空的完整 raw 逐值读数。 -/
theorem value_read_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    {η : Env 𝒱 [] Δ} {X Y R : SecondOrderQuotient.type_l hℳ}
    (hR : holds_l φ η X Y R) (x y : SecondOrderQuotient.type_l hℳ) :
    value_l (ℳ := 𝒱) R x y ↔ SecondOrderQuotient.mem_l hℳ x X ∧
      SecondOrderQuotient.mem_l hℳ y Y ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  have hSpec := (spec_iff_l φ η X Y R).mp hR
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨a, b, ha, hb, hab, hφab⟩ := (hSpec p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hab hxy).mp rfl
    exact ⟨ha, hb, hφab⟩
  · rintro ⟨hx, hy, hφxy⟩
    obtain ⟨p, hxy⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (hSpec p).mpr ⟨x, y, hx, hy, hxy, hφxy⟩, hxy⟩

/-- 精确成员图唯一；不由仅有逐值规格断言图对象唯一。 -/
theorem unique_l {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    {η : Env 𝒱 [] Δ} {X Y R S : SecondOrderQuotient.type_l hℳ}
    (hR : holds_l φ η X Y R) (hS : holds_l φ η X Y S) : R = S :=
  SecondOrderQuotient.ext_l hℳ R S (fun p =>
    (spec_iff_l φ η X Y R).mp hR p |>.trans ((spec_iff_l φ η X Y S).mp hS p).symm)

#print axioms delta_l
#print axioms spec_iff_l
#print axioms value_read_l
#print axioms unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationBounded
