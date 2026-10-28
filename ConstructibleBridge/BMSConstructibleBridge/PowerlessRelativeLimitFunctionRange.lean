import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.SecondOrderUnion

/-! # 实际极限层内图的精确值域与值并

只要求实际函数图和定义域属于该层；原 raw 陪域无须属于 Class 或该层。
双重并界定全部 Kuratowski 输出坐标，再用真实 Δ₀ 分离得到精确值域。
其并给出全部 raw 输出的成员并，不使用 Collection 或选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionRange

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (A f y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists A <|
    PowerlessValueBounded.formula_m (up f) (.bvar .here) (up y)

theorem body_delta_l {Γ Δ : SortContext ℒ} (A f y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m A f y) :=
  .bounded_exists _ (PowerlessValueBounded.delta_l _ _ _)

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (A f y : Term ℒ Γ Δ .set) :
    (body_m A f y).satisfies η ↔ ∃ a, member_l 𝒩 a (A.eval η) ∧
      value_l (ℳ := 𝒩) (f.eval η) a (y.eval η) := by
  simp only [body_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C : type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {A f q : type_l hℳ} (hA : mem_l hℳ A C) (hfC : mem_l hℳ f C)
    (hf : map_l (ℳ := 𝒱) f A q) :
    ∃ R, mem_l hℳ R C ∧ ∀ y, mem_l hℳ y R ↔ ∃ a, value_l (ℳ := 𝒱) f a y := by
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ X : type_l hℳ, ∃ U, ∀ y, mem_l hℳ y U ↔
    ∃ z, mem_l hℳ z X ∧ mem_l hℳ y z at hUnion
  obtain ⟨U, hU⟩ := hUnion f
  have hUC := PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hC hfC hU
  obtain ⟨V, hV⟩ := hUnion U
  have hVC := PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hC hUC hV
  have hOutput {a y} (hy : value_l (ℳ := 𝒱) f a y) : mem_l hℳ y V := by
    obtain ⟨p, hp, s, t, _hs, ht, hPair⟩ := hy
    exact (hV y).mpr ⟨t, (hU t).mpr ⟨p, hp, (hPair t).mpr (Or.inr rfl)⟩,
      (ht y).mpr (Or.inr rfl)⟩
  let η : Env 𝒱 [] [.set, .set] := Env.empty |>.pushFree f |>.pushFree A
  let φ : Formula ℒ [] [.set, .set, .set] :=
    body_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  have hφ y : φ.satisfies (η.pushFree y) ↔ ∃ a, mem_l hℳ a A ∧ value_l (ℳ := 𝒱) f a y :=
    body_formula_l (η.pushFree y) _ _ _
  obtain ⟨R, hRC, hR⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l hBase hLimit hC
    (body_delta_l _ _ _) η hVC (by
      intro s v
      cases v with
      | here => exact hA
      | there v => cases v with
        | here => exact hfC
        | there v => nomatch v)
  refine ⟨R, hRC, fun y => ?_⟩
  constructor
  · intro hy
    obtain ⟨a, _ha, hValue⟩ := (hφ y).mp ((hR y).mp hy).2
    exact ⟨a, hValue⟩
  · rintro ⟨a, hValue⟩
    exact (hR y).mpr ⟨hOutput hValue,
      (hφ y).mpr ⟨a, (SecondOrderFunctionProperties.value_mem_l hℳ hf hValue).1, hValue⟩⟩

/-- 指定层内的实际图已经界定全部输出，不依赖原陪域的 Class 身份。 -/
theorem value_member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {A f q a y : type_l hℳ} (hA : mem_l hℳ A C) (hfC : mem_l hℳ f C)
    (hf : map_l (ℳ := 𝒱) f A q) (hy : value_l (ℳ := 𝒱) f a y) : mem_l hℳ y C := by
  obtain ⟨R, hRC, hR⟩ := exists_l hBase hLimit hC hA hfC hf
  exact PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC R hRC y
    ((hR y).mpr ⟨a, hy⟩)

theorem union_member_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    {A f q P : type_l hℳ} (hA : mem_l hℳ A C) (hfC : mem_l hℳ f C)
    (hf : map_l (ℳ := 𝒱) f A q)
    (hP : PowerlessRelativeHierarchySemantics.union_l hℳ f A P) : mem_l hℳ P C := by
  obtain ⟨R, hRC, hR⟩ := exists_l hBase hLimit hC hA hfC hf
  apply PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hC hRC
  intro p
  refine (hP p).trans ?_
  constructor
  · rintro ⟨a, y, _ha, hValue, hpy⟩
    exact ⟨y, (hR y).mpr ⟨a, hValue⟩, hpy⟩
  · rintro ⟨y, hyR, hpy⟩
    obtain ⟨a, hValue⟩ := (hR y).mp hyR
    exact ⟨a, y, (SecondOrderFunctionProperties.value_mem_l hℳ hf hValue).1, hValue, hpy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionRange
