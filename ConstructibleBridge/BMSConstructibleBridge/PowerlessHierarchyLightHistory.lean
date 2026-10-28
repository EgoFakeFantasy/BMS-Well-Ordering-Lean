import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 固定后继图的纯 Δ₀ 轻量层次历史

对象语言为纯隶属 ℒ，背景为原 SecondOrderArithmetic.theory_m。完整函数图
f:α→C 含干净成员、总性和唯一性；零值为 B，后继通过给定图 D 的实际
Value 读取，非零极限值是全部较早输出的精确并。不改变原 raw history。

全部显式量词界于 α、C、f、D 及实际阶段和输出的成员。有界精确并保留
两向成员覆盖，不能仅用输出包含于某个母集替代全 raw 成员 iff。完整 Map
把任何 raw 图值收回陪域，所以读数本身不额外要求 α 是序数；后续内部
序数归纳仍须由调用端提供真实内部序数证书。

本文件只给检查器 AST、Δ₀ 分类与 raw 语义读取，不构造历史，不预设
f 属于 Class，不假定 Collection 或实际轨迹包络。D 的原 Def 读数、
历史唯一性、Class 成员界和最终原 Derives 均由后续模块接续。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistory

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def empty_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (a : carrier_l 𝒩) : Prop :=
  ∀ x, ¬member_l 𝒩 x a

def empty_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall a (.neg (.equal (.bvar .here) (.bvar .here)))

theorem empty_delta_l {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (empty_m a) :=
  .bounded_forall a (.neg (.equal _ _))

theorem empty_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (a : Term ℒ Γ Δ .set) :
    (empty_m a).satisfies η ↔ empty_holds_l (a.eval η) := by
  simp only [empty_m, empty_holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  simp only [ThirdOrderSemantics.member_l, Env.pushBound, Assignment.push,
    not_true_eq_false]

def successor_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (a b : carrier_l 𝒩) : Prop :=
  ∀ x, member_l 𝒩 x b ↔ member_l 𝒩 x a ∨ x = a

def successor_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m a b) <| .conj
    (membershipLevyBound.boundedForall a (member_m (.bvar .here) (up b)))
    (membershipLevyBound.boundedForall b
      (.disj (member_m (.bvar .here) (up a)) (.equal (.bvar .here) (up a))))

theorem successor_delta_l {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (successor_m a b) :=
  .conj (.rel _ _) (.conj (.bounded_forall a (.rel _ _))
    (.bounded_forall b (.disj (.rel _ _) (.equal _ _))))

theorem successor_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (a b : Term ℒ Γ Δ .set) :
    (successor_m a b).satisfies η ↔ successor_holds_l (a.eval η) (b.eval η) := by
  have h : (successor_m a b).satisfies η ↔ member_l 𝒩 (a.eval η) (b.eval η) ∧
      (∀ x, member_l 𝒩 x (a.eval η) → member_l 𝒩 x (b.eval η)) ∧
      (∀ x, member_l 𝒩 x (b.eval η) → member_l 𝒩 x (a.eval η) ∨ x = a.eval η) := by
    simp only [successor_m, Formula.LevyBound.boundedForall,
      Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, member_m,
      Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [h]
  constructor
  · rintro ⟨ha, hSub, hRead⟩ x
    exact ⟨hRead x, fun hx => hx.elim (hSub x) (fun he => he.symm ▸ ha)⟩
  · intro h
    exact ⟨(h _).mpr (Or.inr rfl), fun x hx => (h x).mpr (Or.inl hx), fun x hx => (h x).mp hx⟩

def limit_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (a : carrier_l 𝒩) : Prop :=
  (∃ x, member_l 𝒩 x a) ∧ ∀ x, member_l 𝒩 x a → ∃ y, member_l 𝒩 y a ∧ member_l 𝒩 x y

def limit_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedExists a (.equal (.bvar .here) (.bvar .here)))
    (membershipLevyBound.boundedForall a <|
      membershipLevyBound.boundedExists (up a) (member_m (.bvar (.there .here)) (.bvar .here)))

theorem limit_delta_l {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (limit_m a) :=
  .conj (.bounded_exists a (.equal _ _)) (.bounded_forall a (.bounded_exists (up a) (.rel _ _)))

theorem limit_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (a : Term ℒ Γ Δ .set) :
    (limit_m a).satisfies η ↔ limit_holds_l (a.eval η) := by
  simp only [limit_m, limit_holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies, member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval, and_true]
  rfl

/-- 输出侧覆盖与全部早期输出侧覆盖共同表达精确并。 -/
def union_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (C f a y : carrier_l 𝒩) : Prop :=
  (∀ x, member_l 𝒩 x y → ∃ b, member_l 𝒩 b a ∧ ∃ d, member_l 𝒩 d C ∧
    value_l (ℳ := 𝒩) f b d ∧ member_l 𝒩 x d) ∧
  (∀ b, member_l 𝒩 b a → ∀ d, member_l 𝒩 d C → value_l (ℳ := 𝒩) f b d →
    ∀ x, member_l 𝒩 x d → member_l 𝒩 x y)

def union_m {Γ Δ : SortContext ℒ} (C f a y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ := .conj
  (membershipLevyBound.boundedForall y <|
    membershipLevyBound.boundedExists (up a) <|
      membershipLevyBound.boundedExists (up (up C)) <| .conj
        (PowerlessValueBounded.formula_m (up (up (up f))) (.bvar (.there .here)) (.bvar .here))
        (member_m (.bvar (.there (.there .here))) (.bvar .here)))
  (membershipLevyBound.boundedForall a <|
    membershipLevyBound.boundedForall (up C) <| .imp
      (PowerlessValueBounded.formula_m (up (up f)) (.bvar (.there .here)) (.bvar .here))
      (membershipLevyBound.boundedForall (.bvar .here)
        (member_m (.bvar .here) (up (up (up y))))))

theorem union_delta_l {Γ Δ : SortContext ℒ} (C f a y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (union_m C f a y) :=
  .conj (.bounded_forall y (.bounded_exists (up a) (.bounded_exists (up (up C))
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.rel _ _)))))
    (.bounded_forall a (.bounded_forall (up C) (.imp (PowerlessValueBounded.delta_l _ _ _)
      (.bounded_forall (.bvar .here) (.rel _ _)))))

theorem union_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C f a y : Term ℒ Γ Δ .set) :
    (union_m C f a y).satisfies η ↔ union_holds_l (C.eval η) (f.eval η) (a.eval η) (y.eval η) := by
  simp only [union_m, union_holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def successor_step_m {Γ Δ : SortContext ℒ} (D C f a y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists a <|
    membershipLevyBound.boundedExists (up C) <| .conj
      (successor_m (.bvar (.there .here)) (up (up a))) <| .conj
        (PowerlessValueBounded.formula_m (up (up f)) (.bvar (.there .here)) (.bvar .here))
        (PowerlessValueBounded.formula_m (up (up D)) (.bvar .here) (up (up y)))

theorem successor_step_delta_l {Γ Δ : SortContext ℒ} (D C f a y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (successor_step_m D C f a y) :=
  .bounded_exists a (.bounded_exists (up C) (.conj (successor_delta_l _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _))))

def step_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (B D C f a y : carrier_l 𝒩) : Prop :=
  (empty_holds_l a ∧ y = B) ∨
    (∃ b, member_l 𝒩 b a ∧ ∃ d, member_l 𝒩 d C ∧ successor_holds_l b a ∧
      value_l (ℳ := 𝒩) f b d ∧ value_l (ℳ := 𝒩) D d y) ∨
    (limit_holds_l a ∧ union_holds_l C f a y)

def step_m {Γ Δ : SortContext ℒ} (B D C f a y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (empty_m a) (.equal y B)) <| .disj
    (successor_step_m D C f a y) (.conj (limit_m a) (union_m C f a y))

theorem step_delta_l {Γ Δ : SortContext ℒ} (B D C f a y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (step_m B D C f a y) :=
  .disj (.conj (empty_delta_l a) (.equal _ _)) (.disj (successor_step_delta_l _ _ _ _ _)
    (.conj (limit_delta_l a) (union_delta_l _ _ _ _)))

theorem step_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (B D C f a y : Term ℒ Γ Δ .set) :
    (step_m B D C f a y).satisfies η ↔
      step_holds_l (B.eval η) (D.eval η) (C.eval η) (f.eval η) (a.eval η) (y.eval η) := by
  simp only [step_m, step_holds_l, successor_step_m, Formula.satisfies,
    empty_formula_l, successor_formula_l, limit_formula_l, union_formula_l,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (B D α C f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessMapBounded.formula_m f α C) <|
    membershipLevyBound.boundedForall α <|
      membershipLevyBound.boundedForall (up C) <| .imp
        (PowerlessValueBounded.formula_m (up (up f)) (.bvar (.there .here)) (.bvar .here))
        (step_m (up (up B)) (up (up D)) (up (up C)) (up (up f))
          (.bvar (.there .here)) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ} (B D α C f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m B D α C f) :=
  .conj (PowerlessMapBounded.delta_l _ _ _) (.bounded_forall α (.bounded_forall (up C)
    (.imp (PowerlessValueBounded.delta_l _ _ _) (step_delta_l _ _ _ _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (B D α C f : carrier_l 𝒩) : Prop :=
  map_l (ℳ := 𝒩) f α C ∧ ∀ a, member_l 𝒩 a α → ∀ y, member_l 𝒩 y C →
    value_l (ℳ := 𝒩) f a y → step_holds_l B D C f a y

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (B D α C f : Term ℒ Γ Δ .set) :
    (formula_m B D α C f).satisfies η ↔ holds_l (B.eval η) (D.eval η) (α.eval η) (C.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessValueBounded.formula_l, step_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

def step_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B D f a y : SecondOrderQuotient.type_l hℳ) : Prop :=
  (PowerlessRelativeHierarchySemantics.empty_l hℳ a ∧ y = B) ∨
    (∃ b d, PowerlessRelativeHierarchySemantics.successor_l hℳ b a ∧
      SecondOrderFunctionObjects.value_l hℳ f b d ∧ SecondOrderFunctionObjects.value_l hℳ D d y) ∨
    (PowerlessRelativeHierarchySemantics.limit_l hℳ a ∧ PowerlessRelativeHierarchySemantics.union_l hℳ f a y)

def history_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B D α C f : SecondOrderQuotient.type_l hℳ) : Prop :=
  SecondOrderFunctionObjects.map_l hℳ f α C ∧ ∀ a y,
    SecondOrderQuotient.mem_l hℳ a α ∧ SecondOrderFunctionObjects.value_l hℳ f a y → step_l hℳ B D f a y

/-- 真正陪域界来自干净函数图；不需要 a⊆α 或任何外部序数性。 -/
theorem union_reading_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {α C f a y : SecondOrderQuotient.type_l hℳ}
    (hMap : SecondOrderFunctionObjects.map_l hℳ f α C) :
    union_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C f a y ↔
      PowerlessRelativeHierarchySemantics.union_l hℳ f a y := by
  constructor
  · rintro ⟨hLeft, hRight⟩ x
    constructor
    · intro hx
      obtain ⟨b, hb, d, _hd, hValue, hxd⟩ := hLeft x hx
      exact ⟨b, d, hb, hValue, hxd⟩
    · rintro ⟨b, d, hb, hValue, hxd⟩
      exact hRight b hb d (SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue).2 hValue x hxd
  · intro hUnion
    constructor
    · intro x hx
      obtain ⟨b, d, hb, hValue, hxd⟩ := (hUnion x).mp hx
      exact ⟨b, hb, d, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue).2, hValue, hxd⟩
    · intro b hb d _hd hValue x hxd
      exact (hUnion x).mpr ⟨b, d, hb, hValue, hxd⟩

theorem step_reading_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B D α C f a y : SecondOrderQuotient.type_l hℳ}
    (hMap : SecondOrderFunctionObjects.map_l hℳ f α C) :
    step_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) B D C f a y ↔ step_l hℳ B D f a y := by
  unfold step_holds_l step_l
  refine or_congr Iff.rfl (or_congr ?_ (and_congr Iff.rfl (union_reading_l hℳ hMap)))
  constructor
  · rintro ⟨b, _hb, d, _hd, hSucc, hValue, hD⟩
    exact ⟨b, d, hSucc, hValue, hD⟩
  · rintro ⟨b, d, hSucc, hValue, hD⟩
    exact ⟨b, (hSucc b).mpr (Or.inr rfl), d,
      (SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue).2, hSucc, hValue, hD⟩

/-- 全 raw 阶段和输出读数；不把陪域内读数误作未经证明的量词缩小。 -/
theorem reading_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B D α C f : SecondOrderQuotient.type_l hℳ} :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) B D α C f ↔ history_l hℳ B D α C f := by
  constructor
  · rintro ⟨hMap, hSteps⟩
    refine ⟨hMap, fun a y hValue => ?_⟩
    exact (step_reading_l hℳ hMap).mp
      (hSteps a hValue.1 y (SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue.2).2 hValue.2)
  · rintro ⟨hMap, hSteps⟩
    exact ⟨hMap, fun a ha y _hy hValue => (step_reading_l hℳ hMap).mpr (hSteps a y ⟨ha, hValue⟩)⟩

theorem reading_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (B D α C f : Term ℒ Γ Δ .set) :
    (formula_m B D α C f).satisfies η ↔
      history_l hℳ (B.eval η) (D.eval η) (α.eval η) (C.eval η) (f.eval η) :=
  (formula_l η B D α C f).trans (reading_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistory
