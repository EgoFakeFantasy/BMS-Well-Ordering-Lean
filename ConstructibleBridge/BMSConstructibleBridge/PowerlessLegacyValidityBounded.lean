import BMSConstructibleBridge.PowerlessBoundedNumericPairing
import BMSConstructibleBridge.PowerlessSuccessorBounded

/-! # 原五标签合法性的纯 Δ₀ 二维证书检查器

节点和表格单元严格使用原平方分支配数，而不是新的三角配数。
参数 N 预留给完整 Seq(ω,ω)；单元 (c,l) 的值一表示合法。
旧零码是合法的假公式，否定分支只检查子码合法，不取布尔否定。

局部表在 c≤C 且 l+c≤B 的三角预算上满足原五标签方程；存在分支
在后继长度查询严格子码。证书只把候选 f 限于 N，不额外要求图值
全为零一，亦不加入映射字段：原数码正确性将把查询图解码回原 real。

本模块只给纯 AST、Δ₀ 分类及任意纯结构的逐环境读数。完整 N 的规格、
内部预算唯一性、证书存在和与原合法性 V 的等价需另行装配；这里尚未
构造旧合法性 Class 图，也不交付统一历史或 BMS 的对象推导终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def node_m {Γ Δ : SortContext ℒ} (ω e N tag payload c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up N) (up tag) (up payload) (.bvar .here))
    (PowerlessSuccessorBounded.formula_m (.bvar .here) (up c))

theorem node_delta_l {Γ Δ : SortContext ℒ} (ω e N tag payload c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (node_m ω e N tag payload c) :=
  .bounded_exists ω (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (PowerlessSuccessorBounded.delta_l _ _))

def node_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N tag payload c : carrier_l 𝒩) : Prop :=
  ∃ r, member_l 𝒩 r ω ∧ PowerlessBoundedNumericPairing.holds_l ω e N tag payload r ∧
    PowerlessNatural.successor_l r c

theorem node_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N tag payload c : Term ℒ Γ Δ .set) :
    (node_m ω e N tag payload c).satisfies η ↔
      node_holds_l (ω.eval η) (e.eval η) (N.eval η) (tag.eval η) (payload.eval η) (c.eval η) := by
  simp only [node_m, node_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessSuccessorBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def query_m {Γ Δ : SortContext ℒ} (ω e N t₁ f c l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up N) (up c) (up l) (.bvar .here))
    (PowerlessValueBounded.formula_m (up f) (.bvar .here) (up t₁))

theorem query_delta_l {Γ Δ : SortContext ℒ} (ω e N t₁ f c l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (query_m ω e N t₁ f c l) :=
  .bounded_exists ω (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (PowerlessValueBounded.delta_l _ _ _))

def query_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N t₁ f c l : carrier_l 𝒩) : Prop :=
  ∃ k, member_l 𝒩 k ω ∧ PowerlessBoundedNumericPairing.holds_l ω e N c l k ∧ value_l f k t₁

theorem query_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N t₁ f c l : Term ℒ Γ Δ .set) :
    (query_m ω e N t₁ f c l).satisfies η ↔ query_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (t₁.eval η) (f.eval η) (c.eval η) (l.eval η) := by
  simp only [query_m, query_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

private def atomic_m {Γ Δ : SortContext ℒ} (ω e N payload l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up₂ ω) (up₂ e) (up₂ N)
      (.bvar (.there .here)) (.bvar .here) (up₂ payload))
    (.conj (member_m (.bvar (.there .here)) (up₂ l)) (member_m (.bvar .here) (up₂ l)))

private theorem atomic_delta_l {Γ Δ : SortContext ℒ} (ω e N payload l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (atomic_m ω e N payload l) :=
  .bounded_exists ω <| .bounded_exists (up ω) <| .conj
    (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _) (.conj (.rel _ _) (.rel _ _))

def atomic_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N payload l : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ ∃ j, member_l 𝒩 j ω ∧
    PowerlessBoundedNumericPairing.holds_l ω e N i j payload ∧ member_l 𝒩 i l ∧ member_l 𝒩 j l

private theorem atomic_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N payload l : Term ℒ Γ Δ .set) :
    (atomic_m ω e N payload l).satisfies η ↔
      atomic_holds_l (ω.eval η) (e.eval η) (N.eval η) (payload.eval η) (l.eval η) := by
  simp only [atomic_m, atomic_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    member_m, member_l, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

private def binary_m {Γ Δ : SortContext ℒ}
    (ω e N t₁ f payload l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up₂ ω) (up₂ e) (up₂ N)
      (.bvar (.there .here)) (.bvar .here) (up₂ payload)) <| .conj
      (query_m (up₂ ω) (up₂ e) (up₂ N) (up₂ t₁) (up₂ f) (.bvar (.there .here)) (up₂ l))
      (query_m (up₂ ω) (up₂ e) (up₂ N) (up₂ t₁) (up₂ f) (.bvar .here) (up₂ l))

private theorem binary_delta_l {Γ Δ : SortContext ℒ}
    (ω e N t₁ f payload l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (binary_m ω e N t₁ f payload l) :=
  .bounded_exists ω <| .bounded_exists (up ω) <| .conj
    (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _) <| .conj
      (query_delta_l _ _ _ _ _ _ _) (query_delta_l _ _ _ _ _ _ _)

def binary_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N t₁ f payload l : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ ∃ j, member_l 𝒩 j ω ∧
    PowerlessBoundedNumericPairing.holds_l ω e N i j payload ∧
      query_holds_l ω e N t₁ f i l ∧ query_holds_l ω e N t₁ f j l

private theorem binary_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N t₁ f payload l : Term ℒ Γ Δ .set) :
    (binary_m ω e N t₁ f payload l).satisfies η ↔ binary_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (t₁.eval η) (f.eval η) (payload.eval η) (l.eval η) := by
  simp only [binary_m, binary_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    query_formula_l, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

private def existential_m {Γ Δ : SortContext ℒ}
    (ω e N t₁ f payload l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessSuccessorBounded.formula_m (up l) (.bvar .here))
    (query_m (up ω) (up e) (up N) (up t₁) (up f) (up payload) (.bvar .here))

private theorem existential_delta_l {Γ Δ : SortContext ℒ}
    (ω e N t₁ f payload l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (existential_m ω e N t₁ f payload l) :=
  .bounded_exists ω (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (query_delta_l _ _ _ _ _ _ _))

def existential_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N t₁ f payload l : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ PowerlessNatural.successor_l l m ∧ query_holds_l ω e N t₁ f payload m

private theorem existential_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N t₁ f payload l : Term ℒ Γ Δ .set) :
    (existential_m ω e N t₁ f payload l).satisfies η ↔ existential_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (t₁.eval η) (f.eval η) (payload.eval η) (l.eval η) := by
  simp only [existential_m, existential_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessSuccessorBounded.formula_l, query_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

private def cases_m {Γ Δ : SortContext ℒ}
    (ω e N t₁ t₂ t₃ t₄ f tag payload l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.disj (.equal tag e) (.equal tag t₁)) (atomic_m ω e N payload l)) <|
    .disj (.conj (.equal tag t₂) (query_m ω e N t₁ f payload l)) <|
      .disj (.conj (.equal tag t₃) (binary_m ω e N t₁ f payload l))
        (.conj (.equal tag t₄) (existential_m ω e N t₁ f payload l))

private theorem cases_delta_l {Γ Δ : SortContext ℒ}
    (ω e N t₁ t₂ t₃ t₄ f tag payload l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (cases_m ω e N t₁ t₂ t₃ t₄ f tag payload l) :=
  .disj (.conj (.disj (.equal _ _) (.equal _ _)) (atomic_delta_l _ _ _ _ _)) <|
    .disj (.conj (.equal _ _) (query_delta_l _ _ _ _ _ _ _)) <|
      .disj (.conj (.equal _ _) (binary_delta_l _ _ _ _ _ _ _))
        (.conj (.equal _ _) (existential_delta_l _ _ _ _ _ _ _))

def cases_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N t₁ t₂ t₃ t₄ f tag payload l : carrier_l 𝒩) : Prop :=
  ((tag = e ∨ tag = t₁) ∧ atomic_holds_l ω e N payload l) ∨
    (tag = t₂ ∧ query_holds_l ω e N t₁ f payload l) ∨
      (tag = t₃ ∧ binary_holds_l ω e N t₁ f payload l) ∨
        (tag = t₄ ∧ existential_holds_l ω e N t₁ f payload l)

private theorem cases_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N t₁ t₂ t₃ t₄ f tag payload l : Term ℒ Γ Δ .set) :
    (cases_m ω e N t₁ t₂ t₃ t₄ f tag payload l).satisfies η ↔ cases_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
      (f.eval η) (tag.eval η) (payload.eval η) (l.eval η) := by
  simp only [cases_m, cases_holds_l, Formula.satisfies,
    atomic_formula_l, query_formula_l, binary_formula_l, existential_formula_l]

def rule_m {Γ Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ f c l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.equal c e) <| membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up ω) <| .conj
      (node_m (up₂ ω) (up₂ e) (up₂ N) (.bvar (.there .here)) (.bvar .here) (up₂ c))
      (cases_m (up₂ ω) (up₂ e) (up₂ N) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄)
        (up₂ f) (.bvar (.there .here)) (.bvar .here) (up₂ l))

theorem rule_delta_l {Γ Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ f c l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (rule_m ω e N t₁ t₂ t₃ t₄ f c l) :=
  .disj (.equal _ _) <| .bounded_exists ω <| .bounded_exists (up ω) <| .conj
    (node_delta_l _ _ _ _ _ _) (cases_delta_l _ _ _ _ _ _ _ _ _ _ _)

def rule_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N t₁ t₂ t₃ t₄ f c l : carrier_l 𝒩) : Prop :=
  c = e ∨ ∃ tag, member_l 𝒩 tag ω ∧ ∃ payload, member_l 𝒩 payload ω ∧
    node_holds_l ω e N tag payload c ∧ cases_holds_l ω e N t₁ t₂ t₃ t₄ f tag payload l

theorem rule_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N t₁ t₂ t₃ t₄ f c l : Term ℒ Γ Δ .set) :
    (rule_m ω e N t₁ t₂ t₃ t₄ f c l).satisfies η ↔ rule_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
      (f.eval η) (c.eval η) (l.eval η) := by
  simp only [rule_m, rule_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, node_formula_l, cases_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def budget_m {Γ Δ : SortContext ℒ} (ω e N l c B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedAddition.formula_m (up ω) (up e) (up N) (up l) (up c) (.bvar .here))
    (.disj (.equal (.bvar .here) (up B)) (member_m (.bvar .here) (up B)))

theorem budget_delta_l {Γ Δ : SortContext ℒ} (ω e N l c B : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (budget_m ω e N l c B) :=
  .bounded_exists ω (.conj (PowerlessBoundedAddition.delta_l _ _ _ _ _ _)
    (.disj (.equal _ _) (.rel _ _)))

def budget_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N l c B : carrier_l 𝒩) : Prop :=
  ∃ s, member_l 𝒩 s ω ∧ PowerlessBoundedAddition.holds_l ω e N l c s ∧ (s = B ∨ member_l 𝒩 s B)

theorem budget_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N l c B : Term ℒ Γ Δ .set) :
    (budget_m ω e N l c B).satisfies η ↔ budget_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (l.eval η) (c.eval η) (B.eval η) := by
  simp only [budget_m, budget_holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedAddition.formula_l,
    member_m, member_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def trace_m {Γ Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ f C B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <| membershipLevyBound.boundedForall (up ω) <|
    let c : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let l : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
    .imp (.disj (.equal c (up₂ C)) (member_m c (up₂ C))) <|
      .imp (budget_m (up₂ ω) (up₂ e) (up₂ N) l c (up₂ B)) <|
        .iff (query_m (up₂ ω) (up₂ e) (up₂ N) (up₂ t₁) (up₂ f) c l)
          (rule_m (up₂ ω) (up₂ e) (up₂ N) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄) (up₂ f) c l)

theorem trace_delta_l {Γ Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ f C B : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (trace_m ω e N t₁ t₂ t₃ t₄ f C B) :=
  .bounded_forall ω <| .bounded_forall (up ω) <|
    .imp (.disj (.equal _ _) (.rel _ _)) <| .imp (budget_delta_l _ _ _ _ _ _) <|
      .iff (query_delta_l _ _ _ _ _ _ _) (rule_delta_l _ _ _ _ _ _ _ _ _ _)

def trace_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N t₁ t₂ t₃ t₄ f C B : carrier_l 𝒩) : Prop :=
  ∀ c, member_l 𝒩 c ω → ∀ l, member_l 𝒩 l ω → (c = C ∨ member_l 𝒩 c C) →
    budget_holds_l ω e N l c B →
      (query_holds_l ω e N t₁ f c l ↔ rule_holds_l ω e N t₁ t₂ t₃ t₄ f c l)

theorem trace_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N t₁ t₂ t₃ t₄ f C B : Term ℒ Γ Δ .set) :
    (trace_m ω e N t₁ t₂ t₃ t₄ f C B).satisfies η ↔ trace_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
      (f.eval η) (C.eval η) (B.eval η) := by
  simp only [trace_m, trace_holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, budget_formula_l, query_formula_l, rule_formula_l,
    member_m, member_l, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def certificate_m {Γ Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ c l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m c ω) <| .conj (member_m l ω) <|
    membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up N) <| .conj
      (budget_m (up₂ ω) (up₂ e) (up₂ N) (up₂ l) (up₂ c) (.bvar (.there .here))) <| .conj
        (trace_m (up₂ ω) (up₂ e) (up₂ N) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄)
          (.bvar .here) (up₂ c) (.bvar (.there .here)))
        (query_m (up₂ ω) (up₂ e) (up₂ N) (up₂ t₁) (.bvar .here) (up₂ c) (up₂ l))

theorem certificate_delta_l {Γ Δ : SortContext ℒ} (ω e N t₁ t₂ t₃ t₄ c l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (certificate_m ω e N t₁ t₂ t₃ t₄ c l) :=
  .conj (.rel _ _) <| .conj (.rel _ _) <|
    .bounded_exists ω <| .bounded_exists (up N) <| .conj (budget_delta_l _ _ _ _ _ _) <|
      .conj (trace_delta_l _ _ _ _ _ _ _ _ _ _) (query_delta_l _ _ _ _ _ _ _)

def certificate_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N t₁ t₂ t₃ t₄ c l : carrier_l 𝒩) : Prop :=
  member_l 𝒩 c ω ∧ member_l 𝒩 l ω ∧ ∃ B, member_l 𝒩 B ω ∧ ∃ f, member_l 𝒩 f N ∧
    budget_holds_l ω e N l c B ∧ trace_holds_l ω e N t₁ t₂ t₃ t₄ f c B ∧ query_holds_l ω e N t₁ f c l

theorem certificate_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N t₁ t₂ t₃ t₄ c l : Term ℒ Γ Δ .set) :
    (certificate_m ω e N t₁ t₂ t₃ t₄ c l).satisfies η ↔ certificate_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
      (c.eval η) (l.eval η) := by
  simp only [certificate_m, certificate_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    budget_formula_l, trace_formula_l, query_formula_l,
    member_m, member_l, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms certificate_delta_l
#print axioms certificate_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityBounded
