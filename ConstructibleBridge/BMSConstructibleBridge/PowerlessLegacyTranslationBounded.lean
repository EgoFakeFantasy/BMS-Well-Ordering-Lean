import BMSConstructibleBridge.PowerlessLegacyIndexBounded
import BMSConstructibleBridge.PowerlessFormulaConstructorBounded

/-! # 原部分翻译的纯 Δ₀ 有限证书

旧节点与二维表格用原平方配数，输出构造器用原三角图 T。V 是旧合法性
的实际二元图；查询必须同时满足 V，不能把总化表 f 的非法默认零当输出。
全部内部数字量词限于 ω，有限候选表限于完整 Seq(ω,ω) N；输出不另设 Q。

这里只给 AST、Δ₀ 分类和逐环境读数。预算可靠性、有限表存在及完整 Class
翻译图仍须接原递归和内部归纳；不宣称已有统一历史或最终 BMS Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₄ t)

def query_m {Γ Δ : SortContext ℒ} (ω e N V f c l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessValueBounded.formula_m V c l) <|
    membershipLevyBound.boundedExists ω <| .conj
      (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up N) (up c) (up l) (.bvar .here))
      (PowerlessValueBounded.formula_m (up f) (.bvar .here) (up q))

theorem query_delta_l {Γ Δ : SortContext ℒ} (ω e N V f c l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (query_m ω e N V f c l q) :=
  .conj (PowerlessValueBounded.delta_l _ _ _) <| .bounded_exists ω <| .conj
    (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _) (PowerlessValueBounded.delta_l _ _ _)

def query_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N V f c l q : carrier_l 𝒩) : Prop :=
  value_l V c l ∧ ∃ k, member_l 𝒩 k ω ∧
    PowerlessBoundedNumericPairing.holds_l ω e N c l k ∧ value_l f k q

theorem query_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N V f c l q : Term ℒ Γ Δ .set) :
    (query_m ω e N V f c l q).satisfies η ↔ query_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (V.eval η) (f.eval η) (c.eval η) (l.eval η) (q.eval η) := by
  simp only [query_m, query_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, PowerlessBoundedNumericPairing.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def atomic_m {Γ Δ : SortContext ℒ} (ω e N T t₁ tag p l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up₂ ω) <| membershipLevyBound.boundedExists (up₃ ω) <|
      let i : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
      let j : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let r : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let s : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .conj (PowerlessBoundedNumericPairing.formula_m (up₄ ω) (up₄ e) (up₄ N) i j (up₄ p)) <|
        .conj (PowerlessLegacyIndexBounded.formula_m (up₄ ω) (up₄ e) (up₄ N) (up₄ l) i r) <|
          .conj (PowerlessLegacyIndexBounded.formula_m (up₄ ω) (up₄ e) (up₄ N) (up₄ l) j s) <|
            .disj (.conj (.equal (up₄ tag) (up₄ e))
              (PowerlessFormulaConstructorBounded.formula_m (up₄ ω) (up₄ e) (up₄ N) (up₄ T) (up₄ t₁) r s (up₄ q)))
              (.conj (.equal (up₄ tag) (up₄ t₁))
                (PowerlessFormulaConstructorBounded.formula_m (up₄ ω) (up₄ e) (up₄ N) (up₄ T) (up₄ e) r s (up₄ q)))

theorem atomic_delta_l {Γ Δ : SortContext ℒ} (ω e N T t₁ tag p l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (atomic_m ω e N T t₁ tag p l q) :=
  .bounded_exists ω <| .bounded_exists (up ω) <| .bounded_exists (up₂ ω) <|
    .bounded_exists (up₃ ω) <| .conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _) <|
      .conj (PowerlessLegacyIndexBounded.delta_l _ _ _ _ _ _) <|
        .conj (PowerlessLegacyIndexBounded.delta_l _ _ _ _ _ _) <|
          .disj (.conj (.equal _ _) (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _))
            (.conj (.equal _ _) (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _))

def atomic_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₁ tag p l q : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ ∃ j, member_l 𝒩 j ω ∧ ∃ r, member_l 𝒩 r ω ∧ ∃ s, member_l 𝒩 s ω ∧
    PowerlessBoundedNumericPairing.holds_l ω e N i j p ∧
      PowerlessLegacyIndexBounded.holds_l ω e N l i r ∧
        PowerlessLegacyIndexBounded.holds_l ω e N l j s ∧
          ((tag = e ∧ PowerlessFormulaConstructorBounded.holds_l ω e N T t₁ r s q) ∨
            (tag = t₁ ∧ PowerlessFormulaConstructorBounded.holds_l ω e N T e r s q))

theorem atomic_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ tag p l q : Term ℒ Γ Δ .set) :
    (atomic_m ω e N T t₁ tag p l q).satisfies η ↔ atomic_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η)
        (tag.eval η) (p.eval η) (l.eval η) (q.eval η) := by
  simp only [atomic_m, atomic_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessBoundedNumericPairing.formula_l, PowerlessLegacyIndexBounded.formula_l,
    PowerlessFormulaConstructorBounded.formula_l, Arguments.eval,
    up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def negation_m {Γ Δ : SortContext ℒ} (ω e N T t₂ V f p l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (query_m (up ω) (up e) (up N) (up V) (up f) (up p) (up l) (.bvar .here))
    (PowerlessFormulaConstructorBounded.formula_m (up ω) (up e) (up N) (up T) (up t₂)
      (.bvar .here) (.bvar .here) (up q))

theorem negation_delta_l {Γ Δ : SortContext ℒ} (ω e N T t₂ V f p l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (negation_m ω e N T t₂ V f p l q) :=
  .bounded_exists ω (.conj (query_delta_l _ _ _ _ _ _ _ _)
    (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _))

def negation_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₂ V f p l q : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a ω ∧ query_holds_l ω e N V f p l a ∧
    PowerlessFormulaConstructorBounded.holds_l ω e N T t₂ a a q

theorem negation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₂ V f p l q : Term ℒ Γ Δ .set) :
    (negation_m ω e N T t₂ V f p l q).satisfies η ↔ negation_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₂.eval η)
        (V.eval η) (f.eval η) (p.eval η) (l.eval η) (q.eval η) := by
  simp only [negation_m, negation_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    query_formula_l, PowerlessFormulaConstructorBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def conjunction_m {Γ Δ : SortContext ℒ} (ω e N T t₂ V f p l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up₂ ω) <| membershipLevyBound.boundedExists (up₃ ω) <|
      membershipLevyBound.boundedExists (up₄ ω) <|
        let i : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
          .bvar (.there (.there (.there (.there .here))))
        let j : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
        let a : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
        let b : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
        let d : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
        .conj (PowerlessBoundedNumericPairing.formula_m (up₅ ω) (up₅ e) (up₅ N) i j (up₅ p)) <|
          .conj (query_m (up₅ ω) (up₅ e) (up₅ N) (up₅ V) (up₅ f) i (up₅ l) a) <|
            .conj (query_m (up₅ ω) (up₅ e) (up₅ N) (up₅ V) (up₅ f) j (up₅ l) b) <|
              .conj (PowerlessFormulaConstructorBounded.formula_m (up₅ ω) (up₅ e) (up₅ N) (up₅ T) (up₅ t₂) a b d)
                (PowerlessFormulaConstructorBounded.formula_m (up₅ ω) (up₅ e) (up₅ N) (up₅ T) (up₅ t₂) d d (up₅ q))

theorem conjunction_delta_l {Γ Δ : SortContext ℒ} (ω e N T t₂ V f p l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (conjunction_m ω e N T t₂ V f p l q) :=
  .bounded_exists ω <| .bounded_exists (up ω) <| .bounded_exists (up₂ ω) <|
    .bounded_exists (up₃ ω) <| .bounded_exists (up₄ ω) <|
      .conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _) <|
        .conj (query_delta_l _ _ _ _ _ _ _ _) <| .conj (query_delta_l _ _ _ _ _ _ _ _) <|
          .conj (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _)
            (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _)

def conjunction_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₂ V f p l q : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ ∃ j, member_l 𝒩 j ω ∧ ∃ a, member_l 𝒩 a ω ∧
    ∃ b, member_l 𝒩 b ω ∧ ∃ d, member_l 𝒩 d ω ∧
      PowerlessBoundedNumericPairing.holds_l ω e N i j p ∧ query_holds_l ω e N V f i l a ∧
        query_holds_l ω e N V f j l b ∧ PowerlessFormulaConstructorBounded.holds_l ω e N T t₂ a b d ∧
          PowerlessFormulaConstructorBounded.holds_l ω e N T t₂ d d q

theorem conjunction_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₂ V f p l q : Term ℒ Γ Δ .set) :
    (conjunction_m ω e N T t₂ V f p l q).satisfies η ↔ conjunction_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₂.eval η)
        (V.eval η) (f.eval η) (p.eval η) (l.eval η) (q.eval η) := by
  simp only [conjunction_m, conjunction_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessBoundedNumericPairing.formula_l, query_formula_l,
    PowerlessFormulaConstructorBounded.formula_l, Arguments.eval,
    up₅, up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def existential_m {Γ Δ : SortContext ℒ} (ω e N T t₃ V f p l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
    (PowerlessSuccessorBounded.formula_m (up₂ l) (.bvar (.there .here))) <| .conj
      (query_m (up₂ ω) (up₂ e) (up₂ N) (up₂ V) (up₂ f) (up₂ p) (.bvar (.there .here)) (.bvar .here))
      (PowerlessFormulaConstructorBounded.formula_m (up₂ ω) (up₂ e) (up₂ N) (up₂ T) (up₂ t₃)
        (up₂ l) (.bvar .here) (up₂ q))

theorem existential_delta_l {Γ Δ : SortContext ℒ} (ω e N T t₃ V f p l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (existential_m ω e N T t₃ V f p l q) :=
  .bounded_exists ω <| .bounded_exists (up ω) <| .conj
    (PowerlessSuccessorBounded.delta_l _ _) <| .conj (query_delta_l _ _ _ _ _ _ _ _)
      (PowerlessFormulaConstructorBounded.delta_l _ _ _ _ _ _ _ _)

def existential_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₃ V f p l q : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ ∃ a, member_l 𝒩 a ω ∧ PowerlessNatural.successor_l l m ∧
    query_holds_l ω e N V f p m a ∧ PowerlessFormulaConstructorBounded.holds_l ω e N T t₃ l a q

theorem existential_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₃ V f p l q : Term ℒ Γ Δ .set) :
    (existential_m ω e N T t₃ V f p l q).satisfies η ↔ existential_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₃.eval η)
        (V.eval η) (f.eval η) (p.eval η) (l.eval η) (q.eval η) := by
  simp only [existential_m, existential_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessSuccessorBounded.formula_l, query_formula_l,
    PowerlessFormulaConstructorBounded.formula_l, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def cases_m {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f tag p l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (atomic_m ω e N T t₁ tag p l q) <|
    .disj (.conj (.equal tag t₂) (negation_m ω e N T t₂ V f p l q)) <|
      .disj (.conj (.equal tag t₃) (conjunction_m ω e N T t₂ V f p l q))
        (.conj (.equal tag t₄) (existential_m ω e N T t₃ V f p l q))

theorem cases_delta_l {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f tag p l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (cases_m ω e N T t₁ t₂ t₃ t₄ V f tag p l q) :=
  .disj (atomic_delta_l _ _ _ _ _ _ _ _ _) <|
    .disj (.conj (.equal _ _) (negation_delta_l _ _ _ _ _ _ _ _ _ _)) <|
      .disj (.conj (.equal _ _) (conjunction_delta_l _ _ _ _ _ _ _ _ _ _))
        (.conj (.equal _ _) (existential_delta_l _ _ _ _ _ _ _ _ _ _))

def cases_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f tag p l q : carrier_l 𝒩) : Prop :=
  atomic_holds_l ω e N T t₁ tag p l q ∨
    (tag = t₂ ∧ negation_holds_l ω e N T t₂ V f p l q) ∨
      (tag = t₃ ∧ conjunction_holds_l ω e N T t₂ V f p l q) ∨
        (tag = t₄ ∧ existential_holds_l ω e N T t₃ V f p l q)

theorem cases_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ t₄ V f tag p l q : Term ℒ Γ Δ .set) :
    (cases_m ω e N T t₁ t₂ t₃ t₄ V f tag p l q).satisfies η ↔ cases_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
        (V.eval η) (f.eval η) (tag.eval η) (p.eval η) (l.eval η) (q.eval η) := by
  simp only [cases_m, cases_holds_l, Formula.satisfies, atomic_formula_l, negation_formula_l,
    conjunction_formula_l, existential_formula_l]

def point_m {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f c l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.equal c e) (.equal q e)) <|
    membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
      (PowerlessLegacyValidityBounded.node_m (up₂ ω) (up₂ e) (up₂ N)
        (.bvar (.there .here)) (.bvar .here) (up₂ c))
      (cases_m (up₂ ω) (up₂ e) (up₂ N) (up₂ T) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄)
        (up₂ V) (up₂ f) (.bvar (.there .here)) (.bvar .here) (up₂ l) (up₂ q))

theorem point_delta_l {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f c l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (point_m ω e N T t₁ t₂ t₃ t₄ V f c l q) :=
  .disj (.conj (.equal _ _) (.equal _ _)) <| .bounded_exists ω <| .bounded_exists (up ω) <|
    .conj (PowerlessLegacyValidityBounded.node_delta_l _ _ _ _ _ _)
      (cases_delta_l _ _ _ _ _ _ _ _ _ _ _ _ _ _)

def point_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f c l q : carrier_l 𝒩) : Prop :=
  (c = e ∧ q = e) ∨ ∃ tag, member_l 𝒩 tag ω ∧ ∃ p, member_l 𝒩 p ω ∧
    PowerlessLegacyValidityBounded.node_holds_l ω e N tag p c ∧
      cases_holds_l ω e N T t₁ t₂ t₃ t₄ V f tag p l q

theorem point_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ t₄ V f c l q : Term ℒ Γ Δ .set) :
    (point_m ω e N T t₁ t₂ t₃ t₄ V f c l q).satisfies η ↔ point_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
        (V.eval η) (f.eval η) (c.eval η) (l.eval η) (q.eval η) := by
  simp only [point_m, point_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessLegacyValidityBounded.node_formula_l, cases_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def trace_m {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f C B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <| membershipLevyBound.boundedForall (up ω) <|
    membershipLevyBound.boundedForall (up₂ ω) <|
      let c : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let l : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let q : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .imp (.disj (.equal c (up₃ C)) (member_m c (up₃ C))) <|
        .imp (PowerlessLegacyValidityBounded.budget_m (up₃ ω) (up₃ e) (up₃ N) l c (up₃ B)) <|
          .iff (query_m (up₃ ω) (up₃ e) (up₃ N) (up₃ V) (up₃ f) c l q)
            (point_m (up₃ ω) (up₃ e) (up₃ N) (up₃ T) (up₃ t₁) (up₃ t₂) (up₃ t₃) (up₃ t₄)
              (up₃ V) (up₃ f) c l q)

theorem trace_delta_l {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f C B : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (trace_m ω e N T t₁ t₂ t₃ t₄ V f C B) :=
  .bounded_forall ω <| .bounded_forall (up ω) <| .bounded_forall (up₂ ω) <|
    .imp (.disj (.equal _ _) (.rel _ _)) <|
      .imp (PowerlessLegacyValidityBounded.budget_delta_l _ _ _ _ _ _) <|
        .iff (query_delta_l _ _ _ _ _ _ _ _) (point_delta_l _ _ _ _ _ _ _ _ _ _ _ _ _)

def trace_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V f C B : carrier_l 𝒩) : Prop :=
  ∀ c, member_l 𝒩 c ω → ∀ l, member_l 𝒩 l ω → ∀ q, member_l 𝒩 q ω →
    (c = C ∨ member_l 𝒩 c C) → PowerlessLegacyValidityBounded.budget_holds_l ω e N l c B →
      (query_holds_l ω e N V f c l q ↔ point_holds_l ω e N T t₁ t₂ t₃ t₄ V f c l q)

theorem trace_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ t₄ V f C B : Term ℒ Γ Δ .set) :
    (trace_m ω e N T t₁ t₂ t₃ t₄ V f C B).satisfies η ↔ trace_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
        (V.eval η) (f.eval η) (C.eval η) (B.eval η) := by
  simp only [trace_m, trace_holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessLegacyValidityBounded.budget_formula_l, query_formula_l, point_formula_l,
    member_m, member_l, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def certificate_m {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V c l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m c ω) <| .conj (member_m l ω) <| .conj (member_m q ω) <|
    membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up N) <| .conj
      (PowerlessLegacyValidityBounded.budget_m (up₂ ω) (up₂ e) (up₂ N) (up₂ l) (up₂ c) (.bvar (.there .here))) <|
        .conj (trace_m (up₂ ω) (up₂ e) (up₂ N) (up₂ T) (up₂ t₁) (up₂ t₂) (up₂ t₃) (up₂ t₄)
          (up₂ V) (.bvar .here) (up₂ c) (.bvar (.there .here)))
          (query_m (up₂ ω) (up₂ e) (up₂ N) (up₂ V) (.bvar .here) (up₂ c) (up₂ l) (up₂ q))

theorem certificate_delta_l {Γ Δ : SortContext ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V c l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (certificate_m ω e N T t₁ t₂ t₃ t₄ V c l q) :=
  .conj (.rel _ _) <| .conj (.rel _ _) <| .conj (.rel _ _) <|
    .bounded_exists ω <| .bounded_exists (up N) <|
      .conj (PowerlessLegacyValidityBounded.budget_delta_l _ _ _ _ _ _) <|
        .conj (trace_delta_l _ _ _ _ _ _ _ _ _ _ _ _) (query_delta_l _ _ _ _ _ _ _ _)

def certificate_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N T t₁ t₂ t₃ t₄ V c l q : carrier_l 𝒩) : Prop :=
  member_l 𝒩 c ω ∧ member_l 𝒩 l ω ∧ member_l 𝒩 q ω ∧
    ∃ B, member_l 𝒩 B ω ∧ ∃ f, member_l 𝒩 f N ∧
      PowerlessLegacyValidityBounded.budget_holds_l ω e N l c B ∧
        trace_holds_l ω e N T t₁ t₂ t₃ t₄ V f c B ∧ query_holds_l ω e N V f c l q

theorem certificate_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ t₄ V c l q : Term ℒ Γ Δ .set) :
    (certificate_m ω e N T t₁ t₂ t₃ t₄ V c l q).satisfies η ↔ certificate_holds_l
      (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (t₄.eval η)
        (V.eval η) (c.eval η) (l.eval η) (q.eval η) := by
  simp only [certificate_m, certificate_holds_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessLegacyValidityBounded.budget_formula_l, trace_formula_l, query_formula_l,
    member_m, member_l, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms certificate_delta_l
#print axioms certificate_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationBounded
