import BMSConstructibleBridge.PowerlessEvaluationClauseBounded
import BMSConstructibleBridge.PowerlessMapBounded

/-! # 三角公式合法性的有界有限证书

检查表是某个内部有限初段到 ω 的集合函数；值为一表示该码在给定槽界下
合法。所有候选表限于 Seq(ω)，构造子检查复用原三角配数的 Δ₀ 公式。
这里只给实际 AST、有界性和逐环境读数；与原合法性 V 的等价须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)
open PowerlessEvaluationClauseBounded (branch_m branch_l branch_delta_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def rule_m {Γ Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ f c l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := up (up s)
  let atom : Formula ℒ (.set :: .set :: Γ) Δ :=
    .conj (member_m (.bvar (.there .here)) (w l)) (member_m (.bvar .here) (w l))
  .disj (.equal c e) <| .disj (branch_m ω e N T e c atom) <|
    .disj (branch_m ω e N T t₁ c atom) <|
      .disj (branch_m ω e N T t₂ c <| .conj
        (PowerlessValueBounded.formula_m (w f) (.bvar (.there .here)) (w t₁))
        (PowerlessValueBounded.formula_m (w f) (.bvar .here) (w t₁)))
        (branch_m ω e N T t₃ c <| .conj (member_m (.bvar (.there .here)) (w l))
          (PowerlessValueBounded.formula_m (w f) (.bvar .here) (w t₁)))

theorem rule_delta_l {Γ Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ f c l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (rule_m ω e N T t₁ t₂ t₃ f c l) :=
  .disj (.equal _ _) <| .disj (branch_delta_l _ _ _ _ _ _ (.conj (.rel _ _) (.rel _ _))) <|
    .disj (branch_delta_l _ _ _ _ _ _ (.conj (.rel _ _) (.rel _ _))) <|
      .disj (branch_delta_l _ _ _ _ _ _ (.conj (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessValueBounded.delta_l _ _ _)))
        (branch_delta_l _ _ _ _ _ _ (.conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)))

def rule_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N T t₁ t₂ t₃ f c l : carrier_l 𝒩) : Prop :=
  c = e ∨ branch_l ω e N T e c (fun a b => member_l 𝒩 a l ∧ member_l 𝒩 b l) ∨
    branch_l ω e N T t₁ c (fun a b => member_l 𝒩 a l ∧ member_l 𝒩 b l) ∨
      branch_l ω e N T t₂ c (fun a b => value_l f a t₁ ∧ value_l f b t₁) ∨
        branch_l ω e N T t₃ c (fun a b => member_l 𝒩 a l ∧ value_l f b t₁)

theorem rule_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ f c l : Term ℒ Γ Δ .set) :
    (rule_m ω e N T t₁ t₂ t₃ f c l).satisfies η ↔
      rule_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (f.eval η) (c.eval η) (l.eval η) := by
  simp only [rule_m, rule_l, branch_m, branch_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessFormulaConstructorBounded.formula_l, PowerlessValueBounded.formula_l,
    member_m, member_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def trace_m {Γ Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ f m l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessMapBounded.formula_m f m ω) <| membershipLevyBound.boundedForall m <|
    .iff (PowerlessValueBounded.formula_m (up f) (.bvar .here) (up t₁))
      (rule_m (up ω) (up e) (up N) (up T) (up t₁) (up t₂) (up t₃) (up f) (.bvar .here) (up l))

theorem trace_delta_l {Γ Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ f m l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (trace_m ω e N T t₁ t₂ t₃ f m l) :=
  .conj (PowerlessMapBounded.delta_l _ _ _) <| .bounded_forall m <|
    .iff (PowerlessValueBounded.delta_l _ _ _) (rule_delta_l _ _ _ _ _ _ _ _ _ _)

def trace_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N T t₁ t₂ t₃ f m l : carrier_l 𝒩) : Prop :=
  map_l f m ω ∧ ∀ c, member_l 𝒩 c m →
    (value_l f c t₁ ↔ rule_l ω e N T t₁ t₂ t₃ f c l)

theorem trace_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ f m l : Term ℒ Γ Δ .set) :
    (trace_m ω e N T t₁ t₂ t₃ f m l).satisfies η ↔
      trace_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (f.eval η) (m.eval η) (l.eval η) := by
  simp only [trace_m, trace_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessValueBounded.formula_l, rule_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def query_m {Γ Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ c l : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := up (up s)
  .conj (member_m c ω) <| .conj (member_m l ω) <|
    membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up N) <|
      .conj (member_m (w c) (.bvar (.there .here))) <|
        .conj (trace_m (w ω) (w e) (w N) (w T) (w t₁) (w t₂) (w t₃)
          (.bvar .here) (.bvar (.there .here)) (w l))
          (PowerlessValueBounded.formula_m (.bvar .here) (w c) (w t₁))

theorem query_delta_l {Γ Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ c l : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (query_m ω e N T t₁ t₂ t₃ c l) :=
  .conj (.rel _ _) <| .conj (.rel _ _) <|
    .bounded_exists ω <| .bounded_exists (up N) <| .conj (.rel _ _) <|
      .conj (trace_delta_l _ _ _ _ _ _ _ _ _ _) (PowerlessValueBounded.delta_l _ _ _)

def query_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N T t₁ t₂ t₃ c l : carrier_l 𝒩) : Prop :=
  member_l 𝒩 c ω ∧ member_l 𝒩 l ω ∧ ∃ m, member_l 𝒩 m ω ∧
    ∃ f, member_l 𝒩 f N ∧ member_l 𝒩 c m ∧ trace_l ω e N T t₁ t₂ t₃ f m l ∧ value_l f c t₁

theorem query_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ c l : Term ℒ Γ Δ .set) :
    (query_m ω e N T t₁ t₂ t₃ c l).satisfies η ↔
      query_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (c.eval η) (l.eval η) := by
  simp only [query_m, query_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, trace_formula_l, PowerlessValueBounded.formula_l,
    member_m, member_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms query_delta_l
#print axioms query_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityBounded
