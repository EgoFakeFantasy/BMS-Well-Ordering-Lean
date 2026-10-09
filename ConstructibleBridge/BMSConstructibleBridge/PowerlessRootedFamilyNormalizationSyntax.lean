import BMSConstructibleBridge.PowerlessRootedRealSyntax
import BMSConstructibleBridge.PowerlessSuccessorBounded

/-! # 统一带根族零根规范化的纯有界正文

纯隶属 ℒ。族、行标记、配数及后继均读取实际参数，不把环境实数
偷偷放进 Class 量词。所有新数变量界于同一个内部 ω，正文为 Δ₀。
这里仅给实际检查器及逐公式读数，尚不证明整个解码集合属于遗传域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRootedFamilyNormalizationSyntax

open Logic FirstOrder StabilityFrame ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def root_m {Γ Δ : SortContext ℒ} (ω e o S U i r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up S) (up o) (up r) (.bvar .here))
    (PowerlessRootedRealSyntax.row_m (up ω) (up e) (up S) (up U) (up i) (.bvar .here))

def graph_m {Γ Δ : SortContext ℒ} (ω e S U i a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up (up ω)) (up (up e)) (up (up S))
      (up (up a)) (up (up b)) (.bvar (.there .here))) <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up (up ω)) (up (up e)) (up (up S))
      (up (up e)) (.bvar (.there .here)) (.bvar .here))
    (PowerlessRootedRealSyntax.row_m (up (up ω)) (up (up e)) (up (up S)) (up (up U))
      (up (up i)) (.bvar .here))

def edge_m {Γ Δ : SortContext ℒ} (ω e o S U i a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (root_m (up ω) (up e) (up o) (up S) (up U) (up i) (.bvar .here)) <|
    membershipLevyBound.boundedExists (up ω) <| .conj
      (PowerlessSuccessorBounded.formula_m (.bvar .here) (up (up a))) <| .disj
      (.conj (.equal (up (up b)) (up (up e)))
        (graph_m (up (up ω)) (up (up e)) (up (up S)) (up (up U))
          (up (up i)) (.bvar .here) (.bvar (.there .here))))
      (membershipLevyBound.boundedExists (up (up ω)) <| .conj
        (PowerlessSuccessorBounded.formula_m (.bvar .here) (up (up (up b))))
        (graph_m (up (up (up ω))) (up (up (up e))) (up (up (up S))) (up (up (up U)))
          (up (up (up i))) (.bvar (.there .here)) (.bvar .here)))

def body_m {Γ Δ : SortContext ℒ} (ω e o S U i z : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up (up ω)) (up (up e)) (up (up S))
      (.bvar (.there .here)) (.bvar .here) (up (up z)))
    (edge_m (up (up ω)) (up (up e)) (up (up o)) (up (up S)) (up (up U))
      (up (up i)) (.bvar (.there .here)) (.bvar .here))

theorem root_delta_m {Γ Δ : SortContext ℒ} (ω e o S U i r : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (root_m ω e o S U i r) :=
  .bounded_exists _ (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (PowerlessRootedRealSyntax.row_delta_m _ _ _ _ _ _))

theorem graph_delta_m {Γ Δ : SortContext ℒ} (ω e S U i a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (graph_m ω e S U i a b) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
      (PowerlessRootedRealSyntax.row_delta_m _ _ _ _ _ _))))

theorem edge_delta_m {Γ Δ : SortContext ℒ} (ω e o S U i a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (edge_m ω e o S U i a b) :=
  .bounded_exists _ (.conj (root_delta_m _ _ _ _ _ _ _)
    (.bounded_exists _ (.conj (PowerlessSuccessorBounded.delta_l _ _)
      (.disj (.conj (.equal _ _) (graph_delta_m _ _ _ _ _ _ _))
        (.bounded_exists _ (.conj (PowerlessSuccessorBounded.delta_l _ _)
          (graph_delta_m _ _ _ _ _ _ _)))))))

theorem body_delta_m {Γ Δ : SortContext ℒ} (ω e o S U i z : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m ω e o S U i z) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (edge_delta_m _ _ _ _ _ _ _ _)))

def root_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e o S U i r : carrier_l 𝒩) : Prop :=
  ∃ c, member_l 𝒩 c ω ∧ PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S o r c ∧
    PowerlessRootedRealSyntax.row_l (𝒩 := 𝒩) ω e S U i c

def graph_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S U i a b : carrier_l 𝒩) : Prop :=
  ∃ c, member_l 𝒩 c ω ∧ ∃ d, member_l 𝒩 d ω ∧
    PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S a b c ∧
    PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S e c d ∧
    PowerlessRootedRealSyntax.row_l (𝒩 := 𝒩) ω e S U i d

def edge_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e o S U i a b : carrier_l 𝒩) : Prop :=
  ∃ r, member_l 𝒩 r ω ∧ root_l ω e o S U i r ∧
    ∃ c, member_l 𝒩 c ω ∧ PowerlessNatural.successor_l (ℳ := 𝒩) c a ∧
      ((b = e ∧ graph_l ω e S U i c r) ∨ ∃ d, member_l 𝒩 d ω ∧
        PowerlessNatural.successor_l (ℳ := 𝒩) d b ∧ graph_l ω e S U i c d)

def body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e o S U i z : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a ω ∧ ∃ b, member_l 𝒩 b ω ∧
    PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S a b z ∧ edge_l ω e o S U i a b

theorem root_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e o S U i r : Term ℒ Γ Δ .set) :
    (root_m ω e o S U i r).satisfies η ↔
      root_l (ω.eval η) (e.eval η) (o.eval η) (S.eval η) (U.eval η) (i.eval η) (r.eval η) := by
  simp only [root_m, root_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessRootedRealSyntax.row_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S U i a b : Term ℒ Γ Δ .set) :
    (graph_m ω e S U i a b).satisfies η ↔
      graph_l (ω.eval η) (e.eval η) (S.eval η) (U.eval η) (i.eval η) (a.eval η) (b.eval η) := by
  simp only [graph_m, graph_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessRootedRealSyntax.row_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem edge_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e o S U i a b : Term ℒ Γ Δ .set) :
    (edge_m ω e o S U i a b).satisfies η ↔
      edge_l (ω.eval η) (e.eval η) (o.eval η) (S.eval η) (U.eval η) (i.eval η) (a.eval η) (b.eval η) := by
  simp only [edge_m, edge_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, root_formula_l, graph_formula_l,
    PowerlessSuccessorBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e o S U i z : Term ℒ Γ Δ .set) :
    (body_m ω e o S U i z).satisfies η ↔
      body_l (ω.eval η) (e.eval η) (o.eval η) (S.eval η) (U.eval η) (i.eval η) (z.eval η) := by
  simp only [body_m, body_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    edge_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms body_delta_m
#print axioms body_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRootedFamilyNormalizationSyntax
