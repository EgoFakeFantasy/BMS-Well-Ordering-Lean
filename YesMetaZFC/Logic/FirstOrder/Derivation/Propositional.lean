import YesMetaZFC.Logic.FirstOrder.Derivation.Structural

/-!
# Hilbert 核上的命题规则

本模块把标准连接词模式组合成局部上下文接口。所有公式已经内在良构，规则不携带
admissible、check certificate 或 sort 判定前提。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Derives

universe u v w

/-- 局部假设。 -/
theorem assumption {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hMem : formula ∈ Γ) :
    Derives T Γ formula :=
  assumption_of_mem hMem

/-- 蕴含引入。 -/
theorem imp_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {antecedent consequent : OpenFormula σ free}
    (hBody : Derives T (antecedent :: Γ) consequent) :
    Derives T Γ (.imp antecedent consequent) :=
  deduction hBody

/-- 蕴含消去。 -/
theorem imp_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {antecedent consequent : OpenFormula σ free}
    (hImplication : Derives T Γ (.imp antecedent consequent))
    (hAntecedent : Derives T Γ antecedent) :
    Derives T Γ consequent :=
  modus_ponens hAntecedent hImplication

/-- 蕴含的传递组合。 -/
theorem imp_trans {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {first middle last : OpenFormula σ free}
    (hFirst : Derives T Γ (.imp first middle))
    (hSecond : Derives T Γ (.imp middle last)) :
    Derives T Γ (.imp first last) := by
  apply imp_intro
  exact imp_elim hSecond.context_weaken_cons
    (imp_elim hFirst.context_weaken_cons
      (assumption List.mem_cons_self))

/-- 真公式引入。 -/
theorem truth_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} :
    Derives T Γ (.truth : OpenFormula σ free) :=
  logical_axiom .truth_intro

/-- 从假推出任意结论。 -/
theorem falsum_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {conclusion : OpenFormula σ free}
    (hFalsum : Derives T Γ .falsum) :
    Derives T Γ conclusion :=
  imp_elim (logical_axiom (.falsum_elimination conclusion)) hFalsum

/-- 否定引入。 -/
theorem neg_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hRefute : Derives T (formula :: Γ) .falsum) :
    Derives T Γ (.neg formula) :=
  imp_elim (logical_axiom (.negation_intro formula))
    (imp_intro hRefute)

/-- 否定消去得到假。 -/
theorem neg_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hFormula : Derives T Γ formula)
    (hNegation : Derives T Γ (.neg formula)) :
    Derives T Γ .falsum := by
  have hStep : Derives T Γ (.imp (.neg formula) .falsum) :=
    imp_elim
      (logical_axiom (.negation_elimination formula))
      hFormula
  exact imp_elim hStep hNegation

/-- 公式与其否定推出任意结论。 -/
theorem contradiction_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {formula conclusion : OpenFormula σ free}
    (hFormula : Derives T Γ formula)
    (hNegation : Derives T Γ (.neg formula)) :
    Derives T Γ conclusion :=
  falsum_elim (neg_elim hFormula hNegation)

/-- 合取引入。 -/
theorem conj_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hLeft : Derives T Γ left) (hRight : Derives T Γ right) :
    Derives T Γ (.conj left right) := by
  have hStep : Derives T Γ (.imp right (.conj left right)) :=
    imp_elim
      (logical_axiom (.conjunction_intro left right))
      hLeft
  exact imp_elim hStep hRight

/-- 合取消去左分量。 -/
theorem conj_elim_left {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hConjunction : Derives T Γ (.conj left right)) :
    Derives T Γ left :=
  imp_elim
    (logical_axiom (.conjunction_elim_left left right))
    hConjunction

/-- 合取消去右分量。 -/
theorem conj_elim_right {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hConjunction : Derives T Γ (.conj left right)) :
    Derives T Γ right :=
  imp_elim
    (logical_axiom (.conjunction_elim_right left right))
    hConjunction

/-- 析取左引入。 -/
theorem disj_intro_left {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hLeft : Derives T Γ left) :
    Derives T Γ (.disj left right) :=
  imp_elim
    (logical_axiom (.disjunction_intro_left left right))
    hLeft

/-- 析取右引入。 -/
theorem disj_intro_right {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hRight : Derives T Γ right) :
    Derives T Γ (.disj left right) :=
  imp_elim
    (logical_axiom (.disjunction_intro_right left right))
    hRight

/-- 析取消去。 -/
theorem disj_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {left right conclusion : OpenFormula σ free}
    (hDisjunction : Derives T Γ (.disj left right))
    (hLeft : Derives T (left :: Γ) conclusion)
    (hRight : Derives T (right :: Γ) conclusion) :
    Derives T Γ conclusion := by
  have hStepLeft : Derives T Γ
      (.imp (.imp right conclusion)
        (.imp (.disj left right) conclusion)) :=
    imp_elim
      (logical_axiom
        (.disjunction_elimination left right conclusion))
      (imp_intro hLeft)
  have hStepRight : Derives T Γ
      (.imp (.disj left right) conclusion) :=
    imp_elim hStepLeft (imp_intro hRight)
  exact imp_elim hStepRight hDisjunction

/-- 双条件引入。 -/
theorem iff_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hForward : Derives T (left :: Γ) right)
    (hBackward : Derives T (right :: Γ) left) :
    Derives T Γ (.iff left right) := by
  have hStep : Derives T Γ
      (.imp (.imp right left) (.iff left right)) :=
    imp_elim
      (logical_axiom (.biconditional_intro left right))
      (imp_intro hForward)
  exact imp_elim hStep (imp_intro hBackward)

/-- 双条件向右消去。 -/
theorem iff_elim_left {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hIff : Derives T Γ (.iff left right))
    (hLeft : Derives T Γ left) :
    Derives T Γ right :=
  imp_elim
    (imp_elim
      (logical_axiom (.biconditional_elim_left left right))
      hIff)
    hLeft

/-- 双条件向左消去。 -/
theorem iff_elim_right {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hIff : Derives T Γ (.iff left right))
    (hRight : Derives T Γ right) :
    Derives T Γ left :=
  imp_elim
    (imp_elim
      (logical_axiom (.biconditional_elim_right left right))
      hIff)
    hRight

namespace Propositional

/-- 蕴含对共同前件的分配。 -/
theorem imp_distribution {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    (antecedent middle consequent : OpenFormula σ free) :
    Derives T Γ
      (.imp (.imp antecedent (.imp middle consequent))
        (.imp (.imp antecedent middle) (.imp antecedent consequent))) :=
  logical_axiom
    (.implication_distribution antecedent middle consequent)

/-- 蕴含的自反性。 -/
theorem imp_refl {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} (formula : OpenFormula σ free) :
    Derives T Γ (.imp formula formula) :=
  of_provable (Provable.self_implication formula)

/-- 已知前件时可忽略额外假设。 -/
theorem imp_const {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    (formula extra : OpenFormula σ free) :
    Derives T Γ (.imp formula (.imp extra formula)) :=
  logical_axiom (.weakening formula extra)

/-- 经典归约模式。 -/
theorem classical_reduction {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} (formula : OpenFormula σ free) :
    Derives T Γ (.imp (.imp (.neg formula) formula) formula) :=
  logical_axiom (.classical formula)

/-- 经典二分模式。 -/
theorem case_analysis {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    (formula conclusion : OpenFormula σ free) :
    Derives T Γ
      (.imp (.imp formula conclusion)
        (.imp (.imp (.neg formula) conclusion) conclusion)) :=
  logical_axiom (.case_analysis formula conclusion)

end Propositional
end Derives
end FirstOrder
end Logic
end YesMetaZFC
