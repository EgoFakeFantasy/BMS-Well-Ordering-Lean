import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional

/-!
# 经典命题接口

本模块只使用 Hilbert 核中的 classical 模式和命题规则，不携带检查证书。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Derives

universe u v w

/-- 若在额外假设 ¬φ 下可推出 φ，则卸载该假设。 -/
theorem neg_assumption_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hFormula : Derives T (.neg formula :: Γ) formula) :
    Derives T Γ formula :=
  imp_elim
    (logical_axiom (.classical formula))
    (imp_intro hFormula)

/-- 反证法。 -/
theorem by_contradiction {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hRefute : Derives T (.neg formula :: Γ) .falsum) :
    Derives T Γ formula :=
  neg_assumption_elim (falsum_elim hRefute)

/-- 双重否定引入。 -/
theorem neg_neg_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hFormula : Derives T Γ formula) :
    Derives T Γ (.neg (.neg formula)) := by
  apply neg_intro
  exact neg_elim hFormula.context_weaken_cons
    (assumption List.mem_cons_self)

/-- 双重否定消去。 -/
theorem neg_neg_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hDoubleNegation : Derives T Γ (.neg (.neg formula))) :
    Derives T Γ formula := by
  apply by_contradiction
  exact neg_elim
    (assumption List.mem_cons_self)
    hDoubleNegation.context_weaken_cons

/-- 排中律。 -/
theorem excluded_middle {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} (formula : OpenFormula σ free) :
    Derives T Γ (.disj formula (.neg formula)) := by
  apply neg_assumption_elim
  have hNegFormula : Derives T
      (.neg (.disj formula (.neg formula)) :: Γ)
      (.neg formula) := by
    apply neg_intro
    have hDisjunction : Derives T
        (formula :: .neg (.disj formula (.neg formula)) :: Γ)
        (.disj formula (.neg formula)) :=
      disj_intro_left (assumption List.mem_cons_self)
    have hNegDisjunction : Derives T
        (formula :: .neg (.disj formula (.neg formula)) :: Γ)
        (.neg (.disj formula (.neg formula))) :=
      assumption (List.mem_cons_of_mem formula List.mem_cons_self)
    exact neg_elim hDisjunction hNegDisjunction
  exact disj_intro_right hNegFormula

end Derives
end FirstOrder
end Logic
end YesMetaZFC
