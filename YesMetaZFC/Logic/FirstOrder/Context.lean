import YesMetaZFC.Logic.FirstOrder.Context.Basic
import YesMetaZFC.Logic.Theory

/-!
# 一阶局部上下文语义

本模块在纯语法上下文上定义逐式满足关系。只需要上下文列表的证明模块应直接导入
`Logic.FirstOrder.Context.Basic`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace Context

/-- 环境满足上下文中的每一个公式。 -/
def Satisfied {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (env : Env M) (context : Context σ) : Prop :=
  ∀ formula, formula ∈ context → Formula.satisfies env formula

theorem sat_mem_m {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Env M}
    {context : Context σ} (hContext : Satisfied env context)
    {formula : Formula σ} (hMem : formula ∈ context) :
    Formula.satisfies env formula :=
  hContext formula hMem

theorem sat_cons_iff_m {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Env M}
    {formula : Formula σ} {context : Context σ} :
    Satisfied env (formula :: context) ↔
      Formula.satisfies env formula ∧ Satisfied env context := by
  constructor
  · intro h
    exact ⟨h formula (by simp), by
      intro ψ hψ
      exact h ψ (by simp [hψ])⟩
  · rintro ⟨hFormula, hContext⟩ ψ hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · exact hFormula
    · exact hContext ψ hMem

theorem sat_weaken_m {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {env : Env M}
    {small large : Context σ}
    (hSubset : ∀ formula, formula ∈ small → formula ∈ large)
    (hLarge : Satisfied env large) :
    Satisfied env small :=
  fun formula hMem => hLarge formula (hSubset formula hMem)

end Context
end FirstOrder
end Logic
end YesMetaZFC
