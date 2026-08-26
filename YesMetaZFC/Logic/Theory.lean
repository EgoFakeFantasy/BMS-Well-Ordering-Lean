import YesMetaZFC.Logic.Semantics
import YesMetaZFC.Logic.Theory.Basic

/-!
# 一阶理论语义

本模块在纯语法理论谓词上叠加模型与语义蕴涵。只需要理论成员关系的证明模块应直接
导入 `Logic.Theory.Basic`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace Theory

/-- 一个赋值满足理论中的所有公式。 -/
def Models {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (T : Theory σ) (env : Env M) : Prop :=
  ∀ φ, T φ → Formula.satisfies env φ

/-- 固定模型 universe 的语义蕴涵。 -/
def SemanticallyEntails {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (T : Theory σ) (φ : Formula σ) : Prop :=
  ∀ {M : Structure.{u, v, w, x} σ}, ∀ env : Env M,
    Models T env → Formula.satisfies env φ

scoped infix:50 " ⊨ₛ " => SemanticallyEntails

theorem models_empty {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (env : Env M) :
    Models (empty : Theory σ) env := by
  intro φ hφ
  cases hφ

theorem models_insert {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {T : Theory σ} {φ : Formula σ}
    {env : Env M} :
    Models (insert φ T) env ↔ Formula.satisfies env φ ∧ Models T env := by
  constructor
  · intro h
    exact ⟨h φ (Or.inl rfl), by
      intro ψ hψ
      exact h ψ (Or.inr hψ)⟩
  · intro h ψ hψ
    rcases h with ⟨hφ, hT⟩
    rcases hψ with hEq | hMem
    · simpa [hEq] using hφ
    · exact hT ψ hMem

theorem entails_of_mem {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {φ : Formula σ} (hMem : T φ) :
    SemanticallyEntails.{u, v, w, x} T φ := by
  intro M env hModels
  exact hModels φ hMem

theorem entails_weaken {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T U : Theory σ} {φ : Formula σ}
    (hSub : ∀ ψ, U ψ → T ψ)
    (hEntails : SemanticallyEntails.{u, v, w, x} U φ) :
    SemanticallyEntails.{u, v, w, x} T φ := by
  intro M env hModels
  exact hEntails env (by
    intro ψ hψ
    exact hModels ψ (hSub ψ hψ))

end Theory
end FirstOrder
end Logic
end YesMetaZFC
