import YesMetaZFC.Automation.RelationalCongruence

/-! # 已覆盖原公式在模型扩张之间的传输

两份实际解释只须在该正文使用的符号上相同。证明通过纯翻译的语法同余，
不展开选择所得的函数值或递归关系图。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
universe x
variable {σ τ : Signature.{0,0,0}}
variable (I : Interpretation σ τ)
variable (functions : (symbol : σ.FuncSymbol) → Formula τ [] (I.sort (σ.funcCodomain symbol) :: (σ.funcDomain symbol).map I.sort))
variable (relations : (symbol : σ.RelSymbol) → Formula τ [] ((σ.relDomain symbol).map I.sort))
variable {ℳ : Structure.{0,0,0,x} τ}

theorem regraph_mapValues {sorts : SortContext σ}
    (args : Values (fun sort => ℳ.Carrier (I.sort sort)) sorts) :
    mapValues (regraph I functions relations) args = mapValues I args := by
  induction args with
  | nil => rfl
  | cons head tail ih => simp only [mapValues]; rw [ih]

/-- 相同实际图的函数值由其实现唯一性保持。 -/
theorem function_regraph (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    (symbol : σ.FuncSymbol) (hGraph : functions symbol = I.function symbol)
    (args : Values source.model.Carrier (σ.funcDomain symbol)) :
    target.function symbol args = source.function symbol args := by
  have hNew := (hTarget.function symbol args _).mpr rfl
  change (functions symbol).satisfies
    (templateEnv (.cons (target.function symbol args) (mapValues (regraph I functions relations) args))) at hNew
  rw [hGraph, regraph_mapValues] at hNew
  exact (hSource.function symbol args _).mp hNew

theorem transfer_covered (source : Expansion I ℳ) (hSource : Realizes source)
    (target : Expansion (regraph I functions relations) ℳ) (hTarget : Realizes target)
    (fc : σ.FuncSymbol → Bool) (rc : σ.RelSymbol → Bool)
    (hFunctions : ∀ symbol, fc symbol = true → functions symbol = I.function symbol)
    (hRelations : ∀ symbol, rc symbol = true → relations symbol = I.relation symbol)
    {free : SortContext σ} (body : Formula σ [] free)
    (hCovered : formulaCovered fc rc body = true) (args : Values source.model.Carrier free) :
    body.satisfies (templateEnv args : Env source.model [] free) ↔
      body.satisfies (templateEnv args : Env target.model [] free) := by
  have hTranslate := openFormula_congr I functions relations fc rc hFunctions hRelations body hCovered
  have hNew := openFormula_correct target hTarget body args
  rw [hTranslate, regraph_mapValues] at hNew
  exact (openFormula_correct source hSource body args).symm.trans hNew

end YesMetaZFC.Automation.RelationalTranslation
