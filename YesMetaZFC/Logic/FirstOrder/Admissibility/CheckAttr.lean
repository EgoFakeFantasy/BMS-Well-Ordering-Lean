import Lean.Elab.Tactic.Simp

/-!
# 合法性计算证书扩展点

公共检查器通过两个独立 simp 集消费项目定义项与公式的计算证书。
属性必须在使用它们的模块之前完成初始化，因此单独置于前置模块。
-/

/-- 项目定义项的计算证书扩展点。 -/
register_simp_attr term_check

/-- 项目定义公式的计算证书扩展点。 -/
register_simp_attr formula_check
