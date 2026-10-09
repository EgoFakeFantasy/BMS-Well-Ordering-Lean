import BMSConstructibleBridge.PowerlessSatisfactionNormalizedMatrix

/-! # 同一规范 Sat 函数的完整纯隶属读数

保留真实图 G、指定母域 U 和完整编码包。所有 raw 输入和输出都量化，
不把规范矩阵换成仅有求值存在性的断言，也不在非传递子域上预设绝对性。
本模块只给对象公式和其精确语义桥；实际图存在由截断装配取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionFunctionGraph

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def graph_m {Γ Δ : SortContext ℒ} (ω e t₁ t₂ t₃ T N F U G : Term ℒ Γ Δ .set) :
    Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .conj (SecondOrderObjectSyntax.map_m G U U) <|
    .forallE .set <| .forallE .set <|
      .iff (SecondOrderObjectSyntax.value_m (w G) (.bvar (.there .here)) (.bvar .here))
        (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w U)) <|
          .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w U))
            (PowerlessSatisfactionNormalizedMatrix.formula_m (w ω) (.bvar (.there .here))
              (w e) (w N) (w T) (w U) (w U) (w t₁) (w t₂) (w t₃) (w F) (.bvar .here)))

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e t₁ t₂ t₃ T N F U G : Term ℒ Γ Δ .set) :
    (graph_m ω e t₁ t₂ t₃ T N F U G).satisfies η ↔
      map_l (ℳ := 𝒩) (G.eval η) (U.eval η) (U.eval η) ∧
        ∀ a r : carrier_l 𝒩, value_l (ℳ := 𝒩) (G.eval η) a r ↔
          member_l 𝒩 a (U.eval η) ∧ member_l 𝒩 r (U.eval η) ∧
            PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩)
              (ω.eval η) a (e.eval η) (N.eval η) (T.eval η) (U.eval η) (U.eval η)
              (t₁.eval η) (t₂.eval η) (t₃.eval η) (F.eval η) r := by
  simp only [graph_m, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessSatisfactionNormalizedMatrix.formula_l, ThirdOrderSemantics.member_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms graph_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionFunctionGraph
