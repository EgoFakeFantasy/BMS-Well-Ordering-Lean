import BMSConstructibleBridge.PowerlessCodedHistoryCoverageSyntax
import BMSConstructibleBridge.PowerlessCanonicalOrderEquations

/-! # 包含实际规范比较图的完整局部覆盖矩阵

纯隶属 ℒ 中保留原十七见证检查器包，增加同一阶段域上的比较函数图、
实际陪域和选定比较值。无枚举递归方程使用原 Uniform 后继；不把
完整计数式层次公式认作绝对，不添加类存在或良序公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalCodedCoverageSyntax

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (B ω x P₀ a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P : carrier_l 𝒩) : Prop :=
  PowerlessCodedHistoryCoverageSyntax.point_l (𝒩 := 𝒩)
    B ω x a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G ∧
  map_l (ℳ := 𝒩) g A R ∧
  PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒩)
    ω e t₁ t₂ t₃ Pair Valid B P₀ f g ∧ value_l (ℳ := 𝒩) g a P

def point_m {Γ Δ : SortContext ℒ}
    (B ω x P₀ a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P :
      Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessCodedHistoryCoverageSyntax.point_m
    B ω x a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G) <|
  .conj (SecondOrderObjectSyntax.map_m g A R) <|
  .conj (PowerlessCanonicalOrderEquations.formula_m
    ω e t₁ t₂ t₃ Pair Valid B P₀ f g) (SecondOrderObjectSyntax.value_m g a P)

theorem point_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (B ω x P₀ a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P :
      Term ℒ Γ Δ .set) :
    (point_m B ω x P₀ a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P).satisfies η ↔
      point_l (B.eval η) (ω.eval η) (x.eval η) (P₀.eval η) (a.eval η) (y.eval η)
        (A.eval η) (U.eval η) (D.eval η) (f.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (t₄.eval η) (Pair.eval η) (N.eval η) (Valid.eval η) (V.eval η)
        (Q.eval η) (G.eval η) (g.eval η) (R.eval η) (P.eval η) := by
  simp only [point_m, point_l, Formula.satisfies,
    PowerlessCodedHistoryCoverageSyntax.point_formula_l hExt, map_formula_l,
    PowerlessCanonicalOrderEquations.formula_l, value_formula_l]

def statement_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (B ω x P₀ : carrier_l 𝒩) : Prop :=
  ∃ a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P, point_l B ω x P₀ a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P

private abbrev up₂₀ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (t))))))))))))))))))))

/-- 原二十个见证在同一个存在块中，输入 B、ω、x、P₀ 保持不变。 -/
def result_m {Γ Δ : SortContext ℒ} (B ω x P₀ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  .existsE .set <|
  let a : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))))
  let y := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))
  let A := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))
  let U := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))
  let D := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))
  let f := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))
  let e := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))
  let t₁ := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
  let t₂ := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
  let t₃ := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
  let t₄ := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
  let Pair := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
  let N := .bvar (.there (.there (.there (.there (.there (.there (.there (.here))))))))
  let Valid := .bvar (.there (.there (.there (.there (.there (.there (.here)))))))
  let V := .bvar (.there (.there (.there (.there (.there (.here))))))
  let Q := .bvar (.there (.there (.there (.there (.here)))))
  let G := .bvar (.there (.there (.there (.here))))
  let g := .bvar (.there (.there (.here)))
  let R := .bvar (.there (.here))
  let P := .bvar (.here)
  point_m (up₂₀ B) (up₂₀ ω) (up₂₀ x) (up₂₀ P₀) a y A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P

theorem result_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (B ω x P₀ : Term ℒ Γ Δ .set) :
    (result_m B ω x P₀).satisfies η ↔ statement_l (B.eval η) (ω.eval η) (x.eval η) (P₀.eval η) := by
  simp only [result_m, statement_l, Formula.satisfies, point_formula_l hExt, up₂₀, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalCodedCoverageSyntax
