import BMSConstructibleBridge.PowerlessCanonicalCodedCoverageSyntax

/-! # 原完整覆盖矩阵定义的局部规范比较关系

纯隶属 ℒ。用右端对象的实际规范覆盖及其中的比较值定义左小于右。
见证、编码和图共用同一存在块；这里不给存在或绝对性加新公理。
后续读数必须认同原全局比较，不能单凭此 AST 替换原程序算子。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalCodedEdgeSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def edge_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (B ω P₀ x y : carrier_l 𝒩) : Prop :=
  ∃ a X A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P,
    PowerlessCanonicalCodedCoverageSyntax.point_l (𝒩 := 𝒩)
      B ω y P₀ a X A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P ∧
    member_l 𝒩 x X ∧ value_l (ℳ := 𝒩) P x y

private abbrev up₂₀ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (t))))))))))))))))))))

/-- 原完整包覆盖右端；左端属于同一层并由同一比较图给出先后。 -/
def edge_m {Γ Δ : SortContext ℒ} (B ω P₀ x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
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
  let X := .bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))
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
  .conj (PowerlessCanonicalCodedCoverageSyntax.point_m
    (up₂₀ B) (up₂₀ ω) (up₂₀ y) (up₂₀ P₀) a X A U D f e t₁ t₂ t₃ t₄ Pair N Valid V Q G g R P) <|
      .conj (member_m (up₂₀ x) X) (value_m P (up₂₀ x) (up₂₀ y))

theorem edge_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (B ω P₀ x y : Term ℒ Γ Δ .set) :
    (edge_m B ω P₀ x y).satisfies η ↔
      edge_l (B.eval η) (ω.eval η) (P₀.eval η) (x.eval η) (y.eval η) := by
  simp only [edge_m, edge_l, Formula.satisfies,
    PowerlessCanonicalCodedCoverageSyntax.point_formula_l hExt, value_formula_l, member_m,
    Arguments.eval, up₂₀, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalCodedEdgeSyntax
