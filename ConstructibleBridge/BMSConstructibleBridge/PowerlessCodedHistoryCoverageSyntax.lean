import BMSConstructibleBridge.PowerlessMemberSatisfactionFunctionAbsolute
import BMSConstructibleBridge.PowerlessMemberDefFunctionAbsolute
import BMSConstructibleBridge.PowerlessMemberOrdinalAbsolute
import BMSConstructibleBridge.PowerlessLegacyNumericSyntax
import BMSConstructibleBridge.PowerlessSatisfactionExistenceSyntax
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 共同域可捕获的完整局部前史覆盖矩阵

纯隶属存在式只以 B、ω、x 为自由参数，不含外部 W 或 Ω。实际
前史见证、完整静态包、Sat／Def 函数图、旧数字翻译资格、真实序数
和有限赋值覆盖、母界传递性及操作闭包在同一组存在见证上组合。
完整图、覆盖及闭包保留无界量词，
本模块不把整包分类为 Δ₀，也不单凭 AST 宣称已取得源模型或终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedHistoryCoverageSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 覆盖全部实际有限函数，不缩为给定有界证书集中的检查。 -/
def finite_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω U : carrier_l 𝒩) : Prop :=
  ∀ z, member_l 𝒩 z U → ∀ r,
    PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩) ω z r → member_l 𝒩 r U

def finite_m {Γ Δ : SortContext ℒ} (ω U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  StabilityFrame.membershipLevyBound.boundedForall U <| .forallE .set <| .imp
    (PowerlessFiniteSequencesSyntax.sequence_m (up (up ω)) (.bvar (.there .here)) (.bvar .here))
    (member_m (.bvar .here) (up (up U)))

theorem finite_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω U : Term ℒ Γ Δ .set) :
    (finite_m ω U).satisfies η ↔ finite_l (ω.eval η) (U.eval η) := by
  simp only [finite_m, finite_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, StabilityFrame.membershipLevyBound, Formula.satisfies,
    PowerlessFiniteSequencesSyntax.sequence_formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def point_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : carrier_l 𝒩) : Prop :=
  member_l 𝒩 a A ∧ value_l (ℳ := 𝒩) f a y ∧ member_l 𝒩 x y ∧
  member_l 𝒩 B U ∧ member_l 𝒩 ω U ∧
  PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩) ω e t₁ t₂ t₃ P N F ∧
  PowerlessMemberSatisfactionFunctionAbsolute.spec_l (𝒩 := 𝒩) ω e t₁ t₂ t₃ P N F U G ∧
  PowerlessMemberDefFunctionAbsolute.spec_l (𝒩 := 𝒩) ω e N Q U G D ∧
  PowerlessLegacyNumericSyntax.spec_l (𝒩 := 𝒩) ω e t₁ t₂ t₃ t₄ P N V Q ∧
  SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩) A ∧
  PowerlessHierarchyLightHistory.holds_l (𝒩 := 𝒩) B D A U f ∧ finite_l ω U ∧
  PowerlessNaturalOrder.transitive_l (ℳ := 𝒩) U ∧
  PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒩) U

def point_m {Γ Δ : SortContext ℒ}
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m a A) <| .conj (value_m f a y) <| .conj (member_m x y) <|
  .conj (member_m B U) <| .conj (member_m ω U) <|
  .conj (PowerlessSatisfactionExistenceSyntax.static_m ω e t₁ t₂ t₃ P N F) <|
  .conj (PowerlessMemberSatisfactionFunctionAbsolute.graph_m ω e t₁ t₂ t₃ P N F U G) <|
  .conj (PowerlessMemberDefFunctionAbsolute.graph_m ω e N Q U G D) <|
  .conj (PowerlessLegacyNumericSyntax.formula_m ω e t₁ t₂ t₃ t₄ P N V Q) <|
  .conj (PowerlessRelativeHierarchySyntax.ordinal_m A) <|
  .conj (PowerlessHierarchyLightHistory.formula_m B D A U f) <|
  .conj (finite_m ω U) <| .conj (PowerlessNaturalOrder.transitive_m U)
    (PowerlessRelativeFiniteHullAssignments.closed_m U)

theorem point_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G : Term ℒ Γ Δ .set) :
    (point_m B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G).satisfies η ↔
      point_l (B.eval η) (ω.eval η) (x.eval η) (a.eval η) (y.eval η) (A.eval η)
        (U.eval η) (D.eval η) (f.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (t₄.eval η) (P.eval η) (N.eval η) (F.eval η)
        (V.eval η) (Q.eval η) (G.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, value_formula_l,
    PowerlessSatisfactionExistenceSyntax.static_formula_l,
    PowerlessMemberSatisfactionFunctionAbsolute.graph_formula_l,
    PowerlessMemberDefFunctionAbsolute.graph_formula_l, PowerlessLegacyNumericSyntax.formula_l,
    PowerlessMemberOrdinalAbsolute.formula_l hExt,
    PowerlessHierarchyLightHistory.formula_l, finite_formula_l,
    PowerlessNaturalOrder.transitive_formula_l, PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    member_m, Arguments.eval]
  rfl

def statement_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (B ω x : carrier_l 𝒩) : Prop :=
  ∃ a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G,
    point_l B ω x a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G

private abbrev up₁₇ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up (up t))))))))))))))))

/-- 十七个见证绑定在同一存在块；B、ω、x 保持原自由参数。 -/
def result_m {Γ Δ : SortContext ℒ} (B ω x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
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
  let G : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
  let Q := (.bvar (.there .here))
  let V := (.bvar (.there (.there .here)))
  let F := (.bvar (.there (.there (.there .here))))
  let N := (.bvar (.there (.there (.there (.there .here)))))
  let P := (.bvar (.there (.there (.there (.there (.there .here))))))
  let t₄ := (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
  let t₃ := (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let t₂ := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let t₁ := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  let e := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
  let f := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
  let D := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
  let U := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
  let A := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
  let y := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
  let a := (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))
  point_m (up₁₇ B) (up₁₇ ω) (up₁₇ x) a y A U D f e t₁ t₂ t₃ t₄ P N F V Q G

theorem result_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (B ω x : Term ℒ Γ Δ .set) :
    (result_m B ω x).satisfies η ↔ statement_l (B.eval η) (ω.eval η) (x.eval η) := by
  simp only [result_m, statement_l, Formula.satisfies, point_formula_l hExt, up₁₇, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedHistoryCoverageSyntax
