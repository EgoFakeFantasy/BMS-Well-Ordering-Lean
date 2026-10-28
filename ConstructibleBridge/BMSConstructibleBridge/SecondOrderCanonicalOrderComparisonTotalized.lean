import BMSConstructibleBridge.SecondOrderCanonicalOrderComparisonSyntax
import YesMetaZFC.Automation.TotalizedGraph

/-! # 后继比较行的无输出缺省分支

复用上游部分图总化：原步骤有输出时逐输出保持，无输出时返回零对象。
任意旧序输入上的单值性由实际规范步骤证明，而不是加入额外守卫。
本模块提供阶段组件；尚未装配完整阶段递归或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparisonTotalized

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev parameters : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

private def body_m : Formula ℒ [] (.set :: parameters) :=
  SecondOrderCanonicalOrderComparisonSyntax.output_m
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
    (.fvar .here)

private def fallback_m : Formula ℒ [] (.set :: parameters) :=
  .equal (.fvar .here) (.fvar (.there (.there (.there (.there .here)))))

def template_m : Formula ℒ [] (.set :: parameters) :=
  _root_.YesMetaZFC.Automation.TotalizedGraph.formula body_m fallback_m

private def arguments_m {Γ Δ : SortContext ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f W : Term ℒ Γ Δ .set) : Arguments ℒ Γ Δ (.set :: parameters) :=
  .cons W (.cons ω (.cons A (.cons P (.cons e (.cons t₁ (.cons t₂ (.cons t₃
      (.cons Pair (.cons Valid (.cons D (.cons f .nil)))))))))))

def output_m {Γ Δ : SortContext ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  _root_.YesMetaZFC.Automation.RelationalTranslation.applyTemplate template_m
    (arguments_m ω A P e t₁ t₂ t₃ Pair Valid D f W)

def output_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f W : carrier_l 𝒩) : Prop :=
  SecondOrderCanonicalOrderComparisonSyntax.output_l ω A P e t₁ t₂ t₃ Pair Valid D f W ∨
    ((¬ ∃ X, SecondOrderCanonicalOrderComparisonSyntax.output_l ω A P e t₁ t₂ t₃ Pair Valid D f X) ∧ W = e)

private def env_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f : carrier_l 𝒩) : Env 𝒩 [] parameters :=
  let η₀ := ((Env.empty.pushFree f).pushFree D).pushFree Valid
  let η₁ := ((η₀.pushFree Pair).pushFree t₃).pushFree t₂
  ((((η₁.pushFree t₁).pushFree e).pushFree P).pushFree A).pushFree ω

private theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f W : carrier_l 𝒩) :
    body_m.satisfies ((env_l ω A P e t₁ t₂ t₃ Pair Valid D f).pushFree W) ↔
      SecondOrderCanonicalOrderComparisonSyntax.output_l ω A P e t₁ t₂ t₃ Pair Valid D f W := by
  simp only [body_m, SecondOrderCanonicalOrderComparisonSyntax.output_formula_l, Term.eval, env_l,
    Env.pushFree_here, Env.pushFree_there]

theorem template_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f W : carrier_l 𝒩) :
    template_m.satisfies ((env_l ω A P e t₁ t₂ t₃ Pair Valid D f).pushFree W) ↔
      output_l ω A P e t₁ t₂ t₃ Pair Valid D f W := by
  rw [template_m, _root_.YesMetaZFC.Automation.TotalizedGraph.satisfies]
  simp only [body_formula_l]
  simp only [fallback_m, Formula.satisfies, Term.eval, env_l, output_l,
    Env.pushFree_here, Env.pushFree_there]

theorem output_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A P e t₁ t₂ t₃ Pair Valid D f W : Term ℒ Γ Δ .set) :
    (output_m ω A P e t₁ t₂ t₃ Pair Valid D f W).satisfies η ↔
      output_l (ω.eval η) (A.eval η) (P.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (D.eval η) (f.eval η) (W.eval η) := by
  rw [output_m, _root_.YesMetaZFC.Automation.RelationalTranslation.applyTemplate_satisfies]
  have hEnv : _root_.YesMetaZFC.Automation.RelationalTranslation.templateEnv
      ((arguments_m ω A P e t₁ t₂ t₃ Pair Valid D f W).eval η) =
      (env_l (ω.eval η) (A.eval η) (P.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (Pair.eval η) (Valid.eval η) (D.eval η) (f.eval η)).pushFree (W.eval η) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      rcases v with _ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | (_ | v)))))))))))
      all_goals first | rfl | cases v
  rw [hEnv]
  exact template_formula_l (ω.eval η) (A.eval η) (P.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
    (t₃.eval η) (Pair.eval η) (Valid.eval η) (D.eval η) (f.eval η) (W.eval η)

/-- 有原输出时，缺省分支不改变任何比较位。 -/
theorem agrees_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A P e t₁ t₂ t₃ Pair Valid D f : carrier_l 𝒩}
    (hExists : ∃ X, SecondOrderCanonicalOrderComparisonSyntax.output_l ω A P e t₁ t₂ t₃ Pair Valid D f X)
    (W : carrier_l 𝒩) : output_l ω A P e t₁ t₂ t₃ Pair Valid D f W ↔
      SecondOrderCanonicalOrderComparisonSyntax.output_l ω A P e t₁ t₂ t₃ Pair Valid D f W := by
  have h := _root_.YesMetaZFC.Automation.TotalizedGraph.agrees
    (env_l ω A P e t₁ t₂ t₃ Pair Valid D f) body_m fallback_m
    (hExists.imp fun X hX => (body_formula_l ω A P e t₁ t₂ t₃ Pair Valid D f X).mpr hX) W
  exact (template_formula_l ω A P e t₁ t₂ t₃ Pair Valid D f W).symm.trans
    (h.trans (body_formula_l ω A P e t₁ t₂ t₃ Pair Valid D f W))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem functional_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D f : carrier_l 𝒩)
    (hUnique : ∀ X Y, SecondOrderCanonicalOrderComparisonSyntax.output_l ω A P e t₁ t₂ t₃ Pair Valid D f X →
      SecondOrderCanonicalOrderComparisonSyntax.output_l ω A P e t₁ t₂ t₃ Pair Valid D f Y → X = Y) :
    ∃! W, output_l ω A P e t₁ t₂ t₃ Pair Valid D f W := by
  let η := env_l ω A P e t₁ t₂ t₃ Pair Valid D f
  have hBody : ∀ X Y, body_m.satisfies (η.pushFree X) → body_m.satisfies (η.pushFree Y) → X = Y := by
    intro X Y hX hY
    exact hUnique X Y ((body_formula_l ω A P e t₁ t₂ t₃ Pair Valid D f X).mp hX)
      ((body_formula_l ω A P e t₁ t₂ t₃ Pair Valid D f Y).mp hY)
  have hFallback : ∃ X, fallback_m.satisfies (η.pushFree X) ∧
      ∀ Y, fallback_m.satisfies (η.pushFree Y) → Y = X := by
    simp only [fallback_m, Formula.satisfies, Term.eval, η, env_l,
      Env.pushFree_here, Env.pushFree_there]
    exact ⟨e, rfl, fun _ h => h⟩
  obtain ⟨W, hW, hOnly⟩ := _root_.YesMetaZFC.Automation.TotalizedGraph.functional η body_m fallback_m hBody hFallback
  exact ⟨W, (template_formula_l ω A P e t₁ t₂ t₃ Pair Valid D f W).mp hW,
    fun X hX => hOnly X ((template_formula_l ω A P e t₁ t₂ t₃ Pair Valid D f X).mpr hX)⟩

/-- 编码包固定后，任意旧序参数都有唯一的总化行。 -/
theorem exists_unique_l (K : source_coding_l hℳ)
    {f A P t₁ t₂ t₃ Pair Valid D : SecondOrderQuotient.type_l hℳ}
    (ht₁ : t₁ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 1))
    (ht₂ : t₂ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 2))
    (ht₃ : t₃ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 3))
    (hPairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N) :
    ∃! W : SecondOrderQuotient.type_l hℳ,
      output_l (𝒩 := 𝒱) K.omega A P (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f W := by
  apply functional_l (𝒩 := 𝒱) K.omega A P (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f
  intro X Y hX hY
  exact SecondOrderCanonicalOrderComparisonSyntax.unique_l
    K ht₁ ht₂ ht₃ hPairMap hPair hV hValid hX hY

/-- 缺省零行也是真正的 ω 子集，不返回任意集合垃圾。 -/
theorem guard_l (K : source_coding_l hℳ)
    {A P t₁ t₂ t₃ Pair Valid D f W : SecondOrderQuotient.type_l hℳ}
    (h : output_l (𝒩 := 𝒱) K.omega A P (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f W) :
    subset_l (ℳ := 𝒱) W K.omega := by
  rcases h with ⟨_, _, hEncoded⟩ | ⟨_, rfl⟩
  · exact SecondOrderComparisonEncodeSyntax.guard_l hEncoded
  · intro x hx
    exact False.elim (PowerlessBMSQuotientSuccessor.zero_l K x hx)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparisonTotalized
