import BMSConstructibleBridge.PowerlessRelativeClassValidity

/-! # 合法性图的纯集合规格与类内读数

对象公式用实际有限证书查询指定整张 F 图，不把原二阶实数 V 当作类参数。
有界绝对性把全部类内输入接回已验证的原商图规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValiditySpecification

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N T t₁ t₂ t₃ F : carrier_l 𝒩) : Prop :=
  ∀ c l, value_l F c l ↔ PowerlessFormulaValidityBounded.query_l ω e N T t₁ t₂ t₃ c l

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def spec_m {Γ Δ : SortContext ℒ} (ω e N T t₁ t₂ t₃ F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .forallE .set <| .forallE .set <| .iff
    (SecondOrderObjectSyntax.value_m (w F) (.bvar (.there .here)) (.bvar .here))
    (PowerlessFormulaValidityBounded.query_m (w ω) (w e) (w N) (w T) (w t₁) (w t₂) (w t₃)
      (.bvar (.there .here)) (.bvar .here))

theorem spec_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N T t₁ t₂ t₃ F : Term ℒ Γ Δ .set) :
    (spec_m ω e N T t₁ t₂ t₃ F).satisfies η ↔
      spec_l (ω.eval η) (e.eval η) (N.eval η) (T.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (F.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, value_formula_l,
    PowerlessFormulaValidityBounded.query_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem query_absolute_l (ω e N T t₁ t₂ t₃ c l : type_l hℳ B) :
    PowerlessFormulaValidityBounded.query_l (𝒩 := structure_l hℳ B hBase) ω e N T t₁ t₂ t₃ c l ↔
      PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val e.val N.val T.val t₁.val t₂.val t₃.val c.val l.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    (((((((((Env.empty).pushFree l).pushFree c).pushFree t₃).pushFree t₂).pushFree t₁).pushFree T).pushFree N).pushFree e).pushFree ω
  have h := PowerlessRelativeClassBounded.formula_l (hBase := hBase)
    (PowerlessFormulaValidityBounded.query_delta_l (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) η
  simpa only [PowerlessFormulaValidityBounded.query_formula_l, Term.eval,
    Env.pushFree_here, Env.pushFree_there, PowerlessRelativeClassRelativization.env_l, η] using h

theorem instance_l (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {ω e N T t₁ t₂ t₃ F : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    (he : e.val = PowerlessFormulaValidityReading.code_l K (SecondOrderModel.zero_l ℳ))
    (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l) :
    spec_l (𝒩 := structure_l hℳ B hBase) ω e N T t₁ t₂ t₃ F := by
  intro c l
  exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c l).trans
    ((hF c.val l.val).trans ((PowerlessRelativeClassValidity.query_iff_l K hω hωEq he ht hT hSpec hV hN c.val l.val).symm.trans
      (query_absolute_l (hBase := hBase) ω e N T t₁ t₂ t₃ c l).symm))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValiditySpecification
