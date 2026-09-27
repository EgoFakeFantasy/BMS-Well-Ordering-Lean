import BMSConstructibleBridge.PowerlessArithmeticOrder
import BMSConstructibleBridge.PowerlessArithmeticPrograms
import BMSConstructibleBridge.SecondOrderProgramUniformParentOrder

/-!
# 原统一祖先程序的纯集合查询

查询输入严格保持 pair (pair (pair 数组 行) 目标列) 候选列，真值为原成员程序输出非零。
公式正文直接调用原编译器，不引入宿主传递闭包、替代父关系或额外关系符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSAncestor

open Logic FirstOrder ThirdOrderSemantics PowerlessArithmeticTerms

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

def program_m : PrimitiveProgram.code_m :=
  SecondOrderProgramAncestorMembership.member_m SecondOrderProgramUniformParent.parent_m

/-- 自由槽依次为数组、行、目标列、候选列；三次配对均使用原算术公式。 -/
def source_m : Formula SecondOrderSyntax.signature_m [] [.num, .num, .num, .num] :=
  .existsE .num (.existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar .here) (.fvar (.there .here)) (.bvar (.there (.there .here))))
    (.conj (PrimitiveFormulas.pair_m (.bvar (.there (.there .here)))
      (.fvar (.there (.there .here))) (.bvar (.there .here)))
      (.conj (PrimitiveFormulas.pair_m (.bvar (.there .here))
        (.fvar (.there (.there (.there .here)))) (.bvar .here))
        (.neg (PrimitiveProgram.form_m program_m (.bvar .here)
          (Term.app (σ := SecondOrderSyntax.signature_m) .zero .nil))))))))

def environment_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (x r t i : SecondOrderModel.num_l 𝒩) : Env 𝒩 [] [.num, .num, .num, .num] :=
  ((((Env.empty (M := 𝒩)).pushFree i).pushFree t).pushFree r).pushFree x

theorem source_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {X : SecondOrderModel.set_l 𝒩}
    (hX : SecondOrderProgramSemantics.graph_semantics_l (PrimitiveProgram.graph_m program_m) X)
    (x r t i : SecondOrderModel.num_l 𝒩) : source_m.satisfies (environment_l x r t i) ↔
      ¬SecondOrderPairing.relation_l X
        (SecondOrderPairing.value_l (SecondOrderPairing.value_l (SecondOrderPairing.value_l x r) t) i)
        (SecondOrderModel.zero_l 𝒩) := by
  have h₁ {Γ Δ : SortContext SecondOrderSyntax.signature_m} (η : Env 𝒩 Γ Δ)
      (s t : Term SecondOrderSyntax.signature_m Γ Δ .num) :
      (PrimitiveProgram.form_m program_m s t).satisfies η ↔
        SecondOrderPairing.relation_l X (s.eval η) (t.eval η) := hX η s t
  simp only [source_m, Formula.satisfies, SecondOrderPairing.formula_l, h₁]
  change (∃ a b c : SecondOrderModel.num_l 𝒩, SecondOrderPairing.value_l x r = a ∧
    SecondOrderPairing.value_l a t = b ∧ SecondOrderPairing.value_l b i = c ∧
      ¬SecondOrderPairing.relation_l X c (SecondOrderModel.zero_l 𝒩)) ↔ _
  constructor
  · rintro ⟨a, b, c, rfl, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, _, _, rfl, rfl, rfl, h⟩

def ancestor_m {Γ Δ : SortContext ℒ} (ω e x r t i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let τ : assignment_m [.num, .num, .num, .num] Γ Δ := fun v => match v with
    | .here => x
    | .there .here => r
    | .there (.there .here) => t
    | .there (.there (.there .here)) => i
  PowerlessArithmeticTranslation.formula_m ω e
    (fun {s} (v : Variable ([] : SortContext SecondOrderSyntax.signature_m) s) => nomatch v) τ source_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 实际原祖先真值；参数仍在同一内部 ω 中。 -/
def ancestor_l (x r t i : PowerlessArithmetic.num_l ω) : Prop :=
  source_m.satisfies (@environment_l 𝒩 x r t i)

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (w z a b c d : Term ℒ Γ Δ .set)
    (x r t i : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (ha : a.eval η = x.val)
    (hb : b.eval η = r.val) (hc : c.eval η = t.val) (hd : d.eval η = i.val) :
    (ancestor_m w z a b c d).satisfies η ↔ ancestor_l (he := he) (h₀ := h₀) (F := F) x r t i := by
  unfold ancestor_m ancestor_l
  apply PowerlessArithmeticTranslation.formula_l hℳ hω (environment_l x r t i) η w z _ _ hw hz
  · intro s v
    nomatch v
  · intro s v
    match s, v with
    | .num, .here => exact ha
    | .num, .there .here => exact hb
    | .num, .there (.there .here) => exact hc
    | .num, .there (.there (.there .here)) => exact hd

theorem graph_l {X : PowerlessArithmetic.set_l ω}
    (hX : SecondOrderProgramSemantics.graph_semantics_l (ℳ := 𝒩) (PrimitiveProgram.graph_m program_m) X)
    (x r t i : PowerlessArithmetic.num_l ω) :
    ancestor_l (he := he) (h₀ := h₀) (F := F) x r t i ↔
      ¬SecondOrderPairing.relation_l (ℳ := 𝒩) X
        (SecondOrderPairing.value_l (SecondOrderPairing.value_l (SecondOrderPairing.value_l x r) t) i)
        (SecondOrderModel.zero_l 𝒩) :=
  source_formula_l hX x r t i

/-- 原祖先程序的真值推出实际内部列严格向左，非外部链的额外前提。 -/
theorem bound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {x r t i : PowerlessArithmetic.num_l ω}
    (h : ancestor_l (he := he) (h₀ := h₀) (F := F) x r t i) : member_l ℳ i.val t.val := by
  have h𝒩 := PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)
  obtain ⟨X, _, hX⟩ := SecondOrderProgramTotality.graph_total_l h𝒩 program_m
  exact (PowerlessArithmeticOrder.lt_l hℳ hω (he := he) (h₀ := h₀) (F := F) i t).mp
    (SecondOrderProgramUniformParentOrder.member_lt_l h𝒩 hX ((graph_l hX x r t i).mp h))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSAncestor
