import BMSConstructibleBridge.PowerlessBMSQuotientMultiplication
import BMSConstructibleBridge.SecondOrderAxioms

/-!
# 商算术存在性与唯一性的 Z₂ 对象证明

源语言是仅含隶属的 ℒ，目标是原二阶算术签名及 `theory_m`；所有闭句均使用
原 `GraphTranslation.form_m`。两个运算各有存在性与唯一性闭句，并在原
`Derives theory_m [] φ` 中交付。回传使用已验证的全公式图商解释和固定签名
强完备性：语义输入覆盖 Type 0 的全部原理论模型，无 β 模型或标准性限制。
这是算术辅助定理，仍不是固定高度 BMS 良序句的对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientArithmeticDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SecondOrderQuotient.structure_l SetTheory.signature

universe u

inductive operation_m where
  | addition
  | multiplication

/-- 始终使用原加法迭代图与原乘法自映射迭代图。 -/
def graph_m (k : operation_m) {Γ Δ : SortContext ℒ}
    (ω e a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  match k with
  | .addition => PowerlessAdditionSyntax.addition_m ω e a b c
  | .multiplication => PowerlessMultiplication.multiplication_m ω e a b c

def graph_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (k : operation_m) (ω e a b c : carrier_l ℳ) : Prop :=
  match k with
  | .addition => PowerlessAddition.addition_l ω e a b c
  | .multiplication => PowerlessMultiplication.multiplication_l ω e a b c

theorem graph_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (k : operation_m) {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e a b c : Term ℒ Γ Δ .set) :
    (graph_m k ω e a b c).satisfies η ↔
      graph_l k (ω.eval η) (e.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  cases k
  · exact PowerlessAdditionSyntax.addition_formula_l η ω e a b c
  · exact PowerlessMultiplication.multiplication_formula_l η ω e a b c

private def zero_m {Γ Δ : SortContext ℒ} (e : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.neg (member_m (.bvar .here) (e.weakenBound SetTheory.SetSort.set)))

private theorem zero_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (e : Term ℒ Γ Δ .set) :
    (zero_m e).satisfies η ↔ PowerlessNatural.zero_l (e.eval η) := by
  simp only [zero_m, Formula.satisfies, member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 对任意内部 ω、零和两个内部自然数，运算有属于同一 ω 的输出。 -/
def total_m (k : operation_m) : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let ω : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let e : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there .here))
    let a : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there .here)
    let b : Term ℒ [.set, .set, .set, .set] [] .set := .bvar .here
    .imp (.conj (SecondOrderOmegaSyntax.omega_m ω)
      (.conj (zero_m e) (.conj (member_m a ω) (member_m b ω))))
      (.existsE .set (.conj (member_m (.bvar .here) (ω.weakenBound SetTheory.SetSort.set))
        (graph_m k (ω.weakenBound SetTheory.SetSort.set) (e.weakenBound SetTheory.SetSort.set)
          (a.weakenBound SetTheory.SetSort.set) (b.weakenBound SetTheory.SetSort.set) (.bvar .here))))

/-- 输出唯一性不把输出属于 ω 作为额外前提。 -/
def functional_m (k : operation_m) : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
  .forallE .set <| .forallE .set <|
    let ω : Term ℒ [.set, .set, .set, .set, .set, .set] [] .set :=
      .bvar (.there (.there (.there (.there (.there .here)))))
    let e : Term ℒ [.set, .set, .set, .set, .set, .set] [] .set :=
      .bvar (.there (.there (.there (.there .here))))
    let a : Term ℒ [.set, .set, .set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let b : Term ℒ [.set, .set, .set, .set, .set, .set] [] .set := .bvar (.there (.there .here))
    let c : Term ℒ [.set, .set, .set, .set, .set, .set] [] .set := .bvar (.there .here)
    let d : Term ℒ [.set, .set, .set, .set, .set, .set] [] .set := .bvar .here
    .imp (.conj (SecondOrderOmegaSyntax.omega_m ω) (.conj (zero_m e)
      (.conj (member_m b ω) (.conj (graph_m k ω e a b c) (graph_m k ω e a b d))))) (.equal c d)

variable {M : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hM

private theorem normalize_l (C : source_coding_l hM) {ω e : SecondOrderQuotient.type_l hM}
    (hω : SecondOrderOmega.omega_l hM ω) (he : PowerlessNatural.zero_l (ℳ := quotient_l) e) :
    ω = C.omega ∧ e = (numberCode_l C (SecondOrderModel.zero_l M)).val := by
  refine ⟨SecondOrderOmega.unique_l hM hω C.omega_spec, ?_⟩
  apply SecondOrderQuotient.ext_l hM
  intro x
  exact iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l C x)

theorem total_models_l (hℳ : Theory.Models M SecondOrderArithmetic.theory_m) (k : operation_m) :
    (total_m k).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  simp only [total_m, Formula.TrueIn, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    zero_formula_l, graph_formula_l, member_m, Arguments.eval]
  change ∀ ω e a b : SecondOrderQuotient.type_l hℳ,
    (SecondOrderOmega.omega_l hℳ ω ∧ PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e ∧
      member_l (SecondOrderQuotient.structure_l hℳ) a ω ∧ member_l (SecondOrderQuotient.structure_l hℳ) b ω) →
    ∃ c, member_l (SecondOrderQuotient.structure_l hℳ) c ω ∧ graph_l (ℳ := SecondOrderQuotient.structure_l hℳ) k ω e a b c
  intro ω e a b ⟨hω, he, ha, hb⟩
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain ⟨rfl, rfl⟩ := normalize_l C hω he
  obtain ⟨p, hp⟩ := numberCode_surjective_l C ⟨a, ha⟩
  obtain ⟨q, hq⟩ := numberCode_surjective_l C ⟨b, hb⟩
  have hp' : (numberCode_l C p).val = a := congrArg Subtype.val hp
  have hq' : (numberCode_l C q).val = b := congrArg Subtype.val hq
  rw [← hp', ← hq']
  cases k
  · exact ⟨_, (numberCode_l C (SecondOrderModel.add_l p q)).property,
      PowerlessBMSQuotientArithmetic.additionInstance_l C p q⟩
  · exact ⟨_, (numberCode_l C (SecondOrderModel.mul_l p q)).property,
      PowerlessBMSQuotientMultiplication.multiplicationInstance_l C p q⟩

theorem functional_models_l (hℳ : Theory.Models M SecondOrderArithmetic.theory_m) (k : operation_m) :
    (functional_m k).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  simp only [functional_m, Formula.TrueIn, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    zero_formula_l, graph_formula_l, member_m, Arguments.eval]
  change ∀ ω e a b c d : SecondOrderQuotient.type_l hℳ,
    (SecondOrderOmega.omega_l hℳ ω ∧ PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e ∧
      member_l (SecondOrderQuotient.structure_l hℳ) b ω ∧
      graph_l (ℳ := SecondOrderQuotient.structure_l hℳ) k ω e a b c ∧
      graph_l (ℳ := SecondOrderQuotient.structure_l hℳ) k ω e a b d) → c = d
  intro ω e a b c d ⟨hω, he, hb, hc, hd⟩
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain ⟨rfl, rfl⟩ := normalize_l C hω he
  cases k
  · exact PowerlessBMSQuotientRecursion.addition_unique_l C hb hc hd
  · exact PowerlessBMSQuotientMultiplication.multiplication_unique_l C hb hc hd

/-- 加法、乘法存在性各自的正式 Z₂ 推导。 -/
theorem total_derives_m (k : operation_m) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (total_m k)) :=
  SecondOrderAxioms.interpretation_m (total_m k) (fun _ hℳ => total_models_l hℳ k)

/-- 加法、乘法唯一性各自的正式 Z₂ 推导。 -/
theorem functional_derives_m (k : operation_m) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (functional_m k)) :=
  SecondOrderAxioms.interpretation_m (functional_m k) (fun _ hℳ => functional_models_l hℳ k)

#print axioms total_derives_m
#print axioms functional_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientArithmeticDerives
