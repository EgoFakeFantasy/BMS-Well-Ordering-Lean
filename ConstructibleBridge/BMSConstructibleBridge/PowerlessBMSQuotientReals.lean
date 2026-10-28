import BMSConstructibleBridge.PowerlessBMSQuotientCoding

/-!
# 图商自然数子集与原模型实数的双向精确对应

原模型的理解直接构造任意纯集合公式在全部内部数上的迹。反向每个实数已有
商子集代表；双侧外延性给出唯一性。不在 Type 中抽取代表或实数选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientReals

open Logic FirstOrder SecondOrderSyntax SecondOrderInterpretation
open PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 任意纯集合公式的内部自然数迹是原模型中的实际实数。 -/
theorem comprehension_l (C : source_coding_l hℳ)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) :
    ∃ X : SecondOrderModel.set_l ℳ, ∀ n,
      SecondOrderModel.mem_l n X ↔ φ.satisfies (η.pushFree (numberCode_l C n).val) := by
  obtain ⟨ρ, τ, hη⟩ := source_surj_l hℳ η
  let ξ := (target_l ρ τ).pushFree C.less
  obtain ⟨X, hX⟩ := SecondOrderModel.comprehension_l hℳ (GraphTranslation.form_m φ)
    (GraphTranslation.form_pure_m φ) ξ
  refine ⟨X, fun n => (hX n).trans ?_⟩
  have h := form_l hℳ φ ρ
    (push_l (SecondOrderNaturalGraph.code_l hℳ C.less C.less_spec n) τ)
  have henv : source_l hℳ ρ
      (push_l (SecondOrderNaturalGraph.code_l hℳ C.less C.less_spec n) τ) =
      η.pushFree (numberCode_l C n).val := by
    rw [← hη]
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v <;> rfl
  rw [henv] at h
  exact h

/-- 任意商内 ω 子集都有一个原模型实数读取其全部内部成员。 -/
theorem trace_exists_l (C : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega) :
    ∃ X : SecondOrderModel.set_l ℳ, setRel_l C A X := by
  let φ : Formula ℒ [] [.set, .set] :=
    .rel .membership (.cons (.fvar .here) (.cons (.fvar (.there .here)) .nil))
  obtain ⟨X, hX⟩ := comprehension_l C φ
    ((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree A.val)
  exact ⟨X, fun n => (hX n).symm⟩

theorem trace_unique_l (C : source_coding_l hℳ)
    {A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega}
    {X Y : SecondOrderModel.set_l ℳ} (hX : setRel_l C A X) (hY : setRel_l C A Y) : X = Y :=
  SecondOrderModel.ext_l hℳ X Y (fun n => (hX n).symm.trans (hY n))

theorem representative_unique_l (C : source_coding_l hℳ)
    {A B : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega}
    {X : SecondOrderModel.set_l ℳ} (hA : setRel_l C A X) (hB : setRel_l C B X) : A = B := by
  apply Subtype.ext
  apply SecondOrderQuotient.ext_l hℳ
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, A.property x hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    rw [← hn'] at hx ⊢
    exact (hB n).mpr ((hA n).mp hx)
  · intro hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, B.property x hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    rw [← hn'] at hx ⊢
    exact (hA n).mpr ((hB n).mp hx)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientReals
