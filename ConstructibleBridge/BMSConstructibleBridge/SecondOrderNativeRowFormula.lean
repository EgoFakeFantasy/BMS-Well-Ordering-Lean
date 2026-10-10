import BMSConstructibleBridge.SecondOrderRealRowFormula

/-! # 带原阶段数及候选历史实数的逐行公式

自由槽依次是输出实数、内部阶段数、候选历史实数、固定内部数序图及纯参数
的根／图对。历史代表用对象存在量词引入；阶段数用同一实际数序图的根码。
纯正文必须自行给出历史和输出的 ω 子集守卫，不能用迹相同代替代表相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNativeRowFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderInterpretation PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l GraphTranslation.context_m

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution signature_m (.set :: .set :: GraphTranslation.context_m (.set :: .set :: Δ))
      [.num, .set] (.set :: .num :: .set :: .set :: GraphTranslation.context_m Δ)
  | _, .here => .fvar .here
  | _, .there .here => .fvar (.there (.there (.there .here)))
  | _, .there (.there .here) => .fvar (.there .here)
  | _, .there (.there (.there .here)) => .fvar (.there (.there (.there .here)))
  | _, .there (.there (.there (.there .here))) => .bvar .here
  | _, .there (.there (.there (.there (.there .here)))) => .bvar (.there .here)
  | _, .there (.there (.there (.there (.there (.there v))))) => .fvar (.there (.there (.there (.there v))))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Δ)) :
    Formula signature_m [.num, .set] (.set :: .num :: .set :: .set :: GraphTranslation.context_m Δ) :=
  SecondOrderFormulaParameters.formula_m (SecondOrderRealRowFormula.formula_m φ) insert_m

def formula_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Δ)) :
    Formula signature_m [] (.set :: .num :: .set :: .set :: GraphTranslation.context_m Δ) :=
  .existsE .set <| .existsE .num <|
    .conj (GraphTranslation.domain_m (.bvar (.there .here)) (.bvar .here)) <|
      .conj (SecondOrderRealTraceSyntax.formula_m (.fvar (.there (.there (.there .here))))
        (.bvar (.there .here)) (.bvar .here) (.fvar (.there (.there .here)))) (body_m φ)

theorem pure_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Δ)) :
    SecondOrderArithmetic.language_m (formula_m φ) = true := by
  have hBody : SecondOrderArithmetic.language_m (body_m φ) = true := by
    apply SecondOrderFormulaParameters.pure_m _ _ (SecondOrderRealRowFormula.pure_m φ)
    intro s v
    rcases v with _ | (_ | (_ | (_ | (_ | (_ | v)))))
    all_goals first | rfl | cases s <;> rfl
  have hDomain : SecondOrderArithmetic.language_m
      (GraphTranslation.domain_m (Γ := [.num, .set])
        (Δ := .set :: .num :: .set :: .set :: GraphTranslation.context_m Δ) (.bvar (.there .here)) (.bvar .here)) = true :=
    GraphTranslation.domain_pure_m _ _ rfl rfl
  have hTrace : SecondOrderArithmetic.language_m
      (SecondOrderRealTraceSyntax.formula_m (Γ := [.num, .set])
        (Δ := .set :: .num :: .set :: .set :: GraphTranslation.context_m Δ)
        (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here)
        (.fvar (.there (.there .here)))) = true := SecondOrderRealTraceSyntax.pure_m _ _ _ _ rfl rfl rfl rfl
  change (SecondOrderArithmetic.language_m
    (GraphTranslation.domain_m (Γ := [.num, .set])
      (Δ := .set :: .num :: .set :: .set :: GraphTranslation.context_m Δ) (.bvar (.there .here)) (.bvar .here)) &&
    (SecondOrderArithmetic.language_m
      (SecondOrderRealTraceSyntax.formula_m (Γ := [.num, .set])
        (Δ := .set :: .num :: .set :: .set :: GraphTranslation.context_m Δ)
        (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here)
        (.fvar (.there (.there .here)))) && SecondOrderArithmetic.language_m (body_m φ))) = true
  rw [hDomain, hTrace, hBody]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private def empty_l : assignment_l ℳ [] := fun v => nomatch v

def parameters_l {Δ : SortContext ℒ} (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ) :
    Env ℳ [] (.set :: GraphTranslation.context_m Δ) := SecondOrderRealRowFormula.parameters_l K τ

def source_l {Δ : SortContext ℒ} (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ)
    (n : SecondOrderModel.num_l ℳ) (A : SecondOrderGraph.code_l ℳ) : Env 𝒱 [] (.set :: .set :: Δ) :=
  (SecondOrderInterpretation.source_l hℳ empty_l τ).pushFree (SecondOrderQuotient.mk_l hℳ A)
    |>.pushFree (numberCode_l K n).val

private theorem body_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Δ))
    (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ) (H W : SecondOrderModel.set_l ℳ)
    (n : SecondOrderModel.num_l ℳ) (A : SecondOrderGraph.code_l ℳ) :
    (body_m φ).satisfies (((((parameters_l K τ).pushFree H).pushFree n).pushFree W).pushBound A.real |>.pushBound A.root) ↔
      ∃ B : SecondOrderGraph.code_l ℳ, SecondOrderRealTraceSyntax.trace_l K.less B.real B.root W ∧
        φ.satisfies ((source_l K τ n A).pushFree (SecondOrderQuotient.mk_l hℳ B)) := by
  rw [body_m, SecondOrderFormulaParameters.formula_l]
  let N := SecondOrderNaturalGraph.code_l hℳ K.less K.less_spec n
  have hEnv : SecondOrderRelationSpecification.parameters_l
      (((((parameters_l K τ).pushFree H).pushFree n).pushFree W).pushBound A.real |>.pushBound A.root) insert_m =
      (SecondOrderRealRowFormula.parameters_l K (push_l N (push_l A τ))).pushFree W := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      rcases v with _ | (_ | (_ | (_ | (_ | (_ | v)))))
      all_goals first | rfl | cases s <;> rfl
  rw [hEnv, SecondOrderRealRowFormula.formula_l]
  apply exists_congr
  intro B
  apply and_congr Iff.rfl
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | (_ | (_ | v))
    all_goals rfl

theorem formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Δ))
    (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ) (H W : SecondOrderModel.set_l ℳ)
    (n : SecondOrderModel.num_l ℳ) :
    (formula_m φ).satisfies ((((parameters_l K τ).pushFree H).pushFree n).pushFree W) ↔
      ∃ A : SecondOrderGraph.code_l ℳ, SecondOrderRealTraceSyntax.trace_l K.less A.real A.root H ∧
        ∃ B : SecondOrderGraph.code_l ℳ, SecondOrderRealTraceSyntax.trace_l K.less B.real B.root W ∧
          φ.satisfies ((source_l K τ n A).pushFree (SecondOrderQuotient.mk_l hℳ B)) := by
  simp only [formula_m, Formula.satisfies, SecondOrderInterpretation.domain_l,
    SecondOrderRealTraceSyntax.formula_l, Term.eval]
  change (∃ R r, SecondOrderDomain.wf_l R r ∧ SecondOrderRealTraceSyntax.trace_l K.less R r H ∧
    (body_m φ).satisfies (((((parameters_l K τ).pushFree H).pushFree n).pushFree W).pushBound R |>.pushBound r)) ↔ _
  constructor
  · rintro ⟨R, r, hR, hTrace, hBody⟩
    exact ⟨⟨R, r, hR⟩, hTrace, (body_formula_l φ K τ H W n ⟨R, r, hR⟩).mp hBody⟩
  · rintro ⟨A, hTrace, hBody⟩
    exact ⟨A.real, A.root, A.wf, hTrace, (body_formula_l φ K τ H W n A).mpr hBody⟩

/-- 正文的两个子集守卫使双代表读法精确，不能省略历史守卫。 -/
theorem exists_unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Δ))
    (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ) (H : SecondOrderModel.set_l ℳ)
    (n : SecondOrderModel.num_l ℳ)
    (hHistory : ∀ A B : SecondOrderGraph.code_l ℳ,
      φ.satisfies ((source_l K τ n A).pushFree (SecondOrderQuotient.mk_l hℳ B)) →
        ThirdOrderSemantics.subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ A) K.omega)
    (hOutput : ∀ A B : SecondOrderGraph.code_l ℳ,
      φ.satisfies ((source_l K τ n A).pushFree (SecondOrderQuotient.mk_l hℳ B)) →
        ThirdOrderSemantics.subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ B) K.omega)
    (hTotal : ∀ A : SecondOrderGraph.code_l ℳ,
      ThirdOrderSemantics.subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ A) K.omega →
        ∃! S : SecondOrderQuotient.type_l hℳ, φ.satisfies ((source_l K τ n A).pushFree S)) :
    ∃! W : SecondOrderModel.set_l ℳ,
      (formula_m φ).satisfies ((((parameters_l K τ).pushFree H).pushFree n).pushFree W) := by
  obtain ⟨A, hA, hAH⟩ := SecondOrderRealTraceSyntax.representative_l K H
  obtain ⟨S, hS, hOnly⟩ := hTotal A hA
  obtain ⟨B, hBS⟩ := SecondOrderQuotient.surj_l hℳ S
  have hBody : φ.satisfies ((source_l K τ n A).pushFree (SecondOrderQuotient.mk_l hℳ B)) := by
    rw [hBS]
    exact hS
  have hB := hOutput A B hBody
  let T : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨SecondOrderQuotient.mk_l hℳ B, hB⟩
  obtain ⟨W, hW⟩ := PowerlessBMSQuotientReals.trace_exists_l K T
  refine ⟨W, (formula_l φ K τ H W n).mpr
    ⟨A, hAH, B, (SecondOrderRealTraceSyntax.reading_l K B hB W).mpr hW, hBody⟩, ?_⟩
  intro Y hY
  obtain ⟨A', hA'H, B', hB'Y, hYBody⟩ := (formula_l φ K τ H Y n).mp hY
  have hA' := hHistory A' B' hYBody
  have hB' := hOutput A' B' hYBody
  have hAA' : SecondOrderQuotient.mk_l hℳ A' = SecondOrderQuotient.mk_l hℳ A :=
    congrArg Subtype.val (PowerlessBMSQuotientReals.representative_unique_l K
      ((SecondOrderRealTraceSyntax.reading_l K A' hA' H).mp hA'H)
      ((SecondOrderRealTraceSyntax.reading_l K A hA H).mp hAH))
  have hSource : source_l K τ n A' = source_l K τ n A :=
    congrArg (fun a => (SecondOrderInterpretation.source_l hℳ empty_l τ).pushFree a
      |>.pushFree (numberCode_l K n).val) hAA'
  rw [hSource] at hYBody
  have hB'S := hOnly (SecondOrderQuotient.mk_l hℳ B') hYBody
  let U : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨SecondOrderQuotient.mk_l hℳ B', hB'⟩
  have hUT : U = T := Subtype.ext (hB'S.trans hBS.symm)
  have hUY : setRel_l K U Y := (SecondOrderRealTraceSyntax.reading_l K B' hB' Y).mp hB'Y
  exact PowerlessBMSQuotientReals.trace_unique_l K (hUT ▸ hUY) hW

#print axioms pure_m
#print axioms formula_l
#print axioms exists_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNativeRowFormula
