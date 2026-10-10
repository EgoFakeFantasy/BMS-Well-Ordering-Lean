import BMSConstructibleBridge.SecondOrderRealTraceSyntax
import BMSConstructibleBridge.SecondOrderFormulaParameters

/-! # 纯集合逐行正文接回原二阶实数输出

首个原自由变量是真实的行实数，其次为固定内部数序图，余槽为原图翻译
所需的参数根／图对。输出集合代表以对象存在量词引入，不抽取 Type 函数。
纯正文的 ω 子集守卫与总唯一性仍须由实际阶段分支提供；这些条件不能
被宿主构造代替。此接口尚不是完整 BMS 的对象层良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRealRowFormula

open Logic FirstOrder SecondOrderSyntax PowerlessBMSQuotientCoding SecondOrderInterpretation

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  GraphTranslation.context_m

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution signature_m (GraphTranslation.context_m (.set :: Δ)) [.num, .set]
      (.set :: .set :: GraphTranslation.context_m Δ)
  | _, .here => .bvar .here
  | _, .there .here => .bvar (.there .here)
  | _, .there (.there v) => .fvar (.there (.there v))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula signature_m [.num, .set] (.set :: .set :: GraphTranslation.context_m Δ) :=
  SecondOrderFormulaParameters.formula_m (GraphTranslation.form_m φ) insert_m

def formula_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula signature_m [] (.set :: .set :: GraphTranslation.context_m Δ) :=
  .existsE .set <| .existsE .num <| .conj
    (GraphTranslation.domain_m (.bvar (.there .here)) (.bvar .here)) <| .conj
      (SecondOrderRealTraceSyntax.formula_m (.fvar (.there .here)) (.bvar (.there .here))
        (.bvar .here) (.fvar .here)) (body_m φ)

theorem pure_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    SecondOrderArithmetic.language_m (formula_m φ) = true := by
  have hBody : SecondOrderArithmetic.language_m (body_m φ) = true := by
    apply SecondOrderFormulaParameters.pure_m _ _ (GraphTranslation.form_pure_m φ)
    intro s v
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases s <;> rfl
  let R : Term signature_m [.num, .set] (.set :: .set :: GraphTranslation.context_m Δ) .set := .bvar (.there .here)
  let a : Term signature_m [.num, .set] (.set :: .set :: GraphTranslation.context_m Δ) .num := .bvar .here
  let less : Term signature_m [.num, .set] (.set :: .set :: GraphTranslation.context_m Δ) .set := .fvar (.there .here)
  let X : Term signature_m [.num, .set] (.set :: .set :: GraphTranslation.context_m Δ) .set := .fvar .here
  have hDomain := GraphTranslation.domain_pure_m R a rfl rfl
  have hTrace := SecondOrderRealTraceSyntax.pure_m less R a X rfl rfl rfl rfl
  change (SecondOrderArithmetic.language_m (GraphTranslation.domain_m R a) &&
    (SecondOrderArithmetic.language_m (SecondOrderRealTraceSyntax.formula_m less R a X) &&
      SecondOrderArithmetic.language_m (body_m φ))) = true
  rw [hDomain, hTrace, hBody]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private def empty_l : assignment_l ℳ [] := fun v => nomatch v

def parameters_l {Δ : SortContext ℒ} (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ) :
    Env ℳ [] (.set :: GraphTranslation.context_m Δ) :=
  (target_l empty_l τ).pushFree K.less

private theorem body_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ) (X : SecondOrderModel.set_l ℳ)
    (A : SecondOrderGraph.code_l ℳ) :
    (body_m φ).satisfies ((((parameters_l K τ).pushFree X).pushBound A.real).pushBound A.root) ↔
      φ.satisfies ((source_l hℳ empty_l τ).pushFree (SecondOrderQuotient.mk_l hℳ A)) := by
  rw [body_m, SecondOrderFormulaParameters.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l
      ((((parameters_l K τ).pushFree X).pushBound A.real).pushBound A.root) insert_m =
      target_l empty_l (push_l A τ) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v =>
          cases s <;> rfl
  rw [hEnv]
  have hSource : source_l hℳ empty_l (push_l A τ) =
      (source_l hℳ empty_l τ).pushFree (SecondOrderQuotient.mk_l hℳ A) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v <;> rfl
  simpa only [hSource] using (SecondOrderInterpretation.form_l hℳ φ empty_l (push_l A τ))

theorem formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ) (X : SecondOrderModel.set_l ℳ) :
    (formula_m φ).satisfies ((parameters_l K τ).pushFree X) ↔
      ∃ A : SecondOrderGraph.code_l ℳ, SecondOrderRealTraceSyntax.trace_l K.less A.real A.root X ∧
        φ.satisfies ((source_l hℳ empty_l τ).pushFree (SecondOrderQuotient.mk_l hℳ A)) := by
  simp only [formula_m, Formula.satisfies, SecondOrderInterpretation.domain_l,
    SecondOrderRealTraceSyntax.formula_l, Term.eval]
  change (∃ R r, SecondOrderDomain.wf_l R r ∧ SecondOrderRealTraceSyntax.trace_l K.less R r X ∧
    (body_m φ).satisfies ((((parameters_l K τ).pushFree X).pushBound R).pushBound r)) ↔ _
  constructor
  · rintro ⟨R, r, hR, hTrace, hBody⟩
    exact ⟨⟨R, r, hR⟩, hTrace, (body_formula_l φ K τ X ⟨R, r, hR⟩).mp hBody⟩
  · rintro ⟨A, hTrace, hBody⟩
    exact ⟨A.real, A.root, A.wf, hTrace, (body_formula_l φ K τ X A).mpr hBody⟩

/-- 子集守卫来自实际正文，不能只凭逐自然数的迹推出它。 -/
theorem reading_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ)
    (hGuard : ∀ S : SecondOrderQuotient.type_l hℳ,
      φ.satisfies ((source_l hℳ empty_l τ).pushFree S) → ThirdOrderSemantics.subset_l (ℳ := 𝒱) S K.omega)
    (X : SecondOrderModel.set_l ℳ) :
    (formula_m φ).satisfies ((parameters_l K τ).pushFree X) ↔
      ∃ S : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega, setRel_l K S X ∧
        φ.satisfies ((source_l hℳ empty_l τ).pushFree S.val) := by
  rw [formula_l]
  constructor
  · rintro ⟨A, hTrace, hBody⟩
    have hA := hGuard (SecondOrderQuotient.mk_l hℳ A) hBody
    exact ⟨⟨SecondOrderQuotient.mk_l hℳ A, hA⟩, (SecondOrderRealTraceSyntax.reading_l K A hA X).mp hTrace, hBody⟩
  · rintro ⟨S, hTrace, hBody⟩
    obtain ⟨A, hA⟩ := SecondOrderQuotient.surj_l hℳ S.val
    have hSubset := hA.symm ▸ S.property
    let T : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨SecondOrderQuotient.mk_l hℳ A, hSubset⟩
    have hTS : T = S := Subtype.ext hA
    have hTraceT : setRel_l K T X := by
      rw [hTS]
      exact hTrace
    have hBodyA : φ.satisfies ((source_l hℳ empty_l τ).pushFree (SecondOrderQuotient.mk_l hℳ A)) := by
      rw [hA]
      exact hBody
    exact ⟨A, (SecondOrderRealTraceSyntax.reading_l K A hSubset X).mpr hTraceT, hBodyA⟩

/-- 纯正文的真实总唯一性传给原实数输出，不选择代表函数。 -/
theorem exists_unique_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (K : source_coding_l hℳ) (τ : assignment_l ℳ Δ)
    (hGuard : ∀ S : SecondOrderQuotient.type_l hℳ,
      φ.satisfies ((source_l hℳ empty_l τ).pushFree S) → ThirdOrderSemantics.subset_l (ℳ := 𝒱) S K.omega)
    (hTotal : ∃! S : SecondOrderQuotient.type_l hℳ,
      φ.satisfies ((source_l hℳ empty_l τ).pushFree S)) :
    ∃! X : SecondOrderModel.set_l ℳ, (formula_m φ).satisfies ((parameters_l K τ).pushFree X) := by
  obtain ⟨S, hS, hOnly⟩ := hTotal
  let T : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨S, hGuard S hS⟩
  obtain ⟨X, hX⟩ := PowerlessBMSQuotientReals.trace_exists_l K T
  refine ⟨X, (reading_l φ K τ hGuard X).mpr ⟨T, hX, hS⟩, ?_⟩
  intro Y hY
  obtain ⟨U, hU, hBody⟩ := (reading_l φ K τ hGuard Y).mp hY
  have hUT : U = T := Subtype.ext (hOnly U.val hBody)
  exact PowerlessBMSQuotientReals.trace_unique_l K (hUT ▸ hU) hX

#print axioms pure_m
#print axioms formula_l
#print axioms reading_l
#print axioms exists_unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRealRowFormula
