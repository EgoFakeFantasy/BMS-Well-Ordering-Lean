import BMSConstructibleBridge.SecondOrderInterpretation
import BMSConstructibleBridge.SecondOrderRelations

/-!
# 在两张固定图的根上读取任意纯集合二元公式

原图翻译的四个首槽是数、图、数、图；交换中间两槽后应用实际二元理解。
只有最后的语义读取要求所指定的两个根内部良基，不要求整张图处处良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphFormulaRelation

open Logic FirstOrder SecondOrderSyntax SecondOrderInterpretation

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  GraphTranslation.context_m

universe u

private def reorder_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: .set :: .num :: .set :: Δ) []
      (.num :: .num :: .set :: .set :: Δ)
  | _, .here => .fvar .here
  | _, .there .here => .fvar (.there (.there .here))
  | _, .there (.there .here) => .fvar (.there .here)
  | _, .there (.there (.there v)) => .fvar (.there (.there (.there v)))

private theorem reorder_pure_m {Δ : SortContext signature_m} :
    SecondOrderSubstitution.images_m (reorder_m (Δ := Δ)) := by
  intro s v
  cases v with
  | here => rfl
  | there v =>
    cases v with
    | here => rfl
    | there v =>
      cases v with
      | here => rfl
      | there v => cases s <;> rfl

/-- 两个根的读取关系由同一个原模型实数表示，支持任意源公式与有限参数。 -/
theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (R S : SecondOrderModel.set_l ℳ) :
    ∃ F : SecondOrderModel.set_l ℳ, ∀ n m
      (hn : SecondOrderDomain.wf_l R n) (hm : SecondOrderDomain.wf_l S m),
      SecondOrderPairing.relation_l F n m ↔
        φ.satisfies ((η.pushFree (SecondOrderQuotient.mk_l hℳ ⟨S, m, hm⟩)).pushFree
          (SecondOrderQuotient.mk_l hℳ ⟨R, n, hn⟩)) := by
  obtain ⟨ρ, τ, hη⟩ := source_surj_l hℳ η
  let σ : Substitution signature_m [] (GraphTranslation.context_m (.set :: .set :: Δ)) []
      (.num :: .num :: .set :: .set :: GraphTranslation.context_m Δ) :=
    .map (fun v => nomatch v) reorder_m
  let ψ := (GraphTranslation.form_m φ).substitute σ
  have hψ : SecondOrderArithmetic.language_m ψ = true :=
    (SecondOrderSubstitution.form_subst_m (GraphTranslation.form_m φ)
      (fun v => nomatch v) reorder_m (fun v => nomatch v) reorder_pure_m).trans
      (GraphTranslation.form_pure_m φ)
  let ξ := ((target_l ρ τ).pushFree S).pushFree R
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ ψ hψ ξ
  refine ⟨F, fun n m hn hm => (hF n m).trans ?_⟩
  refine (Formula.satisfies_substitute _ _ (GraphTranslation.form_m φ)).trans ?_
  have htarget :
      (((ξ.pushFree m).pushFree n).pullback σ) =
      target_l ρ (push_l ⟨R, n, hn⟩ (push_l ⟨S, m, hm⟩ τ)) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v with
      | here => rfl
      | there v =>
        cases v with
        | here => rfl
        | there v =>
          cases v with
          | here => rfl
          | there v =>
            cases v with
            | here => rfl
            | there v => cases s <;> rfl
  rw [htarget, form_l]
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  rw [← hη]
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphFormulaRelation
