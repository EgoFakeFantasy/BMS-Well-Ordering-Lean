import BMSConstructibleBridge.SecondOrderGraphMinimum
import BMSConstructibleBridge.SecondOrderCompleteness
import YesMetaZFC.Automation.ModelClosure

/-! # 全部内部良基节点上的公式归纳

反例集合由原理解模式构造，其极小元由原无内部下降链公式取得。归纳
命题可以含集合量词；不假定关系在宿主层良基或模型的 ω 外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedInduction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def parameters_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) : Env ℳ [] Δ where
  boundVal := fun v => nomatch v
  freeVal := η.freeVal

@[simp] theorem parameters_pushBound_l {Γ Δ : SortContext signature_m} {s : sort_m}
    (η : Env ℳ Γ Δ) (x : ℳ.Carrier s) : parameters_l (η.pushBound x) = parameters_l η := by
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rfl

@[simp] theorem parameters_empty_l {Δ : SortContext signature_m} (η : Env ℳ [] Δ) :
    parameters_l η = η := by
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rfl

private def insert_m {Γ Δ : SortContext signature_m} (n : Term signature_m Γ Δ .num) :
    VariableSubstitution signature_m (.num :: Δ) Γ Δ
  | _, .here => n
  | _, .there v => .fvar v

def at_m {Γ Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  φ.substitute (show Substitution signature_m [] (.num :: Δ) Γ Δ from
    .map (fun v => nomatch v) (insert_m n))

theorem at_formula_l {Γ Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (η : Env ℳ Γ Δ) (n : Term signature_m Γ Δ .num) :
    (at_m φ n).satisfies η ↔ φ.satisfies ((parameters_l η).pushFree (n.eval η)) := by
  refine (Formula.satisfies_substitute η _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v <;> rfl

theorem induction_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true) (η : Env ℳ [] Δ)
    (R : set_l ℳ)
    (hStep : ∀ n, SecondOrderDomain.wf_l R n →
      (∀ m, relation_l R m n → φ.satisfies (η.pushFree m)) → φ.satisfies (η.pushFree n))
    (n : num_l ℳ) (hn : SecondOrderDomain.wf_l R n) : φ.satisfies (η.pushFree n) := by
  classical
  obtain ⟨P, hP⟩ := comprehension_l hℳ (.neg φ) hφ η
  by_contra hBad
  obtain ⟨a, ha, hWf, hMin⟩ := SecondOrderGraphMinimum.exists_l hℳ R P n hn ((hP n).mpr hBad)
  apply (hP a).mp ha
  apply hStep a hWf
  intro b hb
  by_contra hFalse
  exact hMin b hb ((hP b).mpr hFalse)

def schema_m {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) :
    Formula signature_m [] Δ :=
  .forallE .set <| .imp
    (.forallE .num (GraphTranslation.domain_m (.bvar (.there .here)) (.bvar .here))) <| .imp
    (.forallE .num <| .imp
      (.forallE .num <| .imp
        (GraphSyntax.edge_m (.bvar (.there (.there .here))) (.bvar .here) (.bvar (.there .here)))
        (at_m φ (.bvar .here))) (at_m φ (.bvar .here)))
    (.forallE .num (at_m φ (.bvar .here)))

def sentence_m {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) :
    Sentence signature_m := Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) (hφ : language_m φ = true) (η : Env ℳ [] Δ) :
    (schema_m φ).satisfies η := by
  intro R hWf hStep n
  apply (at_formula_l φ _ (.bvar .here)).mpr
  rw [parameters_pushBound_l, parameters_pushBound_l, parameters_empty_l]
  change φ.satisfies (η.pushFree n)
  apply induction_l hℳ φ hφ η R ?_ n
    ((SecondOrderInterpretation.domain_l _ _ _).mp (hWf n))
  intro a _ ha
  have h : (at_m φ (.bvar .here)).satisfies ((η.pushBound R).pushBound a) := by
    apply hStep a
    intro b hb
    apply (at_formula_l φ _ (.bvar .here)).mpr
    rw [parameters_pushBound_l, parameters_pushBound_l, parameters_pushBound_l, parameters_empty_l]
    exact ha b ((SecondOrderPairing.edge_l _ _ _ _).mp hb)
  have hRead := (at_formula_l φ _ (.bvar .here)).mp h
  rw [parameters_pushBound_l, parameters_pushBound_l, parameters_empty_l] at hRead
  change φ.satisfies (η.pushFree a) at hRead
  exact hRead

theorem derives_m {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ))
    (hφ : language_m φ = true) : Derives theory_m [] (sentence_m φ) := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact models_l hℳ φ hφ η

#print axioms induction_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderWellFoundedInduction
