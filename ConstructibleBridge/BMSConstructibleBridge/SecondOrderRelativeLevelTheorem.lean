import BMSConstructibleBridge.SecondOrderRelativeLevelFormula

/-! # 相对层值在原 Z₂ 中的存在与商唯一性

每个实际序数输入都有有效零根输出。不同原实数和不同输出根只保证商相等，
不是原编码字面唯一；这两项结论均接到原正式推导核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

def existence_m {Γ Δ : SortContext signature_m} (B α : Term signature_m Γ Δ .set)
    (rα : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (GraphTranslation.domain_m B zero_m) <|
    .imp (SecondOrderGraphTransitivityFormula.formula_m B zero_m) <|
    .imp (GraphTranslation.domain_m α rα) <|
    .imp (SecondOrderGraphOrdinalFormula.formula_m α rα) <|
    .existsE .set <| .conj (GraphTranslation.domain_m (.bvar .here) zero_m)
      (SecondOrderRelativeLevelFormula.formula_m (B.weakenBound sort_m.set)
        (α.weakenBound sort_m.set) (.bvar .here) (rα.weakenBound sort_m.set) zero_m)

def existence_schema_m : Formula signature_m [] [.set, .set, .num] :=
  existence_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

def existence_sentence_m : Sentence signature_m := Metatheory.Formula.forall_close existence_schema_m

theorem existence_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B α : Term signature_m Γ Δ .set) (rα : Term signature_m Γ Δ .num) :
    (existence_m B α rα).satisfies η := by
  intro hB hTrans hα hOrd
  have hBwf : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ) :=
    (SecondOrderInterpretation.domain_l η B zero_m).mp hB
  have hTrans' := (SecondOrderGraphTransitivityFormula.formula_l hℳ η B zero_m hBwf).mp hTrans
  have hαwf := (SecondOrderInterpretation.domain_l η α rα).mp hα
  have hOrd' := (SecondOrderGraphOrdinalFormula.formula_l hℳ η α rα hαwf).mp hOrd
  obtain ⟨W, hW, hLevel⟩ := SecondOrderRelativeLevel.exists_zero_l hℳ (B.eval η) hBwf hTrans'
    ⟨α.eval η, rα.eval η, hαwf⟩ hOrd'
  refine ⟨W, (SecondOrderInterpretation.domain_l (η.pushBound W) (.bvar .here) zero_m).mpr hW, ?_⟩
  apply (SecondOrderRelativeLevelFormula.formula_l hℳ (η.pushBound W)
    (B.weakenBound sort_m.set) (α.weakenBound sort_m.set) (.bvar .here)
    (rα.weakenBound sort_m.set) zero_m
    (by simpa only [Term.eval_weakenBound] using hBwf)
    (by simpa only [Term.eval_weakenBound] using hαwf) hW).mpr
  simp only [Term.eval_weakenBound]
  simpa only [zero_m, Term.eval, Arguments.eval, Env.pushBound, Assignment.push, zero_l] using hLevel

def uniqueness_m {Γ Δ : SortContext signature_m} (B α C C' : Term signature_m Γ Δ .set)
    (rα rC rC' : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .imp (GraphTranslation.domain_m B zero_m) <|
    .imp (GraphTranslation.domain_m α rα) <|
    .imp (GraphTranslation.domain_m C rC) <|
    .imp (GraphTranslation.domain_m C' rC') <|
    .imp (SecondOrderRelativeLevelFormula.formula_m B α C rα rC) <|
    .imp (SecondOrderRelativeLevelFormula.formula_m B α C' rα rC')
      (GraphTranslation.atom_m GraphSyntax.eq_m C C' rC rC')

def uniqueness_schema_m : Formula signature_m [] [.set, .set, .set, .set, .num, .num, .num] :=
  uniqueness_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

def uniqueness_sentence_m : Sentence signature_m := Metatheory.Formula.forall_close uniqueness_schema_m

theorem uniqueness_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B α C C' : Term signature_m Γ Δ .set)
    (rα rC rC' : Term signature_m Γ Δ .num) : (uniqueness_m B α C C' rα rC rC').satisfies η := by
  intro hB hα hC hC' hLevel hLevel'
  have hBwf : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ) :=
    (SecondOrderInterpretation.domain_l η B zero_m).mp hB
  have hαwf := (SecondOrderInterpretation.domain_l η α rα).mp hα
  have hCwf := (SecondOrderInterpretation.domain_l η C rC).mp hC
  have hC'wf := (SecondOrderInterpretation.domain_l η C' rC').mp hC'
  have hLevelC := (SecondOrderRelativeLevelFormula.formula_l hℳ η B α C rα rC hBwf hαwf hCwf).mp hLevel
  have hLevelC' := (SecondOrderRelativeLevelFormula.formula_l hℳ η B α C' rα rC' hBwf hαwf hC'wf).mp hLevel'
  exact (SecondOrderInterpretation.eq_l η C C' rC rC').mpr
    (SecondOrderRelativeLevel.unique_l hℳ (SecondOrderGraph.refl_l hℳ ⟨B.eval η, zero_l ℳ, hBwf⟩)
      (SecondOrderGraph.refl_l hℳ ⟨α.eval η, rα.eval η, hαwf⟩) hLevelC hLevelC')

theorem existence_models_l (hℳ : Theory.Models ℳ theory_m) : existence_sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact existence_formula_l hℳ η _ _ _

theorem uniqueness_models_l (hℳ : Theory.Models ℳ theory_m) : uniqueness_sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact uniqueness_formula_l hℳ η _ _ _ _ _ _ _

theorem exists_derives_m : Derives theory_m [] existence_sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => existence_models_l hℳ)

theorem unique_derives_m : Derives theory_m [] uniqueness_sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => uniqueness_models_l hℳ)

#print axioms exists_derives_m
#print axioms unique_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelTheorem
