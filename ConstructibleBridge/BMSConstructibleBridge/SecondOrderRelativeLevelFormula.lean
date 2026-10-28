import BMSConstructibleBridge.SecondOrderRelativeLevelBody

/-! # 相对层值的原二阶存在证书公式

存在块只绑定原模型实数及自然数，不量化宿主商类型。完整对象矩阵的双向
语义与实际历史定义连接，供后续相对类量词与正式推导使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def inner_m : Formula signature_m [.set, .num, .set, .set, .set, .set, .num, .set]
    [.set, .set, .num, .set, .num] :=
  SecondOrderRelativeLevelBody.formula_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there (.there .here))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar .here)
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there .here))

def template_m : Formula signature_m [] [.set, .set, .num, .set, .num] :=
  .existsE .set <| .existsE .num <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .num <| .existsE .set inner_m

theorem template_pure_m : language_m template_m = true :=
  SecondOrderRelativeLevelBody.pure_m _ _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

private def env_l (B : set_l ℳ) (α C : SecondOrderGraph.code_l ℳ)
    (A : set_l ℳ) (r : num_l ℳ) (Q D R S : set_l ℳ) (n : num_l ℳ) (W : set_l ℳ) :=
  Env.empty (M := ℳ) |>.pushFree C.root |>.pushFree C.real |>.pushFree α.root |>.pushFree α.real |>.pushFree B
    |>.pushBound A |>.pushBound r |>.pushBound Q |>.pushBound D |>.pushBound R |>.pushBound S |>.pushBound n |>.pushBound W

theorem inner_formula_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (α C : SecondOrderGraph.code_l ℳ)
    (A : set_l ℳ) (r : num_l ℳ) (Q D R S : set_l ℳ) (n : num_l ℳ) (W : set_l ℳ) :
    inner_m.satisfies (env_l B α C A r Q D R S n W) ↔
    ∃ hA : SecondOrderDomain.wf_l A r,
      SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
        (SecondOrderQuotient.mk_l hℳ ⟨A, r, hA⟩) ∧
      SecondOrderOrdinalHierarchy.presentation_l ⟨A, r, hA⟩ Q D R ∧
      SecondOrderRelativeHierarchyStrongTheorem.spec_l B R S hB ∧ mem_l n D ∧
      SecondOrderBisimulation.eq_l α.real A α.root n ∧ SecondOrderSections.spec_l S n W ∧
      SecondOrderBisimulation.eq_l C.real W C.root (zero_l ℳ) := by
  exact SecondOrderRelativeLevelBody.formula_l hℳ (env_l B α C A r Q D R S n W)
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there (.there .here))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.bvar (.there (.there (.there (.there (.there .here))))))
    (.bvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar .here)
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there (.there .here)))))
    (.bvar (.there (.there (.there (.there (.there (.there .here))))))) (.bvar (.there .here)) hB

theorem template_formula_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (α C : SecondOrderGraph.code_l ℳ) :
    template_m.satisfies (Env.empty (M := ℳ) |>.pushFree C.root |>.pushFree C.real |>.pushFree α.root
      |>.pushFree α.real |>.pushFree B) ↔ SecondOrderRelativeLevel.spec_l hℳ B hB α C := by
  constructor
  · rintro ⟨A, r, Q, D, R, S, n, W, h⟩
    obtain ⟨hA, hOrd, hP, hS, hn, hαn, hW, hC⟩ := (inner_formula_l hℳ B hB α C A r Q D R S n W).mp h
    exact ⟨⟨A, r, hA⟩, hOrd, Q, D, R, S, n, W, hP, hS, hn, hαn, hW, hC⟩
  · rintro ⟨A, hOrd, Q, D, R, S, n, W, hP, hS, hn, hαn, hW, hC⟩
    exact ⟨A.real, A.root, Q, D, R, S, n, W,
      (inner_formula_l hℳ B hB α C A.real A.root Q D R S n W).mpr
        ⟨A.wf, hOrd, hP, hS, hn, hαn, hW, hC⟩⟩

def formula_m {Γ Δ : SortContext signature_m} (B α C : Term signature_m Γ Δ .set)
    (rα rC : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m template_m (.cons B (.cons α (.cons rα (.cons C (.cons rC .nil)))))

theorem pure_m {Γ Δ : SortContext signature_m} (B α C : Term signature_m Γ Δ .set)
    (rα rC : Term signature_m Γ Δ .num) (hB : pure_term_m B = true)
    (hα : pure_term_m α = true) (hC : pure_term_m C = true)
    (hrα : pure_term_m rα = true) (hrC : pure_term_m rC = true) :
    language_m (formula_m B α C rα rC) = true :=
  SecondOrderFormulaArguments.pure_m template_m _ template_pure_m
    (by simp only [pure_args_m, hB, hα, hC, hrα, hrC, Bool.true_and])

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B α C : Term signature_m Γ Δ .set) (rα rC : Term signature_m Γ Δ .num)
    (hB : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ))
    (hα : SecondOrderDomain.wf_l (α.eval η) (rα.eval η))
    (hC : SecondOrderDomain.wf_l (C.eval η) (rC.eval η)) :
    (formula_m B α C rα rC).satisfies η ↔ SecondOrderRelativeLevel.spec_l hℳ (B.eval η) hB
      ⟨α.eval η, rα.eval η, hα⟩ ⟨C.eval η, rC.eval η, hC⟩ := by
  rw [formula_m, SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l η
      (Automation.RelationalTranslation.argumentsSubstitution (.cons B (.cons α (.cons rα (.cons C (.cons rC .nil)))))) =
      (Env.empty (M := ℳ) |>.pushFree (rC.eval η) |>.pushFree (C.eval η) |>.pushFree (rα.eval η)
        |>.pushFree (α.eval η) |>.pushFree (B.eval η)) := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      rcases v with _ | _ | _ | _ | _ | v
      all_goals first | rfl | nomatch v
  rw [hEnv]
  exact template_formula_l hℳ (B.eval η) hB
    ⟨α.eval η, rα.eval η, hα⟩ ⟨C.eval η, rC.eval η, hC⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelFormula
