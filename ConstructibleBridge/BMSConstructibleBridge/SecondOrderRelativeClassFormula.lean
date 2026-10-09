import BMSConstructibleBridge.SecondOrderRelativeClass

/-! # 相对类成员的实际二阶公式

阶段和层值分别由实数与根数编码。此类只是全部相对层的并类；最终 HCL
还需额外的类内部可数性筛选及源公理验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeClassFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def body_m {Γ Δ : SortContext signature_m} (B X α C : Term signature_m Γ Δ .set)
    (rX rα rC : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (GraphTranslation.domain_m α rα) <| .conj (GraphTranslation.domain_m C rC) <|
    .conj (SecondOrderRelativeLevelFormula.formula_m B α C rα rC)
      (GraphTranslation.atom_m GraphSyntax.mem_m X C rX rC)

theorem body_pure_m {Γ Δ : SortContext signature_m} (B X α C : Term signature_m Γ Δ .set)
    (rX rα rC : Term signature_m Γ Δ .num) (hB : pure_term_m B = true)
    (hX : pure_term_m X = true) (hα : pure_term_m α = true) (hC : pure_term_m C = true)
    (hrX : pure_term_m rX = true) (hrα : pure_term_m rα = true) (hrC : pure_term_m rC = true) :
    language_m (body_m B X α C rX rα rC) = true :=
  SecondOrderFormulaArguments.conj_pure_m _ _ (GraphTranslation.domain_pure_m α rα hα hrα)
    (SecondOrderFormulaArguments.conj_pure_m _ _ (GraphTranslation.domain_pure_m C rC hC hrC)
      (SecondOrderFormulaArguments.conj_pure_m _ _ (SecondOrderRelativeLevelFormula.pure_m B α C rα rC hB hα hC hrα hrC)
        (GraphTranslation.atom_pure_m _ X C rX rC
          (pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m) hX hC hrX hrC)))

theorem body_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B X α C : Term signature_m Γ Δ .set) (rX rα rC : Term signature_m Γ Δ .num)
    (hB : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ))
    (hX : SecondOrderDomain.wf_l (X.eval η) (rX.eval η)) :
    (body_m B X α C rX rα rC).satisfies η ↔
      ∃ hα : SecondOrderDomain.wf_l (α.eval η) (rα.eval η),
      ∃ hC : SecondOrderDomain.wf_l (C.eval η) (rC.eval η),
        SecondOrderRelativeLevel.spec_l hℳ (B.eval η) hB ⟨α.eval η, rα.eval η, hα⟩ ⟨C.eval η, rC.eval η, hC⟩ ∧
        SecondOrderGraph.mem_l ⟨X.eval η, rX.eval η, hX⟩ ⟨C.eval η, rC.eval η, hC⟩ := by
  constructor
  · intro h
    have hα := (SecondOrderInterpretation.domain_l η α rα).mp h.1
    have hC := (SecondOrderInterpretation.domain_l η C rC).mp h.2.1
    exact ⟨hα, hC, (SecondOrderRelativeLevelFormula.formula_l hℳ η B α C rα rC hB hα hC).mp h.2.2.1,
      (SecondOrderInterpretation.mem_l η X C rX rC).mp h.2.2.2⟩
  · rintro ⟨hα, hC, hLevel, hMember⟩
    exact ⟨(SecondOrderInterpretation.domain_l η α rα).mpr hα,
      (SecondOrderInterpretation.domain_l η C rC).mpr hC,
      (SecondOrderRelativeLevelFormula.formula_l hℳ η B α C rα rC hB hα hC).mpr hLevel,
      (SecondOrderInterpretation.mem_l η X C rX rC).mpr hMember⟩

def inner_m : Formula signature_m [.num, .set, .num, .set] [.set, .set, .num] :=
  body_m (.fvar .here) (.fvar (.there .here)) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))
    (.fvar (.there (.there .here))) (.bvar (.there (.there .here))) (.bvar .here)

def template_m : Formula signature_m [] [.set, .set, .num] :=
  .existsE .set <| .existsE .num <| .existsE .set <| .existsE .num inner_m

theorem template_pure_m : language_m template_m = true :=
  body_pure_m _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl

private def env_l (B : set_l ℳ) (X : SecondOrderGraph.code_l ℳ)
    (α : set_l ℳ) (rα : num_l ℳ) (C : set_l ℳ) (rC : num_l ℳ) :=
  Env.empty (M := ℳ) |>.pushFree X.root |>.pushFree X.real |>.pushFree B
    |>.pushBound α |>.pushBound rα |>.pushBound C |>.pushBound rC

theorem template_formula_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (X : SecondOrderGraph.code_l ℳ) :
    template_m.satisfies (Env.empty (M := ℳ) |>.pushFree X.root |>.pushFree X.real |>.pushFree B) ↔
      SecondOrderRelativeClass.member_l hℳ B hB X := by
  have hBody (α : set_l ℳ) (rα : num_l ℳ) (C : set_l ℳ) (rC : num_l ℳ) :=
    body_formula_l hℳ (env_l B X α rα C rC) (.fvar .here) (.fvar (.there .here))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))
      (.fvar (.there (.there .here))) (.bvar (.there (.there .here))) (.bvar .here) hB X.wf
  constructor
  · rintro ⟨α, rα, C, rC, h⟩
    obtain ⟨hα, hC, hLevel, hMem⟩ := (hBody α rα C rC).mp h
    exact ⟨⟨α, rα, hα⟩, ⟨C, rC, hC⟩, hLevel, hMem⟩
  · rintro ⟨α, C, hLevel, hMem⟩
    exact ⟨α.real, α.root, C.real, C.root,
      (hBody α.real α.root C.real C.root).mpr ⟨α.wf, C.wf, hLevel, hMem⟩⟩

def formula_m {Γ Δ : SortContext signature_m} (B X : Term signature_m Γ Δ .set)
    (rX : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m template_m (.cons B (.cons X (.cons rX .nil)))

theorem pure_m {Γ Δ : SortContext signature_m} (B X : Term signature_m Γ Δ .set)
    (rX : Term signature_m Γ Δ .num) (hB : pure_term_m B = true)
    (hX : pure_term_m X = true) (hrX : pure_term_m rX = true) :
    language_m (formula_m B X rX) = true := SecondOrderFormulaArguments.pure_m template_m _ template_pure_m
      (by simp only [pure_args_m, hB, hX, hrX, Bool.true_and])

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B X : Term signature_m Γ Δ .set) (rX : Term signature_m Γ Δ .num)
    (hB : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ))
    (hX : SecondOrderDomain.wf_l (X.eval η) (rX.eval η)) :
    (formula_m B X rX).satisfies η ↔ SecondOrderRelativeClass.member_l hℳ (B.eval η) hB ⟨X.eval η, rX.eval η, hX⟩ := by
  rw [formula_m, SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l η
      (Automation.RelationalTranslation.argumentsSubstitution (.cons B (.cons X (.cons rX .nil)))) =
      (Env.empty (M := ℳ) |>.pushFree (rX.eval η) |>.pushFree (X.eval η) |>.pushFree (B.eval η)) := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => nomatch v
  rw [hEnv]
  exact template_formula_l hℳ (B.eval η) hB ⟨X.eval η, rX.eval η, hX⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeClassFormula
