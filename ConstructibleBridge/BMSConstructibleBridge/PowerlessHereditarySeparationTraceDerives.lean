import BMSConstructibleBridge.PowerlessHereditarySeparationTrace

/-! # 实数迹恢复遗传分离的对象模式

所有对象及原公式参数显式量化。前提只要求给定真实包络的精确索引迹
属于相对构造类；结论给出遗传类中的精确切片。该模式由原 Z₂ 推导，
不是把内域完整理解或完整 Separation 作为新公理加入背景。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySeparationTraceDerives

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessHereditarySeparationTrace (cut_m cut_l cut_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def body_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B f X n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (PowerlessValueBounded.formula_m (up f) (up n) (.bvar .here))
    (.conj (member_m (.bvar .here) (up X)) (cut_m φ (up B) (.bvar .here))))

def trace_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B f X w S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (member_m (.bvar .here) (up S))
    (.conj (member_m (.bvar .here) (up w)) (body_m φ (up B) (up f) (up X) (.bvar .here))))

def slice_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B X Y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (member_m (.bvar .here) (up Y))
    (.conj (member_m (.bvar .here) (up X)) (cut_m φ (up B) (.bvar .here))))

/-- 六个对象依次量化为 B、X、T、f、w、S，尾部保留原公式的全部参数。 -/
def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let S : Term ℒ [.set, .set, .set, .set, .set, .set] Δ .set := .bvar .here
    let w := .bvar (.there .here)
    let f := .bvar (.there (.there .here))
    let T := .bvar (.there (.there (.there .here)))
    let X := .bvar (.there (.there (.there (.there .here))))
    let B := .bvar (.there (.there (.there (.there (.there .here)))))
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (PowerlessHereditaryClass.body_m B X T f w) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B S) <|
          .imp (trace_m φ B f X w S) <| .existsE .set <|
            .conj (PowerlessHereditaryClass.formula_m (up B) (.bvar .here))
              (slice_m φ (up B) (up X) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem body_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B f X n : Term ℒ Γ Δ .set) :
    (body_m φ B f X n).satisfies η ↔ ∃ y,
      SecondOrderFunctionObjects.value_l hℳ (f.eval η) (n.eval η) y ∧
        mem_l hℳ y (X.eval η) ∧ cut_l φ (parameters_l η) (B.eval η) y := by
  simp only [body_m, Formula.satisfies, PowerlessValueBounded.formula_l, member_m,
    Arguments.eval, cut_formula_l, parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem trace_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B f X w S : Term ℒ Γ Δ .set) :
    (trace_m φ B f X w S).satisfies η ↔ ∀ n,
      mem_l hℳ n (S.eval η) ↔ mem_l hℳ n (w.eval η) ∧ ∃ y,
        SecondOrderFunctionObjects.value_l hℳ (f.eval η) n y ∧ mem_l hℳ y (X.eval η) ∧
          cut_l φ (parameters_l η) (B.eval η) y := by
  simp only [trace_m, Formula.satisfies, body_formula_l, member_m, Arguments.eval,
    parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem slice_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B X Y : Term ℒ Γ Δ .set) :
    (slice_m φ B X Y).satisfies η ↔ ∀ y,
      mem_l hℳ y (Y.eval η) ↔ mem_l hℳ y (X.eval η) ∧ cut_l φ (parameters_l η) (B.eval η) y := by
  simp only [slice_m, Formula.satisfies, cut_formula_l, member_m, Arguments.eval,
    parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem schema_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ B X T f w S : type_l hℳ,
      (∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) →
      PowerlessHereditaryClass.body_l hℳ B X T f w →
      PowerlessRelativeClassCorrespondence.member_l hℳ B S →
      (∀ n, mem_l hℳ n S ↔ mem_l hℳ n w ∧ ∃ y,
        SecondOrderFunctionObjects.value_l hℳ f n y ∧ mem_l hℳ y X ∧ cut_l φ η B y) →
      ∃ Y, PowerlessHereditaryClass.member_l hℳ B Y ∧ ∀ y,
        mem_l hℳ y Y ↔ mem_l hℳ y X ∧ cut_l φ η B y := by
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    PowerlessHereditaryClass.body_formula_l K, PowerlessRelativeHierarchySemantics.class_formula_l K,
    trace_formula_l, slice_formula_l, PowerlessHereditaryClass.formula_l K,
    parameters_pushBound_l, parameters_empty_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (schema_formula_l K φ η).mpr
  intro B X T f w S hBase hBody hS hTrace
  exact PowerlessHereditarySeparationTrace.slice_l φ η hBase hBody hS hTrace

/-- 任意实际源公式的迹恢复模式回到原二阶算术推导核。 -/
theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms schema_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditarySeparationTraceDerives
