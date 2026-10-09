import BMSConstructibleBridge.SecondOrderCodedOrdinalFamilyBound
import BMSConstructibleBridge.SecondOrderCodedFamilyCollectionDerives
import BMSConstructibleBridge.SecondOrderGraphOrdinalFormula

/-! # 已编码序数族共同界的原 Z₂ 闭句

前提只描述原模型中已经统一编码且每行内部良基的序数族。结论的上界
实际存在，并严格包含每个选中行对象；不添加共同界、Collection 或可数
选择作为前提。该闭句不声称任意未编码族能够统一编码，也不是 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedOrdinalFamilyBoundDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open GraphTranslation (domain_m atom_m)
open SecondOrderCodedFamilyCollectionDerives (rows_m member_m rows_formula_l member_formula_l)
open SecondOrderCodedOrdinalFamilyBound (rows_ordinal_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) (r : sort_m) := t.weakenBound r

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

def rows_ordinal_m {Γ Δ : SortContext signature_m} (H I : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num <| .imp
    (.rel .mem (.cons (.bvar .here) (.cons (up I .num) .nil))) <|
    .forallE .set <| .imp
      (SecondOrderSections.formula_m (up (up H .num) .set) (.bvar .here) (.bvar (.there .here))) <|
      .imp (domain_m (.bvar .here) zero_m) (SecondOrderGraphOrdinalFormula.formula_m (.bvar .here) zero_m)

def bound_m {Γ Δ : SortContext signature_m} (H I W : Term signature_m Γ Δ .set)
    (b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (SecondOrderGraphOrdinalFormula.formula_m W b) <| .forallE .set <| .forallE .num <|
    .imp (domain_m (.bvar (.there .here)) (.bvar .here)) <|
      .imp (member_m (up (up H .set) .num) (up (up I .set) .num) (.bvar (.there .here)) (.bvar .here))
        (atom_m GraphSyntax.mem_m (.bvar (.there .here)) (up (up W .set) .num)
          (.bvar .here) (up (up b .set) .num))

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .set <|
    .imp (.conj (rows_m (.bvar (.there .here)) (.bvar .here))
      (rows_ordinal_m (.bvar (.there .here)) (.bvar .here))) <|
      .existsE .set <| .existsE .num <|
        .conj (domain_m (.bvar (.there .here)) (.bvar .here))
          (bound_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
            (.bvar (.there .here)) (.bvar .here))

/-- 不展开巨大序数正文，按模板的纯语言规格组合。 -/
theorem rows_ordinal_pure_m {Γ Δ : SortContext signature_m} (H I : Term signature_m Γ Δ .set)
    (hH : pure_term_m H = true) (hI : pure_term_m I = true) :
    SecondOrderArithmetic.language_m (rows_ordinal_m H I) = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩⟩
  · simp only [SecondOrderArithmetic.language_m, pure_args_m, pure_term_m, up,
      SecondOrderSubstitution.term_weaken_m, hI]
    rfl
  · apply SecondOrderSections.pure_m _ _ _ _ rfl rfl
    simpa only [up, SecondOrderSubstitution.term_weaken_m] using hH
  · exact GraphTranslation.domain_pure_m _ _ rfl rfl
  · exact SecondOrderGraphOrdinalFormula.pure_m _ _ rfl rfl

theorem bound_pure_m {Γ Δ : SortContext signature_m} (H I W : Term signature_m Γ Δ .set)
    (b : Term signature_m Γ Δ .num) (hH : pure_term_m H = true)
    (hI : pure_term_m I = true) (hW : pure_term_m W = true) (hb : pure_term_m b = true) :
    SecondOrderArithmetic.language_m (bound_m H I W b) = true := by
  let A : Term signature_m (.num :: .set :: Γ) Δ .set := .bvar (.there .here)
  let r : Term signature_m (.num :: .set :: Γ) Δ .num := .bvar .here
  let H' := up (up H .set) .num
  let I' := up (up I .set) .num
  let W' := up (up W .set) .num
  let b' := up (up b .set) .num
  have hH' : pure_term_m H' = true := by
    simpa only [H', up, SecondOrderSubstitution.term_weaken_m] using hH
  have hI' : pure_term_m I' = true := by
    simpa only [I', up, SecondOrderSubstitution.term_weaken_m] using hI
  have hW' : pure_term_m W' = true := by
    simpa only [W', up, SecondOrderSubstitution.term_weaken_m] using hW
  have hb' : pure_term_m b' = true := by
    simpa only [b', up, SecondOrderSubstitution.term_weaken_m] using hb
  change (SecondOrderArithmetic.language_m (SecondOrderGraphOrdinalFormula.formula_m W b) &&
    (SecondOrderArithmetic.language_m (domain_m A r) &&
      (SecondOrderArithmetic.language_m (member_m H' I' A r) &&
        SecondOrderArithmetic.language_m (atom_m GraphSyntax.mem_m A W' r b')))) = true
  rw [SecondOrderGraphOrdinalFormula.pure_m W b hW hb,
    GraphTranslation.domain_pure_m A r rfl rfl,
    SecondOrderCodedFamilyCollectionDerives.member_pure_m H' I' A r hH' hI' rfl rfl,
    GraphTranslation.atom_pure_m GraphSyntax.mem_m A W' r b'
      (SecondOrderArithmetic.pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m)
      rfl hW' rfl hb']
  rfl

theorem language_m : SecondOrderArithmetic.language_m sentence_m = true := by
  let H : Term signature_m [.set, .set] [] .set := .bvar (.there .here)
  let I : Term signature_m [.set, .set] [] .set := .bvar .here
  let H' : Term signature_m [.num, .set, .set, .set] [] .set :=
    .bvar (.there (.there (.there .here)))
  let I' : Term signature_m [.num, .set, .set, .set] [] .set := .bvar (.there (.there .here))
  let A : Term signature_m [.num, .set, .set, .set] [] .set := .bvar (.there .here)
  let r : Term signature_m [.num, .set, .set, .set] [] .num := .bvar .here
  change ((SecondOrderArithmetic.language_m (rows_m H I) &&
    SecondOrderArithmetic.language_m (rows_ordinal_m H I)) &&
      (SecondOrderArithmetic.language_m (domain_m A r) &&
        SecondOrderArithmetic.language_m (bound_m H' I' A r))) = true
  rw [SecondOrderCodedFamilyCollectionDerives.rows_pure_m H I rfl rfl,
    rows_ordinal_pure_m H I rfl rfl, GraphTranslation.domain_pure_m A r rfl rfl,
    bound_pure_m H' I' A r rfl rfl rfl rfl]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem rows_ordinal_formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (H I : Term signature_m Γ Δ .set) :
    (rows_ordinal_m H I).satisfies η ↔ rows_ordinal_l hℳ (H.eval η) (I.eval η) := by
  simp only [rows_ordinal_m, Formula.satisfies, SecondOrderSections.formula_l,
    SecondOrderInterpretation.domain_l, up, zero_m, Term.eval_weakenBound, Term.eval, Arguments.eval]
  constructor
  · intro h i hi Y hY hZero
    cases Y with
    | mk Y r hWf =>
      cases hZero
      exact (SecondOrderGraphOrdinalFormula.formula_l hℳ ((η.pushBound i).pushBound Y)
        (.bvar .here) zero_m hWf).mp (h i hi Y hY hWf)
  · intro h i hi Y hY hWf
    exact (SecondOrderGraphOrdinalFormula.formula_l hℳ ((η.pushBound i).pushBound Y)
      (.bvar .here) zero_m hWf).mpr
      (h i hi ⟨Y, zero_l ℳ, hWf⟩ hY rfl)

theorem models_l (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, rows_formula_l,
    rows_ordinal_formula_l hℳ, bound_m, SecondOrderInterpretation.domain_l,
    SecondOrderInterpretation.mem_l, member_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro H I h
  obtain ⟨hRows, hOrdinal⟩ := h
  obtain ⟨δ, hδ, hBound⟩ := SecondOrderCodedOrdinalFamilyBound.exists_l hℳ H I hRows hOrdinal
  obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ δ
  refine ⟨D.real, D.root, D.wf, ?_, ?_⟩
  · let ξ : Env ℳ [.num, .set, .set, .set] [] :=
      ((((Env.empty (M := ℳ)).pushBound H).pushBound I).pushBound D.real).pushBound D.root
    exact (SecondOrderGraphOrdinalFormula.formula_l hℳ ξ (.bvar (.there .here)) (.bvar .here) D.wf).mpr hδ
  · intro R a hWf hMember
    let A : SecondOrderGraph.code_l ℳ := ⟨R, a, hWf⟩
    have hA : SecondOrderCodedFamilyCollection.member_l H I A := by
      apply (SecondOrderCodedFamilyCollectionDerives.member_iff_l hRows A).mpr
      simpa only [Env.pushBound, Assignment.push] using hMember
    have hMem : SecondOrderGraph.mem_l A D := hBound A hA
    simpa only [SecondOrderGraph.mem_l, A, Env.pushBound, Assignment.push] using hMem

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms language_m
#print axioms rows_ordinal_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedOrdinalFamilyBoundDerives
