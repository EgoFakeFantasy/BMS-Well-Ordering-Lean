import BMSConstructibleBridge.SecondOrderCodedFamilyCollection
import BMSConstructibleBridge.SecondOrderInterpretation
import BMSConstructibleBridge.SecondOrderCompleteness

/-! # 已编码良基见证族的原 Z₂ 收集定理

闭句先量化已有族实数 H 和索引实数 I，再要求每个选中行的内部零根良基。
结论构造一个内部良基零根，其成员恰好是那些整行对象。全部索引、候选
图码和双模拟见证在原模型内量化。这里没有未编码族的选择前提，也没有
相对构造域闭包结论；因此不能替代源模型的完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedFamilyCollectionDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderCodedFamilyCollection (rows_wf_l member_l)
open GraphTranslation (domain_m atom_m)

set_option autoImplicit false

universe u

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) (r : sort_m) := t.weakenBound r

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

def rows_m {Γ Δ : SortContext signature_m} (H I : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num <| .imp
    (.rel .mem (.cons (.bvar .here) (.cons (up I .num) .nil))) <|
    .forallE .set <| .imp
      (SecondOrderSections.formula_m (up (up H .num) .set) (.bvar .here) (.bvar (.there .here)))
      (domain_m (.bvar .here) zero_m)

def member_m {Γ Δ : SortContext signature_m} (H I R : Term signature_m Γ Δ .set)
    (a : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .existsE .set <| .conj
    (.rel .mem (.cons (.bvar (.there .here)) (.cons (up (up I .num) .set) .nil))) <|
    .conj (SecondOrderSections.formula_m (up (up H .num) .set) (.bvar .here) (.bvar (.there .here)))
      (atom_m GraphSyntax.eq_m (up (up R .num) .set) (.bvar .here) (up (up a .num) .set) zero_m)

/-- 族的良基前提只使用原二阶语言；保持参数项泛用性。 -/
theorem rows_pure_m {Γ Δ : SortContext signature_m} (H I : Term signature_m Γ Δ .set)
    (hH : pure_term_m H = true) (hI : pure_term_m I = true) :
    SecondOrderArithmetic.language_m (rows_m H I) = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · simp only [SecondOrderArithmetic.language_m, pure_args_m, pure_term_m, up,
      SecondOrderSubstitution.term_weaken_m, hI]
    rfl
  · apply SecondOrderSections.pure_m _ _ _ _ rfl rfl
    simpa only [up, SecondOrderSubstitution.term_weaken_m] using hH
  · exact GraphTranslation.domain_pure_m _ _ rfl rfl

/-- 选中行的跨图成员模板在任意纯项实例化下保持原语言。 -/
theorem member_pure_m {Γ Δ : SortContext signature_m} (H I R : Term signature_m Γ Δ .set)
    (a : Term signature_m Γ Δ .num) (hH : pure_term_m H = true)
    (hI : pure_term_m I = true) (hR : pure_term_m R = true) (ha : pure_term_m a = true) :
    SecondOrderArithmetic.language_m (member_m H I R a) = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · simp only [SecondOrderArithmetic.language_m, pure_args_m, pure_term_m, up,
      SecondOrderSubstitution.term_weaken_m, hI]
    rfl
  · apply SecondOrderSections.pure_m _ _ _ _ rfl rfl
    simpa only [up, SecondOrderSubstitution.term_weaken_m] using hH
  · refine GraphTranslation.atom_pure_m _ _ _ _ _
      (SecondOrderArithmetic.pure_language_m GraphSyntax.matrix_m GraphSyntax.matrix_pure_m) ?_ rfl ?_ rfl
    · simpa only [up, SecondOrderSubstitution.term_weaken_m] using hR
    · simpa only [up, SecondOrderSubstitution.term_weaken_m] using ha

def collection_m {Γ Δ : SortContext signature_m} (H I W : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .conj (domain_m W zero_m) <| .forallE .set <| .forallE .num <|
    .imp (domain_m (.bvar (.there .here)) (.bvar .here)) <|
      .iff (atom_m GraphSyntax.mem_m (.bvar (.there .here)) (up (up W .set) .num) (.bvar .here) zero_m)
        (member_m (up (up H .set) .num) (up (up I .set) .num) (.bvar (.there .here)) (.bvar .here))

def sentence_m : Sentence signature_m :=
  .forallE .set <| .forallE .set <|
    .imp (rows_m (.bvar (.there .here)) (.bvar .here)) <| .existsE .set <|
      collection_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem language_m : SecondOrderArithmetic.language_m sentence_m = true := rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem rows_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H I : Term signature_m Γ Δ .set) :
    (rows_m H I).satisfies η ↔ rows_wf_l (H.eval η) (I.eval η) := by
  simp only [rows_m, rows_wf_l, Formula.satisfies, SecondOrderSections.formula_l,
    SecondOrderInterpretation.domain_l, up, zero_m, Term.eval_weakenBound, Term.eval, Arguments.eval]
  rfl

theorem member_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H I R : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num) :
    (member_m H I R a).satisfies η ↔ ∃ i Y,
      mem_l i (I.eval η) ∧ SecondOrderSections.spec_l (H.eval η) i Y ∧
        SecondOrderBisimulation.eq_l (R.eval η) Y (a.eval η) (zero_l ℳ) := by
  simp only [member_m, Formula.satisfies, SecondOrderSections.formula_l,
    SecondOrderInterpretation.eq_l, up, zero_m, Term.eval_weakenBound, Term.eval, Arguments.eval]
  rfl

theorem member_iff_l {H I : set_l ℳ} (hRows : rows_wf_l H I)
    (D : SecondOrderGraph.code_l ℳ) : member_l H I D ↔ ∃ i Y,
      mem_l i I ∧ SecondOrderSections.spec_l H i Y ∧
        SecondOrderBisimulation.eq_l D.real Y D.root (zero_l ℳ) := by
  constructor
  · rintro ⟨i, Y, hi, hY, hZero, hDY⟩
    exact ⟨i, Y.real, hi, hY, hZero ▸ hDY⟩
  · rintro ⟨i, Y, hi, hY, hDY⟩
    exact ⟨i, ⟨Y, zero_l ℳ, hRows i hi Y hY⟩, hi, hY, rfl, hDY⟩

theorem collection_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H I W : Term signature_m Γ Δ .set) :
    (collection_m H I W).satisfies η ↔
      SecondOrderDomain.wf_l (W.eval η) (zero_l ℳ) ∧ ∀ R a,
        SecondOrderDomain.wf_l R a →
          ((∃ c, SecondOrderPairing.relation_l (W.eval η) c (zero_l ℳ) ∧
              SecondOrderBisimulation.eq_l R (W.eval η) a c) ↔
            ∃ i Y, mem_l i (I.eval η) ∧ SecondOrderSections.spec_l (H.eval η) i Y ∧
              SecondOrderBisimulation.eq_l R Y a (zero_l ℳ)) := by
  simp only [collection_m, Formula.satisfies, SecondOrderInterpretation.domain_l,
    SecondOrderInterpretation.mem_l, member_formula_l, up, zero_m, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, rows_formula_l, collection_formula_l,
    Term.eval]
  intro H I hRows
  obtain ⟨C, hZero, hC⟩ := SecondOrderCodedFamilyCollection.exists_l hℳ H I hRows
  refine ⟨C.real, hZero ▸ C.wf, ?_⟩
  intro R a hR
  let D : SecondOrderGraph.code_l ℳ := ⟨R, a, hR⟩
  have hRead := (hC D).trans (member_iff_l hRows D)
  dsimp only [Env.pushBound, Assignment.push] at hRead ⊢
  simpa only [SecondOrderGraph.mem_l, D, hZero] using hRead

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms language_m
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedFamilyCollectionDerives
