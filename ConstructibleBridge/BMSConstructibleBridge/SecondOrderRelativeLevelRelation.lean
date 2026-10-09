import BMSConstructibleBridge.SecondOrderRelativeLevelMonotonicity
import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.SecondOrderFunctionObjects

/-! # 固定两张图上的相对层值关系

有共同输出界后，直接用原二阶理解取得层值关系实数，再构造有序对集合。
此处允许层值的二阶定义，不依赖它已被翻译成纯集合语言，也不逐阶段选择图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelRelation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def body_m {Γ Δ : SortContext signature_m} (B A C : Term signature_m Γ Δ .set)
    (n m rA rC : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (GraphTranslation.domain_m A n) <| .conj (GraphTranslation.domain_m C m) <|
    .conj (GraphTranslation.atom_m GraphSyntax.mem_m A A n rA) <|
    .conj (GraphTranslation.atom_m GraphSyntax.mem_m C C m rC)
      (SecondOrderRelativeLevelFormula.formula_m B A C n m)

def template_m : Formula signature_m [] [.num, .num, .set, .set, .set, .num, .num] :=
  body_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))

theorem template_pure_m : language_m template_m = true := by
  apply SecondOrderFormulaArguments.conj_pure_m
  · exact GraphTranslation.domain_pure_m _ _ rfl rfl
  · apply SecondOrderFormulaArguments.conj_pure_m
    · exact GraphTranslation.domain_pure_m _ _ rfl rfl
    · apply SecondOrderFormulaArguments.conj_pure_m
      · exact GraphTranslation.atom_pure_m _ _ _ _ _
          (pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m) rfl rfl rfl rfl
      · apply SecondOrderFormulaArguments.conj_pure_m
        · exact GraphTranslation.atom_pure_m _ _ _ _ _
            (pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m) rfl rfl rfl rfl
        · exact SecondOrderRelativeLevelFormula.pure_m _ _ _ _ _ rfl rfl rfl rfl rfl

def root_spec_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (A C : SecondOrderGraph.code_l ℳ)
    (n m : num_l ℳ) : Prop :=
  ∃ hn : SecondOrderDomain.wf_l A.real n, ∃ hm : SecondOrderDomain.wf_l C.real m,
    SecondOrderGraph.mem_l ⟨A.real, n, hn⟩ A ∧ SecondOrderGraph.mem_l ⟨C.real, m, hm⟩ C ∧
      SecondOrderRelativeLevel.spec_l hℳ B hB ⟨A.real, n, hn⟩ ⟨C.real, m, hm⟩

theorem template_formula_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (A C : SecondOrderGraph.code_l ℳ) (n m : num_l ℳ) :
    template_m.satisfies (Env.empty (M := ℳ) |>.pushFree C.root |>.pushFree A.root
      |>.pushFree C.real |>.pushFree A.real |>.pushFree B |>.pushFree m |>.pushFree n) ↔
      root_spec_l hℳ B hB A C n m := by
  let η := Env.empty (M := ℳ) |>.pushFree C.root |>.pushFree A.root
    |>.pushFree C.real |>.pushFree A.real |>.pushFree B |>.pushFree m |>.pushFree n
  constructor
  · intro h
    have hn := (SecondOrderInterpretation.domain_l η
      (.fvar (.there (.there (.there .here)))) (.fvar .here)).mp h.1
    have hm := (SecondOrderInterpretation.domain_l η
      (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here))).mp h.2.1
    exact ⟨hn, hm,
      (SecondOrderInterpretation.mem_l η _ _ _ _).mp h.2.2.1,
      (SecondOrderInterpretation.mem_l η _ _ _ _).mp h.2.2.2.1,
      (SecondOrderRelativeLevelFormula.formula_l hℳ η
        (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here)) hB hn hm).mp h.2.2.2.2⟩
  · rintro ⟨hn, hm, hA, hC, hLevel⟩
    exact ⟨(SecondOrderInterpretation.domain_l η _ _).mpr hn,
      (SecondOrderInterpretation.domain_l η _ _).mpr hm,
      (SecondOrderInterpretation.mem_l η _ _ _ _).mpr hA,
      (SecondOrderInterpretation.mem_l η _ _ _ _).mpr hC,
      (SecondOrderRelativeLevelFormula.formula_l hℳ η
        (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here)) hB hn hm).mpr hLevel⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (A C : SecondOrderGraph.code_l ℳ) :
    ∃ F : set_l ℳ, ∀ n m, relation_l F n m ↔ root_spec_l hℳ B hB A C n m := by
  obtain ⟨F, hF⟩ := SecondOrderRelations.comprehension_l hℳ template_m template_pure_m
    (Env.empty (M := ℳ) |>.pushFree C.root |>.pushFree A.root
      |>.pushFree C.real |>.pushFree A.real |>.pushFree B)
  exact ⟨F, fun n m => (hF n m).trans (template_formula_l hℳ B hB A C n m)⟩

def quotient_spec_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (x y : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∃ X Y : SecondOrderGraph.code_l ℳ, SecondOrderQuotient.mk_l hℳ X = x ∧
    SecondOrderQuotient.mk_l hℳ Y = y ∧ SecondOrderRelativeLevel.spec_l hℳ B hB X Y

theorem quotient_code_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} (X Y : SecondOrderGraph.code_l ℳ) :
    quotient_spec_l hℳ B hB (SecondOrderQuotient.mk_l hℳ X) (SecondOrderQuotient.mk_l hℳ Y) ↔
      SecondOrderRelativeLevel.spec_l hℳ B hB X Y := by
  constructor
  · rintro ⟨X', Y', hX, hY, hLevel⟩
    exact SecondOrderRelativeLevel.transfer_l hℳ
      ((SecondOrderQuotient.eq_iff_l hℳ X' X).mp hX)
      ((SecondOrderQuotient.eq_iff_l hℳ Y' Y).mp hY) hLevel
  · intro hLevel
    exact ⟨X, Y, rfl, rfl, hLevel⟩

theorem quotient_unique_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {x y z : SecondOrderQuotient.type_l hℳ}
    (hy : quotient_spec_l hℳ B hB x y) (hz : quotient_spec_l hℳ B hB x z) : y = z := by
  obtain ⟨X, Y, rfl, rfl, hY⟩ := hy
  obtain ⟨X', Z, hX', rfl, hZ⟩ := hz
  exact (SecondOrderQuotient.eq_iff_l hℳ Y Z).mpr (SecondOrderRelativeLevel.unique_l hℳ
    (SecondOrderGraph.refl_l hℳ ⟨B, zero_l ℳ, hB⟩)
    (SecondOrderGraph.symm_l hℳ ((SecondOrderQuotient.eq_iff_l hℳ X' X).mp hX')) hY hZ)

def graph_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (a c f : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔ ∃ x y,
    SecondOrderQuotient.mem_l hℳ x a ∧ SecondOrderQuotient.mem_l hℳ y c ∧
      quotient_spec_l hℳ B hB x y ∧ SecondOrderPairObjects.ordered_l hℳ x y p

theorem value_iff_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {a c f : SecondOrderQuotient.type_l hℳ}
    (hf : graph_l hℳ B hB a c f) (x y : SecondOrderQuotient.type_l hℳ) :
    SecondOrderFunctionObjects.value_l hℳ f x y ↔ SecondOrderQuotient.mem_l hℳ x a ∧
      SecondOrderQuotient.mem_l hℳ y c ∧ quotient_spec_l hℳ B hB x y := by
  constructor
  · rintro ⟨p, hp, hxy⟩
    obtain ⟨s, t, hs, ht, hLevel, hst⟩ := (hf p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hxy hst).mp rfl
    exact ⟨hs, ht, hLevel⟩
  · rintro ⟨hx, hy, hLevel⟩
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
    exact ⟨p, (hf p).mpr ⟨x, y, hx, hy, hLevel, hp⟩, hp⟩

theorem map_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {a c f : SecondOrderQuotient.type_l hℳ}
    (hf : graph_l hℳ B hB a c f)
    (hTotal : ∀ x, SecondOrderQuotient.mem_l hℳ x a →
      ∃ y, SecondOrderQuotient.mem_l hℳ y c ∧ quotient_spec_l hℳ B hB x y) :
    SecondOrderFunctionObjects.map_l hℳ f a c := by
  constructor
  · intro p hp
    obtain ⟨x, y, hx, hy, _, hp⟩ := (hf p).mp hp
    exact ⟨x, y, hx, hy, hp⟩
  · intro x hx
    obtain ⟨y, hy, hLevel⟩ := hTotal x hx
    refine ⟨y, ⟨hy, (value_iff_l hℳ hf x y).mpr ⟨hx, hy, hLevel⟩⟩, ?_⟩
    intro z hz
    exact quotient_unique_l hℳ ((value_iff_l hℳ hf x z).mp hz.2).2.2 hLevel

theorem graph_exists_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (A C : SecondOrderGraph.code_l ℳ) :
    ∃ f : SecondOrderQuotient.type_l hℳ, ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔
      ∃ x y, SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A) ∧
        SecondOrderQuotient.mem_l hℳ y (SecondOrderQuotient.mk_l hℳ C) ∧
        quotient_spec_l hℳ B hB x y ∧ SecondOrderPairObjects.ordered_l hℳ x y p := by
  obtain ⟨F, hF⟩ := exists_l hℳ B hB A C
  have hRoots n m (h : relation_l F n m) :
      SecondOrderDomain.wf_l A.real n ∧ SecondOrderDomain.wf_l C.real m := by
    obtain ⟨hn, hm, _⟩ := (hF n m).mp h
    exact ⟨hn, hm⟩
  obtain ⟨f, hf⟩ := SecondOrderMixedImage.exists_l hℳ A.real C.real F hRoots
  refine ⟨f, fun p => (hf p).trans ?_⟩
  constructor
  · rintro ⟨n, m, h, hp⟩
    obtain ⟨hn, hm, hA, hC, hLevel⟩ := (hF n m).mp h
    exact ⟨SecondOrderQuotient.mk_l hℳ ⟨A.real, n, hn⟩,
      SecondOrderQuotient.mk_l hℳ ⟨C.real, m, hm⟩, hA, hC,
      (quotient_code_l hℳ ⟨A.real, n, hn⟩ ⟨C.real, m, hm⟩).mpr hLevel, hp⟩
  · rintro ⟨x, y, hx, hy, hLevel, hp⟩
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ y
    obtain ⟨n, hn, hXn⟩ := hx
    obtain ⟨m, hm, hYm⟩ := hy
    let N := SecondOrderGraph.child_l hℳ A n hn
    let M := SecondOrderGraph.child_l hℳ C m hm
    have hXN := (SecondOrderQuotient.eq_iff_l hℳ X N).mpr hXn
    have hYM := (SecondOrderQuotient.eq_iff_l hℳ Y M).mpr hYm
    rw [hXN, hYM] at hLevel hp
    have h := (hF n m).mpr ⟨N.wf, M.wf, SecondOrderGraph.child_mem_l hℳ A n hn,
      SecondOrderGraph.child_mem_l hℳ C m hm, (quotient_code_l hℳ N M).mp hLevel⟩
    exact ⟨n, m, h, hp⟩

#print axioms exists_l
#print axioms graph_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelRelation
