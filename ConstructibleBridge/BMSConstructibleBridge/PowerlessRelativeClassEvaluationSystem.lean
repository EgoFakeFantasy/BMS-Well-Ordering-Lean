import BMSConstructibleBridge.PowerlessRelativeClassEvaluationClosure
import BMSConstructibleBridge.PowerlessFiniteEvaluationZero
import BMSConstructibleBridge.PowerlessRelativeClassConstructorTotal

/-! # 任意类内集合的实际原语法求值系统

从实际 ω 与任意集合 A 出发，构造空集、三个后继标签、同一三角图、全有限
赋值集和求值关系。共同层与历史均在证明中构造，不再是系统存在句的前提。
结论包含零码恒假及四分支方程；良构公式编译与完整 Sat 正确性仍需另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationSystem

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A e t₁ t₂ t₃ T S G : carrier_l 𝒩) : Prop :=
  PowerlessEvaluationTags.tags_l e t₁ t₂ t₃ ∧ PowerlessTriangular.triangular_l ω e T ∧
    PowerlessRelativeClassConstructorTotal.functional_l ω e T ∧
    PowerlessFiniteSequencesSyntax.spec_l ω A S ∧ (∀ f, ¬value_l G e f) ∧
      PowerlessFiniteEvaluationRelationEquations.equations_l ω e T A S t₁ t₂ t₃ G

theorem exists_for_coding_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {ω e t₁ t₂ t₃ T : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    (heEq : e.val = (PowerlessBMSQuotientCoding.numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃)
    (hTriangular : PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T)
    (hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T.val) (A : type_l hℳ B) :
    ∃ S G : type_l hℳ B, spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G := by
  have heRaw := (PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp ht.1
  have hωRaw := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω
  have hTags : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ) e.val t₁.val t₂.val t₃.val :=
    ⟨heRaw, (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e t₁).mp ht.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₁ t₂).mp ht.2.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) t₂ t₃).mp ht.2.2.2⟩
  have hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val ω.val ω.val := by
    simpa only [hωEq] using hMap
  have hBounds : ∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val T.val t a b n → mem_l hℳ a n ∧ mem_l hℳ b n := by
    intro t a b n hn
    rw [hωEq, heEq] at hn
    exact PowerlessBMSQuotientPairingBounds.constructor_bounds_l K hMap hSpec hn
  have hInjective : PowerlessRelativeClassConstructorInjective.injective_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val T.val := by
    intro t a b s d f n hn hm
    rw [hωEq, heEq] at hn hm
    exact PowerlessBMSQuotientConstructorInjective.constructor_injective_l K hMap hSpec hn hm
  obtain ⟨N, hN, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (hBase := hBase) (X := ω) hω
  obtain ⟨S, hS, hSClass⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (hBase := hBase) (X := A) hω
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    (((((((((Env.empty).pushFree ω).pushFree e).pushFree N).pushFree T).pushFree A).pushFree S).pushFree t₁).pushFree t₂).pushFree t₃
  obtain ⟨C, Q, G, _, hG, _, hEquation⟩ := PowerlessRelativeClassEvaluationClosure.exists_l η
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
    hω heRaw hN hT hS hBounds hTags hInjective
  refine ⟨S, G, ht, hTriangular,
    PowerlessRelativeClassConstructorTotal.functional_of_spec_l K hωEq heEq hMap hSpec, hSClass, ?_, hEquation⟩
  intro f hf
  exact PowerlessFiniteEvaluationZero.relation_l (hℳ := hℳ) (C := C.val) (ω := ω.val) (e := e.val)
    (N := N.val) (T := T.val) (A := A.val) (S := S.val) (t₁ := t₁.val) (t₂ := t₂.val) (t₃ := t₃.val)
    (Q := Q.val) (G := G.val) hωRaw heRaw hN hT hS hG f.val
    ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G e f).mp hf)

/-- 保留实际编码见证及同一 T 的原商规格，供内部合法性与求值共同使用。 -/
theorem uniform_coding_exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ K : PowerlessBMSQuotientCoding.source_coding_l hℳ, ∃ e t₁ t₂ t₃ T : type_l hℳ B,
      ω.val = K.omega ∧ e.val = (PowerlessBMSQuotientCoding.numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega ∧
      PowerlessBMSQuotientPairingBounds.spec_l K T.val ∧ ∀ A, ∃ S G,
        spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G := by
  have hInd := hω.1
  change (∃ e : type_l hℳ B, PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e ∧ mem_l hℳ e.val ω.val) ∧
    (∀ a : type_l hℳ B, mem_l hℳ a.val ω.val → ∃ b : type_l hℳ B,
      mem_l hℳ b.val ω.val ∧ PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a b) at hInd
  obtain ⟨e, he, heω⟩ := hInd.1
  obtain ⟨t₁, ht₁ω, h₁⟩ := hInd.2 e heω
  obtain ⟨t₂, ht₂ω, h₂⟩ := hInd.2 t₁ ht₁ω
  obtain ⟨t₃, _, h₃⟩ := hInd.2 t₂ ht₂ω
  obtain ⟨K, T, hωEq, heEq, hTriangular, hMap, hSpec⟩ :=
    PowerlessRelativeClassTriangularDerives.exists_ambient_l (hBase := hBase) hω he
  exact ⟨K, e, t₁, t₂, t₃, T, hωEq, heEq, hMap, hSpec, fun A =>
    exists_for_coding_l K hω hωEq heEq ⟨he, h₁, h₂, h₃⟩ hTriangular hMap hSpec A⟩

/-- 编码参数先于所有求值域固定；不抽取 A 到 G 的 Type 函数。 -/
theorem uniform_exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ e t₁ t₂ t₃ T : type_l hℳ B, ∀ A, ∃ S G,
      spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G := by
  obtain ⟨_, e, t₁, t₂, t₃, T, _, _, _, _, h⟩ := uniform_coding_exists_l hω
  exact ⟨e, t₁, t₂, t₃, T, h⟩

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {ω : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) (A : type_l hℳ B) :
    ∃ e t₁ t₂ t₃ T S G : type_l hℳ B, spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G := by
  obtain ⟨e, t₁, t₂, t₃, T, h⟩ := uniform_exists_l hω
  obtain ⟨S, G, hSG⟩ := h A
  exact ⟨e, t₁, t₂, t₃, T, S, G, hSG⟩

def spec_m {Γ Δ : SortContext ℒ} (ω A e t₁ t₂ t₃ T S G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessEvaluationTags.tags_m e t₁ t₂ t₃) <|
    .conj (PowerlessRelativeClassTriangularDerives.body_m ω e T) <|
      .conj (PowerlessRelativeClassConstructorTotal.functional_m ω e T) <|
        .conj (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
          .conj (PowerlessFiniteEvaluationZero.formula_m e G)
            (PowerlessFiniteEvaluationRelationEquations.equations_m ω e T A S t₁ t₂ t₃ G)

theorem spec_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A e t₁ t₂ t₃ T S G : Term ℒ Γ Δ .set) :
    (spec_m ω A e t₁ t₂ t₃ T S G).satisfies η ↔
      spec_l (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (S.eval η) (G.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, PowerlessEvaluationTags.tags_formula_l,
    PowerlessRelativeClassTriangularDerives.body_l, PowerlessRelativeClassConstructorTotal.functional_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l,
    PowerlessFiniteEvaluationZero.formula_l, PowerlessFiniteEvaluationRelationEquations.equations_formula_l]

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def existence_m {Γ Δ : SortContext ℒ} (ω A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up (up (up t))))))
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      spec_m (w ω) (w A)
        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem existence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A : Term ℒ Γ Δ .set) :
    (existence_m ω A).satisfies η ↔ ∃ e t₁ t₂ t₃ T S G, spec_l (ω.eval η) (A.eval η) e t₁ t₂ t₃ T S G := by
  simp only [existence_m, Formula.satisfies, spec_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def sentence_m : Sentence ℒ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
    .forallE .set (existence_m (.bvar (.there .here)) (.bvar .here))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l, existence_formula_l, Term.eval]
  exact fun _ hω A => exists_l (hBase := hBase) hω A

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase => models_l hℳ B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEvaluationSystem
