import BMSConstructibleBridge.PowerlessRelativeClassConstructorBounds
import BMSConstructibleBridge.PowerlessBMSQuotientConstructorInjective

/-! # 同一类内语法图的严格子码界与构造子单射性

共同见证 T 同时满足实际三角递推、子码严格下降及标签／载荷单射性。
存在句经类相对化及原图翻译回到 Z₂ 推导核；不把三个存在见证混用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassConstructorInjective

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def injective_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e T : carrier_l 𝒩) : Prop :=
  ∀ t a b s d f n, PowerlessFormulaConstructor.constructor_l ω e T t a b n →
    PowerlessFormulaConstructor.constructor_l ω e T s d f n → t = s ∧ a = d ∧ b = f

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def injective_m {Γ Δ : SortContext ℒ} (ω e T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up (up (up t))))))
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      let t : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there (.there .here))))))
      let a : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let b : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there .here))))
      let s : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there .here)))
      let d : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there .here))
      let f : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let n : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
      .imp (PowerlessFormulaConstructor.constructor_m (w ω) (w e) (w T) t a b n) <|
        .imp (PowerlessFormulaConstructor.constructor_m (w ω) (w e) (w T) s d f n)
          (.conj (.equal t s) (.conj (.equal a d) (.equal b f)))

theorem injective_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e T : Term ℒ Γ Δ .set) :
    (injective_m ω e T).satisfies η ↔ injective_l (ω.eval η) (e.eval η) (T.eval η) := by
  simp only [injective_m, injective_l, Formula.satisfies,
    PowerlessFormulaConstructor.constructor_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def body_m {Γ Δ : SortContext ℒ} (ω e T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeClassTriangularDerives.body_m ω e T)
    (.conj (PowerlessRelativeClassConstructorBounds.bounds_m ω e T) (injective_m ω e T))

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {ω e : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e) :
    ∃ T : type_l hℳ B, PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T ∧
      (∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t a b n →
        mem_l hℳ a.val n.val ∧ mem_l hℳ b.val n.val) ∧ injective_l (𝒩 := structure_l hℳ B hBase) ω e T := by
  obtain ⟨K, T, hωEq, heEq, hT, hMap, hSpec⟩ :=
    PowerlessRelativeClassTriangularDerives.exists_ambient_l (hBase := hBase) hω he
  have hωNative := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω
  have hRead {t a b n : type_l hℳ B}
      (hn : PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t a b n) :
      PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
        K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val T.val t.val a.val b.val n.val := by
    simpa only [hωEq, heEq] using PowerlessRelativeClassConstructorBounds.constructor_to_ambient_l hωNative hn
  refine ⟨T, hT, ?_, ?_⟩
  · intro t a b n hn
    exact PowerlessBMSQuotientPairingBounds.constructor_bounds_l K hMap hSpec (hRead hn)
  · intro t a b s d f n hn hm
    obtain ⟨ht, ha, hb⟩ := PowerlessBMSQuotientConstructorInjective.constructor_injective_l K hMap hSpec
      (hRead hn) (hRead hm)
    exact ⟨Subtype.ext ht, Subtype.ext ha, Subtype.ext hb⟩

def sentence_m : Sentence ℒ := .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
  .forallE .set <| .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))) <|
    .existsE .set (body_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) := by
  apply PowerlessRelativeClassRelativization.derives_m
  intro ℳ hℳ B hBase
  simp only [sentence_m, body_m, Formula.TrueIn, Formula.satisfies, omega_formula_l,
    PowerlessRelativeClassTriangularDerives.body_l, PowerlessRelativeClassConstructorBounds.bounds_formula_l,
    injective_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  intro ω hω e he
  exact exists_l (hBase := hBase) hω he

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassConstructorInjective
