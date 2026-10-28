import BMSConstructibleBridge.PowerlessRelativeClassTriangularDerives
import BMSConstructibleBridge.PowerlessBMSQuotientPairingBounds

/-! # 实际原语法图的类内严格子码界及对象推导

类内原加法及配数的正向绝对性保留全部见证，不暗加源模型或 Collection。
实际三角图同时满足原递推和所有构造子的严格载荷界；闭句回传原 Z₂。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassConstructorBounds

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem addition_to_ambient_l {ω e a b c : type_l hℳ B}
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hAdd : PowerlessAddition.addition_l (ℳ := structure_l hℳ B hBase) ω e a b c) :
    PowerlessAddition.addition_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val e.val a.val b.val c.val := by
  obtain ⟨F, hF, hValue⟩ := hAdd
  exact ⟨F.val, PowerlessRelativeClassAdditionAbsolute.iteration_to_ambient_l hω hF,
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b c).mp hValue⟩

theorem code_to_ambient_l {ω e T a b c : type_l hℳ B}
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hCode : PowerlessPairingCode.code_l (ℳ := structure_l hℳ B hBase) ω e T a b c) :
    PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val T.val a.val b.val c.val := by
  obtain ⟨s, t, hSum, hValue, hOut⟩ := hCode
  exact ⟨s.val, t.val, addition_to_ambient_l hω hSum,
    (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) T s t).mp hValue,
    addition_to_ambient_l hω hOut⟩

theorem constructor_to_ambient_l {ω e T t a b n : type_l hℳ B}
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hConstructor : PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t a b n) :
    PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val T.val t.val a.val b.val n.val := by
  obtain ⟨ha, hb, p, hp, ht, hpn, c, hc, hn⟩ := hConstructor
  exact ⟨ha, hb, p.val, code_to_ambient_l hω hp, ht, hpn, c.val, code_to_ambient_l hω hc,
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) c n).mp hn⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def bounds_m {Γ Δ : SortContext ℒ} (ω e T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let t : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let a : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let b : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let n : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (PowerlessFormulaConstructor.constructor_m (w ω) (w e) (w T) t a b n)
      (.conj (SecondOrderObjectSyntax.member_m a n) (SecondOrderObjectSyntax.member_m b n))

theorem bounds_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e T : Term ℒ Γ Δ .set) : (bounds_m ω e T).satisfies η ↔
      ∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := 𝒩) (ω.eval η) (e.eval η) (T.eval η) t a b n →
        member_l 𝒩 a n ∧ member_l 𝒩 b n := by
  simp only [bounds_m, Formula.satisfies, PowerlessFormulaConstructor.constructor_formula_l,
    SecondOrderObjectSyntax.member_m, up, Term.eval_weakenBound, Arguments.eval, Term.eval]
  rfl

def body_m {Γ Δ : SortContext ℒ} (ω e T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeClassTriangularDerives.body_m ω e T) (bounds_m ω e T)

theorem exists_l {ω e : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e) :
    ∃ T : type_l hℳ B, PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase) ω e T ∧
      ∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := structure_l hℳ B hBase) ω e T t a b n →
        mem_l hℳ a.val n.val ∧ mem_l hℳ b.val n.val := by
  obtain ⟨K, T, hωEq, heEq, hT, hMap, hSpec⟩ :=
    PowerlessRelativeClassTriangularDerives.exists_ambient_l (hBase := hBase) hω he
  have hωNative := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω
  refine ⟨T, hT, ?_⟩
  intro t a b n hConstructor
  have hNative := constructor_to_ambient_l hωNative hConstructor
  rw [hωEq, heEq] at hNative
  exact PowerlessBMSQuotientPairingBounds.constructor_bounds_l K (T := T.val)
    (t := t.val) (a := a.val) (b := b.val) (n := n.val) hMap hSpec hNative

def sentence_m : Sentence ℒ := .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
  .forallE .set <| .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))) <|
    .existsE .set (body_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) := by
  apply PowerlessRelativeClassRelativization.derives_m
  intro ℳ hℳ B hBase
  simp only [sentence_m, body_m, Formula.TrueIn, Formula.satisfies, omega_formula_l,
    PowerlessRelativeClassTriangularDerives.body_l, bounds_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  intro ω hω e he
  exact exists_l (hBase := hBase) hω he

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassConstructorBounds
