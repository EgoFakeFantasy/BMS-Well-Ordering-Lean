import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationClosure
import BMSConstructibleBridge.PowerlessRelativeLimitSatisfactionGraph
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification

/-! # 指定外层中的实际完整 Sat 图

复用同一 K/T/V/F，先由严格先前层内的静态参数证明实际求值方程，
再构造指定外层中的 G/R。完整 Sat 规格在原相对类结构上读取，不把
该类的全域真值与某个集合域的满足关系混淆。本模块是层界明确的语义
装配；早期层和全序列集的成员仍须由调用端提供，尚非最终 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfaction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    {B γ D β C : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ}
    (hD : level_l hℳ B γ D) (hInner : limit_l hℳ γ)
    (hC : level_l hℳ B β C) (hOuter : limit_l hℳ β) (hEarlier : mem_l hℳ γ β)
    {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v).val D)
    (hωEq : (ω.eval η).val = K.omega)
    (heEq : (e.eval η).val = code_l K (SecondOrderModel.zero_l ℳ))
    (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase)
      (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η))
    (hTriangular : PowerlessTriangular.triangular_l (ℳ := structure_l hℳ B hBase)
      (ω.eval η) (e.eval η) (T.eval η))
    (hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (T.eval η).val K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K (T.eval η).val)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η).val (ω.eval η).val (N.eval η).val)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η).val (A.eval η).val (S.eval η).val)
    (hV : SecondOrderTriangularFormulaSyntax.spec_l V) {F : type_l hℳ B}
    (hFC : mem_l hℳ F.val C)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l) :
    ∃ G R : type_l hℳ B, mem_l hℳ G.val C ∧ mem_l hℳ R.val C ∧
      PowerlessRelativeClassEvaluationSystem.spec_l (𝒩 := structure_l hℳ B hBase)
        (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (S.eval η) G ∧
      (∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
        PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
          (ω.eval η).val (A.eval η).val (S.eval η).val F.val G.val c f) ∧
      PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase)
        (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) F R := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  have hEval (t : Term ℒ [] Δ .set) : t.eval ξ = (t.eval η).val := by
    match t with
    | .bvar v => nomatch v
    | .fvar _ => rfl
    | .app f _ => nomatch f
  have heRaw : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) (e.eval η).val :=
    (PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) (e.eval η)).mp ht.1
  have hTags : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (e.eval η).val (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val :=
    ⟨heRaw, (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) (e.eval η) (t₁.eval η)).mp ht.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) (t₁.eval η) (t₂.eval η)).mp ht.2.2.1,
      (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) (t₂.eval η) (t₃.eval η)).mp ht.2.2.2⟩
  have hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (T.eval η).val (ω.eval η).val (ω.eval η).val := by simpa only [hωEq] using hMap
  have hBounds : ∀ t a b n, PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η).val (e.eval η).val (T.eval η).val t a b n → mem_l hℳ a n ∧ mem_l hℳ b n := by
    intro t a b n hn
    rw [hωEq, heEq] at hn
    exact PowerlessBMSQuotientPairingBounds.constructor_bounds_l K hMap hSpec hn
  have hInjective : PowerlessRelativeClassConstructorInjective.injective_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      (ω.eval η).val (e.eval η).val (T.eval η).val := by
    intro t a b s d f n hn hm
    rw [hωEq, heEq] at hn hm
    exact PowerlessBMSQuotientConstructorInjective.constructor_injective_l K hMap hSpec hn hm
  have hParamsRaw : ∀ s (v : Variable Δ s), mem_l hℳ (ξ.freeVal v) D := by
    intro s v
    cases s
    exact hParams _ v
  obtain ⟨g, hgC, _, hEquations, hZero⟩ := PowerlessRelativeLimitEvaluationClosure.exists_l K
    hBase hD hInner hC hOuter hEarlier ξ ω e N T A S t₁ t₂ t₃ hParamsRaw
    (by simpa only [hEval] using hωEq) (by simpa only [hEval] using heRaw)
    (by simpa only [hEval] using hN) (by simpa only [hEval] using hT)
    (by simpa only [hEval] using hS) (by simpa only [hEval] using hBounds)
    (by simpa only [hEval] using hTags) (by simpa only [hEval] using hInjective)
  simp only [hEval] at hEquations hZero
  let G : type_l hℳ B := ⟨g, ⟨β, C, hC, hgC⟩⟩
  have hωRaw : SecondOrderOmega.omega_l hℳ (ω.eval η).val := hωEq ▸ K.omega_spec
  have hSClass : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase)
      (ω.eval η) (A.eval η) (S.eval η) := fun f => (hS f.val).trans
    (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l (hBase := hBase) (ω.eval η) (A.eval η) f).symm
  have hSystem : PowerlessRelativeClassEvaluationSystem.spec_l (𝒩 := structure_l hℳ B hBase)
      (ω.eval η) (A.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (T.eval η) (S.eval η) G :=
    ⟨ht, hTriangular, PowerlessRelativeClassConstructorTotal.functional_of_spec_l K hωEq heEq hMap hSpec,
      hSClass, (fun f hf => hZero f.val ((PowerlessRelativeClassFunctionAbsolute.value_l
        (hBase := hBase) G (e.eval η) f).mp hf)),
      PowerlessRelativeClassEvaluationAbsolute.equations_l (ω.eval η) (e.eval η) (T.eval η)
        (A.eval η) (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) G hωRaw hS hEquations⟩
  have hTermC (t : Term ℒ [] Δ .set) : mem_l hℳ (t.eval η).val C := by
    apply PowerlessRelativeLevelClosure.subset_l hℳ hBase hEarlier hD hC
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams _ v
    | .app f _ => nomatch f
  obtain ⟨r, hrC, hr⟩ := PowerlessRelativeLimitSatisfactionGraph.exists_l hBase hOuter hC
    (hTermC ω) (hTermC A) (hTermC S) hFC hgC
  let R : type_l hℳ B := ⟨r, ⟨β, C, hC, hrC⟩⟩
  exact ⟨G, R, hgC, hrC, hSystem, hr,
    PowerlessRelativeClassSatisfactionSpecification.instance_l (hBase := hBase)
      (ω := ω.eval η) (A := A.eval η) (S := S.eval η) (F := F) (G := G) (R := R)
      hr K hωEq hS hF hSystem heEq hMap hSpec hV⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitSatisfaction
