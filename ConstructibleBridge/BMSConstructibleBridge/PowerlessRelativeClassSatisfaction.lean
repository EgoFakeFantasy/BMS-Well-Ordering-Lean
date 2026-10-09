import BMSConstructibleBridge.PowerlessRelativeClassValidity
import BMSConstructibleBridge.PowerlessRelativeClassSequenceAbsolute
import BMSConstructibleBridge.PowerlessSatisfactionGraph

/-! # 同一内部合法性图与跨域求值图的共同装配

合法性关系及其类内图先于所有域 A 固定；每个域再取全有限赋值集、实际
求值图和合法性守卫图。全部读值规格覆盖原商坐标。这里只完成实际图与
合法赋值上的读数，四分支 Sat 方程和严格先前层的应用还需接续。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfaction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

/-- 正确合法性图与原商序列规格使合法赋值上的读数保持原 G。 -/
theorem read_l (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ}
    {ω A S F G R : type_l hℳ B} (hωEq : ω.val = K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l)
    (hR : ∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
      PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val S.val F.val G.val c f)
    {n l : SecondOrderModel.num_l ℳ} {f : SecondOrderQuotient.type_l hℳ}
    (hValid : SecondOrderPairing.relation_l V n l)
    (hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (code_l K l) A.val) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (code_l K n) f ↔
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val (code_l K n) f := by
  have hn : mem_l hℳ (code_l K n) ω.val := hωEq.symm ▸ (numberCode_l K n).property
  have hl : mem_l hℳ (code_l K l) ω.val := hωEq.symm ▸ (numberCode_l K l).property
  have hf : mem_l hℳ f S.val := (hS f).mpr ⟨code_l K l, hl, hMap⟩
  have hValue := (hF (code_l K n) (code_l K l)).mpr ⟨n, l, rfl, rfl, hValid⟩
  exact (hR (code_l K n) f).trans (PowerlessSatisfactionBounded.holds_iff_value_l
    (𝒩 := SecondOrderQuotient.structure_l hℳ) (l := code_l K l) hn hf hl hValue hMap)

/-- 在给定精确长度的任意原商赋值上，图值同时刻画合法性与原求值。 -/
theorem read_iff_l (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ}
    {ω A S F G R : type_l hℳ B} (hωEq : ω.val = K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l)
    (hR : ∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
      PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val S.val F.val G.val c f)
    (n l : SecondOrderModel.num_l ℳ) {f : SecondOrderQuotient.type_l hℳ}
    (hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (code_l K l) A.val) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val (code_l K n) f ↔
      SecondOrderPairing.relation_l V n l ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G.val (code_l K n) f := by
  constructor
  · intro hValue
    obtain ⟨_, _, m, _, hFm, hMap', hG⟩ := (hR (code_l K n) f).mp hValue
    obtain ⟨n', l', hn, hl, hValid⟩ := (hF (code_l K n) m).mp hFm
    have hDomain : m = code_l K l := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, _⟩ := hMap'.2 x hx
        exact (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy.2).1
      · intro hx
        obtain ⟨y, hy, _⟩ := hMap.2 x hx
        exact (SecondOrderFunctionProperties.value_mem_l hℳ hMap' hy.2).1
    have hnEq : n = n' := numberCode_injective_l K (Subtype.ext hn)
    have hlEq : l = l' := numberCode_injective_l K (Subtype.ext (hDomain.symm.trans hl))
    subst n'
    subst l'
    exact ⟨hValid, hG⟩
  · rintro ⟨hValid, hG⟩
    exact (read_l K hωEq hS hF hR hValid hMap).mpr hG

/-- 所有域共用同一编码和合法性图，不抽取域到求值图的 Type 选择函数。 -/
theorem exists_l {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ K : source_coding_l hℳ, ∃ V : SecondOrderModel.set_l ℳ,
      SecondOrderTriangularFormulaSyntax.spec_l V ∧ ∃ e t₁ t₂ t₃ T N F : type_l hℳ B,
        ω.val = K.omega ∧ e.val = code_l K (SecondOrderModel.zero_l ℳ) ∧
        map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T.val K.omega K.omega ∧
        PowerlessBMSQuotientPairingBounds.spec_l K T.val ∧
        PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N.val ∧
        (∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
          PowerlessRelationalCodeValidity.valid_l K V c l) ∧
        ∀ A : type_l hℳ B, ∃ S G R : type_l hℳ B,
          PowerlessRelativeClassEvaluationSystem.spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T S G ∧
          PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val ∧
          ∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
            PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
              ω.val A.val S.val F.val G.val c f := by
  obtain ⟨K, e, t₁, t₂, t₃, T, hωEq, heEq, hT, hSpec, hSystem⟩ :=
    PowerlessRelativeClassEvaluationSystem.uniform_coding_exists_l hω
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  obtain ⟨_, _, hStatic⟩ := hSystem ω
  obtain ⟨N, F, hN, hF⟩ := PowerlessRelativeClassValidity.exists_for_coding_l
    K hω hωEq heEq hStatic.1 hT hSpec hV
  refine ⟨K, V, hV, e, t₁, t₂, t₃, T, N, F, hωEq, heEq, hT, hSpec, hN, hF, ?_⟩
  intro A
  obtain ⟨S, G, hSG⟩ := hSystem A
  obtain ⟨R, hR⟩ := PowerlessSatisfactionGraph.exists_l (hBase := hBase) ω A S F G
  exact ⟨S, G, R, hSG, PowerlessRelativeClassSequenceAbsolute.spec_l hω hSG.2.2.2.1, hR⟩

#print axioms read_l
#print axioms read_iff_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfaction
