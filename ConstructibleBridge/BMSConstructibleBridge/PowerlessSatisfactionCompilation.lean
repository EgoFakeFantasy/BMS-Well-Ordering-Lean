import BMSConstructibleBridge.PowerlessSatisfactionDerives
import BMSConstructibleBridge.PowerlessRelationalValidParameterCompilation
import BMSConstructibleBridge.PowerlessRelationalParameterReading

/-! # 同一公共 Sat 图上的带参数编译

直接使用共同构图见证编译原公式，不与独立选择的另一套编码拼接。合法性
沿内部赋值长度单调延伸，因而原 G 的编译读数保持为实际 R 的读数。数码、
槽环境与最小长度均先于求值域和参数固定；本模块是后续对象模式的语义输入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionCompilation

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

theorem read_widen_l (K : source_coding_l hℳ) {V : SecondOrderModel.set_l ℳ}
    {ω A S F G R : type_l hℳ B} (hωEq : ω.val = K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val A.val S.val)
    (hF : ∀ c l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val c l ↔
      PowerlessRelationalCodeValidity.valid_l K V c l)
    (hR : ∀ c f, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) R.val c f ↔
      PowerlessSatisfactionBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        ω.val A.val S.val F.val G.val c f)
    (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    {c L m f : type_l hℳ B} (hValid : PowerlessRelationalCodeValidity.valid_l K V c.val L.val)
    (hm : mem_l hℳ m.val ω.val) (hLm : subset_l (ℳ := structure_l hℳ B hBase) L m)
    (hf : map_l (ℳ := structure_l hℳ B hBase) f m A) :
    value_l (ℳ := structure_l hℳ B hBase) R c f ↔ value_l (ℳ := structure_l hℳ B hBase) G c f := by
  obtain ⟨n, l, hc, hL, hValid⟩ := hValid
  obtain ⟨q, hq⟩ := PowerlessRelativeClassSyntaxReading.number_l K hωEq hm
  have hLq := PowerlessRelativeClassSyntaxReading.index_le_l K hL hq hLm
  have hLift := SecondOrderTriangularFormulaLength.monotone_l hℳ hV n l q hLq hValid
  exact PowerlessSatisfactionLogicalBranches.read_class_l K hωEq hS hF hR hc hq hLift hf

theorem parameters_l {Δ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ e t₁ t₂ t₃ T N F : type_l hℳ B,
      PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := structure_l hℳ B hBase) ω e t₁ t₂ t₃ T N F ∧
      ∃ c L : type_l hℳ B, mem_l hℳ c.val ω.val ∧ mem_l hℳ L.val ω.val ∧
        value_l (ℳ := structure_l hℳ B hBase) F c L ∧ ∃ ξ : Env (structure_l hℳ B hBase) [] Δ,
          PowerlessSourceEnvironment.bounded_l ξ L ∧ ∀ A : type_l hℳ B,
            ∀ hA : ∃ a, member_l (structure_l hℳ B hBase) a A, ∃ R : type_l hℳ B,
              PowerlessSatisfactionSpecification.spec_l (𝒩 := structure_l hℳ B hBase) ω A e t₁ t₂ t₃ T F R ∧
              ∀ η : Env (PowerlessMemberStructure.structure_l (ℳ := structure_l hℳ B hBase) A hA) [] Δ,
                PowerlessRelationalParameterReading.spec_l φ ξ ω A R c L η := by
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, T, N, F, hωEq, he, hT, hSpec, hN, hF, hDomains⟩ :=
    PowerlessRelativeClassSatisfaction.exists_l hω
  obtain ⟨_, _, _, hStatic, _, _⟩ := hDomains ω
  have hNClass : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω ω N := by
    intro f
    have hN' := hN f.val
    rw [← hωEq] at hN'
    exact hN'.trans (PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l
      (hBase := hBase) ω ω f).symm
  obtain ⟨k, ξ, hk, hξ, hDistinct⟩ := PowerlessRelationalParameterAssignment.slots_l hω hStatic.1.1 Δ
  obtain ⟨c, L, hc, hL, hkL, hValid, hCompile⟩ :=
    PowerlessRelationalCodeValidity.formula_l K hωEq he hStatic.1 hT hSpec hV hω hStatic.2.2.1 φ ξ hk hξ
  have hξL : PowerlessSourceEnvironment.bounded_l ξ L := fun t => hkL _ (hξ t)
  refine ⟨e, t₁, t₂, t₃, T, N, F, ?_, c, L, hc, hL, ?_, ξ, hξL, ?_⟩
  · exact ⟨hStatic.1, hStatic.2.1, hStatic.2.2.1, hNClass,
      PowerlessFormulaValiditySpecification.instance_l K hω hωEq he hStatic.1 hT hSpec hV hN hF⟩
  · exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F c L).mpr
      ((hF c.val L.val).mpr hValid)
  · intro A hA
    obtain ⟨S, G, R, hSystem, hS, hR⟩ := hDomains A
    refine ⟨R, PowerlessRelativeClassSatisfactionSpecification.instance_l hR K hωEq hS hF
      hSystem he hT hSpec hV, ?_⟩
    intro η m hm hLm
    refine ⟨PowerlessRelationalParameterAssignment.exists_l hA ξ η (fun t => hLm _ (hξL t)) hDistinct, ?_⟩
    intro f hf hRep
    exact (read_widen_l K hωEq hS hF hR hV hValid hm hLm hf).trans
      (hCompile hSystem hA m hm hLm f hf η hRep)

#print axioms read_widen_l
#print axioms parameters_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionCompilation
