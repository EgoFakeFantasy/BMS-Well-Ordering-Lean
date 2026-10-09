import BMSConstructibleBridge.PowerlessRelationalSourceSpecification
import BMSConstructibleBridge.PowerlessRelativeClassNaturalProperties

/-! # 弱相对类中的跨域源公式编译

对原 Formula AST 作外部结构递归，先给出同一数码和最小赋值长度，再量化
全部类内求值域与实际关系图。量词使用新槽和类内更新存在性；不假定完整
源模型，不将非标准内部公式码解码为外部 AST。本模块是后续对象模式的语义步骤。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSourceCompilation

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelationalSourceSpecification (spec_l)
open PowerlessRelationalCodeDerivation (derivation_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {ω e T t₁ t₂ t₃ : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
  (ht : PowerlessEvaluationTags.tags_l (ℳ := structure_l hℳ B hBase) e t₁ t₂ t₃)
  (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := structure_l hℳ B hBase) ω e T)

include hω

theorem common_l {Γ Δ : SortContext ℒ} {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {φ ψ : Formula ℒ Γ Δ} {a b k N M : type_l hℳ B}
    (hN : mem_l hℳ N.val ω.val) (hM : mem_l hℳ M.val ω.val)
    (hkN : subset_l (ℳ := structure_l hℳ B hBase) k N) (hφ : spec_l ω e T t₁ t₂ t₃ a N ξ φ)
    (hψ : spec_l ω e T t₁ t₂ t₃ b M ξ ψ) :
    ∃ P : type_l hℳ B, mem_l hℳ P.val ω.val ∧ subset_l (ℳ := structure_l hℳ B hBase) k P ∧
      spec_l ω e T t₁ t₂ t₃ a P ξ φ ∧ spec_l ω e T t₁ t₂ t₃ b P ξ ψ := by
  obtain ⟨P, hP, hNP, hMP⟩ := PowerlessRelativeClassNaturalProperties.upper_l hω hN hM
  exact ⟨P, hP, fun x hx => hNP x (hkN x hx),
    PowerlessRelationalSourceSpecification.widen_l hφ hNP,
    PowerlessRelationalSourceSpecification.widen_l hψ hMP⟩

theorem common_certified_l {Γ Δ : SortContext ℒ} {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {φ ψ : Formula ℒ Γ Δ} {a b k N M : type_l hℳ B}
    (hN : mem_l hℳ N.val ω.val) (hM : mem_l hℳ M.val ω.val)
    (hkN : subset_l (ℳ := structure_l hℳ B hBase) k N)
    (ha : derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ a N) (hb : derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ b M)
    (hφ : spec_l ω e T t₁ t₂ t₃ a N ξ φ) (hψ : spec_l ω e T t₁ t₂ t₃ b M ξ ψ) :
    ∃ P : type_l hℳ B, mem_l hℳ P.val ω.val ∧ subset_l (ℳ := structure_l hℳ B hBase) k P ∧
      derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ a P ∧ derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ b P ∧
      spec_l ω e T t₁ t₂ t₃ a P ξ φ ∧ spec_l ω e T t₁ t₂ t₃ b P ξ ψ := by
  obtain ⟨P, hP, hNP, hMP⟩ := PowerlessRelativeClassNaturalProperties.upper_l hω hN hM
  exact ⟨P, hP, fun x hx => hNP x (hkN x hx), .widen ha hN hP hNP, .widen hb hM hP hMP,
    PowerlessRelationalSourceSpecification.widen_l hφ hNP,
    PowerlessRelationalSourceSpecification.widen_l hψ hMP⟩

include ht hConstruct

theorem formula_certified_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ξ : Env (structure_l hℳ B hBase) Γ Δ)
    {k : type_l hℳ B} (hk : mem_l hℳ k.val ω.val) (hξ : PowerlessSourceEnvironment.bounded_l ξ k) :
    ∃ c N : type_l hℳ B, mem_l hℳ c.val ω.val ∧ mem_l hℳ N.val ω.val ∧
      subset_l (ℳ := structure_l hℳ B hBase) k N ∧ derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ c N ∧ spec_l ω e T t₁ t₂ t₃ c N ξ φ := by
  have htω := PowerlessRelativeClassNaturalProperties.tags_natural_l hω ht
  match φ with
  | .falsum =>
    refine ⟨e, k, htω.1, hk, fun _ h => h, .zero, ?_⟩
    intro A S G hSystem _ _ _ _ f _ _ _
    exact ⟨fun h => hSystem.2.2.2.2.1 f h, False.elim⟩
  | .truth =>
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalEvaluationLogic.Certified.truth_l (𝒩 := structure_l hℳ B hBase)
      (t₂ := t₂) hConstruct htω.2.2.1 htω.1
    refine ⟨c, k, hc, hk, fun _ h => h, hBuild k, ?_⟩
    intro A S G hSystem _ m hm _ f hf _ _
    exact ⟨fun _ => trivial, fun _ => h hSystem f ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)⟩
  | .rel .membership (.cons s (.cons t .nil)) =>
    obtain ⟨c, hc, hCode, _⟩ := hConstruct e htω.1 (s.eval ξ)
      (PowerlessRelativeClassSourceEnvironment.natural_l hω hk hξ s) (t.eval ξ)
      (PowerlessRelativeClassSourceEnvironment.natural_l hω hk hξ t)
    refine ⟨c, k, hc, hk, fun _ h => h, .membership hCode (hξ s) (hξ t), ?_⟩
    intro A S G hSystem _ m hm _ f hf η hη
    exact ((hSystem.2.2.2.2.2 c hc f (s.eval ξ) (t.eval ξ)).1 hCode).trans
      ((and_iff_right ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans
        (PowerlessRelativeClassSourceEnvironment.member_l hf hη s t))
  | .equal (sort := .set) s t =>
    obtain ⟨c, hc, hCode, _⟩ := hConstruct t₁ htω.2.1 (s.eval ξ)
      (PowerlessRelativeClassSourceEnvironment.natural_l hω hk hξ s) (t.eval ξ)
      (PowerlessRelativeClassSourceEnvironment.natural_l hω hk hξ t)
    refine ⟨c, k, hc, hk, fun _ h => h, .equality hCode (hξ s) (hξ t), ?_⟩
    intro A S G hSystem _ m hm _ f hf η hη
    exact ((hSystem.2.2.2.2.2 c hc f (s.eval ξ) (t.eval ξ)).2.1 hCode).trans
      ((and_iff_right ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans
        (PowerlessRelativeClassSourceEnvironment.equal_l hf hη s t))
  | .neg φ =>
    obtain ⟨b, N, hb, hN, hkN, hDφ, hφ⟩ := formula_certified_l φ ξ hk hξ
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalSourceSpecification.negation_certified_l (𝒩 := structure_l hℳ B hBase)
      (t₂ := t₂) (b := b) hConstruct htω.2.2.1 hb hφ
    exact ⟨c, N, hc, hN, hkN, hBuild hDφ, h⟩
  | .conj φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hDφ, hφ⟩ := formula_certified_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hDψ, hψ⟩ := formula_certified_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hDφ, hDψ, hφ, hψ⟩ := common_certified_l hω hN hM hkN hDφ hDψ hφ hψ
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalEvaluationLogic.Certified.conjunction_l (𝒩 := structure_l hℳ B hBase)
      (t₂ := t₂) (a := a) (b := b) hConstruct htω.2.2.1 ha hb
    refine ⟨c, P, hc, hP, hkP, hBuild P hDφ hDψ, ?_⟩
    intro A S G hSystem hA m hm hM f hf η hη
    exact (h hSystem f ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans
      (and_congr (hφ hSystem hA m hm hM f hf η hη) (hψ hSystem hA m hm hM f hf η hη))
  | .disj φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hDφ, hφ⟩ := formula_certified_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hDψ, hψ⟩ := formula_certified_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hDφ, hDψ, hφ, hψ⟩ := common_certified_l hω hN hM hkN hDφ hDψ hφ hψ
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalEvaluationLogic.Certified.disjunction_l (𝒩 := structure_l hℳ B hBase)
      (t₂ := t₂) (a := a) (b := b) hConstruct htω.2.2.1 ha hb
    refine ⟨c, P, hc, hP, hkP, hBuild P hDφ hDψ, ?_⟩
    intro A S G hSystem hA m hm hM f hf η hη
    exact (h hSystem f ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans
      (or_congr (hφ hSystem hA m hm hM f hf η hη) (hψ hSystem hA m hm hM f hf η hη))
  | .imp φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hDφ, hφ⟩ := formula_certified_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hDψ, hψ⟩ := formula_certified_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hDφ, hDψ, hφ, hψ⟩ := common_certified_l hω hN hM hkN hDφ hDψ hφ hψ
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalEvaluationLogic.Certified.implication_l (𝒩 := structure_l hℳ B hBase)
      (t₂ := t₂) (a := a) (b := b) hConstruct htω.2.2.1 ha hb
    refine ⟨c, P, hc, hP, hkP, hBuild P hDφ hDψ, ?_⟩
    intro A S G hSystem hA m hm hM f hf η hη
    exact (h hSystem f ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans
      (imp_congr (hφ hSystem hA m hm hM f hf η hη) (hψ hSystem hA m hm hM f hf η hη))
  | .iff φ ψ =>
    obtain ⟨a, N, ha, hN, hkN, hDφ, hφ⟩ := formula_certified_l φ ξ hk hξ
    obtain ⟨b, M, hb, hM, _, hDψ, hψ⟩ := formula_certified_l ψ ξ hk hξ
    obtain ⟨P, hP, hkP, hDφ, hDψ, hφ, hψ⟩ := common_certified_l hω hN hM hkN hDφ hDψ hφ hψ
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalEvaluationLogic.Certified.biconditional_l (𝒩 := structure_l hℳ B hBase)
      (t₂ := t₂) (a := a) (b := b) hConstruct htω.2.2.1 ha hb
    refine ⟨c, P, hc, hP, hkP, hBuild P hDφ hDψ, ?_⟩
    intro A S G hSystem hA m hm hM f hf η hη
    exact (h hSystem f ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans
      (iff_congr (hφ hSystem hA m hm hM f hf η hη) (hψ hSystem hA m hm hM f hf η hη))
  | .existsE .set φ =>
    obtain ⟨l, hlω, hl⟩ := PowerlessRelativeClassNaturalProperties.successor_exists_l hω hk
    obtain ⟨b, N, hb, hN, hlN, hDφ, hφ⟩ := formula_certified_l φ (ξ.pushBound k) hlω (PowerlessSourceEnvironment.push_l hξ hl)
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalSourceSpecification.existential_certified_l hConstruct htω.2.2.2 hk
      (PowerlessRelativeClassSourceEnvironment.fresh_l hξ) hb (hlN k ((hl k).mpr (Or.inr rfl))) hφ
    exact ⟨c, N, hc, hN, fun x hx => hlN x ((hl x).mpr (Or.inl hx)), hBuild hDφ, h⟩
  | .forallE .set φ =>
    obtain ⟨l, hlω, hl⟩ := PowerlessRelativeClassNaturalProperties.successor_exists_l hω hk
    obtain ⟨b, N, hb, hN, hlN, hDφ, hφ⟩ := formula_certified_l φ (ξ.pushBound k) hlω (PowerlessSourceEnvironment.push_l hξ hl)
    obtain ⟨c, hc, hBuild, h⟩ := PowerlessRelationalSourceSpecification.universal_certified_l hConstruct htω.2.2.1 htω.2.2.2 hk
      (PowerlessRelativeClassSourceEnvironment.fresh_l hξ) hb (hlN k ((hl k).mpr (Or.inr rfl))) hφ
    exact ⟨c, N, hc, hN, fun x hx => hlN x ((hl x).mpr (Or.inl hx)), hBuild hDφ, h⟩

/-- 原接口直接投影同一编译见证；强化接口另保留其有限构造证书。 -/
theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (ξ : Env (structure_l hℳ B hBase) Γ Δ)
    {k : type_l hℳ B} (hk : mem_l hℳ k.val ω.val) (hξ : PowerlessSourceEnvironment.bounded_l ξ k) :
    ∃ c N : type_l hℳ B, mem_l hℳ c.val ω.val ∧ mem_l hℳ N.val ω.val ∧
      subset_l (ℳ := structure_l hℳ B hBase) k N ∧ spec_l ω e T t₁ t₂ t₃ c N ξ φ := by
  obtain ⟨c, N, hc, hN, hkN, _, h⟩ := formula_certified_l hω ht hConstruct φ ξ hk hξ
  exact ⟨c, N, hc, hN, hkN, h⟩

#print axioms formula_l

#print axioms formula_certified_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSourceCompilation
