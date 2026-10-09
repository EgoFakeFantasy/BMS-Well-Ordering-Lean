import BMSConstructibleBridge.PowerlessRelationalEvaluationLogic
import BMSConstructibleBridge.PowerlessRelativeClassSourceEnvironment

/-! # 跨域关系图编译规格与量词步骤

数码和最小槽界先固定，规格量化全部实际求值域、图及足够长的内部赋值。
量词反向由实际类内更新图构造见证，正向由集合函数定义域唯一性对齐长度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSourceSpecification

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelationalCodeDerivation (derivation_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ c N : carrier_l 𝒩) (ξ : Env 𝒩 Γ Δ) (φ : Formula ℒ Γ Δ) : Prop :=
  ∀ {A S G}, PowerlessRelativeClassEvaluationSystem.spec_l ω A e t₁ t₂ t₃ T S G →
    ∀ hA : ∃ a, member_l 𝒩 a A, ∀ m, member_l 𝒩 m ω → subset_l N m →
      ∀ f, map_l f m A → ∀ η : Env (PowerlessMemberStructure.structure_l A hA) Γ Δ,
        PowerlessSourceEnvironment.represents_l ξ η f → (value_l G c f ↔ φ.satisfies η)

theorem widen_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    {ω e T t₁ t₂ t₃ c N M : carrier_l 𝒩} {ξ : Env 𝒩 Γ Δ} {φ : Formula ℒ Γ Δ}
    (h : spec_l ω e T t₁ t₂ t₃ c N ξ φ) (hN : subset_l N M) :
    spec_l ω e T t₁ t₂ t₃ c M ξ φ :=
  fun hSystem hA m hm hM f hf η hη => h hSystem hA m hm (fun x hx => hM x (hN x hx)) f hf η hη

theorem negation_certified_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    {ω e T t₁ t₂ t₃ b N : carrier_l 𝒩} {ξ : Env 𝒩 Γ Δ} {φ : Formula ℒ Γ Δ}
    (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l ω e T)
    (ht₂ : member_l 𝒩 t₂ ω) (hb : member_l 𝒩 b ω) (h : spec_l ω e T t₁ t₂ t₃ b N ξ φ) :
    ∃ c, member_l 𝒩 c ω ∧
      (derivation_l (𝒩 := 𝒩) ω e T t₁ t₂ t₃ b N → derivation_l (𝒩 := 𝒩) ω e T t₁ t₂ t₃ c N) ∧
      spec_l ω e T t₁ t₂ t₃ c N ξ (.neg φ) := by
  obtain ⟨c, hc, hBuild, hCode⟩ := PowerlessRelationalEvaluationLogic.Certified.negation_l hConstruct ht₂ hb
  refine ⟨c, hc, hBuild N, ?_⟩
  intro A S G hSystem hA m hm hM f hf η hη
  exact (hCode hSystem f ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans
    (not_congr (h hSystem hA m hm hM f hf η hη))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {Γ Δ : SortContext ℒ} {ω e T t₁ t₂ t₃ : type_l hℳ B}

theorem existential_certified_l {b k N : type_l hℳ B} {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {φ : Formula ℒ (.set :: Γ) Δ}
    (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := structure_l hℳ B hBase) ω e T)
    (ht₃ : mem_l hℳ t₃.val ω.val) (hk : mem_l hℳ k.val ω.val)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k) (hb : mem_l hℳ b.val ω.val) (hN : mem_l hℳ k.val N.val)
    (h : spec_l ω e T t₁ t₂ t₃ b N (ξ.pushBound k) φ) :
    ∃ c : type_l hℳ B, mem_l hℳ c.val ω.val ∧
      (derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ b N → derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ c N) ∧
      spec_l ω e T t₁ t₂ t₃ c N ξ (.existsE .set φ) := by
  obtain ⟨c, hc, hBuild, hCode⟩ := PowerlessRelationalEvaluationLogic.Certified.existential_l
    (𝒩 := structure_l hℳ B hBase) (t₃ := t₃) (i := k) (b := b) hConstruct ht₃ hk hb
  refine ⟨c, hc, hBuild N hN, ?_⟩
  intro A S G hSystem hA m hm hM f hf η hη
  refine (hCode hSystem f ((hSystem.2.2.2.1 f).mpr ⟨m, hm, hf⟩)).trans ?_
  change PowerlessFiniteEvaluationRelationEquations.exists_l ω A G f k b ↔
    ∃ a : PowerlessMemberStructure.type_l A, φ.satisfies (η.pushBound a)
  constructor
  · rintro ⟨n, _, hn, _, a, ha, g, hg, hUpdate, hValue⟩
    have hLength := PowerlessRelativeClassFunctionProperties.domain_unique_l hn hf
    subst n
    exact ⟨⟨a, ha⟩, (h hSystem hA m hm hM g hg (η.pushBound ⟨a, ha⟩)
      (PowerlessSourceEnvironment.update_l hξ hη ⟨a, ha⟩ hUpdate)).mp hValue⟩
  · rintro ⟨a, ha⟩
    obtain ⟨g, hg, hUpdate⟩ := PowerlessRelativeClassAssignmentUpdate.exists_l hf (hM k hN) a.property
    exact ⟨m, hm, hf, hM k hN, a.val, a.property, g, hg, hUpdate,
      (h hSystem hA m hm hM g hg (η.pushBound a) (PowerlessSourceEnvironment.update_l hξ hη a hUpdate)).mpr ha⟩

theorem universal_certified_l {b k N : type_l hℳ B} {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {φ : Formula ℒ (.set :: Γ) Δ}
    (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := structure_l hℳ B hBase) ω e T)
    (ht₂ : mem_l hℳ t₂.val ω.val) (ht₃ : mem_l hℳ t₃.val ω.val) (hk : mem_l hℳ k.val ω.val)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k) (hb : mem_l hℳ b.val ω.val) (hN : mem_l hℳ k.val N.val)
    (h : spec_l ω e T t₁ t₂ t₃ b N (ξ.pushBound k) φ) :
    ∃ c : type_l hℳ B, mem_l hℳ c.val ω.val ∧
      (derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ b N → derivation_l (𝒩 := structure_l hℳ B hBase) ω e T t₁ t₂ t₃ c N) ∧
      spec_l ω e T t₁ t₂ t₃ c N ξ (.forallE .set φ) := by
  classical
  obtain ⟨p, hp, hBuild₀, h₀⟩ := negation_certified_l (𝒩 := structure_l hℳ B hBase)
    (t₂ := t₂) (b := b) hConstruct ht₂ hb h
  obtain ⟨q, hq, hBuild₁, h₁⟩ := existential_certified_l hConstruct ht₃ hk hξ hp hN h₀
  obtain ⟨c, hc, hBuild₂, h₂⟩ := negation_certified_l (𝒩 := structure_l hℳ B hBase)
    (t₂ := t₂) (b := q) hConstruct ht₂ hq h₁
  refine ⟨c, hc, fun h => hBuild₂ (hBuild₁ (hBuild₀ h)), ?_⟩
  intro A S G hSystem hA m hm hM f hf η hη
  simpa only [Formula.satisfies, not_exists, not_not] using h₂ hSystem hA m hm hM f hf η hη

theorem negation_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    {ω e T t₁ t₂ t₃ b N : carrier_l 𝒩} {ξ : Env 𝒩 Γ Δ} {φ : Formula ℒ Γ Δ}
    (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l ω e T)
    (ht₂ : member_l 𝒩 t₂ ω) (hb : member_l 𝒩 b ω) (h : spec_l ω e T t₁ t₂ t₃ b N ξ φ) :
    ∃ c, member_l 𝒩 c ω ∧ spec_l ω e T t₁ t₂ t₃ c N ξ (.neg φ) := by
  obtain ⟨c, hc, _, h⟩ := negation_certified_l hConstruct ht₂ hb h
  exact ⟨c, hc, h⟩

theorem existential_l {b k N : type_l hℳ B} {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {φ : Formula ℒ (.set :: Γ) Δ}
    (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := structure_l hℳ B hBase) ω e T)
    (ht₃ : mem_l hℳ t₃.val ω.val) (hk : mem_l hℳ k.val ω.val)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k) (hb : mem_l hℳ b.val ω.val) (hN : mem_l hℳ k.val N.val)
    (h : spec_l ω e T t₁ t₂ t₃ b N (ξ.pushBound k) φ) :
    ∃ c : type_l hℳ B, mem_l hℳ c.val ω.val ∧ spec_l ω e T t₁ t₂ t₃ c N ξ (.existsE .set φ) := by
  obtain ⟨c, hc, _, h⟩ := existential_certified_l hConstruct ht₃ hk hξ hb hN h
  exact ⟨c, hc, h⟩

theorem universal_l {b k N : type_l hℳ B} {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {φ : Formula ℒ (.set :: Γ) Δ}
    (hConstruct : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := structure_l hℳ B hBase) ω e T)
    (ht₂ : mem_l hℳ t₂.val ω.val) (ht₃ : mem_l hℳ t₃.val ω.val) (hk : mem_l hℳ k.val ω.val)
    (hξ : ∀ t : Term ℒ Γ Δ .set, t.eval ξ ≠ k) (hb : mem_l hℳ b.val ω.val) (hN : mem_l hℳ k.val N.val)
    (h : spec_l ω e T t₁ t₂ t₃ b N (ξ.pushBound k) φ) :
    ∃ c : type_l hℳ B, mem_l hℳ c.val ω.val ∧ spec_l ω e T t₁ t₂ t₃ c N ξ (.forallE .set φ) := by
  obtain ⟨c, hc, _, h⟩ := universal_certified_l hConstruct ht₂ ht₃ hk hξ hb hN h
  exact ⟨c, hc, h⟩

#print axioms existential_certified_l
#print axioms universal_certified_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalSourceSpecification
