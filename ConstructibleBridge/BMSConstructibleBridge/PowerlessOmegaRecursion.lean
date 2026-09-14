import BMSConstructibleBridge.PowerlessTraceUnique
import BMSConstructibleBridge.PowerlessFunctionUnion

/-!
# 纯定义算子的内部自然数递归

先以完整 Collection 和 Separation 收集所有内部有限轨迹，再取相容并。
总性、单值性是给定纯公式的条件，不是新增背景公理；结果是实际集合函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOmegaRecursion

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessTrace

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem family_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x, ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y))
    (h₀ : ∀ x y z,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z) → y = z)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) (a : carrier_l ℳ) :
    ∃ H, ∀ g, member_l ℳ g H ↔ ∃ n, member_l ℳ n ω ∧ trace_l φ η g n e a := by
  have h₁ : ∀ n g, (trace_m φ).satisfies
      (((PowerlessComprehension.env_l ((η.push a).push e)).pushFree n).pushFree g) ↔ trace_l φ η g n e a := by
    intro n g
    rw [PowerlessComprehension.env_push_l (Γ := .set :: Γ) (η.push a) e,
      PowerlessComprehension.env_push_l (Γ := Γ) η a]
    exact trace_formula_l φ η g n e a
  obtain ⟨H, hH⟩ := PowerlessComprehension.image_l hℳ (trace_m φ) ((η.push a).push e) ω
    (fun n hn => by
      obtain ⟨g, hg⟩ := PowerlessTrace.exists_l hℳ φ η h hω he a n hn
      exact ⟨g, (h₁ n g).mpr hg⟩)
    (fun n hn f g hf hg => PowerlessTraceUnique.unique_l hℳ φ η h₀ hω hn he
      ((h₁ n f).mp hf) ((h₁ n g).mp hg))
  exact ⟨H, fun g => (hH g).trans (exists_congr fun n => and_congr Iff.rfl (h₁ n g))⟩

def recursion_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f ω e a : carrier_l ℳ) : Prop :=
  ∃ B, map_l f ω B ∧ value_l f e a ∧
    ∀ n m x y, member_l ℳ n ω → successor_l n m → value_l f n x → value_l f m y →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x, ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y))
    (h₀ : ∀ x y z,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z) → y = z)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) (a : carrier_l ℳ) :
    ∃ f, recursion_l φ η f ω e a := by
  obtain ⟨H, hH⟩ := family_l hℳ φ η h h₀ hω he a
  have h₁ : ∀ n, member_l ℳ n ω → ∃ g, member_l ℳ g H ∧ trace_l φ η g n e a := by
    intro n hn
    obtain ⟨g, hg⟩ := PowerlessTrace.exists_l hℳ φ η h hω he a n hn
    exact ⟨g, (hH g).mpr ⟨n, hn, hg⟩, hg⟩
  obtain ⟨f, B, hf, hV⟩ := PowerlessFunctionUnion.exists_range_l hℳ
    (fun g hg => by
      obtain ⟨n, hn, S, C, hS, hg, _⟩ := (hH g).mp hg
      exact ⟨S, C, PowerlessNaturalOrder.subset_l hℳ hω S (successor_mem_l hℳ hω hn hS), hg⟩)
    (fun n hn => by
      obtain ⟨g, hg, S, C, hS, hG, _⟩ := h₁ n hn
      obtain ⟨x, hx, _⟩ := hG.2 n ((hS n).mpr (Or.inr rfl))
      exact ⟨g, hg, x, hx.2⟩)
    (fun f hf g hg => by
      obtain ⟨n, hn, hF⟩ := (hH f).mp hf
      obtain ⟨m, hm, hG⟩ := (hH g).mp hg
      exact PowerlessTraceUnique.compatible_l hℳ φ η h₀ hω hn hm he hF hG)
  refine ⟨f, B, hf, ?_, ?_⟩
  · obtain ⟨g, hg, _, _, _, _, hG, _⟩ := h₁ e (zero_mem_l hℳ hω he)
    exact (hV e a).mpr ⟨g, hg, hG⟩
  · intro n m x y hn hm hx hy
    obtain ⟨g, hg, S, C, hS, hG, _, h₂⟩ := h₁ m (successor_mem_l hℳ hω hn hm)
    have h₃ := (hm n).mpr (Or.inr rfl)
    obtain ⟨v, hv, _⟩ := hG.2 n ((hS n).mpr (Or.inl h₃))
    obtain ⟨w, hw, _⟩ := hG.2 m ((hS m).mpr (Or.inr rfl))
    have h₄ := PowerlessFunction.value_unique_l hℳ hf hx ((hV n v).mpr ⟨g, hg, hv.2⟩)
    have h₅ := PowerlessFunction.value_unique_l hℳ hf hy ((hV m w).mpr ⟨g, hg, hw.2⟩)
    subst x
    subst y
    exact h₂ n m v w h₃ hm hv.2 hw.2

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x y z,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree z) → y = z)
    {ω e a f g : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hf : recursion_l φ η f ω e a) (hg : recursion_l φ η g ω e a) : f = g := by
  obtain ⟨B, hf, hF, h₀⟩ := hf
  obtain ⟨C, hg, hG, h₁⟩ := hg
  let ζ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => g), free := fun _ => ω }
  have h₂ : ∀ n, PowerlessTraceUnique.agree_m.satisfies ((PowerlessComprehension.env_l ζ).pushFree n) ↔
      ∀ x y, value_l f n x → value_l g n y → x = y := fun n => PowerlessTraceUnique.agree_formula_l _
  have h₃ := PowerlessNatural.induction_l hℳ PowerlessTraceUnique.agree_m ζ hω
    (fun z hz => (h₂ z).mpr (by
      have h₄ := PowerlessNatural.zero_unique_l hℳ hz he
      subst z
      intro x y hx hy
      exact (PowerlessFunction.value_unique_l hℳ hf hx hF).trans
        (PowerlessFunction.value_unique_l hℳ hg hy hG).symm))
    (fun n m hn hm h₄ => (h₂ m).mpr (by
      intro x y hx hy
      obtain ⟨v, hv, _⟩ := hf.2 n hn
      obtain ⟨w, hw, _⟩ := hg.2 n hn
      have h₅ := (h₂ n).mp h₄ v w hv.2 hw.2
      subst w
      exact h v x y (h₀ n m v x hn hm hv.2 hx) (h₁ n m v y hn hm hw.2 hy)))
  apply PowerlessFunction.ext_l hℳ hf hg
  intro n hn x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := hg.2 n hn
    exact ((h₂ n).mp (h₃ n hn) x y hx hy.2).symm ▸ hy.2
  · intro hx
    obtain ⟨y, hy, _⟩ := hf.2 n hn
    exact (h₂ n).mp (h₃ n hn) y x hy.2 hx ▸ hy.2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOmegaRecursion
