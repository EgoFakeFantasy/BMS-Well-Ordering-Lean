import BMSConstructibleBridge.PowerlessInitialSegment
import BMSConstructibleBridge.PowerlessFunction

/-!
# 递归函数的精确前驱图

H 仅包含 f 在 R-前驱上的有序对。分离从实际集合 f 中取出 H；
图的纯公式、取值、相等与前驱域映射分别核验，不把宿主函数当作内部图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def history_l (H f R a : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p H ↔ ∃ x y, ordered_l x y p ∧ value_l R x a ∧ value_l f x y

def history_m {Γ Δ : SortContext ℒ} (H f R a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    ((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (H.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.existsE .set (.conj
      (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))
      (.conj (SecondOrderObjectSyntax.value_m (w R) (.bvar (.there .here)) (w a))
        (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there .here)) (.bvar .here)))))))

theorem history_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H f R a : Term ℒ Γ Δ .set) :
    (history_m H f R a).satisfies η ↔ history_l (H.eval η) (f.eval η) (R.eval η) (a.eval η) := by
  simp only [history_m, history_l, Formula.satisfies, ordered_formula_l, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f R a : carrier_l ℳ) :
    ∃ H, history_l H f R a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases R (fun _ => a), free := fun _ => f }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .existsE .set (.existsE .set (.conj
      (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
      (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.bvar (.there .here)) (.fvar (.there (.there .here))))))
  have h : ∀ p, φ.satisfies ((PowerlessComprehension.env_l η).pushFree p) ↔
      ∃ x y, ordered_l x y p ∧ value_l R x a := by
    intro p
    simp only [φ, Formula.satisfies, ordered_formula_l, value_formula_l]
    rfl
  obtain ⟨H, hH⟩ := PowerlessComprehension.separation_l hℳ φ η f
  refine ⟨H, fun p => (hH p).trans ((and_congr Iff.rfl (h p)).trans ?_)⟩
  constructor
  · rintro ⟨hp, x, y, h₀, h₁⟩
    exact ⟨x, y, h₀, h₁, p, hp, h₀⟩
  · rintro ⟨x, y, h₀, h₁, q, hq, h₂⟩
    have h₃ := PowerlessBasic.ordered_unique_l hℳ h₀ h₂
    exact ⟨h₃.symm ▸ hq, x, y, h₀, h₁⟩

theorem value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H f R a x y : carrier_l ℳ} (hH : history_l H f R a) :
    ThirdOrderSemantics.value_l H x y ↔ ThirdOrderSemantics.value_l f x y ∧ ThirdOrderSemantics.value_l R x a := by
  constructor
  · rintro ⟨p, hp, h₀⟩
    obtain ⟨s, t, h₁, hs, ht⟩ := (hH p).mp hp
    obtain ⟨h₂, h₃⟩ := (PowerlessBasic.ordered_eq_l hℳ h₀ h₁).mp rfl
    subst s
    subst t
    exact ⟨ht, hs⟩
  · rintro ⟨⟨p, hp, h₀⟩, h₁⟩
    exact ⟨p, (hH p).mpr ⟨x, y, h₀, h₁, p, hp, h₀⟩, h₀⟩

theorem transfer_l {H f g R a : carrier_l ℳ} (hH : history_l H f R a)
    (h : ∀ x y, ThirdOrderSemantics.value_l R x a →
      (ThirdOrderSemantics.value_l f x y ↔ ThirdOrderSemantics.value_l g x y)) : history_l H g R a := by
  intro p
  rw [hH p]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  constructor
  · rintro ⟨hp, hx, hy⟩
    exact ⟨hp, hx, (h x y hx).mp hy⟩
  · rintro ⟨hp, hx, hy⟩
    exact ⟨hp, hx, (h x y hx).mpr hy⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H K f R a : carrier_l ℳ} (hH : history_l H f R a) (hK : history_l K f R a) : H = K :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members H K (fun p => (hH p).trans (hK p).symm)

theorem map_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H f A R a D B C : carrier_l ℳ} (hD : initial_l D A R) (ha : member_l ℳ a D)
    (hf : ThirdOrderSemantics.map_l f D B) (hC : predecessor_l C A R a) (hH : history_l H f R a) :
    ThirdOrderSemantics.map_l H C B := by
  constructor
  · intro p hp
    obtain ⟨x, y, hp, hx, hy⟩ := (hH p).mp hp
    have h₀ := PowerlessFunction.value_mem_l hℳ hf hy
    exact ⟨x, y, (hC x).mpr ⟨hD.1 x h₀.1, hx⟩, h₀.2, hp⟩
  · intro x hx
    have hx₀ := (hC x).mp hx
    obtain ⟨y, hy, _⟩ := hf.2 x (hD.2 a ha x hx₀.1 hx₀.2)
    refine ⟨y, ⟨hy.1, (value_l hℳ hH).mpr ⟨hy.2, hx₀.2⟩⟩, ?_⟩
    intro z hz
    exact PowerlessFunction.value_unique_l hℳ hf ((value_l hℳ hH).mp hz.2).1 hy.2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHistory
