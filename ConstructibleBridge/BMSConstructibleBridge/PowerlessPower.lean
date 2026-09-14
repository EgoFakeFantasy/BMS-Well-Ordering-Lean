import BMSConstructibleBridge.PowerlessComprehension
import BMSConstructibleBridge.ThirdOrderSemantics

/-!
# 沿单射传回已经存在的幂集

若 A 单射到 W 且 P(W) 已存在，只由分离、收集和外延性构造 P(A)。
特别地，这允许三阶工作背景构造任意内部可数集合的幂集，而不加入完整幂集。
所有子集与函数均为模型内部对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPower

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def fiber_m {Γ Δ : SortContext ℒ} (f r x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (value_m (f.weakenBound SetTheory.SetSort.set)
    (x.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (member_m (.bvar .here) (r.weakenBound SetTheory.SetSort.set)))

def range_m {Γ Δ : SortContext ℒ} (f b y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (member_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set))
    (value_m (f.weakenBound SetTheory.SetSort.set) (.bvar .here)
      (y.weakenBound SetTheory.SetSort.set)))

def preimage_m {Γ Δ : SortContext ℒ} (f a r b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (member_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set))
    (.conj (member_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set))
      (fiber_m (f.weakenBound SetTheory.SetSort.set)
        (r.weakenBound SetTheory.SetSort.set) (.bvar .here))))

def preimage_l (f a r b : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x b ↔ member_l ℳ x a ∧ ∃ y, ThirdOrderSemantics.value_l f x y ∧ member_l ℳ y r

theorem fiber_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f r x : Term ℒ Γ Δ .set) :
    Formula.satisfies η (fiber_m f r x) ↔
      ∃ y, ThirdOrderSemantics.value_l (f.eval η) (x.eval η) y ∧ member_l ℳ y (r.eval η) := by
  simp only [fiber_m, Formula.satisfies, value_formula_l, member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem range_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f b y : Term ℒ Γ Δ .set) :
    Formula.satisfies η (range_m f b y) ↔
      ∃ x, member_l ℳ x (b.eval η) ∧ ThirdOrderSemantics.value_l (f.eval η) x (y.eval η) := by
  simp only [range_m, Formula.satisfies, value_formula_l, member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem preimage_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f a r b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (preimage_m f a r b) ↔
      preimage_l (f.eval η) (a.eval η) (r.eval η) (b.eval η) := by
  simp only [preimage_m, Formula.satisfies, fiber_formula_l, member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem preimage_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f a r : carrier_l ℳ) :
    ∃ b, preimage_l f a r b := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => r), free := fun _ => a }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    fiber_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  obtain ⟨b, hb⟩ := PowerlessComprehension.separation_l hℳ φ η a
  refine ⟨b, fun x => (hb x).trans (and_congr Iff.rfl ?_)⟩
  dsimp only [φ]
  rw [fiber_formula_l]
  rfl

theorem preimage_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f a r b c : carrier_l ℳ} (hb : preimage_l f a r b) (hc : preimage_l f a r c) : b = c := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  exact (hb x).trans (hc x).symm

theorem range_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f w b : carrier_l ℳ) :
    ∃ r, ∀ y, member_l ℳ y r ↔ member_l ℳ y w ∧
      ∃ x, member_l ℳ x b ∧ ThirdOrderSemantics.value_l f x y := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => b), free := fun _ => w }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    range_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  obtain ⟨r, hr⟩ := PowerlessComprehension.separation_l hℳ φ η w
  refine ⟨r, fun y => (hr y).trans (and_congr Iff.rfl ?_)⟩
  dsimp only [φ]
  rw [range_formula_l]
  rfl

/-- 按一个已有集合中的所有参数，精确收集其原像；没有多收集任意子类。 -/
theorem family_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f a p : carrier_l ℳ) :
    ∃ q, ∀ b, member_l ℳ b q ↔ ∃ r, member_l ℳ r p ∧ preimage_l f a r b := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases a (fun _ => f), free := fun _ => p }
  let φ : Formula ℒ [] [.set, .set, .set, .set] :=
    preimage_m (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  have h : ∀ r b, φ.satisfies (((PowerlessComprehension.env_l η).pushFree r).pushFree b) ↔
      preimage_l f a r b := by
    intro r b
    dsimp only [φ]
    rw [preimage_formula_l]
    rfl
  obtain ⟨q, hq⟩ := PowerlessComprehension.image_l hℳ φ η p
    (fun r _ => (preimage_exists_l hℳ f a r).imp fun b hb => (h r b).mpr hb)
    (fun r _ b c hb hc => preimage_unique_l hℳ ((h r b).mp hb) ((h r c).mp hc))
  exact ⟨q, fun b => (hq b).trans (exists_congr fun r => and_congr Iff.rfl (h r b))⟩

/-- 已有 P(W) 时，沿实际集合单射 A → W 构造 P(A)。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f a w p : carrier_l ℳ} (hf : ThirdOrderSemantics.map_l f a w)
    (h₁ : ThirdOrderSemantics.injective_l f) (hp : power_l w p) : ∃ q, power_l a q := by
  obtain ⟨q, hq⟩ := family_l hℳ f a p
  refine ⟨q, fun b => ?_⟩
  rw [hq b]
  constructor
  · rintro ⟨r, _, hb⟩
    exact fun x hx => ((hb x).mp hx).1
  · intro hb
    obtain ⟨r, hr⟩ := range_exists_l hℳ f w b
    refine ⟨r, (hp r).mpr (fun y hy => ((hr y).mp hy).1), fun x => ?_⟩
    constructor
    · intro hx
      obtain ⟨y, hy, _⟩ := hf.2 x (hb x hx)
      exact ⟨hb x hx, y, hy.2, (hr y).mpr ⟨hy.1, x, hx, hy.2⟩⟩
    · rintro ⟨_, y, hy, h₂⟩
      obtain ⟨z, hz, h₃⟩ := ((hr y).mp h₂).2
      have h₄ := h₁ x z y hy h₃
      exact h₄.symm ▸ hz

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPower
