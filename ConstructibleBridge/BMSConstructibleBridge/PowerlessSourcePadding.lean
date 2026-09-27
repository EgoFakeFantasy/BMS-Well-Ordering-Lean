import BMSConstructibleBridge.PowerlessSourceParameters

/-!
# 类模型所用固定参数的原语法扩充

七个新增自由槽依次为输入集合、三个标签、三角数图、空集和 ω；
原自由参数保持在尾部，所有绑定槽保持原序。这里的七是实际
参数个数，不是公式复杂度护栏，也不是内部自然数的标准性假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePadding

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def form_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    Formula ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) :=
  ((((((φ.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenFree
    SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenFree
      SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

def env_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ A : carrier_l ℳ) :
    Env ℳ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) :=
  ((((((η.pushFree ω).pushFree e).pushFree T).pushFree t₁).pushFree t₂).pushFree t₃).pushFree A

def omega_m {Γ Δ : SortContext ℒ} :
    Term ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) .set :=
  .fvar (.there (.there (.there (.there (.there (.there .here))))))

def zero_m {Γ Δ : SortContext ℒ} :
    Term ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) .set :=
  .fvar (.there (.there (.there (.there (.there .here)))))

def triangle_m {Γ Δ : SortContext ℒ} :
    Term ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) .set :=
  .fvar (.there (.there (.there (.there .here))))

def tag₁_m {Γ Δ : SortContext ℒ} :
    Term ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) .set :=
  .fvar (.there (.there (.there .here)))

def tag₂_m {Γ Δ : SortContext ℒ} :
    Term ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) .set :=
  .fvar (.there (.there .here))

def tag₃_m {Γ Δ : SortContext ℒ} :
    Term ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) .set :=
  .fvar (.there .here)

def set_m {Γ Δ : SortContext ℒ} :
    Term ℒ Γ (.set :: .set :: .set :: .set :: .set :: .set :: .set :: Δ) .set :=
  .fvar .here

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ A : carrier_l ℳ) :
    (form_m φ).satisfies (env_l η ω e T t₁ t₂ t₃ A) ↔ φ.satisfies η := by
  simp only [form_m, env_l, Formula.satisfies_weakenFree]

theorem push_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ A x : carrier_l ℳ) :
    env_l (η.pushBound (sort := SetTheory.SetSort.set) x) ω e T t₁ t₂ t₃ A =
      (env_l η ω e T t₁ t₂ t₃ A).pushBound (sort := SetTheory.SetSort.set) x := rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourcePadding

