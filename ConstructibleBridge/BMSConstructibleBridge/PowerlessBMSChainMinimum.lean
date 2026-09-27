import BMSConstructibleBridge.PowerlessBMSRepresentationFormula
import BMSConstructibleBridge.PowerlessOrdinalMinimum
import BMSConstructibleBridge.PowerlessSourceParameters

/-!
# 原链条目的最小表示上界

固定全部标签背景参数，在同一个内部链图的全部条目之间最小化表示上界。
候选性质是实际纯公式，数码见证均由内部 ω 限制；完整表示仍包含宽度、
标签、严格序和全部指定行的原祖先边。最小元来自内部分离与正则性，
不先选择一条外部或内部的标签下降序列。

末尾只排除满足给定真实下降契约的链图。它不提供展开下降契约，
也不把 PowerlessTheory 下的结论当作 Z₂ 强度消去。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSChainMinimum

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private def weaken₄_m {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :
    Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
  (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set

/-- 四个见证依次为链位置、原数组码、原宽度和完整标签图。 -/
def represented_m {Γ Δ : SortContext ℒ} (H : Nat)
    (ω e T t₁ t₂ t₃ c N G β : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.existsE .set (.existsE .set (.existsE .set
    (.conj (SecondOrderObjectSyntax.member_m
      (.bvar (.there (.there (.there .here)))) (weaken₄_m ω))
      (.conj (SecondOrderObjectSyntax.member_m
        (.bvar (.there (.there .here))) (weaken₄_m ω))
        (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (weaken₄_m ω))
          (.conj (SecondOrderObjectSyntax.value_m (weaken₄_m G)
            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
            (PowerlessBMSRepresentationFormula.representation_m H
              (weaken₄_m ω) (weaken₄_m e) (weaken₄_m T) (weaken₄_m t₁)
              (weaken₄_m t₂) (weaken₄_m t₃) (weaken₄_m c) (weaken₄_m N)
              (.bvar (.there (.there .here))) (.bvar (.there .here))
              (weaken₄_m β) (.bvar .here)))))))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

/-- 不限制链位置或数组码为外部标准数，也不缩减完整表示的任何一项。 -/
def represented_l (T t₁ t₂ t₃ c N : carrier_l ℳ) (H : Nat) (G β : carrier_l ℳ) : Prop :=
  ∃ i x q : PowerlessArithmetic.num_l ω, ∃ f,
    value_l G i.val x.val ∧
      PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H x q β f

/-- 纯公式与同一内部链图上的完整表示存在性逐项等价。 -/
theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H : Nat)
    (w z T t₁ t₂ t₃ c N G β : Term ℒ Γ Δ .set)
    (hw : w.eval η = ω) (hz : z.eval η = e) :
    (represented_m H w z T t₁ t₂ t₃ c N G β).satisfies η ↔
      represented_l (he := he) (h₀ := h₀) (F := F)
        (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) (N.eval η)
        H (G.eval η) (β.eval η) := by
  have hrep (i : carrier_l ℳ) (x q : PowerlessArithmetic.num_l ω) (f : carrier_l ℳ) :
      (PowerlessBMSRepresentationFormula.representation_m H
        (weaken₄_m w) (weaken₄_m z) (weaken₄_m T) (weaken₄_m t₁)
        (weaken₄_m t₂) (weaken₄_m t₃) (weaken₄_m c) (weaken₄_m N)
        (.bvar (.there (.there .here))) (.bvar (.there .here))
        (weaken₄_m β) (.bvar .here)).satisfies
          ((((η.pushBound i).pushBound x.val).pushBound q.val).pushBound f) ↔
        PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
          (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) (N.eval η)
          H x q (β.eval η) f := by
    rw [PowerlessBMSRepresentationFormula.formula_l hℳ hω (he := he) (h₀ := h₀) (F := F)
        ((((η.pushBound i).pushBound x.val).pushBound q.val).pushBound f) H
        (weaken₄_m w) (weaken₄_m z) (weaken₄_m T) (weaken₄_m t₁)
        (weaken₄_m t₂) (weaken₄_m t₃) (weaken₄_m c) (weaken₄_m N)
        (.bvar (.there (.there .here))) (.bvar (.there .here))
        (weaken₄_m β) (.bvar .here) x q
        (by simpa only [weaken₄_m, Term.eval_weakenBound] using hw)
        (by simpa only [weaken₄_m, Term.eval_weakenBound] using hz) rfl rfl]
    simp only [weaken₄_m, Term.eval_weakenBound]
    rfl
  simp only [represented_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, value_formula_l, weaken₄_m, Term.eval_weakenBound, hw]
  constructor
  · rintro ⟨i, x, q, f, hi, hx, hq, hG, hf⟩
    exact ⟨⟨i, hi⟩, ⟨x, hx⟩, ⟨q, hq⟩, f, hG, (hrep i ⟨x, hx⟩ ⟨q, hq⟩ f).mp hf⟩
  · rintro ⟨i, x, q, f, hG, hf⟩
    exact ⟨i.val, x.val, q.val, f, i.property, x.property, q.property,
      hG, (hrep i.val x q f).mpr hf⟩

/-- 同一链的可表示条目中，序数上界最小；其以下不再存在任何可表示条目。 -/
def minimum_l (T t₁ t₂ t₃ c N : carrier_l ℳ) (H : Nat) (G β : carrier_l ℳ) : Prop :=
  PowerlessOrdinal.ordinal_l β ∧
    represented_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H G β ∧
      ∀ α, member_l ℳ α β →
        ¬represented_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H G α

/-- 一个序数上界见证足以取到全局最小上界；背景参数和链图始终固定。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {T t₁ t₂ t₃ c N G : carrier_l ℳ} {H : Nat}
    (h : ∃ β, PowerlessOrdinal.ordinal_l β ∧
      represented_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H G β) :
    ∃ β, minimum_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H G β := by
  let Δ : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set]
  let η : Env ℳ [] Δ :=
    (((((((((Env.empty (M := ℳ)).pushFree ω).pushFree e).pushFree T).pushFree t₁).pushFree t₂).pushFree
      t₃).pushFree c).pushFree N).pushFree G
  let φ : Formula ℒ [] (.set :: Δ) := represented_m H
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hφ (β : carrier_l ℳ) : φ.satisfies (η.pushFree β) ↔
      represented_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H G β := by
    exact formula_l hℳ hω (he := he) (h₀ := h₀) (F := F)
      (η.pushFree β) H _ _ _ _ _ _ _ _ _ _ rfl rfl
  obtain ⟨ξ, hξ⟩ := PowerlessSourceParameters.env_exists_l η
  obtain ⟨β, hβ, hrep⟩ := h
  have hsat : ∃ β, PowerlessOrdinal.ordinal_l β ∧
      φ.satisfies ((PowerlessComprehension.env_l ξ).pushFree β) := by
    rw [hξ]
    exact ⟨β, hβ, (hφ β).mpr hrep⟩
  obtain ⟨α, hα⟩ := PowerlessOrdinalMinimum.exists_l hℳ φ ξ hsat
  rw [hξ] at hα
  exact ⟨α, hα.1, (hφ α).mp hα.2.1, fun γ hγ hrep => hα.2.2 γ hγ ((hφ γ).mpr hrep)⟩

/-- 每个可表示条目都产生同一链中的严格更小上界表示时，链不可能存在。
图的函数性不是本最小化步骤所需的额外假设；实际链构造在调用处提供它。
-/
theorem no_chain_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {T t₁ t₂ t₃ c N G : carrier_l ℳ} {H : Nat}
    (hinit : ∃ β, PowerlessOrdinal.ordinal_l β ∧
      represented_l (he := he) (h₀ := h₀) (F := F) T t₁ t₂ t₃ c N H G β)
    (hstep : ∀ (i x q : PowerlessArithmetic.num_l ω) (β f : carrier_l ℳ),
      value_l G i.val x.val →
      PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
        T t₁ t₂ t₃ c N H x q β f →
      ∃ j y r : PowerlessArithmetic.num_l ω, ∃ α g,
        value_l G j.val y.val ∧ member_l ℳ α β ∧
          PowerlessBMSRepresentation.representation_l (he := he) (h₀ := h₀) (F := F)
            T t₁ t₂ t₃ c N H y r α g) : False := by
  obtain ⟨β, _, hrep, hbelow⟩ := exists_l hℳ hω hinit
  obtain ⟨i, x, q, f, hi, hf⟩ := hrep
  obtain ⟨j, y, r, α, g, hj, hα, hg⟩ := hstep i x q β f hi hf
  exact hbelow α hα ⟨j, y, r, g, hj, hg⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSChainMinimum
