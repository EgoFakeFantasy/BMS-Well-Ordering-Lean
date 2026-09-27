import BMSConstructibleBridge.PowerlessBMSRepresentationSyntax

/-!
# 原祖先行约束的纯公式

行数码 j 与稳定层数码 k 分别参数化，先证明通用语义，再代入重标号预算。
避免内核在语义证明中展开大型预算计算；数量词只遍历同一内部 ω。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationRows

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l

universe u

private abbrev context_m (Γ : SortContext ℒ) : SortContext ℒ := .set :: .set :: .set :: .set :: .set :: Γ

private def shift_m {Γ Δ : SortContext ℒ} (s : Term ℒ Γ Δ .set) : Term ℒ (context_m Γ) Δ .set :=
  ((((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set

def row_m {Γ Δ : SortContext ℒ} (j k : Nat)
    (ω e T t₁ t₂ t₃ x f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let r : Term ℒ (context_m Γ) Δ .set := .bvar (.there (.there (.there (.there .here))))
  let i : Term ℒ (context_m Γ) Δ .set := .bvar (.there (.there (.there .here)))
  let t : Term ℒ (context_m Γ) Δ .set := .bvar (.there (.there .here))
  let a : Term ℒ (context_m Γ) Δ .set := .bvar (.there .here)
  let b : Term ℒ (context_m Γ) Δ .set := .bvar .here
  let φ : Formula ℒ (context_m Γ) Δ :=
    .imp (SecondOrderObjectSyntax.member_m r (shift_m ω))
      (.imp (SecondOrderObjectSyntax.member_m i (shift_m ω))
        (.imp (SecondOrderObjectSyntax.member_m t (shift_m ω))
          (.imp (PowerlessNumeral.numeral_m j (shift_m e) r)
            (.imp (PowerlessBMSAncestor.ancestor_m (shift_m ω) (shift_m e) (shift_m x) r t i)
              (.imp (SecondOrderObjectSyntax.value_m (shift_m f) i a)
                (.imp (SecondOrderObjectSyntax.value_m (shift_m f) t b)
                  (PowerlessBMSRepresentationSyntax.stable_m k (shift_m ω) (shift_m e)
                    (shift_m T) (shift_m t₁) (shift_m t₂) (shift_m t₃) a b)))))))
  .forallE .set (.forallE .set (.forallE .set (.forallE .set (.forallE .set φ))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

def row_l (j k : Nat) (T t₁ t₂ t₃ f : carrier_l ℳ) (x : PowerlessArithmetic.num_l ω) : Prop :=
  ∀ r : PowerlessArithmetic.num_l ω, PowerlessNumeral.numeral_l e j r.val →
    ∀ i t : PowerlessArithmetic.num_l ω, PowerlessBMSAncestor.ancestor_l (he := he) (h₀ := h₀) (F := F) x r t i →
      ∀ a b, value_l f i.val a → value_l f t.val b →
        ∃ m, PowerlessNumeral.numeral_l e k m ∧ PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m a b

-- 查询正文只通过已证语义接口传输，不在外层联结词化简时重新展开整个原程序。
attribute [local irreducible] PowerlessBMSAncestor.ancestor_m

theorem row_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (j k : Nat)
    (w z T t₁ t₂ t₃ y f : Term ℒ Γ Δ .set) (x : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hy : y.eval η = x.val) :
    (row_m j k w z T t₁ t₂ t₃ y f).satisfies η ↔
      row_l (he := he) (h₀ := h₀) (F := F) j k
        (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (f.eval η) x := by
  have h (r i t : PowerlessArithmetic.num_l ω) (a b : carrier_l ℳ) :=
    PowerlessBMSAncestor.formula_l hℳ hω (he := he) (h₀ := h₀) (F := F)
      (((((η.pushBound r.val).pushBound i.val).pushBound t.val).pushBound a).pushBound b)
      (shift_m w) (shift_m z) (shift_m y) (.bvar (.there (.there (.there (.there .here)))))
      (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here)))) x r t i
      (by simpa only [shift_m, Term.eval_weakenBound] using hw)
      (by simpa only [shift_m, Term.eval_weakenBound] using hz)
      (by simpa only [shift_m, Term.eval_weakenBound] using hy) rfl rfl rfl
  simp only [row_m, row_l, Formula.satisfies, shift_m, SecondOrderObjectSyntax.member_m,
    Arguments.eval, PowerlessNumeral.formula_l, value_formula_l,
    PowerlessBMSRepresentationSyntax.stable_formula_l hℳ, Term.eval_weakenBound, hw, hz]
  constructor
  · intro h₁ r hr i t h₂ a b ha hb
    exact h₁ r.val i.val t.val a b r.property i.property t.property hr ((h r i t a b).mpr h₂) ha hb
  · intro h₁ r i t a b hr hi ht h₂ h₃ ha hb
    exact h₁ ⟨r, hr⟩ h₂ ⟨i, hi⟩ ⟨t, ht⟩ ((h ⟨r, hr⟩ ⟨i, hi⟩ ⟨t, ht⟩ a b).mp h₃) a b ha hb

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSRepresentationRows
