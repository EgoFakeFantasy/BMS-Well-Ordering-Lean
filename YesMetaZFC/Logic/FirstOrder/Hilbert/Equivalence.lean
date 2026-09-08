import YesMetaZFC.Logic.FirstOrder.Derivation

/-!
# 推导等价

推导等价只保存两个方向的蕴含。公式、上下文和量词体已经由内在语法保证良构，
因此本层不再携带 admissibility 结论、自然数 eigenvariable 或新鲜性旁条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 同一理论与局部上下文中的双向可推导关系。 -/
structure DerivationEquivalent
    {σ : Signature.{u, v, w}} {free : SortContext σ}
    (T : Theory σ) (Γ : Context σ free)
    (left right : OpenFormula σ free) : Prop where
  forward : Derives T Γ (.imp left right)
  backward : Derives T Γ (.imp right left)

namespace DerivationEquivalent

/-- 推导等价的自反性。 -/
theorem refl {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    (formula : OpenFormula σ free) :
    DerivationEquivalent T Γ formula formula :=
  ⟨Derives.Propositional.imp_refl formula,
    Derives.Propositional.imp_refl formula⟩

/-- 推导等价的对称性。 -/
theorem symm {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left right : OpenFormula σ free}
    (hEquivalent : DerivationEquivalent T Γ left right) :
    DerivationEquivalent T Γ right left :=
  ⟨hEquivalent.backward, hEquivalent.forward⟩

/-- 推导等价沿局部上下文包含关系单调。 -/
theorem context_weaken {σ : Signature.{u, v, w}}
    {free : SortContext σ} {T : Theory σ}
    {Γ Δ : Context σ free} {left right : OpenFormula σ free}
    (hSubset : ∀ formula, formula ∈ Γ → formula ∈ Δ)
    (hEquivalent : DerivationEquivalent T Γ left right) :
    DerivationEquivalent T Δ left right :=
  ⟨hEquivalent.forward.context_weaken hSubset,
    hEquivalent.backward.context_weaken hSubset⟩

/-- 推导等价沿理论扩张单调。 -/
theorem theory_weaken {σ : Signature.{u, v, w}}
    {free : SortContext σ} {T U : Theory σ}
    {Γ : Context σ free} {left right : OpenFormula σ free}
    (hTheory : Theory.Extends U T)
    (hEquivalent : DerivationEquivalent T Γ left right) :
    DerivationEquivalent U Γ left right :=
  ⟨hEquivalent.forward.theory_weaken hTheory,
    hEquivalent.backward.theory_weaken hTheory⟩

/-- 同时扩大理论与局部上下文。 -/
theorem monotone {σ : Signature.{u, v, w}}
    {free : SortContext σ} {T U : Theory σ}
    {Γ Δ : Context σ free} {left right : OpenFormula σ free}
    (hTheory : Theory.Extends U T)
    (hContext : ∀ formula, formula ∈ Γ → formula ∈ Δ)
    (hEquivalent : DerivationEquivalent T Γ left right) :
    DerivationEquivalent U Δ left right :=
  (hEquivalent.theory_weaken hTheory).context_weaken hContext

/-- 空理论、空上下文中的等价可用于任意背景。 -/
theorem of_empty {σ : Signature.{u, v, w}}
    {free : SortContext σ} {T : Theory σ} {Γ : Context σ free}
    {left right : OpenFormula σ free}
    (hEquivalent :
      DerivationEquivalent (Theory.empty : Theory σ) [] left right) :
    DerivationEquivalent T Γ left right :=
  hEquivalent.monotone
    (fun hTheory => False.elim hTheory)
    (by
      intro formula hMember
      simp at hMember)

/-- 推导等价的传递性。 -/
theorem trans {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left middle right : OpenFormula σ free}
    (hLeftMiddle : DerivationEquivalent T Γ left middle)
    (hMiddleRight : DerivationEquivalent T Γ middle right) :
    DerivationEquivalent T Γ left right :=
  ⟨hLeftMiddle.forward.imp_trans hMiddleRight.forward,
    hMiddleRight.backward.imp_trans hLeftMiddle.backward⟩

/-- 双向蕴含合成为原生双条件。 -/
theorem to_iff {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left right : OpenFormula σ free}
    (hEquivalent : DerivationEquivalent T Γ left right) :
    Derives T Γ (.iff left right) :=
  Derives.iff_intro
    (hEquivalent.forward.context_weaken_cons.imp_elim
      (Derives.assumption List.mem_cons_self))
    (hEquivalent.backward.context_weaken_cons.imp_elim
      (Derives.assumption List.mem_cons_self))

/-- 原生双条件展开为两个方向的蕴含。 -/
theorem of_iff {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left right : OpenFormula σ free}
    (hIff : Derives T Γ (.iff left right)) :
    DerivationEquivalent T Γ left right := by
  constructor
  · apply Derives.imp_intro
    exact Derives.iff_elim_left hIff.context_weaken_cons
      (Derives.assumption List.mem_cons_self)
  · apply Derives.imp_intro
    exact Derives.iff_elim_right hIff.context_weaken_cons
      (Derives.assumption List.mem_cons_self)

/-- 否定保持推导等价。 -/
theorem neg_congr {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left right : OpenFormula σ free}
    (hEquivalent : DerivationEquivalent T Γ left right) :
    DerivationEquivalent T Γ (.neg left) (.neg right) := by
  constructor
  · apply Derives.imp_intro
    apply Derives.neg_intro
    have hRight : Derives T (right :: .neg left :: Γ) right :=
      Derives.assumption List.mem_cons_self
    have hLeft :=
      (hEquivalent.backward.context_weaken_prefix
        (initial := [right, .neg left])).imp_elim hRight
    exact Derives.neg_elim hLeft
      (Derives.assumption (by simp))
  · apply Derives.imp_intro
    apply Derives.neg_intro
    have hLeft : Derives T (left :: .neg right :: Γ) left :=
      Derives.assumption List.mem_cons_self
    have hRight :=
      (hEquivalent.forward.context_weaken_prefix
        (initial := [left, .neg right])).imp_elim hLeft
    exact Derives.neg_elim hRight
      (Derives.assumption (by simp))

/-- 蕴含对前件反变、对后件协变。 -/
theorem imp_congr {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left₁ left₂ right₁ right₂ : OpenFormula σ free}
    (hLeft : DerivationEquivalent T Γ left₁ left₂)
    (hRight : DerivationEquivalent T Γ right₁ right₂) :
    DerivationEquivalent T Γ (.imp left₁ right₁) (.imp left₂ right₂) := by
  constructor
  · apply Derives.imp_intro
    apply Derives.imp_intro
    have hLeft₂ : Derives T (left₂ :: .imp left₁ right₁ :: Γ) left₂ :=
      Derives.assumption List.mem_cons_self
    have hLeft₁ :=
      (hLeft.backward.context_weaken_prefix
        (initial := [left₂, .imp left₁ right₁])).imp_elim hLeft₂
    have hRight₁ :=
      (Derives.assumption (by simp) :
        Derives T (left₂ :: .imp left₁ right₁ :: Γ) (.imp left₁ right₁)).imp_elim hLeft₁
    exact (hRight.forward.context_weaken_prefix
      (initial := [left₂, .imp left₁ right₁])).imp_elim hRight₁
  · apply Derives.imp_intro
    apply Derives.imp_intro
    have hLeft₁ : Derives T (left₁ :: .imp left₂ right₂ :: Γ) left₁ :=
      Derives.assumption List.mem_cons_self
    have hLeft₂ :=
      (hLeft.forward.context_weaken_prefix
        (initial := [left₁, .imp left₂ right₂])).imp_elim hLeft₁
    have hRight₂ :=
      (Derives.assumption (by simp) :
        Derives T (left₁ :: .imp left₂ right₂ :: Γ) (.imp left₂ right₂)).imp_elim hLeft₂
    exact (hRight.backward.context_weaken_prefix
      (initial := [left₁, .imp left₂ right₂])).imp_elim hRight₂

/-- 合取逐分量保持推导等价。 -/
theorem conj_congr {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left₁ left₂ right₁ right₂ : OpenFormula σ free}
    (hLeft : DerivationEquivalent T Γ left₁ left₂)
    (hRight : DerivationEquivalent T Γ right₁ right₂) :
    DerivationEquivalent T Γ (.conj left₁ right₁) (.conj left₂ right₂) := by
  constructor
  · apply Derives.imp_intro
    have hSource : Derives T (.conj left₁ right₁ :: Γ) (.conj left₁ right₁) :=
      Derives.assumption List.mem_cons_self
    exact Derives.conj_intro
      (hLeft.forward.context_weaken_cons.imp_elim hSource.conj_elim_left)
      (hRight.forward.context_weaken_cons.imp_elim hSource.conj_elim_right)
  · apply Derives.imp_intro
    have hSource : Derives T (.conj left₂ right₂ :: Γ) (.conj left₂ right₂) :=
      Derives.assumption List.mem_cons_self
    exact Derives.conj_intro
      (hLeft.backward.context_weaken_cons.imp_elim hSource.conj_elim_left)
      (hRight.backward.context_weaken_cons.imp_elim hSource.conj_elim_right)

/-- 析取逐分量保持推导等价。 -/
theorem disj_congr {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left₁ left₂ right₁ right₂ : OpenFormula σ free}
    (hLeft : DerivationEquivalent T Γ left₁ left₂)
    (hRight : DerivationEquivalent T Γ right₁ right₂) :
    DerivationEquivalent T Γ (.disj left₁ right₁) (.disj left₂ right₂) := by
  constructor
  · apply Derives.imp_intro
    apply Derives.disj_elim (Derives.assumption List.mem_cons_self)
    · exact Derives.disj_intro_left
        ((hLeft.forward.context_weaken_prefix
          (initial := [left₁, .disj left₁ right₁])).imp_elim
            (Derives.assumption List.mem_cons_self))
    · exact Derives.disj_intro_right
        ((hRight.forward.context_weaken_prefix
          (initial := [right₁, .disj left₁ right₁])).imp_elim
            (Derives.assumption List.mem_cons_self))
  · apply Derives.imp_intro
    apply Derives.disj_elim (Derives.assumption List.mem_cons_self)
    · exact Derives.disj_intro_left
        ((hLeft.backward.context_weaken_prefix
          (initial := [left₂, .disj left₂ right₂])).imp_elim
            (Derives.assumption List.mem_cons_self))
    · exact Derives.disj_intro_right
        ((hRight.backward.context_weaken_prefix
          (initial := [right₂, .disj left₂ right₂])).imp_elim
            (Derives.assumption List.mem_cons_self))

/-- 双条件等价于两个方向蕴含的合取。 -/
theorem iff_conjunction {σ : Signature.{u, v, w}}
    {free : SortContext σ} {T : Theory σ} {Γ : Context σ free}
    (left right : OpenFormula σ free) :
    DerivationEquivalent T Γ (.iff left right)
      (.conj (.imp left right) (.imp right left)) := by
  constructor
  · apply Derives.imp_intro
    have hIff : Derives T (.iff left right :: Γ) (.iff left right) :=
      Derives.assumption List.mem_cons_self
    have hDirections := of_iff hIff
    exact Derives.conj_intro hDirections.forward hDirections.backward
  · apply Derives.imp_intro
    have hConjunction : Derives T
        (.conj (.imp left right) (.imp right left) :: Γ)
        (.conj (.imp left right) (.imp right left)) :=
      Derives.assumption List.mem_cons_self
    apply Derives.iff_intro
    · exact hConjunction.conj_elim_left.context_weaken_cons.imp_elim
        (Derives.assumption List.mem_cons_self)
    · exact hConjunction.conj_elim_right.context_weaken_cons.imp_elim
        (Derives.assumption List.mem_cons_self)

/-- 双条件逐分量保持推导等价。 -/
theorem iff_congr {σ : Signature.{u, v, w}} {free : SortContext σ}
    {T : Theory σ} {Γ : Context σ free}
    {left₁ left₂ right₁ right₂ : OpenFormula σ free}
    (hLeft : DerivationEquivalent T Γ left₁ left₂)
    (hRight : DerivationEquivalent T Γ right₁ right₂) :
    DerivationEquivalent T Γ (.iff left₁ right₁) (.iff left₂ right₂) :=
  (iff_conjunction left₁ right₁).trans
    ((imp_congr hLeft hRight).conj_congr (imp_congr hRight hLeft) |>.trans
      (iff_conjunction left₂ right₂).symm)

end DerivationEquivalent
end FirstOrder
end Logic
end YesMetaZFC
