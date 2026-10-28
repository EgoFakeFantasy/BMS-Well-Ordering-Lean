import BMSConstructibleBridge.SecondOrderPureTransfer
import BMSConstructibleBridge.SecondOrderArithmetic

/-!
# 全二阶算术语言的跨结构真值保持

沿用旧数域同构和成员对应，另以 Prop 证书要求集合对应双向全域且单值。
因此允许任意集合量词及集合等式；不抽取集合域的 Type 层选择函数。
旧的纯矩阵接口及其签名保持不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFullTransfer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderPureTransfer

set_option autoImplicit false

universe u v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {𝒩 : FirstOrder.Structure.{0, 0, 0, v} signature_m}

structure coverage_l (C : correspondence_l (M := ℳ) (N := 𝒩)) : Prop where
  left_total : ∀ A, ∃ B, C.setRel_l A B
  right_total : ∀ B, ∃ A, C.setRel_l A B
  left_unique : ∀ {A A' B}, C.setRel_l A B → C.setRel_l A' B → A = A'
  right_unique : ∀ {A B B'}, C.setRel_l A B → C.setRel_l A B' → B = B'

theorem push_set_l {Γ Δ : SortContext signature_m} (C : correspondence_l (M := ℳ) (N := 𝒩))
    (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ) (hη : environments_related_l C η ξ)
    {A : ℳ.Carrier .set} {B : 𝒩.Carrier .set} (hAB : C.setRel_l A B) :
    environments_related_l C (η.pushBound A) (ξ.pushBound B) := by
  refine ⟨?_, hη.2⟩
  intro s w
  cases w with
  | here => exact hAB
  | there w => exact hη.1 w

theorem formula_l {Γ Δ : SortContext signature_m} (C : correspondence_l (M := ℳ) (N := 𝒩))
    (hC : coverage_l C) (φ : Formula signature_m Γ Δ) (hφ : language_m φ = true)
    (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ) (hη : environments_related_l C η ξ) :
    φ.satisfies η ↔ φ.satisfies ξ := by
  match φ with
  | .falsum | .truth => rfl
  | .rel .mem (.cons n (.cons A .nil)) =>
      exact SecondOrderPureTransfer.formula_l C
        (.rel .mem (.cons n (.cons A .nil))) hφ η ξ hη
  | .rel .start _ | .rel .step _ => simp [language_m] at hφ
  | .equal (sort := .num) a b =>
      exact SecondOrderPureTransfer.formula_l C (.equal a b) hφ η ξ hη
  | .equal (sort := .set) a b =>
      have ht : pure_term_m a = true ∧ pure_term_m b = true := by simpa [language_m] using hφ
      have ha := SecondOrderPureTransfer.term_l C a η ξ hη ht.1
      have hb := SecondOrderPureTransfer.term_l C b η ξ hη ht.2
      change C.setRel_l (a.eval η) (a.eval ξ) at ha
      change C.setRel_l (b.eval η) (b.eval ξ) at hb
      change a.eval η = b.eval η ↔ a.eval ξ = b.eval ξ
      exact ⟨fun h => hC.right_unique (h ▸ ha) hb, fun h => hC.left_unique (h ▸ ha) hb⟩
  | .neg ψ => exact not_congr (formula_l C hC ψ hφ η ξ hη)
  | .conj ψ χ =>
      have h : language_m ψ = true ∧ language_m χ = true := by simpa [language_m] using hφ
      exact and_congr (formula_l C hC ψ h.1 η ξ hη) (formula_l C hC χ h.2 η ξ hη)
  | .disj ψ χ =>
      have h : language_m ψ = true ∧ language_m χ = true := by simpa [language_m] using hφ
      exact or_congr (formula_l C hC ψ h.1 η ξ hη) (formula_l C hC χ h.2 η ξ hη)
  | .imp ψ χ =>
      have h : language_m ψ = true ∧ language_m χ = true := by simpa [language_m] using hφ
      exact imp_congr (formula_l C hC ψ h.1 η ξ hη) (formula_l C hC χ h.2 η ξ hη)
  | .iff ψ χ =>
      have h : language_m ψ = true ∧ language_m χ = true := by simpa [language_m] using hφ
      exact iff_congr (formula_l C hC ψ h.1 η ξ hη) (formula_l C hC χ h.2 η ξ hη)
  | .forallE .num ψ =>
      constructor
      · intro h b
        have hEnv := push_number_l C η ξ hη (C.numberEquiv_l.symm b)
        have hBody := (formula_l C hC ψ hφ _ _ hEnv).mp (h (C.numberEquiv_l.symm b))
        simpa only [Equiv.apply_symm_apply] using hBody
      · intro h a
        exact (formula_l C hC ψ hφ _ _ (push_number_l C η ξ hη a)).mpr (h (C.numberEquiv_l a))
  | .existsE .num ψ =>
      constructor
      · rintro ⟨a, h⟩
        exact ⟨C.numberEquiv_l a, (formula_l C hC ψ hφ _ _ (push_number_l C η ξ hη a)).mp h⟩
      · rintro ⟨b, h⟩
        refine ⟨C.numberEquiv_l.symm b, ?_⟩
        apply (formula_l C hC ψ hφ _ _ (push_number_l C η ξ hη (C.numberEquiv_l.symm b))).mpr
        simpa only [Equiv.apply_symm_apply] using h
  | .forallE .set ψ =>
      constructor
      · intro h B
        obtain ⟨A, hAB⟩ := hC.right_total B
        exact (formula_l C hC ψ hφ _ _ (push_set_l C η ξ hη hAB)).mp (h A)
      · intro h A
        obtain ⟨B, hAB⟩ := hC.left_total A
        exact (formula_l C hC ψ hφ _ _ (push_set_l C η ξ hη hAB)).mpr (h B)
  | .existsE .set ψ =>
      constructor
      · rintro ⟨A, h⟩
        obtain ⟨B, hAB⟩ := hC.left_total A
        exact ⟨B, (formula_l C hC ψ hφ _ _ (push_set_l C η ξ hη hAB)).mp h⟩
      · rintro ⟨B, h⟩
        obtain ⟨A, hAB⟩ := hC.right_total B
        exact ⟨A, (formula_l C hC ψ hφ _ _ (push_set_l C η ξ hη hAB)).mpr h⟩
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFullTransfer
