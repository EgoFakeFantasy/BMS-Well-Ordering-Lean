import BMSConstructibleBridge.SecondOrderArithmetic

/-!
# 纯二阶语言在替换下的封闭性

模板实例化必须保持语言检查，才可进入对象理解及归纳模式。这里检查实际
替换像，并沿所有语法构造递归，尤其同时覆盖数和集合量词的捕获避免提升。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubstitution

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

mutual
  theorem term_weaken_m {Γ Δ : SortContext signature_m} {s : sort_m}
      (t : Term signature_m Γ Δ s) (r : sort_m) :
      pure_term_m (t.weakenBound r) = pure_term_m t :=
    match t with
    | .bvar _ | .fvar _ => rfl
    | .app f a => by
        rw [Term.weakenBound_app]
        simp only [pure_term_m, args_weaken_m a r]

  theorem args_weaken_m {Γ Δ : SortContext signature_m} {s : List sort_m}
      (a : Arguments signature_m Γ Δ s) (r : sort_m) :
      pure_args_m (a.weakenBound r) = pure_args_m a :=
    match a with
    | .nil => rfl
    | .cons t a => by
        rw [Arguments.weakenBound_cons]
        simp only [pure_args_m, term_weaken_m t r, args_weaken_m a r]
end

/-- 每个变量的替换像均属于纯语言；不要求像必须是变量。 -/
def images_m {Γ Θ Ξ : SortContext signature_m}
    (ρ : VariableSubstitution signature_m Γ Θ Ξ) : Prop :=
  ∀ {s} (v : Variable Γ s), pure_term_m (ρ v) = true

theorem weaken_m {Γ Θ Ξ : SortContext signature_m}
    (ρ : VariableSubstitution signature_m Γ Θ Ξ) (h : images_m ρ) (s : sort_m) :
    images_m (VariableSubstitution.weakenBound s ρ) := by
  intro r v
  exact (term_weaken_m (ρ v) s).trans (h v)

theorem lift_m {Γ Θ Ξ : SortContext signature_m}
    (ρ : VariableSubstitution signature_m Γ Θ Ξ) (h : images_m ρ) (s : sort_m) :
    images_m (VariableSubstitution.liftBound s ρ) := by
  intro r v
  cases v with
  | here => rfl
  | there v => exact (term_weaken_m (ρ v) s).trans (h v)

mutual
  theorem term_subst_m {Γ Δ Θ Ξ : SortContext signature_m} {s : sort_m}
      (t : Term signature_m Γ Δ s)
      (ρ : VariableSubstitution signature_m Γ Θ Ξ)
      (τ : VariableSubstitution signature_m Δ Θ Ξ) (hρ : images_m ρ) (hτ : images_m τ) :
      pure_term_m (t.substituteMapped ρ τ) = pure_term_m t :=
    match t with
    | .bvar v => hρ v
    | .fvar v => hτ v
    | .app f a => by
        simp only [Term.substituteMapped, pure_term_m, args_subst_m a ρ τ hρ hτ]

  theorem args_subst_m {Γ Δ Θ Ξ : SortContext signature_m} {s : List sort_m}
      (a : Arguments signature_m Γ Δ s)
      (ρ : VariableSubstitution signature_m Γ Θ Ξ)
      (τ : VariableSubstitution signature_m Δ Θ Ξ) (hρ : images_m ρ) (hτ : images_m τ) :
      pure_args_m (a.substituteMapped ρ τ) = pure_args_m a :=
    match a with
    | .nil => rfl
    | .cons t a => by
        simp only [Arguments.substituteMapped, pure_args_m,
          term_subst_m t ρ τ hρ hτ, args_subst_m a ρ τ hρ hτ]
end

/-- 纯替换不改变任意公式的完整二阶语言检查结果。 -/
theorem form_subst_m {Γ Δ Θ Ξ : SortContext signature_m} (φ : Formula signature_m Γ Δ)
    (ρ : VariableSubstitution signature_m Γ Θ Ξ)
    (τ : VariableSubstitution signature_m Δ Θ Ξ) (hρ : images_m ρ) (hτ : images_m τ) :
    language_m (φ.substituteMapped ρ τ) = language_m φ :=
  match φ with
  | .falsum | .truth => rfl
  | .rel r a => by
      cases r <;> simp only [Formula.substituteMapped, language_m, args_subst_m a ρ τ hρ hτ]
  | .equal s t => by
      simp only [Formula.substituteMapped, language_m,
        term_subst_m s ρ τ hρ hτ, term_subst_m t ρ τ hρ hτ]
  | .neg φ => by
      simp only [Formula.substituteMapped, language_m, form_subst_m φ ρ τ hρ hτ]
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ => by
      simp only [Formula.substituteMapped, language_m,
        form_subst_m φ ρ τ hρ hτ, form_subst_m ψ ρ τ hρ hτ]
  | .forallE s φ | .existsE s φ => by
      simp only [Formula.substituteMapped, language_m,
        form_subst_m φ _ _ (lift_m ρ hρ s) (weaken_m τ hτ s)]
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderSubstitution
