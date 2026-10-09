import BMSConstructibleBridge.PowerlessMemberBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import BMSConstructibleBridge.PowerlessSatisfactionNormalizedMatrix

/-! # 同一有限初等子域中的完整规范 Sat 矩阵

十二个原参数全部是绑定槽，原自由上下文不变。只在传递外层 W 使用
纯 Δ₀ 绝对性，再经有限元素性读回同一个 I 的实际成员结构；I 不须传递。
有限族同时保留存在矩阵与同一见证的完整正文，正文也经 W 绝对性
回到原模型；不从存在真值等价推出同见证正文等价。矩阵保留原 Seq
见证、完整有界 Sat 方程与无垃圾成员证书，不用较弱
的求值存在式替代。实际请求闭包及参数捕获由 SourceHistory 原推导提供；
本模块的元素性前提不能充当最终源存在性或完整 Def 截迹。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullSatisfaction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

/-- 绑定槽依次为 R/F/t₃/t₂/t₁/D/M/T/N/e/A/ω。 -/
abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]

def matrix_m (Δ : SortContext ℒ) : Formula ℒ context_m Δ :=
  PowerlessSatisfactionNormalizedMatrix.formula_m
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
    (.bvar (.there (.there (.there (.there (.there (.there (.here))))))))
    (.bvar (.there (.there (.there (.there (.there (.here)))))))
    (.bvar (.there (.there (.there (.there (.here))))))
    (.bvar (.there (.there (.there (.here)))))
    (.bvar (.there (.there (.here))))
    (.bvar (.there (.here)))
    (.bvar (.here))

/-- 新首槽 S 后仍是原十二个参数；保留 D 成员守卫和全部原正文。 -/
def body_m (Δ : SortContext ℒ) : Formula ℒ (.set :: context_m) Δ :=
  .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there (.there (.there (.there (.there (.here))))))))) <|
    .conj (PowerlessFiniteSequencesBounded.formula_m (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))
      (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) (.bvar (.there (.there (.there (.there (.there (.there (.there (.here))))))))) (.bvar .here)) <|
      .conj (PowerlessSatisfactionSpecificationBounded.spec_m
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
        (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))) (.bvar .here)
        (.bvar (.there (.there (.there (.there (.there (.here))))))) (.bvar (.there (.there (.there (.there (.here))))))
        (.bvar (.there (.there (.there (.here))))) (.bvar (.there (.there (.here)))) (.bvar (.there (.here))))
        (PowerlessSatisfactionGraphClean.formula_m
          (.bvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))) (.bvar .here) (.bvar (.there (.here))))

/-- 原规范矩阵逐字等于存在量词加完整正文，不改变见证规格。 -/
theorem matrix_exists_m (Δ : SortContext ℒ) :
    matrix_m Δ = .existsE .set (body_m Δ) := rfl

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk context_m (matrix_m Δ), Sigma.mk (.set :: context_m) (body_m Δ)]

theorem body_delta_l (Δ : SortContext ℒ) :
    Formula.IsDelta0 membershipLevyBound (body_m Δ) :=
  .conj (.rel _ _) <| .conj (PowerlessFiniteSequencesBounded.delta_l _ _ _ _) <|
    .conj (PowerlessSatisfactionSpecificationBounded.delta_l _ _ _ _ _ _ _ _ _ _ _)
      (PowerlessSatisfactionGraphClean.delta_l _ _ _)

theorem matrix_delta_l (Δ : SortContext ℒ) :
    Formula.IsDelta0 membershipLevyBound (matrix_m Δ) :=
  PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem matrix_formula_l {Δ : SortContext ℒ} (η : Env 𝒩 context_m Δ) :
    (matrix_m Δ).satisfies η ↔ PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩)
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.there (.here))))))))
      (η.boundVal (.there (.there (.there (.there (.there (.here)))))))
      (η.boundVal (.there (.there (.there (.there (.here))))))
      (η.boundVal (.there (.there (.there (.here)))))
      (η.boundVal (.there (.there (.here))))
      (η.boundVal (.there (.here)))
      (η.boundVal (.here)) := by
  rw [matrix_m, PowerlessSatisfactionNormalizedMatrix.formula_l]
  rfl

/-- 同一个 S 的原始正文读数；包含 D 成员性和三项完整有界规格。 -/
theorem body_formula_l {Δ : SortContext ℒ} (η : Env 𝒩 context_m Δ) (S : carrier_l 𝒩) :
    (body_m Δ).satisfies (η.pushBound S) ↔
      member_l 𝒩 S (η.boundVal (.there (.there (.there (.there (.there (.here))))))) ∧
      PowerlessFiniteSequencesBounded.holds_l (𝒩 := 𝒩)
        (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))) (η.boundVal (.there (.there (.there (.there (.there (.there (.here)))))))) S ∧
      PowerlessSatisfactionSpecificationBounded.spec_l (𝒩 := 𝒩)
        (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
        (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
        (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
        (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
        (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.here))))))))) S
        (η.boundVal (.there (.there (.there (.there (.here)))))) (η.boundVal (.there (.there (.there (.here)))))
        (η.boundVal (.there (.there (.here)))) (η.boundVal (.there (.here))) (η.boundVal (.here)) ∧
      PowerlessSatisfactionGraphClean.holds_l (𝒩 := 𝒩)
        (η.boundVal (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))) S (η.boundVal (.here)) := by
  simp only [body_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    PowerlessFiniteSequencesBounded.formula_l,
    PowerlessSatisfactionSpecificationBounded.spec_formula_l,
    PowerlessSatisfactionGraphClean.formula_l, Arguments.eval, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

/-- 外层绝对性加完整矩阵反射；绝不在非传递 I 上直接套绝对性。 -/
theorem reflect_l {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩 [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ : carrier_l 𝒩}
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hNonempty : ∃ x, member_l 𝒩 x W₀) (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (hFree : ∀ v : Variable Δ .set, member_l 𝒩 (ν.freeVal v) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (η : Env 𝒩 context_m Δ) (hη : ∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v)
    (hBound : ∀ v : Variable context_m .set, member_l 𝒩 (η.boundVal v) I₀) :
    (matrix_m Δ).satisfies η ↔
      (PowerlessRelativization.formula_m (matrix_m Δ)).satisfies (η.pushFree I₀) := by
  change (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧
    (PowerlessRelativeFiniteElementarity.entry_m (body_m Δ) I W τ).satisfies ζ ∧ True at h
  have hReflect := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (matrix_m Δ) ζ I W τ ν hτ).mp h.1 η hη (fun v => hI₀.symm ▸ hBound v)
  rw [hI₀, hW₀] at hReflect
  have hAbsolute := PowerlessMemberBounded.relativized_l hW hNonempty (matrix_delta_l Δ) η
    (fun v => hIW _ (hBound v)) (fun v => by
      rw [hη _ v]
      exact hIW _ (hFree v))
  exact hAbsolute.symm.trans hReflect

/-- 保持同一个 S 的完整正文真值；不从存在公式等价推出正文等价。 -/
theorem body_reflect_l {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩 [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ : carrier_l 𝒩}
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hNonempty : ∃ x, member_l 𝒩 x W₀) (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (hFree : ∀ v : Variable Δ .set, member_l 𝒩 (ν.freeVal v) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (η : Env 𝒩 (.set :: context_m) Δ) (hη : ∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v)
    (hBound : ∀ v : Variable (.set :: context_m) .set, member_l 𝒩 (η.boundVal v) I₀) :
    (body_m Δ).satisfies η ↔
      (PowerlessRelativization.formula_m (body_m Δ)).satisfies (η.pushFree I₀) := by
  change (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧
    (PowerlessRelativeFiniteElementarity.entry_m (body_m Δ) I W τ).satisfies ζ ∧ True at h
  have hReflect := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (body_m Δ) ζ I W τ ν hτ).mp h.2.1 η hη (fun v => hI₀.symm ▸ hBound v)
  rw [hI₀, hW₀] at hReflect
  have hAbsolute := PowerlessMemberBounded.relativized_l hW hNonempty (body_delta_l Δ) η
    (fun v => hIW _ (hBound v)) (fun v => by
      rw [hη _ v]
      exact hIW _ (hFree v))
  exact hAbsolute.symm.trans hReflect

/-- 原矩阵成立时，回收 I 内 S，并在原模型核验这个 S 的全部正文。 -/
theorem capture_l {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩 [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ : carrier_l 𝒩}
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hNonempty : ∃ x, member_l 𝒩 x W₀) (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (hFree : ∀ v : Variable Δ .set, member_l 𝒩 (ν.freeVal v) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (η : Env 𝒩 context_m Δ) (hη : ∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v)
    (hBound : ∀ v : Variable context_m .set, member_l 𝒩 (η.boundVal v) I₀)
    (hMatrix : (matrix_m Δ).satisfies η) :
    ∃ S, member_l 𝒩 S I₀ ∧ (body_m Δ).satisfies (η.pushBound S) := by
  have hInside := (reflect_l ζ I W τ ν hτ hI₀ hW₀ hW hNonempty hIW
    hFree h η hη hBound).mp hMatrix
  rw [matrix_exists_m] at hInside
  change ∃ S, member_l 𝒩 S I₀ ∧
    (PowerlessRelativization.formula_m (body_m Δ)).satisfies ((η.pushFree I₀).pushBound S) at hInside
  obtain ⟨S, hS, hBody⟩ := hInside
  have hPush : (η.pushFree I₀).pushBound S = (η.pushBound S).pushFree I₀ := by
    apply Env.ext
    · intro s v; cases s; cases v <;> rfl
    · intro s v; cases s; cases v <;> rfl
  rw [hPush] at hBody
  have hBound' : ∀ v : Variable (.set :: context_m) .set,
      member_l 𝒩 ((η.pushBound S).boundVal v) I₀ := by
    intro v
    cases v with
    | here => exact hS
    | there v => exact hBound v
  exact ⟨S, hS, (body_reflect_l ζ I W τ ν hτ hI₀ hW₀ hW hNonempty hIW
    hFree h (η.pushBound S) hη hBound').mpr hBody⟩

/-- 实际 MemberI 上的完整矩阵同值，包含 I 内的 Seq 存在见证。 -/
theorem model_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (η : Env (PowerlessMemberStructure.structure_l I₀ hI) context_m Δ)
    (hη : ∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v) :
    (matrix_m Δ).satisfies (PowerlessRelativization.env_l η) ↔ (matrix_m Δ).satisfies η := by
  have hNonempty : ∃ x, member_l 𝒩 x W₀ := by
    obtain ⟨x, hx⟩ := hI
    exact ⟨x, hIW x hx⟩
  exact (reflect_l ζ I W τ (PowerlessRelativization.env_l ν) hτ hI₀ hW₀ hW hNonempty
    hIW (fun v => (ν.freeVal v).property) h (PowerlessRelativization.env_l η)
    (fun s v => congrArg Subtype.val (hη s v)) (fun v => (η.boundVal v).property)).trans
      (PowerlessRelativization.formula_l (matrix_m Δ) η)

/-- 实际 MemberI 中任意同一见证的正文与原模型同值，不要求 I 传递。 -/
theorem body_model_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (η : Env (PowerlessMemberStructure.structure_l I₀ hI) (.set :: context_m) Δ)
    (hη : ∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v) :
    (body_m Δ).satisfies (PowerlessRelativization.env_l η) ↔ (body_m Δ).satisfies η := by
  have hNonempty : ∃ x, member_l 𝒩 x W₀ := by
    obtain ⟨x, hx⟩ := hI
    exact ⟨x, hIW x hx⟩
  exact (body_reflect_l ζ I W τ (PowerlessRelativization.env_l ν) hτ hI₀ hW₀ hW hNonempty
    hIW (fun v => (ν.freeVal v).property) h (PowerlessRelativization.env_l η)
    (fun s v => congrArg Subtype.val (hη s v)) (fun v => (η.boundVal v).property)).trans
      (PowerlessRelativization.formula_l (body_m Δ) η)

#print axioms matrix_exists_m
#print axioms body_formula_l
#print axioms body_model_l
#print axioms body_delta_l
#print axioms body_reflect_l
#print axioms capture_l
#print axioms matrix_delta_l
#print axioms matrix_formula_l
#print axioms reflect_l
#print axioms model_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullSatisfaction
