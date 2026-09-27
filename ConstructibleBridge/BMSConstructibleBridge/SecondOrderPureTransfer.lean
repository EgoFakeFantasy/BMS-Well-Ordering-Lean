import BMSConstructibleBridge.SecondOrderSyntax

/-!
# 纯算术公式的跨模型真值保持

该矩阵可以在不同的二阶算术结构之间转移，但要求数域由保零、后继、加乘的同构
对应，集合域的相关元素按数的成员关系对应。公式中的集合量词、集合等式、配对及
额外程序关系都被 `pure_m` 排除，因此数域量词可沿同构双向搬运。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPureTransfer

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

universe u v

variable {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {N : FirstOrder.Structure.{0, 0, 0, v} signature_m}

/-- 数域同构与所需集合成员关系的双模型对应。 -/
structure correspondence_l where
  numberEquiv_l : M.Carrier .num ≃ N.Carrier .num
  setRel_l : M.Carrier .set → N.Carrier .set → Prop
  zero_l : numberEquiv_l (M.funcInterp .zero .nil) = N.funcInterp .zero .nil
  succ_l : ∀ a,
    numberEquiv_l (M.funcInterp .succ (.cons a .nil)) =
      N.funcInterp .succ (.cons (numberEquiv_l a) .nil)
  add_l : ∀ a b,
    numberEquiv_l (M.funcInterp .add (.cons a (.cons b .nil))) =
      N.funcInterp .add (.cons (numberEquiv_l a) (.cons (numberEquiv_l b) .nil))
  mul_l : ∀ a b,
    numberEquiv_l (M.funcInterp .mul (.cons a (.cons b .nil))) =
      N.funcInterp .mul (.cons (numberEquiv_l a) (.cons (numberEquiv_l b) .nil))
  member_iff_l : ∀ a A B, setRel_l A B →
    (M.relInterp .mem (.cons a (.cons A .nil)) ↔
      N.relInterp .mem (.cons (numberEquiv_l a) (.cons B .nil)))

namespace correspondence_l

/-- 对两排序载体的逐项对应关系。 -/
def value_related_l (C : correspondence_l (M := M) (N := N)) {s : sort_m}
    (a : M.Carrier s) (b : N.Carrier s) : Prop :=
  match s with
  | .num => C.numberEquiv_l a = b
  | .set => C.setRel_l a b

/-- 异质参数列按各自的语义排序逐项对应。 -/
def values_related_l (C : correspondence_l (M := M) (N := N)) {sorts : List sort_m} :
    FirstOrder.Values M.Carrier sorts → FirstOrder.Values N.Carrier sorts → Prop
  | .nil, .nil => True
  | .cons a as, .cons b bs =>
      C.value_related_l a b ∧ correspondence_l.values_related_l C as bs

end correspondence_l

/-- bound/free 环境逐个数值按同构对应、集合变量按成员关系对应。 -/
def environments_related_l {Γ Δ : SortContext signature_m}
    (C : correspondence_l (M := M) (N := N))
    (η : Env M Γ Δ) (ξ : Env N Γ Δ) : Prop :=
  (∀ {s : sort_m} (entry : Variable Γ s),
    C.value_related_l (η.boundVal entry) (ξ.boundVal entry)) ∧
  (∀ {s : sort_m} (entry : Variable Δ s),
    C.value_related_l (η.freeVal entry) (ξ.freeVal entry))

/-- 加入一对由数同构对应的绑定数值后，环境关系继续成立。 -/
theorem push_number_l {Γ Δ : SortContext signature_m}
    (C : correspondence_l (M := M) (N := N))
    (η : Env M Γ Δ) (ξ : Env N Γ Δ)
    (hη : environments_related_l C η ξ) (a : M.Carrier .num) :
    environments_related_l C (η.pushBound a) (ξ.pushBound (C.numberEquiv_l a)) := by
  rcases hη with ⟨hBound, hFree⟩
  constructor
  · intro s entry
    cases entry with
    | here => rfl
    | there entry => exact hBound entry
  · exact hFree

mutual

/-- 纯项在跨模型环境中的值由数同构或集合关系对应。 -/
theorem term_l {Γ Δ : SortContext signature_m} {s : sort_m}
    (C : correspondence_l (M := M) (N := N))
    (t : Term signature_m Γ Δ s) (η : Env M Γ Δ) (ξ : Env N Γ Δ)
    (hη : environments_related_l C η ξ)
    (ht : pure_term_m t = true) :
    C.value_related_l (Term.eval η t) (Term.eval ξ t) :=
  match t with
  | .bvar entry => hη.1 entry
  | .fvar entry => hη.2 entry
  | .app func_m.zero .nil => C.zero_l
  | .app func_m.succ (.cons n .nil) => by
      have hn : pure_term_m n = true := by
        simpa [pure_term_m, pure_args_m] using ht
      have hn' := term_l C n η ξ hη hn
      change C.numberEquiv_l
          (M.funcInterp .succ (.cons (Term.eval η n) .nil)) =
        N.funcInterp .succ (.cons (Term.eval ξ n) .nil)
      change C.numberEquiv_l (Term.eval η n) = Term.eval ξ n at hn'
      calc
        C.numberEquiv_l
            (M.funcInterp .succ (.cons (Term.eval η n) .nil)) =
            N.funcInterp .succ (.cons (C.numberEquiv_l (Term.eval η n)) .nil) :=
              C.succ_l (Term.eval η n)
        _ = N.funcInterp .succ (.cons (Term.eval ξ n) .nil) := by rw [hn']
  | .app func_m.add (.cons a (.cons b .nil)) => by
      have hab : pure_term_m a = true ∧ pure_term_m b = true := by
        simpa [pure_term_m, pure_args_m] using ht
      have ha := term_l C a η ξ hη hab.1
      have hb := term_l C b η ξ hη hab.2
      change C.numberEquiv_l
          (M.funcInterp .add (.cons (Term.eval η a) (.cons (Term.eval η b) .nil))) =
        N.funcInterp .add (.cons (Term.eval ξ a) (.cons (Term.eval ξ b) .nil))
      change C.numberEquiv_l (Term.eval η a) = Term.eval ξ a at ha
      change C.numberEquiv_l (Term.eval η b) = Term.eval ξ b at hb
      calc
        C.numberEquiv_l
            (M.funcInterp .add (.cons (Term.eval η a) (.cons (Term.eval η b) .nil))) =
            N.funcInterp .add
              (.cons (C.numberEquiv_l (Term.eval η a))
                (.cons (C.numberEquiv_l (Term.eval η b)) .nil)) :=
              C.add_l (Term.eval η a) (Term.eval η b)
        _ = N.funcInterp .add (.cons (Term.eval ξ a) (.cons (Term.eval ξ b) .nil)) := by
          rw [ha, hb]
  | .app func_m.mul (.cons a (.cons b .nil)) => by
      have hab : pure_term_m a = true ∧ pure_term_m b = true := by
        simpa [pure_term_m, pure_args_m] using ht
      have ha := term_l C a η ξ hη hab.1
      have hb := term_l C b η ξ hη hab.2
      change C.numberEquiv_l
          (M.funcInterp .mul (.cons (Term.eval η a) (.cons (Term.eval η b) .nil))) =
        N.funcInterp .mul (.cons (Term.eval ξ a) (.cons (Term.eval ξ b) .nil))
      change C.numberEquiv_l (Term.eval η a) = Term.eval ξ a at ha
      change C.numberEquiv_l (Term.eval η b) = Term.eval ξ b at hb
      calc
        C.numberEquiv_l
            (M.funcInterp .mul (.cons (Term.eval η a) (.cons (Term.eval η b) .nil))) =
            N.funcInterp .mul
              (.cons (C.numberEquiv_l (Term.eval η a))
                (.cons (C.numberEquiv_l (Term.eval η b)) .nil)) :=
              C.mul_l (Term.eval η a) (Term.eval η b)
        _ = N.funcInterp .mul (.cons (Term.eval ξ a) (.cons (Term.eval ξ b) .nil)) := by
          rw [ha, hb]
  | .app func_m.pair args => by simp [pure_term_m] at ht

/-- 纯参数列在两个模型中的求值保持逐项对应。 -/
theorem args_l {Γ Δ : SortContext signature_m} {sorts : List sort_m}
    (C : correspondence_l (M := M) (N := N))
    (args : Arguments signature_m Γ Δ sorts) (η : Env M Γ Δ) (ξ : Env N Γ Δ)
    (hη : environments_related_l C η ξ)
    (ha : pure_args_m args = true) :
    correspondence_l.values_related_l C (Arguments.eval η args) (Arguments.eval ξ args) :=
  match args with
  | .nil => True.intro
  | .cons t rest => by
    have hparts : pure_term_m t = true ∧ pure_args_m rest = true := by
      simpa [pure_args_m] using ha
    exact ⟨term_l C t η ξ hη hparts.1, args_l C rest η ξ hη hparts.2⟩

end

/-- `pure_m` 公式在对应环境中双向保持真值；无集合量词是此结论成立的关键。 -/
theorem formula_l {Γ Δ : SortContext signature_m} (C : correspondence_l (M := M) (N := N))
    (φ : Formula signature_m Γ Δ) :
    ∀ (_hφ : pure_m φ = true) (η : Env M Γ Δ) (ξ : Env N Γ Δ),
      environments_related_l C η ξ →
        (Formula.satisfies η φ ↔ Formula.satisfies ξ φ) := by
  intro _hφ η ξ hη
  match φ with
  | .falsum => simp [pure_m] at _hφ; rfl
  | .truth => simp [pure_m] at _hφ; rfl
  | .rel .mem (.cons n (.cons setTerm .nil)) =>
      have hparts : pure_term_m n = true ∧ pure_term_m setTerm = true := by
        simpa [pure_m, pure_args_m] using _hφ
      have hn := term_l C n η ξ hη hparts.1
      have hSet := term_l C setTerm η ξ hη hparts.2
      change C.numberEquiv_l (Term.eval η n) = Term.eval ξ n at hn
      change C.setRel_l (Term.eval η setTerm) (Term.eval ξ setTerm) at hSet
      have hmem :
          M.relInterp .mem (.cons (Term.eval η n) (.cons (Term.eval η setTerm) .nil)) ↔
            N.relInterp .mem
              (.cons (C.numberEquiv_l (Term.eval η n)) (.cons (Term.eval ξ setTerm) .nil)) :=
        C.member_iff_l (Term.eval η n) (Term.eval η setTerm) (Term.eval ξ setTerm) hSet
      simp only [Formula.satisfies, Arguments.eval]
      rw [← hn]
      exact hmem
  | .rel .start args => simp [pure_m] at _hφ
  | .rel .step args => simp [pure_m] at _hφ
  | @Formula.equal _ _ _ .num left right =>
      have hparts : pure_term_m left = true ∧ pure_term_m right = true := by
        simpa [pure_m] using _hφ
      have hl := term_l C left η ξ hη hparts.1
      have hr := term_l C right η ξ hη hparts.2
      change C.numberEquiv_l (Term.eval η left) = Term.eval ξ left at hl
      change C.numberEquiv_l (Term.eval η right) = Term.eval ξ right at hr
      simp only [Formula.satisfies]
      constructor
      · intro h
        calc
          Term.eval ξ left = C.numberEquiv_l (Term.eval η left) := hl.symm
          _ = C.numberEquiv_l (Term.eval η right) := congrArg C.numberEquiv_l h
          _ = Term.eval ξ right := hr
      · intro h
        apply C.numberEquiv_l.injective
        calc
          C.numberEquiv_l (Term.eval η left) = Term.eval ξ left := hl
          _ = Term.eval ξ right := h
          _ = C.numberEquiv_l (Term.eval η right) := hr.symm
  | @Formula.equal _ _ _ .set left right => simp [pure_m] at _hφ
  | .neg ψ =>
      have hψ : pure_m ψ = true := by simpa [pure_m] using _hφ
      exact not_congr (formula_l C ψ hψ η ξ hη)
  | .conj ψ χ =>
      have hparts : pure_m ψ = true ∧ pure_m χ = true := by
        simpa [pure_m] using _hφ
      exact and_congr (formula_l C ψ hparts.1 η ξ hη)
        (formula_l C χ hparts.2 η ξ hη)
  | .disj ψ χ =>
      have hparts : pure_m ψ = true ∧ pure_m χ = true := by
        simpa [pure_m] using _hφ
      exact or_congr (formula_l C ψ hparts.1 η ξ hη)
        (formula_l C χ hparts.2 η ξ hη)
  | .imp ψ χ =>
      have hparts : pure_m ψ = true ∧ pure_m χ = true := by
        simpa [pure_m] using _hφ
      exact imp_congr (formula_l C ψ hparts.1 η ξ hη)
        (formula_l C χ hparts.2 η ξ hη)
  | .iff ψ χ =>
      have hparts : pure_m ψ = true ∧ pure_m χ = true := by
        simpa [pure_m] using _hφ
      exact iff_congr (formula_l C ψ hparts.1 η ξ hη)
        (formula_l C χ hparts.2 η ξ hη)
  | .forallE .num ψ =>
      have hψ : pure_m ψ = true := by simpa [pure_m] using _hφ
      simp only [Formula.satisfies]
      constructor
      · intro h b
        let a := C.numberEquiv_l.symm b
        have hab : C.numberEquiv_l a = b := C.numberEquiv_l.apply_symm_apply b
        have hEnv := push_number_l C η ξ hη a
        have hBody := (formula_l C ψ hψ (η.pushBound a)
          (ξ.pushBound (C.numberEquiv_l a)) hEnv).mp (h a)
        simpa [hab] using hBody
      · intro h a
        have hEnv := push_number_l C η ξ hη a
        exact (formula_l C ψ hψ (η.pushBound a)
          (ξ.pushBound (C.numberEquiv_l a)) hEnv).mpr (h (C.numberEquiv_l a))
  | .forallE .set ψ => simp [pure_m] at _hφ
  | .existsE .num ψ =>
      have hψ : pure_m ψ = true := by simpa [pure_m] using _hφ
      simp only [Formula.satisfies]
      constructor
      · rintro ⟨a, h⟩
        refine ⟨C.numberEquiv_l a, ?_⟩
        have hEnv := push_number_l C η ξ hη a
        exact (formula_l C ψ hψ (η.pushBound a)
          (ξ.pushBound (C.numberEquiv_l a)) hEnv).mp h
      · rintro ⟨b, h⟩
        let a := C.numberEquiv_l.symm b
        have hab : C.numberEquiv_l a = b := C.numberEquiv_l.apply_symm_apply b
        have hEnv := push_number_l C η ξ hη a
        have hTarget : Formula.satisfies (ξ.pushBound (C.numberEquiv_l a)) ψ := by
          simpa [hab] using h
        have hBody := (formula_l C ψ hψ (η.pushBound a)
          (ξ.pushBound (C.numberEquiv_l a)) hEnv).mpr hTarget
        exact ⟨a, hBody⟩
  | .existsE .set ψ => simp [pure_m] at _hφ

#print axioms correspondence_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPureTransfer
