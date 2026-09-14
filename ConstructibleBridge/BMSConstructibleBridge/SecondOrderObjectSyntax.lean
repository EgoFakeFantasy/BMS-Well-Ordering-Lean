import BMSConstructibleBridge.SecondOrderFunctionObjects

/-!
# 函数对象的纯隶属语言模板

无序对、有序对、求值、函数与单射全部展开为原签名 ℒ 的公式。模板替换保留
所有绑定及自由参数，语义核验在任意二阶模型的同一图商中进行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderObjectSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def member_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .rel .membership (.cons a (.cons b .nil))

private def bind₃ {Γ Δ : SortContext ℒ} (a b c : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set, .set, .set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => a
    | .there .here => b
    | .there (.there .here) => c)

private def bind₁ {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with | .here => a)

def pair_template_m : Formula ℒ [] [.set, .set, .set] :=
  .forallE .set (.iff (member_m (.bvar .here) (.fvar (.there (.there .here))))
    (.disj (.equal (.bvar .here) (.fvar .here)) (.equal (.bvar .here) (.fvar (.there .here)))))

def pair_m {Γ Δ : SortContext ℒ} (a b p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  pair_template_m.substitute (bind₃ a b p)

private theorem pair_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set]) :
    Formula.satisfies η pair_template_m ↔ SecondOrderPairObjects.pair_l hℳ
      (η.freeVal .here) (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) := Iff.rfl

theorem pair_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a b p : Term ℒ Γ Δ .set) :
    Formula.satisfies η (pair_m a b p) ↔ SecondOrderPairObjects.pair_l hℳ (a.eval η) (b.eval η) (p.eval η) := by
  rw [pair_m, Formula.satisfies_substitute, pair_template]
  rfl

def ordered_template_m : Formula ℒ [] [.set, .set, .set] :=
  .existsE .set (.existsE .set (.conj (pair_m (.fvar .here) (.fvar .here) (.bvar (.there .here)))
    (.conj (pair_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
      (pair_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there (.there .here)))))))

def ordered_m {Γ Δ : SortContext ℒ} (a b p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  ordered_template_m.substitute (bind₃ a b p)

private theorem ordered_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set]) :
    Formula.satisfies η ordered_template_m ↔ SecondOrderPairObjects.ordered_l hℳ
      (η.freeVal .here) (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) := by
  simp only [ordered_template_m, Formula.satisfies, pair_l]
  rfl

theorem ordered_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a b p : Term ℒ Γ Δ .set) :
    Formula.satisfies η (ordered_m a b p) ↔
      SecondOrderPairObjects.ordered_l hℳ (a.eval η) (b.eval η) (p.eval η) := by
  rw [ordered_m, Formula.satisfies_substitute, ordered_template]
  rfl

def value_template_m : Formula ℒ [] [.set, .set, .set] :=
  .existsE .set (.conj (member_m (.bvar .here) (.fvar .here))
    (ordered_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.bvar .here)))

def value_m {Γ Δ : SortContext ℒ} (f x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  value_template_m.substitute (bind₃ f x y)

private theorem value_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set]) :
    Formula.satisfies η value_template_m ↔ SecondOrderFunctionObjects.value_l hℳ
      (η.freeVal .here) (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) := by
  simp only [value_template_m, Formula.satisfies, ordered_l]
  rfl

theorem value_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (f x y : Term ℒ Γ Δ .set) :
    Formula.satisfies η (value_m f x y) ↔
      SecondOrderFunctionObjects.value_l hℳ (f.eval η) (x.eval η) (y.eval η) := by
  rw [value_m, Formula.satisfies_substitute, value_template]
  rfl

def map_template_m : Formula ℒ [] [.set, .set, .set] :=
  .conj
    (.forallE .set (.imp (member_m (.bvar .here) (.fvar .here))
      (.existsE .set (.existsE .set (.conj (member_m (.bvar (.there .here)) (.fvar (.there .here)))
        (.conj (member_m (.bvar .here) (.fvar (.there (.there .here))))
          (ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))))))))
    (.forallE .set (.imp (member_m (.bvar .here) (.fvar (.there .here)))
      (.existsE .set (.conj
        (.conj (member_m (.bvar .here) (.fvar (.there (.there .here))))
          (value_m (.fvar .here) (.bvar (.there .here)) (.bvar .here)))
        (.forallE .set (.imp
          (.conj (member_m (.bvar .here) (.fvar (.there (.there .here))))
            (value_m (.fvar .here) (.bvar (.there (.there .here))) (.bvar .here)))
          (.equal (.bvar .here) (.bvar (.there .here)))))))))

def map_m {Γ Δ : SortContext ℒ} (f a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  map_template_m.substitute (bind₃ f a b)

private theorem map_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set]) :
    Formula.satisfies η map_template_m ↔ SecondOrderFunctionObjects.map_l hℳ
      (η.freeVal .here) (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) := by
  simp only [map_template_m, Formula.satisfies, ordered_l, value_l]
  rfl

theorem map_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (f a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (map_m f a b) ↔
      SecondOrderFunctionObjects.map_l hℳ (f.eval η) (a.eval η) (b.eval η) := by
  rw [map_m, Formula.satisfies_substitute, map_template]
  rfl

def injective_template_m : Formula ℒ [] [.set] :=
  .forallE .set (.forallE .set (.forallE .set (.imp
    (value_m (.fvar .here) (.bvar (.there (.there .here))) (.bvar .here))
    (.imp (value_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      (.equal (.bvar (.there (.there .here))) (.bvar (.there .here)))))))

def injective_m {Γ Δ : SortContext ℒ} (f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  injective_template_m.substitute (bind₁ f)

private theorem injective_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set]) :
    Formula.satisfies η injective_template_m ↔ SecondOrderFunctionObjects.injective_l hℳ
      (η.freeVal .here) := by
  simp only [injective_template_m, Formula.satisfies, value_l]
  rfl

theorem injective_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (f : Term ℒ Γ Δ .set) :
    Formula.satisfies η (injective_m f) ↔ SecondOrderFunctionObjects.injective_l hℳ (f.eval η) := by
  rw [injective_m, Formula.satisfies_substitute, injective_template]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderObjectSyntax
