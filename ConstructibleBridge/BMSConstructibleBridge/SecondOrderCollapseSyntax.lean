import BMSConstructibleBridge.SecondOrderCollapseFunction
import BMSConstructibleBridge.SecondOrderObjectSyntax

/-!
# 满射坍缩函数的纯隶属语言规格

传递值域、集合函数、满射和逐点递归方程均在原语言中展开，变量顺序固定为
原关系、域域、值域、函数。不存在额外的坍缩函数符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderObjectSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def bind {Γ Δ : SortContext ℒ} (a d u f : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set, .set, .set, .set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => a
    | .there .here => d
    | .there (.there .here) => u
    | .there (.there (.there .here)) => f)

def template_m : Formula ℒ [] [.set, .set, .set, .set] :=
  .conj
    (.forallE .set (.forallE .set (.imp
      (member_m (.bvar (.there .here)) (.fvar (.there (.there .here))))
      (.imp (member_m (.bvar .here) (.bvar (.there .here)))
        (member_m (.bvar .here) (.fvar (.there (.there .here))))))))
    (.conj (map_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.fvar (.there (.there .here))))
      (.conj
        (.forallE .set (.imp (member_m (.bvar .here) (.fvar (.there (.there .here))))
          (.existsE .set (.conj (member_m (.bvar .here) (.fvar (.there .here)))
            (value_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.bvar (.there .here)))))))
        (.forallE .set (.forallE .set (.imp (member_m (.bvar (.there .here)) (.fvar (.there .here)))
          (.imp (value_m (.fvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here))
            (.forallE .set (.iff (member_m (.bvar .here) (.bvar (.there .here)))
              (.existsE .set (.conj (member_m (.bvar .here) (.fvar (.there .here)))
                (.conj (value_m (.fvar .here) (.bvar .here) (.bvar (.there (.there (.there .here)))))
                  (value_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.bvar (.there .here))))))))))))))

def formula_m {Γ Δ : SortContext ℒ} (a d u f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  template_m.substitute (bind a d u f)

private theorem template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set]) :
    Formula.satisfies η template_m ↔ SecondOrderCollapseFunction.spec_l hℳ
      (η.freeVal .here) (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
      (η.freeVal (.there (.there (.there .here)))) := by
  simp only [template_m, Formula.satisfies, SecondOrderObjectSyntax.map_l, SecondOrderObjectSyntax.value_l]
  rfl

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a d u f : Term ℒ Γ Δ .set) :
    Formula.satisfies η (formula_m a d u f) ↔ SecondOrderCollapseFunction.spec_l hℳ
      (a.eval η) (d.eval η) (u.eval η) (f.eval η) := by
  rw [formula_m, Formula.satisfies_substitute, template]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseSyntax
