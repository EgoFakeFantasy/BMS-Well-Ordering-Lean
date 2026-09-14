import BMSConstructibleBridge.SecondOrderOmega
import BMSConstructibleBridge.SecondOrderObjectSyntax

/-!
# 纯隶属语言中的最小归纳对象

ω 不是额外常元。公式要求对象归纳且包含于每个归纳对象，所有量词均在实际
纯集合论签名中展开，并与任意模型图商的规格对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderObjectSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def bind {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with | .here => a)

def inductive_template_m : Formula ℒ [] [.set] :=
  .conj
    (.existsE .set (.conj
      (.forallE .set (.neg (member_m (.bvar .here) (.bvar (.there .here)))))
      (member_m (.bvar .here) (.fvar .here))))
    (.forallE .set (.imp (member_m (.bvar .here) (.fvar .here))
      (.existsE .set (.conj (member_m (.bvar .here) (.fvar .here))
        (.forallE .set (.iff (member_m (.bvar .here) (.bvar (.there .here)))
          (.disj (member_m (.bvar .here) (.bvar (.there (.there .here))))
            (.equal (.bvar .here) (.bvar (.there (.there .here)))))))))))

def inductive_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  inductive_template_m.substitute (bind a)

private theorem inductive_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set]) :
    Formula.satisfies η inductive_template_m ↔ SecondOrderOmega.inductive_l hℳ (η.freeVal .here) := Iff.rfl

theorem inductive_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (inductive_m a) ↔ SecondOrderOmega.inductive_l hℳ (a.eval η) := by
  rw [inductive_m, Formula.satisfies_substitute, inductive_template]
  rfl

def omega_template_m : Formula ℒ [] [.set] :=
  .conj (inductive_m (.fvar .here))
    (.forallE .set (.imp (inductive_m (.bvar .here))
      (.forallE .set (.imp (member_m (.bvar .here) (.fvar .here))
        (member_m (.bvar .here) (.bvar (.there .here)))))))

def omega_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  omega_template_m.substitute (bind a)

private theorem omega_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set]) :
    Formula.satisfies η omega_template_m ↔ SecondOrderOmega.omega_l hℳ (η.freeVal .here) := by
  simp only [omega_template_m, Formula.satisfies, inductive_l]
  rfl

theorem omega_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (omega_m a) ↔ SecondOrderOmega.omega_l hℳ (a.eval η) := by
  rw [omega_m, Formula.satisfies_substitute, omega_template]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOmegaSyntax
