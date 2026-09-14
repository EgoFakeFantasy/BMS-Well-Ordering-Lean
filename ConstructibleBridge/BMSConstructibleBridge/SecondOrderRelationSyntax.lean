import BMSConstructibleBridge.SecondOrderRegularRelation
import BMSConstructibleBridge.SecondOrderObjectSyntax

/-!
# 纯隶属语言中的关系、域域与正则性

域域明确是所有有序对的左右端点之并；正则性量化其中全部内部非空子集。
所有模板的源语义均与已核验的商结构规格对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationSyntax

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderObjectSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def bind₂ {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set, .set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with | .here => a | .there .here => b)

private def bind₁ {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with | .here => a)

def relation_template_m : Formula ℒ [] [.set, .set] :=
  .forallE .set (.imp (member_m (.bvar .here) (.fvar .here))
    (.existsE .set (.existsE .set (.conj (member_m (.bvar (.there .here)) (.fvar (.there .here)))
      (.conj (member_m (.bvar .here) (.fvar (.there .here)))
        (ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))))))))

def relation_m {Γ Δ : SortContext ℒ} (a o : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  relation_template_m.substitute (bind₂ a o)

private theorem relation_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set]) :
    Formula.satisfies η relation_template_m ↔
      SecondOrderRegularRelation.relation_l hℳ (η.freeVal .here) (η.freeVal (.there .here)) := by
  simp only [relation_template_m, Formula.satisfies, ordered_l]
  rfl

theorem relation_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a o : Term ℒ Γ Δ .set) :
    Formula.satisfies η (relation_m a o) ↔ SecondOrderRegularRelation.relation_l hℳ (a.eval η) (o.eval η) := by
  rw [relation_m, Formula.satisfies_substitute, relation_template]
  rfl

def domain_template_m : Formula ℒ [] [.set, .set] :=
  .existsE .set (.disj (value_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
    (value_m (.fvar .here) (.bvar .here) (.fvar (.there .here))))

def domain_m {Γ Δ : SortContext ℒ} (a x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  domain_template_m.substitute (bind₂ a x)

private theorem domain_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set]) :
    Formula.satisfies η domain_template_m ↔
      SecondOrderRegularRelation.domain_l hℳ (η.freeVal .here) (η.freeVal (.there .here)) := by
  simp only [domain_template_m, Formula.satisfies, value_l]
  rfl

theorem domain_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a x : Term ℒ Γ Δ .set) :
    Formula.satisfies η (domain_m a x) ↔ SecondOrderRegularRelation.domain_l hℳ (a.eval η) (x.eval η) := by
  rw [domain_m, Formula.satisfies_substitute, domain_template]
  rfl

def field_template_m : Formula ℒ [] [.set, .set] :=
  .forallE .set (.iff (member_m (.bvar .here) (.fvar (.there .here))) (domain_m (.fvar .here) (.bvar .here)))

def field_m {Γ Δ : SortContext ℒ} (a d : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  field_template_m.substitute (bind₂ a d)

private theorem field_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set]) :
    Formula.satisfies η field_template_m ↔ ∀ x,
      SecondOrderQuotient.mem_l hℳ x (η.freeVal (.there .here)) ↔
        SecondOrderRegularRelation.domain_l hℳ (η.freeVal .here) x := by
  simp only [field_template_m, Formula.satisfies, domain_l]
  rfl

theorem field_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a d : Term ℒ Γ Δ .set) :
    Formula.satisfies η (field_m a d) ↔ ∀ x, SecondOrderQuotient.mem_l hℳ x (d.eval η) ↔
      SecondOrderRegularRelation.domain_l hℳ (a.eval η) x := by
  rw [field_m, Formula.satisfies_substitute, field_template]
  rfl

def wellFounded_template_m : Formula ℒ [] [.set] :=
  .forallE .set (.imp (.existsE .set (member_m (.bvar .here) (.bvar (.there .here))))
    (.imp (.forallE .set (.imp (member_m (.bvar .here) (.bvar (.there .here)))
      (domain_m (.fvar .here) (.bvar .here))))
      (.existsE .set (.conj (member_m (.bvar .here) (.bvar (.there .here)))
        (.forallE .set (.imp (member_m (.bvar .here) (.bvar (.there (.there .here))))
          (.neg (value_m (.fvar .here) (.bvar .here) (.bvar (.there .here))))))))))

def wellFounded_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  wellFounded_template_m.substitute (bind₁ a)

private theorem wellFounded_template (hℳ : Theory.Models ℳ theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set]) :
    Formula.satisfies η wellFounded_template_m ↔ SecondOrderRegularRelation.wellFounded_l hℳ (η.freeVal .here) := by
  simp only [wellFounded_template_m, Formula.satisfies, domain_l, value_l]
  rfl

theorem wellFounded_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (wellFounded_m a) ↔ SecondOrderRegularRelation.wellFounded_l hℳ (a.eval η) := by
  rw [wellFounded_m, Formula.satisfies_substitute, wellFounded_template]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationSyntax
