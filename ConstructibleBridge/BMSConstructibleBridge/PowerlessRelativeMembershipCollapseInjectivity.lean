import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-!
# 内部成员塌缩的单射性

在同一原 Z₂ 模型的实际图商中，集合函数的输出满足成员递归式时，源域内的
成员外延性推出单射。归纳性质以纯 ℒ 公式表示，再消费既有弱集合论的对象
集合归纳；不对任意宿主谓词归纳，也不假定图商外部良基。

源域无需传递，递归式只读取源域中的成员。最后的条件规格沿原图翻译给出
真正的 Z₂ 推导，并非把单射性添加到塌缩规格的前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseInjectivity

open Logic FirstOrder SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

def ext_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (I : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ x y, SecondOrderQuotient.mem_l hℳ x I → SecondOrderQuotient.mem_l hℳ y I →
    (∀ z, SecondOrderQuotient.mem_l hℳ z I →
      (SecondOrderQuotient.mem_l hℳ z x ↔ SecondOrderQuotient.mem_l hℳ z y)) → x = y

def recursive_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (I H : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ x u, SecondOrderQuotient.mem_l hℳ x I →
    SecondOrderFunctionObjects.value_l hℳ H x u →
    ∀ z, SecondOrderQuotient.mem_l hℳ z u ↔
      ∃ y, SecondOrderQuotient.mem_l hℳ y I ∧ SecondOrderQuotient.mem_l hℳ y x ∧
        SecondOrderFunctionObjects.value_l hℳ H y z

/-- 输出纤维的唯一性；归纳变量是实际商对象 u，而不是外部图节点。 -/
def fiber_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (I H u : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∀ x y, SecondOrderQuotient.mem_l hℳ x I → SecondOrderQuotient.mem_l hℳ y I →
    SecondOrderFunctionObjects.value_l hℳ H x u →
    SecondOrderFunctionObjects.value_l hℳ H y u → x = y

/-- 自由槽依次为归纳输出、源域和集合函数。 -/
def fiber_m : Formula ℒ [] [.set, .set, .set] :=
  .forallE .set (.forallE .set (
    let x : Term ℒ [.set, .set] [.set, .set, .set] .set := .bvar (.there .here)
    let y : Term ℒ [.set, .set] [.set, .set, .set] .set := .bvar .here
    let u : Term ℒ [.set, .set] [.set, .set, .set] .set := .fvar .here
    let I : Term ℒ [.set, .set] [.set, .set, .set] .set := .fvar (.there .here)
    let H : Term ℒ [.set, .set] [.set, .set, .set] .set := .fvar (.there (.there .here))
    .imp (member_m x I) (.imp (member_m y I)
      (.imp (value_m H x u) (.imp (value_m H y u) (.equal x y))))))

theorem fiber_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set]) :
    fiber_m.satisfies η ↔ fiber_l hℳ (η.freeVal (.there .here))
      (η.freeVal (.there (.there .here))) (η.freeVal .here) := by
  simp only [fiber_m, Formula.satisfies, SecondOrderObjectSyntax.value_l]
  rfl

private def ext_template_m : Formula ℒ [] [.set] :=
  .forallE .set (.forallE .set (.imp
    (member_m (.bvar (.there .here)) (.fvar .here))
    (.imp (member_m (.bvar .here) (.fvar .here))
      (.imp (.forallE .set (.imp (member_m (.bvar .here) (.fvar .here))
        (.iff (member_m (.bvar .here) (.bvar (.there (.there .here))))
          (member_m (.bvar .here) (.bvar (.there .here))))))
        (.equal (.bvar (.there .here)) (.bvar .here))))))

private def bind₁_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with | .here => I)

def ext_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  ext_template_m.substitute (bind₁_m I)

private theorem ext_template_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set]) :
    ext_template_m.satisfies η ↔ ext_l hℳ (η.freeVal .here) := by
  simp only [ext_template_m, Formula.satisfies]
  rfl

theorem ext_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (I : Term ℒ Γ Δ .set) : (ext_m I).satisfies η ↔ ext_l hℳ (I.eval η) := by
  rw [ext_m, Formula.satisfies_substitute, ext_template_l]
  rfl

private def recursive_template_m : Formula ℒ [] [.set, .set] :=
  .forallE .set (.forallE .set (.imp
    (member_m (.bvar (.there .here)) (.fvar .here))
    (.imp (value_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
      (.forallE .set (.iff (member_m (.bvar .here) (.bvar (.there .here)))
        (.existsE .set (.conj (member_m (.bvar .here) (.fvar .here))
          (.conj (member_m (.bvar .here) (.bvar (.there (.there (.there .here)))))
            (value_m (.fvar (.there .here)) (.bvar .here) (.bvar (.there .here)))))))))))

private def bind₂_m {Γ Δ : SortContext ℒ} (I H : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set, .set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => I
    | .there .here => H)

def recursive_m {Γ Δ : SortContext ℒ} (I H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  recursive_template_m.substitute (bind₂_m I H)

private theorem recursive_template_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set]) :
    recursive_template_m.satisfies η ↔ recursive_l hℳ (η.freeVal .here)
      (η.freeVal (.there .here)) := by
  simp only [recursive_template_m, Formula.satisfies, SecondOrderObjectSyntax.value_l]
  rfl

theorem recursive_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (I H : Term ℒ Γ Δ .set) :
    (recursive_m I H).satisfies η ↔ recursive_l hℳ (I.eval η) (H.eval η) := by
  rw [recursive_m, Formula.satisfies_substitute, recursive_template_l]
  rfl

/-- 每个子输出上的纤维唯一性经成员递归式返回到源域中的成员外延性。 -/
theorem injective_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (I T H : SecondOrderQuotient.type_l hℳ)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hExt : ext_l hℳ I) (hRec : recursive_l hℳ I H) :
    SecondOrderFunctionObjects.injective_l hℳ H := by
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] :=
    (Env.empty.pushFree H).pushFree I
  have hφ : ∀ u, fiber_m.satisfies (η.pushFree u) := by
    apply PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    intro u ih
    apply (fiber_formula_l hℳ (η.pushFree u)).mpr
    intro x y hx hy hxu hyu
    apply hExt x y hx hy
    have hSub : ∀ x y, SecondOrderQuotient.mem_l hℳ x I →
        SecondOrderQuotient.mem_l hℳ y I →
        SecondOrderFunctionObjects.value_l hℳ H x u →
        SecondOrderFunctionObjects.value_l hℳ H y u →
        ∀ z, SecondOrderQuotient.mem_l hℳ z I → SecondOrderQuotient.mem_l hℳ z x →
          SecondOrderQuotient.mem_l hℳ z y := by
      intro x y hx hy hxu hyu z hz hzx
      obtain ⟨v, hv, _⟩ := hH.2 z hz
      have hvu : SecondOrderQuotient.mem_l hℳ v u :=
        (hRec x u hx hxu v).mpr ⟨z, hz, hzx, hv.2⟩
      obtain ⟨w, hw, hwy, hwv⟩ := (hRec y u hy hyu v).mp hvu
      have hzw : z = w :=
        (fiber_formula_l hℳ (η.pushFree v)).mp (ih v hvu) z w hz hw hv.2 hwv
      exact hzw.symm ▸ hwy
    intro z hz
    exact ⟨hSub x y hx hy hxu hyu z hz, hSub y x hy hx hyu hxu z hz⟩
  intro x y u hxu hyu
  exact (fiber_formula_l hℳ (η.pushFree u)).mp (hφ u) x y
    (SecondOrderFunctionProperties.value_mem_l hℳ hH hxu).1
    (SecondOrderFunctionProperties.value_mem_l hℳ hH hyu).1 hxu hyu

/-- 单射使递归式同时反映源域内的实际成员关系。 -/
theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (I T H : SecondOrderQuotient.type_l hℳ)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hExt : ext_l hℳ I) (hRec : recursive_l hℳ I H)
    {x y u v : SecondOrderQuotient.type_l hℳ}
    (hx : SecondOrderQuotient.mem_l hℳ x I) (hy : SecondOrderQuotient.mem_l hℳ y I)
    (hxu : SecondOrderFunctionObjects.value_l hℳ H x u)
    (hyv : SecondOrderFunctionObjects.value_l hℳ H y v) :
    SecondOrderQuotient.mem_l hℳ x y ↔ SecondOrderQuotient.mem_l hℳ u v := by
  constructor
  · intro hxy
    exact (hRec y v hy hyv u).mpr ⟨x, hx, hxy, hxu⟩
  · intro huv
    obtain ⟨z, _, hzy, hzu⟩ := (hRec y v hy hyv u).mp huv
    have hxz := injective_l hℳ I T H hH hExt hRec x z u hxu hzu
    exact hxz.symm ▸ hzy

/-- 自由槽依次为源域、陪域和实际集合函数。 -/
def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let T : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let H : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (.conj (map_m H I T) (.conj (ext_m I) (recursive_m I H))) (injective_m H)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem schema_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set]) :
    schema_m.satisfies η ↔
      ((SecondOrderFunctionObjects.map_l hℳ (η.freeVal (.there (.there .here)))
        (η.freeVal .here) (η.freeVal (.there .here)) ∧
        ext_l hℳ (η.freeVal .here) ∧ recursive_l hℳ (η.freeVal .here)
          (η.freeVal (.there (.there .here)))) →
      SecondOrderFunctionObjects.injective_l hℳ (η.freeVal (.there (.there .here)))) := by
  simp only [schema_m, Formula.satisfies, SecondOrderObjectSyntax.map_l,
    ext_formula_l, recursive_formula_l, SecondOrderObjectSyntax.injective_l]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (schema_formula_l hℳ η).mpr
  rintro ⟨hH, hExt, hRec⟩
  exact injective_l hℳ _ _ _ hH hExt hRec

/-- 条件单射规格由原 Z₂ 正式推出；没有新增塌缩或选择公理。 -/
theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

#print axioms injective_l
#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseInjectivity
