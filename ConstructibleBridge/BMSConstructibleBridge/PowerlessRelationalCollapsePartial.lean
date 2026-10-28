import BMSConstructibleBridge.PowerlessRelativeMembershipCollapsePartial
import BMSConstructibleBridge.SecondOrderCollapseSyntax

/-! # 任意原关系的有界局部坍缩与内部一致性

纯隶属 ℒ，原 Z₂。源关系 A 可以是一般有界关系图，不要求等于
源点的隶属。局部值域 C 与原全值域 T 独立，只需实际 C 传递。
因此检查器不含未知全坍缩值域作为 Class 参数，供后续局部预算使用。

一致性通过原公式的内部集合归纳证明，不使用模型外部良基性，
不假定局部解已有共同层界，也不把此接口当作解码闭包已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapsePartial

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def closed_m {Γ Δ : SortContext ℒ} (A I E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E <| membershipLevyBound.boundedForall (up I) <|
    .imp (PowerlessValueBounded.formula_m (up (up A)) (.bvar .here) (.bvar (.there .here)))
      (member_m (.bvar .here) (up (up E)))

def recursive_m {Γ Δ : SortContext ℒ} (A E C G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E <| membershipLevyBound.boundedForall (up C) <|
    .imp (PowerlessValueBounded.formula_m (up (up G)) (.bvar (.there .here)) (.bvar .here)) <|
      membershipLevyBound.boundedForall (up (up C)) <|
        .iff (member_m (.bvar .here) (.bvar (.there .here))) <|
          membershipLevyBound.boundedExists (up (up (up E))) <| .conj
            (PowerlessValueBounded.formula_m (up (up (up (up A)))) (.bvar .here)
              (.bvar (.there (.there (.there .here)))))
            (PowerlessValueBounded.formula_m (up (up (up (up G)))) (.bvar .here) (.bvar (.there .here)))

def partial_m {Γ Δ : SortContext ℒ} (A I E C G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeMembershipCollapsePartial.subset_m E I) <|
    .conj (closed_m A I E) <| .conj (PowerlessMapBounded.formula_m G E C) (recursive_m A E C G)

theorem delta_m {Γ Δ : SortContext ℒ} (A I E C G : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (partial_m A I E C G) :=
  .conj (.bounded_forall _ (.rel _ _)) <| .conj
    (.bounded_forall _ (.bounded_forall _ (.imp (PowerlessValueBounded.delta_l _ _ _) (.rel _ _)))) <|
      .conj (PowerlessMapBounded.delta_l _ _ _) <|
        .bounded_forall _ (.bounded_forall _ (.imp (PowerlessValueBounded.delta_l _ _ _)
          (.bounded_forall _ (.iff (.rel _ _) (.bounded_exists _ (.conj
            (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _)))))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def partial_l (A I E C G : Raw) : Prop :=
  (∀ x, mem_l hℳ x E → mem_l hℳ x I) ∧
    (∀ x, mem_l hℳ x E → ∀ a, mem_l hℳ a I →
      SecondOrderFunctionObjects.value_l hℳ A a x → mem_l hℳ a E) ∧
    SecondOrderFunctionObjects.map_l hℳ G E C ∧
      ∀ x, mem_l hℳ x E → ∀ y, mem_l hℳ y C →
        SecondOrderFunctionObjects.value_l hℳ G x y → ∀ z, mem_l hℳ z C →
          (mem_l hℳ z y ↔ ∃ a, mem_l hℳ a E ∧
            SecondOrderFunctionObjects.value_l hℳ A a x ∧ SecondOrderFunctionObjects.value_l hℳ G a z)

theorem formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (A I E C G : Term ℒ Γ Δ .set) :
    (partial_m A I E C G).satisfies η ↔
      partial_l (A.eval η) (I.eval η) (E.eval η) (C.eval η) (G.eval η) := by
  simp only [partial_m, partial_l, closed_m, recursive_m, PowerlessRelativeMembershipCollapsePartial.subset_m,
    Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessValueBounded.formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem recursive_l {A I E C G : Raw} (hG : partial_l A I E C G)
    (hC : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C) :
    ∀ x, mem_l hℳ x E → ∀ y, SecondOrderFunctionObjects.value_l hℳ G x y →
      ∀ z, mem_l hℳ z y ↔ ∃ a, mem_l hℳ a E ∧
        SecondOrderFunctionObjects.value_l hℳ A a x ∧ SecondOrderFunctionObjects.value_l hℳ G a z := by
  intro x hx y hxy z
  have hyC := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 hxy).2
  constructor
  · intro hzy
    exact (hG.2.2.2 x hx y hyC hxy z (hC y hyC z hzy)).mp hzy
  · rintro ⟨a, ha, hax, haz⟩
    have hzC := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 haz).2
    exact (hG.2.2.2 x hx y hyC hxy z hzC).mpr ⟨a, ha, hax, haz⟩

def point_m {Γ Δ : SortContext ℒ} (E H G y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E <|
    .imp (value_m (up H) (.bvar .here) (up y)) <| .forallE .set <|
      .imp (value_m (up (up G)) (.bvar (.there .here)) (.bvar .here))
        (.equal (up (up y)) (.bvar .here))

theorem point_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (E H G y : Term ℒ Γ Δ .set) :
    (point_m E H G y).satisfies η ↔
      ∀ x, mem_l hℳ x (E.eval η) → SecondOrderFunctionObjects.value_l hℳ (H.eval η) x (y.eval η) →
        ∀ z, SecondOrderFunctionObjects.value_l hℳ (G.eval η) x z → y.eval η = z := by
  simp only [point_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 归纳在原全坍缩的输出上进行，允许局部母界 C 与原值域 T 不同。 -/
theorem agrees_l {A I E T H C G : Raw} (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hC : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hG : partial_l A I E C G) : ∀ x, mem_l hℳ x E → ∀ y z,
      SecondOrderFunctionObjects.value_l hℳ H x y → SecondOrderFunctionObjects.value_l hℳ G x z → y = z := by
  let η : Env 𝒱 [] [.set, .set, .set] := Env.empty |>.pushFree G |>.pushFree H |>.pushFree E
  let φ : Formula ℒ [] [.set, .set, .set, .set] := point_m
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar .here)
  have hRec := recursive_l hG hC
  have hAll : ∀ y, φ.satisfies (η.pushFree y) := by
    apply PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    intro y ih
    apply (point_formula_l (η.pushFree y) _ _ _ _).mpr
    intro x hx hxy z hxz
    apply SecondOrderQuotient.ext_l hℳ y z
    intro a
    constructor
    · intro hay
      obtain ⟨b, hbI, hbx, hba⟩ := (hH.2.2.2 x y (hG.1 x hx) hxy a).mp hay
      have hbE := hG.2.1 x hx b hbI hbx
      obtain ⟨c, hc, _⟩ := hG.2.2.1.2 b hbE
      have hac : a = c := (point_formula_l (η.pushFree a) _ _ _ _).mp (ih a hay) b hbE hba c hc.2
      exact (hRec x hx z hxz a).mpr ⟨b, hbE, hbx, hac.symm ▸ hc.2⟩
    · intro haz
      obtain ⟨b, hbE, hbx, hba⟩ := (hRec x hx z hxz a).mp haz
      obtain ⟨c, hc, _⟩ := hH.2.1.2 b (hG.1 b hbE)
      have hcy := (hH.2.2.2 x y (hG.1 x hx) hxy c).mpr ⟨b, hG.1 b hbE, hbx, hc.2⟩
      have hca := (point_formula_l (η.pushFree c) _ _ _ _).mp (ih c hcy) b hbE hc.2 a hba
      exact hca ▸ hcy
  intro x hx y z hxy hxz
  exact (point_formula_l (η.pushFree y) _ _ _ _).mp (hAll y) x hx hxy z hxz

theorem value_l {A I E T H C G : Raw} (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hC : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hG : partial_l A I E C G) {x y : Raw} (hx : mem_l hℳ x E) :
    SecondOrderFunctionObjects.value_l hℳ G x y ↔ SecondOrderFunctionObjects.value_l hℳ H x y := by
  constructor
  · intro hxy
    obtain ⟨z, hz, _⟩ := hH.2.1.2 x (hG.1 x hx)
    exact (agrees_l hH hC hG x hx z y hz.2 hxy) ▸ hz.2
  · intro hxy
    obtain ⟨z, hz, _⟩ := hG.2.2.1.2 x hx
    exact (agrees_l hH hC hG x hx y z hxy hz.2).symm ▸ hz.2

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  let A : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let I := .fvar (.there .here)
  let E := .fvar (.there (.there .here))
  let T := .fvar (.there (.there (.there .here)))
  let H := .fvar (.there (.there (.there (.there .here))))
  let C := .fvar (.there (.there (.there (.there (.there .here)))))
  let G := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
      .imp (partial_m A I E C G) (PowerlessRelativeMembershipCollapsePartial.agreement_m E H G)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, formula_l,
    PowerlessRelativeMembershipCollapsePartial.agreement_m, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, SecondOrderObjectSyntax.value_l,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  exact fun hH hC hG x hx y => value_l hH hC hG hx

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapsePartial
