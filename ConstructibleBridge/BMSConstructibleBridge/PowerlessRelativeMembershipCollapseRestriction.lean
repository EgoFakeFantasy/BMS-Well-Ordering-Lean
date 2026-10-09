import BMSConstructibleBridge.PowerlessRelativeMembershipCollapsePartial
import BMSConstructibleBridge.SecondOrderFunctionRestriction

/-! # 同一成员坍缩在实际源层上的局部解

由原 Z₂ 分离与限制图构造 E=I∩U 及 G=H↾E。U 的实际传递性保证 E
在 I 的隶属前驱下封闭，因此 G 满足不含 H 的原局部检查式。全域逐值
对应保留同一 H，不重选坍缩像，也不要求 H 或限制图已经属于 Class。
本文件给预算归纳提供真实 raw 局部解；局部解入预算层仍是独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseRestriction

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def domain_m {Γ Δ : SortContext ℒ} (I U E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up E))
    (.conj (member_m (.bvar .here) (up I)) (member_m (.bvar .here) (up U)))

def restriction_m {Γ Δ : SortContext ℒ} (E H G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (value_m (up (up G)) (.bvar (.there .here)) (.bvar .here))
      (.conj (member_m (.bvar (.there .here)) (up (up E)))
        (value_m (up (up H)) (.bvar (.there .here)) (.bvar .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def domain_l (I U E : Raw) : Prop :=
  ∀ x, mem_l hℳ x E ↔ mem_l hℳ x I ∧ mem_l hℳ x U

theorem domain_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I U E : Term ℒ Γ Δ .set) : (domain_m I U E).satisfies η ↔
      domain_l (I.eval η) (U.eval η) (E.eval η) := by
  simp only [domain_m, domain_l, Formula.satisfies, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem restriction_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (E H G : Term ℒ Γ Δ .set) : (restriction_m E H G).satisfies η ↔
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ (G.eval η) x y ↔
        mem_l hℳ x (E.eval η) ∧ SecondOrderFunctionObjects.value_l hℳ (H.eval η) x y := by
  simp only [restriction_m, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 每个实际传递母域都给出同一 H 的真实前驱封闭限制，不预供局部解。 -/
theorem exists_l {I U T H : Raw}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hU : ∀ x, mem_l hℳ x U → ∀ y, mem_l hℳ y x → mem_l hℳ y U) :
    ∃ E G, domain_l I U E ∧
      PowerlessRelativeMembershipCollapsePartial.partial_l I E T G ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ G x y ↔
        mem_l hℳ x E ∧ SecondOrderFunctionObjects.value_l hℳ H x y := by
  let φ : Formula ℒ [] [.set, .set] := member_m (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set] := Env.empty.pushFree I
  obtain ⟨E, hE⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) U
  have hDomain : domain_l I U E := by
    intro x
    have hφ : φ.satisfies (η.pushFree x) ↔ mem_l hℳ x I := by
      simp only [φ, member_m, Formula.satisfies, Arguments.eval, Term.eval, η]
      rfl
    exact (hE x).trans ((and_congr Iff.rfl hφ).trans and_comm)
  have hSub : ∀ x, mem_l hℳ x E → mem_l hℳ x I := fun x hx => ((hDomain x).mp hx).1
  have hClosed : ∀ x, mem_l hℳ x E → ∀ y, mem_l hℳ y I →
      mem_l hℳ y x → mem_l hℳ y E := by
    intro x hx y hyI hyx
    exact (hDomain y).mpr ⟨hyI, hU x ((hDomain x).mp hx).2 y hyx⟩
  obtain ⟨G, hG, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hH.2.1 hSub
  refine ⟨E, G, hDomain, ⟨hSub, hClosed, hG, ?_⟩, hRead⟩
  intro x hx y _hy hxy z _hz
  have hHxy := ((hRead x y).mp hxy).2
  constructor
  · intro hzy
    obtain ⟨a, haI, hax, haz⟩ := (hH.2.2.2.1 x y (hSub x hx) hHxy z).mp hzy
    have haE := hClosed x hx a haI hax
    exact ⟨a, haE, hax, (hRead a z).mpr ⟨haE, haz⟩⟩
  · rintro ⟨a, haE, hax, haz⟩
    exact (hH.2.2.2.1 x y (hSub x hx) hHxy z).mpr
      ⟨a, hSub a haE, hax, ((hRead a z).mp haz).2⟩

/-- 实际相对层的传递性由原层关系提供，调用端无需额外闭包守卫。 -/
theorem level_l {B α I U T H : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hU : PowerlessRelativeHierarchySemantics.level_l hℳ B α U)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H) :
    ∃ E G, domain_l I U E ∧
      PowerlessRelativeMembershipCollapsePartial.partial_l I E T G ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ G x y ↔
        mem_l hℳ x E ∧ SecondOrderFunctionObjects.value_l hℳ H x y :=
  exists_l hH (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hU)

def schema_m {Δ : SortContext ℒ} (I U T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeMembershipCollapse.spec_m I T H) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m U) <|
      .existsE .set <| .existsE .set <|
        let E : Term ℒ [.set, .set] Δ .set := .bvar (.there .here)
        let G : Term ℒ [.set, .set] Δ .set := .bvar .here
        .conj (domain_m (up (up I)) (up (up U)) E) <|
          .conj (PowerlessRelativeMembershipCollapsePartial.partial_m
            (up (up I)) E (up (up T)) G) (restriction_m E (up (up H)) G)

def sentence_m {Δ : SortContext ℒ} (I U T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m I U T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (I U T H : Term ℒ [] Δ .set) : (sentence_m I U T H).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeMembershipCollapse.spec_formula_l,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, domain_formula_l,
    PowerlessRelativeMembershipCollapsePartial.formula_l, restriction_formula_l,
    up, Term.eval_weakenBound]
  exact fun hH hU => exists_l (hℳ := hℳ) hH hU

theorem derives_m {Δ : SortContext ℒ} (I U T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m I U T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ I U T H)

#print axioms exists_l
#print axioms level_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseRestriction
