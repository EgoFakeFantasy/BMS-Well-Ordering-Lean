import BMSConstructibleBridge.PowerlessRelativeMembershipCollapse
import BMSConstructibleBridge.PowerlessMapBounded

/-! # 有界局部成员坍缩的检查式与内部唯一读数

局部定义域 E 只需在源 I 的隶属前驱下封闭，不要求 I 或 E 传递。
检查式只含 I/E/T/G，不含待收回类内的全图 H，且是纯隶属 Δ₀ 公式。
原 Z₂ 的内部集合归纳证明每个合格局部解都与已有 H 一致；不是宿主良基归纳。
这提供后续共同见证界的检查器，不假定这样的共同界已经存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapsePartial

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def subset_m {Γ Δ : SortContext ℒ} (E I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E (member_m (.bvar .here) (up I))

def closed_m {Γ Δ : SortContext ℒ} (I E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E <| membershipLevyBound.boundedForall (up I) <|
    .imp (member_m (.bvar .here) (.bvar (.there .here)))
      (member_m (.bvar .here) (up (up E)))

def recursive_m {Γ Δ : SortContext ℒ} (E T G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E <| membershipLevyBound.boundedForall (up T) <|
    .imp (PowerlessValueBounded.formula_m (up (up G)) (.bvar (.there .here)) (.bvar .here)) <|
      membershipLevyBound.boundedForall (up (up T)) <|
        .iff (member_m (.bvar .here) (.bvar (.there .here))) <|
          membershipLevyBound.boundedExists (up (up (up E))) <|
            .conj (member_m (.bvar .here) (.bvar (.there (.there (.there .here)))))
              (PowerlessValueBounded.formula_m (up (up (up (up G))))
                (.bvar .here) (.bvar (.there .here)))

def partial_m {Γ Δ : SortContext ℒ} (I E T G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (subset_m E I) <| .conj (closed_m I E) <|
    .conj (PowerlessMapBounded.formula_m G E T) (recursive_m E T G)

theorem delta_m {Γ Δ : SortContext ℒ} (I E T G : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (partial_m I E T G) :=
  .conj (.bounded_forall _ (.rel _ _)) <| .conj
    (.bounded_forall _ (.bounded_forall _ (.imp (.rel _ _) (.rel _ _)))) <|
    .conj (PowerlessMapBounded.delta_l _ _ _) <|
      .bounded_forall _ (.bounded_forall _ (.imp (PowerlessValueBounded.delta_l _ _ _)
        (.bounded_forall _ (.iff (.rel _ _) (.bounded_exists _
          (.conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)))))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def partial_l (I E T G : Raw) : Prop :=
  (∀ x, mem_l hℳ x E → mem_l hℳ x I) ∧
  (∀ x, mem_l hℳ x E → ∀ y, mem_l hℳ y I → mem_l hℳ y x → mem_l hℳ y E) ∧
  SecondOrderFunctionObjects.map_l hℳ G E T ∧
  ∀ x, mem_l hℳ x E → ∀ y, mem_l hℳ y T →
    SecondOrderFunctionObjects.value_l hℳ G x y → ∀ z, mem_l hℳ z T →
      (mem_l hℳ z y ↔ ∃ a, mem_l hℳ a E ∧ mem_l hℳ a x ∧
        SecondOrderFunctionObjects.value_l hℳ G a z)

theorem formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I E T G : Term ℒ Γ Δ .set) : (partial_m I E T G).satisfies η ↔
      partial_l (I.eval η) (E.eval η) (T.eval η) (G.eval η) := by
  simp only [partial_m, partial_l, subset_m, closed_m, recursive_m,
    Formula.LevyBound.boundedForall, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessMapBounded.formula_l, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 传递陪域使有界检查式覆盖环境中的所有潜在输出成员。 -/
theorem recursive_l {I E T G : Raw} (hG : partial_l I E T G)
    (hT : ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T) :
    PowerlessRelativeMembershipCollapseInjectivity.recursive_l hℳ E G := by
  intro x y hx hxy z
  have hyT := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 hxy).2
  constructor
  · intro hzy
    exact (hG.2.2.2 x hx y hyT hxy z (hT y hyT z hzy)).mp hzy
  · rintro ⟨a, ha, hax, haz⟩
    have hzT := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 haz).2
    exact (hG.2.2.2 x hx y hyT hxy z hzT).mpr ⟨a, ha, hax, haz⟩

def point_m {Γ Δ : SortContext ℒ} (E H G x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (member_m x E) <| .forallE .set <| .forallE .set <|
    .imp (value_m (up (up H)) (up (up x)) (.bvar (.there .here))) <|
      .imp (value_m (up (up G)) (up (up x)) (.bvar .here))
        (.equal (.bvar (.there .here)) (.bvar .here))

theorem point_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (E H G x : Term ℒ Γ Δ .set) : (point_m E H G x).satisfies η ↔
      (mem_l hℳ (x.eval η) (E.eval η) → ∀ y z,
        SecondOrderFunctionObjects.value_l hℳ (H.eval η) (x.eval η) y →
        SecondOrderFunctionObjects.value_l hℳ (G.eval η) (x.eval η) z → y = z) := by
  simp only [point_m, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 归纳只需局部域在 I 的前驱下封闭，不需要源域传递或成员外延性。 -/
theorem agrees_l {I E T H G : Raw}
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hRec : PowerlessRelativeMembershipCollapseInjectivity.recursive_l hℳ I H)
    (hT : ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T)
    (hG : partial_l I E T G) : ∀ x, mem_l hℳ x E → ∀ y z,
      SecondOrderFunctionObjects.value_l hℳ H x y →
      SecondOrderFunctionObjects.value_l hℳ G x z → y = z := by
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree G).pushFree H).pushFree E
  let φ : Formula ℒ [] [.set, .set, .set, .set] := point_m
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar .here)
  have hGRec := recursive_l hG hT
  have hAll : ∀ x, φ.satisfies (η.pushFree x) := by
    apply PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    intro x ih
    apply (point_formula_l (η.pushFree x) _ _ _ _).mpr
    intro hx y z hxy hxz
    apply SecondOrderQuotient.ext_l hℳ y z
    intro a
    constructor
    · intro hay
      obtain ⟨b, hbI, hbx, hba⟩ := (hRec x y (hG.1 x hx) hxy a).mp hay
      have hbE := hG.2.1 x hx b hbI hbx
      obtain ⟨c, hc, _⟩ := hG.2.2.1.2 b hbE
      have hac := (point_formula_l (η.pushFree b) _ _ _ _).mp (ih b hbx) hbE a c hba hc.2
      exact (hGRec x z hx hxz a).mpr ⟨b, hbE, hbx, hac.symm ▸ hc.2⟩
    · intro haz
      obtain ⟨b, hbE, hbx, hba⟩ := (hGRec x z hx hxz a).mp haz
      obtain ⟨c, hc, _⟩ := hH.2 b (hG.1 b hbE)
      have hca := (point_formula_l (η.pushFree b) _ _ _ _).mp (ih b hbx) hbE c a hc.2 hba
      exact (hRec x y (hG.1 x hx) hxy a).mpr ⟨b, hG.1 b hbE, hbx, hca ▸ hc.2⟩
  exact fun x => (point_formula_l (η.pushFree x) _ _ _ _).mp (hAll x)

theorem value_l {I E T H G : Raw}
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hRec : PowerlessRelativeMembershipCollapseInjectivity.recursive_l hℳ I H)
    (hT : ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T)
    (hG : partial_l I E T G) {x y : Raw} (hx : mem_l hℳ x E) :
    SecondOrderFunctionObjects.value_l hℳ G x y ↔ SecondOrderFunctionObjects.value_l hℳ H x y := by
  constructor
  · intro hxy
    obtain ⟨z, hz, _⟩ := hH.2 x (hG.1 x hx)
    exact (agrees_l hH hRec hT hG x hx z y hz.2 hxy) ▸ hz.2
  · intro hxy
    obtain ⟨z, hz, _⟩ := hG.2.2.1.2 x hx
    exact (agrees_l hH hRec hT hG x hx y z hxy hz.2).symm ▸ hz.2

def agreement_m {Γ Δ : SortContext ℒ} (E H G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall E <| .forallE .set <|
    .iff (value_m (up (up G)) (.bvar (.there .here)) (.bvar .here))
      (value_m (up (up H)) (.bvar (.there .here)) (.bvar .here))

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let I : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let E := .fvar (.there .here)
  let T := .fvar (.there (.there .here))
  let H := .fvar (.there (.there (.there .here)))
  let G := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m T) <|
    .imp (SecondOrderObjectSyntax.map_m H I T) <|
      .imp (PowerlessRelativeMembershipCollapseInjectivity.recursive_m I H) <|
        .imp (partial_m I E T G) (agreement_m E H G)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, agreement_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderObjectSyntax.map_l, PowerlessRelativeMembershipCollapseInjectivity.recursive_formula_l,
    formula_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, SecondOrderObjectSyntax.value_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hT hH hRec hG x hx y => value_l hH hRec hT hG hx

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms delta_m
#print axioms agrees_l
#print axioms value_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapsePartial
