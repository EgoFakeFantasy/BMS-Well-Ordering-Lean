import BMSConstructibleBridge.PowerlessVirtualHullExtensionality

/-! # 全部内部数码上的实际坍缩与总同构

纯隶属语言、原 Z₂。固定纯求值在内部 ω 上总定义且单值，虚拟全像
外延，并有同一全像中的真实单集上邻，则每个数码都属于实际隶属图
域域。直接复用原代码图及集合坍缩，得到定义于整个 ω 的实际函数。
全部原输出均有坍缩值，关系单值、单射、隶属双向对应，并满射到同一
传递 raw 值域。不收集原全像，不使用外部良基或 Type 选择。
这些纯求值条件须由同一实际程序装配；本模块不预称 T/H 属于 Class，
也不替代元素性、凝聚、严格阶段界或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableWholeCollapse

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l at_m at_formula_l)
open PowerlessDefinableMembershipIsomorphism
  (image_m image_l image_formula_l project_m project_l project_formula_l point_l point_formula_l ext_m ext_l ext_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

private theorem env_id_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) : PowerlessDefinableMembershipDiagram.env_l η (fun v => .fvar v) = parameters_l η := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; rfl

def defined_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up C)) <|
    .existsE .set <| at_m φ (.bvar (.there .here)) (.bvar .here)

private def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C T H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (image_m φ (up C) (.bvar .here) (fun v => .fvar v)) <|
    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ T))
      (project_m φ (up₂ C) (up₂ H) (.bvar (.there .here)) (.bvar .here) (fun v => .fvar v))

def isomorphism_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C T H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (total_m φ C T H) (PowerlessDefinableMembershipIsomorphism.conclusion_m φ C H T)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

def isomorphism_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw) : Prop :=
  (∀ x, image_l φ η C x → ∃ y, ε y T ∧ project_l φ η C H x y) ∧
  (∀ x, point_l φ η C H x) ∧
  (∀ x y z, project_l φ η C H x y → project_l φ η C H x z → y = z) ∧
  (∀ x y a b, project_l φ η C H x a → project_l φ η C H y b → (ε x y ↔ ε a b)) ∧
  (∀ y, ε y T → ∃ x, project_l φ η C H x y)

theorem isomorphism_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (C T H : Term ℒ Γ Δ .set) :
    (isomorphism_m φ C T H).satisfies η ↔
      isomorphism_l φ (parameters_l η) (C.eval η) (T.eval η) (H.eval η) := by
  simp only [isomorphism_m, total_m, PowerlessDefinableMembershipIsomorphism.conclusion_m,
    isomorphism_l, Formula.satisfies, image_formula_l, point_formula_l, project_formula_l,
    env_id_l, parameters_pushBound_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (hUnique : ∀ n x y, ε n K.omega → φ.satisfies ((η.pushFree n).pushFree x) →
      φ.satisfies ((η.pushFree n).pushFree y) → x = y)
    (hCode : ∀ n, ε n K.omega → ∃ x, φ.satisfies ((η.pushFree n).pushFree x))
    (hExt : ext_l φ η K.omega)
    (hUpper : ∀ x, image_l φ η K.omega x → ∃ z, image_l φ η K.omega z ∧
      SecondOrderPairObjects.pair_l hℳ x x z) :
    ∃ A T H : Raw, PowerlessDefinableMembershipDiagram.spec_l φ η K.omega A ∧
      PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A K.omega ∧
      SecondOrderCollapseFunction.spec_l hℳ A K.omega T H ∧ isomorphism_l φ η K.omega T H := by
  obtain ⟨A, D, T, H, hA, hD, hH⟩ := PowerlessDefinableMembershipCollapse.exists_l K φ η hUnique
  have hDω := PowerlessVirtualHullExtensionality.domain_l φ η hA hD hCode hUpper
  subst D
  refine ⟨A, T, H, hA, hD, hH, ?_,
    PowerlessDefinableMembershipIsomorphism.injective_l φ η hUnique hA hD hH hExt,
    (fun x y z hy hz => PowerlessDefinableMembershipIsomorphism.same_l φ η hUnique hA hD hH hy hz),
    (fun x y a b hx hy => PowerlessDefinableMembershipIsomorphism.member_l φ η hUnique hA hD hH hExt hx hy),
    PowerlessDefinableMembershipIsomorphism.onto_l φ η hA hD hH⟩
  rintro x ⟨n, hn, hnx⟩
  obtain ⟨y, ⟨hy, hny⟩, _⟩ := hH.2.1.2 n hn
  exact ⟨y, hy, n, hn, hnx, hny⟩

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let A : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let T := .bvar (.there .here)
    let H := .bvar .here
    .conj (PowerlessDefinableMembershipDiagram.spec_m φ (up₃ ω) A) <|
      .conj (PowerlessDefinableMembershipCollapse.domain_m A (up₃ ω)) <|
        .conj (SecondOrderCollapseSyntax.formula_m A (up₃ ω) T H)
          (isomorphism_m φ (up₃ ω) T H)

theorem conclusion_formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 Γ Δ) (ω : Term ℒ Γ Δ .set) :
    (conclusion_m φ ω).satisfies η ↔ ∃ A T H : Raw,
      PowerlessDefinableMembershipDiagram.spec_l φ (parameters_l η) (ω.eval η) A ∧
        PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A (ω.eval η) ∧
          SecondOrderCollapseFunction.spec_l hℳ A (ω.eval η) T H ∧
            isomorphism_l φ (parameters_l η) (ω.eval η) T H := by
  simp only [conclusion_m, Formula.satisfies, PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessDefinableMembershipCollapse.domain_formula_l, SecondOrderCollapseSyntax.formula_l,
    isomorphism_formula_l, parameters_pushBound_l, up₃, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
    .imp (PowerlessBMSQuotientSubsetImageDerives.unique_m φ (.bvar .here)) <|
      .imp (defined_m φ (.bvar .here)) <| .imp (ext_m φ (.bvar .here) (fun v => .fvar v)) <|
        .imp (PowerlessVirtualHullExtensionality.upper_m φ (.bvar .here))
          (conclusion_m φ (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, defined_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    PowerlessBMSQuotientSubsetImageDerives.unique_m, at_formula_l, ext_formula_l,
    PowerlessVirtualHullExtensionality.upper_m, image_formula_l,
    SecondOrderObjectSyntax.pair_l h𝒩, env_id_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there, and_imp]
  intro η ω hω hUnique hCode hExt hUpper
  obtain rfl := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  obtain ⟨A, T, H, hA, hD, hH, hIso⟩ := exists_l K φ η hUnique hCode hExt hUpper
  simp only [conclusion_formula_l, parameters_pushBound_l, parameters_empty_l,
    Term.eval, Env.pushBound_bound_here]
  exact ⟨A, T, H, hA, hD, hH, hIso⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableWholeCollapse
