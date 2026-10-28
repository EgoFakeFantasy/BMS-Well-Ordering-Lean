import BMSConstructibleBridge.PowerlessDefinableWholeCollapse
import BMSConstructibleBridge.PowerlessRelativeHierarchyDerives

/-! # 同一实际坍缩对传递覆盖种子的固定性

对象语言为纯隶属 ℒ，背景为原 Z₂。归纳性质是实际 project 纯公式，
使用原内部集合归纳，不使用模型外部良基或集合秩。整个种子及其成员
位于原虚拟域时，坍缩在种子上逐点为恒等。T 的传递性是原坍缩规格
的一部分；这里明确保留它，不把任意关系同构误认为环境中的坍缩。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseSeed

open Logic FirstOrder ThirdOrderSemantics
open PowerlessDefinableMembershipIsomorphism
  (image_m image_l image_formula_l project_m project_l project_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeHierarchyDerives (transitive_m transitive_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (v : Term ℒ Γ Δ .set) :=
  v.weakenBound SetTheory.SetSort.set

private theorem env_id_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) : PowerlessDefinableMembershipDiagram.env_l η (fun v => .fvar v) =
      parameters_l η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v; cases s; rfl

def cover_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up S))
    (image_m φ (up C) (.bvar .here) (fun v => .fvar v))

def fixed_m {Γ Θ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C S T H x : Term ℒ Γ Θ .set) (τ : Variable Δ .set → Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  .imp (SecondOrderObjectSyntax.member_m x S) <|
    .conj (SecondOrderObjectSyntax.member_m x T) (project_m φ C H x x τ)

theorem fixed_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Θ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Θ)
    (C S T H x : Term ℒ Γ Θ .set) (τ : Variable Δ .set → Term ℒ Γ Θ .set) :
    (fixed_m φ C S T H x τ).satisfies η ↔
      (member_l 𝒩 (x.eval η) (S.eval η) → member_l 𝒩 (x.eval η) (T.eval η) ∧
        project_l φ (PowerlessDefinableMembershipDiagram.env_l η τ)
          (C.eval η) (H.eval η) (x.eval η) (x.eval η)) := by
  simp only [fixed_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, project_formula_l]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

private theorem step_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {C T H : Raw}
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hT : ∀ x, ε x T → ∀ z, ε z x → ε z T)
    (x : Raw) (hx : image_l φ η C x)
    (ih : ∀ z, ε z x → ε z T ∧ project_l φ η C H z z) :
    ε x T ∧ project_l φ η C H x x := by
  obtain ⟨y, hy, hxy⟩ := hIso.1 x hx
  have hEq : x = y := SecondOrderQuotient.ext_l hℳ x y (fun z => by
    constructor
    · intro hzx
      have hz := ih z hzx
      exact (hIso.2.2.2.1 z x z y hz.2 hxy).mp hzx
    · intro hzy
      obtain ⟨w, hwz⟩ := hIso.2.2.2.2 z (hT y hy z hzy)
      have hwx := (hIso.2.2.2.1 w x z y hwz hxy).mpr hzy
      have hw := ih w hwx
      have hzw : z = w := hIso.2.2.1 w z w hwz hw.2
      rw [hzw]
      exact hwx)
  simpa only [← hEq] using And.intro hy hxy

/-- 内部集合归纳固定种子成员，不假定原虚拟像是集合或传递。 -/
theorem fixed_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C S T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hS : ∀ x, ε x S → ∀ z, ε z x → ε z S)
    (hT : ∀ x, ε x T → ∀ z, ε z x → ε z T)
    (hCover : ∀ x, ε x S → image_l φ η C x) :
    ∀ x, ε x S → ε x T ∧ project_l φ η C H x x := by
  let ξ : Env 𝒱 [] (.set :: .set :: .set :: .set :: Δ) :=
    (((η.pushFree C).pushFree S).pushFree T).pushFree H
  let ψ : Formula ℒ [] (.set :: .set :: .set :: .set :: .set :: Δ) :=
    fixed_m φ (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
        (fun v => .fvar (.there (.there (.there (.there (.there v))))))
  have hEnv (x : Raw) : PowerlessDefinableMembershipDiagram.env_l
      (ξ.pushFree (sort := SetTheory.SetSort.set) x)
        (fun v => .fvar (.there (.there (.there (.there (.there v)))))) = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; rfl
  have hFormula (x : Raw) : ψ.satisfies (ξ.pushFree x) ↔
      (ε x S → ε x T ∧ project_l φ η C H x x) := by
    simp only [ψ, fixed_formula_l, hEnv, ξ, Term.eval,
      Env.pushFree_here, Env.pushFree_there, member_l, SecondOrderQuotient.structure_l]
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) ψ ξ
    (fun x ih => (hFormula x).mpr (fun hx => step_l φ η hIso hT x (hCover x hx)
      (fun z hz => (hFormula z).mp (ih z hz) (hS x hx z hz))))
  exact fun x => (hFormula x).mp (hAll x)

theorem seed_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C S T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hS : ∀ x, ε x S → ∀ z, ε z x → ε z S)
    (hT : ∀ x, ε x T → ∀ z, ε z x → ε z T)
    (hCover : ∀ x, ε x S → image_l φ η C x) (hSI : image_l φ η C S) :
    ε S T ∧ project_l φ η C H S S := by
  -- 种子本身仅用 S∈虚拟域，不要求不可能的 S∈S。
  exact step_l φ η hIso hT S hSI (fixed_l φ η C S T H hIso hS hT hCover)

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C S T H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set <| fixed_m φ (up C) (up S) (up T) (up H) (.bvar .here) (fun v => .fvar v))
    (.conj (SecondOrderObjectSyntax.member_m S T) (project_m φ C H S S (fun v => .fvar v)))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C S T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessDefinableWholeCollapse.isomorphism_m φ C T H) <|
    .imp (transitive_m S) <| .imp (transitive_m T) <|
      .imp (cover_m φ C S) <| .imp (image_m φ C S (fun v => .fvar v))
        (conclusion_m φ C S T H)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C S T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ C S T H)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (C S T H : Term ℒ [] Δ .set) :
    (sentence_m φ C S T H).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessDefinableWholeCollapse.isomorphism_formula_l,
    transitive_formula_l h𝒩, cover_m, image_formula_l, env_id_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here]
  intro hIso hS hT hCover hSI
  simp only [conclusion_m, Formula.satisfies, fixed_formula_l, project_formula_l, env_id_l,
    parameters_pushBound_l, parameters_empty_l, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, SecondOrderObjectSyntax.member_m, Arguments.eval,
    member_l, SecondOrderQuotient.structure_l]
  exact ⟨fixed_l φ η (C.eval η) (S.eval η) (T.eval η) (H.eval η) hIso hS hT hCover,
    seed_l φ η (C.eval η) (S.eval η) (T.eval η) (H.eval η) hIso hS hT hCover hSI⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C S T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ C S T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ C S T H)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseSeed
