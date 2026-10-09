import BMSConstructibleBridge.PowerlessHereditaryIntrinsicUniformRange
import BMSConstructibleBridge.PowerlessHereditaryRelativization
import BMSConstructibleBridge.PowerlessHereditaryParameterEnvelope

/-! # 遗传请求的环境收集模式之原 Z₂ 推导

对象语言纯隶属 ℒ，背景原 SecondOrderArithmetic.theory_m，推导关系
原 Derives。每个有限原公式实例的遗传见证由一个环境商集合覆盖，
且集合中的全部对象仍是相应原请求的遗传见证。正文真值在实际
Hereditary 子模型读取，不用 Class 真值替代。

结论没有给 C 添加遗传 guard；这是环境收集，不是 Hereditary
Collection 公理，更不是最终固定高度 BMS 良序 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryAmbientCollectionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessHereditaryStructure.structure_l PowerlessHereditaryStructure.type_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)
private abbrev up₃ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up₂ t)

def request_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B n X : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  (PowerlessHereditaryRelativization.formula_m φ).substitute
    (show Substitution ℒ [] (.set :: .set :: .set :: Δ) Γ Ε from
      .map (fun v => nomatch v) (fun {s} v => match s with
        | .set => match v with
          | .here => B
          | .there .here => X
          | .there (.there .here) => n
          | .there (.there (.there v)) => τ v))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Ε)
    (B : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) (n X : carrier_l 𝒩) : Prop :=
  (PowerlessHereditaryRelativization.formula_m φ).satisfies
    ((((PowerlessDefinableMembershipDiagram.env_l η τ).pushFree n).pushFree X).pushFree (B.eval η))

theorem request_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Ε)
    (B n X : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (request_m φ B n X τ).satisfies η ↔ holds_l φ η B τ (n.eval η) (X.eval η) := by
  rw [request_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => (PowerlessHereditaryRelativization.formula_m φ).satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v <;> rfl

private theorem env_push_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Ε Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Ε) (τ : Variable Δ .set → Term ℒ Γ Ε .set) (x : carrier_l 𝒩) :
    PowerlessDefinableMembershipDiagram.env_l (η.pushBound x) (fun v => up (τ v)) =
      PowerlessDefinableMembershipDiagram.env_l η τ := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; exact Term.eval_weakenBound _ _ _

def some_m {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (PowerlessHereditaryClass.formula_m (up₂ B) (.bvar .here))
      (request_m φ (up₂ B) (.bvar (.there .here)) (.bvar .here) (fun v => up₂ (τ v)))

def conclusion_m {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .existsE .set <| .conj
    (.forallE .set <| .imp
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))) <|
      .conj (PowerlessHereditaryClass.formula_m (up₂ B) (.bvar .here)) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₃ ω))
          (request_m φ (up₃ B) (.bvar .here) (.bvar (.there .here)) (fun v => up₃ (τ v))))
    (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ ω)) <|
      .existsE .set <| .conj
        (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here)))) <|
        .conj (PowerlessHereditaryClass.formula_m (up₃ B) (.bvar .here))
          (request_m φ (up₃ B) (.bvar (.there .here)) (.bvar .here) (fun v => up₃ (τ v))))

def schema_m {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω : Term ℒ [] Ε .set) (ν : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (up B))) <|
          .imp (PowerlessHereditaryParameterEnvelope.parameters_m Δ B ν) <|
            .imp (some_m φ B ω ν) (conclusion_m φ B ω ν)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem some_formula_l (K : source_coding_l hℳ) {Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Ε)
    (B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (some_m φ B ω τ).satisfies η ↔ ∀ n, mem_l hℳ n (ω.eval η) → ∃ X,
      PowerlessHereditaryClass.member_l hℳ (B.eval η) X ∧ holds_l φ η B τ n X := by
  simp only [some_m, Formula.satisfies, PowerlessHereditaryClass.formula_l K, request_formula_l,
    holds_l, env_push_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem conclusion_formula_l (K : source_coding_l hℳ) {Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Ε)
    (B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (conclusion_m φ B ω τ).satisfies η ↔ ∃ C,
      (∀ X, mem_l hℳ X C → PowerlessHereditaryClass.member_l hℳ (B.eval η) X ∧
        ∃ n, mem_l hℳ n (ω.eval η) ∧ holds_l φ η B τ n X) ∧
      ∀ n, mem_l hℳ n (ω.eval η) → ∃ X, mem_l hℳ X C ∧
        PowerlessHereditaryClass.member_l hℳ (B.eval η) X ∧ holds_l φ η B τ n X := by
  simp only [conclusion_m, Formula.satisfies, PowerlessHereditaryClass.formula_l K, request_formula_l,
    holds_l, env_push_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem reading_l (K : source_coding_l hℳ) {B₀ : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B₀ → ∀ y, mem_l hℳ y x → mem_l hℳ y B₀}
    {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Ε)
    (B : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (χ : Env (PowerlessHereditaryStructure.structure_l hℳ B₀ hBase) [] Δ)
    (hb : B.eval η = B₀) (hτ : ∀ v : Variable Δ .set, (τ v).eval η = (χ.freeVal v).val)
    (x X : PowerlessHereditaryStructure.type_l hℳ B₀) :
    holds_l φ η B τ x.val X.val ↔ φ.satisfies ((χ.pushFree x).pushFree X) := by
  have hEnv :
      (((PowerlessDefinableMembershipDiagram.env_l η τ).pushFree
        (sort := SetTheory.SetSort.set) x.val).pushFree
          (sort := SetTheory.SetSort.set) X.val).pushFree (sort := SetTheory.SetSort.set) (B.eval η) =
        (PowerlessHereditaryRelativization.env_l ((χ.pushFree
          (sort := SetTheory.SetSort.set) x).pushFree (sort := SetTheory.SetSort.set) X)).pushFree
            (sort := SetTheory.SetSort.set) B₀ := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => exact hb
      | there v => cases v with
        | here => rfl
        | there v => cases v with
          | here => rfl
          | there v => exact hτ v
  unfold holds_l
  rw [hEnv]
  exact PowerlessHereditaryRelativization.formula_l K φ ((χ.pushFree x).pushFree X)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B ω : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Δ [] Ε) :
    (Metatheory.Formula.forall_close (schema_m φ B ω ν)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessHereditaryClass.formula_l K,
    PowerlessHereditaryParameterEnvelope.parameters_formula_l K,
    some_formula_l K, conclusion_formula_l K, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hB hNonempty hParams hSome
  have hωEq := SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  let χ : Env (PowerlessHereditaryStructure.structure_l h𝒩 (B.eval η) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨(ν v).eval η, hParams _ v⟩ }
  have hRead (x X : PowerlessHereditaryStructure.type_l h𝒩 (B.eval η)) :=
    reading_l (hBase := hBase) K φ η B ν χ rfl (fun _ => rfl) x X
  have hSome' (x : PowerlessHereditaryStructure.type_l h𝒩 (B.eval η))
      (hx : mem_l h𝒩 x.val K.omega) : ∃ X : PowerlessHereditaryStructure.type_l h𝒩 (B.eval η),
        φ.satisfies ((χ.pushFree x).pushFree X) := by
    obtain ⟨X, hXHC, hφ⟩ := hSome x.val (hωEq.symm ▸ hx)
    let X₀ : PowerlessHereditaryStructure.type_l h𝒩 (B.eval η) := ⟨X, hXHC⟩
    exact ⟨X₀, (hRead x X₀).mp hφ⟩
  obtain ⟨_U, _hU, _H, _hTrace, C, hRange, hCover⟩ :=
    PowerlessHereditaryIntrinsicUniformRange.exists_l K hB hNonempty φ χ hSome'
  refine ⟨C, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨x, X, hx, hXZ, hφ⟩ := hRange Z hZ
    exact ⟨hXZ ▸ X.property, x.val, hωEq.symm ▸ hx, hXZ ▸ (hRead x X).mpr hφ⟩
  · intro x hx
    have hxK : mem_l h𝒩 x K.omega := hωEq ▸ hx
    let x₀ : PowerlessHereditaryStructure.type_l h𝒩 (B.eval η) :=
      ⟨x, PowerlessHereditaryClass.transitive_l h𝒩
        (PowerlessHereditaryOmega.member_l h𝒩 hBase K.omega_spec) hxK⟩
    obtain ⟨X, hXC, hφ⟩ := hCover x₀ hxK
    exact ⟨X.val, hXC, X.property, (hRead x₀ X).mpr hφ⟩

theorem derives_m {Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω : Term ℒ [] Ε .set) (ν : VariableSubstitution ℒ Δ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m φ B ω ν))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B ω ν)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryAmbientCollectionDerives
