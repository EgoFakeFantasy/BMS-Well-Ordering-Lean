import BMSConstructibleBridge.PowerlessHereditaryPairing
import BMSConstructibleBridge.PowerlessHereditaryTransitiveSuperset
import BMSConstructibleBridge.PowerlessHereditaryOmega
import BMSConstructibleBridge.PowerlessRelativeClassParameterSeedLift

/-! # 原有限遗传参数的共同可数传递包络

对象语言为纯隶属 ℒ，背景为原 Z₂。参数上下文 Δ 与装配上下文 Ε
分开；只包住指定的原参数，不把后取的包络、种子或全局编码元数据
倒灌进参数列表。外部有限上下文归纳合并实际遗传证书，再取得一张
真正属于 Class 的内部 ω 满射。对象出口是原核中的 Derives。

此处需要基底及原参数的遗传性，不能由 Class 资格代替。内部 ω
不假定外部标准；没有抽取 Type 层的包络或枚举选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterEnvelope

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)

def parameters_m {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) : Formula ℒ Γ Ε :=
  match Δ with
  | [] => .truth
  | .set :: Δ => .conj (PowerlessHereditaryClass.formula_m B (τ .here))
      (parameters_m Δ B (fun v => τ (.there v)))

def conclusion_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .existsE .set <| .existsE .set <|
    let D := .bvar (.there .here)
    let F := .bvar .here
    .conj (PowerlessHereditaryClass.body_m (up₂ B) (up₂ B) D F (up₂ ω)) <|
      .conj (SecondOrderObjectSyntax.member_m (up₂ ω) D)
        (PowerlessRelativeClassParameterSeed.members_m Δ D (fun v => up₂ (τ v)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

private theorem pair_l {B x y : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ z, ε z B → ∀ t, ε t z → ε t B)
    (hx : PowerlessHereditaryClass.member_l hℳ B x)
    (hy : PowerlessHereditaryClass.member_l hℳ B y) :
    ∃ P, PowerlessHereditaryClass.member_l hℳ B P ∧ ∀ z, ε z P ↔ z = x ∨ z = y := by
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ x y
  let X : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨x, PowerlessHereditaryClass.contained_l hℳ hBase hx⟩
  let Y : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨y, PowerlessHereditaryClass.contained_l hℳ hBase hy⟩
  let Z : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨P, PowerlessRelativeClassPair.pair_l hℳ hBase X.property Y.property hP⟩
  have hRead (z : PowerlessRelativeClassStructure.type_l hℳ B) :
      ε z.val Z.val ↔ z = X ∨ z = Y :=
    (hP z.val).trans (or_congr
      ⟨fun h => Subtype.ext (show z.val = X.val from h), congrArg Subtype.val⟩
      ⟨fun h => Subtype.ext (show z.val = Y.val from h), congrArg Subtype.val⟩)
  have hZ := PowerlessHereditaryPairEnvelope.exists_l
    ((PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X).mp hx)
    ((PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) Y).mp hy) hRead
  exact ⟨P, (PowerlessHereditaryClassInternals.correspondence_l
    (hBase := hBase) Z).mpr hZ, hP⟩

private theorem cover_l {B ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ z, ε z B → ∀ t, ε t z → ε t B)
    (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hω : SecondOrderOmega.omega_l hℳ ω) {Δ : SortContext ℒ}
    (η : Env 𝒱 [] Δ)
    (hParams : ∀ s (v : Variable Δ s), PowerlessHereditaryClass.member_l hℳ B (η.freeVal v)) :
    ∃ D, PowerlessHereditaryClass.member_l hℳ B D ∧
      (∀ x, ε x D → ∀ y, ε y x → ε y D) ∧ ε B D ∧ ε ω D ∧
        ∀ s (v : Variable Δ s), ε (η.freeVal v) D := by
  induction Δ with
  | nil =>
      obtain ⟨P, hP, hRead⟩ := pair_l hBase hB
        (PowerlessHereditaryOmega.member_l hℳ hBase hω)
      obtain ⟨D, hD, hPD, hTrans⟩ :=
        PowerlessHereditaryTransitiveSuperset.exists_l hℳ hBase hP
      exact ⟨D, hD, hTrans, hTrans P hPD B ((hRead B).mpr (Or.inl rfl)),
        hTrans P hPD ω ((hRead ω).mpr (Or.inr rfl)), fun _ v => nomatch v⟩
  | cons s Δ ih =>
      cases s
      let ξ : Env 𝒱 [] Δ :=
        { boundVal := η.boundVal, freeVal := fun v => η.freeVal (.there v) }
      obtain ⟨D, hD, _hTrans, hBD, hωD, hMembers⟩ :=
        ih ξ (fun s v => hParams s (.there v))
      obtain ⟨P, hP, hRead⟩ := pair_l hBase hD (hParams _ .here)
      obtain ⟨T, hT, hPT, hTrans⟩ :=
        PowerlessHereditaryTransitiveSuperset.exists_l hℳ hBase hP
      have hDT : ε D T := hTrans P hPT D ((hRead D).mpr (Or.inl rfl))
      refine ⟨T, hT, hTrans, hTrans D hDT B hBD, hTrans D hDT ω hωD, ?_⟩
      intro s v
      cases s
      cases v with
      | here =>
          exact hTrans P hPT (η.freeVal .here)
            ((hRead (η.freeVal .here)).mpr (Or.inr rfl))
      | there v => exact hTrans D hDT (η.freeVal (.there v)) (hMembers _ v)

theorem exists_l {B ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ z, ε z B → ∀ t, ε t z → ε t B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hB : PowerlessHereditaryClass.member_l hℳ B B)
    {Ε : SortContext ℒ} (Δ : SortContext ℒ) (η : Env 𝒱 [] Ε)
    (τ : VariableSubstitution ℒ Δ [] Ε)
    (hParams : ∀ s (v : Variable Δ s),
      PowerlessHereditaryClass.member_l hℳ B ((τ v).eval η)) :
    ∃ D F, PowerlessHereditaryClass.body_l hℳ B B D F ω ∧ ε ω D ∧
      ∀ s (v : Variable Δ s), ε ((τ v).eval η) D := by
  let ξ : Env 𝒱 [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun v => (τ v).eval η }
  obtain ⟨T, hT, _hTrans, hBT, hωT, hMembers⟩ := cover_l hBase hB hω ξ hParams
  obtain ⟨D, F, w, hD, hF, hTD, hTrans, hw, hMap, hOnto⟩ := hT
  have hwEq := SecondOrderOmega.unique_l hℳ hw hω
  rw [hwEq] at hMap hOnto
  exact ⟨D, F, ⟨hD, hF, hTrans T hTD B hBT, hTrans, hω, hMap, hOnto⟩,
    hTrans T hTD ω hωT, fun s v => hTrans T hTD ((τ v).eval η) (hMembers s v)⟩

theorem parameters_formula_l (K : source_coding_l hℳ) {Γ Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (η : Env 𝒱 Γ Ε) (B : Term ℒ Γ Ε .set)
    (τ : VariableSubstitution ℒ Δ Γ Ε) : (parameters_m Δ B τ).satisfies η ↔
    ∀ s (v : Variable Δ s), PowerlessHereditaryClass.member_l hℳ (B.eval η) ((τ v).eval η) := by
  induction Δ with
  | nil =>
      constructor
      · intro _ _ v; nomatch v
      · intro _; trivial
  | cons s Δ ih =>
      cases s
      change (_ ∧ (parameters_m Δ B (fun v => τ (.there v))).satisfies η) ↔ _
      rw [PowerlessHereditaryClass.formula_l K, ih]
      constructor
      · rintro ⟨h₀, h₁⟩ s v
        cases s
        cases v with
        | here => exact h₀
        | there v => exact h₁ _ v
      · intro h
        exact ⟨h _ .here, fun _ v => h _ (.there v)⟩

def schema_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (parameters_m Δ B τ) (conclusion_m Δ B ω τ)

def sentence_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Δ B ω τ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    (sentence_m Δ B ω τ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessHereditaryClass.formula_l K,
    parameters_formula_l K, PowerlessHereditaryClass.body_formula_l K,
    PowerlessRelativeClassParameterSeed.members_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hω hB hParams
  exact exists_l hBase hω hB Δ η τ hParams

theorem derives_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Δ B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 Δ B ω τ)

#print axioms exists_l
#print axioms parameters_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterEnvelope
