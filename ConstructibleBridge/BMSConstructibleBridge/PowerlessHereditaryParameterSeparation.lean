import BMSConstructibleBridge.PowerlessHereditaryProgramParameterDomain
import BMSConstructibleBridge.PowerlessHereditaryAmbientBaseGuard
import BMSConstructibleBridge.PowerlessClassProgramSeparation
import BMSConstructibleBridge.PowerlessRelativeFiniteNumeralTags
import BMSConstructibleBridge.PowerlessRelativeClassReflectedSeparation

/-! # 有限遗传参数的实际 Class 分离

纯隶属 ℒ，背景原 Z₂。实际构造共同可数传递包络及另一套分离种子，
取得内部枚举、字母表、码域、初始帧和环境良序；调用者只给原有限
参数与母集的遗传性，不预供反射、类内枚举或分离程序资源。

原正文按 Class 真值分离，实际输出仍遗传。此处不声称正文在
Hereditary 子模型中同值；该层的完整分离与最终 BMS 良序须另接线。
对象模式直接回到原 Derives，外部有限上下文不假定内部 ω 标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem exists_l {B ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, ε x B → ∀ y, ε y x → ε y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, ε d B) {Θ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: Θ))
    (χ : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] Θ)
    (X : PowerlessRelativeClassStructure.type_l hℳ B)
    (hX : PowerlessHereditaryClass.member_l hℳ B X.val)
    (hParams : ∀ v : Variable Θ .set,
      PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val) :
    ∃ Y : PowerlessRelativeClassStructure.type_l hℳ B,
      PowerlessHereditaryClass.member_l hℳ B Y.val ∧
        ∀ x : PowerlessRelativeClassStructure.type_l hℳ B,
          ε x.val Y.val ↔ ε x.val X.val ∧ ψ.satisfies (χ.pushFree x) := by
  obtain ⟨K, e, r₁, r₂, r₃, Pair, Valid, _hωEq, heEq, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l (PowerlessBMSQuotientOmega.omega_l hℳ hω)
  have he : ∀ x, ¬ε x e := heEq ▸ PowerlessBMSQuotientSuccessor.zero_l K
  obtain ⟨a, ha⟩ := PowerlessRelativeFiniteProgramStep.record_exists_l e e e
  have hωHC := PowerlessHereditaryOmega.member_l hℳ hBase hω
  let t₀ := PowerlessRelativeFiniteNumeralTags.value_l K 0
  let t₁ := PowerlessRelativeFiniteNumeralTags.value_l K 1
  let t₂ := PowerlessRelativeFiniteNumeralTags.value_l K 2
  have h₀ω : ε t₀ ω := PowerlessRelativeFiniteNumeralTags.member_l K hω 0
  have h₁ω : ε t₁ ω := PowerlessRelativeFiniteNumeralTags.member_l K hω 1
  have h₂ω : ε t₂ ω := PowerlessRelativeFiniteNumeralTags.member_l K hω 2
  have h₀ := PowerlessHereditaryClass.contained_l hℳ hBase
    (PowerlessHereditaryClass.transitive_l hℳ hωHC h₀ω)
  have h₁ := PowerlessHereditaryClass.contained_l hℳ hBase
    (PowerlessHereditaryClass.transitive_l hℳ hωHC h₁ω)
  have h₂ := PowerlessHereditaryClass.contained_l hℳ hBase
    (PowerlessHereditaryClass.transitive_l hℳ hωHC h₂ω)
  have ht : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂ :=
    ⟨fun h => (by decide : 0 ≠ 1) (PowerlessRelativeFiniteNumeralTags.injective_l K h),
      fun h => (by decide : 0 ≠ 2) (PowerlessRelativeFiniteNumeralTags.injective_l K h),
      fun h => (by decide : 1 ≠ 2) (PowerlessRelativeFiniteNumeralTags.injective_l K h)⟩
  let ξ : Env 𝒱 [] Θ := PowerlessRelativeClassRelativization.env_l χ
  have hParams' : ∀ s (v : Variable (.set :: Θ) s),
      PowerlessHereditaryClass.member_l hℳ B ((ξ.pushFree (sort := SetTheory.SetSort.set) X.val).freeVal v) := by
    intro s v
    cases s
    cases v with
    | here => exact hX
    | there v => exact hParams v
  let τ : VariableSubstitution ℒ (.set :: Θ) [] (.set :: Θ) := fun v => .fvar v
  obtain ⟨D, F, hEnvelope, hωD, hMembers⟩ := PowerlessHereditaryParameterEnvelope.exists_l
    hBase hω hB (.set :: Θ) (ξ.pushFree (sort := SetTheory.SetSort.set) X.val)
    τ (by intro s v; cases s; exact hParams' _ v)
  obtain ⟨hDClass, hFClass, hBD, hD, _hω, hF, hFOnto⟩ := hEnvelope
  obtain ⟨C, G, Q, S, P, hC, hG, hMap, hOnto, hSeed, hQ, hAlphabet, hDomain⟩ :=
    PowerlessClassProgramEnvelopeDomain.exists_l hBase hω hDClass hFClass hF hFOnto h₀ h₁ h₂
  obtain ⟨P₀, _hP₀HC, hGuard⟩ :=
    PowerlessHereditaryAmbientBaseGuard.exists_l K hBase hω hB hNonempty
  let ζ : Env 𝒱 [] (List.replicate 21 SetTheory.SetSort.set) :=
    PowerlessSourceTuple.env_l (Env.empty (M := 𝒱)) 21
      (.cons ω (.cons e (.cons r₁ (.cons r₂ (.cons r₃ (.cons Pair (.cons Valid (.cons B (.cons P₀ (.cons C (.cons Q (.cons t₀ (.cons t₁ (.cons t₂ (.cons a (.cons G (.cons S (.cons P (.cons t₀ (.cons t₁ (.cons D (.nil))))))))))))))))))))))
  obtain ⟨Y, hRead⟩ := PowerlessClassProgramSeparation.exists_l K ζ
    (.fvar (.here))
    (.fvar (.there (.here)))
    (.fvar (.there (.there (.here))))
    (.fvar (.there (.there (.there (.here)))))
    (.fvar (.there (.there (.there (.there (.here))))))
    (.fvar (.there (.there (.there (.there (.there (.here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))))))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.here))))))))))))))))))))))
    hCoding hω hGuard hC (PowerlessHereditaryClass.contained_l hℳ hBase hωHC)
    hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain
    ((hSeed B).mpr (Or.inl hBD))
    ((hSeed t₀).mpr (Or.inl (hD ω hωD t₀ h₀ω)))
    ((hSeed t₁).mpr (Or.inl (hD ω hωD t₁ h₁ω))) ht.1 hD
    (fun x hx => (hSeed x).mpr (Or.inl hx)) ((hSeed D).mpr (Or.inr rfl))
    hBD hωD ψ χ X (hMembers _ .here) (fun v => hMembers _ (.there v))
  have hSubset : ∀ x, ε x Y.val → ε x X.val := by
    intro x hx
    let x' : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hx⟩
    exact ((hRead x').mp hx).1
  exact ⟨Y, PowerlessHereditarySubset.member_l hℳ hBase hX Y.property hSubset, hRead⟩

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)

def conclusion_m {Θ Ε : SortContext ℒ} (ψ : Formula ℒ [] (.set :: Θ))
    (B X : Term ℒ [] Ε .set) (ν : VariableSubstitution ℒ Θ [] Ε) : Formula ℒ [] Ε :=
  .existsE .set <| .conj (PowerlessHereditaryClass.formula_m (up B) (.bvar .here)) <|
    .forallE .set <| .iff
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ X))
        (PowerlessRelativeClassReflectedSeparation.class_m ψ (up₂ B) (.bvar .here)
          (fun v => up₂ (ν v))))

def schema_m {Θ Ε : SortContext ℒ} (ψ : Formula ℒ [] (.set :: Θ))
    (B ω X : Term ℒ [] Ε .set) (ν : VariableSubstitution ℒ Θ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (up B))) <|
          .imp (PowerlessHereditaryClass.formula_m B X) <|
            .imp (PowerlessHereditaryParameterEnvelope.parameters_m Θ B ν) (conclusion_m ψ B X ν)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Ε : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: Θ)) (B ω X : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Θ [] Ε) :
    (Metatheory.Formula.forall_close (schema_m ψ B ω X ν)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessHereditaryClass.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    PowerlessHereditaryParameterEnvelope.parameters_formula_l K]
  intro η hBase hω hB hNonempty hX hParams
  let χ : Env (PowerlessRelativeClassStructure.structure_l h𝒩 (B.eval η) hBase) [] Θ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨(ν v).eval η, PowerlessHereditaryClass.contained_l h𝒩 hBase (hParams _ v)⟩ }
  let X₀ : PowerlessRelativeClassStructure.type_l h𝒩 (B.eval η) :=
    ⟨X.eval η, PowerlessHereditaryClass.contained_l h𝒩 hBase hX⟩
  obtain ⟨Y, _hYHC, hRead⟩ := exists_l hBase hω hB hNonempty ψ χ X₀ hX (fun v => hParams _ v)
  have hFull := (PowerlessRelativeClassReflectedSeparation.conclusion_formula_l K ψ η B X ν
    χ X₀ rfl (fun _ => rfl)).mpr ⟨Y, hRead⟩
  obtain ⟨Z, hZClass, hRaw⟩ := hFull
  have hZ : PowerlessRelativeClassCorrespondence.member_l h𝒩 (B.eval η) Z := by
    simpa only [PowerlessRelativeClassCorrespondence.member_l, up,
      Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
      (PowerlessRelativeHierarchySemantics.class_formula_l K (η.pushBound Z)
        (up B) (.bvar .here)).mp hZClass
  have hSubset : ∀ x, SecondOrderQuotient.mem_l h𝒩 x Z →
      SecondOrderQuotient.mem_l h𝒩 x (X.eval η) := by
    intro x hx
    simpa only [SecondOrderObjectSyntax.member_m, Formula.satisfies, Arguments.eval,
      Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      SecondOrderQuotient.structure_l] using ((hRaw x).mp hx).1
  refine ⟨Z, ?_, hRaw⟩
  apply (PowerlessHereditaryClass.formula_l K (η.pushBound Z) (up B) (.bvar .here)).mpr
  simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
    PowerlessHereditarySubset.member_l h𝒩 hBase hX hZ hSubset

theorem derives_m {Θ Ε : SortContext ℒ} (ψ : Formula ℒ [] (.set :: Θ))
    (B ω X : Term ℒ [] Ε .set) (ν : VariableSubstitution ℒ Θ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m ψ B ω X ν))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 ψ B ω X ν)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryParameterSeparation
