import BMSConstructibleBridge.PowerlessRelativeClassEnumerationClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramDomain
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationSectionDerives

/-! # 从原包络枚举构造另一套分离程序域

纯隶属 ℒ，背景原 Z₂。给定实际 Class 中的内部 ω 满射到 D，
实际构造 C=D∪{D} 及其 Class 枚举，再构造三类指令字母表和全部
内部有限程序码域。D 的原成员全部仍在 C，且 D 本身在 C；
不要求 C 进入 D，也不重用原数码求值的常量种子。

对象出口保留原 D/ω/标签，绑定新 C/G/Q/S/P。D 的传递性、
原参数的包络归属及标签互异性由调用处另证，本文件不改变这些义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramEnvelopeDomain

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₄ t)

def seed_m {Γ Δ : SortContext ℒ} (D C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up C))
    (.disj (SecondOrderObjectSyntax.member_m (.bvar .here) (up D))
      (.equal (.bvar .here) (up D)))

def packet_m {Γ Δ : SortContext ℒ}
    (B ω D C G t₀ t₁ t₂ Q S P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B C) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m B G) <|
      .conj (SecondOrderObjectSyntax.map_m G ω C) <|
        .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
          .conj (seed_m D C) <|
            .conj (PowerlessRelativeHierarchySyntax.class_m B Q) <|
              .conj (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q)
                (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P)

def conclusion_m {Γ Δ : SortContext ℒ} (B ω D t₀ t₁ t₂ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    packet_m (up₅ B) (up₅ ω) (up₅ D)
      (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
      (up₅ t₀) (up₅ t₁) (up₅ t₂)
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

def packet_l (B ω D C G t₀ t₁ t₂ Q S P : SecondOrderQuotient.type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B C ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B G ∧
      map_l (ℳ := 𝒱) G ω C ∧
        (∀ x, ε x C → ∃ i, ε i ω ∧ value_l (ℳ := 𝒱) G i x) ∧
          (∀ x, ε x C ↔ ε x D ∨ x = D) ∧
            PowerlessRelativeClassCorrespondence.member_l hℳ B Q ∧
              (∀ q, ε q Q ↔ PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q) ∧
                PowerlessRelativeFiniteProgramDomain.domain_l B ω Q S P

theorem exists_l {B ω D F t₀ t₁ t₂ : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, ε x B → ∀ y, ε y x → ε y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hD : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hF : PowerlessRelativeClassCorrespondence.member_l hℳ B F)
    (hMap : map_l (ℳ := 𝒱) F ω D)
    (hOnto : ∀ x, ε x D → ∃ i, ε i ω ∧ value_l (ℳ := 𝒱) F i x)
    (h₀ : PowerlessRelativeClassCorrespondence.member_l hℳ B t₀)
    (h₁ : PowerlessRelativeClassCorrespondence.member_l hℳ B t₁)
    (h₂ : PowerlessRelativeClassCorrespondence.member_l hℳ B t₂) :
    ∃ C G Q S P, packet_l B ω D C G t₀ t₁ t₂ Q S P := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωC := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, hωC⟩
  let T : PowerlessRelativeClassStructure.type_l hℳ B := ⟨D, hD⟩
  let J : PowerlessRelativeClassStructure.type_l hℳ B := ⟨F, hF⟩
  obtain ⟨C, G, hRead, hG, hGOnto⟩ := PowerlessRelativeClassEnumerationClosure.adjoin_l
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω)
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) J O T).mpr hMap)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) J O T).mpr hOnto) T
  have hRawRead (x : SecondOrderQuotient.type_l hℳ) :
      ε x C.val ↔ ε x D ∨ x = D := by
    constructor
    · intro hx
      let x' : PowerlessRelativeClassStructure.type_l hℳ B :=
        ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property hx⟩
      exact ((hRead x').mp hx).elim Or.inl (fun h => Or.inr (congrArg Subtype.val h))
    · rintro (hx | rfl)
      · let x' : PowerlessRelativeClassStructure.type_l hℳ B :=
          ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hD hx⟩
        exact (hRead x').mpr (Or.inl hx)
      · exact (hRead T).mpr (Or.inr rfl)
  obtain ⟨Q, hQ, hAlphabet⟩ := PowerlessRelativeFiniteProgramAlphabet.exists_l
    hBase C.property hωC h₀ h₁ h₂
  obtain ⟨S, P, hDomain⟩ := PowerlessRelativeFiniteProgramDomain.exists_l hBase hω hωC hQ
  exact ⟨C.val, G.val, Q, S, P, C.property, G.property,
    (PowerlessRelativeClassFunctionAbsolute.map_l G O C).mp hG,
    (PowerlessRelativeClassFunctionAbsolute.onto_l G O C).mp hGOnto,
    hRawRead, hQ, hAlphabet, hDomain⟩

theorem seed_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (D C : Term ℒ Γ Δ .set) : (seed_m D C).satisfies η ↔
    ∀ x, ε x (C.eval η) ↔ ε x (D.eval η) ∨ x = D.eval η := by
  simp only [seed_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem packet_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (B ω D C G t₀ t₁ t₂ Q S P : Term ℒ Γ Δ .set) :
    (packet_m B ω D C G t₀ t₁ t₂ Q S P).satisfies η ↔
      packet_l (B.eval η) (ω.eval η) (D.eval η) (C.eval η) (G.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (Q.eval η) (S.eval η) (P.eval η) := by
  simp only [packet_m, packet_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, seed_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K]
  rfl

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω D t₀ t₁ t₂ : Term ℒ Γ Δ .set) :
    (conclusion_m B ω D t₀ t₁ t₂).satisfies η ↔
      ∃ C G Q S P, packet_l (B.eval η) (ω.eval η) (D.eval η) C G
        (t₀.eval η) (t₁.eval η) (t₂.eval η) Q S P := by
  simp only [conclusion_m, Formula.satisfies, packet_formula_l K,
    up₅, up₄, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

def schema_m {Δ : SortContext ℒ} (B ω D F t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B D) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B F) <|
          .imp (SecondOrderObjectSyntax.map_m F ω D) <|
            .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m F ω D) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
                .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
                  .imp (PowerlessRelativeHierarchySyntax.class_m B t₂)
                    (conclusion_m B ω D t₀ t₁ t₂)

def sentence_m {Δ : SortContext ℒ} (B ω D F t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω D F t₀ t₁ t₂)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω D F t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m B ω D F t₀ t₁ t₂).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, packet_formula_l K,
    up₅, up₄, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro η hBase hω hD hF hMap hOnto h₀ h₁ h₂
  exact exists_l hBase hω hD hF hMap hOnto h₀ h₁ h₂

theorem derives_m {Δ : SortContext ℒ} (B ω D F t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω D F t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω D F t₀ t₁ t₂)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramEnvelopeDomain
