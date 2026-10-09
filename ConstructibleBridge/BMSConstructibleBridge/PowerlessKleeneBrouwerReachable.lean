import BMSConstructibleBridge.PowerlessKleeneBrouwerEndpoint
import BMSConstructibleBridge.PowerlessKleeneBrouwerPathClass

/-! # 实际可达末节点域及其前驱封闭

纯隶属 ℒ，原 Z₂。D 在实际 Class I 中按「是某条 S 路径的末节点」作 Δ₀
分离，不用根良基谓词筛选。给定 S 的原完整路径规格后，真实前驱追加证明
D 对所有 I 内 A 前驱封闭。根良基向此域的内部传输另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerReachable

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerEndpoint (endpoint_l endpoint_m endpoint_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def reachable_m {Γ Δ : SortContext ℒ} (ω I S a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists S (endpoint_m (up ω) (up I) (.bvar .here) (up a))

theorem reachable_delta_l {Γ Δ : SortContext ℒ} (ω I S a : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (reachable_m ω I S a) :=
  .bounded_exists _ (PowerlessKleeneBrouwerEndpoint.endpoint_delta_l _ _ _ _)

def reading_m {Γ Δ : SortContext ℒ} (ω I S D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up D)) <|
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up I))
      (reachable_m (up ω) (up I) (up S) (.bvar .here))

def closed_m {Γ Δ : SortContext ℒ} (I A D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall D <| membershipLevyBound.boundedForall (up I) <|
    .imp (PowerlessValueBounded.formula_m (up (up A)) (.bvar .here) (.bvar (.there .here)))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up D)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (ω I S D : Raw) : Prop :=
  ∀ a, mem_l hℳ a D ↔ mem_l hℳ a I ∧ ∃ f, mem_l hℳ f S ∧ endpoint_l ω I f a

def closed_l (I A D : Raw) : Prop :=
  ∀ a, mem_l hℳ a D → ∀ b, mem_l hℳ b I → value_l (ℳ := 𝒱) A b a → mem_l hℳ b D

theorem reachable_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω I S a : Term ℒ Γ Δ .set) :
    (reachable_m ω I S a).satisfies η ↔
      ∃ f, mem_l hℳ f (S.eval η) ∧ endpoint_l (ω.eval η) (I.eval η) f (a.eval η) := by
  simp only [reachable_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, endpoint_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω I S D : Term ℒ Γ Δ .set) :
    (reading_m ω I S D).satisfies η ↔ reading_l (ω.eval η) (I.eval η) (S.eval η) (D.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    reachable_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem closed_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I A D : Term ℒ Γ Δ .set) :
    (closed_m I A D).satisfies η ↔ closed_l (I.eval η) (A.eval η) (D.eval η) := by
  simp only [closed_m, closed_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem closed_of_reading_l {ω I A z r S D : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S) (hD : reading_l ω I S D) :
    closed_l I A D := by
  intro a ha b hb hEdge
  obtain ⟨_haI, f, hfS, hEnd⟩ := (hD a).mp ha
  obtain ⟨q, hPathQ, hEndQ, _⟩ :=
    PowerlessKleeneBrouwerEndpoint.append_l hω ((hS f).mp hfS) hEnd hb hEdge
  exact (hD b).mpr ⟨hb, q, (hS q).mpr hPathQ, hEndQ⟩

theorem exists_l {B ω I A z r S : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hSClass : PowerlessRelativeClassCorrespondence.member_l hℳ B S)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S) :
    ∃ D, PowerlessRelativeClassCorrespondence.member_l hℳ B D ∧ reading_l ω I S D ∧ closed_l I A D := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, hωClass⟩
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨I, hI⟩
  let S₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨S, hSClass⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set] :=
    reachable_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar .here)
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] [.set, .set, .set] :=
    Env.empty |>.pushFree S₀ |>.pushFree I₀ |>.pushFree O
  have hδ : Formula.IsDelta0 membershipLevyBound φ := reachable_delta_l _ _ _ _
  obtain ⟨D, hD⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (hBase := hBase) hδ η I₀
  have hφ (a : PowerlessRelativeClassStructure.type_l hℳ B) : φ.satisfies (η.pushFree a) ↔
      ∃ f, mem_l hℳ f S ∧ endpoint_l ω I f a.val :=
    (PowerlessRelativeClassBounded.formula_l hδ (η.pushFree a)).trans
      (reachable_formula_l (PowerlessRelativeClassRelativization.env_l (η.pushFree a)) _ _ _ _)
  have hRead : reading_l ω I S D.val := by
    intro a
    constructor
    · intro ha
      let a₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
        ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase D.property ha⟩
      obtain ⟨haI, hBody⟩ := (hD a₀).mp ha
      exact ⟨haI, (hφ a₀).mp hBody⟩
    · rintro ⟨haI, hBody⟩
      let a₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
        ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hI haI⟩
      exact (hD a₀).mpr ⟨haI, (hφ a₀).mpr hBody⟩
  exact ⟨D.val, D.property, hRead, closed_of_reading_l hω hS hRead⟩

def schema_m {Δ : SortContext ℒ} (B ω I A z r S : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B I) <| .imp (PowerlessRelativeHierarchySyntax.class_m B S) <|
      .imp (PowerlessKleeneBrouwerPathClass.reading_m ω I A z r S) <|
        .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
          .conj (reading_m (up ω) (up I) (up S) (.bvar .here)) (closed_m (up I) (up A) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B ω I A z r S : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r S)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r S : Term ℒ [] Δ .set) : (sentence_m B ω I A z r S).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessKleeneBrouwerPathClass.reading_formula_l, reading_formula_l, closed_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r S : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I A z r S)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r S)

#print axioms closed_of_reading_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerReachable
