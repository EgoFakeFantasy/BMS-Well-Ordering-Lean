import BMSConstructibleBridge.PowerlessKleeneBrouwerPath
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation
import BMSConstructibleBridge.PowerlessKleeneBrouwerGraph

/-! # 实际 Class 内的同根下降路径集合

纯隶属 ℒ，原 Z₂。原内部 ω 的 Class 资格在证明内取得；
先构造全部有限 I 序列，再用有界路径正文作实际 Class 分离。
读数量化全部 raw 序列。KB 图存在不等于已满足路径树最小元条款。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathClass

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (ω I A z r S : Raw) : Prop :=
  ∀ f, mem_l hℳ f S ↔ path_l (𝒩 := 𝒱) ω I A z r f

theorem exists_l {B ω I A z r : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I) :
    ∃ S, PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧ reading_l ω I A z r S := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  let O : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, hωClass⟩
  let I₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨I, hI⟩
  let A₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨A, hA⟩
  let Z : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωClass hz⟩
  let R : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨r, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hI hr⟩
  have hO : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) O :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω
  obtain ⟨F, hF, _hFClass⟩ :=
    PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l (hBase := hBase) (X := I₀) hO
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    path_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar .here)
  let η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) []
      [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree R |>.pushFree Z |>.pushFree A₀ |>.pushFree I₀ |>.pushFree O
  have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
    PowerlessKleeneBrouwerPath.path_delta_l _ _ _ _ _ _
  obtain ⟨S, hS⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (hBase := hBase) hφ η F
  have hRead (f : PowerlessRelativeClassStructure.type_l hℳ B) :
      φ.satisfies (η.pushFree f) ↔ path_l (𝒩 := 𝒱) ω I A z r f.val :=
    (PowerlessRelativeClassBounded.formula_l (hBase := hBase) hφ (η.pushFree f)).trans
      (path_formula_l (PowerlessRelativeClassRelativization.env_l (η.pushFree f)) _ _ _ _ _ _)
  refine ⟨S.val, S.property, fun f => ⟨?_, ?_⟩⟩
  · intro hf
    let f₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property hf⟩
    exact (hRead f₀).mp ((hS f₀).mp hf).2
  · intro hPath
    have hfF : mem_l hℳ f F.val := (hF f).mpr
      (by obtain ⟨n, hn, hf, _⟩ := hPath; exact ⟨n, hn, hf⟩)
    let f₀ : PowerlessRelativeClassStructure.type_l hℳ B :=
      ⟨f, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase F.property hfF⟩
    exact (hS f₀).mpr ⟨hfF, (hRead f₀).mpr hPath⟩

theorem graph_exists_l {B ω I A z r : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I) :
    ∃ S J, PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B J ∧ reading_l ω I A z r S ∧
      PowerlessKleeneBrouwerGraph.reading_l ω I S J := by
  obtain ⟨S, hSClass, hS⟩ := exists_l hBase hω hI hA hz hr
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  obtain ⟨J, hJClass, hJ⟩ := PowerlessKleeneBrouwerGraph.exists_l hBase hωClass hI hSClass
  exact ⟨S, J, hSClass, hJClass, hS, hJ⟩

def reading_m {Γ Δ : SortContext ℒ} (ω I A z r S : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up S))
    (path_m (up ω) (up I) (up A) (up z) (up r) (.bvar .here))

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω I A z r S : Term ℒ Γ Δ .set) :
    (reading_m ω I A z r S).satisfies η ↔
      reading_l (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η) (S.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    path_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B ω I A z r : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
          .imp (SecondOrderObjectSyntax.member_m z ω) <| .imp (SecondOrderObjectSyntax.member_m r I) <|
            .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
              (reading_m (up ω) (up I) (up A) (up z) (up r) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B ω I A z r : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r : Term ℒ [] Δ .set) : (sentence_m B ω I A z r).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, reading_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hBase hω hI hA hz hr => exists_l (hℳ := hℳ) hBase hω hI hA hz hr

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I A z r)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathClass
