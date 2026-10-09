import BMSConstructibleBridge.PowerlessRelativeClassParameterSeed
import BMSConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
import BMSConstructibleBridge.PowerlessRelativeOrdinalCutoff

/-! # 较短实际历史的可数常量种子

原 Z₂ 背景，实际 Class 基底枚举与实际 Class 阶段计数图产生同一满射。
种子精确包含基底、阶段域的全部成员，以及 B、阶段域、ω 三个对象。
空阶段域单独处理；不选择跨阶段枚举族，也不假定内部 ω 外部标准。

种子及其枚举只须属于 Class，不声称枚举图属于 W。主线还须证明种子
包含于实际 W，再构造同一个程序像并消费历史覆盖归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalHistorySeed

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

/-- 精确成员规格保留实际阶段域，不用一份任意母集覆盖代替。 -/
def seed_l (ω α C : Raw) : Prop :=
  ∀ x, mem_l hℳ x C ↔ mem_l hℳ x B ∨ mem_l hℳ x α ∨ x = B ∨ x = α ∨ x = ω

def seed_m {Γ Δ : SortContext ℒ} (B ω α C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up C)) <|
    .disj (SecondOrderObjectSyntax.member_m (.bvar .here) (up B)) <|
      .disj (SecondOrderObjectSyntax.member_m (.bvar .here) (up α)) <|
        .disj (.equal (.bvar .here) (up B)) <|
          .disj (.equal (.bvar .here) (up α)) (.equal (.bvar .here) (up ω))

theorem seed_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (B ω α C : Term ℒ Γ Δ .set) : (seed_m B ω α C).satisfies η ↔
      seed_l (B := B.eval η) (ω.eval η) (α.eval η) (C.eval η) := by
  simp only [seed_m, seed_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  rfl

include hBase in
theorem exists_l (ω α G : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hG : map_l (ℳ := 𝒱) G.val ω.val B)
    (hOnto : ∀ x : Raw, mem_l hℳ x B →
      ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := 𝒱) G.val i x)
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l B ω.val α.val) :
    ∃ C F : type_l hℳ B, map_l (ℳ := 𝒱) F.val ω.val C.val ∧
      (∀ x : Raw, mem_l hℳ x C.val →
        ∃ i, mem_l hℳ i ω.val ∧ value_l (ℳ := 𝒱) F.val i x) ∧
      seed_l (B := B) ω.val α.val C.val := by
  classical
  let b : type_l hℳ B := ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩
  have hωClass : omega_l (ℳ := 𝒩) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l ω).mpr hω
  have hGClass : map_l (ℳ := 𝒩) G ω b :=
    (PowerlessRelativeClassFunctionAbsolute.map_l G ω b).mpr hG
  have hOntoClass := (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) G ω b).mpr hOnto
  obtain ⟨X, J, hX, hJ, hJOnto⟩ : ∃ X J : type_l hℳ B,
      (∀ x : type_l hℳ B, mem_l hℳ x.val X.val ↔
        mem_l hℳ x.val B ∨ mem_l hℳ x.val α.val) ∧
      map_l (ℳ := 𝒩) J ω X ∧
      (∀ x : type_l hℳ B, mem_l hℳ x.val X.val →
        ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) J i x) := by
    by_cases hNonempty : ∃ d : Raw, mem_l hℳ d α.val
    · obtain ⟨d, hd⟩ := hNonempty
      let d' : type_l hℳ B :=
        ⟨d, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase α.property hd⟩
      obtain ⟨R, hR, hMap, hInjective⟩ := hCount
      let r : type_l hℳ B := ⟨R, hR⟩
      have hMapClass : map_l (ℳ := 𝒩) r α ω :=
        (PowerlessRelativeClassFunctionAbsolute.map_l r α ω).mpr hMap
      have hInjectiveClass (x y i : type_l hℳ B)
          (hxi : value_l (ℳ := 𝒩) r x i) (hyi : value_l (ℳ := 𝒩) r y i) : x = y :=
        Subtype.ext (hInjective x.val y.val i.val
          ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) r x i).mp hxi)
          ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) r y i).mp hyi))
      obtain ⟨E, hE, hEOnto, _⟩ := PowerlessRelativeClassInjectionEnumeration.exists_l
        hMapClass hInjectiveClass (show mem_l hℳ d'.val α.val from hd)
      obtain ⟨X, hX⟩ := PowerlessRelativeClassEnumerationClosure.union_l (hBase := hBase) b α
      obtain ⟨J, hJ, hJOnto⟩ := PowerlessRelativeClassEnumerationUnion.exists_l
        hωClass hGClass hE hOntoClass hEOnto hX
      exact ⟨X, J, hX, hJ, hJOnto⟩
    · refine ⟨b, G, ?_, hGClass, hOntoClass⟩
      intro x
      exact ⟨Or.inl, fun h => h.elim id (fun hx => False.elim (hNonempty ⟨x.val, hx⟩))⟩
  obtain ⟨C₀, F₀, hC₀, hF₀, hOnto₀⟩ :=
    PowerlessRelativeClassEnumerationClosure.adjoin_l hωClass hJ hJOnto b
  obtain ⟨C₁, F₁, hC₁, hF₁, hOnto₁⟩ :=
    PowerlessRelativeClassEnumerationClosure.adjoin_l hωClass hF₀ hOnto₀ α
  obtain ⟨C, F, hC, hF, hFOnto⟩ :=
    PowerlessRelativeClassEnumerationClosure.adjoin_l hωClass hF₁ hOnto₁ ω
  have hEq (x y : type_l hℳ B) : x = y ↔ x.val = y.val :=
    ⟨congrArg Subtype.val, Subtype.ext⟩
  have hRead (x : type_l hℳ B) : mem_l hℳ x.val C.val ↔
      mem_l hℳ x.val B ∨ mem_l hℳ x.val α.val ∨ x.val = B ∨ x.val = α.val ∨ x.val = ω.val := by
    rw [hC x, hC₁ x, hC₀ x, hX x, hEq x b, hEq x α, hEq x ω]
    simp only [b, or_assoc]
  refine ⟨C, F, (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F ω C).mp hF,
    (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) F ω C).mp hFOnto, ?_⟩
  intro x
  constructor
  · intro hx
    exact (hRead ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property hx⟩).mp hx
  · intro hx
    have hxClass : PowerlessRelativeClassCorrespondence.member_l hℳ B x := by
      rcases hx with hx | hx | rfl | rfl | rfl
      · exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase b.property hx
      · exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase α.property hx
      · exact b.property
      · exact α.property
      · exact ω.property
    exact (hRead ⟨x, hxClass⟩).mpr hx

/-- 母界只需覆盖实际种子组成部分；绝不把 W 本身加入常量种子。 -/
theorem subset_l {ω α C W : Raw} (hC : seed_l (B := B) ω α C)
    (hBW : ∀ x, mem_l hℳ x B → mem_l hℳ x W)
    (hαW : ∀ x, mem_l hℳ x α → mem_l hℳ x W)
    (hB : mem_l hℳ B W) (hα : mem_l hℳ α W) (hω : mem_l hℳ ω W) :
    ∀ x, mem_l hℳ x C → mem_l hℳ x W := by
  intro x hx
  rcases (hC x).mp hx with hx | hx | rfl | rfl | rfl
  · exact hBW x hx
  · exact hαW x hx
  · exact hB
  · exact hα
  · exact hω

def conclusion_m {Δ : SortContext ℒ} (B ω α : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <| .existsE .set <|
    let C : Term ℒ [.set, .set] Δ .set := .bvar (.there .here)
    let F := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) C) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) F) <|
        .conj (SecondOrderObjectSyntax.map_m F (up₂ ω) C) <|
          .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m F (up₂ ω) C)
            (seed_m (up₂ B) (up₂ ω) (up₂ α) C)

def schema_m {Δ : SortContext ℒ} (B ω α G : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B α) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
            .imp (SecondOrderObjectSyntax.map_m G ω B) <|
              .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω B) <|
                .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω α) (conclusion_m B ω α)

def sentence_m {Δ : SortContext ℒ} (B ω α G : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω α G)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω α G : Term ℒ [] Δ .set) :
    (sentence_m B ω α G).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l, PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K]
  intro η hB hω hωClass hαClass hGClass hMap hOnto hCount
  obtain ⟨C, F, hF, hFOnto, hSeed⟩ := exists_l (hBase := hB)
    ⟨ω.eval η, hωClass⟩ ⟨α.eval η, hαClass⟩ ⟨G.eval η, hGClass⟩ hω hMap hOnto hCount
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, seed_formula_l,
    up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact ⟨C.val, F.val, C.property, F.property, hF, hFOnto, hSeed⟩

theorem derives_m {Δ : SortContext ℒ} (B ω α G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω α G)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω α G)

#print axioms seed_formula_l
#print axioms exists_l
#print axioms subset_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalHistorySeed
