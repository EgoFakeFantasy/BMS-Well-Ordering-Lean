import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabet
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationClosure
import BMSConstructibleBridge.PowerlessRelativeClassProductEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionIndexEnumeration

/-! # 具体三类指令字母表的实际 Class 满射

从常量种子的实际 ω 满射构造常量、调用和配对三类指令的枚举，再用
内部交错合并。结论覆盖同一个原字母表 Q；原 raw 规格中的中间有序对
由实际 Class 配对闭包回收，不另换字母表，也不要求内部 ω 外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAlphabetEnumeration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩" => structure_l hℳ B hBase

theorem exists_l {ω C G t₀ t₁ t₂ Q : type_l hℳ B}
    (hω : omega_l (ℳ := 𝒩) ω) (hG : map_l (ℳ := 𝒩) G ω C)
    (hOnto : ∀ x : type_l hℳ B, mem_l hℳ x.val C.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) G i x)
    (hQ : ∀ q, mem_l hℳ q Q.val ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l C.val ω.val t₀.val t₁.val t₂.val q) :
    ∃ F : type_l hℳ B, map_l (ℳ := 𝒩) F ω Q ∧ ∀ q : type_l hℳ B,
      mem_l hℳ q.val Q.val → ∃ i : type_l hℳ B,
        mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) F i q := by
  obtain ⟨T₀, E₀, hT₀, hE₀, hEOnto₀⟩ :=
    PowerlessRelativeClassEnumerationClosure.singleton_enumeration_l hω t₀
  obtain ⟨T₁, E₁, hT₁, hE₁, hEOnto₁⟩ :=
    PowerlessRelativeClassEnumerationClosure.singleton_enumeration_l hω t₁
  obtain ⟨T₂, E₂, hT₂, hE₂, hEOnto₂⟩ :=
    PowerlessRelativeClassEnumerationClosure.singleton_enumeration_l hω t₂
  obtain ⟨J, hJ, hRead⟩ :=
    PowerlessRelativeClassSatisfactionIndexEnumeration.identity_l (hBase := hBase) ω
  have hJOnto : ∀ j : type_l hℳ B, mem_l hℳ j.val ω.val →
      ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ value_l (ℳ := 𝒩) J i j :=
    fun j hj => ⟨j, hj, (hRead j j).mpr ⟨hj, rfl⟩⟩
  obtain ⟨P, hP⟩ := PowerlessRelativeClassProduct.exists_l hBase ω ω
  obtain ⟨R, hR, hROnto⟩ := PowerlessRelativeClassProductEnumeration.exists_l
    hω hJ hJ hJOnto hJOnto hP
  obtain ⟨Q₀, hQ₀⟩ := PowerlessRelativeClassProduct.exists_l hBase T₀ C
  obtain ⟨Q₁, hQ₁⟩ := PowerlessRelativeClassProduct.exists_l hBase T₁ ω
  obtain ⟨Q₂, hQ₂⟩ := PowerlessRelativeClassProduct.exists_l hBase T₂ P
  obtain ⟨F₀, hF₀, hFOnto₀⟩ := PowerlessRelativeClassProductEnumeration.exists_l
    hω hE₀ hG hEOnto₀ hOnto hQ₀
  obtain ⟨F₁, hF₁, hFOnto₁⟩ := PowerlessRelativeClassProductEnumeration.exists_l
    hω hE₁ hJ hEOnto₁ hJOnto hQ₁
  obtain ⟨F₂, hF₂, hFOnto₂⟩ := PowerlessRelativeClassProductEnumeration.exists_l
    hω hE₂ hR hEOnto₂ hROnto hQ₂
  obtain ⟨U, hU⟩ := PowerlessRelativeClassEnumerationClosure.union_l (hBase := hBase) Q₁ Q₂
  obtain ⟨H, hH, hHOnto⟩ := PowerlessRelativeClassEnumerationUnion.exists_l
    hω hF₁ hF₂ hFOnto₁ hFOnto₂ hU
  have hUnion (q : type_l hℳ B) : mem_l hℳ q.val Q.val ↔
      mem_l hℳ q.val Q₀.val ∨ mem_l hℳ q.val U.val := by
    rw [hU, hQ₀, hQ₁, hQ₂]
    constructor
    · intro hq
      rcases (hQ q.val).mp hq with ⟨a, ha, hq⟩ | ⟨k, hk, hq⟩ | ⟨k, l, p, hk, hl, hkl, hq⟩
      · let a' : type_l hℳ B := ⟨a,
          PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property ha⟩
        exact Or.inl ⟨t₀, a', (hT₀ t₀).mpr rfl, ha,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l t₀ a' q).mpr hq⟩
      · let k' : type_l hℳ B := ⟨k,
          PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hk⟩
        exact Or.inr (Or.inl ⟨t₁, k', (hT₁ t₁).mpr rfl, hk,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l t₁ k' q).mpr hq⟩)
      · let k' : type_l hℳ B := ⟨k,
          PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hk⟩
        let l' : type_l hℳ B := ⟨l,
          PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hl⟩
        let p' : type_l hℳ B := ⟨p,
          PowerlessRelativeClassPair.ordered_l hℳ hBase k'.property l'.property hkl⟩
        exact Or.inr (Or.inr ⟨t₂, p', (hT₂ t₂).mpr rfl,
          (hP p').mpr ⟨k', l', hk, hl,
            (PowerlessRelativeClassFunctionAbsolute.ordered_l k' l' p').mpr hkl⟩,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l t₂ p' q).mpr hq⟩)
    · rintro (⟨t, a, ht, ha, hq⟩ | ⟨t, k, ht, hk, hq⟩ | ⟨t, p, ht, hp, hq⟩)
      · have hEq := (hT₀ t).mp ht
        subst t
        exact (hQ q.val).mpr (Or.inl ⟨a.val, ha,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l t₀ a q).mp hq⟩)
      · have hEq := (hT₁ t).mp ht
        subst t
        exact (hQ q.val).mpr (Or.inr (Or.inl ⟨k.val, hk,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l t₁ k q).mp hq⟩))
      · have hEq := (hT₂ t).mp ht
        subst t
        obtain ⟨k, l, hk, hl, hkl⟩ := (hP p).mp hp
        exact (hQ q.val).mpr (Or.inr (Or.inr ⟨k.val, l.val, p.val, hk, hl,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l k l p).mp hkl,
          (PowerlessRelativeClassFunctionAbsolute.ordered_l t₂ p q).mp hq⟩))
  exact PowerlessRelativeClassEnumerationUnion.exists_l hω hF₀ hH hFOnto₀ hHOnto hUnion

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (B ω Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up ω) (up Q))
      (PowerlessRelativeClassEnumerationSectionDerives.onto_m (.bvar .here) (up ω) (up Q))

theorem conclusion_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (B ω Q : Term ℒ Γ Δ .set) : (conclusion_m B ω Q).satisfies η ↔
      ∃ F, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) F ∧
        map_l (ℳ := 𝒱) F (ω.eval η) (Q.eval η) ∧ ∀ q, mem_l hℳ q (Q.eval η) →
          ∃ i, mem_l hℳ i (ω.eval η) ∧ value_l (ℳ := 𝒱) F i q := by
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (B C ω G t₀ t₁ t₂ Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
                .imp (PowerlessRelativeHierarchySyntax.class_m B t₂) <|
                  .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
                    .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                      .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                        .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q)
                          (conclusion_m B ω Q)

def sentence_m {Δ : SortContext ℒ} (B C ω G t₀ t₁ t₂ Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B C ω G t₀ t₁ t₂ Q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B C ω G t₀ t₁ t₂ Q : Term ℒ [] Δ .set) :
    (sentence_m B C ω G t₀ t₁ t₂ Q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeHierarchySemantics.class_formula_l K,
    map_formula_l, PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l, conclusion_l K]
  intro η hBase hω hωC hC hG h₀ h₁ h₂ hQ hMap hOnto hAlphabet
  let O : type_l h𝒩 (B.eval η) := ⟨ω.eval η, hωC⟩
  let A : type_l h𝒩 (B.eval η) := ⟨C.eval η, hC⟩
  let E : type_l h𝒩 (B.eval η) := ⟨G.eval η, hG⟩
  let q : type_l h𝒩 (B.eval η) := ⟨Q.eval η, hQ⟩
  let a : type_l h𝒩 (B.eval η) := ⟨t₀.eval η, h₀⟩
  let b : type_l h𝒩 (B.eval η) := ⟨t₁.eval η, h₁⟩
  let c : type_l h𝒩 (B.eval η) := ⟨t₂.eval η, h₂⟩
  obtain ⟨F, hF, hFOnto⟩ := exists_l (hBase := hBase) (t₀ := a) (t₁ := b) (t₂ := c) (Q := q)
    ((PowerlessRelativeClassOmegaAbsolute.omega_l O).mpr hω)
    ((PowerlessRelativeClassFunctionAbsolute.map_l E O A).mpr hMap)
    ((PowerlessRelativeClassFunctionAbsolute.onto_l E O A).mpr hOnto) hAlphabet
  exact ⟨F.val, F.property, (PowerlessRelativeClassFunctionAbsolute.map_l F O q).mp hF,
    (PowerlessRelativeClassFunctionAbsolute.onto_l F O q).mp hFOnto⟩

theorem derives_m {Δ : SortContext ℒ} (B C ω G t₀ t₁ t₂ Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B C ω G t₀ t₁ t₂ Q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B C ω G t₀ t₁ t₂ Q)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramAlphabetEnumeration
