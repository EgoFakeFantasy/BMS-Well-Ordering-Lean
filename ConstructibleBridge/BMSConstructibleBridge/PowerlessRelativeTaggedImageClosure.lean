import BMSConstructibleBridge.PowerlessRelativeFiniteProgramImageClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramTaggedOperator

/-! # 标签程序闭包回收原有限图族的见证闭包

标签位于同一个 I 时，用其配对闭包构造实际查询 (标签,a)，再用
已证明的合法调用闭包回收对应 J 的全部输出。Class 输出守卫由
J:W→W 及实际 Class W 推出，不增加选择或要求 J∈W。
本模块保留每张原图的读数，尚不代替原矩阵规格与源模型装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeTaggedImageClosure

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramTaggedOperator (relation_m relation_formula_l maps_m maps_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def graph_m {Γ Δ : SortContext ℒ} (J I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up I)) <|
    .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ I))
      (SecondOrderObjectSyntax.value_m (up₂ J) (.bvar (.there .here)) (.bvar .here))) <|
    .forallE .set <| .forallE .set <|
      .imp (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up₂ I)) <|
        .imp (SecondOrderObjectSyntax.value_m (up₂ J) (.bvar (.there .here)) (.bvar .here))
          (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ I))

def family_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set)
    (F : List (Term ℒ Γ Δ .set × Term ℒ Γ Δ .set)) : Formula ℒ Γ Δ :=
  match F with
  | [] => .truth
  | p :: F => .conj (graph_m p.2 I) (family_m I F)

def tags_m {Γ Δ : SortContext ℒ} (I : Term ℒ Γ Δ .set)
    (F : List (Term ℒ Γ Δ .set × Term ℒ Γ Δ .set)) : Formula ℒ Γ Δ :=
  match F with
  | [] => .truth
  | p :: F => .conj (SecondOrderObjectSyntax.member_m p.1 I) (tags_m I F)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem graph_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (J I : Term ℒ Γ Δ .set) :
    (graph_m J I).satisfies η ↔
      (∀ a, mem_l hℳ a (I.eval η) → ∃ y, mem_l hℳ y (I.eval η) ∧
        value_l (ℳ := 𝒱) (J.eval η) a y) ∧
      (∀ a y, mem_l hℳ a (I.eval η) → value_l (ℳ := 𝒱) (J.eval η) a y →
        mem_l hℳ y (I.eval η)) := by
  simp only [graph_m, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

theorem family_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I : Term ℒ Γ Δ .set)
    (F : List (Term ℒ Γ Δ .set × Term ℒ Γ Δ .set)) :
    (family_m I F).satisfies η ↔ ∀ p ∈ F,
      (∀ a, mem_l hℳ a (I.eval η) → ∃ y, mem_l hℳ y (I.eval η) ∧
        value_l (ℳ := 𝒱) (p.2.eval η) a y) ∧
      (∀ a y, mem_l hℳ a (I.eval η) → value_l (ℳ := 𝒱) (p.2.eval η) a y →
        mem_l hℳ y (I.eval η)) := by
  induction F with
  | nil => simp [family_m, Formula.satisfies]
  | cons p F ih => simp [family_m, Formula.satisfies, graph_formula_l, ih]

theorem tags_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (I : Term ℒ Γ Δ .set)
    (F : List (Term ℒ Γ Δ .set × Term ℒ Γ Δ .set)) :
    (tags_m I F).satisfies η ↔ ∀ p ∈ F, mem_l hℳ (p.1.eval η) (I.eval η) := by
  induction F with
  | nil => simp [tags_m, Formula.satisfies]
  | cons p F ih =>
    change (mem_l hℳ (p.1.eval η) (I.eval η) ∧ (tags_m I F).satisfies η) ↔ _
    simp [ih]

theorem family_l {Δ : SortContext ℒ} (B W : Term ℒ [] Δ .set)
    (F : List (Term ℒ [] Δ .set × Term ℒ [] Δ .set)) (η : Env 𝒱 [] Δ)
    (I : type_l hℳ)
    (hB : ∀ a, mem_l hℳ a (B.eval η) → ∀ b, mem_l hℳ b a → mem_l hℳ b (B.eval η))
    (hW : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (W.eval η))
    (hMaps : ∀ p ∈ F, map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η))
    (hTags : ∀ p ∈ F, mem_l hℳ (p.1.eval η) I)
    (hBound : ∀ a, mem_l hℳ a I → mem_l hℳ a (W.eval η))
    (hPair : ∀ a b, mem_l hℳ a I → mem_l hℳ b I →
      ∃ q, mem_l hℳ q I ∧ ordered_l (ℳ := 𝒱) a b q)
    (hCall : ∀ x y, mem_l hℳ x I →
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
        (relation_m W F).satisfies ((η.pushFree x).pushFree y) → mem_l hℳ y I) :
    ∀ p ∈ F, (∀ a, mem_l hℳ a I → ∃ y, mem_l hℳ y I ∧
      value_l (ℳ := 𝒱) (p.2.eval η) a y) ∧
      (∀ a y, mem_l hℳ a I → value_l (ℳ := 𝒱) (p.2.eval η) a y → mem_l hℳ y I) := by
  intro p hp
  have hRead (a y : type_l hℳ) (ha : mem_l hℳ a I)
      (hy : value_l (ℳ := 𝒱) (p.2.eval η) a y) : mem_l hℳ y I := by
    obtain ⟨q, hq, hCode⟩ := hPair (p.1.eval η) a (hTags p hp) ha
    have hyW := (SecondOrderFunctionProperties.value_mem_l hℳ (hMaps p hp) hy).2
    have hyC := PowerlessRelativeClassCorrespondence.transitive_l hℳ hB hW hyW
    exact hCall q y hq hyC ((relation_formula_l W F η q y).mpr
      ⟨p, hp, a, hBound a ha, hCode, hy⟩)
  refine ⟨?_, hRead⟩
  intro a ha
  obtain ⟨y, hy, _⟩ := (hMaps p hp).2 a (hBound a ha)
  exact ⟨y, hRead a y ha hy.2, hy.2⟩

theorem closure_l {Δ : SortContext ℒ} (B W I : Term ℒ [] Δ .set)
    (F : List (Term ℒ [] Δ .set × Term ℒ [] Δ .set)) (η : Env 𝒱 [] Δ)
    (hB : ∀ a, mem_l hℳ a (B.eval η) → ∀ b, mem_l hℳ b a → mem_l hℳ b (B.eval η))
    (hW : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (W.eval η))
    (hMaps : ∀ p ∈ F, map_l (ℳ := 𝒱) (p.2.eval η) (W.eval η) (W.eval η))
    (hTags : ∀ p ∈ F, mem_l hℳ (p.1.eval η) (I.eval η))
    (hBound : ∀ a, mem_l hℳ a (I.eval η) → mem_l hℳ a (W.eval η))
    (hPair : ∀ a b, mem_l hℳ a (I.eval η) → mem_l hℳ b (I.eval η) →
      ∃ q, mem_l hℳ q (I.eval η) ∧ ordered_l (ℳ := 𝒱) a b q)
    (hCall : ∀ x y, mem_l hℳ x (I.eval η) →
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y →
        (relation_m W F).satisfies ((η.pushFree x).pushFree y) → mem_l hℳ y (I.eval η)) :
    (family_m I F).satisfies η :=
  (family_formula_l η I F).mpr (family_l B W F η (I.eval η) hB hW hMaps hTags hBound hPair hCall)

def schema_m {Δ : SortContext ℒ} (B W I : Term ℒ [] Δ .set)
    (F : List (Term ℒ [] Δ .set × Term ℒ [] Δ .set)) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B W) <|
      .imp (maps_m W F) <| .imp (tags_m I F) <|
        .imp (ThirdOrderTheory.subset_m I W) <|
          .imp (PowerlessRelativeFiniteProgramImageClosure.closure_m (relation_m W F) B I)
            (family_m I F)

def sentence_m {Δ : SortContext ℒ} (B W I : Term ℒ [] Δ .set)
    (F : List (Term ℒ [] Δ .set × Term ℒ [] Δ .set)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B W I F)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B W I : Term ℒ [] Δ .set) (F : List (Term ℒ [] Δ .set × Term ℒ [] Δ .set)) :
    (sentence_m B W I F).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, maps_formula_l, tags_formula_l,
    subset_formula_l, PowerlessRelativeFiniteProgramImageClosure.closure_formula_l K,
    PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l]
  intro η hB hW hMaps hTags hBound hClosure
  exact closure_l B W I F η hB hW hMaps hTags hBound hClosure.1 hClosure.2

theorem derives_m {Δ : SortContext ℒ} (B W I : Term ℒ [] Δ .set)
    (F : List (Term ℒ [] Δ .set × Term ℒ [] Δ .set)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B W I F)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B W I F)

#print axioms graph_formula_l
#print axioms family_formula_l
#print axioms tags_formula_l
#print axioms family_l
#print axioms closure_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeTaggedImageClosure
