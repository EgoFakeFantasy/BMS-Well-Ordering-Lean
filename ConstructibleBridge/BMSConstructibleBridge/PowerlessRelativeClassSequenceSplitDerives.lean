import BMSConstructibleBridge.PowerlessRelativeClassSequenceSplit

/-! # 内部后继长度序列的实际前缀／末项单射

以 Δ₀ 关系把每个后继长度序列送到其前缀和末项的有序对，构造类内集合
函数图并证明单射。母集无需枚举；无需选择逆函数或假设 Collection。
正式结论在原 Z₂ 推导核中，后继长度由实际成员分解表述。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSplitDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceSplit (prefix_l split_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def prefix_m {Γ Δ : SortContext ℒ} (n X f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall n <| membershipLevyBound.boundedForall (up X) <|
    .iff (PowerlessValueBounded.formula_m (up (up g)) (.bvar (.there .here)) (.bvar .here))
      (PowerlessValueBounded.formula_m (up (up f)) (.bvar (.there .here)) (.bvar .here))

theorem prefix_delta_l {Γ Δ : SortContext ℒ} (n X f g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (prefix_m n X f g) :=
  .bounded_forall _ (.bounded_forall _ (.iff (PowerlessValueBounded.delta_l _ _ _)
    (PowerlessValueBounded.delta_l _ _ _)))

theorem prefix_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (n X f g : Term ℒ Γ Δ .set) :
    (prefix_m n X f g).satisfies η ↔ prefix_l (n.eval η) (X.eval η) (f.eval η) (g.eval η) := by
  simp only [prefix_m, prefix_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def split_m {Γ Δ : SortContext ℒ} (n X P f p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists P <| membershipLevyBound.boundedExists (up X) <|
    .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p))) <|
      .conj (prefix_m (up (up n)) (up (up X)) (up (up f)) (.bvar (.there .here)))
        (PowerlessValueBounded.formula_m (up (up f)) (up (up n)) (.bvar .here))

theorem split_delta_l {Γ Δ : SortContext ℒ} (n X P f p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (split_m n X P f p) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
    (.conj (prefix_delta_l _ _ _ _) (PowerlessValueBounded.delta_l _ _ _))))

theorem split_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (n X P f p : Term ℒ Γ Δ .set) :
    (split_m n X P f p).satisfies η ↔
      split_l (n.eval η) (X.eval η) (P.eval η) (f.eval η) (p.eval η) := by
  simp only [split_m, split_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, prefix_formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨g, hg, a, ha, hga, hPrefix, hLast⟩ => ⟨g, a, hg, ha, hga, hPrefix, hLast⟩,
    fun ⟨g, a, hg, ha, hga, hPrefix, hLast⟩ => ⟨g, hg, a, ha, hga, hPrefix, hLast⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem exists_l {n m X P Q : type_l hℳ B}
    (hSucc : ∀ i, member_l ClassModel i m ↔ member_l ClassModel i n ∨ i = n)
    (hP : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) n X P)
    (hQ : PowerlessRelativeClassSequenceSlices.spec_l (ℳ₀ := ClassModel) m X Q) :
    ∃ D H : type_l hℳ B,
      (∀ p, member_l ClassModel p D ↔ ∃ g a, member_l ClassModel g P ∧
        member_l ClassModel a X ∧ ordered_l (ℳ := ClassModel) g a p) ∧
      map_l (ℳ := ClassModel) H Q D ∧ injective_l (ℳ := ClassModel) H ∧
      ∀ f p, value_l (ℳ := ClassModel) H f p ↔
        member_l ClassModel f Q ∧ split_l (ℳ₀ := ClassModel) n X P f p := by
  obtain ⟨D, hD⟩ := PowerlessRelativeClassProduct.exists_l hBase P X
  have hMem {f p : type_l hℳ B} (hp : split_l (ℳ₀ := ClassModel) n X P f p) :
      member_l ClassModel p D := by
    obtain ⟨g, a, hg, ha, hga, _, _⟩ := hp
    exact (hD p).mpr ⟨g, a, hg, ha, hga⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := split_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env ClassModel [] [.set, .set, .set] := (((Env.empty).pushFree P).pushFree X).pushFree n
  have hRead (f p : type_l hℳ B) : φ.satisfies ((η.pushFree p).pushFree f) ↔
      split_l (ℳ₀ := ClassModel) n X P f p := split_formula_l _ _ _ _ _ _
  have hTotal (f : type_l hℳ B) (hf : member_l ClassModel f Q) :
      ∃! p : type_l hℳ B, member_l ClassModel p D ∧ φ.satisfies ((η.pushFree p).pushFree f) := by
    obtain ⟨p, hp, hUnique⟩ := PowerlessRelativeClassSequenceSplit.exists_unique_l
      (hBase := hBase) ((hQ f).mp hf) hSucc hP
    exact ⟨p, ⟨hMem hp, (hRead f p).mpr hp⟩, fun q hq => hUnique q ((hRead f q).mp hq.2)⟩
  obtain ⟨H, hH, hValues⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (φ := φ) (split_delta_l _ _ _ _ _) η Q D hTotal
  have hValue (f p : type_l hℳ B) : value_l (ℳ := ClassModel) H f p ↔
      member_l ClassModel f Q ∧ split_l (ℳ₀ := ClassModel) n X P f p := by
    refine (hValues f p).trans ⟨?_, ?_⟩
    · exact fun h => ⟨h.1, (hRead f p).mp h.2.2⟩
    · exact fun h => ⟨h.1, hMem h.2, (hRead f p).mpr h.2⟩
  refine ⟨D, H, hD, hH, ?_, hValue⟩
  intro f g p hf hg
  obtain ⟨hfQ, hfSplit⟩ := (hValue f p).mp hf
  obtain ⟨hgQ, hgSplit⟩ := (hValue g p).mp hg
  exact PowerlessRelativeClassSequenceSplit.injective_l
    ((hQ f).mp hfQ) ((hQ g).mp hgQ) hSucc hP hfSplit hgSplit

def specification_m {Γ Δ : SortContext ℒ} (n X P Q D H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set (.iff (member_m (.bvar .here) (up D))
    (PowerlessRelativeClassProduct.body_m (up P) (up X) (.bvar .here)))) <|
    .conj (map_m H Q D) <| .conj (injective_m H) <| .forallE .set <| .forallE .set <|
      .iff (value_m (up (up H)) (.bvar (.there .here)) (.bvar .here)) <|
        .conj (member_m (.bvar (.there .here)) (up (up Q)))
          (split_m (up (up n)) (up (up X)) (up (up P)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (n X P Q D H : Term ℒ Γ Δ .set) :
    (specification_m n X P Q D H).satisfies η ↔
      (∀ p, member_l ℳ₀ p (D.eval η) ↔ ∃ g a, member_l ℳ₀ g (P.eval η) ∧
        member_l ℳ₀ a (X.eval η) ∧ ordered_l g a p) ∧
      map_l (H.eval η) (Q.eval η) (D.eval η) ∧ injective_l (H.eval η) ∧
      ∀ f p, value_l (H.eval η) f p ↔ member_l ℳ₀ f (Q.eval η) ∧
        split_l (n.eval η) (X.eval η) (P.eval η) f p := by
  simp only [specification_m, Formula.satisfies, member_m, Arguments.eval,
    PowerlessRelativeClassProduct.body_formula_l, map_formula_l, injective_formula_l,
    value_formula_l, split_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let n : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let m : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let X : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let P : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let Q : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchySyntax.successor_m n m) <|
    .imp (PowerlessRelativeClassSequenceSlices.spec_m n X P) <|
      .imp (PowerlessRelativeClassSequenceSlices.spec_m m X Q) <| .existsE .set <| .existsE .set <|
        specification_m (up (up n)) (up (up X)) (up (up P)) (up (up Q))
          (.bvar (.there .here)) (.bvar .here)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, PowerlessRelativeHierarchySyntax.successor_m, Formula.satisfies,
    PowerlessRelativeClassSequenceSlices.spec_formula_l, specification_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hSucc hP hQ => exists_l (hBase := hBase) hSucc hP hQ

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m
    (fun _ hℳ B hBase => models_l hℳ B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSplitDerives
