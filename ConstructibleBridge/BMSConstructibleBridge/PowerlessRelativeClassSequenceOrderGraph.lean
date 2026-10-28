import BMSConstructibleBridge.PowerlessRelativeClassSequenceLexicographic
import BMSConstructibleBridge.PowerlessRelativeClassSequenceSplitDerives
import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph

/-! # 全部内部有限序列的统一长度优先关系图

先比较长度，再比较同长度序列的首差异位置。一个 Δ₀ 正文同时定义全部
内部长度的关系，不为每个长度任意选择良序。这里只交付实际关系图及原 Z₂
对象推导；母关系良序时该图也良序的内部归纳仍由后续模块承担。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderGraph

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassSequenceLexicographic (lex_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def lex_m {Γ Δ : SortContext ℒ} (n X R f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  membershipLevyBound.boundedExists n <| membershipLevyBound.boundedExists (up X) <|
    membershipLevyBound.boundedExists (up (up X)) <|
      .conj (PowerlessValueBounded.formula_m (w f) (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
        .conj (PowerlessValueBounded.formula_m (w g) (.bvar (.there (.there .here))) (.bvar .here)) <|
          .conj (PowerlessValueBounded.formula_m (w R) (.bvar (.there .here)) (.bvar .here))
            (PowerlessRelativeClassSequenceSplitDerives.prefix_m (.bvar (.there (.there .here))) (w X) (w f) (w g))

theorem lex_delta_l {Γ Δ : SortContext ℒ} (n X R f g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (lex_m n X R f g) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _
    (.conj (PowerlessValueBounded.delta_l _ _ _) (.conj (PowerlessValueBounded.delta_l _ _ _)
      (.conj (PowerlessValueBounded.delta_l _ _ _)
        (PowerlessRelativeClassSequenceSplitDerives.prefix_delta_l _ _ _ _))))))

theorem lex_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (n X R f g : Term ℒ Γ Δ .set) :
    (lex_m n X R f g).satisfies η ↔
      lex_l (n.eval η) (X.eval η) (R.eval η) (f.eval η) (g.eval η) := by
  simp only [lex_m, lex_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, PowerlessRelativeClassSequenceSplitDerives.prefix_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨i, hi, a, ha, b, hb, hfa, hgb, hab, hPrefix⟩ =>
    ⟨i, a, b, hi, ha, hb, hfa, hgb, hab, hPrefix⟩,
    fun ⟨i, a, b, hi, ha, hb, hfa, hgb, hab, hPrefix⟩ =>
      ⟨i, hi, a, ha, b, hb, hfa, hgb, hab, hPrefix⟩⟩

def shortlex_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω X R f g : carrier_l ℳ₀) : Prop :=
  ∃ n m, member_l ℳ₀ n ω ∧ member_l ℳ₀ m ω ∧ map_l f n X ∧ map_l g m X ∧
    (member_l ℳ₀ n m ∨ n = m ∧ lex_l n X R f g)

def shortlex_m {Γ Δ : SortContext ℒ} (ω X R f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    .conj (PowerlessMapBounded.formula_m (w f) (.bvar (.there .here)) (w X)) <|
      .conj (PowerlessMapBounded.formula_m (w g) (.bvar .here) (w X)) <|
        .disj (member_m (.bvar (.there .here)) (.bvar .here))
          (.conj (.equal (.bvar (.there .here)) (.bvar .here))
            (lex_m (.bvar (.there .here)) (w X) (w R) (w f) (w g)))

theorem shortlex_delta_l {Γ Δ : SortContext ℒ} (ω X R f g : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (shortlex_m ω X R f g) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessMapBounded.delta_l _ _ _)
    (.conj (PowerlessMapBounded.delta_l _ _ _)
      (.disj (.rel _ _) (.conj (.equal _ _) (lex_delta_l _ _ _ _ _))))))

theorem shortlex_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω X R f g : Term ℒ Γ Δ .set) :
    (shortlex_m ω X R f g).satisfies η ↔
      shortlex_l (ω.eval η) (X.eval η) (R.eval η) (f.eval η) (g.eval η) := by
  simp only [shortlex_m, shortlex_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessMapBounded.formula_l, lex_formula_l, member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact ⟨fun ⟨n, hn, m, hm, hf, hg, hCompare⟩ => ⟨n, m, hn, hm, hf, hg, hCompare⟩,
    fun ⟨n, m, hn, hm, hf, hg, hCompare⟩ => ⟨n, hn, m, hm, hf, hg, hCompare⟩⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem exists_l {ω X R S : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω X S) :
    ∃ L : type_l hℳ B, ∀ f g, value_l (ℳ := ClassModel) L f g ↔
      shortlex_l (ℳ₀ := ClassModel) ω X R f g := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := shortlex_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env ClassModel [] [.set, .set, .set] := (((Env.empty).pushFree R).pushFree X).pushFree ω
  have hRead (f g : type_l hℳ B) : φ.satisfies ((η.pushFree g).pushFree f) ↔
      shortlex_l (ℳ₀ := ClassModel) ω X R f g := shortlex_formula_l _ _ _ _ _ _
  obtain ⟨L, hL⟩ := PowerlessRelativeClassRelationalGraph.exists_l
    (φ := φ) (shortlex_delta_l _ _ _ _ _) η S S
  refine ⟨L, fun f g => (hL f g).trans ⟨fun h => (hRead f g).mp h.2.2, ?_⟩⟩
  intro h
  have hφ := (hRead f g).mpr h
  obtain ⟨n, m, hn, hm, hf, hg, _⟩ := h
  exact ⟨(hS f).mpr ⟨n, hn, hf⟩, (hS g).mpr ⟨m, hm, hg⟩, hφ⟩

theorem of_omega_l {ω X R : type_l hℳ B} (hω : omega_l (ℳ := ClassModel) ω) :
    ∃ L : type_l hℳ B, ∀ f g, value_l (ℳ := ClassModel) L f g ↔
      shortlex_l (ℳ₀ := ClassModel) ω X R f g := by
  obtain ⟨S, hS⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_l (hBase := hBase) (X := X) hω
  exact exists_l (hBase := hBase) (S := S) hS

def specification_m {Γ Δ : SortContext ℒ} (ω X R L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    .iff (value_m (up (up L)) (.bvar (.there .here)) (.bvar .here))
      (shortlex_m (up (up ω)) (up (up X)) (up (up R)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω X R L : Term ℒ Γ Δ .set) :
    (specification_m ω X R L).satisfies η ↔ ∀ f g, value_l (L.eval η) f g ↔
      shortlex_l (ω.eval η) (X.eval η) (R.eval η) f g := by
  simp only [specification_m, Formula.satisfies, value_formula_l, shortlex_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let R : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .existsE .set
    (specification_m (up ω) (up X) (up R) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, specification_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact fun hω => of_omega_l (hBase := hBase) hω

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m
    (fun _ hℳ B hBase => models_l hℳ B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceOrderGraph
