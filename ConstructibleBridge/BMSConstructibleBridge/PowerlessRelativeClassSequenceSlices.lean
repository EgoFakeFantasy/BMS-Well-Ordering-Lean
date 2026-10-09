import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation

/-! # 任意类参数上内部有限序列的定长切片

从实际内部有限序列集合，以有界函数公式作 Δ₀ 分离，得到每个内部
自然数长度的精确切片。母集不要求可枚举，长度不要求外部标准。
对象语言为纯集合语言，守卫化翻译的正式出口是原 Z₂ 中的 Derives；
此处不使用 Collection，也不声称已经完成最终 BMS 目标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSlices

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 量化整个当前模型域的精确定长切片规格。 -/
def spec_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (n X P : carrier_l ℳ₀) : Prop :=
  ∀ f, member_l ℳ₀ f P ↔ map_l f n X

def spec_m {Γ Δ : SortContext ℒ} (n X P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up P))
    (map_m (.bvar .here) (up n) (up X))

theorem spec_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (n X P : Term ℒ Γ Δ .set) :
    (spec_m n X P).satisfies η ↔ spec_l (n.eval η) (X.eval η) (P.eval η) := by
  simp only [spec_m, Formula.satisfies, member_m, map_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

/-- 给定整个内部有限序列集后，只需长度属于 ω 即可作精确切片。 -/
theorem exists_l {ω X S n : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω X S)
    (hn : member_l ClassModel n ω) :
    ∃ P : type_l hℳ B, spec_l (ℳ₀ := ClassModel) n X P := by
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessMapBounded.formula_m
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  let η : Env ClassModel [] [.set, .set] := ((Env.empty).pushFree X).pushFree n
  have hRead (f : type_l hℳ B) :
      φ.satisfies (η.pushFree f) ↔ map_l (ℳ := ClassModel) f n X :=
    PowerlessMapBounded.formula_l (η.pushFree f)
      (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  obtain ⟨P, hP⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    (hBase := hBase) (φ := φ) (PowerlessMapBounded.delta_l _ _ _) η S
  refine ⟨P, fun f => ?_⟩
  constructor
  · intro hf
    exact (hRead f).mp ((hP f).mp hf).2
  · intro hf
    exact (hP f).mpr ⟨(hS f).mpr ⟨n, hn, hf⟩, (hRead f).mpr hf⟩

/-- 由类内 ω 和任意母集直接取得定长切片，不需要母集的枚举。 -/
theorem of_omega_l {ω X n : type_l hℳ B}
    (hω : omega_l (ℳ := ClassModel) ω) (hn : member_l ClassModel n ω) :
    ∃ P : type_l hℳ B, spec_l (ℳ₀ := ClassModel) n X P := by
  obtain ⟨S, hS⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_l
    (hBase := hBase) (X := X) hω
  exact exists_l (hBase := hBase) (S := S) hS hn

def conclusion_m {Γ Δ : SortContext ℒ} (n X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (spec_m (up n) (up X) (.bvar .here))

theorem conclusion_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (n X : Term ℒ Γ Δ .set) :
    (conclusion_m n X).satisfies η ↔ ∃ P, spec_l (n.eval η) (X.eval η) P := by
  simp only [conclusion_m, Formula.satisfies, spec_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let X : Term ℒ [] [.set, .set, .set] .set := .fvar (.there .here)
  let n : Term ℒ [] [.set, .set, .set] .set := .fvar (.there (.there .here))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (member_m n ω) (conclusion_m n X)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, member_m,
    Arguments.eval, conclusion_l]
  exact fun hω hn => of_omega_l (hBase := hBase) hω hn

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m
    (fun _ hℳ B hBase => models_l hℳ B hBase)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceSlices
