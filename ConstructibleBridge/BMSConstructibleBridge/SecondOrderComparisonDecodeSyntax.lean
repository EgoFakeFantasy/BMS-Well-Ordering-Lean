import BMSConstructibleBridge.SecondOrderComparisonRoundtrip
import BMSConstructibleBridge.PowerlessMemberDefArithmeticSemantics
import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderAxioms
import YesMetaZFC.Automation.ModelClosure

/-! # 比较解码的纯对象公式和原 Z₂ 推导出口

自然数关系位使用原配数的关系式翻译，不混用另一种配对算法。
存在唯一性对所有参数成立：即使参数不是有效算术编码，纯公式仍定义
一个载体有界的完整关系图。与原比较实数的精确对应另用有效编码规格核验。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecodeSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def query_template_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  let x : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let y : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let ω : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let e : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let R : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let f : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let i : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .bvar (.there .here)
  let j : Term ℒ [.set, .set] [.set, .set, .set, .set, .set, .set] .set := .bvar .here
  .existsE .set <| .existsE .set <| .conj (member_m i ω) <|
    .conj (member_m j ω) <| .conj (value_m f i x) <| .conj (value_m f j y)
      (PowerlessMemberDefSyntax.edge_m ω e R i j)

private def bind_m {Γ Δ : SortContext ℒ} (ω e R f x y : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set, .set, .set, .set, .set, .set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => x
    | .there .here => y
    | .there (.there .here) => ω
    | .there (.there (.there .here)) => e
    | .there (.there (.there (.there .here))) => R
    | .there (.there (.there (.there (.there .here)))) => f)

def query_m {Γ Δ : SortContext ℒ} (ω e R f x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  query_template_m.substitute (bind_m ω e R f x y)

def query_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e R f x y : 𝒩.Carrier .set) : Prop :=
  query_template_m.satisfies ((((((Env.empty.pushFree f).pushFree R).pushFree e).pushFree ω).pushFree y).pushFree x)

theorem query_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e R f x y : Term ℒ Γ Δ .set) :
    (query_m ω e R f x y).satisfies η ↔
      query_l (ω.eval η) (e.eval η) (R.eval η) (f.eval η) (x.eval η) (y.eval η) := by
  refine (Formula.satisfies_substitute η _ query_template_m).trans ?_
  apply Iff.of_eq
  apply congrArg (fun ξ => query_template_m.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | _ | _ | _ | _ | _ | v
    all_goals first | rfl | nomatch v

def graph_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e R f C P : 𝒩.Carrier .set) : Prop :=
  ∀ p, member_l 𝒩 p P ↔ ∃ x y, member_l 𝒩 x C ∧ member_l 𝒩 y C ∧
    query_l ω e R f x y ∧ ordered_l (ℳ := 𝒩) x y p

def graph_m {Γ Δ : SortContext ℒ} (ω e R f C P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .forallE .set <| .iff (member_m (.bvar .here) (up P)) <|
    .existsE .set <| .existsE .set <| .conj (member_m (.bvar (.there .here)) (w C)) <|
      .conj (member_m (.bvar .here) (w C)) <|
        .conj (query_m (w ω) (w e) (w R) (w f) (.bvar (.there .here)) (.bvar .here))
          (ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here))))

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e R f C P : Term ℒ Γ Δ .set) :
    (graph_m ω e R f C P).satisfies η ↔
      graph_l (ω.eval η) (e.eval η) (R.eval η) (f.eval η) (C.eval η) (P.eval η) := by
  simp only [graph_m, graph_l, Formula.satisfies, query_formula_l, ordered_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (ω e R f C : type_l hℳ) : ∃ P, graph_l (𝒩 := 𝒱) ω e R f C P := by
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ query_template_m
    ((((Env.empty.pushFree f).pushFree R).pushFree e).pushFree ω) C C
  exact ⟨P, hP⟩

theorem unique_l {ω e R f C P Q : type_l hℳ}
    (hP : graph_l (𝒩 := 𝒱) ω e R f C P) (hQ : graph_l (𝒩 := 𝒱) ω e R f C Q) : P = Q :=
  SecondOrderQuotient.ext_l hℳ P Q (fun p => (hP p).trans (hQ p).symm)

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let e : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let R : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let f : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let C : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .existsE .set <| .conj (graph_m (up ω) (up e) (up R) (up f) (up C) (.bvar .here)) <|
    .forallE .set <| .imp (graph_m (up (up ω)) (up (up e)) (up (up R)) (up (up f)) (up (up C)) (.bvar .here))
      (.equal (.bvar .here) (.bvar (.there .here)))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, graph_formula_l, up, Term.eval_weakenBound, Term.eval]
  obtain ⟨P, hP⟩ := exists_l hℳ _ _ _ _ _
  exact ⟨P, hP, fun Q hQ => unique_l hQ hP⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecodeSyntax
