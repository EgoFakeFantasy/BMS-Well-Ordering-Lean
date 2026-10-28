import BMSConstructibleBridge.SecondOrderComparisonHistoryDecode
import BMSConstructibleBridge.SecondOrderOmegaSyntax
import BMSConstructibleBridge.SecondOrderAxioms
import YesMetaZFC.Automation.ModelClosure

/-! # 比较历史解码的原 Z₂ 对象推导

纯句子显式量化 ω、零、历史实数的 ω 子集代表、固定载体和枚举图。
给定任意历史代表即可得到实际函数图及精确值域；不要求历史已经满足
递归方程。本模块没有把这项编码恢复定理替换成最终 BMS 良序句子。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private def bind_m {Γ Δ : SortContext ℒ} (ω e H f C i P : Term ℒ Γ Δ .set) :
    Substitution ℒ [] [.set, .set, .set, .set, .set, .set, .set] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => P
    | .there .here => i
    | .there (.there .here) => ω
    | .there (.there (.there .here)) => e
    | .there (.there (.there (.there .here))) => H
    | .there (.there (.there (.there (.there .here)))) => f
    | .there (.there (.there (.there (.there (.there .here))))) => C)

def output_m {Γ Δ : SortContext ℒ} (ω e H f C i P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  SecondOrderComparisonHistoryDecode.formula_m.substitute (bind_m ω e H f C i P)

def output_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e H f C i P : 𝒩.Carrier .set) : Prop :=
  SecondOrderComparisonHistoryDecode.formula_m.satisfies
    (((((((Env.empty.pushFree C).pushFree f).pushFree H).pushFree e).pushFree ω).pushFree i).pushFree P)

theorem output_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e H f C i P : Term ℒ Γ Δ .set) :
    (output_m ω e H f C i P).satisfies η ↔ output_l
      (ω.eval η) (e.eval η) (H.eval η) (f.eval η) (C.eval η) (i.eval η) (P.eval η) := by
  refine (Formula.satisfies_substitute η _ SecondOrderComparisonHistoryDecode.formula_m).trans ?_
  apply Iff.of_eq
  apply congrArg (fun ξ => SecondOrderComparisonHistoryDecode.formula_m.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | _ | _ | _ | _ | _ | _ | v
    all_goals first | rfl | nomatch v

def history_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e H f C b g : 𝒩.Carrier .set) : Prop :=
  map_l (ℳ := 𝒩) g ω b ∧
    (∀ i P, value_l (ℳ := 𝒩) g i P ↔ member_l 𝒩 i ω ∧ output_l ω e H f C i P) ∧
    ∀ P, member_l 𝒩 P b ↔ ∃ i, member_l 𝒩 i ω ∧ output_l ω e H f C i P

def history_m {Γ Δ : SortContext ℒ} (ω e H f C b g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  .conj (map_m g ω b) <| .conj
    (.forallE .set <| .forallE .set <|
      .iff (value_m (w g) (.bvar (.there .here)) (.bvar .here)) <|
        .conj (member_m (.bvar (.there .here)) (w ω))
          (output_m (w ω) (w e) (w H) (w f) (w C) (.bvar (.there .here)) (.bvar .here)))
    (.forallE .set <| .iff (member_m (.bvar .here) (up b)) <|
      .existsE .set <| .conj (member_m (.bvar .here) (w ω))
        (output_m (w ω) (w e) (w H) (w f) (w C) (.bvar .here) (.bvar (.there .here))))

theorem history_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e H f C b g : Term ℒ Γ Δ .set) :
    (history_m ω e H f C b g).satisfies η ↔ history_l
      (ω.eval η) (e.eval η) (H.eval η) (f.eval η) (C.eval η) (b.eval η) (g.eval η) := by
  simp only [history_m, history_l, Formula.satisfies, map_formula_l, value_formula_l,
    output_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (H : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A H) (C f : type_l hℳ) :
    ∃ b g, history_l (𝒩 := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A.val f C b g := by
  obtain ⟨b, g, hb, hg, hRead⟩ := SecondOrderBoundedRelationHistory.exists_l K
    SecondOrderComparisonHistoryDecode.formula_m (SecondOrderComparisonHistoryDecode.parameters_l K A C f) C
    (SecondOrderComparisonHistoryDecode.total_l K A H hA C f)
    (SecondOrderComparisonHistoryDecode.unique_l K A H hA C f) (by
      intro i P hP p hp
      obtain ⟨X, _, hXP⟩ := (SecondOrderComparisonHistoryDecode.formula_l K A H hA C f i P).mp hP
      obtain ⟨x, y, ⟨hx, hy, _⟩, hxy⟩ := (hXP p).mp hp
      exact ⟨x, y, hx, hy, hxy⟩)
  refine ⟨b, g, hg, hRead, ?_⟩
  intro P
  refine (hb P).trans ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    exact ⟨(numberCode_l K i).val, (numberCode_l K i).property, hi⟩
  · rintro ⟨i, hi, hP⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i, hi⟩
    have hn' : (numberCode_l K n).val = i := congrArg Subtype.val hn
    exact ⟨n, hn'.symm ▸ hP⟩

private def zero_m {Γ Δ : SortContext ℒ} (e : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.neg (member_m (.bvar .here) (up e)))

private theorem zero_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (e : Term ℒ Γ Δ .set) :
    (zero_m e).satisfies η ↔ PowerlessNatural.zero_l (ℳ := 𝒩) (e.eval η) := by
  simp only [zero_m, PowerlessNatural.zero_l, Formula.satisfies, member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def total_m {Γ Δ : SortContext ℒ} (ω e H f C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (zero_m e) <|
    .imp (ThirdOrderTheory.subset_m H ω) <| .existsE .set <| .existsE .set <|
      history_m (up (up ω)) (up (up e)) (up (up H)) (up (up f)) (up (up C))
        (.bvar (.there .here)) (.bvar .here)

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  total_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) : sentence_m.TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l hℳ,
    zero_formula_l, subset_formula_l, history_formula_l, up, Term.eval_weakenBound, Term.eval]
  intro hω he hH
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have heEq : η.freeVal (.there .here) = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    exact ⟨fun h => (he x h).elim, fun h => (PowerlessBMSQuotientSuccessor.zero_l K x h).elim⟩
  rw [hωEq] at hH
  let A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨η.freeVal (.there (.there .here)), hH⟩
  obtain ⟨H, hA⟩ := PowerlessBMSQuotientReals.trace_exists_l K A
  rw [hωEq, heEq]
  exact exists_l K A H hA _ _

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryDerives
