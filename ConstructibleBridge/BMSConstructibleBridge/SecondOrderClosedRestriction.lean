import BMSConstructibleBridge.SecondOrderSelectedCollapseGraph
import BMSConstructibleBridge.SecondOrderFiniteRootTransport

/-! # 前驱封闭限制保留同一内部根对象

原二阶语言，原 Z₂。实际选点 P 的内部对角图是双模拟见证；
只限制到前驱封闭集不会改变其中根所代表的对象。见证是原模型中的实数，
不是任意外部恒等关系。本模块同时提供原推导核的闭模式出口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderClosedRestriction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem equal_l (hℳ : Theory.Models ℳ theory_m) (R Q P : set_l ℳ)
    (hClosed : ∀ a, mem_l a P → ∀ b, relation_l R b a → mem_l b P)
    (hQ : ∀ a b, relation_l Q a b ↔ mem_l a P ∧ mem_l b P ∧ relation_l R a b) :
    ∀ a, mem_l a P → SecondOrderBisimulation.eq_l R Q a a := by
  obtain ⟨H, hH⟩ := SecondOrderSelectedCollapseGraph.identity_l hℳ P
  have hWitness : SecondOrderBisimulation.witness_l R Q H := by
    intro a b hab
    obtain ⟨ha, rfl⟩ := (hH a b).mp hab
    constructor
    · intro c hc
      have hcP := hClosed a ha c hc
      exact ⟨c, (hQ c a).mpr ⟨hcP, ha, hc⟩, (hH c c).mpr ⟨hcP, rfl⟩⟩
    · intro d hd
      obtain ⟨hdP, _ha, hdR⟩ := (hQ d a).mp hd
      exact ⟨d, hdR, (hH d d).mpr ⟨hdP, rfl⟩⟩
  exact fun a ha => ⟨H, hWitness, (hH a a).mpr ⟨ha, rfl⟩⟩

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

def closed_m {Γ Δ : SortContext signature_m} (R P : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num <| .imp (.rel .mem (.cons (.bvar .here) (.cons (up P) .nil))) <|
    .forallE .num <| .imp (GraphSyntax.edge_m (up (up R)) (.bvar .here) (.bvar (.there .here)))
      (.rel .mem (.cons (.bvar .here) (.cons (up (up P)) .nil)))

def restricted_m {Γ Δ : SortContext signature_m} (R Q P : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <|
    .iff (GraphSyntax.edge_m (up (up Q)) (.bvar (.there .here)) (.bvar .here)) <|
      .conj (.rel .mem (.cons (.bvar (.there .here)) (.cons (up (up P)) .nil))) <|
        .conj (.rel .mem (.cons (.bvar .here) (.cons (up (up P)) .nil)))
          (GraphSyntax.edge_m (up (up R)) (.bvar (.there .here)) (.bvar .here))

private def bind_m {Δ : SortContext signature_m} (R Q : Term signature_m [] Δ .set)
    (a : Term signature_m [] Δ .num) :
    Substitution signature_m [] [.set, .set, .num, .num] [] Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => R
    | .there .here => Q
    | .there (.there .here) => a
    | .there (.there (.there .here)) => a)

def equal_m {Δ : SortContext signature_m} (R Q : Term signature_m [] Δ .set)
    (a : Term signature_m [] Δ .num) : Formula signature_m [] Δ :=
  GraphSyntax.eq_m.substitute (bind_m R Q a)

theorem equal_formula_l {Δ : SortContext signature_m} (η : Env ℳ [] Δ)
    (R Q : Term signature_m [] Δ .set) (a : Term signature_m [] Δ .num) :
    (equal_m R Q a).satisfies η ↔ SecondOrderBisimulation.eq_l (R.eval η) (Q.eval η) (a.eval η) (a.eval η) := by
  rw [equal_m, Formula.satisfies_substitute, SecondOrderBisimulation.eq_formula_l]
  rfl

def schema_m {Δ : SortContext signature_m} (R Q P : Term signature_m [] Δ .set)
    (a : Term signature_m [] Δ .num) : Formula signature_m [] Δ :=
  .imp (closed_m R P) <| .imp (restricted_m R Q P) <|
    .imp (.rel .mem (.cons a (.cons P .nil))) (equal_m R Q a)

def sentence_m {Δ : SortContext signature_m} (R Q P : Term signature_m [] Δ .set)
    (a : Term signature_m [] Δ .num) : Sentence signature_m :=
  Metatheory.Formula.forall_close (schema_m R Q P a)

theorem models_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (η : Env ℳ [] Δ) (R Q P : Term signature_m [] Δ .set) (a : Term signature_m [] Δ .num) :
    (schema_m R Q P a).satisfies η := by
  simp only [schema_m, closed_m, restricted_m, Formula.satisfies, SecondOrderPairing.edge_l,
    equal_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact fun hClosed hQ ha => equal_l hℳ (R.eval η) (Q.eval η) (P.eval η) hClosed hQ (a.eval η) ha

theorem derives_m {Δ : SortContext signature_m} (R Q P : Term signature_m [] Δ .set)
    (a : Term signature_m [] Δ .num) : Derives theory_m [] (sentence_m R Q P a) := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact models_l hℳ η R Q P a

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderClosedRestriction
