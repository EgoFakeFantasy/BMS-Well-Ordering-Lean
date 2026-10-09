import BMSConstructibleBridge.SecondOrderMemberDefArithmetic
import BMSConstructibleBridge.SecondOrderCompleteness

/-! # 原五标签赋值的内部槽反转

以 i + succ r = l 关系式反转内部长度 l 的槽，而不抽取 Type 层减法或
反转函数。原量词的头部前插在反转后成为末尾槽 l 的新增值，旧槽保持。
实际反转码由关系理解和内部有限图编码产生，涵盖全部非标准内部长度。
原 Z₂ 出口只证明赋值反转存在；全内部公式翻译与 Def 等价仍待完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyAssignmentReversal

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers
open SecondOrderSequenceSyntax (read_l)
open SecondOrderAssignmentSyntax (valid_l extension_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

private def succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

def index_l (l i r : num_l ℳ) : Prop := add_l i (succ_l r) = l

def index_m {Γ Δ : SortContext signature_m} (l i r : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .equal (Term.app (σ := signature_m) .add (.cons i (.cons (succ_m r) .nil))) l

theorem index_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (l i r : Term signature_m Γ Δ .num) :
    (index_m l i r).satisfies η ↔ index_l (l.eval η) (i.eval η) (r.eval η) := Iff.rfl

theorem symmetric_l (hℳ : Theory.Models ℳ theory_m) (l i r : num_l ℳ) :
    index_l l i r ↔ index_l l r i := by
  unfold index_l
  rw [add_succ_l hℳ, add_succ_l hℳ, add_comm_l hℳ i r]

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {l i r s : num_l ℳ}
    (hr : index_l l i r) (hs : index_l l i s) : r = s :=
  injective_l hℳ ((add_cancel_l hℳ i _ _).mp (hr.trans hs.symm))

theorem bounds_l (hℳ : Theory.Models ℳ theory_m) {l i r : num_l ℳ}
    (h : index_l l i r) : SecondOrderOrder.lt_l i l ∧ SecondOrderOrder.lt_l r l :=
  ⟨⟨r, h⟩, ⟨i, (symmetric_l hℳ l i r).mp h⟩⟩

theorem index_exists_l (hℳ : Theory.Models ℳ theory_m) {l i : num_l ℳ}
    (hi : SecondOrderOrder.lt_l i l) : ∃! r, index_l l i r := by
  obtain ⟨r, hr⟩ := hi
  exact ⟨r, hr, fun s hs => unique_l hℳ hs hr⟩

/-- 旧槽在头部前插后右移一次，其反转后的目标槽保持不变。 -/
theorem shifted_l (hℳ : Theory.Models ℳ theory_m) (l i r : num_l ℳ) :
    index_l (succ_l l) (succ_l i) r ↔ index_l l i r := by
  unfold index_l
  rw [succ_add_l hℳ, (injective_l hℳ).eq_iff]

theorem fresh_l (hℳ : Theory.Models ℳ theory_m) (l : num_l ℳ) :
    index_l (succ_l l) (zero_l ℳ) l := zero_add_l hℳ _

def reversed_l (E : set_l ℳ) (c l r x : num_l ℳ) : Prop :=
  ∃ i, index_l l i r ∧ read_l E c i x

def reversed_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c l r x : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (index_m (up l) (.bvar .here) (up r))
    (SecondOrderSequenceSyntax.formula_m (up E) (up c) (.bvar .here) (up x))

theorem reversed_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c l r x : Term signature_m Γ Δ .num) :
    (reversed_m E c l r x).satisfies η ↔
      reversed_l (E.eval η) (c.eval η) (l.eval η) (r.eval η) (x.eval η) := by
  simp only [reversed_m, reversed_l, Formula.satisfies, index_formula_l,
    SecondOrderSequenceSyntax.raw_l, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 反转读数在前插下恰好增加末尾值，不改变任何原目标槽。 -/
theorem prepend_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} {c l d x r y : num_l ℳ}
    (hd : extension_l E c l d x) :
    reversed_l E d (succ_l l) r y ↔ (r = l ∧ y = x) ∨ reversed_l E c l r y := by
  constructor
  · rintro ⟨i, hi, hRead⟩
    rcases predecessor_l hℳ i with rfl | ⟨i, rfl⟩
    · exact Or.inl ⟨unique_l hℳ hi (fresh_l hℳ l), (hd.2.1 y).mp hRead⟩
    · exact Or.inr ⟨i, (shifted_l hℳ l i r).mp hi, (hd.2.2 i y).mp hRead⟩
  · rintro (⟨hR, hY⟩ | ⟨i, hi, hRead⟩)
    · subst r
      subst y
      exact ⟨zero_l ℳ, fresh_l hℳ l, (hd.2.1 x).mpr rfl⟩
    · exact ⟨succ_l i, (shifted_l hℳ l i r).mpr hi, (hd.2.2 i y).mpr hRead⟩

theorem total_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} {c l r : num_l ℳ}
    (hc : valid_l E c l) (hr : SecondOrderOrder.lt_l r l) :
    ∃! x, reversed_l E c l r x := by
  obtain ⟨i, hi, _⟩ := index_exists_l hℳ hr
  have hi' := (symmetric_l hℳ l r i).mp hi
  obtain ⟨x, hx, hUnique⟩ := hc.1 i (bounds_l hℳ hi').1
  refine ⟨x, ⟨i, hi', hx⟩, ?_⟩
  rintro y ⟨j, hj, hy⟩
  have hji := unique_l hℳ ((symmetric_l hℳ l j r).mp hj) hi
  subst j
  exact hUnique y hy

/-- 单个内部数码精确保存反转图，包括界外无边。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : SecondOrderBinaryPowers.spec_l E) {c l : num_l ℳ} (hc : valid_l E c l) :
    ∃ d, valid_l E d l ∧ ∀ r x, read_l E d r x ↔ reversed_l E c l r x := by
  let φ : Formula signature_m [] [.num, .num, .set, .num, .num] := reversed_m
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env ℳ [] [.set, .num, .num] := ((Env.empty.pushFree l).pushFree c).pushFree E
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl) η
  have hGraph (r x : num_l ℳ) : SecondOrderPairing.relation_l H r x ↔ reversed_l E c l r x :=
    (hH r x).trans (reversed_formula_l _ _ _ _ _ _)
  have hTotal r (hr : SecondOrderOrder.lt_l r l) : ∃! x, SecondOrderPairing.relation_l H r x := by
    obtain ⟨x, hx, hUnique⟩ := total_l hℳ hc hr
    exact ⟨x, (hGraph r x).mpr hx, fun y hy => hUnique y ((hGraph r y).mp hy)⟩
  obtain ⟨d, hd⟩ := SecondOrderSequenceCode.exists_l hℳ hE H l hTotal
  have hRead (r x : num_l ℳ) : read_l E d r x ↔ reversed_l E c l r x := by
    refine (SecondOrderSequenceSyntax.read_eq_l hE d r x).trans
      ((hd r x).trans ((and_congr Iff.rfl (hGraph r x)).trans ?_))
    exact ⟨And.right, fun h => ⟨by obtain ⟨i, hi, _⟩ := h; exact (bounds_l hℳ hi).2, h⟩⟩
  refine ⟨d, ⟨?_, ?_⟩, hRead⟩
  · intro r hr
    obtain ⟨x, hx, hUnique⟩ := total_l hℳ hc hr
    exact ⟨x, (hRead r x).mpr hx, fun y hy => hUnique y ((hRead r y).mp hy)⟩
  · intro r x hx
    obtain ⟨i, hi, _⟩ := (hRead r x).mp hx
    exact (bounds_l hℳ hi).2

def specification_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (c l d : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (SecondOrderAssignmentSyntax.formula_m E d l) <|
    .forallE .num <| .forallE .num <|
      .iff (SecondOrderSequenceSyntax.formula_m (up (up E)) (up (up d))
        (.bvar (.there .here)) (.bvar .here))
        (reversed_m (up (up E)) (up (up c)) (up (up l)) (.bvar (.there .here)) (.bvar .here))

theorem specification_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (c l d : Term signature_m Γ Δ .num) :
    (specification_m E c l d).satisfies η ↔
      valid_l (E.eval η) (d.eval η) (l.eval η) ∧ ∀ r x,
        read_l (E.eval η) (d.eval η) r x ↔ reversed_l (E.eval η) (c.eval η) (l.eval η) r x := by
  simp only [specification_m, Formula.satisfies, SecondOrderAssignmentSyntax.raw_l,
    SecondOrderSequenceSyntax.raw_l, reversed_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m : Formula signature_m [] [.set, .num, .num] :=
  .imp (SecondOrderMemberDefArithmetic.powers_m (.fvar .here)) <|
    .imp (SecondOrderAssignmentSyntax.formula_m (.fvar .here)
      (.fvar (.there .here)) (.fvar (.there (.there .here)))) <|
      .existsE .num <| specification_m (.fvar .here) (.fvar (.there .here))
        (.fvar (.there (.there .here))) (.bvar .here)

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ theory_m) : sentence_m.TrueIn ℳ := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderMemberDefArithmetic.powers_formula_l,
    SecondOrderAssignmentSyntax.raw_l, specification_formula_l, Term.eval]
  exact fun hE hc => exists_l hℳ hE hc

theorem derives_m : Derives theory_m [] sentence_m :=
  SecondOrderCompleteness.derives_m (fun _ hℳ => models_l hℳ)

#print axioms prepend_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyAssignmentReversal
