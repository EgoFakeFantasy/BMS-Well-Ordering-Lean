import BMSConstructibleBridge.PowerlessLegacyLinkBounded
import BMSConstructibleBridge.PowerlessLegacyTranslationBounded
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionRows

/-! # 原 Def 指定参数行的完整有界查询

F 表示原部分翻译二元图，P 表示原数字幂图；I 是实际 ω×Seq(A) 母集。
查询同时检查原赋值有效性、长度预算、反转填充链接和指定槽 Sat 读取。
有限赋值及查询有序对分别以 Seq(A)、I 为界，不能用逐个存在的无界
见证替代。这里给出纯 Δ₀ AST 及精确值语义；原行识别仍由后续模块
消费完整求值保持性，不能把此证书定义当作整个 Def 或 BMS 已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableQueryBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def translation_m {Γ Δ : SortContext ℒ} (ω e N F p l q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up N) (up l) (up q) (.bvar .here))
    (PowerlessValueBounded.formula_m (up F) (up p) (.bvar .here))

theorem translation_delta_l {Γ Δ : SortContext ℒ} (ω e N F p l q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (translation_m ω e N F p l q) :=
  .bounded_exists ω (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
    (PowerlessValueBounded.delta_l _ _ _))

def translation_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F p l q : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a ω ∧ PowerlessBoundedNumericPairing.holds_l ω e N l q a ∧ value_l F p a

theorem translation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F p l q : Term ℒ Γ Δ .set) :
    (translation_m ω e N F p l q).satisfies η ↔
      translation_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (p.eval η) (l.eval η) (q.eval η) := by
  simp only [translation_m, translation_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessBoundedNumericPairing.formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def body_m {Γ Δ : SortContext ℒ}
    (ω e N P F A S U R p l c x m q L f t : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessLegacyAssignmentBounded.valid_m ω e N P c l) <|
    .conj (PowerlessSuccessorBounded.formula_m l m) <|
      .conj (translation_m ω e N F p m q) <|
        .conj (PowerlessLegacyValidityBounded.budget_m ω e N m p L) <|
          .conj (PowerlessMapBounded.formula_m f L A) <|
            .conj (PowerlessLegacyLinkBounded.formula_m ω e N P c l L e A U f) <|
              .conj (PowerlessPairBounded.ordered_m q f t)
                (PowerlessRelativeClassSatisfactionRows.query_m ω A S l R t x)

theorem body_delta_l {Γ Δ : SortContext ℒ}
    (ω e N P F A S U R p l c x m q L f t : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m ω e N P F A S U R p l c x m q L f t) :=
  .conj (PowerlessLegacyAssignmentBounded.valid_delta_l _ _ _ _ _ _)
    (.conj (PowerlessSuccessorBounded.delta_l _ _)
      (.conj (translation_delta_l _ _ _ _ _ _ _)
        (.conj (PowerlessLegacyValidityBounded.budget_delta_l _ _ _ _ _ _)
          (.conj (PowerlessMapBounded.delta_l _ _ _)
            (.conj (PowerlessLegacyLinkBounded.delta_l _ _ _ _ _ _ _ _ _ _ _)
              (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
                (PowerlessRelativeClassSatisfactionRows.query_delta_l _ _ _ _ _ _ _)))))))

def body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N P F A S U R p l c x m q L f t : carrier_l 𝒩) : Prop :=
  PowerlessLegacyAssignmentBounded.valid_holds_l ω e N P c l ∧
    PowerlessNatural.successor_l l m ∧ translation_l ω e N F p m q ∧
      PowerlessLegacyValidityBounded.budget_holds_l ω e N m p L ∧ map_l f L A ∧
        PowerlessLegacyLinkBounded.holds_l ω e N P c l L e A U f ∧ ordered_l q f t ∧
          PowerlessRelativeClassSatisfactionRows.query_l ω A S l R t x

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P F A S U R p l c x m q L f t : Term ℒ Γ Δ .set) :
    (body_m ω e N P F A S U R p l c x m q L f t).satisfies η ↔
      body_l (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (F.eval η) (A.eval η)
        (S.eval η) (U.eval η) (R.eval η) (p.eval η) (l.eval η) (c.eval η) (x.eval η)
          (m.eval η) (q.eval η) (L.eval η) (f.eval η) (t.eval η) := by
  simp only [body_m, body_l, Formula.satisfies, PowerlessLegacyAssignmentBounded.valid_formula_l,
    PowerlessSuccessorBounded.formula_l, translation_formula_l,
    PowerlessLegacyValidityBounded.budget_formula_l, PowerlessMapBounded.formula_l,
    PowerlessLegacyLinkBounded.formula_l, PowerlessPairBounded.ordered_formula_l,
    PowerlessRelativeClassSatisfactionRows.query_formula_l]

def formula_m {Γ Δ : SortContext ℒ}
    (ω e N P F A S I U R p l c x : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up (up ω)) <|
      membershipLevyBound.boundedExists (up (up (up S))) <|
        membershipLevyBound.boundedExists (up (up (up (up I)))) <|
          let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up t))))
          body_m (w ω) (w e) (w N) (w P) (w F) (w A) (w S) (w U) (w R)
            (w p) (w l) (w c) (w x) (.bvar (.there (.there (.there (.there .here)))))
            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
            (.bvar (.there .here)) (.bvar .here)

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω e N P F A S I U R p l c x : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N P F A S I U R p l c x) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up (up ω))
    (.bounded_exists (up (up (up S))) (.bounded_exists (up (up (up (up I))))
      (body_delta_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N P F A S I U R p l c x : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ ∃ q, member_l 𝒩 q ω ∧ ∃ L, member_l 𝒩 L ω ∧
    ∃ f, member_l 𝒩 f S ∧ ∃ t, member_l 𝒩 t I ∧
      body_l ω e N P F A S U R p l c x m q L f t

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N P F A S I U R p l c x : Term ℒ Γ Δ .set) :
    (formula_m ω e N P F A S I U R p l c x).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (P.eval η) (F.eval η) (A.eval η)
        (S.eval η) (I.eval η) (U.eval η) (R.eval η) (p.eval η) (l.eval η) (c.eval η) (x.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, body_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableQueryBounded
