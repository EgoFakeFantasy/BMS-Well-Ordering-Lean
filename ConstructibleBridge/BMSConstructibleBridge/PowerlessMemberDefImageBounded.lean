import BMSConstructibleBridge.PowerlessFiniteSequencesBounded
import BMSConstructibleBridge.PowerlessLegacyImageIndicesBounded
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlots
import BMSConstructibleBridge.SecondOrderRowFamilyBounded

/-! # 原成员 Def 的有界翻译像检查器

固定完整数字序列 N、旧五标签翻译图 F、母层 W 及其规范 Sat 函数 G。
候选 H 不预先要求属于 Class，也不预先要求满足原 Def。非空分支仅在
W 中寻找有限序列集、表示积、合法旧码指标和查询图，最后检查全部行族。
空分支保留原规格中的 H={A}，即 pair(A,A,H)，不是任意空行族。

这里交付实际纯隶属 Δ₀ AST 及任意结构读数。与原完整 Def 的等价另在
Reading 模块利用同一内部编码包证明；此文件不宣称统一层次历史完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame SecondOrderObjectSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₄ t)

def empty_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} (A : carrier_l ℳ) : Prop :=
  ∀ x, ¬member_l ℳ x A

/-- 空母集检查只量化 A 自身。 -/
def empty_m {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall A (.neg (.equal (.bvar .here) (.bvar .here)))

theorem empty_delta_l {Γ Δ : SortContext ℒ} (A : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (empty_m A) :=
  .bounded_forall A (.neg (.equal _ _))

theorem empty_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A : Term ℒ Γ Δ .set) :
    (empty_m A).satisfies η ↔ empty_l (ℳ := 𝒩) (A.eval η) := by
  simp only [empty_m, empty_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  simp only [ThirdOrderSemantics.member_l, Env.pushBound, Assignment.push, not_true_eq_false]

/-- 两个有界覆盖方向；不把 P 预先当作积或假设其成员无垃圾。 -/
def product_m {Γ Δ : SortContext ℒ} (X Y P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedForall P <|
    membershipLevyBound.boundedExists (up X) <|
      membershipLevyBound.boundedExists (up₂ Y) <|
        PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here)
          (.bvar (.there (.there .here)))) <|
    membershipLevyBound.boundedForall X <|
      membershipLevyBound.boundedForall (up Y) <|
        membershipLevyBound.boundedExists (up₂ P) <|
          PowerlessPairBounded.ordered_m (.bvar (.there (.there .here)))
            (.bvar (.there .here)) (.bvar .here)

theorem product_delta_l {Γ Δ : SortContext ℒ} (X Y P : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (product_m X Y P) :=
  .conj (.bounded_forall P (.bounded_exists (up X) (.bounded_exists (up₂ Y)
    (PowerlessPairBounded.ordered_delta_l _ _ _))))
    (.bounded_forall X (.bounded_forall (up Y) (.bounded_exists (up₂ P)
      (PowerlessPairBounded.ordered_delta_l _ _ _))))

def product_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (X Y P : carrier_l 𝒩) : Prop :=
  (∀ p, member_l 𝒩 p P → ∃ x, member_l 𝒩 x X ∧
    ∃ y, member_l 𝒩 y Y ∧ ordered_l (ℳ := 𝒩) x y p) ∧
  ∀ x, member_l 𝒩 x X → ∀ y, member_l 𝒩 y Y →
    ∃ p, member_l 𝒩 p P ∧ ordered_l (ℳ := 𝒩) x y p

theorem product_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (X Y P : Term ℒ Γ Δ .set) :
    (product_m X Y P).satisfies η ↔ product_holds_l (X.eval η) (Y.eval η) (P.eval η) := by
  simp only [product_m, product_holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 反向量词只取 W；层内有序对闭包随后恢复全部 raw 指标。 -/
def indices_m {Γ Δ : SortContext ℒ}
    (ω e N F A Seq Idx W I : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (membershipLevyBound.boundedForall I <|
    PowerlessLegacyImageIndicesBounded.select_m (up ω) (up e) (up N) (up F)
      (up A) (up Seq) (up Idx) (.bvar .here)) <|
    membershipLevyBound.boundedForall W <| .imp
      (PowerlessLegacyImageIndicesBounded.select_m (up ω) (up e) (up N) (up F)
        (up A) (up Seq) (up Idx) (.bvar .here))
      (member_m (.bvar .here) (up I))

theorem indices_delta_l {Γ Δ : SortContext ℒ}
    (ω e N F A Seq Idx W I : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (indices_m ω e N F A Seq Idx W I) :=
  .conj (.bounded_forall I (PowerlessLegacyImageIndicesBounded.select_delta_l _ _ _ _ _ _ _ _))
    (.bounded_forall W (.imp
      (PowerlessLegacyImageIndicesBounded.select_delta_l _ _ _ _ _ _ _ _) (.rel _ _)))

def indices_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F A Seq Idx W I : carrier_l 𝒩) : Prop :=
  (∀ j, member_l 𝒩 j I →
    PowerlessLegacyImageIndicesBounded.select_l ω e N F A Seq Idx j) ∧
  ∀ j, member_l 𝒩 j W →
    PowerlessLegacyImageIndicesBounded.select_l ω e N F A Seq Idx j → member_l 𝒩 j I

theorem indices_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F A Seq Idx W I : Term ℒ Γ Δ .set) :
    (indices_m ω e N F A Seq Idx W I).satisfies η ↔
      indices_holds_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (A.eval η)
        (Seq.eval η) (Idx.eval η) (W.eval η) (I.eval η) := by
  simp only [indices_m, indices_holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessLegacyImageIndicesBounded.select_formula_l, member_m,
    ThirdOrderSemantics.member_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 只需行使用的 I×A 读数；域外边及垃圾成员不会改变这些行。 -/
def queries_m {Γ Δ : SortContext ℒ}
    (ω A Seq Idx Sat I Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall I <|
    membershipLevyBound.boundedForall (up A) <| .iff
      (PowerlessValueBounded.formula_m (up₂ Q) (.bvar (.there .here)) (.bvar .here))
      (PowerlessRelativeClassSatisfactionAllSlots.query_m (up₂ ω) (up₂ A)
        (up₂ Seq) (up₂ Idx) (up₂ Sat) (.bvar (.there .here)) (.bvar .here))

theorem queries_delta_l {Γ Δ : SortContext ℒ}
    (ω A Seq Idx Sat I Q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (queries_m ω A Seq Idx Sat I Q) :=
  .bounded_forall I (.bounded_forall (up A) (.iff (PowerlessValueBounded.delta_l _ _ _)
    (PowerlessRelativeClassSatisfactionAllSlots.query_delta_l _ _ _ _ _ _ _)))

def queries_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A Seq Idx Sat I Q : carrier_l 𝒩) : Prop :=
  ∀ j, member_l 𝒩 j I → ∀ x, member_l 𝒩 x A →
    (value_l (ℳ := 𝒩) Q j x ↔
      PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒩) ω A Seq Idx Sat j x)

theorem queries_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A Seq Idx Sat I Q : Term ℒ Γ Δ .set) :
    (queries_m ω A Seq Idx Sat I Q).satisfies η ↔
      queries_holds_l (ω.eval η) (A.eval η) (Seq.eval η) (Idx.eval η) (Sat.eval η)
        (I.eval η) (Q.eval η) := by
  simp only [queries_m, queries_holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, PowerlessRelativeClassSatisfactionAllSlots.query_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  simp only [ThirdOrderSemantics.member_l, Env.pushBound, Assignment.push]

/-- 固定四个见证的局部数据条件，不含待检验的 H。 -/
def data_m {Γ Δ : SortContext ℒ}
    (ω e N F W A Sat Seq Idx I Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessFiniteSequencesBounded.formula_m ω A W Seq) <|
    .conj (product_m ω Seq Idx) <|
      .conj (indices_m ω e N F A Seq Idx W I) (queries_m ω A Seq Idx Sat I Q)

theorem data_delta_l {Γ Δ : SortContext ℒ}
    (ω e N F W A Sat Seq Idx I Q : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (data_m ω e N F W A Sat Seq Idx I Q) :=
  .conj (PowerlessFiniteSequencesBounded.delta_l _ _ _ _) <|
    .conj (product_delta_l _ _ _) <|
      .conj (indices_delta_l _ _ _ _ _ _ _ _ _) (queries_delta_l _ _ _ _ _ _ _)

def data_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F W A Sat Seq Idx I Q : carrier_l 𝒩) : Prop :=
  PowerlessFiniteSequencesBounded.holds_l ω A W Seq ∧
    product_holds_l ω Seq Idx ∧ indices_holds_l ω e N F A Seq Idx W I ∧
      queries_holds_l ω A Seq Idx Sat I Q

theorem data_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F W A Sat Seq Idx I Q : Term ℒ Γ Δ .set) :
    (data_m ω e N F W A Sat Seq Idx I Q).satisfies η ↔
      data_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (W.eval η) (A.eval η)
        (Sat.eval η) (Seq.eval η) (Idx.eval η) (I.eval η) (Q.eval η) := by
  simp only [data_m, data_l, Formula.satisfies, PowerlessFiniteSequencesBounded.formula_l,
    product_formula_l, indices_formula_l, queries_formula_l]

/-- 整包可提供的见证域；Sat 由实际 G 的值读数另行指定。 -/
def domain_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F W G A Sat : carrier_l 𝒩) : Prop :=
  ∃ Seq, member_l 𝒩 Seq W ∧ ∃ Idx, member_l 𝒩 Idx W ∧
    ∃ I, member_l 𝒩 I W ∧ ∃ Q, member_l 𝒩 Q W ∧
      data_l ω e N F W A Sat Seq Idx I Q ∧ value_l (ℳ := 𝒩) G A Sat

/-- 五个存在对象全部真正有界于 W；待检验的 H 不是见证的母界。 -/
def image_m {Γ Δ : SortContext ℒ}
    (ω e N F W G A H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists W <|
    membershipLevyBound.boundedExists (up W) <|
      membershipLevyBound.boundedExists (up₂ W) <|
        membershipLevyBound.boundedExists (up₃ W) <|
          membershipLevyBound.boundedExists (up₄ W) <|
            let Sat : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
              .bvar (.there (.there (.there (.there .here))))
            let Seq : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
              .bvar (.there (.there (.there .here)))
            let Idx : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
              .bvar (.there (.there .here))
            let I : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
              .bvar (.there .here)
            let Q : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
            .conj (PowerlessValueBounded.formula_m (up₅ G) (up₅ A) Sat) <|
              .conj (data_m (up₅ ω) (up₅ e) (up₅ N) (up₅ F) (up₅ W) (up₅ A)
                Sat Seq Idx I Q) (SecondOrderRowFamilyBounded.formula_m I (up₅ A) Q (up₅ H))

theorem image_delta_l {Γ Δ : SortContext ℒ}
    (ω e N F W G A H : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (image_m ω e N F W G A H) :=
  .bounded_exists W (.bounded_exists (up W) (.bounded_exists (up₂ W)
    (.bounded_exists (up₃ W) (.bounded_exists (up₄ W)
      (.conj (PowerlessValueBounded.delta_l _ _ _)
        (.conj (data_delta_l _ _ _ _ _ _ _ _ _ _ _) (SecondOrderRowFamilyBounded.delta_l _ _ _ _)))))))

def image_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F W G A H : carrier_l 𝒩) : Prop :=
  ∃ Sat, member_l 𝒩 Sat W ∧ ∃ Seq, member_l 𝒩 Seq W ∧
    ∃ Idx, member_l 𝒩 Idx W ∧ ∃ I, member_l 𝒩 I W ∧
      ∃ Q, member_l 𝒩 Q W ∧ value_l (ℳ := 𝒩) G A Sat ∧
        data_l ω e N F W A Sat Seq Idx I Q ∧
          SecondOrderRowFamilyBounded.holds_l I A Q H

theorem image_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F W G A H : Term ℒ Γ Δ .set) :
    (image_m ω e N F W G A H).satisfies η ↔
      image_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (W.eval η) (G.eval η)
        (A.eval η) (H.eval η) := by
  simp only [image_m, image_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, data_formula_l, SecondOrderRowFamilyBounded.formula_l,
    Arguments.eval, up₅, up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ}
    (ω e N F W G A H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (empty_m A) (PowerlessPairBounded.pair_m A A H))
    (.conj (.neg (empty_m A)) (image_m ω e N F W G A H))

theorem delta_l {Γ Δ : SortContext ℒ}
    (ω e N F W G A H : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω e N F W G A H) :=
  .disj (.conj (empty_delta_l _) (PowerlessPairBounded.pair_delta_l _ _ _))
    (.conj (.neg (empty_delta_l _)) (image_delta_l _ _ _ _ _ _ _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F W G A H : carrier_l 𝒩) : Prop :=
  (empty_l (ℳ := 𝒩) A ∧ pair_l (ℳ := 𝒩) A A H) ∨
    (¬empty_l (ℳ := 𝒩) A ∧ image_l ω e N F W G A H)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F W G A H : Term ℒ Γ Δ .set) :
    (formula_m ω e N F W G A H).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (W.eval η) (G.eval η)
        (A.eval η) (H.eval η) := by
  simp only [formula_m, holds_l, Formula.satisfies, empty_formula_l,
    PowerlessPairBounded.pair_formula_l, image_formula_l]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageBounded
