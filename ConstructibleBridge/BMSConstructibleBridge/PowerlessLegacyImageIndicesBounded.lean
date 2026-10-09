import BMSConstructibleBridge.PowerlessLegacyDefinableQueryReading
import BMSConstructibleBridge.SecondOrderFiniteEnumerationRoots

/-! # 旧公式四标签翻译像的有界行指标

所有检查都在纯隶属语言 ℒ 中以实际母集界定。指标 j 编码 (l,(q,f))，
只保留原旧码 p 在长度 m=succ(l) 的翻译输出 q，以及满足共同预算 L 的
有限赋值 f。尾部从槽 l 起统一取同一母集成员；这正是 raw link 逆向所需
的条件，不把所有四标签公式行或任意 Sat 行认同原 Def。

原翻译及完整数字序列的正确性由调用端提供；这里先给实际 Δ₀ AST、任意
纯结构中的准确读数及全部内部数字的读数。没有无界见证或 Type 选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyImageIndicesBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame SecondOrderObjectSyntax
open PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderModel (num_l set_l succ_l zero_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₃ t)

/-- 所有 L 内且不在 l 内的槽统一取 b，特别包含待更新的槽 l。 -/
def tail_m {Γ Δ : SortContext ℒ} (l L f b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall L <| .imp
    (.neg (member_m (.bvar .here) (up l)))
    (PowerlessValueBounded.formula_m (up f) (.bvar .here) (up b))

theorem tail_delta_l {Γ Δ : SortContext ℒ} (l L f b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (tail_m l L f b) :=
  .bounded_forall L (.imp (.neg (.rel _ _)) (PowerlessValueBounded.delta_l _ _ _))

def tail_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (l L f b : carrier_l 𝒩) : Prop :=
  ∀ i, member_l 𝒩 i L → ¬member_l 𝒩 i l → ThirdOrderSemantics.value_l (ℳ := 𝒩) f i b

theorem tail_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (l L f b : Term ℒ Γ Δ .set) :
    (tail_m l L f b).satisfies η ↔ tail_l (l.eval η) (L.eval η) (f.eval η) (b.eval η) := by
  simp only [tail_m, tail_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessValueBounded.formula_l, member_m, ThirdOrderSemantics.member_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- p、后继长度 m、预算 L 与默认值 b 全部有给定母界。 -/
def body_m {Γ Δ : SortContext ℒ} (ω e N F A l q f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up ω) <|
      membershipLevyBound.boundedExists (up₂ ω) <|
        membershipLevyBound.boundedExists (up₃ A) <|
          let p : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          let m : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
          let L : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let b : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .conj (PowerlessSuccessorBounded.formula_m (up₄ l) m) <|
            .conj (PowerlessLegacyDefinableQueryBounded.translation_m (up₄ ω) (up₄ e)
              (up₄ N) (up₄ F) p m (up₄ q)) <|
              .conj (PowerlessLegacyValidityBounded.budget_m (up₄ ω) (up₄ e) (up₄ N) m p L) <|
                .conj (PowerlessMapBounded.formula_m (up₄ f) L (up₄ A))
                  (tail_m (up₄ l) L (up₄ f) b)

theorem body_delta_l {Γ Δ : SortContext ℒ} (ω e N F A l q f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (body_m ω e N F A l q f) :=
  .bounded_exists ω (.bounded_exists (up ω) (.bounded_exists (up₂ ω)
    (.bounded_exists (up₃ A) (.conj (PowerlessSuccessorBounded.delta_l _ _)
      (.conj (PowerlessLegacyDefinableQueryBounded.translation_delta_l _ _ _ _ _ _ _)
        (.conj (PowerlessLegacyValidityBounded.budget_delta_l _ _ _ _ _ _)
          (.conj (PowerlessMapBounded.delta_l _ _ _) (tail_delta_l _ _ _ _))))))))

def body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e N F A l q f : carrier_l 𝒩) : Prop :=
  ∃ p, member_l 𝒩 p ω ∧ ∃ m, member_l 𝒩 m ω ∧ ∃ L, member_l 𝒩 L ω ∧
    ∃ b, member_l 𝒩 b A ∧ PowerlessNatural.successor_l (ℳ := 𝒩) l m ∧
      PowerlessLegacyDefinableQueryBounded.translation_l (𝒩 := 𝒩) ω e N F p m q ∧
      PowerlessLegacyValidityBounded.budget_holds_l (𝒩 := 𝒩) ω e N m p L ∧
      ThirdOrderSemantics.map_l (ℳ := 𝒩) f L A ∧ tail_l l L f b

theorem body_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F A l q f : Term ℒ Γ Δ .set) :
    (body_m ω e N F A l q f).satisfies η ↔
      body_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (A.eval η)
        (l.eval η) (q.eval η) (f.eval η) := by
  simp only [body_m, body_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessSuccessorBounded.formula_l, PowerlessLegacyDefinableQueryBounded.translation_formula_l,
    PowerlessLegacyValidityBounded.budget_formula_l, PowerlessMapBounded.formula_l,
    tail_formula_l, Arguments.eval, up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 在 ω×(ω×Seq(A)) 中检查翻译像与常值尾，不把 raw U 作为类内参数。 -/
def select_m {Γ Δ : SortContext ℒ} (ω e N F A Seq Idx j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up Idx) <|
      membershipLevyBound.boundedExists (up₂ ω) <|
        membershipLevyBound.boundedExists (up₃ Seq) <|
          let l : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          let t : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
          let q : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let f : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .conj (PowerlessPairBounded.ordered_m l t (up₄ j)) <|
            .conj (PowerlessPairBounded.ordered_m q f t)
              (body_m (up₄ ω) (up₄ e) (up₄ N) (up₄ F) (up₄ A) l q f)

theorem select_delta_l {Γ Δ : SortContext ℒ} (ω e N F A Seq Idx j : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (select_m ω e N F A Seq Idx j) :=
  .bounded_exists ω (.bounded_exists (up Idx) (.bounded_exists (up₂ ω)
    (.bounded_exists (up₃ Seq) (.conj (PowerlessPairBounded.ordered_delta_l _ _ _)
      (.conj (PowerlessPairBounded.ordered_delta_l _ _ _) (body_delta_l _ _ _ _ _ _ _ _))))))

def select_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N F A Seq Idx j : carrier_l 𝒩) : Prop :=
  ∃ l, member_l 𝒩 l ω ∧ ∃ t, member_l 𝒩 t Idx ∧
    ∃ q, member_l 𝒩 q ω ∧ ∃ f, member_l 𝒩 f Seq ∧
      ThirdOrderSemantics.ordered_l (ℳ := 𝒩) l t j ∧
        ThirdOrderSemantics.ordered_l (ℳ := 𝒩) q f t ∧ body_l ω e N F A l q f

theorem select_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N F A Seq Idx j : Term ℒ Γ Δ .set) :
    (select_m ω e N F A Seq Idx j).satisfies η ↔
      select_l (ω.eval η) (e.eval η) (N.eval η) (F.eval η) (A.eval η)
        (Seq.eval η) (Idx.eval η) (j.eval η) := by
  simp only [select_m, select_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessPairBounded.ordered_formula_l, body_formula_l, Arguments.eval,
    up₄, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- L 的全部 raw 成员正好读取全部内部 i<L；尾部不删去非标准坐标。 -/
theorem tail_numeric_l (K : source_coding_l hℳ) (l L : num_l ℳ)
    (f b : SecondOrderQuotient.type_l hℳ) :
    tail_l (𝒩 := RawModel) (code_l K l) (code_l K L) f b ↔
      ∀ i, SecondOrderOrder.lt_l i L → ¬SecondOrderOrder.lt_l i l →
        ThirdOrderSemantics.value_l (ℳ := RawModel) f (code_l K i) b := by
  constructor
  · intro h i hi hNot
    exact h (code_l K i) ((numberCode_mem_iff_lt_l K i L).mpr hi)
      (fun hil => hNot ((numberCode_mem_iff_lt_l K i l).mp hil))
  · intro h x hx hNot
    obtain ⟨i, hi, hix⟩ := SecondOrderFiniteEnumerationRoots.member_number_l K L x hx
    rw [← hix] at hNot ⊢
    exact h i hi (fun hil => hNot ((numberCode_mem_iff_lt_l K i l).mpr hil))

/-- 后继和预算的数字读数保留 m=succ(l)，不假定原 C 或 f 属于 Class。 -/
theorem body_numeric_l (K : source_coding_l hℳ) {N F A f : SecondOrderQuotient.type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := RawModel) K.omega K.omega N)
    {C : set_l ℳ}
    (hF : ∀ n s, ThirdOrderSemantics.value_l (ℳ := RawModel) F (code_l K n) (code_l K s) ↔
      SecondOrderPairing.relation_l C n s) (l q : num_l ℳ) :
    body_l (𝒩 := RawModel) K.omega (code_l K (zero_l ℳ)) N F A (code_l K l) (code_l K q) f ↔
      ∃ p m L : num_l ℳ, ∃ b : SecondOrderQuotient.type_l hℳ,
        mem_l hℳ b A ∧ m = succ_l l ∧ SecondOrderLegacyFormulaTranslation.query_l C p m q ∧
          SecondOrderLegacyFormulaTranslationLength.bound_l m p L ∧
          ThirdOrderSemantics.map_l (ℳ := RawModel) f (code_l K L) A ∧
          ∀ i, SecondOrderOrder.lt_l i L → ¬SecondOrderOrder.lt_l i l →
            ThirdOrderSemantics.value_l (ℳ := RawModel) f (code_l K i) b := by
  unfold body_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro p
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro m
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro L
  apply exists_congr
  intro b
  exact and_congr Iff.rfl (and_congr
    ((PowerlessNumberSuccessorReading.successor_l K l (code_l K m)).trans
      (PowerlessLegacyNumericReading.code_eq_l K m (succ_l l)))
    (and_congr (PowerlessLegacyDefinableQueryReading.translation_reading_l K hN hF p m q)
      (and_congr (PowerlessLegacyNumericReading.budget_l K hN m p L)
        (and_congr Iff.rfl (tail_numeric_l K l L f b)))))

#print axioms tail_delta_l
#print axioms select_delta_l
#print axioms select_formula_l
#print axioms tail_numeric_l
#print axioms body_numeric_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyImageIndicesBounded
