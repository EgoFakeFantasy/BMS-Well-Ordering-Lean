import BMSConstructibleBridge.PowerlessHereditaryGraphPresentation
import BMSConstructibleBridge.PowerlessRelativeClassRootedReal
import BMSConstructibleBridge.PowerlessRootedRealSyntax

/-! # 遗传对象的实际带根实数请求

请求正文是纯隶属对象公式，而不是宿主谓词。它要求传递包络的实际
类内枚举、全部内部数上的成员边，以及精确的单根标记。每个已有
遗传对象确有类内实数输出；完整见证族的内域闭包仍需另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequest

open Logic FirstOrder StabilityFrame ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def real_m {Γ Δ : SortContext ℒ} (ω V : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (up V)) (member_m (.bvar .here) (up ω)))

def graph_m {Γ Δ : SortContext ℒ} (ω e S V T f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <| membershipLevyBound.boundedForall (up ω) <|
    .iff (PowerlessRootedRealSyntax.edge_m (up (up ω)) (up (up e)) (up (up S)) (up (up V))
      (.bvar (.there .here)) (.bvar .here))
      (PowerlessHereditaryGraphPresentation.edge_m (up (up T)) (up (up f))
        (.bvar (.there .here)) (.bvar .here))

def root_m {Γ Δ : SortContext ℒ} (ω e o S V r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall ω <| .iff
    (PowerlessRootedRealSyntax.row_m (up ω) (up e) (up S) (up V) (up o) (.bvar .here))
    (.equal (.bvar .here) (up r))

def body_m {Γ Δ : SortContext ℒ} (B ω e o S X V T f r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessHereditaryClass.body_m B X T f ω) <|
    .conj (PowerlessRelativeHierarchySyntax.class_m B V) <|
      .conj (real_m ω V) <| .conj (member_m r ω) <|
        .conj (PowerlessValueBounded.formula_m f r X) <|
          .conj (graph_m ω e S V T f) (root_m ω e o S V r)

def formula_m {Γ Δ : SortContext ℒ} (B ω e o S X V : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    body_m (up (up (up B))) (up (up (up ω))) (up (up (up e))) (up (up (up o)))
      (up (up (up S))) (up (up (up X))) (up (up (up V)))
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def body_l (B ω e o S X V T f r : SecondOrderQuotient.type_l hℳ) : Prop :=
  PowerlessHereditaryClass.body_l hℳ B X T f ω ∧
    PowerlessRelativeClassCorrespondence.member_l hℳ B V ∧
      (∀ c, mem_l hℳ c V → mem_l hℳ c ω) ∧ mem_l hℳ r ω ∧
        ThirdOrderSemantics.value_l (ℳ := 𝒱) f r X ∧
          (∀ a, mem_l hℳ a ω → ∀ b, mem_l hℳ b ω →
            (PowerlessRootedRealSyntax.edge_l (𝒩 := 𝒱) ω e S V a b ↔
              PowerlessHereditaryGraphPresentation.edge_l (ℳ₀ := 𝒱) T f a b)) ∧
          (∀ a, mem_l hℳ a ω → (PowerlessRootedRealSyntax.row_l (𝒩 := 𝒱) ω e S V o a ↔ a = r))

def holds_l (B ω e o S X V : SecondOrderQuotient.type_l hℳ) : Prop :=
  ∃ T f r, body_l B ω e o S X V T f r

theorem real_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω V : Term ℒ Γ Δ .set) :
    (real_m ω V).satisfies η ↔ ∀ c, mem_l hℳ c (V.eval η) → mem_l hℳ c (ω.eval η) := by
  simp only [real_m, Formula.satisfies, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem graph_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω e S V T f : Term ℒ Γ Δ .set) :
    (graph_m ω e S V T f).satisfies η ↔ ∀ a, mem_l hℳ a (ω.eval η) →
      ∀ b, mem_l hℳ b (ω.eval η) →
        (PowerlessRootedRealSyntax.edge_l (𝒩 := 𝒱) (ω.eval η) (e.eval η) (S.eval η) (V.eval η) a b ↔
          PowerlessHereditaryGraphPresentation.edge_l (ℳ₀ := 𝒱) (T.eval η) (f.eval η) a b) := by
  simp only [graph_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessRootedRealSyntax.edge_formula_l,
    PowerlessHereditaryGraphPresentation.edge_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem root_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω e o S V r : Term ℒ Γ Δ .set) :
    (root_m ω e o S V r).satisfies η ↔ ∀ a, mem_l hℳ a (ω.eval η) →
      (PowerlessRootedRealSyntax.row_l (𝒩 := 𝒱) (ω.eval η) (e.eval η) (S.eval η) (V.eval η) (o.eval η) a ↔
        a = r.eval η) := by
  simp only [root_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessRootedRealSyntax.row_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem body_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω e o S X V T f r : Term ℒ Γ Δ .set) :
    (body_m B ω e o S X V T f r).satisfies η ↔
      body_l (B.eval η) (ω.eval η) (e.eval η) (o.eval η) (S.eval η) (X.eval η) (V.eval η) (T.eval η) (f.eval η) (r.eval η) := by
  simp only [body_m, body_l, Formula.satisfies, PowerlessHereditaryClass.body_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, real_formula_l,
    PowerlessValueBounded.formula_l, graph_formula_l, root_formula_l, member_m, Arguments.eval]
  rfl

theorem formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω e o S X V : Term ℒ Γ Δ .set) :
    (formula_m B ω e o S X V).satisfies η ↔
      holds_l (B.eval η) (ω.eval η) (e.eval η) (o.eval η) (S.eval η) (X.eval η) (V.eval η) := by
  simp only [formula_m, holds_l, Formula.satisfies, body_formula_l K,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
/-- 每个遗传对象的请求都有实际类内输出，没有从宿主选择代表或根。 -/
theorem exists_l (K : source_coding_l hℳ) {S X : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hX : PowerlessHereditaryClass.member_l hℳ B X) :
    ∃ V, holds_l B K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val S X V := by
  obtain ⟨T, f, w, hT, hf, hXT, hTrans, hω, hMap, hOnto⟩ := hX
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  rw [hωEq] at hMap hOnto
  let O : type_l hℳ B := ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  obtain ⟨Q, hQ⟩ := PowerlessHereditaryGraphPresentation.class_graph_l (hBase := hBase) O ⟨T, hT⟩ ⟨f, hf⟩
  obtain ⟨U, hU, R, hTrace, hRead⟩ := PowerlessRelativeClassNumericGraph.coded_l (hBase := hBase) K Q
  obtain ⟨a, ha, haX⟩ := hOnto X hXT
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨a, ha⟩
  have hr' : (numberCode_l K r).val = a := congrArg Subtype.val hr
  obtain ⟨V, hV, F, hVTrace, hZero, hOne⟩ := PowerlessRelativeClassRootedReal.rows_l (hBase := hBase) K U r
  refine ⟨V.val, T, f, (numberCode_l K r).val,
    ⟨hT, hf, hXT, hTrans, K.omega_spec, hMap, hOnto⟩, V.property, hV,
    (numberCode_l K r).property, hr'.symm ▸ haX, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨a, ha⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨b, hb⟩
    have hn' : (numberCode_l K n).val = a := congrArg Subtype.val hn
    have hm' : (numberCode_l K m).val = b := congrArg Subtype.val hm
    rw [← hn', ← hm']
    have h := (PowerlessRootedRealSyntax.edge_instance_l K hS hV hVTrace n m).trans
      ((hZero (SecondOrderPairing.value_l n m)).trans
        ((hTrace (SecondOrderPairing.value_l n m)).trans (hRead n m)))
    refine h.trans ⟨fun hEdge => ((hQ _ _).mp hEdge).2.2,
      fun hEdge => (hQ _ _).mpr ⟨(numberCode_l K n).property, (numberCode_l K m).property, hEdge⟩⟩
  · intro a ha
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨a, ha⟩
    have hn' : (numberCode_l K n).val = a := congrArg Subtype.val hn
    rw [← hn']
    exact ((PowerlessRootedRealSyntax.row_instance_l K hS hV hVTrace _ n).trans (hOne n)).trans
      ⟨fun h => congrArg (fun i => (numberCode_l K i).val) h,
        fun h => numberCode_injective_l K (Subtype.ext h)⟩

/-- 输出实数界是请求公式本身的一部分，规范最小化后仍保留。 -/
theorem real_l {B ω e o S X V : SecondOrderQuotient.type_l hℳ}
    (h : holds_l B ω e o S X V) : ∀ c, mem_l hℳ c V → mem_l hℳ c ω := by
  obtain ⟨_, _, _, h⟩ := h
  exact h.2.2.1

theorem class_l {B ω e o S X V : SecondOrderQuotient.type_l hℳ}
    (h : holds_l B ω e o S X V) : PowerlessRelativeClassCorrespondence.member_l hℳ B V := by
  obtain ⟨_, _, _, h⟩ := h
  exact h.2.1

#print axioms formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequest
