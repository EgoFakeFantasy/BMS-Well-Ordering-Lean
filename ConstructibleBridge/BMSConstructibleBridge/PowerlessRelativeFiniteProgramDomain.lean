import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabet
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

/-! # 实际 Class 内的全部内部有限程序编码

代码是 (指令词, 指定输出坐标)。母域为 Seq(Q)×ω；词的内部长度
由它的实际函数定义域读取，不另存可互相冲突的长度标签。
允许空词及缺失输出坐标，后者已由 Output 的确定缺省语义处理。
本模块只构造实际代码母集，逐代码的输出矩阵另行装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramDomain

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeClassStructure (structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def product_m {Γ Δ : SortContext ℒ} (S ω P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up P))
    (PowerlessRelativeClassProduct.body_m (up S) (up ω) (.bvar .here))

def domain_m {Γ Δ : SortContext ℒ} (B ω Q S P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B S) <|
    .conj (PowerlessFiniteSequencesSyntax.spec_m ω Q S) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m B P) (product_m S ω P)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def domain_l (B ω Q S P : type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω Q S ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B P ∧
        ∀ p, mem_l hℳ p P ↔ ∃ w k, mem_l hℳ w S ∧ mem_l hℳ k ω ∧ ordered_l (ℳ := 𝒱) w k p

theorem domain_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω Q S P : Term ℒ Γ Δ .set) :
    (domain_m B ω Q S P).satisfies η ↔
      domain_l (B.eval η) (ω.eval η) (Q.eval η) (S.eval η) (P.eval η) := by
  simp only [domain_m, domain_l, product_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessFiniteSequencesSyntax.spec_formula_l, PowerlessRelativeClassProduct.body_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {B ω Q : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ B Q) :
    ∃ S P, domain_l B ω Q S P := by
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨ω, hωC⟩
  let Q' : PowerlessRelativeClassStructure.type_l hℳ B := ⟨Q, hQ⟩
  have hωLocal : omega_l (ℳ := structure_l hℳ B hBase) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  obtain ⟨S, hS, _⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_ambient_l
    (hBase := hBase) (X := Q') hωLocal
  obtain ⟨P, hP⟩ := SecondOrderDefinableRelationImage.exists_l hℳ (Δ := []) .truth Env.empty S.val ω
  have hRead : ∀ p, mem_l hℳ p P ↔
      ∃ w k, mem_l hℳ w S.val ∧ mem_l hℳ k ω ∧ ordered_l (ℳ := 𝒱) w k p := by
    simpa only [Formula.satisfies, true_and, SecondOrderPairObjects.ordered_l,
      SecondOrderPairObjects.pair_l, ThirdOrderSemantics.ordered_l,
      ThirdOrderSemantics.pair_l, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hP
  exact ⟨S.val, P, S.property, hS,
    PowerlessRelativeClassProduct.member_l hBase S.property hωC hRead, hRead⟩

theorem decode_l {B ω Q S P p : type_l hℳ} (hDomain : domain_l B ω Q S P)
    (hp : mem_l hℳ p P) : ∃ w k n, ordered_l (ℳ := 𝒱) w k p ∧
      mem_l hℳ k ω ∧ mem_l hℳ n ω ∧ map_l (ℳ := 𝒱) w n Q := by
  obtain ⟨w, k, hw, hk, hCode⟩ := (hDomain.2.2.2 p).mp hp
  obtain ⟨n, hn, hWord⟩ := (hDomain.2.1 w).mp hw
  exact ⟨w, k, n, hCode, hk, hn, hWord⟩

/-- 干净函数图的定义域唯一，甚至不要求两个陪域相同。 -/
theorem length_unique_l {w n m Q R : type_l hℳ}
    (hn : map_l (ℳ := 𝒱) w n Q) (hm : map_l (ℳ := 𝒱) w m R) : n = m := by
  apply SecondOrderQuotient.ext_l hℳ
  intro i
  constructor
  · intro hi
    obtain ⟨y, hy, _⟩ := hn.2 i hi
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hm hy.2).1
  · intro hi
    obtain ⟨y, hy, _⟩ := hm.2 i hi
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hn hy.2).1

def schema_m {Δ : SortContext ℒ} (B ω Q : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
          .existsE .set <| .existsE .set <|
            domain_m (up₂ B) (up₂ ω) (up₂ Q) (.bvar (.there .here)) (.bvar .here)

def sentence_m {Δ : SortContext ℒ} (B ω Q : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω Q)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω Q : Term ℒ [] Δ .set) :
    (sentence_m B ω Q).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, domain_formula_l K,
    up₂, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hω hωC hQ
  exact exists_l hBase hω hωC hQ

theorem derives_m {Δ : SortContext ℒ} (B ω Q : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω Q)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω Q)

#print axioms exists_l
#print axioms decode_l
#print axioms length_unique_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramDomain
