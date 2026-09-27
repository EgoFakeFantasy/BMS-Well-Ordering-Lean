import BMSConstructibleBridge.PowerlessTruthParameters
import BMSConstructibleBridge.PowerlessTruthOracle
import BMSConstructibleBridge.PowerlessOracleRules

/-!
# 低层调用接受公式的无核心参数语义

原低层公式及完整求值见证均保留实际原语法真值。下列等价只整理
参数，不提供证书存在性，不需要小层满足完整 Core。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleParameters

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n D p c f : carrier_l ℳ) : Prop :=
  B.satisfies (env_l ω e T t₁ t₂ t₃ n p c f) ∨
    PowerlessTruthParameters.step_l ω e T t₁ t₂ t₃ D p c f

def certificate_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n D : carrier_l ℳ) : Prop :=
  ∀ r, member_l ℳ r D → ∃ p c f, PowerlessTruthRecord.record_l p c f r ∧
    member_l ℳ c ω ∧ step_l B ω e T t₁ t₂ t₃ n D p c f

theorem certificate_formula_l (B : Formula ℒ [] context_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n D : Term ℒ Γ Δ .set) :
    (PowerlessTruthOracle.certificate_m B ω e T t₁ t₂ t₃ n D).satisfies η ↔
      certificate_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η)
        (t₂.eval η) (t₃.eval η) (n.eval η) (D.eval η) := by
  simp only [PowerlessTruthOracle.certificate_m, certificate_l, step_l, Formula.satisfies,
    PowerlessTruthRecord.record_formula_l, PowerlessTruthParameters.step_formula_l,
    instance_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def accepts_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) : Prop :=
  ∃ D, certificate_l B ω e T t₁ t₂ t₃ n D ∧ PowerlessTruthRecord.entry_l D p c f

theorem accepts_formula_l (B : Formula ℒ [] context_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) :
    (PowerlessTruthOracle.accepts_m B ω e T t₁ t₂ t₃ n p c f).satisfies η ↔
      accepts_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (n.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [PowerlessTruthOracle.accepts_m, accepts_l, Formula.satisfies,
    certificate_formula_l B, PowerlessTruthRecord.entry_formula_l, Term.eval_weakenBound]
  rfl


def nand_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n p a b f : carrier_l ℳ) : Prop :=
  PowerlessAmbientAssignments.finite_l ω f ∧
    ((p = e ∧ (accepts_l B ω e T t₁ t₂ t₃ n t₁ a f ∨ accepts_l B ω e T t₁ t₂ t₃ n t₁ b f)) ∨
      (p = t₁ ∧ accepts_l B ω e T t₁ t₂ t₃ n e a f ∧ accepts_l B ω e T t₁ t₂ t₃ n e b f))

theorem nand_formula_l (B : Formula ℒ [] context_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n p a b f : Term ℒ Γ Δ .set) :
    (PowerlessOracleRules.nand_m B ω e T t₁ t₂ t₃ n p a b f).satisfies η ↔
      nand_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (n.eval η) (p.eval η) (a.eval η) (b.eval η) (f.eval η) := by
  simp only [PowerlessOracleRules.nand_m, nand_l, Formula.satisfies,
    PowerlessAmbientAssignments.finite_formula_l, accepts_formula_l]

def witness_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n p b f i a : carrier_l ℳ) : Prop :=
  ∃ g, PowerlessAmbientAssignments.finite_l ω g ∧ PowerlessAssignmentUpdate.update_l f i a g ∧
    accepts_l B ω e T t₁ t₂ t₃ n p b g

theorem witness_formula_l (B : Formula ℒ [] context_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n p b f i a : Term ℒ Γ Δ .set) :
    (PowerlessOracleRules.witness_m B ω e T t₁ t₂ t₃ n p b f i a).satisfies η ↔
      witness_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (n.eval η) (p.eval η) (b.eval η) (f.eval η) (i.eval η) (a.eval η) := by
  simp only [PowerlessOracleRules.witness_m, witness_l, Formula.satisfies,
    PowerlessAmbientAssignments.finite_formula_l, PowerlessAssignmentUpdate.update_formula_l, accepts_formula_l, Term.eval_weakenBound]
  rfl

def existential_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n b f i : carrier_l ℳ) : Prop :=
  PowerlessAmbientAssignments.slot_l ω f i ∧ ∃ a, witness_l B ω e T t₁ t₂ t₃ n e b f i a

theorem existential_formula_l (B : Formula ℒ [] context_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n b f i : Term ℒ Γ Δ .set) :
    (PowerlessOracleRules.existential_m B ω e T t₁ t₂ t₃ n b f i).satisfies η ↔
      existential_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (n.eval η) (b.eval η) (f.eval η) (i.eval η) := by
  simp only [PowerlessOracleRules.existential_m, existential_l, Formula.satisfies,
    PowerlessAmbientAssignments.slot_formula_l, witness_formula_l, Term.eval_weakenBound]
  rfl

def positive_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n b f i j : carrier_l ℳ) : Prop :=
  PowerlessAmbientAssignments.slot_l ω f i ∧ ∃ z, value_l f j z ∧
    ∃ a, member_l ℳ a z ∧ witness_l B ω e T t₁ t₂ t₃ n e b f i a

theorem positive_formula_l (B : Formula ℒ [] context_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n b f i j : Term ℒ Γ Δ .set) :
    (PowerlessOracleRules.positive_m B ω e T t₁ t₂ t₃ n b f i j).satisfies η ↔
      positive_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (n.eval η) (b.eval η) (f.eval η) (i.eval η) (j.eval η) := by
  simp only [PowerlessOracleRules.positive_m, positive_l, Formula.satisfies,
    PowerlessAmbientAssignments.slot_formula_l, value_formula_l, witness_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def negative_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n b f i j : carrier_l ℳ) : Prop :=
  PowerlessAmbientAssignments.finite_l ω f ∧ (¬ PowerlessAmbientAssignments.slot_l ω f i ∨
    ∀ z, value_l f j z → ∀ a, member_l ℳ a z → witness_l B ω e T t₁ t₂ t₃ n t₁ b f i a)

theorem negative_formula_l (B : Formula ℒ [] context_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n b f i j : Term ℒ Γ Δ .set) :
    (PowerlessOracleRules.negative_m B ω e T t₁ t₂ t₃ n b f i j).satisfies η ↔
      negative_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (n.eval η) (b.eval η) (f.eval η) (i.eval η) (j.eval η) := by
  simp only [PowerlessOracleRules.negative_m, negative_l, Formula.satisfies,
    PowerlessAmbientAssignments.finite_formula_l, PowerlessAmbientAssignments.slot_formula_l, value_formula_l, witness_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl
end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleParameters
