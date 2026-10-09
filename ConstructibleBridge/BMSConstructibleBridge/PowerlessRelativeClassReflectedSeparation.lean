import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation
import BMSConstructibleBridge.PowerlessRelativizationDelta
import BMSConstructibleBridge.PowerlessRelativeClassParameterSeed

/-! # 单个原公式反射后的实际 Class 分离

纯隶属语言、原 Z₂。原公式任意复杂；只有限制到实际 Class 集合 T
的正文是 Δ₀。给定同一正文在输入集合上的类／T 真值对应，原有界
分离构造实际 Class 见证，并保留全部 raw 成员的精确读数。
这里不假定完整类分离或 Collection，也不宣称已经产生反射前提。
对象模式显式保留该有限真值对应；后续应由同一程序坍缩消去它。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassReflectedSeparation

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) := up (up t)

private def entries_m {Δ Γ Θ : SortContext ℒ} (x : Term ℒ Γ Θ .set)
    (ν : VariableSubstitution ℒ Δ Γ Θ) : VariableSubstitution ℒ (.set :: Δ) Γ Θ
  | _, .here => x
  | _, .there v => ν v

def class_m {Δ Γ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B x : Term ℒ Γ Θ .set) (ν : VariableSubstitution ℒ Δ Γ Θ) : Formula ℒ Γ Θ :=
  (PowerlessRelativeClassRelativization.formula_m φ).substitute
    (PowerlessRelativeParameters.binding_m B (entries_m x ν))

def restriction_m {Δ Γ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (T x : Term ℒ Γ Θ .set) (ν : VariableSubstitution ℒ Δ Γ Θ) : Formula ℒ Γ Θ :=
  PowerlessRelativeParameters.instance_m φ T (entries_m x ν)

theorem restriction_delta_l {Δ Γ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (T x : Term ℒ Γ Θ .set) (ν : VariableSubstitution ℒ Δ Γ Θ) :
    Formula.IsDelta0 membershipLevyBound (restriction_m φ T x ν) :=
  PowerlessRelativizationDelta.instance_l φ T (entries_m x ν)

private def bounded_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  restriction_m φ (.fvar (.there .here)) (.fvar .here)
    (fun v => .fvar (.there (.there v)))

def parameters_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Γ Θ : SortContext ℒ} (η : Env 𝒱 Γ Θ)
    (ν : VariableSubstitution ℒ Δ Γ Θ) : Env 𝒱 [] Δ where
  boundVal v := nomatch v
  freeVal v := (ν v).eval η

private theorem parameters_up_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Γ Θ : SortContext ℒ} (η : Env 𝒱 Γ Θ)
    (ν : VariableSubstitution ℒ Δ Γ Θ) (x : carrier_l 𝒱) :
    parameters_l (η.pushBound x) (fun v => up (ν v)) = parameters_l η ν := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    exact Term.eval_weakenBound _ _ _

private theorem bounded_formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Θ)
    (T : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ) (x : carrier_l 𝒱) :
    (bounded_m φ).satisfies
      (((parameters_l η ν).pushFree (T.eval η)).pushFree x) ↔
      (restriction_m φ (up T) (.bvar .here) (fun v => up (ν v))).satisfies
        (η.pushBound x) := by
  simp only [bounded_m, restriction_m, PowerlessRelativeParameters.instance_m,
    Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => (PowerlessRelativization.formula_m φ).satisfies ξ)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here =>
        change T.eval η = (up T).eval (η.pushBound x)
        simp only [up, Term.eval_weakenBound]
    | there v =>
        cases v with
        | here => rfl
        | there v =>
            change (ν v).eval η = (up (ν v)).eval (η.pushBound x)
            simp only [up, Term.eval_weakenBound]

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

def agreement_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B T X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up X)) <|
    .iff (class_m φ (up B) (.bvar .here) (fun v => up (ν v)))
      (restriction_m φ (up T) (.bvar .here) (fun v => up (ν v)))

def conclusion_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .forallE .set <| .iff
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up₂ X))
        (class_m φ (up₂ B) (.bvar .here) (fun v => up₂ (ν v))))

def schema_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B T X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B T) <|
      .imp (SecondOrderObjectSyntax.member_m X T) <|
        .imp (PowerlessRelativeClassParameterSeed.members_m Δ T ν) <|
          .imp (agreement_m φ B T X ν) (conclusion_m φ B X ν)

def sentence_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B T X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B T X ν)

theorem class_formula_l {Δ Γ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env 𝒱 Γ Θ) (B x : Term ℒ Γ Θ .set)
    (ν : VariableSubstitution ℒ Δ Γ Θ) :
    (class_m φ B x ν).satisfies η ↔
      (PowerlessRelativeClassRelativization.formula_m φ).satisfies
        (((parameters_l η ν).pushFree (x.eval η)).pushFree (B.eval η)) := by
  rw [class_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => (PowerlessRelativeClassRelativization.formula_m φ).satisfies ξ)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

theorem restriction_formula_l {Δ Γ Θ : SortContext ℒ}
    {A : Raw} {hA : ∃ z, mem_l hℳ z A} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env 𝒱 Γ Θ) (T x : Term ℒ Γ Θ .set)
    (ν : VariableSubstitution ℒ Δ Γ Θ)
    (ζ : Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) A hA) [] Δ)
    (y : PowerlessMemberStructure.type_l (ℳ := 𝒱) A)
    (hT : T.eval η = A) (hx : x.eval η = y.val)
    (hν : ∀ v : Variable Δ .set, (ν v).eval η = (ζ.freeVal v).val) :
    (restriction_m φ T x ν).satisfies η ↔ φ.satisfies (ζ.pushFree y) := by
  apply PowerlessRelativeParameters.instance_l φ η T (entries_m x ν) (ζ.pushFree y) hT
  intro v
  cases v with
  | here => exact hx
  | there v => exact hν v

theorem point_formula_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Θ)
    (B : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ)
    {hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η)}
    (ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase) [] Δ)
    (hν : ∀ v : Variable Δ .set, (ν v).eval η = (ξ.freeVal v).val)
    (x : PowerlessRelativeClassStructure.type_l hℳ (B.eval η)) (Y : Raw) :
    (class_m φ (up₂ B) (.bvar .here) (fun v => up₂ (ν v))).satisfies
      ((η.pushBound Y).pushBound x.val) ↔ φ.satisfies (ξ.pushFree x) := by
  rw [class_formula_l]
  have hEnv :
      (((parameters_l ((η.pushBound Y).pushBound x.val) (fun v => up₂ (ν v))).pushFree
        (sort := SetTheory.SetSort.set) x.val).pushFree (sort := SetTheory.SetSort.set)
        ((up₂ B).eval ((η.pushBound Y).pushBound x.val))) =
      (PowerlessRelativeClassRelativization.env_l (ξ.pushFree x)).pushFree
        (sort := SetTheory.SetSort.set) (B.eval η) := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => exact (Term.eval_weakenBound _ _ _).trans (Term.eval_weakenBound _ _ _)
      | there v =>
          cases v with
          | here => rfl
          | there v =>
              change (up₂ (ν v)).eval ((η.pushBound Y).pushBound x.val) = (ξ.freeVal v).val
              simpa only [up₂, up, Term.eval_weakenBound] using hν v
  simp only [Term.eval, Env.pushBound_bound_here]
  rw [hEnv]
  exact PowerlessRelativeClassRelativization.formula_l K φ (ξ.pushFree x)

/-- 对象分离包与实际类参数呈现的精确读数。 -/
theorem conclusion_formula_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Θ)
    (B X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ)
    {hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η)}
    (ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase) [] Δ)
    (A : PowerlessRelativeClassStructure.type_l hℳ (B.eval η))
    (hX : X.eval η = A.val)
    (hν : ∀ v : Variable Δ .set, (ν v).eval η = (ξ.freeVal v).val) :
    (conclusion_m φ B X ν).satisfies η ↔
      ∃ Y : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
        ∀ x : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
          mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val A.val ∧ φ.satisfies (ξ.pushFree x) := by
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  change (∃ Y : Raw, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) Y ∧
    ∀ x : Raw, mem_l hℳ x Y ↔ mem_l hℳ x (X.eval η) ∧
      (class_m φ (up₂ B) (.bvar .here) (fun v => up₂ (ν v))).satisfies
        ((η.pushBound Y).pushBound x)) ↔ _
  constructor
  · rintro ⟨Y, hYC, hRead⟩
    refine ⟨⟨Y, hYC⟩, fun x => ?_⟩
    simpa only [hX] using (hRead x.val).trans
      (and_congr Iff.rfl (point_formula_l K φ η B ν ξ hν x Y))
  · rintro ⟨Y, hRead⟩
    refine ⟨Y.val, Y.property, fun x => ?_⟩
    constructor
    · intro hxY
      let xc : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
        ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hxY⟩
      obtain ⟨hxA, hxφ⟩ := (hRead xc).mp hxY
      exact ⟨by simpa only [hX] using hxA, (point_formula_l K φ η B ν ξ hν xc Y.val).mpr hxφ⟩
    · rintro ⟨hxX, hxφ⟩
      have hxA : mem_l hℳ x A.val := hX ▸ hxX
      let xc : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
        ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
      exact (hRead xc).mpr ⟨hxA, (point_formula_l K φ η B ν ξ hν xc Y.val).mp hxφ⟩

def member_env_l {B : Raw}
    {hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B}
    {Δ : SortContext ℒ} (η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] Δ)
    (T : Raw) (hT : ∃ z, mem_l hℳ z T)
    (hParams : ∀ v : Variable Δ .set, mem_l hℳ (η.freeVal v).val T) :
    Env (PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT) [] Δ where
  boundVal v := nomatch v
  freeVal {s} v := match s with | .set => ⟨(η.freeVal v).val, hParams v⟩

/-- 类参数呈现下的有限反射分离，不要求原复杂正文是 Δ₀。 -/
theorem class_exists_l {B : Raw}
    {hBase : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] Δ)
    (X T : PowerlessRelativeClassStructure.type_l hℳ B)
    (hXT : mem_l hℳ X.val T.val)
    (hCover : ∀ x : PowerlessRelativeClassStructure.type_l hℳ B,
      mem_l hℳ x.val X.val → mem_l hℳ x.val T.val)
    (hParams : ∀ v : Variable Δ .set, mem_l hℳ (η.freeVal v).val T.val)
    (hReflection : ∀ x : PowerlessRelativeClassStructure.type_l hℳ B,
      ∀ hx : mem_l hℳ x.val X.val, φ.satisfies (η.pushFree x) ↔
        φ.satisfies ((member_env_l η T.val ⟨X.val, hXT⟩ hParams).pushFree
          (sort := SetTheory.SetSort.set) ⟨x.val, hCover x hx⟩)) :
    ∃ Y : PowerlessRelativeClassStructure.type_l hℳ B,
      ∀ x : PowerlessRelativeClassStructure.type_l hℳ B,
        mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val X.val ∧ φ.satisfies (η.pushFree x) := by
  let ζ := member_env_l η T.val ⟨X.val, hXT⟩ hParams
  have hBound : Formula.IsDelta0 membershipLevyBound (bounded_m φ) :=
    restriction_delta_l φ (.fvar (.there .here)) (.fvar .here)
      (fun v => .fvar (.there (.there v)))
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l hBound (η.pushFree T) X
  have hRead (x : PowerlessRelativeClassStructure.type_l hℳ B)
      (hx : mem_l hℳ x.val X.val) :
      (bounded_m φ).satisfies ((η.pushFree T).pushFree x) ↔
        φ.satisfies (ζ.pushFree (sort := SetTheory.SetSort.set) ⟨x.val, hCover x hx⟩) := by
    have hRaw := PowerlessRelativeClassBounded.formula_l hBound ((η.pushFree T).pushFree x)
    apply hRaw.trans
    apply PowerlessRelativeParameters.instance_l φ
      (PowerlessRelativeClassRelativization.env_l ((η.pushFree T).pushFree x))
      (.fvar (.there .here)) (entries_m (.fvar .here) (fun v => .fvar (.there (.there v))))
      (ζ.pushFree (sort := SetTheory.SetSort.set) ⟨x.val, hCover x hx⟩) rfl
    intro v
    cases v with
    | here => rfl
    | there v => rfl
  refine ⟨Y, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨hxX, hxφ⟩ := (hY x).mp hx
    exact ⟨hxX, (hReflection x hxX).mpr ((hRead x hxX).mp hxφ)⟩
  · rintro ⟨hxX, hxφ⟩
    exact (hY x).mpr ⟨hxX, (hRead x hxX).mpr ((hReflection x hxX).mp hxφ)⟩

/-- 真值对应仅在 X 的实际成员上使用；结论读数覆盖全部 raw 对象。 -/
theorem exists_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒱 [] Θ)
    (B T X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) →
      ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hT : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (T.eval η))
    (hXT : mem_l hℳ (X.eval η) (T.eval η))
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ ((ν v).eval η) (T.eval η))
    (hAgreement : (agreement_m φ B T X ν).satisfies η) :
    (conclusion_m φ B X ν).satisfies η := by
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with
        | .set => ⟨(ν v).eval η, PowerlessRelativeClassCorrespondence.transitive_l
            hℳ hBase hT (hParams _ v)⟩ }
  let V : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨T.eval η, hT⟩
  let A : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨X.eval η, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hT hXT⟩
  have hBound : Formula.IsDelta0 membershipLevyBound (bounded_m φ) :=
    restriction_delta_l φ (.fvar (.there .here)) (.fvar .here)
      (fun v => .fvar (.there (.there v)))
  obtain ⟨Y, hY⟩ := PowerlessRelativeClassDeltaSeparation.exists_l
    hBound (ξ.pushFree V) A
  have hRead (x : PowerlessRelativeClassStructure.type_l hℳ (B.eval η)) :
      mem_l hℳ x.val Y.val ↔ mem_l hℳ x.val (X.eval η) ∧
        (restriction_m φ (up T) (.bvar .here) (fun v => up (ν v))).satisfies
          (η.pushBound x.val) := by
    have hEnv : PowerlessRelativeClassRelativization.env_l ((ξ.pushFree V).pushFree x) =
        ((parameters_l η ν).pushFree (sort := SetTheory.SetSort.set) (T.eval η)).pushFree
          (sort := SetTheory.SetSort.set) x.val := by
      apply Env.ext
      · intro _ v; nomatch v
      · intro s v
        cases s
        cases v with
        | here => rfl
        | there v => cases v <;> rfl
    have hAbsolute := PowerlessRelativeClassBounded.formula_l hBound ((ξ.pushFree V).pushFree x)
    rw [hEnv] at hAbsolute
    exact (hY x).trans (and_congr Iff.rfl
      (hAbsolute.trans (bounded_formula_l φ η T ν x.val)))
  simp only [agreement_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here] at hAgreement
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₂, up,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  refine ⟨Y.val, Y.property, fun x => ?_⟩
  have hClassEq :
      (class_m φ (up₂ B) (.bvar .here) (fun v => up₂ (ν v))).satisfies
        ((η.pushBound Y.val).pushBound x) ↔
      (class_m φ (up B) (.bvar .here) (fun v => up (ν v))).satisfies
        (η.pushBound x) := by
    rw [class_formula_l, class_formula_l]
    have hParamsEq : parameters_l ((η.pushBound Y.val).pushBound x)
        (fun v => up₂ (ν v)) = parameters_l η ν := by
      apply Env.ext
      · intro _ v; nomatch v
      · intro s v
        cases s
        change (up₂ (ν v)).eval ((η.pushBound Y.val).pushBound x) = (ν v).eval η
        simp only [up₂, up, Term.eval_weakenBound]
    rw [hParamsEq, parameters_up_l]
    simp only [up₂, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  constructor
  · intro hx
    let x₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y.property hx⟩
    obtain ⟨hxX, hxφ⟩ := (hRead x₀).mp hx
    exact ⟨hxX, hClassEq.mpr ((hAgreement x hxX).mpr hxφ)⟩
  · rintro ⟨hxX, hxφ⟩
    let x₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
      ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxX⟩
    exact (hRead x₀).mpr ⟨hxX, (hAgreement x hxX).mp (hClassEq.mp hxφ)⟩

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B T X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ) :
    (sentence_m φ B T X ν).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    PowerlessRelativeClassParameterSeed.members_formula_l]
  intro η hBase hT hXT hParams hAgreement
  exact exists_l K φ η B T X ν hBase hT hXT hParams hAgreement

theorem derives_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ))
    (B T X : Term ℒ [] Θ .set) (ν : VariableSubstitution ℒ Δ [] Θ) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B T X ν)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ B T X ν)

#print axioms restriction_delta_l
#print axioms class_exists_l
#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassReflectedSeparation
