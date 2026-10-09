import BMSConstructibleBridge.PowerlessDefinableMembershipCollapse

/-! # 可定义虚拟域与实际坍缩的关系式同构

纯隶属语言、原 Z₂。实际代码隶属图及其真实域域、递归坍缩已给定，
原求值全像不要求为集合。对原输出作可定义纯公式的内部集合归纳，
证明同一坍缩值识别原输出；同一原输出的坍缩值则由相同行与外延性
识别。结论是关系式单值、单射、隶属对应及对实际值域的满射。
虚拟域的外延性是明确守卫，须由实际区分见证请求导出，不能当新公理。
不要求虚拟域传递，不用外部 Acc，也不预称 T/H 属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipIsomorphism

open Logic FirstOrder ThirdOrderSemantics
open PowerlessDefinableMembershipDiagram (at_m at_formula_l env_l spec_l value_iff_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)
private abbrev up₃ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up₂ t)
private abbrev up₄ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up₂ (up₂ t)

private theorem env_up_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (η : Env 𝒩 Γ Ε)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) (x : 𝒩.Carrier .set) :
    env_l (η.pushBound x) (fun v => up (τ v)) = env_l η τ := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; exact Term.eval_weakenBound _ _ _

private theorem env_id_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) :
    env_l η (fun v => .fvar v) = parameters_l η := by
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; rfl

def image_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C x : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up C))
    (at_m φ (.bvar .here) (up x) (fun v => up (τ v)))

def project_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D H x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up D)) <|
    .conj (at_m φ (.bvar .here) (up x) (fun v => up (τ v)))
      (SecondOrderObjectSyntax.value_m (up H) (.bvar .here) (up y))

def ext_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .forallE .set <|
    .imp (image_m φ (up₂ C) (.bvar (.there .here)) (fun v => up₂ (τ v))) <|
      .imp (image_m φ (up₂ C) (.bvar .here) (fun v => up₂ (τ v))) <|
        .imp (.forallE .set <| .imp
          (image_m φ (up₃ C) (.bvar .here) (fun v => up₃ (τ v)))
          (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there (.there .here))))
            (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))))
          (.equal (.bvar (.there .here)) (.bvar .here))

def point_m {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D H x : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .forallE .set <|
    .imp (project_m φ (up₂ D) (up₂ H) (up₂ x) (.bvar .here) (fun v => up₂ (τ v))) <|
      .imp (project_m φ (up₂ D) (up₂ H) (.bvar (.there .here)) (.bvar .here) (fun v => up₂ (τ v)))
        (.equal (up₂ x) (.bvar (.there .here)))

def image_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (C x : 𝒩.Carrier .set) : Prop :=
  ∃ n, member_l 𝒩 n C ∧ φ.satisfies ((η.pushFree n).pushFree x)

def project_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (D H x y : 𝒩.Carrier .set) : Prop :=
  ∃ n, member_l 𝒩 n D ∧ φ.satisfies ((η.pushFree n).pushFree x) ∧ value_l H n y

def ext_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (C : 𝒩.Carrier .set) : Prop :=
  ∀ x y, image_l φ η C x → image_l φ η C y →
    (∀ z, image_l φ η C z → (member_l 𝒩 z x ↔ member_l 𝒩 z y)) → x = y

def point_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ) (D H x : 𝒩.Carrier .set) : Prop :=
  ∀ y z, project_l φ η D H x z → project_l φ η D H y z → x = y

theorem image_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Ε)
    (C x : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (image_m φ C x τ).satisfies η ↔ image_l φ (env_l η τ) (C.eval η) (x.eval η) := by
  simp only [image_m, image_l, Formula.satisfies, at_formula_l, env_up_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem project_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Ε)
    (D H x y : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (project_m φ D H x y τ).satisfies η ↔ project_l φ (env_l η τ)
      (D.eval η) (H.eval η) (x.eval η) (y.eval η) := by
  simp only [project_m, project_l, Formula.satisfies, at_formula_l, env_up_l,
    value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem ext_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Ε)
    (C : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (ext_m φ C τ).satisfies η ↔ ext_l φ (env_l η τ) (C.eval η) := by
  simp only [ext_m, ext_l, Formula.satisfies, image_formula_l, env_up_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem point_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Ε)
    (D H x : Term ℒ Γ Ε .set) (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    (point_m φ D H x τ).satisfies η ↔ point_l φ (env_l η τ) (D.eval η) (H.eval η) (x.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, project_formula_l, env_up_l,
    up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem domain_subset_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {C A D : Raw} (hA : spec_l φ η C A)
    (hD : PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A D) :
    ∀ n, ε n D → ε n C := by
  intro n hn
  obtain ⟨m, h | h⟩ := (hD n).mp hn
  · exact ((value_iff_l φ η hA n m).mp h).1
  · exact ((value_iff_l φ η hA m n).mp h).2.1

theorem domain_output_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) {C A D : Raw} (hA : spec_l φ η C A)
    (hD : PowerlessDefinableMembershipCollapse.domain_l (𝒩 := 𝒱) A D) :
    ∀ n, ε n D → ∃ x, φ.satisfies ((η.pushFree n).pushFree x) := by
  intro n hn
  obtain ⟨m, h | h⟩ := (hD n).mp hn
  · obtain ⟨_, _, x, _, hx, _, _⟩ := (value_iff_l φ η hA n m).mp h
    exact ⟨x, hx⟩
  · obtain ⟨_, _, _, x, _, hx, _⟩ := (value_iff_l φ η hA m n).mp h
    exact ⟨x, hx⟩

section Diagram

include hℳ

variable {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
  (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
  {C A D T H : SecondOrderQuotient.type_l hℳ}
  (hUnique : ∀ n x y, SecondOrderQuotient.mem_l hℳ n C → φ.satisfies ((η.pushFree n).pushFree x) →
    φ.satisfies ((η.pushFree n).pushFree y) → x = y)
  (hA : spec_l φ η C A) (hD : PowerlessDefinableMembershipCollapse.domain_l
    (𝒩 := SecondOrderQuotient.structure_l hℳ) A D)
  (hH : SecondOrderCollapseFunction.spec_l hℳ A D T H)

include hUnique hA in
theorem edge_l {n m x y : Raw} (hn : ε n C) (hm : ε m C)
    (hx : φ.satisfies ((η.pushFree n).pushFree x))
    (hy : φ.satisfies ((η.pushFree m).pushFree y)) : value_l (ℳ := 𝒱) A n m ↔ ε x y := by
  constructor
  · intro h
    obtain ⟨_, _, a, b, ha, hb, hab⟩ := (value_iff_l φ η hA n m).mp h
    obtain rfl := hUnique n a x hn ha hx
    obtain rfl := hUnique m b y hm hb hy
    exact hab
  · intro h
    exact (value_iff_l φ η hA n m).mpr ⟨hn, hm, x, y, hx, hy, h⟩

include hUnique hA hD hH in
/-- 同一原输出给相同前驱行，不以外部良基归纳证明坍缩相等。 -/
theorem same_l {x y z : Raw} (hy : project_l φ η D H x y)
    (hz : project_l φ η D H x z) : y = z := by
  obtain ⟨n, hn, hnx, hny⟩ := hy
  obtain ⟨m, hm, hmx, hmz⟩ := hz
  have hnC := domain_subset_l φ η hA hD n hn
  have hmC := domain_subset_l φ η hA hD m hm
  have hRow k : value_l (ℳ := 𝒱) A k n ↔ value_l (ℳ := 𝒱) A k m := by
    constructor
    · intro h
      obtain ⟨hk, _, a, b, ha, hb, hab⟩ := (value_iff_l φ η hA k n).mp h
      have hbx := hUnique n b x hnC hb hnx
      exact (value_iff_l φ η hA k m).mpr ⟨hk, hmC, a, x, ha, hmx, hbx ▸ hab⟩
    · intro h
      obtain ⟨hk, _, a, b, ha, hb, hab⟩ := (value_iff_l φ η hA k m).mp h
      have hbx := hUnique m b x hmC hb hmx
      exact (value_iff_l φ η hA k n).mpr ⟨hk, hnC, a, x, ha, hnx, hbx ▸ hab⟩
  apply SecondOrderQuotient.ext_l hℳ y z
  intro v
  rw [hH.2.2.2 n y hn hny v, hH.2.2.2 m z hm hmz v]
  exact exists_congr (fun k => and_congr Iff.rfl (and_congr (hRow k) Iff.rfl))

include hUnique hA hD hH in
theorem step_l (hExt : ext_l φ η C) (x : Raw)
    (ih : ∀ v, ε v x → point_l φ η D H v) : point_l φ η D H x := by
  rintro y z ⟨n, hn, hnx, hnz⟩ ⟨m, hm, hmy, hmz⟩
  have hnC := domain_subset_l φ η hA hD n hn
  have hmC := domain_subset_l φ η hA hD m hm
  apply hExt x y ⟨n, hnC, hnx⟩ ⟨m, hmC, hmy⟩
  rintro v ⟨k, hkC, hkv⟩
  constructor
  · intro hvx
    have hkn := (edge_l φ η hUnique hA hkC hnC hkv hnx).mpr hvx
    have hkD := (hD k).mpr ⟨n, Or.inl hkn⟩
    obtain ⟨q, ⟨_, hkq⟩, _⟩ := hH.2.1.2 k hkD
    have hqz := (hH.2.2.2 n z hn hnz q).mpr ⟨k, hkD, hkn, hkq⟩
    obtain ⟨l, hl, hlm, hlq⟩ := (hH.2.2.2 m z hm hmz q).mp hqz
    obtain ⟨w, hlw⟩ := domain_output_l φ η hA hD l hl
    have hwy := (edge_l φ η hUnique hA
      (domain_subset_l φ η hA hD l hl) hmC hlw hmy).mp hlm
    have hEq := ih v hvx w q ⟨k, hkD, hkv, hkq⟩ ⟨l, hl, hlw, hlq⟩
    change ε v y
    exact hEq.symm ▸ hwy
  · intro hvy
    have hkm := (edge_l φ η hUnique hA hkC hmC hkv hmy).mpr hvy
    have hkD := (hD k).mpr ⟨m, Or.inl hkm⟩
    obtain ⟨q, ⟨_, hkq⟩, _⟩ := hH.2.1.2 k hkD
    have hqz := (hH.2.2.2 m z hm hmz q).mpr ⟨k, hkD, hkm, hkq⟩
    obtain ⟨l, hl, hln, hlq⟩ := (hH.2.2.2 n z hn hnz q).mp hqz
    obtain ⟨w, hlw⟩ := domain_output_l φ η hA hD l hl
    have hwx := (edge_l φ η hUnique hA
      (domain_subset_l φ η hA hD l hl) hnC hlw hnx).mp hln
    have hEq := ih w hwx v q ⟨l, hl, hlw, hlq⟩ ⟨k, hkD, hkv, hkq⟩
    change ε v x
    exact hEq ▸ hwx

include hUnique hA hD hH in
/-- 归纳性质是真实纯公式实例，使用原模型内部正则与分离。 -/
theorem injective_l (hExt : ext_l φ η C) : ∀ x, point_l φ η D H x := by
  let ξ : Env 𝒱 [] (.set :: .set :: Δ) := (η.pushFree D).pushFree H
  let ψ : Formula ℒ [] (.set :: .set :: .set :: Δ) :=
    point_m φ (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
      (fun v => .fvar (.there (.there (.there v))))
  have hEnv (x : Raw) : env_l (ξ.pushFree (sort := SetTheory.SetSort.set) x)
      (fun v => .fvar (.there (.there (.there v)))) = η := by
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s; rfl
  have hFormula (x : Raw) : ψ.satisfies (ξ.pushFree x) ↔ point_l φ η D H x := by
    simpa only [ψ, hEnv, ξ, Term.eval, Env.pushFree_here, Env.pushFree_there] using
      point_formula_l φ (ξ.pushFree x) (.fvar (.there (.there .here)))
        (.fvar (.there .here)) (.fvar .here) (fun v => .fvar (.there (.there (.there v))))
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) ψ ξ
    (fun x ih => (hFormula x).mpr (step_l φ η hUnique hA hD hH hExt x
      (fun v hv => (hFormula v).mp (ih v hv))))
  exact fun x => (hFormula x).mp (hAll x)

include hUnique hA hD hH in
theorem member_l (hExt : ext_l φ η C) {x y a b : Raw}
    (hx : project_l φ η D H x a) (hy : project_l φ η D H y b) : ε x y ↔ ε a b := by
  obtain ⟨n, hn, hnx, hna⟩ := hx
  obtain ⟨m, hm, hmy, hmb⟩ := hy
  have hnC := domain_subset_l φ η hA hD n hn
  have hmC := domain_subset_l φ η hA hD m hm
  constructor
  · intro hxy
    have hnm := (edge_l φ η hUnique hA hnC hmC hnx hmy).mpr hxy
    exact (hH.2.2.2 m b hm hmb a).mpr ⟨n, hn, hnm, hna⟩
  · intro hab
    obtain ⟨k, hk, hkm, hka⟩ := (hH.2.2.2 m b hm hmb a).mp hab
    obtain ⟨z, hkz⟩ := domain_output_l φ η hA hD k hk
    have hzy := (edge_l φ η hUnique hA (domain_subset_l φ η hA hD k hk) hmC hkz hmy).mp hkm
    have hEq := injective_l φ η hUnique hA hD hH hExt x z a
      ⟨n, hn, hnx, hna⟩ ⟨k, hk, hkz, hka⟩
    simpa only [← hEq] using hzy

include hA hD hH in
theorem onto_l : ∀ y, ε y T → ∃ x, project_l φ η D H x y := by
  intro y hy
  obtain ⟨n, hn, hny⟩ := hH.2.2.1 y hy
  obtain ⟨x, hnx⟩ := domain_output_l φ η hA hD n hn
  exact ⟨x, n, hn, hnx, hny⟩

end Diagram

def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (D H T : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (.forallE .set <| point_m φ (up D) (up H) (.bvar .here) (fun v => .fvar v)) <|
    .conj (.forallE .set <| .forallE .set <| .forallE .set <| .imp
      (project_m φ (up₃ D) (up₃ H) (.bvar (.there (.there .here))) (.bvar (.there .here)) (fun v => .fvar v))
      (.imp (project_m φ (up₃ D) (up₃ H) (.bvar (.there (.there .here))) (.bvar .here) (fun v => .fvar v))
        (.equal (.bvar (.there .here)) (.bvar .here)))) <|
      .conj (.forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <| .imp
        (project_m φ (up₄ D) (up₄ H) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (fun v => .fvar v))
        (.imp (project_m φ (up₄ D) (up₄ H) (.bvar (.there (.there .here))) (.bvar .here) (fun v => .fvar v))
          (.iff (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
            (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here)))))
        (.forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up T)) <|
          .existsE .set <| project_m φ (up₂ D) (up₂ H) (.bvar .here) (.bvar (.there .here)) (fun v => .fvar v))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C A D T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessBMSQuotientSubsetImageDerives.unique_m φ C) <|
    .imp (PowerlessDefinableMembershipDiagram.spec_m φ C A) <|
      .imp (PowerlessDefinableMembershipCollapse.domain_m A D) <|
        .imp (SecondOrderCollapseSyntax.formula_m A D T H) <|
          .imp (ext_m φ C (fun v => .fvar v)) (conclusion_m φ D H T)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C A D T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ C A D T H)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (C A D T H : Term ℒ [] Δ .set) :
    (sentence_m φ C A D T H).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessBMSQuotientSubsetImageDerives.unique_m,
    PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessDefinableMembershipCollapse.domain_formula_l, SecondOrderCollapseSyntax.formula_l,
    ext_formula_l, env_id_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there, and_imp]
  intro η hUnique hA hD hH hExt
  simp only [conclusion_m, Formula.satisfies, point_formula_l, project_formula_l,
    env_id_l, parameters_pushBound_l, parameters_empty_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₄, up₃, up₂, up, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  exact ⟨injective_l φ η hUnique hA hD hH hExt,
    fun x y z hy hz => same_l φ η hUnique hA hD hH hy hz,
    fun x y a b hx hy => member_l φ η hUnique hA hD hH hExt hx hy,
    onto_l φ η hA hD hH⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C A D T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ C A D T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ C A D T H)

#print axioms edge_l
#print axioms same_l
#print axioms injective_l
#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessDefinableMembershipIsomorphism
