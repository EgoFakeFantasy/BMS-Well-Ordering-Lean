import BMSConstructibleBridge.PowerlessAppendFamily

/-!
# 全部内部有限赋值图的集合

Pₙ 精确包含所有 n→A 集合函数，而非外部长度的元组编码。
存在性按实际纯公式作内部归纳，再用唯一性收集全部内部 n 的层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteAssignments

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def family_l (n A P : carrier_l ℳ) : Prop := ∀ f, member_l ℳ f P ↔ map_l f n A

def family_m {Γ Δ : SortContext ℒ} (n A P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (P.weakenBound SetTheory.SetSort.set))
    (SecondOrderObjectSyntax.map_m (.bvar .here) (n.weakenBound SetTheory.SetSort.set) (A.weakenBound SetTheory.SetSort.set)))

theorem family_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (n A P : Term ℒ Γ Δ .set) :
    (family_m n A P).satisfies η ↔ family_l (n.eval η) (A.eval η) (P.eval η) := by
  simp only [family_m, family_l, Formula.satisfies, map_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {n A P Q : carrier_l ℳ} (hP : family_l n A P) (hQ : family_l n A Q) : P = Q :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members P Q (fun f => (hP f).trans (hQ f).symm)

theorem empty_l {e : carrier_l ℳ} (he : PowerlessNatural.zero_l e) (A : carrier_l ℳ) : map_l e e A :=
  ⟨fun p hp => (he p hp).elim, fun x hx => (he x hx).elim⟩

theorem empty_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {e f A : carrier_l ℳ} (he : PowerlessNatural.zero_l e) (hf : map_l f e A) : f = e := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro p
  constructor
  · intro hp
    obtain ⟨x, _, hx, _⟩ := hf.1 p hp
    exact (he x hx).elim
  · exact fun hp => (he p hp).elim

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {e : carrier_l ℳ} (he : PowerlessNatural.zero_l e) (A : carrier_l ℳ) : ∃ P, family_l e A P := by
  obtain ⟨P, hP⟩ := PowerlessBasic.pairing_l hℳ e e
  refine ⟨P, fun f => ?_⟩
  constructor
  · intro hf
    have h₁ : f = e := (hP f).mp hf |>.elim id id
    exact h₁.symm ▸ empty_l he A
  · intro hf
    exact (hP f).mpr (Or.inl (empty_unique_l hℳ he hf))

theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {n m A P : carrier_l ℳ} (hP : family_l n A P) (hm : PowerlessNatural.successor_l n m) :
    ∃ Q, family_l m A Q := by
  obtain ⟨_, _, Q, _, _, _, hQ⟩ := PowerlessAppendFamily.exists_l hℳ n P A
  refine ⟨Q, fun g => (hQ g).trans ?_⟩
  constructor
  · rintro ⟨f, hf, a, ha, hg⟩
    exact PowerlessAppendGraph.map_l hℳ ((hP f).mp hf) ha hm hg
  · intro hg
    obtain ⟨f, a, hf, ha, hg⟩ := PowerlessAppendGraph.decompose_l hℳ hg hm
    exact ⟨f, (hP f).mpr hf, a, ha, hg⟩

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (A : carrier_l ℳ) : ∀ n, member_l ℳ n ω → ∃ P, family_l n A P := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => A, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set] := .existsE .set
    (family_m (.fvar .here) (.fvar (.there .here)) (.bvar .here))
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔ ∃ P, family_l n A P := by
    intro n
    simp only [φ, Formula.satisfies, family_formula_l]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun e he => (h e).mpr (zero_l hℳ he A))
    (fun n m _ hm h₁ => (h m).mpr (by
      obtain ⟨P, hP⟩ := (h n).mp h₁
      exact successor_l hℳ hP hm))
  exact fun n hn => (h n).mp (h₀ n hn)

theorem family_graph_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (A : carrier_l ℳ) :
    ∃ F B, map_l F ω B ∧ (∀ P, member_l ℳ P B ↔ ∃ n, member_l ℳ n ω ∧ family_l n A P) ∧
      ∀ n, member_l ℳ n ω → ∀ P, value_l F n P ↔ family_l n A P := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => A, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    family_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  have h : ∀ n P, φ.satisfies (((PowerlessComprehension.env_l η).pushFree n).pushFree P) ↔ family_l n A P := by
    intro n P
    dsimp only [φ]
    rw [family_formula_l]
    rfl
  obtain ⟨F, B, hF, hB, h₀⟩ := PowerlessMapping.exists_l hℳ φ η ω
    (fun n hn => (exists_l hℳ hω A n hn).imp fun P hP => (h n P).mpr hP)
    (fun n _ P Q hP hQ => unique_l hℳ ((h n P).mp hP) ((h n Q).mp hQ))
  exact ⟨F, B, hF, fun P => (hB P).trans (exists_congr fun n => and_congr Iff.rfl (h n P)),
    fun n hn P => (h₀ n hn P).trans (h n P)⟩

theorem all_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) (A : carrier_l ℳ) :
    ∃ S, ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A := by
  obtain ⟨F, B, _, hB, _⟩ := family_graph_l hℳ hω A
  obtain ⟨S, hS⟩ := PowerlessBasic.union_l hℳ B
  refine ⟨S, fun f => (hS f).trans ?_⟩
  constructor
  · rintro ⟨P, hP, hf⟩
    obtain ⟨n, hn, h₀⟩ := (hB P).mp hP
    exact ⟨n, hn, (h₀ f).mp hf⟩
  · rintro ⟨n, hn, hf⟩
    obtain ⟨P, hP⟩ := exists_l hℳ hω A n hn
    exact ⟨P, (hB P).mpr ⟨n, hn, hP⟩, (hP f).mpr hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteAssignments
