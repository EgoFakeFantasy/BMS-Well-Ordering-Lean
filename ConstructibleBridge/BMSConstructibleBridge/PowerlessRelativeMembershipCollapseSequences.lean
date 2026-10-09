import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseGraphs
import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-! # 成员塌缩固定捕获的内部有限数码空间

对象语言是纯隶属 ℒ，背景为原 Z₂，正式出口使用原 Derives。
真实配对／二元并闭包与 ω⊆I 给出所有内部有限数码函数 f∈I；
成员塌缩再逐点固定每个 f，因而固定已捕获的完整 Seq(ω,ω)。
内部长度可以非标准，不以外部 Nat 列表代替实际有限函数集合。

ω⊆I、ω∈I 和数码空间 N∈I 是不同守卫，不能相互替代。
结论不自动证明 N 被原壳捕获，也不等于原 Def 的截迹绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSequences

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeMembershipCollapseInjectivity (recursive_l recursive_m recursive_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原有限函数本身先进入 I，再由同一真实 H 图证明固定。 -/
theorem sequence_l (K : source_coding_l hℳ) {ω I T H f : type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωI : ∀ x, mem_l hℳ x ω → mem_l hℳ x I)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω ω f) :
    mem_l hℳ f I ∧ SecondOrderFunctionObjects.value_l hℳ H f f := by
  obtain ⟨n, hn, hMap⟩ := hf
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hfI := PowerlessRelativeFiniteHullAssignments.subset_member_l K
    (fun x hx => hωI x (hωEq.symm ▸ hx)) hClosed (hωEq ▸ hn) hMap hωI
  exact ⟨hfI, PowerlessRelativeMembershipCollapseGraphs.graph_l
    (fun _ hx _ hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωI hH hRec hClosed hfI
    (fun _ hx => SecondOrderOmegaTransitive.member_l hℳ hω hn hx) hMap⟩

/-- N 的全部真实成员属于 I 且被固定；N∈I 才能进一步固定 N 本身。 -/
theorem space_l (K : source_coding_l hℳ) {ω N I T H : type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωI : ∀ x, mem_l hℳ x ω → mem_l hℳ x I)
    (hωMem : mem_l hℳ ω I) (hNMem : mem_l hℳ N I)
    (hH : SecondOrderFunctionObjects.map_l hℳ H I T) (hRec : recursive_l hℳ I H)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) I)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω ω N) :
    SecondOrderFunctionObjects.value_l hℳ H ω ω ∧
      SecondOrderFunctionObjects.value_l hℳ H N N ∧
        (∀ f, mem_l hℳ f N → mem_l hℳ f I) ∧
          ∀ f, mem_l hℳ f N → SecondOrderFunctionObjects.value_l hℳ H f f := by
  have hMembers f (hf : mem_l hℳ f N) :=
    sequence_l K hω hωI hH hRec hClosed ((hN f).mp hf)
  exact ⟨PowerlessRelativeMembershipCollapseBase.base_l hℳ ω I T H
    (fun _ hx _ hy => SecondOrderOmegaTransitive.member_l hℳ hω hx hy)
    hωI hH hRec hωMem,
    PowerlessRelativeMembershipCollapseGraphs.image_fixed_l hH hRec hNMem hMembers,
    fun f hf => (hMembers f hf).1, fun f hf => (hMembers f hf).2⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def fixed_m {Γ Δ : SortContext ℒ} (ω N I H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (value_m H ω ω) <| .conj (value_m H N N) <|
    .conj (ThirdOrderTheory.subset_m N I) <| .forallE .set <|
      .imp (member_m (.bvar .here) (up N))
        (value_m (up H) (.bvar .here) (.bvar .here))

theorem fixed_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω N I H : Term ℒ Γ Δ .set) : (fixed_m ω N I H).satisfies η ↔
      SecondOrderFunctionObjects.value_l hℳ (H.eval η) (ω.eval η) (ω.eval η) ∧
        SecondOrderFunctionObjects.value_l hℳ (H.eval η) (N.eval η) (N.eval η) ∧
          (∀ f, mem_l hℳ f (N.eval η) → mem_l hℳ f (I.eval η)) ∧
            ∀ f, mem_l hℳ f (N.eval η) →
              SecondOrderFunctionObjects.value_l hℳ (H.eval η) f f := by
  simp only [fixed_m, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l,
    ThirdOrderSemantics.member_l, member_m, Arguments.eval, up, Term.eval_weakenBound,
    Term.eval, SecondOrderQuotient.structure_l]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let N := .fvar (.there .here)
  let I := .fvar (.there (.there .here))
  let T := .fvar (.there (.there (.there .here)))
  let H := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m ω I) <| .imp (member_m ω I) <|
      .imp (member_m N I) <| .imp (map_m H I T) <| .imp (recursive_m I H) <|
        .imp (PowerlessRelativeFiniteHullAssignments.closed_m I) <|
          .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω N) (fixed_m ω N I H)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, ThirdOrderSemantics.subset_l,
    ThirdOrderSemantics.member_l, SecondOrderObjectSyntax.map_l, recursive_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, fixed_formula_l,
    member_m, Arguments.eval, Term.eval, SecondOrderQuotient.structure_l]
  exact fun hω hωI hωMem hNMem hH hRec hClosed hN =>
    space_l K hω hωI hωMem hNMem hH hRec hClosed hN

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms sequence_l
#print axioms space_l
#print axioms fixed_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSequences
