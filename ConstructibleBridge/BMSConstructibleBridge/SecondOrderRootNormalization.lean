import BMSConstructibleBridge.SecondOrderCanonicalGraft
import BMSConstructibleBridge.SecondOrderGraftSemantics

/-! # 任意有效根的零根规范呈现

实际选择集合记录旧根的全部子节点，新根拼接得到唯一原图。有效输入与
输出内部双模拟相等；不存在 Type 层代表选择，未要求原根本来就是零。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootNormalization

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure spec_l (A : set_l ℳ) (r : num_l ℳ) (P W : set_l ℳ) : Prop where
  selection : ∀ c, mem_l c P ↔ relation_l A c r
  graft : SecondOrderGraft.spec_l A P W

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : set_l ℳ) (r : num_l ℳ) :
    ∃ P W : set_l ℳ, spec_l A r P W := by
  let φ : Formula signature_m [] [.num, .set, .num] :=
    GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.fvar (.there (.there .here)))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree r).pushFree A)
  obtain ⟨W, hW, _⟩ := SecondOrderCanonicalGraft.exists_l hℳ A P
  exact ⟨P, W, fun c => (hP c).trans (SecondOrderPairing.edge_l _ _ _ _), hW⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {A P P' W W' : set_l ℳ} {r : num_l ℳ}
    (h : spec_l A r P W) (h' : spec_l A r P' W') : W = W' := by
  have hP : P = P' := ext_l hℳ P P' (fun c => (h.selection c).trans (h'.selection c).symm)
  subst P'
  exact SecondOrderCanonicalGraft.unique_l hℳ h.graft h'.graft

theorem root_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {P W : set_l ℳ} (h : spec_l A.real A.root P W) : SecondOrderDomain.wf_l W (zero_l ℳ) :=
  SecondOrderGraftDomain.root_l hℳ A.real P W h.graft
    (fun c hc => SecondOrderDomain.child_l hℳ A.real A.root c A.wf ((h.selection c).mp hc))

def code_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {P W : set_l ℳ} (h : spec_l A.real A.root P W) : SecondOrderGraph.code_l ℳ :=
  ⟨W, zero_l ℳ, root_l hℳ A h⟩

theorem eq_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {P W : set_l ℳ} (h : spec_l A.real A.root P W) : SecondOrderGraph.eq_l (code_l hℳ A h) A := by
  apply (SecondOrderGraph.ext_l hℳ (code_l hℳ A h) A).mpr
  intro B
  have hRoots : ∀ c, mem_l c P → SecondOrderDomain.wf_l A.real c :=
    fun c hc => SecondOrderDomain.child_l hℳ A.real A.root c A.wf ((h.selection c).mp hc)
  change SecondOrderGraph.mem_l B (SecondOrderGraftSemantics.code_l hℳ A.real P W h.graft hRoots) ↔ _
  rw [SecondOrderGraftSemantics.mem_l hℳ A.real P W h.graft hRoots B]
  exact exists_congr (fun c => and_congr (h.selection c) Iff.rfl)

theorem normal_exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) :
    ∃ W : set_l ℳ, ∃ hW : SecondOrderDomain.wf_l W (zero_l ℳ),
      SecondOrderGraph.eq_l ⟨W, zero_l ℳ, hW⟩ A := by
  obtain ⟨P, W, h⟩ := exists_l hℳ A.real A.root
  exact ⟨W, root_l hℳ A h, eq_l hℳ A h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootNormalization
