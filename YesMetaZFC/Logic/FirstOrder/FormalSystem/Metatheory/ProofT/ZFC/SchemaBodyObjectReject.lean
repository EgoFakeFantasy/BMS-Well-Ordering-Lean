import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaBodyObject

/-! # 任意原始正文的递归拒绝证书 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Body
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem term_reject (depth : Nat) (input : Tree) (h : SchemaTerm.check depth input = false) :
    Rejection rules (row 0 depth input) := by
  apply Rejection.of_rule
  intro rule hRule values _ hHead hGuards
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [termRule, constantRule, atomRule, unaryRule, binaryRule] at values hHead hGuards ⊢
  · have hFields : [depth, treeValue input] =
        [values 0, nodeValue 0 [nodeValue (values 1) []]] :=
      ((nodeValue_eq_iff 0 0 [depth, treeValue input]
        [values 0, nodeValue 0 [nodeValue (values 1) []]]).mp hHead).2
    have hDepth := (List.cons.inj hFields).1
    have hInput := (List.cons.inj (List.cons.inj hFields).2).1
    have hIndex := hGuards (.var 1, .var 0) List.mem_cons_self
    change values 1 < values 0 at hIndex
    have hTree : input = .node 0 [leaf (values 1)] := by
      apply treeValue_injective
      exact hInput
    have hTrue := (SchemaTerm.check_eq_true_iff depth input).mpr
      ⟨values 1, hDepth.symm ▸ hIndex, hTree⟩
    rw [h] at hTrue
    contradiction
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 0 []]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 1 []]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 2 [values 1, values 2]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 3 [values 1, values 2]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 4 [values 1]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 5 [values 1, values 2]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 6 [values 1, values 2]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 7 [values 1, values 2]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 8 [values 1, values 2]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 9 [values 1]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 10 [values 1]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)
  · have hTag := ((nodeValue_eq_iff 0 1 [depth, treeValue input]
      [values 0, nodeValue 11 [values 1, values 2]]).mp hHead).1
    exact False.elim (Nat.zero_ne_one hTag)

theorem atom_check (tag depth : Nat) (left right : Tree) (hTag : tag = 2 ∨ tag = 3 ∨ tag = 11) :
    SchemaBody.check depth (.node tag [left, right]) =
      (SchemaTerm.check depth left && SchemaTerm.check depth right) := by
  rcases hTag with rfl | rfl | rfl
  all_goals
    unfold SchemaBody.check
    rw [ProjectDecode.formula.eq_def]
    cases hLeft : ProjectDecode.term depth left <;> cases hRight : ProjectDecode.term depth right <;>
      simp [SchemaTerm.check, hLeft, hRight]

theorem unary_check (tag depth : Nat) (binder : Bool) (body : Tree)
    (hTag : (tag = 4 ∧ binder = false) ∨ (tag = 9 ∧ binder = true) ∨ (tag = 10 ∧ binder = true)) :
    SchemaBody.check depth (.node tag [body]) =
      SchemaBody.check (if binder then depth + 1 else depth) body := by
  rcases hTag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    unfold SchemaBody.check
    rw [ProjectDecode.formula.eq_def]
    simp
    first
    | solve | cases ProjectDecode.formula depth body <;> rfl
    | solve | cases ProjectDecode.formula (depth + 1) body <;> rfl

theorem binary_check (tag depth : Nat) (left right : Tree) (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8) :
    SchemaBody.check depth (.node tag [left, right]) =
      (SchemaBody.check depth left && SchemaBody.check depth right) := by
  rcases hTag with rfl | rfl | rfl | rfl
  all_goals
    unfold SchemaBody.check
    rw [ProjectDecode.formula.eq_def]
    cases hLeft : ProjectDecode.formula depth left <;> cases hRight : ProjectDecode.formula depth right <;>
      simp [hLeft, hRight]

private theorem reject_atom_matched (tag depth : Nat) (input : Tree) (values : Fin 3 → Nat)
    (hTag : tag = 2 ∨ tag = 3 ∨ tag = 11)
    (hHead : row 1 depth input = nodeValue 1 [values 0, nodeValue tag [values 1, values 2]])
    (hBad : SchemaBody.check depth input = false) :
    ∃ premise, premise ∈ (atomRule tag).premises ∧ Rejection rules (premise.eval values) := by
  have hFields := ((nodeValue_eq_iff 1 1 [depth, treeValue input]
    [values 0, nodeValue tag [values 1, values 2]]).mp hHead).2
  have hDepth := (List.cons.inj hFields).1
  have hInput := (List.cons.inj (List.cons.inj hFields).2).1
  obtain ⟨left, right, rfl, hLeft, hRight⟩ := treeValue_node_two hInput
  rw [atom_check tag depth left right hTag, Bool.and_eq_false_iff] at hBad
  rcases hBad with hBad | hBad
  · refine ⟨SchemaObjectGraph.node (n := 3) 0 [.var 0, .var 1] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 0 [values 0, values 1])
    rw [← hDepth, ← hLeft]
    exact term_reject depth left hBad
  · refine ⟨SchemaObjectGraph.node (n := 3) 0 [.var 0, .var 2] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 0 [values 0, values 2])
    rw [← hDepth, ← hRight]
    exact term_reject depth right hBad

private theorem reject_unary_matched (tag depth : Nat) (binder : Bool) (input : Tree) (values : Fin 2 → Nat)
    (hTag : (tag = 4 ∧ binder = false) ∨ (tag = 9 ∧ binder = true) ∨ (tag = 10 ∧ binder = true))
    (hHead : row 1 depth input = nodeValue 1 [values 0, nodeValue tag [values 1]])
    (hBad : SchemaBody.check depth input = false)
    (ih : ∀ childDepth child, sizeOf child < sizeOf input → SchemaBody.check childDepth child = false →
      Rejection rules (row 1 childDepth child)) :
    ∃ premise, premise ∈ (unaryRule tag binder).premises ∧ Rejection rules (premise.eval values) := by
  have hFields := ((nodeValue_eq_iff 1 1 [depth, treeValue input]
    [values 0, nodeValue tag [values 1]]).mp hHead).2
  have hDepth := (List.cons.inj hFields).1
  have hInput := (List.cons.inj (List.cons.inj hFields).2).1
  obtain ⟨body, rfl, hBody⟩ := treeValue_node_one hInput
  rw [unary_check tag depth binder body hTag] at hBad
  refine ⟨SchemaObjectGraph.node (n := 2) 1 [if binder then .succ (.var 0) else .var 0, .var 1] ,
    List.mem_cons_self, ?_⟩
  have hReject := ih (if binder then depth + 1 else depth) body (by simp; omega) hBad
  cases binder
  · change Rejection rules (nodeValue 1 [values 0, values 1])
    rw [← hDepth, ← hBody]
    exact hReject
  · change Rejection rules (nodeValue 1 [values 0 + 1, values 1])
    rw [← hDepth, ← hBody]
    exact hReject

private theorem reject_binary_matched (tag depth : Nat) (input : Tree) (values : Fin 3 → Nat)
    (hTag : tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8)
    (hHead : row 1 depth input = nodeValue 1 [values 0, nodeValue tag [values 1, values 2]])
    (hBad : SchemaBody.check depth input = false)
    (ih : ∀ childDepth child, sizeOf child < sizeOf input → SchemaBody.check childDepth child = false →
      Rejection rules (row 1 childDepth child)) :
    ∃ premise, premise ∈ (binaryRule tag).premises ∧ Rejection rules (premise.eval values) := by
  have hFields := ((nodeValue_eq_iff 1 1 [depth, treeValue input]
    [values 0, nodeValue tag [values 1, values 2]]).mp hHead).2
  have hDepth := (List.cons.inj hFields).1
  have hInput := (List.cons.inj (List.cons.inj hFields).2).1
  obtain ⟨left, right, rfl, hLeft, hRight⟩ := treeValue_node_two hInput
  rw [binary_check tag depth left right hTag, Bool.and_eq_false_iff] at hBad
  rcases hBad with hBad | hBad
  · refine ⟨SchemaObjectGraph.node (n := 3) 1 [.var 0, .var 1] , List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 1 [values 0, values 1])
    rw [← hDepth, ← hLeft]
    exact ih depth left (by simp; omega) hBad
  · refine ⟨SchemaObjectGraph.node (n := 3) 1 [.var 0, .var 2] , List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Rejection rules (nodeValue 1 [values 0, values 2])
    rw [← hDepth, ← hRight]
    exact ih depth right (by simp; omega) hBad

/-- 对任意原始树递归构造拒绝证书，畸形构造通过全部规则头的反演排除。 -/
theorem check_reject (depth : Nat) (input : Tree) (hBad : SchemaBody.check depth input = false) :
    Rejection rules (row 1 depth input) := by
  apply Rejection.of_rule
  intro rule hRule values _ hHead _
  have ih : ∀ childDepth child, sizeOf child < sizeOf input → SchemaBody.check childDepth child = false →
      Rejection rules (row 1 childDepth child) := by
    intro childDepth child _ hChild
    exact check_reject childDepth child hChild
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [termRule, constantRule, atomRule, unaryRule, binaryRule] at values hHead ⊢
  · have hTag := ((nodeValue_eq_iff 1 0 [depth, treeValue input]
      [values 0, nodeValue 0 [nodeValue (values 1) []]]).mp hHead).1
    exact False.elim (Nat.one_ne_zero hTag)
  · have hFields := ((nodeValue_eq_iff 1 1 [depth, treeValue input]
      [values 0, nodeValue 0 []]).mp hHead).2
    have hInput := (List.cons.inj (List.cons.inj hFields).2).1
    have hShape := treeValue_node_zero hInput
    subst input
    unfold SchemaBody.check at hBad
    rw [ProjectDecode.formula.eq_def] at hBad
    simp at hBad
  · have hFields := ((nodeValue_eq_iff 1 1 [depth, treeValue input]
      [values 0, nodeValue 1 []]).mp hHead).2
    have hInput := (List.cons.inj (List.cons.inj hFields).2).1
    have hShape := treeValue_node_zero hInput
    subst input
    unfold SchemaBody.check at hBad
    rw [ProjectDecode.formula.eq_def] at hBad
    simp at hBad
  · exact reject_atom_matched 2 depth input values (by simp) hHead hBad
  · exact reject_atom_matched 3 depth input values (by simp) hHead hBad
  · exact reject_unary_matched 4 depth false input values (by simp) hHead hBad ih
  · exact reject_binary_matched 5 depth input values (by simp) hHead hBad ih
  · exact reject_binary_matched 6 depth input values (by simp) hHead hBad ih
  · exact reject_binary_matched 7 depth input values (by simp) hHead hBad ih
  · exact reject_binary_matched 8 depth input values (by simp) hHead hBad ih
  · exact reject_unary_matched 9 depth true input values (by simp) hHead hBad ih
  · exact reject_unary_matched 10 depth true input values (by simp) hHead hBad ih
  · exact reject_atom_matched 11 depth input values (by simp) hHead hBad
termination_by sizeOf input

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Body
