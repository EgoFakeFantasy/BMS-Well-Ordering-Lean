import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaBodyDerives

/-! # 有限表重命名的规则证书 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def lifted : Nat → List Nat → List Nat
  | 0, table => table
  | cutoff + 1, table => SchemaRename.lift (lifted cutoff table)

def lookupRow (table : List Nat) (index output : Nat) : Nat := nodeValue 0 [listValue table, index, output]
def indexRow (table : List Nat) (cutoff index output : Nat) : Nat :=
  nodeValue 1 [listValue table, cutoff, index, output]
def formulaRow (table : List Nat) (cutoff : Nat) (input output : Tree) : Nat :=
  nodeValue 2 [listValue table, cutoff, treeValue input, treeValue output]
def termRow (table : List Nat) (cutoff : Nat) (input output : Tree) : Nat :=
  nodeValue 3 [listValue table, cutoff, treeValue input, treeValue output]
def validRow (target : Nat) (table : List Nat) : Nat := nodeValue 4 [target, listValue table]
def runRow (target : Nat) (table : List Nat) (input output : Tree) : Nat :=
  nodeValue 5 [target, listValue table, treeValue input, treeValue output]

theorem head_variables (rule : Rule) (hRule : rule ∈ rules) : ∀ i, i ∈ rule.head.variables := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem heads_tagged (rule : Rule) (hRule : rule ∈ rules) : rule.head.tag?.isSome := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem accept_rule (rule : Rule) (hRule : rule ∈ rules) (values : Fin rule.arity → Nat)
    (hGuards : ∀ guard, guard ∈ rule.guards → guard.1.eval values < guard.2.eval values)
    (hPremises : ∀ premise, premise ∈ rule.premises → Acceptance rules (premise.eval values)) :
    Acceptance rules (rule.head.eval values) :=
  Acceptance.of_rule rule hRule values
    (fun index => rule.head.variable_le values (head_variables rule hRule index)) hGuards hPremises

theorem lookup_accept (table : List Nat) (index output : Nat) (hLookup : table[index]? = some output) :
    Acceptance rules (lookupRow table index output) := by
  induction table generalizing index with
  | nil => simp at hLookup
  | cons head tail ih =>
    cases index with
    | zero =>
      have hOutput : head = output := Option.some.inj hLookup
      subst output
      exact accept_rule lookupZero (by simp [rules])
        (fun i => if i.val = 0 then head else listValue tail)
        (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
        (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
    | succ index =>
      exact accept_rule lookupSucc (by simp [rules])
        (fun i => if i.val = 0 then head else if i.val = 1 then listValue tail else if i.val = 2 then index else output)
        (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
          intro premise hPremise
          have hPremise := List.mem_singleton.mp hPremise
          subst premise
          exact ih index hLookup)

theorem index_accept (table : List Nat) (cutoff index output : Nat)
    (hLookup : (lifted cutoff table)[index]? = some output) :
    Acceptance rules (indexRow table cutoff index output) := by
  induction cutoff generalizing index output with
  | zero =>
    exact accept_rule indexBase (by simp [rules])
      (fun i => if i.val = 0 then listValue table else if i.val = 1 then index else output)
      (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
        intro premise hPremise
        have hPremise := List.mem_singleton.mp hPremise
        subst premise
        exact lookup_accept table index output hLookup)
  | succ cutoff ih =>
    cases index with
    | zero =>
      have hOutput : 0 = output := Option.some.inj hLookup
      subst output
      exact accept_rule indexZero (by simp [rules])
        (fun i => if i.val = 0 then listValue table else cutoff)
        (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
        (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
    | succ index =>
      change ((lifted cutoff table).map Nat.succ)[index]? = some output at hLookup
      rw [List.getElem?_map] at hLookup
      obtain ⟨previous, hPrevious, rfl⟩ := Option.map_eq_some_iff.mp hLookup
      exact accept_rule indexSucc (by simp [rules])
        (fun i => if i.val = 0 then listValue table else if i.val = 1 then cutoff else if i.val = 2 then index else previous)
        (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
          intro premise hPremise
          have hPremise := List.mem_singleton.mp hPremise
          subst premise
          exact ih index previous hPrevious)

theorem valid_accept (target : Nat) (table : List Nat) (hValid : ∀ value, value ∈ table → value < target) :
    Acceptance rules (validRow target table) := by
  induction table with
  | nil =>
    exact accept_rule validNil (by simp [rules]) (fun _ => target)
      (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
      (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
  | cons head tail ih =>
    exact accept_rule validCons (by simp [rules])
      (fun i => if i.val = 0 then target else if i.val = 1 then head else listValue tail)
      (by
        intro guard hGuard
        have hGuard := List.mem_singleton.mp hGuard
        subst guard
        exact hValid head List.mem_cons_self) (by
        intro premise hPremise
        have hPremise := List.mem_singleton.mp hPremise
        subst premise
        exact ih (fun value hValue => hValid value (List.mem_cons_of_mem head hValue)))

theorem term_accept (table : List Nat) (cutoff : Nat) (input output : Tree)
    (hRun : SchemaRename.term (lifted cutoff table) input = some output) :
    Acceptance rules (termRow table cutoff input output) := by
  have hCheck : SchemaTerm.check (lifted cutoff table).length input = true := by
    rw [← SchemaRename.term_isSome, hRun]
    rfl
  obtain ⟨index, _, rfl⟩ := (SchemaTerm.check_eq_true_iff _ input).mp hCheck
  change (fun value => Tree.node 0 [leaf value]) <$> (lifted cutoff table)[index]? = some output at hRun
  obtain ⟨value, hValue, rfl⟩ := Option.map_eq_some_iff.mp hRun
  exact accept_rule termRule (by simp [rules])
    (fun i => if i.val = 0 then listValue table else if i.val = 1 then cutoff else if i.val = 2 then index else value)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
      intro premise hPremise
      have hPremise := List.mem_singleton.mp hPremise
      subst premise
      exact index_accept table cutoff index value hValue)

theorem constant_accept (tag : Nat) (table : List Nat) (cutoff : Nat) (hTag : tag = 0 ∨ tag = 1) :
    Acceptance rules (formulaRow table cutoff (.node tag []) (.node tag [])) := by
  have hRule : constantRule tag ∈ rules := by rcases hTag with rfl | rfl <;> simp [rules]
  exact accept_rule (constantRule tag) hRule
    (fun i => if i.val = 0 then listValue table else cutoff)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))

theorem unary_accept (tag : Nat) (binder : Bool) (table : List Nat) (cutoff : Nat) (input output : Tree)
    (hRule : unaryRule tag binder ∈ rules)
    (hBody : Acceptance rules (formulaRow table (if binder then cutoff + 1 else cutoff) input output)) :
    Acceptance rules (formulaRow table cutoff (.node tag [input]) (.node tag [output])) := by
  exact accept_rule (unaryRule tag binder) hRule
    (fun i => if i.val = 0 then listValue table else if i.val = 1 then cutoff else if i.val = 2 then treeValue input else treeValue output)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
      intro premise hPremise
      have hPremise := List.mem_singleton.mp hPremise
      subst premise
      cases binder <;> exact hBody)

theorem binary_accept (tag premiseTag : Nat) (table : List Nat) (cutoff : Nat) (left right leftOut rightOut : Tree)
    (hRule : binaryRule tag premiseTag ∈ rules)
    (hLeft : Acceptance rules (nodeValue premiseTag [listValue table, cutoff, treeValue left, treeValue leftOut]))
    (hRight : Acceptance rules (nodeValue premiseTag [listValue table, cutoff, treeValue right, treeValue rightOut])) :
    Acceptance rules (formulaRow table cutoff (.node tag [left, right]) (.node tag [leftOut, rightOut])) := by
  exact accept_rule (binaryRule tag premiseTag) hRule
    (fun i => if i.val = 0 then listValue table else if i.val = 1 then cutoff else if i.val = 2 then treeValue left
      else if i.val = 3 then treeValue right else if i.val = 4 then treeValue leftOut else treeValue rightOut)
    (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry)) (by
      intro premise hPremise
      dsimp only [binaryRule] at hPremise
      rcases List.mem_cons.mp hPremise with hPremise | hPremise
      · subst premise; exact hLeft
      · have hPremise := List.mem_singleton.mp hPremise
        subst premise; exact hRight)

/-- cutoff 规则逐构造子对应实际重命名器；量词分支通过同一原表的提升解释。 -/
theorem formula_accept (current : List Nat) (input : Tree) :
    ∀ table cutoff, current = lifted cutoff table → ∀ output,
      SchemaRename.formula current input = some output → Acceptance rules (formulaRow table cutoff input output) := by
  fun_induction SchemaRename.formula current input
  case case1 =>
    intro table cutoff _ output hOutput
    cases hOutput
    exact constant_accept 0 table cutoff (Or.inl rfl)
  case case2 =>
    intro table cutoff _ output hOutput
    cases hOutput
    exact constant_accept 1 table cutoff (Or.inr rfl)
  case case3 current left right | case4 current left right | case12 current left right =>
    intro table cutoff hTable output hOutput
    obtain ⟨leftOut, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp hOutput
    obtain ⟨rightOut, hRight, hOutput⟩ := Option.bind_eq_some_iff.mp hRest
    cases hOutput
    exact binary_accept _ 3 table cutoff left right leftOut rightOut (by simp [rules])
      (term_accept table cutoff left leftOut (hTable ▸ hLeft))
      (term_accept table cutoff right rightOut (hTable ▸ hRight))
  case case5 current body ih =>
    intro table cutoff hTable output hOutput
    obtain ⟨bodyOut, hBody, hOutput⟩ := Option.bind_eq_some_iff.mp hOutput
    cases hOutput
    exact unary_accept 4 false table cutoff body bodyOut (by simp [rules])
      (ih table cutoff hTable bodyOut hBody)
  case case10 current body ih | case11 current body ih =>
    intro table cutoff hTable output hOutput
    obtain ⟨bodyOut, hBody, hOutput⟩ := Option.bind_eq_some_iff.mp hOutput
    cases hOutput
    exact unary_accept _ true table cutoff body bodyOut (by simp [rules])
      (ih table (cutoff + 1) (congrArg SchemaRename.lift hTable) bodyOut hBody)
  case case6 current left right ihLeft ihRight
     | case7 current left right ihLeft ihRight
     | case8 current left right ihLeft ihRight
     | case9 current left right ihLeft ihRight =>
    intro table cutoff hTable output hOutput
    obtain ⟨leftOut, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp hOutput
    obtain ⟨rightOut, hRight, hOutput⟩ := Option.bind_eq_some_iff.mp hRest
    cases hOutput
    exact binary_accept _ 2 table cutoff left right leftOut rightOut (by simp [rules])
      (ihLeft table cutoff hTable leftOut hLeft) (ihRight table cutoff hTable rightOut hRight)
  case case13 => intro _ _ _ _ hOutput; cases hOutput

theorem run_accept (target : Nat) (table : List Nat) (input output : Tree)
    (hRun : SchemaRename.run target table input = some output) :
    Acceptance rules (runRow target table input output) := by
  unfold SchemaRename.run at hRun
  split at hRun
  next hValid =>
    apply accept_rule runRule (by simp [rules])
      (fun i => if i.val = 0 then target else if i.val = 1 then listValue table
        else if i.val = 2 then treeValue input else treeValue output)
      (by intro entry hEntry; exact False.elim (List.not_mem_nil hEntry))
    intro premise hPremise
    dsimp only [runRule] at hPremise
    rcases List.mem_cons.mp hPremise with hPremise | hPremise
    · subst premise
      apply valid_accept
      intro value hValue
      exact of_decide_eq_true (List.all_eq_true.mp hValid value hValue)
    · have hPremise := List.mem_singleton.mp hPremise
      subst premise
      exact formula_accept table input table 0 rfl output hRun
  next _ => cases hRun

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaObjectGraph.Rename
