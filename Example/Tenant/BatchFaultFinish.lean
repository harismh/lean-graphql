import Example.Tenant.BatchFaultCompletion

namespace Example.Tenant.BatchFault
open GraphQL GraphQL.Plan Planning Batching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem related_get (related : RelatedLists relation left right) (index : Nat)
    (leftBound : index < left.length) (rightBound : index < right.length) : relation left[index] right[index] := by
  induction related generalizing index with
  | nil => simp at leftBound
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index (by simpa using leftBound) (by simpa using rightBound)

theorem traverse_contract (sources : List α) (execute : α → Machine C A β) (relation : α → β → Prop)
    (valid : ∀ source ∈ sources, Sat pre post (execute source) (relation source)) :
    Sat pre post (traverse execute sources) (RelatedLists relation sources) := by
  simpa using Fault.traverse_mapped_contract sources id execute relation valid

theorem task_result_contract (request : Binding.Request) (child : IR.Resolved .project nested)
    (nonempty : nested ≠ .nil) (task : Task) (raw : Outcome ApplicationError Project)
    (post : Fault.Post (branchId .taskProject) request task () raw) (path : Spec.Path) :
    Sat Fault.contracts.Pre Fault.contracts.Post
      ((traverse (fun project => childResult request child project (path ++ [.field "project"]))
        (branchRows (carriers := Binding.carriers) .taskProject raw)).bind
        (fun children => .done (assemble .taskProject raw children (path ++ [.field "project"]))))
      (FrameAt (single .taskProject () child nonempty) request task path) := by
  apply sat_bind _ _ (traverse_contract _ _
    (fun project => FrameAt child request project (path ++ [.field "project"])) ?_)
  · intro results related
    have lengthEq := related_lists_length related
    have certificate := branch_frame .taskProject () child nonempty request task raw post path
      (fun i => results[i.val]'(by omega)) (fun i => by
        simpa [childPath, isList, IR.Branch.name] using related_get related i.val i.isLt (by omega))
    have equal : List.ofFn (fun i : Fin (branchRows (carriers := Binding.carriers) .taskProject raw).length => results[i.val]'(by omega)) = results := by
      apply List.ext_getElem
      · simpa using lengthEq
      · intro i left right; simp
    rw [equal] at certificate
    exact certificate
  · intro project member
    exact child_result_contract request child project (post_rows_owned .taskProject request task () raw post project member) _

theorem finish_contract (request : Binding.Request) (child : IR.Resolved .project nested)
    (nonempty : nested ≠ .nil) (prepared : Batching.Prepared) (valid : PreparedEvidence request prepared)
    (outcomes : Outcomes prepared)
    (permitted : ∀ i, Fault.Post (branchId .taskProject) request ((rows prepared).getValue i).1 () (outcomes i)) :
    Sat Fault.contracts.Pre Fault.contracts.Post (finish request child prepared outcomes)
      (Spec.AuthorizedResponse request.snapshot request.principal (selection nested)) := by
  let taskChild := single .taskProject () child nonempty
  let projectChild := single .tasks () taskChild (by intro h; cases h)
  unfold finish
  apply sat_bind _ _ (sat_tabulate _ (fun (parent : Fin (rows prepared).count) result => FrameAt projectChild request
    ((branchRows (carriers := Binding.carriers) .projects prepared.projects)[parent.val]'(by simpa [rows] using parent.isLt))
    [.field "projects", .index parent.val] result) ?_)
  · intro projects certificates
    have root := branch_frame .projects () projectChild (by intro h; cases h) request () prepared.projects valid.1 [] projects
      (fun i => by simpa [childPath, isList, IR.Branch.name] using certificates i)
    obtain ⟨frame, evidence, rendered⟩ := root () rfl True.intro
    obtain ⟨tree, authorized, erased⟩ := evidence []
    refine ⟨⟨(by intro h; cases h), IR.resolved_valid (resolved child nonempty)⟩, tree, authorized, ?_⟩
    exact congrArg Spec.envelope (erased.trans rendered)
  · intro parent
    apply sat_bind _ _ (sat_tabulate _ (fun (task : Fin ((rows prepared).width parent)) result => FrameAt taskChild request
      ((rows prepared).getValue ⟨parent, task⟩).1
      [.field "projects", .index parent.val, .field "tasks", .index task.val] result) ?_)
    · intro tasks certificates
      exact branch_frame .tasks () taskChild (by intro h; cases h) request _ (prepared.tasks parent) (valid.2 parent)
        [.field "projects", .index parent.val] tasks
        (fun i => by simpa [childPath, isList, IR.Branch.name, rows] using certificates i)
    · intro task
      exact task_result_contract request child nonempty _ (outcomes ⟨parent, task⟩) (permitted ⟨parent, task⟩)
        [.field "projects", .index parent.val, .field "tasks", .index task.val]

end Example.Tenant.BatchFault

