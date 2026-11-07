import Example.Tenant.Selection
import Example.Tenant.Model

namespace Example.Tenant.IR

inductive Leaf : ObjectType → Type where
  | projectId : Leaf .project
  | projectTitle : Leaf .project
  | taskId : Leaf .task
  | taskTitle : Leaf .task
  deriving DecidableEq

def Leaf.name : Leaf object → String
  | .projectId | .taskId => "id"
  | .projectTitle | .taskTitle => "title"

theorem leaf_declared (field : Leaf object) : LeafField object field.name := by
  cases field
  · exact .projectId
  · exact .projectTitle
  · exact .taskId
  · exact .taskTitle

inductive Branch : ObjectType → ObjectType → Type where
  | project : Branch .query .project
  | projects : Branch .query .project
  | tasks : Branch .project .task
  | taskProject : Branch .task .project
  deriving DecidableEq

def Branch.name : Branch parent child → String
  | .project | .taskProject => "project"
  | .projects => "projects"
  | .tasks => "tasks"

def Branch.Args : Branch parent child → Type
  | .project => String
  | .projects | .tasks | .taskProject => Unit

def Branch.literals (field : Branch parent child) : field.Args → List (String × Literal) :=
  match field with
  | .project => fun key => [("id", .string key)]
  | .projects | .tasks | .taskProject => fun _ => []

theorem branch_declared (field : Branch parent child) (args : field.Args) :
    ObjectField parent field.name (field.literals args) child := by
  cases field
  · exact .project args
  · exact .projects
  · exact .tasks
  · exact .taskProject

/-- A schema-indexed, guard-free selection. Source indices anchor the lowering proof.
Argument failures are representable, but never produced by P1 literal lowering. -/
inductive Resolved : ObjectType → PSelection → Type where
  | nil : Resolved object .nil
  | leaf (field : Leaf object) (rest : Resolved object tail)
      (fresh : field.name ∉ tail.names) :
      Resolved object (.field field.name [] .nil tail)
  | object (field : Branch parent child) (args : field.Args)
      (argumentError : Option FrameworkError)
      (children : Resolved child nested) (nonempty : nested ≠ .nil)
      (rest : Resolved parent tail) (fresh : field.name ∉ tail.names) :
      Resolved parent (.field field.name (field.literals args) nested tail)

def Clean : Resolved object selection → Prop
  | .nil => True
  | .leaf _ rest _ => Clean rest
  | .object _ _ error children _ rest _ => error = none ∧ Clean children ∧ Clean rest

theorem resolved_valid (resolved : Resolved object selection) : ValidPSelection object selection := by
  induction resolved with
  | nil => exact .nil
  | leaf field rest fresh ih => exact .leaf (leaf_declared field) fresh ih
  | object field args error children nonempty rest fresh childIH restIH =>
    exact .object (branch_declared field args) nonempty fresh childIH restIH

abbrev Checked (object : ObjectType) (selection : PSelection) :=
  { resolved : Resolved object selection // Clean resolved }

def lower : (object : ObjectType) → (selection : PSelection) → Option (Checked object selection)
  | _, .nil => some ⟨.nil, trivial⟩
  | .project, .field "id" [] .nil rest => do
    let tail ← lower .project rest
    if fresh : "id" ∉ rest.names then return ⟨.leaf .projectId tail.val fresh, tail.property⟩ else none
  | .project, .field "title" [] .nil rest => do
    let tail ← lower .project rest
    if fresh : "title" ∉ rest.names then return ⟨.leaf .projectTitle tail.val fresh, tail.property⟩ else none
  | .task, .field "id" [] .nil rest => do
    let tail ← lower .task rest
    if fresh : "id" ∉ rest.names then return ⟨.leaf .taskId tail.val fresh, tail.property⟩ else none
  | .task, .field "title" [] .nil rest => do
    let tail ← lower .task rest
    if fresh : "title" ∉ rest.names then return ⟨.leaf .taskTitle tail.val fresh, tail.property⟩ else none
  | .query, .field "project" [("id", .string key)] children rest => do
    let child ← lower .project children
    let tail ← lower .query rest
    if ne : children ≠ .nil then
      if fresh : "project" ∉ rest.names then
        return ⟨.object .project key none child.val ne tail.val fresh, rfl, child.property, tail.property⟩
      else none
    else none
  | .query, .field "projects" [] children rest => do
    let child ← lower .project children
    let tail ← lower .query rest
    if ne : children ≠ .nil then
      if fresh : "projects" ∉ rest.names then
        return ⟨.object .projects () none child.val ne tail.val fresh, rfl, child.property, tail.property⟩
      else none
    else none
  | .project, .field "tasks" [] children rest => do
    let child ← lower .task children
    let tail ← lower .project rest
    if ne : children ≠ .nil then
      if fresh : "tasks" ∉ rest.names then
        return ⟨.object .tasks () none child.val ne tail.val fresh, rfl, child.property, tail.property⟩
      else none
    else none
  | .task, .field "project" [] children rest => do
    let child ← lower .project children
    let tail ← lower .task rest
    if ne : children ≠ .nil then
      if fresh : "project" ∉ rest.names then
        return ⟨.object .taskProject () none child.val ne tail.val fresh, rfl, child.property, tail.property⟩
      else none
    else none
  | _, _ => none

theorem lower_sound (_h : lower object selection = some resolved) : ValidPSelection object selection :=
  resolved_valid resolved.val

theorem lower_complete (valid : ValidPSelection object selection) :
    ∃ resolved, lower object selection = some resolved := by
  induction selection generalizing object with
  | nil => exact ⟨⟨.nil, trivial⟩, rfl⟩
  | field name args children rest childIH restIH =>
    cases valid with
    | leaf decl fresh tail =>
      obtain ⟨tr, ht⟩ := restIH tail
      cases decl <;> simp [lower, ht, fresh]
    | object decl ne fresh child tail =>
      obtain ⟨cr, hc⟩ := childIH child
      obtain ⟨tr, ht⟩ := restIH tail
      cases decl <;> simp [lower, hc, ht, ne, fresh]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem lower_clean (resolved : Resolved object selection) (clean : Clean resolved) :
    lower object selection = some ⟨resolved, clean⟩ := by
  induction resolved with
  | nil => rfl
  | leaf field rest fresh ih =>
    cases field <;> simp [lower, Leaf.name, ih clean, fresh] <;> exact fresh
  | object field args error children nonempty rest fresh childIH restIH =>
    obtain ⟨rfl, childClean, restClean⟩ := clean
    cases field <;> try (change Unit at args; cases args)
    all_goals simp [lower, Branch.name, Branch.literals, childIH childClean, restIH restClean, nonempty, fresh] <;> exact fresh

theorem checked_unique (left right : Checked object selection) : left = right :=
  Option.some.inj ((lower_clean left.val left.property).symm.trans (lower_clean right.val right.property))

end Example.Tenant.IR
