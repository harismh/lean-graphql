import Example.Tenant.Resolved

namespace Example.Tenant.IR

/-- Variables are retained as expressions; P1 accepts literals only. -/
inductive ArgExpr (α : Type) where
  | literal (value : α)
  | variable (name : String)

inductive Guard where
  | always
  | variable (name : String)
  | both (outer inner : Guard)

/-- Occurrences and their child guards stay nested until profile-specific instantiation.
P1 rejects variable expressions and guards, rather than silently evaluating them. -/
inductive Template : ObjectType → Type where
  | nil : Template object
  | leaf (field : Leaf object) (guard : Guard) (rest : Template object) : Template object
  | object (field : Branch parent child) (args : ArgExpr field.Args) (guard : Guard)
      (children : Template child) (rest : Template parent) : Template parent

def Template.surfaceP1 {object : ObjectType} : Template object → Option PSelection
  | .nil => some .nil
  | .leaf field .always rest => do
    return .field field.name [] .nil (← rest.surfaceP1)
  | .object field (.literal args) .always children rest => do
    return .field field.name (field.literals args) (← children.surfaceP1) (← rest.surfaceP1)
  | _ => none

abbrev Instantiated (object : ObjectType) := (selection : PSelection) × Checked object selection

def instantiateP1 (template : Template object) : Option (Instantiated object) := do
  let selection ← template.surfaceP1
  let checked ← lower object selection
  return ⟨selection, checked⟩

def toTemplate : Resolved object selection → Template object
  | .nil => .nil
  | .leaf field rest _ => .leaf field .always (toTemplate rest)
  | .object field args _ children _ rest _ =>
    .object field (.literal args) .always (toTemplate children) (toTemplate rest)

theorem template_surface (resolved : Resolved object selection) :
    (toTemplate resolved).surfaceP1 = some selection := by
  induction resolved with
  | nil => rfl
  | leaf field rest fresh ih => simp [toTemplate, Template.surfaceP1, ih]
  | object field args error children nonempty rest fresh childIH restIH =>
    simp [toTemplate, Template.surfaceP1, childIH, restIH]

theorem template_instantiates (resolved : Resolved object selection) :
    ∃ checked, instantiateP1 (toTemplate resolved) = some ⟨selection, checked⟩ := by
  obtain ⟨checked, h⟩ := lower_complete (resolved_valid resolved)
  exact ⟨checked, by simp [instantiateP1, template_surface, h]⟩

theorem instantiate_source (template : Template object) (result : Instantiated object)
    (h : instantiateP1 template = some result) : template.surfaceP1 = some result.1 := by
  unfold instantiateP1 at h
  cases hs : template.surfaceP1 with
  | none => simp [hs] at h
  | some selection =>
    cases hl : lower object selection with
    | none => simp [hs, hl] at h
    | some checked =>
      simp [hs, hl] at h
      cases h
      rfl

theorem template_guard_rejected (field : Leaf object) (name : String) (rest : Template object) :
    instantiateP1 (.leaf field (.variable name) rest) = none := rfl

theorem template_variable_rejected (field : Branch parent child) (name : String)
    (children : Template child) (rest : Template parent) :
    instantiateP1 (.object field (.variable name) .always children rest) = none := rfl

end Example.Tenant.IR
