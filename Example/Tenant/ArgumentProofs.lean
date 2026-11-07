import Example.Tenant.Schema
import GraphQL.Plan.Arguments

namespace Example.Tenant.ArgumentProofs
open GraphQL.Plan

def pairArguments : List GraphQL.Argument := [⟨"left", .named "String" true⟩, ⟨"right", .named "String" true⟩]

def leftAccessor : NamedArgument pairArguments "left" := ⟨⟨0, by decide⟩, rfl⟩
def rightAccessor : NamedArgument pairArguments "right" := ⟨⟨1, by decide⟩, rfl⟩

def swappedPack (value : (argumentCode pairArguments).denote) : ArgumentRecord pairArguments
  | ⟨0, _⟩ => value.2
  | ⟨1, _⟩ => value.1
  | ⟨n + 2, h⟩ => False.elim (by simp [pairArguments] at h; omega)

theorem same_typed_argument_swap_rejected : ¬ ArgumentProjectionAgreement pairArguments swappedPack := by
  intro agreement
  have wrong := agreement ("left value", "right value") ⟨0, by decide⟩
  change "right value" = "left value" at wrong
  contradiction

theorem same_typed_layout_swap_rejected :
    ¬ FieldRepresents Binding.demoAst ⟨"pair", .named "String" true, pairArguments⟩
      ⟨"pair", .pair .string .string, .string⟩ pairArguments.reverse := by decide

theorem argument_names_observed (left right : String) :
    leftAccessor.read (packArguments pairArguments (left, right)) = left ∧
    rightAccessor.read (packArguments pairArguments (left, right)) = right := ⟨rfl, rfl⟩

theorem accessor_name_swap_rejected : ¬ pairArguments[1].name = "left" := by decide

end Example.Tenant.ArgumentProofs
