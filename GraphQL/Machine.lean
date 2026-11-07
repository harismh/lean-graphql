import GraphQL.Response

namespace GraphQL

/-- A pure suspension tree. The driver supplies exactly the answer type for a call.
    There is no IO, scheduler, network or mutable state in this interface. -/
inductive Machine (Call : Type) (Answer : Call → Type) (α : Type) where
  | done (value : α)
  | pending (call : Call) (resume : Answer call → Machine Call Answer α)

def Machine.bind (machine : Machine C A α) (next : α → Machine C A β) : Machine C A β :=
  match machine with
  | .done value => next value
  | .pending call resume => .pending call (fun answer => (resume answer).bind next)

instance : Monad (Machine C A) where
  pure := .done
  bind := Machine.bind

/-- Binding a continuation cannot dispatch it before the pending call is answered. -/
theorem Machine.bind_pending (c : C) (k : A c → Machine C A α)
    (next : α → Machine C A β) :
    (Machine.pending c k).bind next = Machine.pending c (fun a => (k a).bind next) := rfl

end GraphQL
