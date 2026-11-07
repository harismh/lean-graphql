import GraphQL.Plan.Machine

namespace GraphQL.Plan

variable {C : Type} {A : C → Type} {α : Type} {m : Type → Type}
  {pre : C → Prop} {post : (call : C) → A call → Prop} {Q : α → Prop}

/-- A backend must produce evidence for the actual returned answer. A predicate
annotation by itself is not a certified producer. -/
abbrev CertifiedBackend (m : Type → Type) (pre : C → Prop) (post : (call : C) → A call → Prop) :=
  (call : C) → pre call → m {answer : A call // post call answer}

/-- Recurses on the actual Machine, carrying the continuation obligation supplied
by Sat. Exceptions or nontermination in m need not produce a certified result. -/
def driveCertified [Monad m] (backend : CertifiedBackend m pre post) :
    (program : Machine C A α) → Sat pre post program Q → m {result : α // Q result}
  | .done result, proof => pure ⟨result, proof⟩
  | .pending call resume, proof => do
    let answer ← backend call proof.1
    driveCertified backend (resume answer.val) (proof.2 answer.val answer.property)

/-- The pure producer constructs its certificate from the caller's refinement
proof. It does not assert anything about external services. -/
def pureBackend [Monad m] (resolve : (call : C) → A call)
    (refines : ∀ call, pre call → post call (resolve call)) : CertifiedBackend m pre post :=
  fun call valid => pure ⟨resolve call, refines call valid⟩

theorem drive_pure_value (resolve : (call : C) → A call)
    (refines : ∀ call, pre call → post call (resolve call))
    (program : Machine C A α) (proof : Sat pre post program Q) :
    (driveCertified (m := Id) (pureBackend resolve refines) program proof).val = runMachine resolve program := by
  induction program with
  | done => rfl
  | pending call resume ih => exact ih (resolve call) (proof.2 _ (refines call proof.1))

/-- A failure of a transport operation is not an Answer and cannot be scattered
as though it were a vector of per-key resolver errors. Only public names cross
this boundary; private exception strings are not representable. -/
inductive TransportFailure where
  | unavailable | interrupted | internal
  deriving DecidableEq, Repr

abbrev TransportBackend (m : Type → Type) (pre : C → Prop) (post : (call : C) → A call → Prop) :=
  (call : C) → pre call → m (Except TransportFailure {answer : A call // post call answer})

/-- Transport failure aborts the current request before its continuation runs. -/
def driveTransport [Monad m] (backend : TransportBackend m pre post) :
    (program : Machine C A α) → Sat pre post program Q → m (Except TransportFailure {result : α // Q result})
  | .done result, proof => pure (.ok ⟨result, proof⟩)
  | .pending call resume, proof => do
    match ← backend call proof.1 with
    | .error failure => pure (.error failure)
    | .ok answer => driveTransport backend (resume answer.val) (proof.2 answer.val answer.property)

def transportBackend [Monad m] (backend : CertifiedBackend m pre post) : TransportBackend m pre post :=
  fun call valid => do return .ok (← backend call valid)

theorem drive_transport_success [Monad m] [LawfulMonad m] (backend : CertifiedBackend m pre post)
    (program : Machine C A α) (proof : Sat pre post program Q) :
    driveTransport (transportBackend backend) program proof =
      (do return .ok (← driveCertified backend program proof)) := by
  induction program with
  | done => simp [driveTransport, driveCertified]
  | pending call resume ih =>
    simp only [driveTransport, transportBackend, driveCertified, bind_assoc, pure_bind]
    congr 1
    funext answer
    exact ih answer.val (proof.2 answer.val answer.property)

theorem transport_failure_stops (backend : TransportBackend Id pre post) (failure : TransportFailure)
    (proof : Sat pre post (.pending call resume) Q)
    (failed : backend call proof.1 = .error failure) :
    driveTransport backend (.pending call resume) proof = .error failure := by
  simp [driveTransport, failed]
  rfl

/-- Exceptions are converted to a named request transport failure. The exception
payload is discarded and never becomes a per-field answer. -/
def redactTransport [Monad m] [MonadExceptOf ε m]
    (backend : TransportBackend m pre post) : TransportBackend m pre post :=
  fun call valid => try backend call valid catch _ => pure (.error .internal)

end GraphQL.Plan
