import GraphQL.Machine
import GraphQL.Plan.Specifications

namespace GraphQL.Plan

variable {C : Type} {A : C → Type}

theorem machine_bind_done (machine : Machine C A α) : machine.bind Machine.done = machine := by
  induction machine with
  | done value => rfl
  | pending call resume ih => simp only [Machine.bind]; congr; funext answer; exact ih answer

theorem machine_bind_assoc (machine : Machine C A α) (next : α → Machine C A β)
    (last : β → Machine C A γ) :
    (machine.bind next).bind last = machine.bind (fun value => (next value).bind last) := by
  induction machine with
  | done value => rfl
  | pending call resume ih => simp only [Machine.bind]; congr; funext answer; exact ih answer

instance : LawfulMonad (Machine C A) := LawfulMonad.mk' _
  (fun machine => machine_bind_done machine) (fun _ _ => rfl) machine_bind_assoc

/-- Universal over permitted answers, so this is independent of any particular driver. -/
def Sat (pre : C → Prop) (post : (call : C) → A call → Prop) : Machine C A α → (α → Prop) → Prop
  | .done value, Q => Q value
  | .pending call resume, Q => pre call ∧ ∀ answer, post call answer → Sat pre post (resume answer) Q

def runMachine (resolve : (call : C) → A call) : Machine C A α → α
  | .done value => value
  | .pending call resume => runMachine resolve (resume (resolve call))

theorem sat_weaken (machine : Machine C A α) (h : Sat pre post machine P)
    (implies : ∀ value, P value → Q value) : Sat pre post machine Q := by
  induction machine with
  | done value => exact implies value h
  | pending call resume ih => exact ⟨h.1, fun answer valid => ih answer (h.2 answer valid)⟩

theorem sat_bind (machine : Machine C A α) (next : α → Machine C A β)
    (first : Sat pre post machine P) (rest : ∀ value, P value → Sat pre post (next value) Q) :
    Sat pre post (machine.bind next) Q := by
  induction machine with
  | done value => exact rest value first
  | pending call resume ih => exact ⟨first.1, fun answer valid => ih answer (first.2 answer valid)⟩

theorem run_bind (resolve : (call : C) → A call) (machine : Machine C A α) (next : α → Machine C A β) :
    runMachine resolve (machine.bind next) = runMachine resolve (next (runMachine resolve machine)) := by
  induction machine with
  | done value => rfl
  | pending call resume ih => exact ih (resolve call)

theorem sat_run (resolve : (call : C) → A call)
    (valid : ∀ call, pre call → post call (resolve call))
    (machine : Machine C A α) (proof : Sat pre post machine Q) : Q (runMachine resolve machine) := by
  induction machine with
  | done value => exact proof
  | pending call resume ih => exact ih (resolve call) (proof.2 _ (valid call proof.1))

def traverse (f : α → Machine C A β) : List α → Machine C A (List β)
  | [] => .done []
  | row :: rest => (f row).bind (fun value => (traverse f rest).bind (fun tail => .done (value :: tail)))

theorem run_traverse (resolve : (call : C) → A call) (f : α → Machine C A β) (rows : List α) :
    runMachine resolve (traverse f rows) = rows.map (fun row => runMachine resolve (f row)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [traverse, run_bind, runMachine, List.map_cons, ih]

theorem sat_traverse (f : α → Machine C A β) (rows : List α)
    (valid : ∀ row ∈ rows, Sat pre post (f row) (relation row)) :
    Sat pre post (traverse f rows) (RelatedLists relation rows) := by
  induction rows with
  | nil => exact .nil
  | cons row rest ih =>
    apply sat_bind _ _ (valid row List.mem_cons_self)
    intro result related
    apply sat_bind _ _ (ih (fun r member => valid r (List.mem_cons_of_mem _ member)))
    exact fun tail proof => RelatedLists.cons related proof

/-- Dependent finite traversal retains the original index type in the result. -/
def tabulate {β : Fin n → Type} (f : (i : Fin n) → Machine C A (β i)) : Machine C A ((i : Fin n) → β i) :=
  match n with
  | 0 => .done (fun i => nomatch i)
  | n + 1 => (f 0).bind (fun head => (tabulate (fun i : Fin n => f i.succ)).bind
      (fun tail => .done (Fin.cases head tail)))

theorem run_tabulate (resolve : (call : C) → A call) {β : Fin n → Type}
    (f : (i : Fin n) → Machine C A (β i)) :
    runMachine resolve (tabulate f) = fun i => runMachine resolve (f i) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [tabulate, run_bind, runMachine, ih]
    funext i
    cases i using Fin.cases <;> rfl

theorem sat_tabulate {β : Fin n → Type} (f : (i : Fin n) → Machine C A (β i))
    (relation : (i : Fin n) → β i → Prop) (valid : ∀ i, Sat pre post (f i) (relation i)) :
    Sat pre post (tabulate f) (fun values => ∀ i, relation i (values i)) := by
  induction n with
  | zero => intro values; exact Fin.elim0 values
  | succ n ih =>
    apply sat_bind _ _ (valid 0)
    intro head headValid
    apply sat_bind _ _ (ih (fun i => f i.succ) (fun i => relation i.succ) (fun i => valid i.succ))
    intro tail tailValid i
    cases i using Fin.cases with
    | zero => exact headValid
    | succ i => exact tailValid i

/-- A pure stateful driver can vary its answer for every occurrence of a call. -/
def runStateMachine (resolve : σ → (call : C) → A call × σ) : Machine C A α → σ → α × σ
  | .done value, state => (value, state)
  | .pending call resume, state =>
    let (answer, next) := resolve state call
    runStateMachine resolve (resume answer) next

theorem sat_run_state (resolve : σ → (call : C) → A call × σ)
    (valid : ∀ state call, pre call → post call (resolve state call).1)
    (machine : Machine C A α) (proof : Sat pre post machine Q) (state : σ) :
    Q (runStateMachine resolve machine state).1 := by
  induction machine generalizing state with
  | done value => exact proof
  | pending call resume ih =>
    exact ih (resolve state call).1 (proof.2 _ (valid state call proof.1)) (resolve state call).2

end GraphQL.Plan
