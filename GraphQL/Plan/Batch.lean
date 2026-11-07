import GraphQL.Plan.Bindings
import GraphQL.Plan.Interpreter

namespace GraphQL.Plan.Batch
open GraphQL.Plan
variable {C : Type} {A : C → Type} {α β : Type}
variable {schema : Schema} {models : Fin schema.objectCount → Type} {scope app : Type}

/-- Exact primitive count, universally quantified over answers at every suspension. -/
def Calls : Machine C A α → Nat → Prop
  | .done _, n => n = 0
  | .pending _ resume, n => ∃ k, n = k + 1 ∧ ∀ answer, Calls (resume answer) k

theorem calls_bind (machine : Machine C A α) (next : α → Machine C A β)
    (first : Calls machine n) (rest : ∀ value, Calls (next value) m) :
    Calls (machine.bind next) (n + m) := by
  induction machine generalizing n with
  | done value => simp only [Calls] at first; subst n; simpa [Machine.bind] using rest value
  | pending call resume ih =>
    obtain ⟨k, rfl, valid⟩ := first
    exact ⟨k + m, by omega, fun answer => ih answer (valid answer)⟩

def runCount (resolve : (call : C) → A call) : Machine C A α → α × Nat
  | .done value => (value, 0)
  | .pending call resume => let result := runCount resolve (resume (resolve call)); (result.1, result.2 + 1)

theorem calls_count (machine : Machine C A α) (proof : Calls machine n)
    (resolve : (call : C) → A call) : (runCount resolve machine).2 = n := by
  induction machine generalizing n with
  | done => exact proof.symm
  | pending call resume ih =>
    obtain ⟨k, rfl, valid⟩ := proof
    exact congrArg (· + 1) (ih (resolve call) (valid (resolve call)))

theorem count_value (machine : Machine C A α) (resolve : (call : C) → A call) :
    (runCount resolve machine).1 = runMachine resolve machine := by
  induction machine with
  | done => rfl
  | pending call resume ih => exact ih (resolve call)

theorem count_bind (resolve : (call : C) → A call) (machine : Machine C A α)
    (next : α → Machine C A β) :
    (runCount resolve (machine.bind next)).2 =
      (runCount resolve machine).2 + (runCount resolve (next (runMachine resolve machine))).2 := by
  induction machine with
  | done => simp [runCount, runMachine, Machine.bind]
  | pending call resume ih =>
    simp only [Machine.bind, runCount, runMachine, ih]
    omega

theorem tabulate_calls {β : Fin n → Type} (f : (i : Fin n) → Machine C A (β i))
    (each : ∀ i, Calls (f i) 1) : Calls (tabulate f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have proof := calls_bind (f 0) (fun head =>
      (tabulate (fun i : Fin n => f i.succ)).bind (fun tail => .done (Fin.cases (motive := β) head tail)))
      (each 0) (fun head => calls_bind _ _
        (ih (fun i => f i.succ) (fun i => each i.succ)) (fun _ => (rfl : Calls (.done _) 0)))
    simpa only [tabulate, Nat.add_zero, Nat.add_comm 1 n] using proof

theorem tabulate_cost {β : Fin n → Type} (f : (i : Fin n) → Machine C A (β i))
    (cost : Fin n → Nat) (each : ∀ i, Calls (f i) (cost i)) :
    Calls (tabulate f) (List.ofFn cost).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have proof := calls_bind (f 0) (fun head =>
      (tabulate (fun i : Fin n => f i.succ)).bind (fun tail => .done (Fin.cases (motive := β) head tail)))
      (each 0) (fun head => calls_bind _ _
        (ih (fun i => f i.succ) (fun i => cost i.succ) (fun i => each i.succ))
        (fun _ => (rfl : Calls (.done _) 0)))
    simpa only [tabulate, Nat.add_zero, List.ofFn_succ, List.sum_cons] using proof

/-- Stable first representative per key; one scope is supplied outside the row list. -/
def keys [DecidableEq κ] (key : α → κ) (rows : List α) : List κ := (rows.map key).eraseDups

def representative [DecidableEq κ] (key : α → κ) (rows : List α)
    (i : Fin (keys key rows).length) : α :=
  rows[(rows.map key).idxOf (keys key rows)[i]]' (by
    have member := List.getElem_mem i.isLt
    have h := List.idxOf_lt_length_of_mem (List.mem_eraseDups.mp member)
    simpa using h)

theorem representative_mem [DecidableEq κ] (key : α → κ) (rows : List α)
    (i : Fin (keys key rows).length) : representative key rows i ∈ rows := List.getElem_mem _

theorem representative_key [DecidableEq κ] (key : α → κ) (rows : List α)
    (i : Fin (keys key rows).length) : key (representative key rows i) = (keys key rows)[i] := by
  have present : (keys key rows)[i] ∈ rows.map key := List.mem_eraseDups.mp (List.getElem_mem i.isLt)
  have h := List.getElem_idxOf (List.idxOf_lt_length_of_mem present)
  simpa only [List.getElem_map, representative] using h

def position [DecidableEq κ] (key : α → κ) (rows : List α) (i : Fin rows.length) :
    Fin (keys key rows).length := ⟨(keys key rows).idxOf (key rows[i]),
      List.idxOf_lt_length_of_mem (List.mem_eraseDups.mpr (List.mem_map.mpr ⟨rows[i], List.getElem_mem i.isLt, rfl⟩))⟩

theorem position_key [DecidableEq κ] (key : α → κ) (rows : List α) (i : Fin rows.length) :
    (keys key rows)[position key rows i] = key rows[i] := List.getElem_idxOf _

theorem representative_outcome [DecidableEq κ] (key : α → κ) (single : α → β)
    (sufficient : ∀ left right, key left = key right → single left = single right)
    (rows : List α) (i : Fin rows.length) :
    single (representative key rows (position key rows i)) = single rows[i] :=
  sufficient _ _ ((representative_key key rows _).trans (position_key key rows i))

/-- Ceiling division, with an explicit empty-wave case. -/
def chunks (size capacity : Nat) : Nat := if size = 0 then 0 else (size - 1) / capacity + 1

theorem chunks_ceiling (size capacity : Nat) (positive : 0 < capacity) :
    chunks size capacity = (size + capacity - 1) / capacity := by
  by_cases empty : size = 0
  · subst size; simp [chunks, Nat.div_eq_of_lt (by omega : capacity - 1 < capacity)]
  · rw [chunks, if_neg empty]
    have arithmetic : size + capacity - 1 = size - 1 + capacity := by omega
    rw [arithmetic, Nat.add_div_right _ positive]

def width (size capacity chunk : Nat) : Nat := min capacity (size - chunk * capacity)

def sourceIndex (positive : 0 < capacity) (chunk : Fin (chunks size capacity))
    (offset : Fin (width size capacity chunk.val)) : Fin size :=
  ⟨chunk.val * capacity + offset.val, by
    have h := offset.isLt
    simp only [width, Nat.lt_min] at h
    omega⟩

def group (positive : 0 < capacity) (i : Fin size) : Fin (chunks size capacity) :=
  ⟨i.val / capacity, by
    have hi := i.isLt
    have bound := Nat.div_le_div_right (c := capacity) (show i.val ≤ size - 1 by omega)
    simp only [chunks, if_neg (show size ≠ 0 by omega)]
    omega⟩

def offset (positive : 0 < capacity) (i : Fin size) : Fin (width size capacity (group positive i).val) :=
  ⟨i.val % capacity, by
    have remainder := Nat.mod_lt i.val positive
    have division := Nat.div_add_mod i.val capacity
    rw [Nat.mul_comm capacity] at division
    simp only [width, group, Nat.lt_min]
    omega⟩

theorem chunk_position (positive : 0 < capacity) (i : Fin size) :
    sourceIndex positive (group positive i) (offset positive i) = i := by
  apply Fin.ext
  simpa [sourceIndex, group, offset, Nat.mul_comm] using Nat.div_add_mod i.val capacity

/-- This emits one actual batch suspension per chunk; no hidden single fallback. -/
def load (field : FieldId schema owner) (context : scope) (inputs : Vector (models owner × field.Args) size)
    (capacity : Nat) (positive : 0 < capacity) :
    Execution schema models scope app (Fin size → Outcome app (field.Out models)) :=
  (tabulate (fun chunk : Fin (chunks size capacity) =>
    Machine.pending (.batch field context (Vector.ofFn (fun offset => inputs.get (sourceIndex positive chunk offset))))
      (fun answer : Vector (Outcome app (field.Out models)) (width size capacity chunk.val) => .done answer))).bind
    (fun answers => .done (fun i => (answers (group positive i)).get (offset positive i)))

theorem load_calls (field : FieldId schema owner) (context : scope)
    (inputs : Vector (models owner × field.Args) size) (positive : 0 < capacity) :
    Calls (load (app := app) field context inputs capacity positive) (chunks size capacity) := by
  unfold load
  apply calls_bind (n := chunks size capacity) (m := 0)
  · exact tabulate_calls _ (fun _ => ⟨0, rfl, fun _ => rfl⟩)
  · intro _; rfl

theorem load_exact (field : FieldId schema owner) (context : scope)
    (inputs : Vector (models owner × field.Args) size) (positive : 0 < capacity)
    (resolve : (call : Call schema models scope) → Answer app call)
    (single : models owner → field.Args → Outcome app (field.Out models))
    (exact : ∀ n (rows : Vector (models owner × field.Args) n) i,
      (resolve (.batch field context rows)).get i = single (rows.get i).1 (rows.get i).2) :
    runMachine resolve (load field context inputs capacity positive) =
      fun i => single (inputs.get i).1 (inputs.get i).2 := by
  simp only [load, run_bind, run_tabulate, runMachine]
  funext i
  rw [exact]
  have ofFn_get {α : Type} {n : Nat} (f : Fin n → α) (j : Fin n) :
      (Vector.ofFn f).get j = f j := by simp [Vector.get, Fin.cast]
  rw [ofFn_get, chunk_position]

theorem chunk_nonempty (positive : 0 < capacity) (chunk : Fin (chunks size capacity)) :
    0 < width size capacity chunk.val := by
  have bound := chunk.isLt
  have nonempty : size ≠ 0 := by intro empty; subst size; simp [chunks] at bound
  simp only [chunks, if_neg nonempty] at bound
  have mul := (Nat.le_div_iff_mul_le positive).mp (show chunk.val ≤ (size - 1) / capacity by omega)
  simp only [width, Nat.lt_min]
  omega

def BoundedBatch (capacity : Nat) : Call schema models scope → Prop
  | .one .. => False
  | .batch _ _ (n := n) _ => 0 < n ∧ n ≤ capacity

theorem load_bounded (field : FieldId schema owner) (context : scope)
    (inputs : Vector (models owner × field.Args) size) (positive : 0 < capacity) :
    Sat (BoundedBatch capacity) (fun _ (_ : Answer app _) => True)
      (load field context inputs capacity positive) (fun _ => True) := by
  unfold load
  apply sat_bind _ _ (sat_tabulate _ (fun _ _ => True) ?_)
  · intro _ _; trivial
  · intro chunk
    exact ⟨⟨chunk_nonempty positive chunk, Nat.min_le_left _ _⟩, fun _ _ => trivial⟩

end GraphQL.Plan.Batch
