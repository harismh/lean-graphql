import GraphQL.Plan.BatchRows

namespace GraphQL.Plan.Batch
open GraphQL.Plan
variable {schema : Schema} {models : Fin schema.objectCount → Type} {scope app : Type}
variable {owner : Fin schema.objectCount} {field : FieldId schema owner}
  {adapter : Adapter schema models scope app}

/-- Every emitted chunk must satisfy compatibility; every original input has a
precondition. Reassembly preserves the postcondition at its original position. -/
theorem load_contract (contracts : Contracts schema models scope app) (field : FieldId schema owner)
    (context : scope) (inputs : Vector (models owner × field.Args) size) (positive : 0 < capacity)
    (parents : ∀ i, contracts.pre field context (inputs.get i).1 (inputs.get i).2)
    (compatible : ∀ chunk : Fin (chunks size capacity), contracts.compatible field context
      (Vector.ofFn (fun offset => inputs.get (sourceIndex positive chunk offset)))) :
    Sat contracts.Pre contracts.Post (load field context inputs capacity positive)
      (fun results => ∀ i, contracts.post field context (inputs.get i).1 (inputs.get i).2 (results i)) := by
  unfold load
  apply sat_bind _ _ (sat_tabulate _ (fun chunk answers => ∀ offset,
    contracts.post field context (inputs.get (sourceIndex positive chunk offset)).1
      (inputs.get (sourceIndex positive chunk offset)).2 (answers.get offset)) ?_)
  · intro answers valid i
    simpa only [chunk_position] using valid (group positive i) (offset positive i)
  · intro chunk
    constructor
    · exact ⟨compatible chunk, fun i => by simpa [Vector.get, Fin.cast] using parents (sourceIndex positive chunk i)⟩
    · intro answer valid i
      simpa [Vector.get, Fin.cast] using valid i

/-- Deduplicated fault answers can be reused only when the postcondition transfers
along the chosen key. Exact deterministic result equality alone is insufficient. -/
theorem wave_contract (contracts : Contracts schema models scope app)
    (eligible : Eligible adapter field) (context : scope) (inputs : List (models owner × field.Args))
    (positive : 0 < capacity)
    (parents : ∀ input ∈ inputs, contracts.pre field context input.1 input.2)
    (compatible : ∀ {n} (rows : Vector (models owner × field.Args) n), contracts.compatible field context rows)
    (reuse : ∀ left ∈ inputs, ∀ right ∈ inputs,
      eligible.key.key context left.1 left.2 = eligible.key.key context right.1 right.2 →
      ∀ answer, contracts.post field context left.1 left.2 answer → contracts.post field context right.1 right.2 answer) :
    Sat contracts.Pre contracts.Post (wave eligible context inputs capacity positive)
      (fun results => ∀ i, contracts.post field context inputs[i].1 inputs[i].2 (results i)) := by
  letI := eligible.key.equal
  unfold wave
  apply sat_bind _ _ (load_contract contracts field context _ positive ?_ (fun _ => compatible _))
  · intro answers valid i
    exact reuse _ (representative_mem _ _ _) _ (List.getElem_mem i.isLt)
      ((representative_key (fun input : models owner × field.Args => eligible.key.key context input.1 input.2) inputs _).trans (position_key _ inputs i)) _ (by
        simpa [Vector.get, Fin.cast] using valid (position _ inputs i))
  · intro i
    simpa [Vector.get, Fin.cast] using parents _ (representative_mem _ inputs i)

theorem rows_wave_contract (contracts : Contracts schema models scope app)
    (eligible : Eligible adapter field) (context : scope) (rows : Gathered (models owner × field.Args))
    (positive : 0 < capacity)
    (parents : ∀ input ∈ rowInputs rows, contracts.pre field context input.1 input.2)
    (compatible : ∀ {n} (inputs : Vector (models owner × field.Args) n), contracts.compatible field context inputs)
    (reuse : ∀ left ∈ rowInputs rows, ∀ right ∈ rowInputs rows,
      eligible.key.key context left.1 left.2 = eligible.key.key context right.1 right.2 →
      ∀ answer, contracts.post field context left.1 left.2 answer → contracts.post field context right.1 right.2 answer) :
    Sat contracts.Pre contracts.Post (rowsWave eligible context rows capacity positive)
      (fun results => ∀ i, contracts.post field context (rows.getValue i).1 (rows.getValue i).2 (results i)) := by
  unfold rowsWave
  apply sat_bind _ _ (wave_contract contracts eligible context (rowInputs rows) positive parents compatible reuse)
  intro answers valid i
  simpa [rowInputs, rowPosition] using valid ⟨(rowPosition rows i).val, by simpa [rowInputs] using (rowPosition rows i).isLt⟩

end GraphQL.Plan.Batch
