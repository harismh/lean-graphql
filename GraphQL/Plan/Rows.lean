import Std

namespace GraphQL.Plan

/-- The row index itself is provenance: both parent occurrence and filtered position. -/
abbrev RowIndex {n : Nat} (width : Fin n → Nat) := (parent : Fin n) × Fin (width parent)

structure Nested (α : Type) where
  count : Nat
  width : Fin count → Nat
  values : (parent : Fin count) → Vector α (width parent)

/-- A finite flattened family. Materialization orders indices parent-first, then position. -/
structure Gathered (α : Type) where
  count : Nat
  width : Fin count → Nat
  getValue : RowIndex width → α

def gather (rows : Nested α) : Gathered α :=
  ⟨rows.count, rows.width, fun ij => (rows.values ij.1).get ij.2⟩

def scatter (rows : Gathered α) : Nested α :=
  ⟨rows.count, rows.width, fun i => Vector.ofFn (fun j => rows.getValue ⟨i, j⟩)⟩

def Gathered.map (f : α → β) (rows : Gathered α) : Gathered β :=
  ⟨rows.count, rows.width, fun ij => f (rows.getValue ij)⟩

def Gathered.positions (rows : Gathered α) : List (RowIndex rows.width) :=
  (List.finRange rows.count).flatMap (fun i => (List.finRange (rows.width i)).map (fun j => ⟨i, j⟩))

def Gathered.materialize (rows : Gathered α) : Vector α rows.positions.length :=
  ⟨(rows.positions.map rows.getValue).toArray, by simp⟩

def Nested.toLists (rows : Nested α) : List (List α) :=
  List.ofFn (fun i => (rows.values i).toList)

def Nested.ofLists (rows : List (List α)) : Nested α :=
  ⟨rows.length, fun i => rows[i].length, fun i => ⟨rows[i].toArray, by simp⟩⟩

theorem scatter_gather (rows : Nested α) : scatter (gather rows) = rows := by
  cases rows with
  | mk count width values =>
    simp only [scatter, gather]
    congr
    funext i
    apply Vector.ext
    intro j hj
    simp [Vector.get, Fin.cast]

theorem gather_scatter (rows : Gathered α) : gather (scatter rows) = rows := by
  cases rows with
  | mk count width values =>
    simp only [gather, scatter]
    congr
    funext ij
    simp [Vector.get, Fin.cast]

theorem scatter_map_at (f : α → β) (rows : Gathered α) (i : Fin rows.count)
    (j : Fin (rows.width i)) :
    ((scatter (rows.map f)).values i).get j = f (rows.getValue ⟨i, j⟩) := by
  simp [scatter, Gathered.map, Vector.get, Fin.cast]

theorem nested_lists_roundtrip (rows : List (List α)) : (Nested.ofLists rows).toLists = rows := by
  simp [Nested.toLists, Nested.ofLists]

theorem gather_scatter_lists (rows : List (List α)) :
    (scatter (gather (Nested.ofLists rows))).toLists = rows := by
  rw [scatter_gather, nested_lists_roundtrip]

theorem materialize_length (rows : Gathered α) : rows.materialize.size = rows.positions.length := rfl

theorem materialize_at (rows : Gathered α) (i : Fin rows.positions.length) :
    rows.materialize.get i = rows.getValue rows.positions[i] := by
  simp [Gathered.materialize, Vector.get, Fin.cast]

theorem position_present (rows : Gathered α) (ij : RowIndex rows.width) :
    ij ∈ rows.positions := by
  cases ij with
  | mk i j =>
    apply List.mem_flatMap.mpr
    refine ⟨i, by simp, ?_⟩
    exact List.mem_map.mpr ⟨j, by simp, rfl⟩

/-- Two one-level gathers compose without losing either parent coordinate. -/
def flattenIndex {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (index : (i : Fin n) × (j : Fin (width i)) × Fin (inner i j)) :
    (ij : RowIndex width) × Fin (inner ij.1 ij.2) :=
  ⟨⟨index.1, index.2.1⟩, index.2.2⟩

def unflattenIndex {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (index : (ij : RowIndex width) × Fin (inner ij.1 ij.2)) :
    (i : Fin n) × (j : Fin (width i)) × Fin (inner i j) :=
  ⟨index.1.1, index.1.2, index.2⟩

theorem nested_index_roundtrip {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (index : (i : Fin n) × (j : Fin (width i)) × Fin (inner i j)) :
    unflattenIndex (flattenIndex index) = index := rfl

theorem flattened_index_roundtrip {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (index : (ij : RowIndex width) × Fin (inner ij.1 ij.2)) :
    flattenIndex (unflattenIndex index) = index := rfl

theorem materialize_scatter (rows : Gathered α) :
    rows.materialize.toList = (scatter rows).toLists.flatten := by
  simp [Gathered.materialize, Gathered.positions, scatter, Nested.toLists,
    List.finRange, List.flatMap_def, List.map_ofFn, Vector.toList_ofFn, Vector.toList,
    List.map_flatten, List.map_map, Function.comp_def]

theorem materialize_gather (rows : Nested α) :
    (gather rows).materialize.toList = rows.toLists.flatten := by
  rw [materialize_scatter, scatter_gather]

/-- Composition acts on values as well as coordinates, retaining both parent indices. -/
def gatherNested {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (values : (i : Fin n) → (j : Fin (width i)) → Vector α (inner i j))
    (index : (ij : RowIndex width) × Fin (inner ij.1 ij.2)) : α :=
  (values index.1.1 index.1.2).get index.2

def scatterNested {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (values : ((ij : RowIndex width) × Fin (inner ij.1 ij.2)) → α)
    (i : Fin n) (j : Fin (width i)) : Vector α (inner i j) :=
  Vector.ofFn (fun k => values ⟨⟨i, j⟩, k⟩)

theorem nested_values_roundtrip {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (values : (i : Fin n) → (j : Fin (width i)) → Vector α (inner i j)) :
    scatterNested (gatherNested values) = values := by
  funext i j
  apply Vector.ext
  intro k hk
  simp [scatterNested, gatherNested, Vector.get, Fin.cast]

theorem flattened_values_roundtrip {n : Nat} {width : Fin n → Nat}
    {inner : (i : Fin n) → Fin (width i) → Nat}
    (values : ((ij : RowIndex width) × Fin (inner ij.1 ij.2)) → α) :
    gatherNested (scatterNested values) = values := by
  funext index
  simp [gatherNested, scatterNested, Vector.get, Fin.cast]

theorem materialize_map (f : α → β) (rows : Gathered α) :
    (rows.map f).materialize = rows.materialize.map f := by
  apply Vector.ext
  intro i hi
  simp [Gathered.materialize, Gathered.map, Gathered.positions, List.map_map, Function.comp_def]

end GraphQL.Plan
