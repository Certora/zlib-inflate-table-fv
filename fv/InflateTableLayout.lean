/-
  Layout facts for `struct code` (`__1353`) against THIS program's composite
  environment (`Inftrees.prog.prog_comp_env`).

  Pattern: InflateMeasure.lean (export repo) — one batched `decide` per table,
  projections at use sites; `rfl` where no environment is involved.

  Also here: the `Cop.semSwitchArg` facts for the `switch (type)` scrutinee —
  three `rfl`s verifying, for the values the spec's `ty_valid` admits, that the
  selected case index is the numeral itself.
-/
import InftreesAST

open CC
open Inftrees

namespace InflateTable.Layout

/-- The composite env every layout fact is stated against. -/
abbrev cenv : CompositeEnv := Inftrees.prog.prog_comp_env

/-- The `struct code` composite, looked up once. -/
def codeCo : Composite :=
  match cenv.get __1353 with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

/-! ## Sizes, alignment, access mode -/

/-- `sizeof(struct code) = 4` — what `AssignLoc.copy` loads and stores. -/
theorem code_sizeof : sizeof cenv (Ty.Tstruct __1353 noattr) = 4 := by decide

/-- `alignofBlockcopy = 2` — `triple_assign_copy`'s alignment side conditions
    reduce to evenness of the two offsets. -/
theorem code_alignofBlockcopy :
    alignofBlockcopy cenv (Ty.Tstruct __1353 noattr) = 2 := by decide

/-- Struct assignment takes the copy path (no environment involved). -/
theorem code_accessMode : accessMode (Ty.Tstruct __1353 noattr) = .By_copy := rfl

/-- The `semAdd_ptr_int`/`idxOfs` stride for every u16 array. -/
theorem sizeof_tushort : sizeof cenv tushort = 2 := rfl

/-- The `idxOfs` stride for the `code` table (`next`, `*table`). -/
theorem sizeof_code_elem : sizeof cenv (Ty.Tstruct __1353 noattr) = 4 :=
  code_sizeof

/-! ## Field offsets, batched (InflateMeasure pattern) -/

/-- Every field offset of `struct code`, in member order:
    `op` at 0, `bits` at 1, `val` at 2 — no padding, total 4. -/
def offTable : List (Ident × CC.Z) :=
  [(_op, 0), (_bits, 1), (_val, 2)]

/-- **All three offsets in one `decide`.** -/
theorem offTable_ok : ∀ p ∈ offTable,
    fieldOffset cenv p.1 codeCo.co_members = .OK (p.2, .Full) := by
  decide

theorem op_offset :
    fieldOffset cenv _op codeCo.co_members = .OK (0, .Full) :=
  offTable_ok (_op, 0) (by decide)

theorem bits_offset :
    fieldOffset cenv _bits codeCo.co_members = .OK (1, .Full) :=
  offTable_ok (_bits, 1) (by decide)

theorem val_offset :
    fieldOffset cenv _val codeCo.co_members = .OK (2, .Full) :=
  offTable_ok (_val, 2) (by decide)

/-! ## The switch scrutinee

`Cop.semSwitchArg` at a `tint` scrutinee: for the three values `ty_valid`
admits, the selected case index is the numeral itself.  These feed
`triple_switch_const`'s `hsel` at each of the three per-type instantiations. -/

theorem semSwitchArg_zero :
    Cop.semSwitchArg (.Vint (Integers.Int.repr 0)) tint = some 0 := rfl

theorem semSwitchArg_one :
    Cop.semSwitchArg (.Vint (Integers.Int.repr 1)) tint = some 1 := rfl

theorem semSwitchArg_two :
    Cop.semSwitchArg (.Vint (Integers.Int.repr 2)) tint = some 2 := rfl

end InflateTable.Layout
