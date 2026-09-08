/-
  The body of `inflate_table`, segment by segment.

  This file works through the generated AST (InftreesAST.lean:444-1545) in
  source order, one triple per segment, in the style of the export repo's
  `U16LoopSep.lean` (the acceptance test that is literally this function's
  first loop).  Segments carry the SMALLEST heap footprint they touch; the
  full-footprint assembly (framing `preHeap`'s other components around each
  segment) is InflateTableChain.lean's job.  Each `§n` section header below
  names its segment and the inftrees.c lines it covers; §27's `body_matches`
  pins the reassembled body to the generated AST by `rfl`.
-/
import InflateTableSpec
import InflateTableLayout
import InflateTableInvariants

open CC CC.Sep CC.HProp
open Inftrees

set_option maxRecDepth 20000

namespace InflateTable.Body

/-! ## §0 Bridges

Every operator this function applies is computable on `Vint` arguments, so
these are `rfl` — stated once so proofs downstream never unfold `Cop`. -/

/-- 32-bit unsigned less-than against `Nat`s (the `u32` analogue of `u64_ltu`;
    only `cmpu_eq_nat32` existed at 32 bits). -/
theorem ltu_nat32 (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    Integers.Int.ltu (Integers.Int.repr ((a : _root_.Int)))
      (Integers.Int.repr ((b : _root_.Int))) = decide (a < b) := by
  show BitVec.ult _ _ = _
  rw [BitVec.ult]
  simp only [u32_toNat_repr, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- No-wrap bound for a smaller index, at an abstract base offset.

    NOTE the proof shape: `omega` silently drops any hypothesis or goal whose
    operators were elaborated at the `CC.Z` abbrev (it matches `Int`
    syntactically), and `Ptrofs.unsigned` returns `CC.Z` — so the offset atom
    is renamed to an `_root_.Int` variable and both sides re-elaborated before
    `omega` runs.  Every no-wrap fact at a caller-supplied offset needs this
    lemma (or this dance). -/
theorem no_wrap_mono (o : Integers.Ptrofs) (a b : Nat)
    (h : Integers.Ptrofs.unsigned o + 2 * (a : _root_.Int)
           < 18446744073709551616)
    (hba : b ≤ a) :
    Integers.Ptrofs.unsigned o + 2 * (b : _root_.Int)
      < 18446744073709551616 := by
  obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned o = A := ⟨_, rfl⟩
  rw [hA] at h ⊢
  have h2 : A + 2 * ((a : Nat) : _root_.Int)
      < (18446744073709551616 : _root_.Int) := h
  show A + 2 * ((b : Nat) : _root_.Int) < (18446744073709551616 : _root_.Int)
  omega

/-- The value of `(void *) 0` on this 64-bit target. -/
abbrev nullv : Val := .Vlong (Integers.Int64.repr 0)

theorem semCast_null (m : Mem) :
    Cop.semCast (.Vint (Integers.Int.repr 0)) tint (tptr tvoid) m = some nullv := rfl

/-- `x <= c` at `(tuint, tint)`: the usual arithmetic conversions make it an
    unsigned comparison. -/
theorem semBinop_le_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Ole (.Vint x) tuint (.Vint c) tint m
      = some (Val.ofBool (!Integers.Int.ltu c x)) := rfl

/-- `x < y` at `(tuint, tuint)`. -/
theorem semBinop_lt_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Olt (.Vint x) tuint (.Vint y) tuint m
      = some (Val.ofBool (Integers.Int.ltu x y)) := rfl

/-- `x >= c` at `(tuint, tint)`. -/
theorem semBinop_ge_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oge (.Vint x) tuint (.Vint c) tint m
      = some (Val.ofBool (!Integers.Int.ltu x c)) := rfl

/-- `x != c` at `(tushort, tint)`: integer promotion, then a signed compare. -/
theorem semBinop_ne_ushort_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .One (.Vint x) tushort (.Vint c) tint m
      = some (Val.ofBool (!(Integers.Int.eq x c))) := rfl

/-- `x + c` at `(tuint, tint) → tuint`. -/
theorem semBinop_add_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tuint (.Vint c) tint m
      = some (.Vint (Integers.Int.add x c)) := rfl

/-- `x - c` at `(tuint, tint) → tuint`. -/
theorem semBinop_sub_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vint x) tuint (.Vint c) tint m
      = some (.Vint (Integers.Int.sub x c)) := rfl

/-- `x + c` at `(tushort, tint) → tint` (integer promotion). -/
theorem semBinop_add_ushort_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tushort (.Vint c) tint m
      = some (.Vint (Integers.Int.add x c)) := rfl

/-- `x + y` at `(tushort, tushort) → tint` (both promote). -/
theorem semBinop_add_ushort_ushort (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tushort (.Vint y) tushort m
      = some (.Vint (Integers.Int.add x y)) := rfl

/-- Storing a `tint` value into a `tushort` cell zero-extends to 16 bits. -/
theorem semCast_int_ushort (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tint tushort m
      = some (.Vint (Integers.Int.zero_ext 16 x)) := rfl

theorem tushort_byvalue : accessMode tushort = .By_value .Mint16unsigned := rfl

/-- `count[len]` with a `tuint` index: array base decays, index is Unsigned. -/
theorem classify_count_uint :
    Cop.classifyAdd (typeof (.Evar _count (tarray tushort 16)))
      (typeof (.Etempvar _len tuint)) = .pi tushort .Unsigned := rfl

/-! ### Hoisting existentials out of an assertion

`anyBytes` — and therefore `codeRegion`, and `postHeap`'s three write slots —
is an existential over byte runs, but `Sep.triple_exists` peels an existential
only at the **top** of an `Assn`.  These three lemmas move one out from under a
`∗` and out of a `LocalSt`, which is what every carve of the table region needs
in InflateTableChain.lean.  Stated as equalities so they can be `rw`n under
anything. -/

theorem sep_hexists_l {α : Sort u} (f : α → HProp) (Q : HProp) :
    hexists f ∗ Q = hexists (fun x => f x ∗ Q) := by
  funext h
  refine propext ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨h1, h2, hd, heq, hf, hq⟩ := hs
    obtain ⟨x, hf⟩ := hf
    exact ⟨x, h1, h2, hd, heq, hf, hq⟩
  · obtain ⟨x, h1, h2, hd, heq, hf, hq⟩ := hs
    exact ⟨h1, h2, hd, heq, ⟨x, hf⟩, hq⟩

theorem sep_hexists_r {α : Sort u} (P : HProp) (f : α → HProp) :
    P ∗ hexists f = hexists (fun x => P ∗ f x) := by
  funext h
  refine propext ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨h1, h2, hd, heq, hp, hf⟩ := hs
    obtain ⟨x, hf⟩ := hf
    exact ⟨x, h1, h2, hd, heq, hp, hf⟩
  · obtain ⟨x, h1, h2, hd, heq, hp, hf⟩ := hs
    exact ⟨h1, h2, hd, heq, hp, ⟨x, hf⟩⟩

/-! The third member of this family, `localst_hexists`, is stated in §16 where
the table-region cells are introduced. -/

/-! ## §1 Environment and temporaries

`FunctionEntry2` allocates the three fn_vars in order and binds the six
parameters as temporaries.  `bh`/`bc`/`bo` are the fresh blocks of `here`,
`count`, `offs`. -/

abbrev envOf (bh bc bo : Block) : Env :=
  ((emptyEnv.set _here (bh, Ty.Tstruct __1353 noattr)).set _count
      (bc, tarray tushort 16)).set _offs (bo, tarray tushort 16)

theorem envOf_here (bh bc bo : Block) :
    (envOf bh bc bo).get _here = some (bh, Ty.Tstruct __1353 noattr) := rfl

theorem envOf_count (bh bc bo : Block) :
    (envOf bh bc bo).get _count = some (bc, tarray tushort 16) := rfl

theorem envOf_offs (bh bc bo : Block) :
    (envOf bh bc bo).get _offs = some (bo, tarray tushort 16) := rfl

/-- The six parameters, live for the whole function. -/
abbrev paramTemps (L : Layout) (ty : _root_.Int) (codes : Nat) :
    List (Ident × Val) :=
  [(_type, .Vint (Integers.Int.repr ty)),
   (_lens, .Vptr L.lensB L.lensO),
   (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))),
   (_table, .Vptr L.tblB L.tblO),
   (_bits, .Vptr L.bitsB L.bitsO),
   (_work, .Vptr L.workB L.workO)]

/-- The parameters **plus the two loop temporaries the main loop's invariant
    tracks**.  `TLoop` carries `(_incr, vi)` and `(_fill, vf)`, so they have to
    be in the tracked list from entry onwards — `bindParameterTemps` leaves both
    at `.Vundef` (verified by `rfl` in `Entry.entry_facts`), which is exactly
    why `LoopSt.vi`/`vf` are arbitrary `Val`s. -/
abbrev entryTemps (L : Layout) (ty : _root_.Int) (codes : Nat) :
    List (Ident × Val) :=
  (_incr, .Vundef) :: (_fill, .Vundef) :: paramTemps L ty codes

/-- The tracked list after the prologue (`base`, `extra`, `match` set). -/
abbrev T0 (L : Layout) (ty : _root_.Int) (codes : Nat) : List (Ident × Val) :=
  (_match, .Vint (Integers.Int.repr 0)) :: (_extra, nullv) :: (_base, nullv)
    :: entryTemps L ty codes

/-- The count-array base: an array-typed `Evar` decays to its own address. -/
theorem eval_count_base {ge : CGenv} {le : TempEnv} {m : Mem}
    (bh bc bo : Block) :
    EvalExpr ge (envOf bh bc bo) le m (.Evar _count (tarray tushort 16))
      (.Vptr bc Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ bc Integers.Ptrofs.zero .Full _
    (eval_var_local (envOf_count bh bc bo)) (DerefLoc.reference (by decide))

/-! ## §2 The prologue (InftreesAST.lean:445-452)

Three `Sset`s; the heap is untouched, so `H` stays generic and these lemmas
serve any ambient footprint. -/

/-- `id = (void *) 0;` — used twice (`base`, `extra`). -/
theorem set_null_triple (ge : CGenv) (fe : EntryRel) (E : Env)
    (l : List (Ident × Val)) (H : HProp) (id : Ident)
    (hne : ∀ p ∈ l, p.1 ≠ id) :
    Triple ge fe f_inflate_table (LocalSt E l H)
      (.Sset id (.Ecast (.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))
      (.only (LocalSt E ((id, nullv) :: l) H)) :=
  triple_set_local ge fe f_inflate_table E l l H id _ nullv
    (fun _ hp => hp) hne
    (fun _ m _ _ _ _ =>
      EvalExpr.Ecast _ _ (.Vint (Integers.Int.repr 0)) _
        (EvalExpr.Econst_int _ _) (semCast_null m))

/-- `id = c;` for an integer constant — used for `match = 0`, `len = 0`,
    `sym = 0`, `max = 15`, and every other counter initialization. -/
theorem set_const_triple (ge : CGenv) (fe : EntryRel) (E : Env)
    (l : List (Ident × Val)) (H : HProp) (id : Ident) (c : _root_.Int)
    (hne : ∀ p ∈ l, p.1 ≠ id) :
    Triple ge fe f_inflate_table (LocalSt E l H)
      (.Sset id (.Econst_int (Integers.Int.repr c) tint))
      (.only (LocalSt E ((id, .Vint (Integers.Int.repr c)) :: l) H)) :=
  triple_set_local ge fe f_inflate_table E l l H id _ _
    (fun _ hp => hp) hne
    (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)

/-! ## §3 Loop 1 — zero `count[0..15]` (inftrees.c:116-117; AST 453-471)

Port of the export repo's `U16LoopSep`, with three deltas: the enclosing
environment has three locals, the index temporary `_len` is `tuint` (so the
guard is an unsigned comparison and the address signedness is `.Unsigned`),
and the tracked-temporaries list carries an abstract ambient tail `T` (the
prologue's `base`/`extra`/`match` plus the six parameters) that must survive
the loop for the segments after it. -/

/-- `k` cells of `count` written, the rest still undefined. -/
abbrev Hcnt (bc : Block) (k : Nat) : HProp :=
  arrayU16 .Freeable bc 0 k (fun _ => 0)
  ∗ undefBytes .Freeable bc (2 * (k : _root_.Int)) (32 - 2 * k)

abbrev guard1 : Expr :=
  .Ebinop .Ole (.Etempvar _len tuint) (.Econst_int (Integers.Int.repr 15) tint) tint

abbrev assign1 : Stmt :=
  .Sassign
    (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
      (.Etempvar _len tuint) (tptr tushort)) tushort)
    (.Econst_int (Integers.Int.repr 0) tint)

abbrev incr1 : Stmt :=
  .Sset _len (.Ebinop .Oadd (.Etempvar _len tuint)
    (.Econst_int (Integers.Int.repr 1) tint) tuint)

abbrev loop1 : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse guard1 .Sskip .Sbreak) assign1) incr1

/-- The guard, at any `len ≤ 16`: true exactly while `len ≤ 15`.  Unsigned
    comparison, unlike the template's signed one. -/
theorem guard1_eval {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} (k : Nat)
    (hk : k ≤ 16)
    (hlen : le.get _len = some (.Vint (Integers.Int.repr ((k : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m guard1 v
      ∧ Cop.boolVal v (typeof guard1) m = some (decide (k ≤ 15)) := by
  refine ⟨Val.ofBool (!Integers.Int.ltu (Integers.Int.repr 15)
            (Integers.Int.repr ((k : _root_.Int)))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Ole _ _ _ (.Vint (Integers.Int.repr ((k : _root_.Int))))
      (.Vint (Integers.Int.repr 15)) _
      (EvalExpr.Etempvar _len tuint _ hlen) (EvalExpr.Econst_int _ _)
      (semBinop_le_uint_int _ _ _ _)
  · simp only [typeof, boolVal_ofBool_int]
    rw [show (15 : _root_.Int) = ((15 : Nat) : _root_.Int) from rfl,
        ltu_nat32 15 k (by omega) (by omega)]
    by_cases h : k ≤ 15
    · simp only [h, decide_true]
      rw [show decide (15 < k) = false from by
            rw [decide_eq_false_iff_not]; omega]
      rfl
    · simp only [h, decide_false]
      rw [show decide (15 < k) = true from by
            rw [decide_eq_true_eq]; omega]
      rfl

/-- One iteration's write, `count[len] = 0` at `len = k`. -/
theorem write1_step (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
    (T : List (Ident × Val)) (k : Nat) (hk : k < 16) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_len, .Vint (Integers.Int.repr ((k : _root_.Int)))) :: T) (Hcnt bc k))
      assign1
      (.only (LocalSt (envOf bh bc bo)
        ((_len, .Vint (Integers.Int.repr ((k : _root_.Int)))) :: T)
        (Hcnt bc (k + 1)))) := by
  have haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
        (Integers.Int.repr ((k : _root_.Int)))) = 2 * (k : _root_.Int) := by
    rw [u16Ofs_unsigned ge.genv_cenv .Unsigned Integers.Ptrofs.zero k (by omega)
          (by rw [ptrofs_unsigned_zero]
              show (0 : _root_.Int) + 2 * (k : _root_.Int) < 18446744073709551616
              omega),
        ptrofs_unsigned_zero]
    show (0 : _root_.Int) + 2 * (k : _root_.Int) = 2 * (k : _root_.Int)
    omega
  have hsuf : (32 - 2 * k) = 2 * ((15 - k) + 1) := by omega
  have hpeel : undefBytes .Freeable bc (2 * (k : _root_.Int)) (32 - 2 * k)
      = mapsto .Mint16unsigned .Freeable bc (2 * (k : _root_.Int)) .Vundef
        ∗ undefBytes .Freeable bc (2 * (k : _root_.Int) + 2) (2 * (15 - k)) := by
    rw [hsuf, undefBytes_uncons_u16 .Freeable bc (2 * (k : _root_.Int)) (15 - k)
          (by omega)]
  refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint16unsigned .Freeable bc
    (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
      (Integers.Int.repr ((k : _root_.Int))))
    (by decide) (by simpa only [typeof] using tushort_byvalue) ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  rw [show Hcnt bc k
         = mapsto .Mint16unsigned .Freeable bc (2 * (k : _root_.Int)) .Vundef
           ∗ (arrayU16 .Freeable bc 0 k (fun _ => 0)
              ∗ undefBytes .Freeable bc (2 * (k : _root_.Int) + 2) (2 * (15 - k)))
       from by
        show arrayU16 .Freeable bc 0 k (fun _ => 0)
              ∗ undefBytes .Freeable bc (2 * (k : _root_.Int)) (32 - 2 * k) = _
        rw [hpeel, sep_left_comm_eq]] at hH
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨.Vundef, .Vint (Integers.Int.repr 0), h1, h2, hd12, heq, ?_, ?_, ?_, ?_⟩
  · rw [haddr]; exact hm1
  · exact eval_index_lvalue (eval_count_base bh bc bo)
      (EvalExpr.Etempvar _len tuint _ (hT.get List.mem_cons_self))
      classify_count_uint
  · exact ⟨.Vint (Integers.Int.repr 0), EvalExpr.Econst_int _ _, rfl⟩
  · intro h1' hm1' hd1'
    refine ⟨rfl, hT, ?_⟩
    show Hcnt bc (k + 1) (Heap.union h1' h2)
    have hgrow : mapsto .Mint16unsigned .Freeable bc (2 * (k : _root_.Int))
                     (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))))
                   ∗ (arrayU16 .Freeable bc 0 k (fun _ => 0)
                      ∗ undefBytes .Freeable bc (2 * (k : _root_.Int) + 2)
                          (2 * (15 - k)))
                 = Hcnt bc (k + 1) := by
      have hsnoc := arrayU16_snoc .Freeable bc 0 k (fun _ => 0) 0
      rw [show (0 : _root_.Int) + 2 * (k : _root_.Int) = 2 * (k : _root_.Int)
            from by omega] at hsnoc
      rw [sep_left_comm_eq, ← sep_assoc_eq, hsnoc]
      show arrayU16 .Freeable bc 0 (k + 1) (fun j => if j = k then 0 else 0)
            ∗ undefBytes .Freeable bc (2 * (k : _root_.Int) + 2) (2 * (15 - k))
           = _
      rw [show (fun j : Nat => if j = k then (0 : Nat) else 0) = (fun _ => 0) from by
            funext j; simp,
          show 2 * (k : _root_.Int) + 2 = 2 * ((k + 1 : Nat) : _root_.Int) from by
            omega,
          show 2 * (15 - k) = 32 - 2 * (k + 1) from by omega]
    rw [← hgrow]
    refine ⟨h1', h2, hd1', rfl, ?_, hrest⟩
    rw [haddr] at hm1'
    exact hm1'

/-! ### Loop 1, assembled -/

/-- Measure `n` = iterations left; `16 - n` cells written. -/
def Inv1 (bh bc bo : Block) (T : List (Ident × Val)) (n : Nat) : Sep.Assn :=
  fun e le hp =>
    ∃ _ : n ≤ 16,
      LocalSt (envOf bh bc bo)
        ((_len, .Vint (Integers.Int.repr (((16 - n : Nat) : _root_.Int)))) :: T)
        (Hcnt bc (16 - n)) e le hp

def JAssn1 (bh bc bo : Block) (T : List (Ident × Val)) (n : Nat) : Sep.Assn :=
  fun e le hp =>
    ∃ m, ∃ _ : n = m + 1, ∃ _ : m ≤ 15,
      LocalSt (envOf bh bc bo)
        ((_len, .Vint (Integers.Int.repr (((15 - m : Nat) : _root_.Int)))) :: T)
        (Hcnt bc (16 - m)) e le hp

/-- Exit state: all sixteen cells zeroed, `len = 16`, ambient temps intact. -/
def Post1 (bh bc bo : Block) (T : List (Ident × Val)) : Sep.Assn :=
  LocalSt (envOf bh bc bo)
    ((_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int)))) :: T)
    (Hcnt bc 16)

theorem body1_triple (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
    (T : List (Ident × Val)) (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (Inv1 bh bc bo T n)
      (.Ssequence (.Sifthenelse guard1 .Sskip .Sbreak) assign1)
      { normal := JAssn1 bh bc bo T n, brk := Post1 bh bc bo T,
        cont := JAssn1 bh bc bo T n, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hn : n ≤ 16) => ?_)
  match n with
  | 0 =>
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT _ _ => ?_) ?_
      · have h := guard1_eval (ge := ge) (e := envOf bh bc bo) (m := mm) 16
          (by omega) (hT.get List.mem_cons_self)
        simpa using h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        exact hx
  | m + 1 =>
      have hk : 15 - m < 16 := by omega
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_len, .Vint (Integers.Int.repr (((15 - m : Nat) : _root_.Int)))) :: T)
          (Hcnt bc (15 - m))) _ _ _ ?_ ?_
      · rw [show (16 : Nat) - (m + 1) = 15 - m from by omega]
        refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        have h := guard1_eval (ge := ge) (e := envOf bh bc bo) (m := mm) (15 - m)
          (by omega) (hT.get List.mem_cons_self)
        simpa using h
      · refine triple_conseq ge fe f_inflate_table
          (write1_step ge fe bh bc bo T (15 - m) hk)
          (fun e le hp x => x) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        refine ⟨m, rfl, by omega, ?_⟩
        rw [show 15 - m + 1 = 16 - m from by omega] at hx
        exact hx

theorem incr1_triple (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
    (T : List (Ident × Val)) (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (JAssn1 bh bc bo T n) incr1
      { normal := fun e le hp => ∃ n', n' < n ∧ Inv1 bh bc bo T n' e le hp,
        brk := Post1 bh bc bo T, cont := Assn.no, ret := R.ret,
        goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (m : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnm : n = m + 1) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hm15 : m ≤ 15) => ?_)
  subst hnm
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T _ _len _
      (.Vint (Integers.Int.repr (((16 - m : Nat) : _root_.Int))))
      (fun p hp => List.mem_cons_of_mem _ hp) hTlen
      (fun le mm hp hT _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr (((15 - m : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _len tuint _ (hT.get List.mem_cons_self))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_uint_int]
    show some (Val.Vint (Integers.Int.add
              (Integers.Int.repr (((15 - m : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_add, show 15 - m + 1 = 16 - m from by omega]
  · exact ⟨m, by omega, by omega, hx.1, hx.2.1, hx.2.2⟩

/-- **Loop 1.**  From nothing written to all sixteen `count` cells zeroed,
    the ambient temporaries carried through untouched. -/
theorem loop1_triple (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
    (T : List (Ident × Val)) (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (Inv1 bh bc bo T 16) loop1
      { normal := Post1 bh bc bo T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _ (Inv1 bh bc bo T) (JAssn1 bh bc bo T) _ _
    (body1_triple ge fe bh bc bo T _) (incr1_triple ge fe bh bc bo T hTlen _) 16

/-- **Segment 1** = `len = 0;` + loop 1, from the fresh (undefined) `count`
    block to the zeroed array. -/
theorem seg1_triple (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
    (T : List (Ident × Val)) (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T (undefBytes .Freeable bc 0 32))
      (.Ssequence (.Sset _len (.Econst_int (Integers.Int.repr 0) tint)) loop1)
      { normal := Post1 bh bc bo T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _ (Inv1 bh bc bo T 16) _ _ _ ?_
    (loop1_triple ge fe bh bc bo T hTlen R)
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) T (undefBytes .Freeable bc 0 32)
      _len 0 hTlen)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT, hu⟩ := hx
  refine ⟨Nat.le_refl 16, henv, ?_, ?_⟩
  · simpa using hT
  · show Hcnt bc 0 hp
    show (arrayU16 .Freeable bc 0 0 (fun _ => 0)
          ∗ undefBytes .Freeable bc (2 * ((0 : Nat) : _root_.Int)) (32 - 2 * 0)) hp
    rw [show arrayU16 .Freeable bc 0 0 (fun _ => 0) = emp from rfl, emp_sep_eq,
        show (2 : _root_.Int) * ((0 : Nat) : _root_.Int) = 0 from by omega]
    simpa using hu

/-! ## §4 Loop 2 — count the lengths (inftrees.c:118-119; AST 473-512)

`for (sym = 0; sym < codes; sym++) count[lens[sym]]++;`

clightgen normalizes the increment into two reads of `lens[sym]` (`_t'34`,
`_t'35` — same cell, no store between, so same value), a read of
`count[lens[sym]]` (`_t'36`), and the store.  The invariant ties the `count`
array's contents to the model: after `s` symbols, cell `l` holds
`Model.count lensF s l`. -/

open InflateTable.Model in
/-- The counting loop's footprint: the (read-only) `lens` array and the
    `count` local holding the model counts of the first `s` symbols. -/
abbrev Hc2 (pl : Permission) (lensB : Block) (lensO : Integers.Ptrofs)
    (codes : Nat) (lensF : Nat → Nat) (bc : Block) (s : Nat) : HProp :=
  arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
  ∗ arrayU16 .Freeable bc 0 16 (fun l => count lensF s l)

abbrev guard2 : Expr :=
  .Ebinop .Olt (.Etempvar _sym tuint) (.Etempvar _codes tuint) tint

abbrev readLens (dst : Ident) : Stmt :=
  .Sset dst (.Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
    (.Etempvar _sym tuint) (tptr tushort)) tushort)

abbrev readCnt : Stmt :=
  .Sset _t'36 (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
    (.Etempvar _t'35 tushort) (tptr tushort)) tushort)

abbrev assign2 : Stmt :=
  .Sassign
    (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
      (.Etempvar _t'34 tushort) (tptr tushort)) tushort)
    (.Ebinop .Oadd (.Etempvar _t'36 tushort)
      (.Econst_int (Integers.Int.repr 1) tint) tint)

abbrev iter2 : Stmt :=
  .Ssequence (readLens _t'34) (.Ssequence (readLens _t'35)
    (.Ssequence readCnt assign2))

abbrev incr2 : Stmt :=
  .Sset _sym (.Ebinop .Oadd (.Etempvar _sym tuint)
    (.Econst_int (Integers.Int.repr 1) tint) tuint)

abbrev loop2 : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse guard2 .Sskip .Sbreak) iter2) incr2

section Loop2

open InflateTable.Model

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (pl : Permission) (lensB : Block) (lensO : Integers.Ptrofs)
variable (codes : Nat) (lensF : Nat → Nat)
variable (T : List (Ident × Val))

/-- The guard `sym < codes`, decided by the tracked values. -/
theorem guard2_eval {e : Env} {le : TempEnv} {m : Mem} (s : Nat)
    (hs16 : s < 65536) (hc16 : codes < 65536)
    (hsym : le.get _sym = some (.Vint (Integers.Int.repr ((s : _root_.Int)))))
    (hcod : le.get _codes
      = some (.Vint (Integers.Int.repr ((codes : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m guard2 v
      ∧ Cop.boolVal v (typeof guard2) m = some (decide (s < codes)) := by
  refine ⟨Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((s : _root_.Int)))
            (Integers.Int.repr ((codes : _root_.Int)))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Olt _ _ _
      (.Vint (Integers.Int.repr ((s : _root_.Int))))
      (.Vint (Integers.Int.repr ((codes : _root_.Int)))) _
      (EvalExpr.Etempvar _sym tuint _ hsym)
      (EvalExpr.Etempvar _codes tuint _ hcod)
      (semBinop_lt_uint _ _ _ _)
  · simp only [typeof, boolVal_ofBool_int]
    rw [ltu_nat32 s codes (by omega) (by omega)]

/-- **One iteration**: the two `lens[sym]` reads, the `count[…]` read, and the
    increment write.  From counts-of-`s` to counts-of-`s+1`. -/
theorem iter2_step
    (hpl : permOrder pl .Readable = true)
    (hb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hmemL : (_lens, .Vptr lensB lensO) ∈ T)
    (hT : ∀ p ∈ T, p.1 ≠ _t'34 ∧ p.1 ≠ _t'35 ∧ p.1 ≠ _t'36)
    (s : Nat) (hs : s < codes) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_sym, .Vint (Integers.Int.repr ((s : _root_.Int)))) :: T)
        (Hc2 pl lensB lensO codes lensF bc s))
      iter2
      (.only (LocalSt (envOf bh bc bo)
        ((_t'36, .Vint (Integers.Int.repr
            ((count lensF s (lensF s) : Nat))))
          :: (_t'35, .Vint (Integers.Int.repr ((lensF s : Nat))))
          :: (_t'34, .Vint (Integers.Int.repr ((lensF s : Nat))))
          :: (_sym, .Vint (Integers.Int.repr ((s : _root_.Int)))) :: T)
        (Hc2 pl lensB lensO codes lensF bc (s + 1)))) := by
  -- shared address facts
  have haddrL : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Unsigned lensO
        (Integers.Int.repr ((s : _root_.Int))))
      = Integers.Ptrofs.unsigned lensO + 2 * (s : _root_.Int) :=
    u16Ofs_unsigned ge.genv_cenv .Unsigned lensO s (by omega)
      (no_wrap_mono lensO codes s hnoL (by omega))
  have hi16 : lensF s < 16 := by have := hlens15 s hs; omega
  -- the count-cell address, in the raw shape `eval_index_u16` consumes …
  have haddrC0 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
        (Integers.Int.repr ((lensF s : Nat))))
      = Integers.Ptrofs.unsigned Integers.Ptrofs.zero
          + 2 * ((lensF s : Nat) : _root_.Int) :=
    u16Ofs_unsigned ge.genv_cenv .Signed Integers.Ptrofs.zero (lensF s)
      (by omega)
      (by rw [ptrofs_unsigned_zero]
          show (0 : _root_.Int) + 2 * ((lensF s : Nat) : _root_.Int)
                < 18446744073709551616
          omega)
  -- … and normalized for the split/update rewrites
  have haddrC : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
        (Integers.Int.repr ((lensF s : Nat))))
      = 2 * ((lensF s : Nat) : _root_.Int) := by
    rw [haddrC0, ptrofs_unsigned_zero]
    show (0 : _root_.Int) + 2 * ((lensF s : Nat) : _root_.Int) = _
    omega
  have hcb : ∀ j, count lensF s j < 65536 :=
    fun j => Nat.lt_of_le_of_lt (count_le lensF s j) (by omega)
  -- the value of `lens[sym]`, read twice into _t'34 and _t'35
  have hreadL : ∀ (dst : Ident) (l₀ : List (Ident × Val)) (le : TempEnv)
      (m : Mem) (hp : Heap),
      TempsHold l₀ le → ((_lens, .Vptr lensB lensO) ∈ l₀) →
      ((_sym, .Vint (Integers.Int.repr ((s : _root_.Int)))) ∈ l₀) →
      Hc2 pl lensB lensO codes lensF bc s hp → Heap.Agrees hp m →
      EvalExpr ge (envOf bh bc bo) le m
        (.Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
          (.Etempvar _sym tuint) (tptr tushort)) tushort)
        (.Vint (Integers.Int.repr ((lensF s : Nat)))) := by
    intro dst l0 le m hp hT' hmL hmS hH hag
    obtain ⟨hL, hC, hd, heq, harrL, harrC⟩ := hH
    subst heq
    exact eval_index_u16 hpl harrL (Heap.Agrees_union_left hag) hs hb
      (EvalExpr.Etempvar _lens _ _ (hT'.get hmL))
      (EvalExpr.Etempvar _sym tuint _ (hT'.get hmS)) rfl haddrL
  -- ── _t'34 = lens[sym] ─────────────────────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'34 _
      (.Vint (Integers.Int.repr ((lensF s : Nat))))
      (fun p hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _sym ≠ _t'34; decide
        · exact (hT p hp2).1)
      (fun le m hp hT' hH hag =>
        hreadL _t'34 _ le m hp hT' (List.mem_cons_of_mem _ hmemL)
          List.mem_cons_self hH hag)) ?_
  -- ── _t'35 = lens[sym] ─────────────────────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'35 _
      (.Vint (Integers.Int.repr ((lensF s : Nat))))
      (fun p hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _t'34 ≠ _t'35; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _sym ≠ _t'35; decide
        · exact (hT p hp3).2.1)
      (fun le m hp hT' hH hag =>
        hreadL _t'35 _ le m hp hT'
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemL))
          (List.mem_cons_of_mem _ List.mem_cons_self) hH hag)) ?_
  -- ── _t'36 = count[_t'35] ──────────────────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'36 _
      (.Vint (Integers.Int.repr ((count lensF s (lensF s) : Nat))))
      (fun p hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _t'35 ≠ _t'36; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _t'34 ≠ _t'36; decide
        rcases List.mem_cons.mp hp3 with rfl | hp4
        · show _sym ≠ _t'36; decide
        · exact (hT p hp4).2.2)
      (fun le m hp hT' hH hag => ?_)) ?_
  · obtain ⟨hL, hC, hd, heq, harrL, harrC⟩ := hH
    subst heq
    exact eval_index_u16 (by decide) harrC (Heap.Agrees_union_right hd hag)
      hi16 hcb (eval_count_base bh bc bo)
      (EvalExpr.Etempvar _t'35 tushort _ (hT'.get List.mem_cons_self))
      rfl haddrC0
  -- ── count[_t'34] = _t'36 + 1 ──────────────────────────────────────────────
  have hcnew : count lensF s (lensF s) + 1 < 65536 := by
    have := count_le lensF s (lensF s); omega
  have hsplit := arrayU16_split .Freeable bc 0 16
    (fun l => count lensF s l) (lensF s) hi16
  rw [show (0 : _root_.Int) + 2 * ((lensF s : Nat) : _root_.Int)
        = 2 * ((lensF s : Nat) : _root_.Int) from by omega] at hsplit
  have hupd := arrayU16_update .Freeable bc 0 16
    (fun l => count lensF s l) (lensF s) (count lensF s (lensF s) + 1) hi16
  rw [show (0 : _root_.Int) + 2 * ((lensF s : Nat) : _root_.Int)
        = 2 * ((lensF s : Nat) : _root_.Int) from by omega] at hupd
  refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint16unsigned .Freeable bc
    (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
      (Integers.Int.repr ((lensF s : Nat))))
    (by decide) (by simpa only [typeof] using tushort_byvalue) ?_
  intro e le hp m hP hag
  obtain ⟨henv, hT', hH⟩ := hP
  subst henv
  rw [show Hc2 pl lensB lensO codes lensF bc s
        = mapsto .Mint16unsigned .Freeable bc
            (2 * ((lensF s : Nat) : _root_.Int))
            (.Vint (Integers.Int.repr ((count lensF s (lensF s) : Nat))))
          ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
             ∗ arrayOfRest (u16elt .Freeable bc (fun l => count lensF s l))
                 2 0 16 (lensF s))
      from by
        show arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
              ∗ arrayU16 .Freeable bc 0 16 (fun l => count lensF s l) = _
        rw [hsplit, sep_left_comm_eq]] at hH
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨.Vint (Integers.Int.repr ((count lensF s (lensF s) : Nat))),
          .Vint (Integers.Int.repr ((count lensF s (lensF s) + 1 : Nat))),
          h1, h2, hd12, heq, ?_, ?_, ?_, ?_⟩
  · rw [haddrC]; exact hm1
  · exact eval_index_lvalue (eval_count_base bh bc bo)
      (EvalExpr.Etempvar _t'34 tushort _
        (hT'.get (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))) rfl
  · -- `_t'36 + 1`, then the store's `tint → tushort` cast
    refine ⟨.Vint (Integers.Int.add
              (Integers.Int.repr ((count lensF s (lensF s) : Nat)))
              (Integers.Int.repr 1)), ?_, ?_⟩
    · refine EvalExpr.Ebinop .Oadd _ _ _ _ (.Vint (Integers.Int.repr 1)) _
        (EvalExpr.Etempvar _t'36 tushort _ (hT'.get List.mem_cons_self))
        (EvalExpr.Econst_int _ _) ?_
      simp only [typeof]
      exact semBinop_add_ushort_int _ _ _ _
    · simp only [typeof]
      rw [semCast_int_ushort]
      show some (Val.Vint (Integers.Int.zero_ext 16 (Integers.Int.add
        (Integers.Int.repr ((count lensF s (lensF s) : Nat)))
        (Integers.Int.repr (((1 : Nat) : _root_.Int)))))) = _
      rw [u32_add, zero_ext16_repr _ hcnew]
  · intro h1' hm1' hd1'
    refine ⟨rfl, hT', ?_⟩
    show Hc2 pl lensB lensO codes lensF bc (s + 1) (Heap.union h1' h2)
    have hgrow : mapsto .Mint16unsigned .Freeable bc
            (2 * ((lensF s : Nat) : _root_.Int))
            (.Vint (Integers.Int.repr ((count lensF s (lensF s) + 1 : Nat))))
          ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
             ∗ arrayOfRest (u16elt .Freeable bc (fun l => count lensF s l))
                 2 0 16 (lensF s))
        = Hc2 pl lensB lensO codes lensF bc (s + 1) := by
      rw [sep_left_comm_eq, ← hupd, count_update_fun]
    rw [← hgrow]
    refine ⟨h1', h2, hd1', rfl, ?_, hrest⟩
    rw [haddrC] at hm1'
    exact hm1'

/-! ### The counting loop, assembled -/

/-- Measure `n` = symbols still to count; `codes - n` already counted. -/
def Inv2 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ _ : n ≤ codes,
    LocalSt (envOf bh bc bo)
      ((_sym, .Vint (Integers.Int.repr (((codes - n : Nat) : _root_.Int)))) :: T)
      (Hc2 pl lensB lensO codes lensF bc (codes - n)) e le hp

def JAssn2 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ m, ∃ _ : n = m + 1, ∃ _ : m + 1 ≤ codes,
    LocalSt (envOf bh bc bo)
      ((_sym, .Vint (Integers.Int.repr (((codes - (m + 1) : Nat) : _root_.Int))))
        :: T)
      (Hc2 pl lensB lensO codes lensF bc (codes - m)) e le hp

/-- Exit: every symbol counted; the `count` array holds the model counts. -/
def Post2 : Sep.Assn :=
  LocalSt (envOf bh bc bo)
    ((_sym, .Vint (Integers.Int.repr ((codes : _root_.Int)))) :: T)
    (Hc2 pl lensB lensO codes lensF bc codes)

theorem body2_triple
    (hpl : permOrder pl .Readable = true)
    (hb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hmemL : (_lens, .Vptr lensB lensO) ∈ T)
    (hmemC : (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))) ∈ T)
    (hT : ∀ p ∈ T, p.1 ≠ _t'34 ∧ p.1 ≠ _t'35 ∧ p.1 ≠ _t'36)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (Inv2 bh bc bo pl lensB lensO codes lensF T n)
      (.Ssequence (.Sifthenelse guard2 .Sskip .Sbreak) iter2)
      { normal := JAssn2 bh bc bo pl lensB lensO codes lensF T n,
        brk := Post2 bh bc bo pl lensB lensO codes lensF T,
        cont := JAssn2 bh bc bo pl lensB lensO codes lensF T n,
        ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hn : n ≤ codes) => ?_)
  match n with
  | 0 =>
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := guard2_eval ge codes (e := envOf bh bc bo) (m := mm)
          codes (by omega) (by omega)
          (hT'.get List.mem_cons_self)
          (hT'.get (List.mem_cons_of_mem _ hmemC))
        rw [show decide (codes < codes) = false from by
              rw [decide_eq_false_iff_not]; omega] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        exact hx
  | m + 1 =>
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_sym, .Vint (Integers.Int.repr
              (((codes - (m + 1) : Nat) : _root_.Int)))) :: T)
          (Hc2 pl lensB lensO codes lensF bc (codes - (m + 1)))) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        have h := guard2_eval ge codes (e := envOf bh bc bo) (m := mm)
          (codes - (m + 1)) (by omega) (by omega)
          (hT'.get List.mem_cons_self)
          (hT'.get (List.mem_cons_of_mem _ hmemC))
        rw [show decide (codes - (m + 1) < codes) = true from by
              rw [decide_eq_true_eq]; omega] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (iter2_step ge fe bh bc bo pl lensB lensO codes lensF T hpl hb
            hlens15 hc16 hnoL hmemL hT (codes - (m + 1)) (by omega))
          (fun e le hp x => x) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        refine ⟨m, rfl, by omega, ?_⟩
        obtain ⟨henv, hT', hH⟩ := hx
        rw [show codes - (m + 1) + 1 = codes - m from by omega] at hH
        exact ⟨henv,
          TempsHold_mono (fun p hp =>
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hp))) hT', hH⟩

theorem incr2_triple
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table
      (JAssn2 bh bc bo pl lensB lensO codes lensF T n) incr2
      { normal := fun e le hp =>
          ∃ n', n' < n
            ∧ Inv2 bh bc bo pl lensB lensO codes lensF T n' e le hp,
        brk := Post2 bh bc bo pl lensB lensO codes lensF T,
        cont := Assn.no, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (m : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnm : n = m + 1) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hmc : m + 1 ≤ codes) => ?_)
  subst hnm
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T _ _sym _
      (.Vint (Integers.Int.repr (((codes - m : Nat) : _root_.Int))))
      (fun p hp => List.mem_cons_of_mem _ hp) hTsym
      (fun le mm hp hT' _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr (((codes - (m + 1) : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _sym tuint _ (hT'.get List.mem_cons_self))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_uint_int]
    show some (Val.Vint (Integers.Int.add
              (Integers.Int.repr (((codes - (m + 1) : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_add, show codes - (m + 1) + 1 = codes - m from by omega]
  · exact ⟨m, by omega, by omega, hx.1, hx.2.1, hx.2.2⟩

/-- **Loop 2.**  From zero counts to the model counts of all `codes` symbols. -/
theorem loop2_triple
    (hpl : permOrder pl .Readable = true)
    (hb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hmemL : (_lens, .Vptr lensB lensO) ∈ T)
    (hmemC : (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))) ∈ T)
    (hT : ∀ p ∈ T, p.1 ≠ _t'34 ∧ p.1 ≠ _t'35 ∧ p.1 ≠ _t'36)
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (Inv2 bh bc bo pl lensB lensO codes lensF T codes) loop2
      { normal := Post2 bh bc bo pl lensB lensO codes lensF T,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _
    (Inv2 bh bc bo pl lensB lensO codes lensF T)
    (JAssn2 bh bc bo pl lensB lensO codes lensF T) _ _
    (body2_triple ge fe bh bc bo pl lensB lensO codes lensF T hpl hb hlens15
      hc16 hnoL hmemL hmemC hT _)
    (incr2_triple ge fe bh bc bo pl lensB lensO codes lensF T hTsym _) codes

/-- **Segment 2** = `sym = 0;` + loop 2, starting from the all-zero `count`
    array loop 1 left behind. -/
theorem seg2_triple
    (hpl : permOrder pl .Readable = true)
    (hb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hmemL : (_lens, .Vptr lensB lensO) ∈ T)
    (hmemC : (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))) ∈ T)
    (hT : ∀ p ∈ T, p.1 ≠ _t'34 ∧ p.1 ≠ _t'35 ∧ p.1 ≠ _t'36)
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T
        (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
         ∗ arrayU16 .Freeable bc 0 16 (fun _ => 0)))
      (.Ssequence (.Sset _sym (.Econst_int (Integers.Int.repr 0) tint)) loop2)
      { normal := Post2 bh bc bo pl lensB lensO codes lensF T,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (Inv2 bh bc bo pl lensB lensO codes lensF T codes) _ _ _ ?_
    (loop2_triple ge fe bh bc bo pl lensB lensO codes lensF T hpl hb hlens15
      hc16 hnoL hmemL hmemC hT hTsym R)
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) T _ _sym 0 hTsym)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT', hH⟩ := hx
  refine ⟨Nat.le_refl codes, henv, ?_, ?_⟩
  · rw [show ((codes - codes : Nat) : _root_.Int) = ((0 : Nat) : _root_.Int)
          from by omega]
    simpa using hT'
  · show Hc2 pl lensB lensO codes lensF bc (codes - codes) hp
    rw [show codes - codes = 0 from by omega]
    show (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
          ∗ arrayU16 .Freeable bc 0 16
              (fun l => InflateTable.Model.count lensF 0 l)) hp
    rw [show (fun l => InflateTable.Model.count lensF 0 l)
          = (fun _ : Nat => 0) from by funext l; rfl]
    exact hH

end Loop2

/-! ## §4.5 AST guards

Each chunk above is a **hand transcription** of a sub-term of
`f_inflate_table.fn_body`.  Nothing forces a transcription to be faithful, so
each is pinned by a `rfl` against the generated AST at its real position — the
`IsSortedReal.body_eq` pattern.  If `inftrees.c` or the exporter changes, these
fail loudly instead of the proofs silently drifting onto a program that is not
the one being compiled.

The guards are positional (they carry the prefix of the body), so they nest:
the one below pins the prologue, `loop1` and `loop2` at once — and with them
everything inside those loops (`guard1`/`assign1`/`incr1`, `iter2`/`incr2`).
§27's `body_matches` (`fn_body = fullBody := rfl`) covers the whole function
and subsumes this one. -/

theorem prologue_and_loops12_match : ∃ rest : Stmt,
    f_inflate_table.fn_body
      = .Ssequence
          (.Sset _base (.Ecast (.Econst_int (Integers.Int.repr 0) tint)
            (tptr tvoid)))
          (.Ssequence
            (.Sset _extra (.Ecast (.Econst_int (Integers.Int.repr 0) tint)
              (tptr tvoid)))
            (.Ssequence
              (.Sset _match (.Econst_int (Integers.Int.repr 0) tint))
              (.Ssequence
                (.Ssequence
                  (.Sset _len (.Econst_int (Integers.Int.repr 0) tint))
                  loop1)
                (.Ssequence
                  (.Ssequence
                    (.Sset _sym (.Econst_int (Integers.Int.repr 0) tint))
                    loop2)
                  rest)))) :=
  ⟨_, rfl⟩

/-! ## §5 Loop 3 — find `max` (inftrees.c:123-124; AST 519-545)

`for (max = MAXBITS; max >= 1; max--) if (count[max] != 0) break;`

First loop with a data-dependent `break`: the invariant cannot decide the
inner guard, so the proof cases on the model value (`by_cases` on
`cnt (m+1) = 0`) before `triple_if_local`.  The exit characterization —
`max ≤ 15`, all counts above `max` zero, and `max = 0` or `count[max] ≠ 0` —
is exactly `maxLen_char`'s hypothesis set, pinning `max = Model.maxLen`. -/

/-- 32-bit equality against `Nat`s (alias of `cmpu_eq_nat32` at `Int.eq`). -/
theorem eq_nat32 (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    Integers.Int.eq (Integers.Int.repr ((a : _root_.Int)))
      (Integers.Int.repr ((b : _root_.Int))) = decide (a = b) :=
  cmpu_eq_nat32 a b ha hb

/-- `(m+1) - 1 = m` at 32 bits, no side condition (wraparound agrees). -/
theorem u32_sub_one (m : Nat) :
    Integers.Int.sub (Integers.Int.repr (((m + 1 : Nat) : _root_.Int)))
      (Integers.Int.repr (((1 : Nat) : _root_.Int)))
      = Integers.Int.repr ((m : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show ((Integers.Int.repr (((m + 1 : Nat) : _root_.Int)))
        - (Integers.Int.repr (((1 : Nat) : _root_.Int))) : BitVec 32).toNat = _
  rw [BitVec.toNat_sub, u32_toNat_repr, u32_toNat_repr, u32_toNat_repr]
  omega

/-- The address of `count[k]`/`offs[k]` (zero-based block), any signedness. -/
theorem cnt_addr0 (ge : CGenv) (si : Signedness) (k : Nat) (hk : k ≤ 15) :
    Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort si Integers.Ptrofs.zero
        (Integers.Int.repr ((k : _root_.Int))))
      = Integers.Ptrofs.unsigned Integers.Ptrofs.zero
          + 2 * ((k : Nat) : _root_.Int) :=
  u16Ofs_unsigned ge.genv_cenv si Integers.Ptrofs.zero k (by omega)
    (by rw [ptrofs_unsigned_zero]
        show (0 : _root_.Int) + 2 * ((k : Nat) : _root_.Int)
              < 18446744073709551616
        omega)

/-- `x != 0` on a tracked `tushort` temporary, decided by its value. -/
theorem ne0_eval {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    (id : Ident) (v : Nat) (hv : v < 65536)
    (hid : le.get id = some (.Vint (Integers.Int.repr ((v : _root_.Int))))) :
    ∃ w, EvalExpr ge e le m
        (.Ebinop .One (.Etempvar id tushort)
          (.Econst_int (Integers.Int.repr 0) tint) tint) w
      ∧ Cop.boolVal w tint m = some (decide (v ≠ 0)) := by
  refine ⟨Val.ofBool (!(Integers.Int.eq (Integers.Int.repr ((v : _root_.Int)))
            (Integers.Int.repr 0))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .One _ _ _
      (.Vint (Integers.Int.repr ((v : _root_.Int))))
      (.Vint (Integers.Int.repr 0)) _
      (EvalExpr.Etempvar id tushort _ hid) (EvalExpr.Econst_int _ _)
      (semBinop_ne_ushort_int _ _ _ _)
  · simp only [boolVal_ofBool_int]
    rw [show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
        eq_nat32 v 0 (by omega) (by omega)]
    by_cases h : v = 0
    · subst h; simp
    · simp [h]

abbrev guard3 : Expr :=
  .Ebinop .Oge (.Etempvar _max tuint) (.Econst_int (Integers.Int.repr 1) tint) tint

abbrev read3 : Stmt :=
  .Sset _t'33 (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
    (.Etempvar _max tuint) (tptr tushort)) tushort)

abbrev brk3 : Stmt :=
  .Sifthenelse (.Ebinop .One (.Etempvar _t'33 tushort)
    (.Econst_int (Integers.Int.repr 0) tint) tint) .Sbreak .Sskip

abbrev incr3 : Stmt :=
  .Sset _max (.Ebinop .Osub (.Etempvar _max tuint)
    (.Econst_int (Integers.Int.repr 1) tint) tuint)

abbrev loop3 : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse guard3 .Sskip .Sbreak)
    (.Ssequence read3 brk3)) incr3

section Scan3

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (cnt : Nat → Nat) (T : List (Ident × Val))

/-- The scan's footprint: just the (now fixed) `count` array. -/
abbrev Hscan (bc : Block) (cnt : Nat → Nat) : HProp :=
  arrayU16 .Freeable bc 0 16 cnt

theorem guard3_eval {e : Env} {le : TempEnv} {m : Mem} (k : Nat)
    (hk : k < 65536)
    (hmax : le.get _max = some (.Vint (Integers.Int.repr ((k : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m guard3 v
      ∧ Cop.boolVal v (typeof guard3) m = some (decide (1 ≤ k)) := by
  refine ⟨Val.ofBool (!Integers.Int.ltu (Integers.Int.repr ((k : _root_.Int)))
            (Integers.Int.repr 1)), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Oge _ _ _
      (.Vint (Integers.Int.repr ((k : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _max tuint _ hmax) (EvalExpr.Econst_int _ _)
      (semBinop_ge_uint_int _ _ _ _)
  · simp only [typeof, boolVal_ofBool_int]
    rw [show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl,
        ltu_nat32 k 1 (by omega) (by omega)]
    by_cases h : 1 ≤ k
    · simp only [h, decide_true]
      rw [show decide (k < 1) = false from by
            rw [decide_eq_false_iff_not]; omega]
      rfl
    · simp only [h, decide_false]
      rw [show decide (k < 1) = true from by
            rw [decide_eq_true_eq]; omega]
      rfl

/-- Measure `n` = `max + 1`; counts above `max = n-1` are zero. -/
def Inv3 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ _ : 1 ≤ n, ∃ _ : n ≤ 16, ∃ _ : ∀ l, n - 1 < l → l ≤ 15 → cnt l = 0,
    LocalSt (envOf bh bc bo)
      ((_max, .Vint (Integers.Int.repr (((n - 1 : Nat) : _root_.Int)))) :: T)
      (Hscan bc cnt) e le hp

def JAssn3 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ m, ∃ _ : n = m + 2, ∃ _ : m + 2 ≤ 16,
    ∃ _ : ∀ l, m < l → l ≤ 15 → cnt l = 0,
      LocalSt (envOf bh bc bo)
        ((_max, .Vint (Integers.Int.repr (((m + 1 : Nat) : _root_.Int)))) :: T)
        (Hscan bc cnt) e le hp

/-- Exit: `max` is the largest length with a nonzero count (0 if none) —
    `maxLen_char`'s hypothesis set verbatim. -/
def Post3 : Sep.Assn := fun e le hp =>
  ∃ M, M ≤ 15 ∧ (∀ l, M < l → l ≤ 15 → cnt l = 0) ∧ (M = 0 ∨ cnt M ≠ 0) ∧
    LocalSt (envOf bh bc bo)
      ((_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
      (Hscan bc cnt) e le hp

theorem body3_triple
    (hcb : ∀ j, cnt j < 65536)
    (hT33 : ∀ p ∈ T, p.1 ≠ _t'33)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (Inv3 bh bc bo cnt T n)
      (.Ssequence (.Sifthenelse guard3 .Sskip .Sbreak) (.Ssequence read3 brk3))
      { normal := JAssn3 bh bc bo cnt T n, brk := Post3 bh bc bo cnt T,
        cont := JAssn3 bh bc bo cnt T n, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (h1 : 1 ≤ n) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (h16 : n ≤ 16) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hzp : ∀ l, n - 1 < l → l ≤ 15 → cnt l = 0) => ?_)
  match n with
  | 0 => exact absurd h1 (by omega)
  | 1 =>
      -- `max = 0`: the guard fails and the loop exits with no nonzero count
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := guard3_eval ge (e := envOf bh bc bo) (m := mm) 0 (by omega)
          (hT'.get List.mem_cons_self)
        simpa using h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        exact ⟨0, by omega, fun l hl h15 => hzp l (by omega) h15,
               Or.inl rfl, hx⟩
  | m + 2 =>
      -- `max = m + 1 ≥ 1`: guard holds, read `count[max]`, maybe break
      have hi15 : m + 1 ≤ 15 := by omega
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_max, .Vint (Integers.Int.repr (((m + 1 : Nat) : _root_.Int)))) :: T)
          (Hscan bc cnt)) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        have h := guard3_eval ge (e := envOf bh bc bo) (m := mm) (m + 1)
          (by omega) (hT'.get List.mem_cons_self)
        rw [show decide (1 ≤ m + 1) = true from by
              rw [decide_eq_true_eq]; omega] at h
        exact h
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'33, .Vint (Integers.Int.repr ((cnt (m + 1) : Nat))))
            :: (_max, .Vint (Integers.Int.repr (((m + 1 : Nat) : _root_.Int))))
            :: T)
          (Hscan bc cnt)) _ _ _ ?_ ?_
      · -- _t'33 = count[max]
        refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
          _t'33 _ (.Vint (Integers.Int.repr ((cnt (m + 1) : Nat))))
          (fun p hp => hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _max ≠ _t'33; decide
            · exact hT33 p hp2)
          (fun le mm hp hT' hH hag => ?_)
        exact eval_index_u16 (by decide) hH hag (by omega : m + 1 < 16) hcb
          (eval_count_base bh bc bo)
          (EvalExpr.Etempvar _max tuint _ (hT'.get List.mem_cons_self))
          rfl (cnt_addr0 ge .Unsigned (m + 1) hi15)
      · -- if (count[max] != 0) break; — decided by the model value
        by_cases hz : cnt (m + 1) = 0
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · have h := ne0_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
              _t'33 (cnt (m + 1)) (hcb _) (hT'.get List.mem_cons_self)
            rw [show decide (cnt (m + 1) ≠ 0) = false from by
                  rw [decide_eq_false_iff_not]; exact fun hne => hne hz] at h
            exact h
          · refine triple_conseq ge fe f_inflate_table
              (triple_skip ge fe f_inflate_table _)
              (fun _ _ _ x => x) (fun e le hp hx => ?_)
              (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
              (fun _ _ hx => hx.elim)
            obtain ⟨henv, hT', hH⟩ := hx
            refine ⟨m, rfl, by omega, ?_, henv,
              TempsHold_mono (fun p hp => List.mem_cons_of_mem _ hp) hT', hH⟩
            intro l hl h15
            by_cases he : l = m + 1
            · subst he; exact hz
            · exact hzp l (by omega) h15
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · have h := ne0_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
              _t'33 (cnt (m + 1)) (hcb _) (hT'.get List.mem_cons_self)
            rw [show decide (cnt (m + 1) ≠ 0) = true from by
                  rw [decide_eq_true_eq]; exact hz] at h
            exact h
          · refine triple_conseq ge fe f_inflate_table
              (triple_break ge fe f_inflate_table _)
              (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim)
              (fun e le hp hx => ?_)
              (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
            obtain ⟨henv, hT', hH⟩ := hx
            exact ⟨m + 1, by omega, fun l hl h15 => hzp l (by omega) h15,
                   Or.inr hz, henv,
                   TempsHold_mono (fun p hp => List.mem_cons_of_mem _ hp) hT',
                   hH⟩

theorem incr3_triple
    (hTmax : ∀ p ∈ T, p.1 ≠ _max)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (JAssn3 bh bc bo cnt T n) incr3
      { normal := fun e le hp =>
          ∃ n', n' < n ∧ Inv3 bh bc bo cnt T n' e le hp,
        brk := Post3 bh bc bo cnt T, cont := Assn.no,
        ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (m : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnm : n = m + 2) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (h16 : m + 2 ≤ 16) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hzp : ∀ l, m < l → l ≤ 15 → cnt l = 0) => ?_)
  subst hnm
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T _ _max _
      (.Vint (Integers.Int.repr ((m : _root_.Int))))
      (fun p hp => List.mem_cons_of_mem _ hp) hTmax
      (fun le mm hp hT' _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · refine EvalExpr.Ebinop .Osub _ _ _
      (.Vint (Integers.Int.repr (((m + 1 : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _max tuint _ (hT'.get List.mem_cons_self))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_sub_uint_int]
    show some (Val.Vint (Integers.Int.sub
              (Integers.Int.repr (((m + 1 : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_sub_one]
  · obtain ⟨henv, hT', hH⟩ := hx
    exact ⟨m + 1, by omega, by omega, by omega, hzp, henv, hT', hH⟩

/-- **Loop 3.**  From `max = 15` down to the largest counted length. -/
theorem loop3_triple
    (hcb : ∀ j, cnt j < 65536)
    (hT33 : ∀ p ∈ T, p.1 ≠ _t'33)
    (hTmax : ∀ p ∈ T, p.1 ≠ _max)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (Inv3 bh bc bo cnt T 16) loop3
      { normal := Post3 bh bc bo cnt T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _ (Inv3 bh bc bo cnt T)
    (JAssn3 bh bc bo cnt T) _ _
    (body3_triple ge fe bh bc bo cnt T hcb hT33 _)
    (incr3_triple ge fe bh bc bo cnt T hTmax _) 16

/-- **Segment 3** = `max = 15;` + loop 3. -/
theorem seg3_triple
    (hcb : ∀ j, cnt j < 65536)
    (hT33 : ∀ p ∈ T, p.1 ≠ _t'33)
    (hTmax : ∀ p ∈ T, p.1 ≠ _max)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) T (Hscan bc cnt))
      (.Ssequence (.Sset _max (.Econst_int (Integers.Int.repr 15) tint)) loop3)
      { normal := Post3 bh bc bo cnt T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _ (Inv3 bh bc bo cnt T 16) _ _ _ ?_
    (loop3_triple ge fe bh bc bo cnt T hcb hT33 hTmax R)
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) T (Hscan bc cnt) _max 15 hTmax)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT', hH⟩ := hx
  exact ⟨by omega, by omega, fun l hl h15 => by omega, henv, hT', hH⟩

end Scan3

/-! ## §6 Loop 4 — find `min` (inftrees.c:135-136; AST 627-655)

`for (min = 1; min < max; min++) if (count[min] != 0) break;`

Mirror of loop 3, scanning up, with the tracked `max` value `M` as the
dynamic bound.  Runs only on the `max ≠ 0` path, so `1 ≤ M ≤ 15` are
hypotheses. -/

abbrev guard4 : Expr :=
  .Ebinop .Olt (.Etempvar _min tuint) (.Etempvar _max tuint) tint

abbrev read4 : Stmt :=
  .Sset _t'32 (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
    (.Etempvar _min tuint) (tptr tushort)) tushort)

abbrev brk4 : Stmt :=
  .Sifthenelse (.Ebinop .One (.Etempvar _t'32 tushort)
    (.Econst_int (Integers.Int.repr 0) tint) tint) .Sbreak .Sskip

abbrev incr4 : Stmt :=
  .Sset _min (.Ebinop .Oadd (.Etempvar _min tuint)
    (.Econst_int (Integers.Int.repr 1) tint) tuint)

abbrev loop4 : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse guard4 .Sskip .Sbreak)
    (.Ssequence read4 brk4)) incr4

section Scan4

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (cnt : Nat → Nat) (M : Nat) (T : List (Ident × Val))

theorem guard4_eval {e : Env} {le : TempEnv} {m : Mem} (k : Nat)
    (hk : k < 65536) (hM : M < 65536)
    (hmin : le.get _min = some (.Vint (Integers.Int.repr ((k : _root_.Int)))))
    (hmax : le.get _max = some (.Vint (Integers.Int.repr ((M : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m guard4 v
      ∧ Cop.boolVal v (typeof guard4) m = some (decide (k < M)) := by
  refine ⟨Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((k : _root_.Int)))
            (Integers.Int.repr ((M : _root_.Int)))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Olt _ _ _
      (.Vint (Integers.Int.repr ((k : _root_.Int))))
      (.Vint (Integers.Int.repr ((M : _root_.Int)))) _
      (EvalExpr.Etempvar _min tuint _ hmin)
      (EvalExpr.Etempvar _max tuint _ hmax)
      (semBinop_lt_uint _ _ _ _)
  · simp only [typeof, boolVal_ofBool_int]
    rw [ltu_nat32 k M (by omega) (by omega)]

/-- Measure `n`; `min = M - n`, counts in `[1, min)` are zero. -/
def Inv4 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ _ : n + 1 ≤ M, ∃ _ : ∀ l, 1 ≤ l → l < M - n → cnt l = 0,
    LocalSt (envOf bh bc bo)
      ((_min, .Vint (Integers.Int.repr (((M - n : Nat) : _root_.Int))))
        :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
      (Hscan bc cnt) e le hp

def JAssn4 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ k, ∃ _ : n = k + 1, ∃ _ : k + 2 ≤ M,
    ∃ _ : ∀ l, 1 ≤ l → l < M - k → cnt l = 0,
      LocalSt (envOf bh bc bo)
        ((_min, .Vint (Integers.Int.repr (((M - (k + 1) : Nat) : _root_.Int))))
          :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
        (Hscan bc cnt) e le hp

/-- Exit: `min` is the smallest counted length (or `M` if none below it). -/
def Post4 : Sep.Assn := fun e le hp =>
  ∃ Mn, 1 ≤ Mn ∧ Mn ≤ M ∧ (∀ l, 1 ≤ l → l < Mn → cnt l = 0)
    ∧ (Mn = M ∨ cnt Mn ≠ 0) ∧
    LocalSt (envOf bh bc bo)
      ((_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
        :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
      (Hscan bc cnt) e le hp

theorem body4_triple
    (hcb : ∀ j, cnt j < 65536)
    (hM15 : M ≤ 15)
    (hT32 : ∀ p ∈ T, p.1 ≠ _t'32)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (Inv4 bh bc bo cnt M T n)
      (.Ssequence (.Sifthenelse guard4 .Sskip .Sbreak) (.Ssequence read4 brk4))
      { normal := JAssn4 bh bc bo cnt M T n, brk := Post4 bh bc bo cnt M T,
        cont := JAssn4 bh bc bo cnt M T n, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnM : n + 1 ≤ M) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hzp : ∀ l, 1 ≤ l → l < M - n → cnt l = 0) => ?_)
  match n with
  | 0 =>
      -- `min = M`: guard fails, exit with `Mn = M`
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := guard4_eval ge M (e := envOf bh bc bo) (m := mm) (M - 0)
          (by omega) (by omega)
          (hT'.get List.mem_cons_self)
          (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
        rw [show decide (M - 0 < M) = false from by
              rw [decide_eq_false_iff_not]; omega] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        refine ⟨M, by omega, by omega,
                fun l h1 hl => hzp l h1 (by omega), Or.inl rfl, ?_⟩
        rw [show ((M : Nat) : _root_.Int) = ((M - 0 : Nat) : _root_.Int)
              from by omega]
        exact hx
  | k + 1 =>
      -- `min = M - (k+1) ∈ [1, M)`: guard holds, read, maybe break
      have hmin1 : 1 ≤ M - (k + 1) := by omega
      have hi15 : M - (k + 1) ≤ 15 := by omega
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_min, .Vint (Integers.Int.repr (((M - (k + 1) : Nat) : _root_.Int))))
            :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
          (Hscan bc cnt)) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        have h := guard4_eval ge M (e := envOf bh bc bo) (m := mm) (M - (k + 1))
          (by omega) (by omega)
          (hT'.get List.mem_cons_self)
          (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
        rw [show decide (M - (k + 1) < M) = true from by
              rw [decide_eq_true_eq]; omega] at h
        exact h
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'32, .Vint (Integers.Int.repr ((cnt (M - (k + 1)) : Nat))))
            :: (_min, .Vint (Integers.Int.repr (((M - (k + 1) : Nat) : _root_.Int))))
            :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
          (Hscan bc cnt)) _ _ _ ?_ ?_
      · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
          _t'32 _ (.Vint (Integers.Int.repr ((cnt (M - (k + 1)) : Nat))))
          (fun p hp => hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _min ≠ _t'32; decide
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · show _max ≠ _t'32; decide
            · exact hT32 p hp3)
          (fun le mm hp hT' hH hag => ?_)
        exact eval_index_u16 (by decide) hH hag (by omega : M - (k + 1) < 16)
          hcb (eval_count_base bh bc bo)
          (EvalExpr.Etempvar _min tuint _ (hT'.get List.mem_cons_self))
          rfl (cnt_addr0 ge .Unsigned (M - (k + 1)) hi15)
      · by_cases hz : cnt (M - (k + 1)) = 0
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · have h := ne0_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
              _t'32 (cnt (M - (k + 1))) (hcb _) (hT'.get List.mem_cons_self)
            rw [show decide (cnt (M - (k + 1)) ≠ 0) = false from by
                  rw [decide_eq_false_iff_not]; exact fun hne => hne hz] at h
            exact h
          · refine triple_conseq ge fe f_inflate_table
              (triple_skip ge fe f_inflate_table _)
              (fun _ _ _ x => x) (fun e le hp hx => ?_)
              (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
              (fun _ _ hx => hx.elim)
            obtain ⟨henv, hT', hH⟩ := hx
            refine ⟨k, rfl, by omega, ?_, henv,
              TempsHold_mono (fun p hp => List.mem_cons_of_mem _ hp) hT', hH⟩
            intro l h1 hl
            by_cases he : l = M - (k + 1)
            · subst he; exact hz
            · exact hzp l h1 (by omega)
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · have h := ne0_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
              _t'32 (cnt (M - (k + 1))) (hcb _) (hT'.get List.mem_cons_self)
            rw [show decide (cnt (M - (k + 1)) ≠ 0) = true from by
                  rw [decide_eq_true_eq]; exact hz] at h
            exact h
          · refine triple_conseq ge fe f_inflate_table
              (triple_break ge fe f_inflate_table _)
              (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim)
              (fun e le hp hx => ?_)
              (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
            obtain ⟨henv, hT', hH⟩ := hx
            exact ⟨M - (k + 1), hmin1, by omega,
                   fun l h1 hl => hzp l h1 (by omega), Or.inr hz, henv,
                   TempsHold_mono (fun p hp => List.mem_cons_of_mem _ hp) hT',
                   hH⟩

theorem incr4_triple
    (hTmin : ∀ p ∈ T, p.1 ≠ _min)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (JAssn4 bh bc bo cnt M T n) incr4
      { normal := fun e le hp =>
          ∃ n', n' < n ∧ Inv4 bh bc bo cnt M T n' e le hp,
        brk := Post4 bh bc bo cnt M T, cont := Assn.no,
        ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (k : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnk : n = k + 1) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hkM : k + 2 ≤ M) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hzp : ∀ l, 1 ≤ l → l < M - k → cnt l = 0) => ?_)
  subst hnk
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _min _
      (.Vint (Integers.Int.repr (((M - k : Nat) : _root_.Int))))
      (fun p hp => List.mem_cons_of_mem _ hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _max ≠ _min; decide
        · exact hTmin p hp2)
      (fun le mm hp hT' _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr (((M - (k + 1) : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _min tuint _ (hT'.get List.mem_cons_self))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_uint_int]
    show some (Val.Vint (Integers.Int.add
              (Integers.Int.repr (((M - (k + 1) : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_add, show M - (k + 1) + 1 = M - k from by omega]
  · obtain ⟨henv, hT', hH⟩ := hx
    exact ⟨k, by omega, by omega, hzp, henv, hT', hH⟩

/-- **Loop 4.**  From `min = 1` up to the smallest counted length. -/
theorem loop4_triple
    (hcb : ∀ j, cnt j < 65536)
    (hM1 : 1 ≤ M) (hM15 : M ≤ 15)
    (hT32 : ∀ p ∈ T, p.1 ≠ _t'32)
    (hTmin : ∀ p ∈ T, p.1 ≠ _min)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (Inv4 bh bc bo cnt M T (M - 1)) loop4
      { normal := Post4 bh bc bo cnt M T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _ (Inv4 bh bc bo cnt M T)
    (JAssn4 bh bc bo cnt M T) _ _
    (body4_triple ge fe bh bc bo cnt M T hcb hM15 hT32 _)
    (incr4_triple ge fe bh bc bo cnt M T hTmin _) (M - 1)

/-- **Segment 4** = `min = 1;` + loop 4. -/
theorem seg4_triple
    (hcb : ∀ j, cnt j < 65536)
    (hM1 : 1 ≤ M) (hM15 : M ≤ 15)
    (hT32 : ∀ p ∈ T, p.1 ≠ _t'32)
    (hTmin : ∀ p ∈ T, p.1 ≠ _min)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
        (Hscan bc cnt))
      (.Ssequence (.Sset _min (.Econst_int (Integers.Int.repr 1) tint)) loop4)
      { normal := Post4 bh bc bo cnt M T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (Inv4 bh bc bo cnt M T (M - 1)) _ _ _ ?_
    (loop4_triple ge fe bh bc bo cnt M T hcb hM1 hM15 hT32 hTmin R)
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) _ (Hscan bc cnt) _min 1
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _max ≠ _min; decide
        · exact hTmin p hp2))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT', hH⟩ := hx
  refine ⟨by omega, fun l h1 hl => by omega, ?_⟩
  rw [show ((M - (M - 1) : Nat) : _root_.Int) = ((1 : Nat) : _root_.Int)
        from by omega]
  exact ⟨henv, hT', hH⟩

end Scan4

/-! ## §7 Root read and the two clamps (inftrees.c:122, 125, 137)

`root = *bits;` then `if (root > max) root = max;` and, after the min scan,
`if (root < min) root = min;`.  The clamps are data-dependent conditionals:
the proof cases on the comparison and lands on `Nat.min`/`Nat.max` of the
tracked values, so the clamped `root` is `min (max b0 minv) maxv`-shaped by
composition — in `[1, 15]` whenever `1 ≤ min ≤ max ≤ 15`. -/

/-- `x > y` at `(tuint, tuint)`. -/
theorem semBinop_gt_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Ogt (.Vint x) tuint (.Vint y) tuint m
      = some (Val.ofBool (Integers.Int.ltu y x)) := rfl

/-- A `tuint` comparison of two tracked temporaries, decided by their values.
    `flip = false` gives `id1 < id2`, `flip = true` gives `id1 > id2`. -/
theorem cmp_uint_eval {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    (flip : Bool) (id1 id2 : Ident) (a b : Nat)
    -- the full unsigned range, not `65536`: the first operand of both clamps is
    -- `root = *bits`, an arbitrary `unsigned` the caller chose
    (ha : a < 4294967296) (hb : b < 4294967296)
    (h1 : le.get id1 = some (.Vint (Integers.Int.repr ((a : _root_.Int)))))
    (h2 : le.get id2 = some (.Vint (Integers.Int.repr ((b : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m
        (.Ebinop (if flip then .Ogt else .Olt) (.Etempvar id1 tuint)
          (.Etempvar id2 tuint) tint) v
      ∧ Cop.boolVal v tint m
          = some (decide (if flip then b < a else a < b)) := by
  cases flip with
  | false =>
      refine ⟨Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((a : _root_.Int)))
                (Integers.Int.repr ((b : _root_.Int)))), ?_, ?_⟩
      · exact EvalExpr.Ebinop .Olt _ _ _ _ _ _
          (EvalExpr.Etempvar id1 tuint _ h1) (EvalExpr.Etempvar id2 tuint _ h2)
          (semBinop_lt_uint _ _ _ _)
      · simp only [boolVal_ofBool_int]
        rw [ltu_nat32 a b (by omega) (by omega)]
        rfl
  | true =>
      refine ⟨Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((b : _root_.Int)))
                (Integers.Int.repr ((a : _root_.Int)))), ?_, ?_⟩
      · exact EvalExpr.Ebinop .Ogt _ _ _ _ _ _
          (EvalExpr.Etempvar id1 tuint _ h1) (EvalExpr.Etempvar id2 tuint _ h2)
          (semBinop_gt_uint _ _ _ _)
      · simp only [boolVal_ofBool_int]
        rw [ltu_nat32 b a (by omega) (by omega)]
        rfl

/-- `root = *bits;` — a `Mint32` load through the `bits` parameter. -/
theorem read_root_triple (ge : CGenv) (fe : EntryRel) (E : Env)
    (pb : Permission) (bitsB : Block) (bitsO : Integers.Ptrofs) (b0 : Nat)
    (l : List (Ident × Val))
    (hpb : permOrder pb .Readable = true)
    (hmemB : (_bits, .Vptr bitsB bitsO) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ _root) :
    Triple ge fe f_inflate_table
      (LocalSt E l (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
        (.Vint (Integers.Int.repr ((b0 : _root_.Int))))))
      (.Sset _root (.Ederef (.Etempvar _bits (tptr tuint)) tuint))
      (.only (LocalSt E
        ((_root, .Vint (Integers.Int.repr ((b0 : _root_.Int)))) :: l)
        (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))))) :=
  triple_set_local ge fe f_inflate_table E l l _ _root _ _
    (fun _ hp => hp) hne
    (fun le m hp hT hH hag =>
      eval_deref_mapsto rfl hpb hH hag
        (EvalExpr.Etempvar _bits _ _ (hT.get hmemB)))

/-- `if (root > max) root = max;` — leaves `root = min r M`. -/
theorem clamp1_triple (ge : CGenv) (fe : EntryRel) (E : Env)
    (r M : Nat) (rest : List (Ident × Val)) (H : HProp)
    (hr : r < 4294967296) (hM : M < 4294967296)
    (hmemM : (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) ∈ rest)
    (hne : ∀ p ∈ rest, p.1 ≠ _root) :
    Triple ge fe f_inflate_table
      (LocalSt E ((_root, .Vint (Integers.Int.repr ((r : _root_.Int)))) :: rest) H)
      (.Sifthenelse (.Ebinop .Ogt (.Etempvar _root tuint)
          (.Etempvar _max tuint) tint)
        (.Sset _root (.Etempvar _max tuint)) .Sskip)
      (.only (LocalSt E
        ((_root, .Vint (Integers.Int.repr ((Nat.min r M : Nat)))) :: rest) H)) := by
  by_cases hcmp : M < r
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · have h := cmp_uint_eval (ge := ge) (e := E) (m := mm) true _root _max r M
        (by omega) (by omega) (hT'.get List.mem_cons_self)
        (hT'.get (List.mem_cons_of_mem _ hmemM))
      rw [show decide (if true then M < r else r < M) = true from by
            rw [decide_eq_true_eq]; simpa using hcmp] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_set_local ge fe f_inflate_table E _ rest H _root _
          (.Vint (Integers.Int.repr ((M : _root_.Int))))
          (fun p hp => List.mem_cons_of_mem _ hp) hne
          (fun le mm hp hT' _ _ =>
            EvalExpr.Etempvar _max tuint _
              (hT'.get (List.mem_cons_of_mem _ hmemM))))
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      rw [show Nat.min r M = M from Nat.min_eq_right (by omega)]
      exact hx
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · have h := cmp_uint_eval (ge := ge) (e := E) (m := mm) true _root _max r M
        (by omega) (by omega) (hT'.get List.mem_cons_self)
        (hT'.get (List.mem_cons_of_mem _ hmemM))
      rw [show decide (if true then M < r else r < M) = false from by
            rw [decide_eq_false_iff_not]; simpa using hcmp] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_skip ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      rw [show Nat.min r M = r from Nat.min_eq_left (by omega)]
      exact hx

/-- `if (root < min) root = min;` — leaves `root = max r Mn`. -/
theorem clamp2_triple (ge : CGenv) (fe : EntryRel) (E : Env)
    (r Mn : Nat) (rest : List (Ident × Val)) (H : HProp)
    (hr : r < 4294967296) (hMn : Mn < 4294967296)
    (hmemM : (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int)))) ∈ rest)
    (hne : ∀ p ∈ rest, p.1 ≠ _root) :
    Triple ge fe f_inflate_table
      (LocalSt E ((_root, .Vint (Integers.Int.repr ((r : _root_.Int)))) :: rest) H)
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _root tuint)
          (.Etempvar _min tuint) tint)
        (.Sset _root (.Etempvar _min tuint)) .Sskip)
      (.only (LocalSt E
        ((_root, .Vint (Integers.Int.repr ((Nat.max r Mn : Nat)))) :: rest) H)) := by
  by_cases hcmp : r < Mn
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · have h := cmp_uint_eval (ge := ge) (e := E) (m := mm) false _root _min r Mn
        (by omega) (by omega) (hT'.get List.mem_cons_self)
        (hT'.get (List.mem_cons_of_mem _ hmemM))
      rw [show decide (if false then Mn < r else r < Mn) = true from by
            rw [decide_eq_true_eq]; simpa using hcmp] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_set_local ge fe f_inflate_table E _ rest H _root _
          (.Vint (Integers.Int.repr ((Mn : _root_.Int))))
          (fun p hp => List.mem_cons_of_mem _ hp) hne
          (fun le mm hp hT' _ _ =>
            EvalExpr.Etempvar _min tuint _
              (hT'.get (List.mem_cons_of_mem _ hmemM))))
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      rw [show Nat.max r Mn = Mn from Nat.max_eq_right (by omega)]
      exact hx
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · have h := cmp_uint_eval (ge := ge) (e := E) (m := mm) false _root _min r Mn
        (by omega) (by omega) (hT'.get List.mem_cons_self)
        (hT'.get (List.mem_cons_of_mem _ hmemM))
      rw [show decide (if false then Mn < r else r < Mn) = false from by
            rw [decide_eq_false_iff_not]; simpa using hcmp] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_skip ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      rw [show Nat.max r Mn = r from Nat.max_eq_left (by omega)]
      exact hx

/-! ## §8 Returning (shared by all six `return` sites)

`inflate_table` has three fn_vars, so every `return` must free their blocks
(`here` 4 bytes, `count` 32, `offs` 32).  The lemma below packages the
`freeList` discharge once: the locals arrive as three raw byte runs — every
site can normalize to that shape (`undefBytes` is definitionally a
`bytesPtsTo`; `arrayU16_bytes` and `mapsto_eq_bytes`/`bytesPtsTo_append`
convert the written shapes) — and the rest of the footprint is handed to the
`ret` postcondition.  All six sites return integer constants, so the
expression evaluates without heap or temporaries. -/

private theorem union_eq_none {h1 h2 : Heap} {b : Block} {ofs : CC.Z}
    (h : Heap.union h1 h2 b ofs = none) :
    h1 b ofs = none ∧ h2 b ofs = none := by
  cases h1b : h1 b ofs with
  | none => exact ⟨rfl, by simpa [Heap.union, h1b] using h⟩
  | some c => exact absurd h (by simp [Heap.union, h1b])

private theorem union_none_of {h1 h2 : Heap} {b : Block} {ofs : CC.Z}
    (ha : h1 b ofs = none) (hb : h2 b ofs = none) :
    Heap.union h1 h2 b ofs = none := by
  simp [Heap.union, ha, hb]

theorem blocks_of_envOf (bh bc bo : Block) :
    blocksOfEnv Inftrees.prog.prog_comp_env (envOf bh bc bo)
      = [(bh, 0, 4), (bc, 0, 32), (bo, 0, 32)] := by
  show (PTree.elements _).map (blockOfBinding Inftrees.prog.prog_comp_env) = _
  rw [show PTree.elements
        (((emptyEnv.set _here (bh, Ty.Tstruct __1353 noattr)).set _count
            (bc, tarray tushort 16)).set _offs (bo, tarray tushort 16))
      = [(_here, (bh, Ty.Tstruct __1353 noattr)),
         (_count, (bc, tarray tushort 16)),
         (_offs, (bo, tarray tushort 16))] from rfl]
  show [blockOfBinding _ (_here, (bh, Ty.Tstruct __1353 noattr)),
        blockOfBinding _ (_count, (bc, tarray tushort 16)),
        blockOfBinding _ (_offs, (bo, tarray tushort 16))] = _
  rw [blockOfBinding, blockOfBinding, blockOfBinding]
  rw [show sizeof Inftrees.prog.prog_comp_env (Ty.Tstruct __1353 noattr) = 4
        from by decide,
      show sizeof Inftrees.prog.prog_comp_env (tarray tushort 16) = 32
        from by decide]

/-- `return <int constant>;` with the three locals owned as byte runs and
    `Hrest` handed to the `ret` postcondition. -/
theorem return_const_triple (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
    (l : List (Ident × Val)) (vh vc vo : List MemVal) (Hrest : HProp)
    (a : Expr) (rv : Integers.Int) (Ret : Val → HProp)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hlh : vh.length = 4) (hlc : vc.length = 32) (hlo : vo.length = 32)
    (hev : ∀ (le : TempEnv) (m : Mem),
        EvalExpr ge (envOf bh bc bo) le m a (.Vint rv))
    (hcast : ∀ m : Mem,
        Cop.semCast (.Vint rv) (typeof a) tint m = some (.Vint rv))
    (hret : ∀ hr, Hrest hr → Ret (.Vint rv) hr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))
      (.Sreturn (some a))
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := Ret } := by
  refine triple_return ge fe f_inflate_table _ _ _ (fun e le hp m hP hag => ?_)
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  obtain ⟨h1, h234, hdx1, heq1, hb1, hH2⟩ := hH
  obtain ⟨h2, h34, hdx2, heq2, hb2, hH3⟩ := hH2
  obtain ⟨h3, hr, hdx3, heq3, hb3, hbr⟩ := hH3
  subst heq1; subst heq2; subst heq3
  have hag234 : Heap.Agrees (Heap.union h2 (Heap.union h3 hr)) m :=
    Heap.Agrees_union_right hdx1 hag
  have hag34 : Heap.Agrees (Heap.union h3 hr) m :=
    Heap.Agrees_union_right hdx2 hag234
  have hag1 : Heap.Agrees h1 m := Heap.Agrees_union_left hag
  have hag2 : Heap.Agrees h2 m := Heap.Agrees_union_left hag234
  have hag3 : Heap.Agrees h3 m := Heap.Agrees_union_left hag34
  have hagr : Heap.Agrees hr m := Heap.Agrees_union_right hdx3 hag34
  -- the three ranges are Freeable in `m`
  have hr1 := bytesPtsTo_rangePerm hb1 hag1
  have hr2 := bytesPtsTo_rangePerm hb2 hag2
  have hr3 := bytesPtsTo_rangePerm hb3 hag3
  rw [hlh] at hr1; rw [hlc] at hr2; rw [hlo] at hr3
  -- ownership coverage of the three ranges
  have hown1 := bytesPtsTo_ownsRange bh .Freeable vh 0 h1 hb1
  have hown2 := bytesPtsTo_ownsRange bc .Freeable vc 0 h2 hb2
  have hown3 := bytesPtsTo_ownsRange bo .Freeable vo 0 h3 hb3
  -- the free succeeds
  obtain ⟨m', hfree⟩ := freeList_isSome_of_rangePerm
    [(bh, 0, 4), (bc, 0, 32), (bo, 0, 32)] m
    (fun blk hblk => by
      rcases List.mem_cons.mp hblk with rfl | hblk
      · simpa using hr1
      rcases List.mem_cons.mp hblk with rfl | hblk
      · simpa using hr2
      rcases List.mem_cons.mp hblk with rfl | hblk
      · simpa using hr3
      · cases hblk)
    (by simp [List.pairwise_cons, hd1, hd2, hd3])
  refine ⟨.Vint rv, .Vint rv, m', hr, hev le m, hcast m, ?_, hret hr hbr, ?_⟩
  · rw [hcenv, blocks_of_envOf]
    exact hfree
  · intro hf hdf hagf
    have hfn : ∀ (b' : Block) (o : CC.Z),
        Heap.union h1 (Heap.union h2 (Heap.union h3 hr)) b' o ≠ none →
        hf b' o = none := by
      intro b' o hne
      rcases hdf b' o with hn | hn
      · exact absurd hn hne
      · exact hn
    constructor
    · -- `hr` stays disjoint from the frame
      intro b' o
      rcases hdf b' o with hn | hn
      · exact Or.inl ((union_eq_none ((union_eq_none
          ((union_eq_none hn).2)).2)).2)
      · exact Or.inr hn
    · -- the frees do not touch `hr ∪ hf`
      refine Agrees_freeList [(bh, 0, 4), (bc, 0, 32), (bo, 0, 32)] m m' hfree
        ?_ (Heap.Agrees_union hagr (Heap.Agrees_union_right hdf hagf))
      intro blk hblk ofs hlo' hhi'
      rcases List.mem_cons.mp hblk with rfl | hblk
      · -- `here`'s range: h1 owns the cell
        have hlo2 : (0 : _root_.Int) ≤ ofs := by simpa using hlo'
        have hhi2 : ofs < 4 := by simpa using hhi'
        have hc := hown1 ofs.toNat (by rw [hlh]; omega)
        rw [show (0 : _root_.Int) + ((ofs.toNat : Nat) : _root_.Int) = ofs
              from by omega] at hc
        have hrn : hr bh ofs = none := by
          rcases hdx1 bh ofs with hn | hn
          · rw [hn] at hc; exact absurd hc (by simp)
          · exact (union_eq_none ((union_eq_none hn).2)).2
        have hfn' : hf bh ofs = none :=
          hfn bh ofs (by rw [Heap.union_of_left hc]; simp)
        exact union_none_of hrn hfn'
      rcases List.mem_cons.mp hblk with rfl | hblk
      · -- `count`'s range: h2 owns the cell
        have hlo2 : (0 : _root_.Int) ≤ ofs := by simpa using hlo'
        have hhi2 : ofs < 32 := by simpa using hhi'
        have hc := hown2 ofs.toNat (by rw [hlc]; omega)
        rw [show (0 : _root_.Int) + ((ofs.toNat : Nat) : _root_.Int) = ofs
              from by omega] at hc
        have hrn : hr bc ofs = none := by
          rcases hdx2 bc ofs with hn | hn
          · rw [hn] at hc; exact absurd hc (by simp)
          · exact (union_eq_none hn).2
        have h1n : h1 bc ofs = none := by
          rcases hdx1 bc ofs with hn | hn
          · exact hn
          · exfalso
            have := (union_eq_none hn).1
            rw [this] at hc; exact absurd hc (by simp)
        have hfn' : hf bc ofs = none := by
          refine hfn bc ofs ?_
          rw [Heap.union_of_right h1n, Heap.union_of_left hc]
          simp
        exact union_none_of hrn hfn'
      rcases List.mem_cons.mp hblk with rfl | hblk
      · -- `offs`'s range: h3 owns the cell
        have hlo2 : (0 : _root_.Int) ≤ ofs := by simpa using hlo'
        have hhi2 : ofs < 32 := by simpa using hhi'
        have hc := hown3 ofs.toNat (by rw [hlo]; omega)
        rw [show (0 : _root_.Int) + ((ofs.toNat : Nat) : _root_.Int) = ofs
              from by omega] at hc
        have hrn : hr bo ofs = none := by
          rcases hdx3 bo ofs with hn | hn
          · rw [hn] at hc; exact absurd hc (by simp)
          · exact hn
        have h2n : h2 bo ofs = none := by
          rcases hdx2 bo ofs with hn | hn
          · exact hn
          · exfalso
            have := (union_eq_none hn).1
            rw [this] at hc; exact absurd hc (by simp)
        have h1n : h1 bo ofs = none := by
          rcases hdx1 bo ofs with hn | hn
          · exact hn
          · exfalso
            have h34n := (union_eq_none hn).2
            have := (union_eq_none h34n).1
            rw [this] at hc; exact absurd hc (by simp)
        have hfn' : hf bo ofs = none := by
          refine hfn bo ofs ?_
          rw [Heap.union_of_right h1n, Heap.union_of_right h2n,
              Heap.union_of_left hc]
          simp
        exact union_none_of hrn hfn'
      · cases hblk

/-! ## §9 Loop 5 — the Kraft check (inftrees.c:140-145; AST 665-700)

    left = 1;
    for (len = 1; len <= MAXBITS; len++) {
        left <<= 1;
        left -= count[len];
        if (left < 0) return -1;      /* over-subscribed */
    }

First signed arithmetic (`left : int`) and the first early `return`.  The
tracked `left` value is the model's `leftC` (= `Model.leftAt` at the real
counts), the shift/subtract are unconditional mod-2^32 identities, and the
`left < 0` test is decided by the invariant's bound `0 ≤ leftC (len-1) ≤
2^(len-1)` — which also keeps the 32-bit values faithful to the integers. -/

/-- The `left` recurrence over an arbitrary count function (definitionally
    `Model.leftAt` when `cnt = Model.count lensF codes`). -/
def leftC (cnt : Nat → Nat) : Nat → _root_.Int
  | 0 => 1
  | l + 1 => 2 * leftC cnt l - (cnt (l + 1) : _root_.Int)

theorem leftC_eq_leftAt (lensF : Nat → Nat) (codes : Nat) :
    ∀ l, leftC (fun j => InflateTable.Model.count lensF codes j) l
          = InflateTable.Model.leftAt lensF codes l
  | 0 => rfl
  | l + 1 => by
      show 2 * leftC (fun j => InflateTable.Model.count lensF codes j) l
            - (InflateTable.Model.count lensF codes (l + 1) : _root_.Int) = _
      rw [leftC_eq_leftAt lensF codes l]
      rfl

/-- Unfold one step at an abstract index. -/
theorem leftC_pred (cnt : Nat → Nat) (d : Nat) (hd : 1 ≤ d) :
    leftC cnt d = 2 * leftC cnt (d - 1) - (cnt d : _root_.Int) := by
  rw [show d = (d - 1) + 1 from by omega]
  rfl

/-- `leftC` never exceeds `2^l` (counts are nonnegative). -/
theorem leftC_le_pow (cnt : Nat → Nat) :
    ∀ l, leftC cnt l ≤ ((2 ^ l : Nat) : _root_.Int)
  | 0 => by simp [leftC]
  | l + 1 => by
      have ih := leftC_le_pow cnt l
      have hn : (2 : Nat) ^ (l + 1) = 2 * 2 ^ l := by
        rw [Nat.pow_succ]; omega
      show 2 * leftC cnt l - (cnt (l + 1) : _root_.Int) ≤ _
      omega

/-! ### 32-bit bridges for the signed arithmetic -/

theorem i32_toInt_repr (v : _root_.Int)
    (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) :
    (Integers.Int.repr v).toInt = v := by
  rw [show Integers.Int.repr v = BitVec.ofInt 32 v from rfl, BitVec.toInt_ofInt]
  show Int.bmod v 4294967296 = v
  simp only [Int.bmod]
  split <;> omega

theorem i32_sub_repr (a b : _root_.Int) :
    Integers.Int.sub (Integers.Int.repr a) (Integers.Int.repr b)
      = Integers.Int.repr (a - b) := by
  apply BitVec.eq_of_toNat_eq
  show ((Integers.Int.repr a) - (Integers.Int.repr b) : BitVec 32).toNat = _
  rw [BitVec.toNat_sub]
  simp only [Integers.Int.repr, Integers.MI.repr, BitVec.toNat_ofInt]
  omega

theorem i32_shl_one (v : _root_.Int) :
    Integers.Int.shl (Integers.Int.repr v) (Integers.Int.repr 1)
      = Integers.Int.repr (2 * v) := by
  apply BitVec.eq_of_toNat_eq
  show ((Integers.Int.repr v) <<< ((Integers.Int.repr 1).toNat) : BitVec 32).toNat = _
  rw [show ((Integers.Int.repr 1).toNat) = 1 from rfl, BitVec.toNat_shiftLeft]
  simp only [Integers.Int.repr, Integers.MI.repr, BitVec.toNat_ofInt]
  rw [Nat.shiftLeft_eq]
  rw [show ((2 : Nat) ^ (32 : Nat)) = 4294967296 from rfl,
      show ((2 : Nat) ^ (1 : Nat)) = 2 from rfl]
  omega

theorem i32_lt_zero (v : _root_.Int)
    (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) :
    Integers.Int.lt (Integers.Int.repr v) (Integers.Int.repr 0)
      = decide (v < 0) := by
  show decide ((Integers.Int.repr v).toInt < (Integers.Int.repr 0).toInt)
        = decide (v < 0)
  rw [i32_toInt_repr v h1 h2,
      show ((Integers.Int.repr 0).toInt : _root_.Int) = 0 from rfl]

/-- `x << 1` at `(tint, tint)` (the shift amount 1 passes the `< 32` guard). -/
theorem semBinop_shl_int_one (cenv : CompositeEnv) (m : Mem) (x : Integers.Int) :
    Cop.semBinaryOperation cenv .Oshl (.Vint x) tint
      (.Vint (Integers.Int.repr 1)) tint m
      = some (.Vint (Integers.Int.shl x (Integers.Int.repr 1))) := rfl

/-- `x - y` at `(tint, tushort) → tint` (promotion, signed subtract). -/
theorem semBinop_sub_int_ushort (cenv : CompositeEnv) (m : Mem)
    (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vint x) tint (.Vint c) tushort m
      = some (.Vint (Integers.Int.sub x c)) := rfl

/-- `x < c` at `(tint, tint)` — the signed compare. -/
theorem semBinop_lt_int_int (cenv : CompositeEnv) (m : Mem)
    (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Olt (.Vint x) tint (.Vint c) tint m
      = some (Val.ofBool (Integers.Int.lt x c)) := rfl

/-- `-1` as an expression. -/
theorem semUnop_neg_one (m : Mem) :
    Cop.semUnaryOperation .Oneg (.Vint (Integers.Int.repr 1)) tint m
      = some (.Vint (Integers.Int.repr (-1))) := rfl

theorem semCast_int_int (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tint tint m = some (.Vint x) := rfl

/-! ### The loop -/

abbrev shl5 : Stmt :=
  .Sset _left (.Ebinop .Oshl (.Etempvar _left tint)
    (.Econst_int (Integers.Int.repr 1) tint) tint)

abbrev read5 : Stmt :=
  .Sset _t'31 (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
    (.Etempvar _len tuint) (tptr tushort)) tushort)

abbrev sub5 : Stmt :=
  .Sset _left (.Ebinop .Osub (.Etempvar _left tint)
    (.Etempvar _t'31 tushort) tint)

abbrev retm1 : Stmt :=
  .Sreturn (some (.Eunop .Oneg (.Econst_int (Integers.Int.repr 1) tint) tint))

abbrev if5 : Stmt :=
  .Sifthenelse (.Ebinop .Olt (.Etempvar _left tint)
    (.Econst_int (Integers.Int.repr 0) tint) tint) retm1 .Sskip

abbrev iter5 : Stmt :=
  .Ssequence shl5 (.Ssequence (.Ssequence read5 sub5) if5)

abbrev loop5 : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse guard1 .Sskip .Sbreak) iter5) incr1

section Kraft

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (cnt : Nat → Nat) (Hrest : HProp) (T : List (Ident × Val))

/-- Loop 5's footprint: the counts plus everything a `return -1` must produce
    (the other two locals to free, and the rest for the postcondition). -/
abbrev H5 (bh bc bo : Block) (cnt : Nat → Nat) (Hrest : HProp) : HProp :=
  Hscan bc cnt
  ∗ (undefBytes .Freeable bh 0 4 ∗ (undefBytes .Freeable bo 0 32 ∗ Hrest))

/-- `H5` in the shape `return_const_triple` consumes. -/
theorem H5_bytes (bh bc bo : Block) (cnt : Nat → Nat) (Hrest : HProp) :
    H5 bh bc bo cnt Hrest
      = bytesPtsTo bh .Freeable 0 (List.replicate 4 .Undef)
        ∗ (bytesPtsTo bc .Freeable 0 (u16Bytes cnt 16)
           ∗ (bytesPtsTo bo .Freeable 0 (List.replicate 32 .Undef) ∗ Hrest)) := by
  show arrayU16 .Freeable bc 0 16 cnt ∗ _ = _
  rw [arrayU16_bytes .Freeable bc 0 cnt (by omega) 16, sep_left_comm_eq]
  rfl

/-- The `-1` a failed check returns, evaluated. -/
theorem neg_one_eval {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} :
    EvalExpr ge e le m
      (.Eunop .Oneg (.Econst_int (Integers.Int.repr 1) tint) tint)
      (.Vint (Integers.Int.repr (-1))) :=
  EvalExpr.Eunop _ _ _ (.Vint (Integers.Int.repr 1)) _
    (EvalExpr.Econst_int _ _) (semUnop_neg_one m)

/-- **One Kraft iteration** at length `d`: shift, subtract `count[d]`, and
    either return `-1` (over-subscribed) or record `0 ≤ leftC d`. -/
theorem iter5_step
    (hcb : ∀ j, cnt j < 65536)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hT31 : ∀ p ∈ T, p.1 ≠ _t'31)
    (hTleft : ∀ p ∈ T, p.1 ≠ _left)
    (Ret : Val → HProp)
    (hret : ∀ hr, Hrest hr → Ret (.Vint (Integers.Int.repr (-1))) hr)
    (d : Nat) (hdlo : 1 ≤ d) (hdhi : d ≤ 15)
    (hnn : 0 ≤ leftC cnt (d - 1)) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_left, .Vint (Integers.Int.repr (leftC cnt (d - 1))))
          :: (_len, .Vint (Integers.Int.repr ((d : _root_.Int)))) :: T)
        (H5 bh bc bo cnt Hrest))
      iter5
      { normal := fun e le hp => 0 ≤ leftC cnt d ∧
          LocalSt (envOf bh bc bo)
            ((_left, .Vint (Integers.Int.repr (leftC cnt d)))
              :: (_t'31, .Vint (Integers.Int.repr ((cnt d : Nat))))
              :: (_len, .Vint (Integers.Int.repr ((d : _root_.Int)))) :: T)
            (H5 bh bc bo cnt Hrest) e le hp,
        brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
  have hub := leftC_le_pow cnt (d - 1)
  have hpow : (2 : Nat) ^ (d - 1) ≤ 32768 :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : d - 1 ≤ 15))
      (by omega)
  have hw : leftC cnt d = 2 * leftC cnt (d - 1) - (cnt d : _root_.Int) :=
    leftC_pred cnt d hdlo
  -- ── left <<= 1 ────────────────────────────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_left, .Vint (Integers.Int.repr (2 * leftC cnt (d - 1))))
        :: (_len, .Vint (Integers.Int.repr ((d : _root_.Int)))) :: T)
      (H5 bh bc bo cnt Hrest)) _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _left _
      (.Vint (Integers.Int.repr (2 * leftC cnt (d - 1))))
      (fun p hp => List.mem_cons_of_mem _ hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _len ≠ _left; decide
        · exact hTleft p hp2)
      (fun le mm hp hT' _ _ => by
        refine EvalExpr.Ebinop .Oshl _ _ _
          (.Vint (Integers.Int.repr (leftC cnt (d - 1))))
          (.Vint (Integers.Int.repr 1)) _
          (EvalExpr.Etempvar _left tint _ (hT'.get List.mem_cons_self))
          (EvalExpr.Econst_int _ _) ?_
        simp only [typeof]
        rw [semBinop_shl_int_one, i32_shl_one])) ?_
  -- ── t'31 = count[len]; left -= t'31 ──────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_left, .Vint (Integers.Int.repr (leftC cnt d)))
        :: (_t'31, .Vint (Integers.Int.repr ((cnt d : Nat))))
        :: (_len, .Vint (Integers.Int.repr ((d : _root_.Int)))) :: T)
      (H5 bh bc bo cnt Hrest)) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'31, .Vint (Integers.Int.repr ((cnt d : Nat))))
          :: (_left, .Vint (Integers.Int.repr (2 * leftC cnt (d - 1))))
          :: (_len, .Vint (Integers.Int.repr ((d : _root_.Int)))) :: T)
        (H5 bh bc bo cnt Hrest)) _ _ _
      (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'31 _
        (.Vint (Integers.Int.repr ((cnt d : Nat))))
        (fun p hp => hp)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _left ≠ _t'31; decide
          rcases List.mem_cons.mp hp2 with rfl | hp3
          · show _len ≠ _t'31; decide
          · exact hT31 p hp3)
        (fun le mm hp hT' hH hag => by
          obtain ⟨hC, hR3, hd0, heq, harrC, hHr⟩ := hH
          subst heq
          exact eval_index_u16 (by decide) harrC (Heap.Agrees_union_left hag)
            (by omega : d < 16) hcb (eval_count_base bh bc bo)
            (EvalExpr.Etempvar _len tuint _
              (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self)))
            rfl (cnt_addr0 ge .Unsigned d hdhi))) ?_
    refine triple_conseq ge fe f_inflate_table
      (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
        ((_t'31, .Vint (Integers.Int.repr ((cnt d : Nat))))
          :: (_len, .Vint (Integers.Int.repr ((d : _root_.Int)))) :: T)
        _ _left _
        (.Vint (Integers.Int.repr (leftC cnt d)))
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2))
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _t'31 ≠ _left; decide
          rcases List.mem_cons.mp hp2 with rfl | hp3
          · show _len ≠ _left; decide
          · exact hTleft p hp3)
        (fun le mm hp hT' _ _ => by
          refine EvalExpr.Ebinop .Osub _ _ _
            (.Vint (Integers.Int.repr (2 * leftC cnt (d - 1))))
            (.Vint (Integers.Int.repr ((cnt d : Nat)))) _
            (EvalExpr.Etempvar _left tint _
              (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self)))
            (EvalExpr.Etempvar _t'31 tushort _ (hT'.get List.mem_cons_self)) ?_
          simp only [typeof]
          rw [semBinop_sub_int_ushort, i32_sub_repr, ← hw]))
      (fun _ _ _ x => x) (fun e le hp hx => hx)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ hx => hx.elim)
  -- ── if (left < 0) return -1; ──────────────────────────────────────────────
  · have hcd : cnt d < 65536 := hcb d
    have hlo : -2147483648 ≤ leftC cnt d := by omega
    have hhi : leftC cnt d < 2147483648 := by omega
    by_cases hneg : leftC cnt d < 0
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · refine ⟨Val.ofBool (Integers.Int.lt
            (Integers.Int.repr (leftC cnt d)) (Integers.Int.repr 0)), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Olt _ _ _ _ (.Vint (Integers.Int.repr 0)) _
            (EvalExpr.Etempvar _left tint _ (hT'.get List.mem_cons_self))
            (EvalExpr.Econst_int _ _) (semBinop_lt_int_int _ _ _ _)
        · simp only [typeof, boolVal_ofBool_int]
          rw [i32_lt_zero _ hlo hhi,
              show decide (leftC cnt d < 0) = true from by
                rw [decide_eq_true_eq]; exact hneg]
      · refine triple_conseq ge fe f_inflate_table
          (return_const_triple ge fe bh bc bo
            ((_left, .Vint (Integers.Int.repr (leftC cnt d)))
              :: (_t'31, .Vint (Integers.Int.repr ((cnt d : Nat))))
              :: (_len, .Vint (Integers.Int.repr ((d : _root_.Int)))) :: T)
            (List.replicate 4 .Undef) (u16Bytes cnt 16)
            (List.replicate 32 .Undef) Hrest _
            (Integers.Int.repr (-1)) Ret hcenv hd1 hd2 hd3
            (by simp) (by rw [u16Bytes_length]) (by simp)
            (fun le m => neg_one_eval)
            (fun m => semCast_int_int m _) hret)
          (fun e le hp hx => ?_) (fun _ _ _ hx => hx.elim)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx)
        obtain ⟨henv, hT', hH⟩ := hx
        rw [H5_bytes] at hH
        exact ⟨henv, hT', hH⟩
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · refine ⟨Val.ofBool (Integers.Int.lt
            (Integers.Int.repr (leftC cnt d)) (Integers.Int.repr 0)), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Olt _ _ _ _ (.Vint (Integers.Int.repr 0)) _
            (EvalExpr.Etempvar _left tint _ (hT'.get List.mem_cons_self))
            (EvalExpr.Econst_int _ _) (semBinop_lt_int_int _ _ _ _)
        · simp only [typeof, boolVal_ofBool_int]
          rw [i32_lt_zero _ hlo hhi,
              show decide (leftC cnt d < 0) = false from by
                rw [decide_eq_false_iff_not]; exact hneg]
      · refine triple_conseq ge fe f_inflate_table
          (triple_skip ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun e le hp hx => ⟨by omega, hx⟩)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)

/-! ### The Kraft loop, assembled -/

/-- Measure `n` = lengths still to check; `len = 16 - n`, and every prefix
    `left` seen so far was nonnegative (that is what "no return yet" means). -/
def Inv5 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ _ : n ≤ 15, ∃ _ : ∀ j, j ≤ 15 - n → 0 ≤ leftC cnt j,
    LocalSt (envOf bh bc bo)
      ((_left, .Vint (Integers.Int.repr (leftC cnt (15 - n))))
        :: (_len, .Vint (Integers.Int.repr (((16 - n : Nat) : _root_.Int)))) :: T)
      (H5 bh bc bo cnt Hrest) e le hp

def JAssn5 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ m, ∃ _ : n = m + 1, ∃ _ : m ≤ 14, ∃ _ : ∀ j, j ≤ 15 - m → 0 ≤ leftC cnt j,
    LocalSt (envOf bh bc bo)
      ((_left, .Vint (Integers.Int.repr (leftC cnt (15 - m))))
        :: (_len, .Vint (Integers.Int.repr (((16 - (m + 1) : Nat) : _root_.Int))))
        :: T)
      (H5 bh bc bo cnt Hrest) e le hp

/-- Exit: the check passed at every length — `kraftOk` for these counts. -/
def Post5 : Sep.Assn := fun e le hp =>
  (∀ j, j ≤ 15 → 0 ≤ leftC cnt j) ∧
  LocalSt (envOf bh bc bo)
    ((_left, .Vint (Integers.Int.repr (leftC cnt 15)))
      :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int)))) :: T)
    (H5 bh bc bo cnt Hrest) e le hp

theorem body5_triple
    (hcb : ∀ j, cnt j < 65536)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hT31 : ∀ p ∈ T, p.1 ≠ _t'31)
    (hTleft : ∀ p ∈ T, p.1 ≠ _left)
    (Ret : Val → HProp)
    (hret : ∀ hr, Hrest hr → Ret (.Vint (Integers.Int.repr (-1))) hr)
    (n : Nat) :
    Triple ge fe f_inflate_table (Inv5 bh bc bo cnt Hrest T n)
      (.Ssequence (.Sifthenelse guard1 .Sskip .Sbreak) iter5)
      { normal := JAssn5 bh bc bo cnt Hrest T n,
        brk := Post5 bh bc bo cnt Hrest T,
        cont := JAssn5 bh bc bo cnt Hrest T n,
        ret := Ret, goto := fun _ => Assn.no } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (h15 : n ≤ 15) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hpre : ∀ j, j ≤ 15 - n → 0 ≤ leftC cnt j) => ?_)
  match n with
  | 0 =>
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := guard1_eval (ge := ge) (e := envOf bh bc bo) (m := mm) 16
          (by omega) (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
        simpa using h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        exact ⟨fun j hj => hpre j (by omega), hx⟩
  | m + 1 =>
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_left, .Vint (Integers.Int.repr (leftC cnt (15 - (m + 1)))))
            :: (_len, .Vint (Integers.Int.repr
                (((16 - (m + 1) : Nat) : _root_.Int)))) :: T)
          (H5 bh bc bo cnt Hrest)) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        have h := guard1_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
          (16 - (m + 1)) (by omega)
          (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
        rw [show decide (16 - (m + 1) ≤ 15) = true from by
              rw [decide_eq_true_eq]; omega] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (iter5_step ge fe bh bc bo cnt Hrest T hcb hcenv hd1 hd2 hd3 hT31
            hTleft Ret hret (16 - (m + 1)) (by omega) (by omega) ?_)
          (fun e le hp hx => ?_) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx) (fun _ _ _ _ hx => hx)
        · rw [show 16 - (m + 1) - 1 = 15 - (m + 1) from by omega]
          exact hpre (15 - (m + 1)) (by omega)
        · rw [show (15 - (m + 1) : Nat) = 16 - (m + 1) - 1 from by omega] at hx
          exact hx
        · obtain ⟨hnn, henv, hT', hH⟩ := hx
          rw [show leftC cnt (16 - (m + 1)) = leftC cnt (15 - m) from by
                rw [show (16 - (m + 1) : Nat) = 15 - m from by omega]] at hnn hT'
          refine ⟨m, rfl, by omega, ?_, henv,
            TempsHold_mono (fun p hp => ?_) hT', hH⟩
          · intro j hj
            by_cases he : j = 15 - m
            · subst he; exact hnn
            · exact hpre j (by omega)
          · rcases List.mem_cons.mp hp with rfl | hp2
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2)

theorem incr5_triple
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (Ret : Val → HProp) (n : Nat) :
    Triple ge fe f_inflate_table (JAssn5 bh bc bo cnt Hrest T n) incr1
      { normal := fun e le hp =>
          ∃ n', n' < n ∧ Inv5 bh bc bo cnt Hrest T n' e le hp,
        brk := Post5 bh bc bo cnt Hrest T, cont := Assn.no,
        ret := Ret, goto := fun _ => Assn.no } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (m : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnm : n = m + 1) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hm14 : m ≤ 14) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hpre : ∀ j, j ≤ 15 - m → 0 ≤ leftC cnt j) => ?_)
  subst hnm
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
      ((_left, .Vint (Integers.Int.repr (leftC cnt (15 - m)))) :: T) _ _len _
      (.Vint (Integers.Int.repr (((16 - m : Nat) : _root_.Int))))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _left ≠ _len; decide
        · exact hTlen p hp2)
      (fun le mm hp hT' _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr (((16 - (m + 1) : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _len tuint _
        (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self)))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_uint_int]
    show some (Val.Vint (Integers.Int.add
              (Integers.Int.repr (((16 - (m + 1) : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_add, show 16 - (m + 1) + 1 = 16 - m from by omega]
  · obtain ⟨henv, hT', hH⟩ := hx
    refine ⟨m, by omega, by omega, hpre, henv,
      TempsHold_mono (fun p hp => ?_) hT', hH⟩
    rcases List.mem_cons.mp hp with rfl | hp2
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    rcases List.mem_cons.mp hp2 with rfl | hp3
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp3)

/-- **Loop 5.**  Either every prefix of the Kraft sum is nonnegative (exit
    `Post5`), or the code was over-subscribed and `-1` was returned. -/
theorem loop5_triple
    (hcb : ∀ j, cnt j < 65536)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hT31 : ∀ p ∈ T, p.1 ≠ _t'31)
    (hTleft : ∀ p ∈ T, p.1 ≠ _left)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (Ret : Val → HProp)
    (hret : ∀ hr, Hrest hr → Ret (.Vint (Integers.Int.repr (-1))) hr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (Inv5 bh bc bo cnt Hrest T 15) loop5
      { normal := Post5 bh bc bo cnt Hrest T, brk := R.brk, cont := R.cont,
        ret := Ret, goto := fun _ => Assn.no } :=
  triple_loop ge fe f_inflate_table _ (Inv5 bh bc bo cnt Hrest T)
    (JAssn5 bh bc bo cnt Hrest T) _ _
    (body5_triple ge fe bh bc bo cnt Hrest T hcb hcenv hd1 hd2 hd3 hT31
      hTleft Ret hret)
    (incr5_triple ge fe bh bc bo cnt Hrest T hTlen Ret) 15

/-- **Segment 5 core** = `len = 1;` + loop 5 (the preceding `left = 1;` is a
    `set_const_triple` at composition time). -/
theorem seg5_triple
    (hcb : ∀ j, cnt j < 65536)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hT31 : ∀ p ∈ T, p.1 ≠ _t'31)
    (hTleft : ∀ p ∈ T, p.1 ≠ _left)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (Ret : Val → HProp)
    (hret : ∀ hr, Hrest hr → Ret (.Vint (Integers.Int.repr (-1))) hr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_left, .Vint (Integers.Int.repr 1)) :: T)
        (H5 bh bc bo cnt Hrest))
      (.Ssequence (.Sset _len (.Econst_int (Integers.Int.repr 1) tint)) loop5)
      { normal := Post5 bh bc bo cnt Hrest T, brk := R.brk, cont := R.cont,
        ret := Ret, goto := fun _ => Assn.no } := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (Inv5 bh bc bo cnt Hrest T 15) _ _ _ ?_
    (loop5_triple ge fe bh bc bo cnt Hrest T hcb hcenv hd1 hd2 hd3 hT31
      hTleft hTlen Ret hret R)
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
      ((_left, .Vint (Integers.Int.repr 1)) :: T) _ _len _
      (.Vint (Integers.Int.repr (((1 : Nat) : _root_.Int))))
      (fun p hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _left ≠ _len; decide
        · exact hTlen p hp2)
      (fun le mm hp hT' _ _ => EvalExpr.Econst_int _ _))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT', hH⟩ := hx
  refine ⟨by omega, fun j hj => by
      rw [show j = 0 from by omega]
      show (0 : _root_.Int) ≤ 1
      omega, henv,
    TempsHold_mono (fun p hp => ?_) hT', hH⟩
  rcases List.mem_cons.mp hp with rfl | hp2
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_cons.mp hp2 with rfl | hp3
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp3)

end Kraft

/-! ## §10 The incomplete-set check (inftrees.c:146-147; AST 707-736)

`if (left > 0 && (type == CODES || max != 1)) return -1;`

clightgen compiles the short-circuit into nested ifs computing `_t'3`.  The
pass-through records exactly the negation — `left ≤ 0 ∨ (type ≠ 0 ∧ max = 1)`
— which, with `Post5`'s `0 ≤ left`, is the `incomplete_count_one` setup. -/

theorem semBinop_gt_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Ogt (.Vint x) tint (.Vint c) tint m
      = some (Val.ofBool (Integers.Int.lt c x)) := rfl

theorem semBinop_eq_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tint (.Vint c) tint m
      = some (Val.ofBool (Integers.Int.eq x c)) := rfl

/-- The `max == 0` guard's value, as `triple_if_local` wants it. -/
theorem eqz_uint_eval {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    (id : Ident) (a : Nat) (ha : a < 4294967296)
    (h1 : le.get id = some (.Vint (Integers.Int.repr ((a : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m
        (.Ebinop .Oeq (.Etempvar id tuint)
          (.Econst_int (Integers.Int.repr 0) tint) tint) v
      ∧ Cop.boolVal v tint m = some (decide (a = 0)) := by
  refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr ((a : _root_.Int)))
            (Integers.Int.repr 0)), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
      (EvalExpr.Etempvar id tuint _ h1) (EvalExpr.Econst_int _ _) rfl
  · simp only [boolVal_ofBool_int]
    rw [show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
        eq_nat32 a 0 (by omega) (by omega)]

/-- `x != c` at `(tuint, tint)`. -/
theorem semBinop_ne_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .One (.Vint x) tuint (.Vint c) tint m
      = some (Val.ofBool (!(Integers.Int.eq x c))) := rfl

theorem boolVal_vint (m : Mem) (x : Integers.Int) :
    Cop.boolVal (.Vint x) tint m
      = some (!(Integers.Int.eq x (Integers.Int.repr 0))) := rfl

theorem i32_lt_int (a b : _root_.Int)
    (ha1 : -2147483648 ≤ a) (ha2 : a < 2147483648)
    (hb1 : -2147483648 ≤ b) (hb2 : b < 2147483648) :
    Integers.Int.lt (Integers.Int.repr a) (Integers.Int.repr b)
      = decide (a < b) := by
  show decide ((Integers.Int.repr a).toInt < (Integers.Int.repr b).toInt)
        = decide (a < b)
  rw [i32_toInt_repr a ha1 ha2, i32_toInt_repr b hb1 hb2]

theorem i32_eq_int (a b : _root_.Int)
    (ha1 : -2147483648 ≤ a) (ha2 : a < 2147483648)
    (hb1 : -2147483648 ≤ b) (hb2 : b < 2147483648) :
    Integers.Int.eq (Integers.Int.repr a) (Integers.Int.repr b)
      = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp [Integers.Int.eq, Integers.MI.eq]
  · simp only [h, decide_false]
    show (Integers.Int.repr a == Integers.Int.repr b) = false
    rw [beq_eq_false_iff_ne]
    intro hc
    exact h (by rw [← i32_toInt_repr a ha1 ha2, ← i32_toInt_repr b hb1 hb2, hc])

abbrev chk6 : Stmt :=
  .Ssequence
    (.Sifthenelse (.Ebinop .Ogt (.Etempvar _left tint)
        (.Econst_int (Integers.Int.repr 0) tint) tint)
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar _type tint)
          (.Econst_int (Integers.Int.repr 0) tint) tint)
        (.Sset _t'3 (.Ecast (.Econst_int (Integers.Int.repr 1) tint) tbool))
        (.Ssequence
          (.Sset _t'3 (.Ecast (.Ebinop .One (.Etempvar _max tuint)
              (.Econst_int (Integers.Int.repr 1) tint) tint) tbool))
          (.Sset _t'3 (.Ecast (.Etempvar _t'3 tint) tbool))))
      (.Sset _t'3 (.Econst_int (Integers.Int.repr 0) tint)))
    (.Sifthenelse (.Etempvar _t'3 tint) retm1 .Sskip)

section Chk6

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (cnt : Nat → Nat) (Hrest : HProp) (l : List (Ident × Val))

theorem chk6_triple
    (lv ty : _root_.Int) (M : Nat)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hlv1 : -2147483648 ≤ lv) (hlv2 : lv < 2147483648)
    (hty1 : 0 ≤ ty) (hty2 : ty < 3) (hM : M ≤ 15)
    (hmemLv : (_left, .Vint (Integers.Int.repr lv)) ∈ l)
    (hmemTy : (_type, .Vint (Integers.Int.repr ty)) ∈ l)
    (hmemM : (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) ∈ l)
    (hT3 : ∀ p ∈ l, p.1 ≠ _t'3)
    (Ret : Val → HProp)
    (hret : ∀ hr, Hrest hr → Ret (.Vint (Integers.Int.repr (-1))) hr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l (H5 bh bc bo cnt Hrest)) chk6
      { normal := fun e le hp => (lv ≤ 0 ∨ (ty ≠ 0 ∧ M = 1)) ∧
          LocalSt (envOf bh bc bo)
            ((_t'3, .Vint (Integers.Int.repr 0)) :: l)
            (H5 bh bc bo cnt Hrest) e le hp,
        brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
  have hretbr : Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_t'3, .Vint (Integers.Int.repr 1)) :: l)
        (H5 bh bc bo cnt Hrest)) retm1
      { normal := fun e le hp => (lv ≤ 0 ∨ (ty ≠ 0 ∧ M = 1)) ∧
          LocalSt (envOf bh bc bo)
            ((_t'3, .Vint (Integers.Int.repr 0)) :: l)
            (H5 bh bc bo cnt Hrest) e le hp,
        brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
    refine triple_conseq ge fe f_inflate_table
      (return_const_triple ge fe bh bc bo
        ((_t'3, .Vint (Integers.Int.repr 1)) :: l)
        (List.replicate 4 .Undef) (u16Bytes cnt 16)
        (List.replicate 32 .Undef) Hrest _
        (Integers.Int.repr (-1)) Ret hcenv hd1 hd2 hd3
        (by simp) (by rw [u16Bytes_length]) (by simp)
        (fun le m => neg_one_eval)
        (fun m => semCast_int_int m _) hret)
      (fun e le hp hx => ?_) (fun _ _ _ hx => hx.elim)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ hx => hx)
    obtain ⟨henv, hT', hH⟩ := hx
    rw [H5_bytes] at hH
    exact ⟨henv, hT', hH⟩
  by_cases hpos : 0 < lv
  · by_cases hty0 : ty = 0
    · -- left > 0, CODES: t'3 = 1, return -1
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'3, .Vint (Integers.Int.repr 1)) :: l)
          (H5 bh bc bo cnt Hrest)) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) ?_
        · refine ⟨Val.ofBool (Integers.Int.lt (Integers.Int.repr 0)
              (Integers.Int.repr lv)), ?_, ?_⟩
          · exact EvalExpr.Ebinop .Ogt _ _ _ _ (.Vint (Integers.Int.repr 0)) _
              (EvalExpr.Etempvar _left tint _ (hT'.get hmemLv))
              (EvalExpr.Econst_int _ _) (semBinop_gt_int _ _ _ _)
          · simp only [typeof, boolVal_ofBool_int]
            rw [i32_lt_int 0 lv (by omega) (by omega) hlv1 hlv2,
                show decide ((0 : _root_.Int) < lv) = true from by
                  rw [decide_eq_true_eq]; exact hpos]
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr ty)
                (Integers.Int.repr 0)), ?_, ?_⟩
            · exact EvalExpr.Ebinop .Oeq _ _ _ _ (.Vint (Integers.Int.repr 0)) _
                (EvalExpr.Etempvar _type tint _ (hT'.get hmemTy))
                (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
            · simp only [typeof, boolVal_ofBool_int]
              rw [i32_eq_int ty 0 (by omega) (by omega) (by omega) (by omega),
                  show decide (ty = (0 : _root_.Int)) = true from by
                    rw [decide_eq_true_eq]; exact hty0]
          · exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
              _t'3 _ (.Vint (Integers.Int.repr 1)) (fun p hp => hp) hT3
              (fun le mm hp hT' _ _ =>
                EvalExpr.Ecast _ _ (.Vint (Integers.Int.repr 1)) _
                  (EvalExpr.Econst_int _ _) rfl)
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) hretbr
        exact ⟨.Vint (Integers.Int.repr 1),
          EvalExpr.Etempvar _t'3 tint _ (hT'.get List.mem_cons_self), rfl⟩
    · by_cases hM1 : M = 1
      · -- left > 0, LENS/DISTS, max = 1: incomplete but allowed — t'3 = 0
        subst hM1
        refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_t'3, .Vint (Integers.Int.repr 0)) :: l)
            (H5 bh bc bo cnt Hrest)) _ _ _ ?_ ?_
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · refine ⟨Val.ofBool (Integers.Int.lt (Integers.Int.repr 0)
                (Integers.Int.repr lv)), ?_, ?_⟩
            · exact EvalExpr.Ebinop .Ogt _ _ _ _ (.Vint (Integers.Int.repr 0)) _
                (EvalExpr.Etempvar _left tint _ (hT'.get hmemLv))
                (EvalExpr.Econst_int _ _) (semBinop_gt_int _ _ _ _)
            · simp only [typeof, boolVal_ofBool_int]
              rw [i32_lt_int 0 lv (by omega) (by omega) hlv1 hlv2,
                  show decide ((0 : _root_.Int) < lv) = true from by
                    rw [decide_eq_true_eq]; exact hpos]
          · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
              (fun le mm hp hT' _ _ => ?_) ?_
            · refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr ty)
                  (Integers.Int.repr 0)), ?_, ?_⟩
              · exact EvalExpr.Ebinop .Oeq _ _ _ _
                  (.Vint (Integers.Int.repr 0)) _
                  (EvalExpr.Etempvar _type tint _ (hT'.get hmemTy))
                  (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
              · simp only [typeof, boolVal_ofBool_int]
                rw [i32_eq_int ty 0 (by omega) (by omega) (by omega) (by omega),
                    show decide (ty = (0 : _root_.Int)) = false from by
                      rw [decide_eq_false_iff_not]; exact hty0]
            · -- t'3 = (max != 1) = 0; then t'3 = (bool) t'3 = 0
              refine triple_seq_fwd ge fe f_inflate_table _
                (LocalSt (envOf bh bc bo)
                  ((_t'3, .Vint (Integers.Int.repr 0)) :: l)
                  (H5 bh bc bo cnt Hrest)) _ _ _
                (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
                  _t'3 _ (.Vint (Integers.Int.repr 0)) (fun p hp => hp) hT3
                  (fun le mm hp hT' _ _ => by
                    refine EvalExpr.Ecast _ _
                      (Val.ofBool (!(Integers.Int.eq
                        (Integers.Int.repr (((1 : Nat) : _root_.Int)))
                        (Integers.Int.repr 1)))) _
                      (EvalExpr.Ebinop .One _ _ _ _
                        (.Vint (Integers.Int.repr 1)) _
                        (EvalExpr.Etempvar _max tuint _ (hT'.get hmemM))
                        (EvalExpr.Econst_int _ _)
                        (semBinop_ne_uint_int _ _ _ _)) ?_
                    rw [show (!(Integers.Int.eq
                          (Integers.Int.repr (((1 : Nat) : _root_.Int)))
                          (Integers.Int.repr 1))) = false from rfl]
                    rfl)) ?_
              exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
                l _ _t'3 _ (.Vint (Integers.Int.repr 0))
                (fun p hp => List.mem_cons_of_mem _ hp) hT3
                (fun le mm hp hT' _ _ =>
                  EvalExpr.Ecast _ _ (.Vint (Integers.Int.repr 0)) _
                    (EvalExpr.Etempvar _t'3 tint _
                      (hT'.get List.mem_cons_self)) rfl)
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · exact ⟨.Vint (Integers.Int.repr 0),
              EvalExpr.Etempvar _t'3 tint _ (hT'.get List.mem_cons_self), rfl⟩
          · refine triple_conseq ge fe f_inflate_table
              (triple_skip ge fe f_inflate_table _)
              (fun _ _ _ x => x)
              (fun e le hp hx => ⟨Or.inr ⟨hty0, rfl⟩, hx⟩)
              (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
              (fun _ _ hx => hx.elim)
      · -- left > 0, LENS/DISTS, max ≠ 1: t'3 = 1, return -1
        refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_t'3, .Vint (Integers.Int.repr 1)) :: l)
            (H5 bh bc bo cnt Hrest)) _ _ _ ?_ ?_
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
            (fun le mm hp hT' _ _ => ?_) ?_
          · refine ⟨Val.ofBool (Integers.Int.lt (Integers.Int.repr 0)
                (Integers.Int.repr lv)), ?_, ?_⟩
            · exact EvalExpr.Ebinop .Ogt _ _ _ _ (.Vint (Integers.Int.repr 0)) _
                (EvalExpr.Etempvar _left tint _ (hT'.get hmemLv))
                (EvalExpr.Econst_int _ _) (semBinop_gt_int _ _ _ _)
            · simp only [typeof, boolVal_ofBool_int]
              rw [i32_lt_int 0 lv (by omega) (by omega) hlv1 hlv2,
                  show decide ((0 : _root_.Int) < lv) = true from by
                    rw [decide_eq_true_eq]; exact hpos]
          · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
              (fun le mm hp hT' _ _ => ?_) ?_
            · refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr ty)
                  (Integers.Int.repr 0)), ?_, ?_⟩
              · exact EvalExpr.Ebinop .Oeq _ _ _ _
                  (.Vint (Integers.Int.repr 0)) _
                  (EvalExpr.Etempvar _type tint _ (hT'.get hmemTy))
                  (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
              · simp only [typeof, boolVal_ofBool_int]
                rw [i32_eq_int ty 0 (by omega) (by omega) (by omega) (by omega),
                    show decide (ty = (0 : _root_.Int)) = false from by
                      rw [decide_eq_false_iff_not]; exact hty0]
            · refine triple_seq_fwd ge fe f_inflate_table _
                (LocalSt (envOf bh bc bo)
                  ((_t'3, .Vint (Integers.Int.repr 1)) :: l)
                  (H5 bh bc bo cnt Hrest)) _ _ _
                (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
                  _t'3 _ (.Vint (Integers.Int.repr 1)) (fun p hp => hp) hT3
                  (fun le mm hp hT' _ _ => by
                    refine EvalExpr.Ecast _ _
                      (Val.ofBool (!(Integers.Int.eq
                        (Integers.Int.repr ((M : _root_.Int)))
                        (Integers.Int.repr 1)))) _
                      (EvalExpr.Ebinop .One _ _ _ _
                        (.Vint (Integers.Int.repr 1)) _
                        (EvalExpr.Etempvar _max tuint _ (hT'.get hmemM))
                        (EvalExpr.Econst_int _ _)
                        (semBinop_ne_uint_int _ _ _ _)) ?_
                    rw [show (1 : _root_.Int) = ((1 : Nat) : _root_.Int)
                          from rfl,
                        eq_nat32 M 1 (by omega) (by omega),
                        show decide (M = 1) = false from by
                          rw [decide_eq_false_iff_not]; exact hM1]
                    rfl)) ?_
              exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
                l _ _t'3 _ (.Vint (Integers.Int.repr 1))
                (fun p hp => List.mem_cons_of_mem _ hp) hT3
                (fun le mm hp hT' _ _ =>
                  EvalExpr.Ecast _ _ (.Vint (Integers.Int.repr 1)) _
                    (EvalExpr.Etempvar _t'3 tint _
                      (hT'.get List.mem_cons_self)) rfl)
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
            (fun le mm hp hT' _ _ => ?_) hretbr
          exact ⟨.Vint (Integers.Int.repr 1),
            EvalExpr.Etempvar _t'3 tint _ (hT'.get List.mem_cons_self), rfl⟩
  · -- left ≤ 0: else branch, t'3 = 0, no return
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'3, .Vint (Integers.Int.repr 0)) :: l)
        (H5 bh bc bo cnt Hrest)) _ _ _ ?_ ?_
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · refine ⟨Val.ofBool (Integers.Int.lt (Integers.Int.repr 0)
            (Integers.Int.repr lv)), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Ogt _ _ _ _ (.Vint (Integers.Int.repr 0)) _
            (EvalExpr.Etempvar _left tint _ (hT'.get hmemLv))
            (EvalExpr.Econst_int _ _) (semBinop_gt_int _ _ _ _)
        · simp only [typeof, boolVal_ofBool_int]
          rw [i32_lt_int 0 lv (by omega) (by omega) hlv1 hlv2,
              show decide ((0 : _root_.Int) < lv) = false from by
                rw [decide_eq_false_iff_not]; omega]
      · exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
          _t'3 _ (.Vint (Integers.Int.repr 0)) (fun p hp => hp) hT3
          (fun le mm hp hT' _ _ => EvalExpr.Econst_int _ _)
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · exact ⟨.Vint (Integers.Int.repr 0),
          EvalExpr.Etempvar _t'3 tint _ (hT'.get List.mem_cons_self), rfl⟩
      · refine triple_conseq ge fe f_inflate_table
          (triple_skip ge fe f_inflate_table _)
          (fun _ _ _ x => x)
          (fun e le hp hx => ⟨Or.inl (by omega), hx⟩)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)

end Chk6

/-! ## §11 Loop 6 — the offsets (inftrees.c:150-152; AST 738-790)

`offs[1] = 0; for (len = 1; len < MAXBITS; len++) offs[len+1] = offs[len] + count[len];`

`offs[0]` is never written, so the local lives as three zones: an undefined
cell 0, the initialized cells `1..k` (an `arrayU16` at base offset 2 whose
index `j` is cell `j+1`), and an undefined suffix.  The iteration lemma is
parametrized by `e` with `len = e + 1`, which keeps every array index in
successor form — definitionally aligned with `offsC`'s unfolding — so no
index arithmetic leaks into the heap rewrites. -/

/-- The running offsets: `offsC 1 = 0`, `offsC (l+1) = offsC l + cnt l` for
    `l ≥ 1` (`Model.offs` at the real counts, by `offsC_count_eq`). -/
def offsC (cnt : Nat → Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => if l = 0 then 0 else offsC cnt l + cnt l

/-- The recurrence, at any `l ≥ 1`. -/
theorem offsC_succ (cnt : Nat → Nat) (l : Nat) (hl : 1 ≤ l) :
    offsC cnt (l + 1) = offsC cnt l + cnt l := by
  show (if l = 0 then 0 else offsC cnt l + cnt l) = _
  rw [if_neg (by omega)]

open InflateTable.Model in
theorem offsC_count_eq (lensF : Nat → Nat) (codes : Nat) :
    ∀ l, offsC (fun j => count lensF codes j) l = offs lensF codes l
  | 0 => by rw [offs_zero]; rfl
  | 1 => by rw [offs_one]; rfl
  | (l + 1) + 1 => by
      show (if l + 1 = 0 then 0
            else offsC (fun j => count lensF codes j) (l + 1)
                 + count lensF codes (l + 1)) = _
      rw [if_neg (by omega), offsC_count_eq lensF codes (l + 1),
          offs_succ lensF codes (l + 1) (by omega)]

/-- `x < c` at `(tuint, tint)`: unsigned comparison after conversion. -/
theorem semBinop_lt_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Olt (.Vint x) tuint (.Vint c) tint m
      = some (Val.ofBool (Integers.Int.ltu x c)) := rfl

abbrev offs1Init : Stmt :=
  .Sassign
    (.Ederef (.Ebinop .Oadd (.Evar _offs (tarray tushort 16))
      (.Econst_int (Integers.Int.repr 1) tint) (tptr tushort)) tushort)
    (.Econst_int (Integers.Int.repr 0) tint)

abbrev guard6 : Expr :=
  .Ebinop .Olt (.Etempvar _len tuint) (.Econst_int (Integers.Int.repr 15) tint) tint

abbrev read29 : Stmt :=
  .Sset _t'29 (.Ederef (.Ebinop .Oadd (.Evar _offs (tarray tushort 16))
    (.Etempvar _len tuint) (tptr tushort)) tushort)

abbrev read30 : Stmt :=
  .Sset _t'30 (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
    (.Etempvar _len tuint) (tptr tushort)) tushort)

abbrev assign6 : Stmt :=
  .Sassign
    (.Ederef (.Ebinop .Oadd (.Evar _offs (tarray tushort 16))
      (.Ebinop .Oadd (.Etempvar _len tuint)
        (.Econst_int (Integers.Int.repr 1) tint) tuint) (tptr tushort)) tushort)
    (.Ebinop .Oadd (.Etempvar _t'29 tushort) (.Etempvar _t'30 tushort) tint)

abbrev loop6 : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse guard6 .Sskip .Sbreak)
    (.Ssequence read29 (.Ssequence read30 assign6))) incr1

section Offs6

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (cnt : Nat → Nat) (T : List (Ident × Val))

/-- The `offs` local with cells `1..k` initialized. -/
abbrev Hoffs (bo : Block) (cnt : Nat → Nat) (k : Nat) : HProp :=
  undefBytes .Freeable bo 0 2
  ∗ (arrayU16 .Freeable bo 2 k (fun j => offsC cnt (j + 1))
     ∗ undefBytes .Freeable bo (2 + 2 * (k : _root_.Int)) (30 - 2 * k))

/-- Loop 6's footprint. -/
abbrev H6 (bc bo : Block) (cnt : Nat → Nat) (k : Nat) : HProp :=
  Hscan bc cnt ∗ Hoffs bo cnt k

/-- The `offs` base pointer (array decay). -/
theorem eval_offs_base {ge : CGenv} {le : TempEnv} {m : Mem}
    (bh bc bo : Block) :
    EvalExpr ge (envOf bh bc bo) le m (.Evar _offs (tarray tushort 16))
      (.Vptr bo Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ bo Integers.Ptrofs.zero .Full _
    (eval_var_local (envOf_offs bh bc bo)) (DerefLoc.reference (by decide))

theorem guard6_eval {e : Env} {le : TempEnv} {m : Mem} (k : Nat)
    (hk : k < 65536)
    (hlen : le.get _len = some (.Vint (Integers.Int.repr ((k : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m guard6 v
      ∧ Cop.boolVal v (typeof guard6) m = some (decide (k < 15)) := by
  refine ⟨Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((k : _root_.Int)))
            (Integers.Int.repr 15)), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Olt _ _ _
      (.Vint (Integers.Int.repr ((k : _root_.Int))))
      (.Vint (Integers.Int.repr 15)) _
      (EvalExpr.Etempvar _len tuint _ hlen) (EvalExpr.Econst_int _ _)
      (semBinop_lt_uint_int _ _ _ _)
  · simp only [typeof, boolVal_ofBool_int]
    rw [show (15 : _root_.Int) = ((15 : Nat) : _root_.Int) from rfl,
        ltu_nat32 k 15 (by omega) (by omega)]

/-- `offs[1] = 0;` — cell 1 leaves the undefined zone, the array is born. -/
theorem offs_init_triple (l : List (Ident × Val)) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hscan bc cnt ∗ undefBytes .Freeable bo 0 32))
      offs1Init
      (.only (LocalSt (envOf bh bc bo) l (H6 bc bo cnt 1))) := by
  have haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
        (Integers.Int.repr (((1 : Nat) : _root_.Int)))) = 2 := by
    rw [cnt_addr0 ge .Signed 1 (by omega), ptrofs_unsigned_zero]
    show (0 : _root_.Int) + 2 * ((1 : Nat) : _root_.Int) = 2
    omega
  have hpeel : undefBytes .Freeable bo 2 30
      = mapsto .Mint16unsigned .Freeable bo 2 .Vundef
        ∗ undefBytes .Freeable bo 4 28 := by
    rw [show (30 : Nat) = 2 * (14 + 1) from rfl,
        undefBytes_uncons_u16 .Freeable bo 2 14 (by omega)]
    rfl
  have hsplit : undefBytes .Freeable bo 0 32
      = mapsto .Mint16unsigned .Freeable bo 2 .Vundef
        ∗ (undefBytes .Freeable bo 0 2 ∗ undefBytes .Freeable bo 4 28) := by
    rw [show (32 : Nat) = 2 + 30 from rfl, undefBytes_append .Freeable bo 0 2 30,
        show (0 : _root_.Int) + ((2 : Nat) : _root_.Int) = 2 from by omega,
        hpeel, sep_left_comm_eq]
  refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint16unsigned .Freeable bo
    (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
      (Integers.Int.repr (((1 : Nat) : _root_.Int))))
    (by decide) (by simpa only [typeof] using tushort_byvalue) ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  rw [hsplit, sep_left_comm_eq] at hH
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨.Vundef, .Vint (Integers.Int.repr 0), h1, h2, hd12, heq, ?_, ?_, ?_, ?_⟩
  · rw [haddr]; exact hm1
  · exact eval_index_lvalue (eval_offs_base bh bc bo)
      (EvalExpr.Econst_int _ _) rfl
  · exact ⟨.Vint (Integers.Int.repr 0), EvalExpr.Econst_int _ _, rfl⟩
  · intro h1' hm1' hd1'
    refine ⟨rfl, hT, ?_⟩
    show H6 bc bo cnt 1 (Heap.union h1' h2)
    have hsnoc := arrayU16_snoc .Freeable bo 2 0 (fun j => offsC cnt (j + 1)) 0
    rw [show (2 : _root_.Int) + 2 * ((0 : Nat) : _root_.Int) = 2 from by omega,
        show arrayU16 .Freeable bo 2 0 (fun j => offsC cnt (j + 1)) = emp
          from rfl, emp_sep_eq] at hsnoc
    have hgrow : mapsto .Mint16unsigned .Freeable bo 2
            (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))))
          ∗ (Hscan bc cnt
             ∗ (undefBytes .Freeable bo 0 2 ∗ undefBytes .Freeable bo 4 28))
        = H6 bc bo cnt 1 := by
      rw [hsnoc,
          show (fun j : Nat => if j = 0 then (0 : Nat) else offsC cnt (j + 1))
            = (fun j => offsC cnt (j + 1)) from by
            funext j
            by_cases hj : j = 0
            · subst hj; rfl
            · rw [if_neg hj],
          sep_left_comm_eq]
      show Hscan bc cnt
            ∗ (arrayU16 .Freeable bo 2 1 (fun j => offsC cnt (j + 1))
               ∗ (undefBytes .Freeable bo 0 2 ∗ undefBytes .Freeable bo 4 28))
           = _
      rw [show arrayU16 .Freeable bo 2 1 (fun j => offsC cnt (j + 1))
              ∗ (undefBytes .Freeable bo 0 2 ∗ undefBytes .Freeable bo 4 28)
            = undefBytes .Freeable bo 0 2
              ∗ (arrayU16 .Freeable bo 2 1 (fun j => offsC cnt (j + 1))
                 ∗ undefBytes .Freeable bo 4 28) from sep_left_comm_eq _ _ _,
          show (4 : _root_.Int) = 2 + 2 * ((1 : Nat) : _root_.Int) from by omega,
          show (28 : Nat) = 30 - 2 * 1 from by omega]
    rw [← hgrow]
    refine ⟨h1', h2, hd1', rfl, ?_, hrest⟩
    rw [haddr] at hm1'
    exact hm1'

/-- **One offsets iteration** at `len = e + 1`:
    `offs[len+1] = offs[len] + count[len];` grows the initialized prefix. -/
theorem iter6_step
    (hos : ∀ j, offsC cnt j < 65536)
    (hcb : ∀ j, cnt j < 65536)
    (hT29 : ∀ p ∈ T, p.1 ≠ _t'29)
    (hT30 : ∀ p ∈ T, p.1 ≠ _t'30)
    (e : Nat) (he : e ≤ 13) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_len, .Vint (Integers.Int.repr (((e + 1 : Nat) : _root_.Int)))) :: T)
        (H6 bc bo cnt (e + 1)))
      (.Ssequence read29 (.Ssequence read30 assign6))
      (.only (LocalSt (envOf bh bc bo)
        ((_t'30, .Vint (Integers.Int.repr ((cnt (e + 1) : Nat))))
          :: (_t'29, .Vint (Integers.Int.repr ((offsC cnt (e + 1) : Nat))))
          :: (_len, .Vint (Integers.Int.repr (((e + 1 : Nat) : _root_.Int))))
          :: T)
        (H6 bc bo cnt (e + 2)))) := by
  have haddrR : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
        (Integers.Int.repr (((e + 1 : Nat) : _root_.Int))))
      = 2 + 2 * ((e : Nat) : _root_.Int) := by
    rw [cnt_addr0 ge .Unsigned (e + 1) (by omega), ptrofs_unsigned_zero]
    show (0 : _root_.Int) + 2 * (((e + 1 : Nat)) : _root_.Int)
          = 2 + 2 * ((e : Nat) : _root_.Int)
    omega
  have haddrW : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
        (Integers.Int.repr (((e + 2 : Nat) : _root_.Int))))
      = 2 + 2 * (((e + 1 : Nat)) : _root_.Int) := by
    rw [cnt_addr0 ge .Unsigned (e + 2) (by omega), ptrofs_unsigned_zero]
    show (0 : _root_.Int) + 2 * (((e + 2 : Nat)) : _root_.Int)
          = 2 + 2 * (((e + 1 : Nat)) : _root_.Int)
    omega
  -- ── _t'29 = offs[len] ─────────────────────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'29 _
      (.Vint (Integers.Int.repr ((offsC cnt (e + 1) : Nat))))
      (fun p hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _len ≠ _t'29; decide
        · exact hT29 p hp2)
      (fun le mm hp hT' hH hag => ?_)) ?_
  · obtain ⟨hC, hOf, hdCO, heq, hscn, hof⟩ := hH
    subst heq
    obtain ⟨h0, hAS, hd0, heq0, hu0, hAS'⟩ := hof
    subst heq0
    obtain ⟨hA, hS, hdA, heqA, harr, hsuf⟩ := hAS'
    subst heqA
    have hagA : Heap.Agrees hA mm :=
      Heap.Agrees_union_left (Heap.Agrees_union_right hd0
        (Heap.Agrees_union_right hdCO hag))
    refine EvalExpr.Elvalue _ bo
      (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
        (Integers.Int.repr (((e + 1 : Nat) : _root_.Int)))) .Full _
      (eval_index_lvalue (eval_offs_base bh bc bo)
        (EvalExpr.Etempvar _len tuint _ (hT'.get List.mem_cons_self)) rfl) ?_
    refine DerefLoc.value .Mint16unsigned _ rfl ?_
    show Mem.load .Mint16unsigned mm bo _ = _
    rw [haddrR]
    exact arrayU16_load .Freeable bo (by decide) (e + 1)
      (fun j => offsC cnt (j + 1)) e (by omega) (fun j => hos (j + 1)) 2 hA mm
      harr hagA
  -- ── _t'30 = count[len] ────────────────────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'30 _
      (.Vint (Integers.Int.repr ((cnt (e + 1) : Nat))))
      (fun p hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _t'29 ≠ _t'30; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _len ≠ _t'30; decide
        · exact hT30 p hp3)
      (fun le mm hp hT' hH hag => ?_)) ?_
  · obtain ⟨hC, hOf, hdCO, heq, hscn, hof⟩ := hH
    subst heq
    exact eval_index_u16 (by decide) hscn (Heap.Agrees_union_left hag)
      (by omega : e + 1 < 16) hcb (eval_count_base bh bc bo)
      (EvalExpr.Etempvar _len tuint _
        (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self)))
      rfl (cnt_addr0 ge .Unsigned (e + 1) (by omega))
  -- ── offs[len + 1] = t'29 + t'30 ───────────────────────────────────────────
  have hpeel : undefBytes .Freeable bo (2 + 2 * (((e + 1 : Nat)) : _root_.Int))
        (30 - 2 * (e + 1))
      = mapsto .Mint16unsigned .Freeable bo
          (2 + 2 * (((e + 1 : Nat)) : _root_.Int)) .Vundef
        ∗ undefBytes .Freeable bo
            (2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2) (2 * (13 - e)) := by
    rw [show (30 - 2 * (e + 1) : Nat) = 2 * ((13 - e) + 1) from by omega,
        undefBytes_uncons_u16 .Freeable bo
          (2 + 2 * (((e + 1 : Nat)) : _root_.Int)) (13 - e) (by omega)]
  have hsnoc := arrayU16_snoc .Freeable bo 2 (e + 1)
    (fun j => offsC cnt (j + 1)) (offsC cnt (e + 1) + cnt (e + 1))
  have hfun : (fun j : Nat => if j = e + 1
        then offsC cnt (e + 1) + cnt (e + 1) else offsC cnt (j + 1))
      = (fun j => offsC cnt (j + 1)) := by
    funext j
    by_cases hj : j = e + 1
    · subst hj
      rw [if_pos rfl, offsC_succ cnt (e + 1) (by omega)]
    · rw [if_neg hj]
  refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint16unsigned .Freeable bo
    (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
      (Integers.Int.repr (((e + 2 : Nat) : _root_.Int))))
    (by decide) (by simpa only [typeof] using tushort_byvalue) ?_
  intro ev le hp m hP hag
  obtain ⟨henv, hT', hH⟩ := hP
  subst henv
  rw [show H6 bc bo cnt (e + 1)
        = mapsto .Mint16unsigned .Freeable bo
            (2 + 2 * (((e + 1 : Nat)) : _root_.Int)) .Vundef
          ∗ (Hscan bc cnt
             ∗ (undefBytes .Freeable bo 0 2
                ∗ (arrayU16 .Freeable bo 2 (e + 1) (fun j => offsC cnt (j + 1))
                   ∗ undefBytes .Freeable bo
                       (2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2)
                       (2 * (13 - e)))))
      from by
        show Hscan bc cnt
              ∗ (undefBytes .Freeable bo 0 2
                 ∗ (arrayU16 .Freeable bo 2 (e + 1) (fun j => offsC cnt (j + 1))
                    ∗ undefBytes .Freeable bo
                        (2 + 2 * (((e + 1 : Nat)) : _root_.Int))
                        (30 - 2 * (e + 1)))) = _
        rw [hpeel,
            show arrayU16 .Freeable bo 2 (e + 1) (fun j => offsC cnt (j + 1))
                ∗ (mapsto .Mint16unsigned .Freeable bo
                    (2 + 2 * (((e + 1 : Nat)) : _root_.Int)) .Vundef
                   ∗ undefBytes .Freeable bo
                       (2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2)
                       (2 * (13 - e)))
              = mapsto .Mint16unsigned .Freeable bo
                  (2 + 2 * (((e + 1 : Nat)) : _root_.Int)) .Vundef
                ∗ (arrayU16 .Freeable bo 2 (e + 1) (fun j => offsC cnt (j + 1))
                   ∗ undefBytes .Freeable bo
                       (2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2)
                       (2 * (13 - e))) from sep_left_comm_eq _ _ _,
            show undefBytes .Freeable bo 0 2
                ∗ (mapsto .Mint16unsigned .Freeable bo
                    (2 + 2 * (((e + 1 : Nat)) : _root_.Int)) .Vundef
                   ∗ (arrayU16 .Freeable bo 2 (e + 1)
                        (fun j => offsC cnt (j + 1))
                      ∗ undefBytes .Freeable bo
                          (2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2)
                          (2 * (13 - e))))
              = mapsto .Mint16unsigned .Freeable bo
                  (2 + 2 * (((e + 1 : Nat)) : _root_.Int)) .Vundef
                ∗ (undefBytes .Freeable bo 0 2
                   ∗ (arrayU16 .Freeable bo 2 (e + 1)
                        (fun j => offsC cnt (j + 1))
                      ∗ undefBytes .Freeable bo
                          (2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2)
                          (2 * (13 - e)))) from sep_left_comm_eq _ _ _,
            sep_left_comm_eq]] at hH
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨.Vundef,
          .Vint (Integers.Int.repr ((offsC cnt (e + 1) + cnt (e + 1) : Nat))),
          h1, h2, hd12, heq, ?_, ?_, ?_, ?_⟩
  · rw [haddrW]; exact hm1
  · refine eval_index_lvalue (eval_offs_base bh bc bo) ?_ rfl
    refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr (((e + 1 : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _len tuint _
        (hT'.get (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_uint_int]
    show some (Val.Vint (Integers.Int.add
              (Integers.Int.repr (((e + 1 : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_add]
  · refine ⟨.Vint (Integers.Int.add
        (Integers.Int.repr ((offsC cnt (e + 1) : Nat)))
        (Integers.Int.repr ((cnt (e + 1) : Nat)))), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Oadd _ _ _ _ _ _
        (EvalExpr.Etempvar _t'29 tushort _
          (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self)))
        (EvalExpr.Etempvar _t'30 tushort _ (hT'.get List.mem_cons_self))
        (by simp only [typeof]
            exact semBinop_add_ushort_ushort ge.genv_cenv m _ _)
    · simp only [typeof]
      rw [semCast_int_ushort]
      show some (Val.Vint (Integers.Int.zero_ext 16 (Integers.Int.add
        (Integers.Int.repr ((offsC cnt (e + 1) : Nat)))
        (Integers.Int.repr ((cnt (e + 1) : Nat)))))) = _
      rw [u32_add, zero_ext16_repr _ (by
            rw [← offsC_succ cnt (e + 1) (by omega)]
            exact hos (e + 2))]
  · intro h1' hm1' hd1'
    refine ⟨rfl, hT', ?_⟩
    show H6 bc bo cnt (e + 2) (Heap.union h1' h2)
    rw [hfun] at hsnoc
    have hgrow : mapsto .Mint16unsigned .Freeable bo
            (2 + 2 * (((e + 1 : Nat)) : _root_.Int))
            (.Vint (Integers.Int.repr
              ((offsC cnt (e + 1) + cnt (e + 1) : Nat))))
          ∗ (Hscan bc cnt
             ∗ (undefBytes .Freeable bo 0 2
                ∗ (arrayU16 .Freeable bo 2 (e + 1) (fun j => offsC cnt (j + 1))
                   ∗ undefBytes .Freeable bo
                       (2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2)
                       (2 * (13 - e)))))
        = H6 bc bo cnt (e + 2) := by
      show _ = Hscan bc cnt
                ∗ (undefBytes .Freeable bo 0 2
                   ∗ (arrayU16 .Freeable bo 2 (e + 2)
                        (fun j => offsC cnt (j + 1))
                      ∗ undefBytes .Freeable bo
                          (2 + 2 * (((e + 2 : Nat)) : _root_.Int))
                          (30 - 2 * (e + 2))))
      rw [← hsnoc,
          show (2 : _root_.Int) + 2 * (((e + 2 : Nat)) : _root_.Int)
            = 2 + 2 * (((e + 1 : Nat)) : _root_.Int) + 2 from by omega,
          show (30 - 2 * (e + 2) : Nat) = 2 * (13 - e) from by omega]
      sep_cancel
    rw [← hgrow]
    refine ⟨h1', h2, hd1', rfl, ?_, hrest⟩
    rw [haddrW] at hm1'
    exact hm1'

/-! ### The offsets loop, assembled -/

/-- Measure `n` = iterations left; `len = 15 - n`, cells `1..len` written. -/
def Inv6 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ _ : n ≤ 14,
    LocalSt (envOf bh bc bo)
      ((_len, .Vint (Integers.Int.repr (((15 - n : Nat) : _root_.Int)))) :: T)
      (H6 bc bo cnt (15 - n)) e le hp

def JAssn6 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ m, ∃ _ : n = m + 1, ∃ _ : m ≤ 13,
    LocalSt (envOf bh bc bo)
      ((_t'30, .Vint (Integers.Int.repr ((cnt (14 - m) : Nat))))
        :: (_t'29, .Vint (Integers.Int.repr ((offsC cnt (14 - m) : Nat))))
        :: (_len, .Vint (Integers.Int.repr (((14 - m : Nat) : _root_.Int))))
        :: T)
      (H6 bc bo cnt (15 - m)) e le hp

/-- Exit: all fifteen offsets computed. -/
def Post6 : Sep.Assn :=
  LocalSt (envOf bh bc bo)
    ((_len, .Vint (Integers.Int.repr (((15 : Nat) : _root_.Int)))) :: T)
    (H6 bc bo cnt 15)

theorem body6_triple
    (hos : ∀ j, offsC cnt j < 65536)
    (hcb : ∀ j, cnt j < 65536)
    (hT29 : ∀ p ∈ T, p.1 ≠ _t'29)
    (hT30 : ∀ p ∈ T, p.1 ≠ _t'30)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (Inv6 bh bc bo cnt T n)
      (.Ssequence (.Sifthenelse guard6 .Sskip .Sbreak)
        (.Ssequence read29 (.Ssequence read30 assign6)))
      { normal := JAssn6 bh bc bo cnt T n, brk := Post6 bh bc bo cnt T,
        cont := JAssn6 bh bc bo cnt T n, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hn : n ≤ 14) => ?_)
  match n with
  | 0 =>
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := guard6_eval ge (e := envOf bh bc bo) (m := mm) 15 (by omega)
          (hT'.get List.mem_cons_self)
        rw [show decide (15 < 15) = false from by
              rw [decide_eq_false_iff_not]; omega] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        exact hx
  | m + 1 =>
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_len, .Vint (Integers.Int.repr
              (((15 - (m + 1) : Nat) : _root_.Int)))) :: T)
          (H6 bc bo cnt (15 - (m + 1)))) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        have h := guard6_eval ge (e := envOf bh bc bo) (m := mm) (15 - (m + 1))
          (by omega) (hT'.get List.mem_cons_self)
        rw [show decide (15 - (m + 1) < 15) = true from by
              rw [decide_eq_true_eq]; omega] at h
        exact h
      · -- `len = 15 - (m+1) = (14 - m - 1) + 1`, so `e = 13 - m`
        have hlen : (15 - (m + 1) : Nat) = (13 - m) + 1 := by omega
        refine triple_conseq ge fe f_inflate_table
          (show Triple ge fe f_inflate_table
            (LocalSt (envOf bh bc bo)
              ((_len, .Vint (Integers.Int.repr
                  ((((13 - m) + 1 : Nat) : _root_.Int)))) :: T)
              (H6 bc bo cnt ((13 - m) + 1)))
            (.Ssequence read29 (.Ssequence read30 assign6))
            (.only (LocalSt (envOf bh bc bo)
              ((_t'30, .Vint (Integers.Int.repr ((cnt ((13 - m) + 1) : Nat))))
                :: (_t'29, .Vint (Integers.Int.repr
                     ((offsC cnt ((13 - m) + 1) : Nat))))
                :: (_len, .Vint (Integers.Int.repr
                     ((((13 - m) + 1 : Nat) : _root_.Int)))) :: T)
              (H6 bc bo cnt ((13 - m) + 2)))) from
            iter6_step ge fe bh bc bo cnt T hos hcb hT29 hT30 (13 - m) (by omega))
          (fun e le hp hx => by rw [hlen] at hx; exact hx)
          (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        refine ⟨m, rfl, by omega, ?_⟩
        rw [show ((13 - m) + 1 : Nat) = 14 - m from by omega,
            show ((13 - m) + 2 : Nat) = 15 - m from by omega] at hx
        exact hx

theorem incr6_triple
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (hT29 : ∀ p ∈ T, p.1 ≠ _t'29)
    (hT30 : ∀ p ∈ T, p.1 ≠ _t'30)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (JAssn6 bh bc bo cnt T n) incr1
      { normal := fun e le hp =>
          ∃ n', n' < n ∧ Inv6 bh bc bo cnt T n' e le hp,
        brk := Post6 bh bc bo cnt T, cont := Assn.no,
        ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (m : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnm : n = m + 1) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hm13 : m ≤ 13) => ?_)
  subst hnm
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T _ _len _
      (.Vint (Integers.Int.repr (((15 - m : Nat) : _root_.Int))))
      (fun p hp => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))) hTlen
      (fun le mm hp hT' _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr (((14 - m : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _len tuint _
        (hT'.get (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_uint_int]
    show some (Val.Vint (Integers.Int.add
              (Integers.Int.repr (((14 - m : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_add, show 14 - m + 1 = 15 - m from by omega]
  · exact ⟨m, by omega, by omega, hx.1, hx.2.1, hx.2.2⟩

/-- **Loop 6.**  All fifteen running offsets computed. -/
theorem loop6_triple
    (hos : ∀ j, offsC cnt j < 65536)
    (hcb : ∀ j, cnt j < 65536)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (hT29 : ∀ p ∈ T, p.1 ≠ _t'29)
    (hT30 : ∀ p ∈ T, p.1 ≠ _t'30)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (Inv6 bh bc bo cnt T 14) loop6
      { normal := Post6 bh bc bo cnt T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _ (Inv6 bh bc bo cnt T)
    (JAssn6 bh bc bo cnt T) _ _
    (body6_triple ge fe bh bc bo cnt T hos hcb hT29 hT30 _)
    (incr6_triple ge fe bh bc bo cnt T hTlen hT29 hT30 _) 14

/-- **Segment 6** = `offs[1] = 0;` + `len = 1;` + loop 6. -/
theorem seg6_triple
    (hos : ∀ j, offsC cnt j < 65536)
    (hcb : ∀ j, cnt j < 65536)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (hT29 : ∀ p ∈ T, p.1 ≠ _t'29)
    (hT30 : ∀ p ∈ T, p.1 ≠ _t'30)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T
        (Hscan bc cnt ∗ undefBytes .Freeable bo 0 32))
      (.Ssequence offs1Init
        (.Ssequence (.Sset _len (.Econst_int (Integers.Int.repr 1) tint)) loop6))
      { normal := Post6 bh bc bo cnt T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) T (H6 bc bo cnt 1)) _ _ _
    (offs_init_triple ge fe bh bc bo cnt T) ?_
  refine triple_seq_fwd ge fe f_inflate_table _ (Inv6 bh bc bo cnt T 14) _ _ _ ?_
    (loop6_triple ge fe bh bc bo cnt T hos hcb hTlen hT29 hT30 R)
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) T (H6 bc bo cnt 1) _len 1 hTlen)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT', hH⟩ := hx
  refine ⟨by omega, henv, ?_, ?_⟩
  · rw [show ((15 - 14 : Nat) : _root_.Int) = ((1 : Nat) : _root_.Int)
          from by omega]
    exact hT'
  · rw [show (15 - 14 : Nat) = 1 from by omega]
    exact hH

/-- **`fullBody` segment 15 alone**: `len = 1;` then loop 6.

    `seg6_triple` above proves `offs1Init ; (len = 1; loop6)` as a single
    `Ssequence`, but `fullBody`'s spine has `offs1Init` and `seg15` as **two**
    slots — `Ssequence a (Ssequence b c)`, not `Ssequence (Ssequence a b) c`.
    `Ssequence` is a constructor, not an associative operator, and a triple for
    one association does not give the other (the continuations differ:
    `Kseq b (Kseq c k)` vs `Kseq (Ssequence b c) k`).  This is the same trap the
    AST guard caught for `bwIncBlock`; the chain needs the halves separately. -/
theorem seg6b_triple
    (hos : ∀ j, offsC cnt j < 65536)
    (hcb : ∀ j, cnt j < 65536)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (hT29 : ∀ p ∈ T, p.1 ≠ _t'29)
    (hT30 : ∀ p ∈ T, p.1 ≠ _t'30)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T (H6 bc bo cnt 1))
      (.Ssequence (.Sset _len (.Econst_int (Integers.Int.repr 1) tint)) loop6)
      { normal := Post6 bh bc bo cnt T, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _ (Inv6 bh bc bo cnt T 14) _ _ _ ?_
    (loop6_triple ge fe bh bc bo cnt T hos hcb hTlen hT29 hT30 R)
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) T (H6 bc bo cnt 1) _len 1 hTlen)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT', hH⟩ := hx
  refine ⟨by omega, henv, ?_, ?_⟩
  · rw [show ((15 - 14 : Nat) : _root_.Int) = ((1 : Nat) : _root_.Int)
          from by omega]
    exact hT'
  · rw [show (15 - 14 : Nat) = 1 from by omega]
    exact hH

end Offs6

/-! ## §12 The sort loop (inftrees.c:155-156; AST 792-860)

`for (sym = 0; sym < codes; sym++) if (lens[sym] != 0) work[offs[lens[sym]]++] = sym;`

The safety-critical write of the whole prologue: `work`'s index is a *value
read out of memory*, so its bound is a theorem — `Model.sort_write_lt_nlive`
— not a check.  clightgen reads `lens[sym]` three times
(`_t'26`, `_t'28`, `_t'27`; no store between, so all three agree) and keeps
the old offset in `_t'4`. -/

/-- The `offs` contents after `s` symbols: the base offset plus the symbols of
    that length already placed. -/
def sortOffs (cnt : Nat → Nat) (lensF : Nat → Nat) (s l : Nat) : Nat :=
  offsC cnt l + InflateTable.Model.count lensF s l

/-- All fifteen offset cells, at arbitrary contents (the suffix is empty at
    `k = 15`, so this is the two-zone form the sort loop keeps). -/
abbrev HoffsAt (bo : Block) (g : Nat → Nat) : HProp :=
  undefBytes .Freeable bo 0 2
  ∗ arrayU16 .Freeable bo 2 15 (fun j => g (j + 1))

/-- `offs`'s 32 bytes as one concrete run.

    **Why `offs[0]` is `Undef` forever.**  The program's first write to `offs`
    is `offs[1] = 0` (inftrees.c:150) and the loops that follow only ever touch
    `offs[1..15]`, so cell 0 keeps the `Undef` bytes `Mem.alloc` left.  That is
    why `HLoop` carries `HoffsAt` and not a full `arrayU16 .Freeable bo 0 16`:
    the latter is **unsatisfiable** here, since `arrayU16`'s elements are
    `mapsto … (.Vint …)` and undefined bytes decode to `Vundef`.  `offs` is dead
    after the sort loop anyway — it is carried only so `return` can free it. -/
def offsBytes (g : Nat → Nat) : List MemVal :=
  List.replicate 2 .Undef ++ u16Bytes (fun j => g (j + 1)) 15

theorem offsBytes_length (g : Nat → Nat) : (offsBytes g).length = 32 := by
  show (List.replicate 2 (MemVal.Undef)
        ++ u16Bytes (fun j => g (j + 1)) 15).length = 32
  rw [List.length_append, List.length_replicate, u16Bytes_length]

/-- …and the byte-run form the `return` needs (`return_const_triple` takes the
    three locals as raw runs with length side conditions). -/
theorem HoffsAt_bytes (bo : Block) (g : Nat → Nat) :
    HoffsAt bo g = bytesPtsTo bo .Freeable 0 (offsBytes g) := by
  show undefBytes .Freeable bo 0 2 ∗ arrayU16 .Freeable bo 2 15 (fun j => g (j + 1))
    = bytesPtsTo bo .Freeable 0
        (List.replicate 2 (MemVal.Undef) ++ u16Bytes (fun j => g (j + 1)) 15)
  rw [bytesPtsTo_append, List.length_replicate,
      arrayU16_bytes .Freeable bo 2 (fun j => g (j + 1)) (by decide) 15]
  rfl

theorem Hoffs_eq_HoffsAt (bo : Block) (cnt : Nat → Nat) :
    Hoffs bo cnt 15 = HoffsAt bo (offsC cnt) := by
  show undefBytes .Freeable bo 0 2
        ∗ (arrayU16 .Freeable bo 2 15 (fun j => offsC cnt (j + 1))
           ∗ undefBytes .Freeable bo (2 + 2 * ((15 : Nat) : _root_.Int))
               (30 - 2 * 15)) = _
  rw [show (30 - 2 * 15 : Nat) = 0 from by omega, undefBytes_zero, sep_emp_eq]

section SortLoop

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (pl pw : Permission) (lensB workB : Block)
variable (lensO workO : Integers.Ptrofs)
variable (codes : Nat) (lensF workF : Nat → Nat)
variable (cnt : Nat → Nat) (T : List (Ident × Val))

/-- **What the sort loop records about `work`'s contents.**  Safety of the
    loop itself needs only that its writes land in bounds, but the *main*
    loop needs to know what is there — so the invariant also carries "every
    live symbol below `s` sits at its own slot".  `Model.posOf` is exactly the
    C's `offs[lens[sym]]++`, so the step is `if_pos rfl` plus `posOf_ne` to
    see that the new write misses every earlier slot. -/
abbrev Placed (lensF workF : Nat → Nat) (codes s : Nat) : Prop :=
  ∀ t, t < s → lensF t ≠ 0 →
    workF (InflateTable.Model.posOf lensF codes t) = t

/-- The sort loop's footprint: `lens` (read), `work` (written), `offs`. -/
abbrev H7 (bo : Block) (pl pw : Permission) (lensB workB : Block)
    (lensO workO : Integers.Ptrofs) (codes : Nat) (lensF workF g : Nat → Nat) :
    HProp :=
  arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
  ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) codes workF
     ∗ HoffsAt bo g)

/-- **The placing branch**, for a symbol with nonzero length `d + 1`: read the
    offset, bump it, and store the symbol into `work` at the OLD offset.

    The `work` index is a value read out of memory; `Model.sort_write_lt_nlive`
    is what bounds it. -/
theorem sort_place_step
    (hpl : permOrder pl .Readable = true)
    (hpw : permOrder pw .Writable = true)
    (hlb : ∀ j, lensF j < 65536)
    (hwb : ∀ j, workF j < 65536)
    (hgb : ∀ j, sortOffs cnt lensF s j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hcnt : cnt = fun j => InflateTable.Model.count lensF codes j)
    (hs : s < codes) (d : Nat) (hd : lensF s = d + 1) (hd14 : d ≤ 14)
    (l₀ : List (Ident × Val))
    (hmemL : (_lens, .Vptr lensB lensO) ∈ l₀)
    (hmemW : (_work, .Vptr workB workO) ∈ l₀)
    (hmemS : (_sym, .Vint (Integers.Int.repr ((s : _root_.Int)))) ∈ l₀)
    (hT4 : ∀ p ∈ l₀, p.1 ≠ _t'4)
    (hT27 : ∀ p ∈ l₀, p.1 ≠ _t'27)
    (hT28 : ∀ p ∈ l₀, p.1 ≠ _t'28) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l₀
        (H7 bo pl pw lensB workB lensO workO codes lensF workF
          (sortOffs cnt lensF s)))
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Sset _t'28 (.Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
              (.Etempvar _sym tuint) (tptr tushort)) tushort))
            (.Sset _t'4 (.Ederef (.Ebinop .Oadd (.Evar _offs (tarray tushort 16))
              (.Etempvar _t'28 tushort) (tptr tushort)) tushort)))
          (.Ssequence
            (.Sset _t'27 (.Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
              (.Etempvar _sym tuint) (tptr tushort)) tushort))
            (.Sassign
              (.Ederef (.Ebinop .Oadd (.Evar _offs (tarray tushort 16))
                (.Etempvar _t'27 tushort) (tptr tushort)) tushort)
              (.Ebinop .Oadd (.Etempvar _t'4 tushort)
                (.Econst_int (Integers.Int.repr 1) tint) tint))))
        (.Sassign
          (.Ederef (.Ebinop .Oadd (.Etempvar _work (tptr tushort))
            (.Etempvar _t'4 tushort) (tptr tushort)) tushort)
          (.Ecast (.Etempvar _sym tuint) tushort)))
      (.only (LocalSt (envOf bh bc bo)
        ((_t'27, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
          :: (_t'4, .Vint (Integers.Int.repr
               ((sortOffs cnt lensF s (d + 1) : Nat))))
          :: (_t'28, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
          :: l₀)
        (H7 bo pl pw lensB workB lensO workO codes lensF
          (fun j => if j = sortOffs cnt lensF s (d + 1) then s else workF j)
          (sortOffs cnt lensF (s + 1))))) := by
  -- the write index and its bound (the safety-critical fact)
  have hidx_lt : sortOffs cnt lensF s (d + 1) < codes := by
    have hlt := InflateTable.Model.sort_write_lt_nlive lensF codes (d + 1)
      (InflateTable.Model.count lensF s (d + 1)) hlens15 (by omega) (by omega)
      (by
        rw [← hd]
        exact InflateTable.Model.count_prefix_lt lensF s codes (lensF s) hs rfl)
    have hnl := InflateTable.Model.nlive_le_codes lensF codes
    have hoff : offsC cnt (d + 1) = InflateTable.Model.offs lensF codes (d + 1) := by
      rw [hcnt]; exact offsC_count_eq lensF codes (d + 1)
    rw [sortOffs, hoff]
    omega
  -- addresses
  have haddrL : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Unsigned lensO
        (Integers.Int.repr ((s : _root_.Int))))
      = Integers.Ptrofs.unsigned lensO + 2 * (s : _root_.Int) :=
    u16Ofs_unsigned ge.genv_cenv .Unsigned lensO s (by omega)
      (no_wrap_mono lensO codes s hnoL (by omega))
  have haddrO : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
        (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
      = 2 + 2 * ((d : Nat) : _root_.Int) := by
    rw [cnt_addr0 ge .Signed (d + 1) (by omega), ptrofs_unsigned_zero]
    show (0 : _root_.Int) + 2 * (((d + 1 : Nat)) : _root_.Int) = _
    omega
  have haddrW : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Signed workO
        (Integers.Int.repr ((sortOffs cnt lensF s (d + 1) : Nat))))
      = Integers.Ptrofs.unsigned workO
        + 2 * ((sortOffs cnt lensF s (d + 1) : Nat) : _root_.Int) :=
    u16Ofs_unsigned ge.genv_cenv .Signed workO (sortOffs cnt lensF s (d + 1))
      (by omega) (no_wrap_mono workO codes _ hnoW (by omega))
  -- reading `lens[sym]`, twice
  have hreadL : ∀ (lx : List (Ident × Val)) (le : TempEnv) (m : Mem) (hp : Heap),
      TempsHold lx le → ((_lens, .Vptr lensB lensO) ∈ lx) →
      ((_sym, .Vint (Integers.Int.repr ((s : _root_.Int)))) ∈ lx) →
      H7 bo pl pw lensB workB lensO workO codes lensF workF
        (sortOffs cnt lensF s) hp → Heap.Agrees hp m →
      EvalExpr ge (envOf bh bc bo) le m
        (.Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
          (.Etempvar _sym tuint) (tptr tushort)) tushort)
        (.Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int))) := by
    intro lx le m hp hTx hmL hmS hH hag
    obtain ⟨hL, hR, hdLR, heq, harrL, hrest⟩ := hH
    subst heq
    have h := eval_index_u16 (e := envOf bh bc bo) hpl harrL
      (Heap.Agrees_union_left hag) hs hlb
      (EvalExpr.Etempvar _lens (tptr tushort) _ (hTx.get hmL))
      (EvalExpr.Etempvar _sym tuint _ (hTx.get hmS)) rfl haddrL
    rw [hd] at h
    exact h
  -- ── the two mid-states of the statement, spelled out ─────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'27, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
        :: (_t'4, .Vint (Integers.Int.repr
             ((sortOffs cnt lensF s (d + 1) : Nat))))
        :: (_t'28, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
        :: l₀)
      (H7 bo pl pw lensB workB lensO workO codes lensF workF
        (sortOffs cnt lensF (s + 1)))) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'4, .Vint (Integers.Int.repr
             ((sortOffs cnt lensF s (d + 1) : Nat))))
          :: (_t'28, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
          :: l₀)
        (H7 bo pl pw lensB workB lensO workO codes lensF workF
          (sortOffs cnt lensF s))) _ _ _ ?_ ?_
    · -- _t'28 = lens[sym]; _t'4 = offs[_t'28]
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'28, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
            :: l₀)
          (H7 bo pl pw lensB workB lensO workO codes lensF workF
            (sortOffs cnt lensF s))) _ _ _
        (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'28 _
          (.Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
          (fun p hp => hp) hT28
          (fun le m hp hTx hH hag =>
            hreadL _ le m hp hTx hmemL hmemS hH hag)) ?_
      refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
        _t'4 _ (.Vint (Integers.Int.repr ((sortOffs cnt lensF s (d + 1) : Nat))))
        (fun p hp => hp)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _t'28 ≠ _t'4; decide
          · exact hT4 p hp2)
        (fun le m hp hTx hH hag => ?_)
      obtain ⟨hL, hWO, hdx, heq, harrL, hWO'⟩ := hH
      subst heq
      obtain ⟨hW, hOf, hdx2, heq2, harrW, hof⟩ := hWO'
      subst heq2
      obtain ⟨h0, hA, hdx3, heq3, hu0, harrO⟩ := hof
      subst heq3
      have hagO : Heap.Agrees hA m :=
        Heap.Agrees_union_right hdx3
          (Heap.Agrees_union_right hdx2 (Heap.Agrees_union_right hdx hag))
      refine EvalExpr.Elvalue _ bo
        (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
          (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int))) .Full _
        (eval_index_lvalue (eval_offs_base bh bc bo)
          (EvalExpr.Etempvar _t'28 tushort _ (hTx.get List.mem_cons_self))
          rfl) ?_
      refine DerefLoc.value .Mint16unsigned _ rfl ?_
      show Mem.load .Mint16unsigned m bo _ = _
      rw [haddrO]
      exact arrayU16_load .Freeable bo (by decide) 15
        (fun j => sortOffs cnt lensF s (j + 1)) d (by omega)
        (fun j => hgb (j + 1)) 2 hA m harrO hagO
    · -- _t'27 = lens[sym]; offs[_t'27] = _t'4 + 1
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'27, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
            :: (_t'4, .Vint (Integers.Int.repr
                 ((sortOffs cnt lensF s (d + 1) : Nat))))
            :: (_t'28, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
            :: l₀)
          (H7 bo pl pw lensB workB lensO workO codes lensF workF
            (sortOffs cnt lensF s))) _ _ _
        (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'27 _
          (.Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
          (fun p hp => hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _t'4 ≠ _t'27; decide
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · show _t'28 ≠ _t'27; decide
            · exact hT27 p hp3)
          (fun le m hp hTx hH hag =>
            hreadL _ le m hp hTx
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemL))
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemS))
              hH hag)) ?_
      -- the offs store
      have hsplitO := arrayU16_split .Freeable bo 2 15
        (fun j => sortOffs cnt lensF s (j + 1)) d (by omega)
      have hupdO := arrayU16_update .Freeable bo 2 15
        (fun j => sortOffs cnt lensF s (j + 1)) d
        (sortOffs cnt lensF s (d + 1) + 1) (by omega)
      have hfunO : (fun j : Nat => if j = d
            then sortOffs cnt lensF s (d + 1) + 1
            else sortOffs cnt lensF s (j + 1))
          = (fun j => sortOffs cnt lensF (s + 1) (j + 1)) := by
        funext j
        by_cases hj : j = d
        · rw [if_pos hj, hj]
          show _ = offsC cnt (d + 1)
                    + InflateTable.Model.count lensF (s + 1) (d + 1)
          rw [InflateTable.Model.count_succ, if_pos hd]
          show offsC cnt (d + 1)
                + InflateTable.Model.count lensF s (d + 1) + 1 = _
          omega
        · rw [if_neg hj]
          show offsC cnt (j + 1)
                + InflateTable.Model.count lensF s (j + 1)
             = offsC cnt (j + 1)
                + InflateTable.Model.count lensF (s + 1) (j + 1)
          rw [InflateTable.Model.count_succ,
              if_neg (fun hc => hj (by omega : j = d))]
      refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint16unsigned
        .Freeable bo
        (idxOfs ge.genv_cenv tushort .Signed Integers.Ptrofs.zero
          (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
        (by decide) (by simpa only [typeof] using tushort_byvalue) ?_
      intro ev le hp m hP hag
      obtain ⟨henv, hTx, hH⟩ := hP
      subst henv
      rw [show H7 bo pl pw lensB workB lensO workO codes lensF workF
              (sortOffs cnt lensF s)
            = mapsto .Mint16unsigned .Freeable bo
                (2 + 2 * ((d : Nat) : _root_.Int))
                (.Vint (Integers.Int.repr
                  ((sortOffs cnt lensF s (d + 1) : Nat))))
              ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
                 ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) codes
                      workF
                    ∗ (undefBytes .Freeable bo 0 2
                       ∗ arrayOfRest
                           (u16elt .Freeable bo
                             (fun j => sortOffs cnt lensF s (j + 1)))
                           2 2 15 d)))
          from by
            show arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
                  ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) codes
                       workF
                     ∗ (undefBytes .Freeable bo 0 2
                        ∗ arrayU16 .Freeable bo 2 15
                            (fun j => sortOffs cnt lensF s (j + 1)))) = _
            rw [hsplitO]
            sep_cancel] at hH
      obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
      refine ⟨.Vint (Integers.Int.repr ((sortOffs cnt lensF s (d + 1) : Nat))),
              .Vint (Integers.Int.repr
                ((sortOffs cnt lensF s (d + 1) + 1 : Nat))),
              h1, h2, hd12, heq, ?_, ?_, ?_, ?_⟩
      · rw [haddrO]; exact hm1
      · exact eval_index_lvalue (eval_offs_base bh bc bo)
          (EvalExpr.Etempvar _t'27 tushort _ (hTx.get List.mem_cons_self)) rfl
      · refine ⟨.Vint (Integers.Int.add
            (Integers.Int.repr ((sortOffs cnt lensF s (d + 1) : Nat)))
            (Integers.Int.repr 1)), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Oadd _ _ _ _ (.Vint (Integers.Int.repr 1)) _
            (EvalExpr.Etempvar _t'4 tushort _
              (hTx.get (List.mem_cons_of_mem _ List.mem_cons_self)))
            (EvalExpr.Econst_int _ _)
            (by simp only [typeof]; exact semBinop_add_ushort_int _ _ _ _)
        · simp only [typeof]
          rw [semCast_int_ushort]
          show some (Val.Vint (Integers.Int.zero_ext 16 (Integers.Int.add
            (Integers.Int.repr ((sortOffs cnt lensF s (d + 1) : Nat)))
            (Integers.Int.repr (((1 : Nat) : _root_.Int)))))) = _
          rw [u32_add, zero_ext16_repr _ (by
                have h := hgb (d + 1)
                have hb := hidx_lt
                omega)]
      · intro h1' hm1' hd1'
        refine ⟨rfl, hTx, ?_⟩
        show H7 bo pl pw lensB workB lensO workO codes lensF workF
              (sortOffs cnt lensF (s + 1)) (Heap.union h1' h2)
        rw [hfunO] at hupdO
        rw [show H7 bo pl pw lensB workB lensO workO codes lensF workF
                (sortOffs cnt lensF (s + 1))
              = mapsto .Mint16unsigned .Freeable bo
                  (2 + 2 * ((d : Nat) : _root_.Int))
                  (.Vint (Integers.Int.repr
                    ((sortOffs cnt lensF s (d + 1) + 1 : Nat))))
                ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes
                     lensF
                   ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) codes
                        workF
                      ∗ (undefBytes .Freeable bo 0 2
                         ∗ arrayOfRest
                             (u16elt .Freeable bo
                               (fun j => sortOffs cnt lensF s (j + 1)))
                             2 2 15 d)))
            from by
              show arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
                    ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) codes
                         workF
                       ∗ (undefBytes .Freeable bo 0 2
                          ∗ arrayU16 .Freeable bo 2 15
                              (fun j => sortOffs cnt lensF (s + 1) (j + 1)))) = _
              rw [hupdO]
              sep_cancel]
        refine ⟨h1', h2, hd1', rfl, ?_, hrest⟩
        rw [haddrO] at hm1'
        exact hm1'
  · -- ── work[_t'4] = (ushort) sym ──────────────────────────────────────────
    have hsplitW := arrayU16_split pw workB (Integers.Ptrofs.unsigned workO)
      codes workF (sortOffs cnt lensF s (d + 1)) hidx_lt
    have hupdW := arrayU16_update pw workB (Integers.Ptrofs.unsigned workO)
      codes workF (sortOffs cnt lensF s (d + 1)) s hidx_lt
    refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint16unsigned pw workB
      (idxOfs ge.genv_cenv tushort .Signed workO
        (Integers.Int.repr ((sortOffs cnt lensF s (d + 1) : Nat))))
      hpw (by simpa only [typeof] using tushort_byvalue) ?_
    intro ev le hp m hP hag
    obtain ⟨henv, hTx, hH⟩ := hP
    subst henv
    rw [show H7 bo pl pw lensB workB lensO workO codes lensF workF
            (sortOffs cnt lensF (s + 1))
          = mapsto .Mint16unsigned pw workB
              (Integers.Ptrofs.unsigned workO
                + 2 * ((sortOffs cnt lensF s (d + 1) : Nat) : _root_.Int))
              (.Vint (Integers.Int.repr
                ((workF (sortOffs cnt lensF s (d + 1)) : Nat))))
            ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
               ∗ (arrayOfRest (u16elt pw workB workF) 2
                    (Integers.Ptrofs.unsigned workO) codes
                    (sortOffs cnt lensF s (d + 1))
                  ∗ HoffsAt bo (sortOffs cnt lensF (s + 1))))
        from by
          show arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
                ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) codes
                     workF
                   ∗ HoffsAt bo (sortOffs cnt lensF (s + 1))) = _
          rw [hsplitW]
          sep_cancel] at hH
    obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
    refine ⟨.Vint (Integers.Int.repr
              ((workF (sortOffs cnt lensF s (d + 1)) : Nat))),
            .Vint (Integers.Int.repr ((s : Nat))),
            h1, h2, hd12, heq, ?_, ?_, ?_, ?_⟩
    · rw [haddrW]; exact hm1
    · exact eval_index_lvalue
        (EvalExpr.Etempvar _work (tptr tushort) _
          (hTx.get (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemW)))))
        (EvalExpr.Etempvar _t'4 tushort _
          (hTx.get (List.mem_cons_of_mem _ List.mem_cons_self))) rfl
    · refine ⟨.Vint (Integers.Int.repr ((s : Nat))), ?_, ?_⟩
      · refine EvalExpr.Ecast _ _ (.Vint (Integers.Int.repr ((s : _root_.Int)))) _
          (EvalExpr.Etempvar _sym tuint _
            (hTx.get (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemS))))) ?_
        show some (Val.Vint (Integers.Int.zero_ext 16
              (Integers.Int.repr ((s : _root_.Int))))) = _
        rw [zero_ext16_repr s (by omega)]
      · simp only [typeof]
        show some (Val.Vint (Integers.Int.zero_ext 16
              (Integers.Int.repr ((s : Nat))))) = _
        rw [zero_ext16_repr s (by omega)]
    · intro h1' hm1' hd1'
      refine ⟨rfl, hTx, ?_⟩
      show H7 bo pl pw lensB workB lensO workO codes lensF
            (fun j => if j = sortOffs cnt lensF s (d + 1) then s else workF j)
            (sortOffs cnt lensF (s + 1)) (Heap.union h1' h2)
      rw [show H7 bo pl pw lensB workB lensO workO codes lensF
              (fun j => if j = sortOffs cnt lensF s (d + 1) then s else workF j)
              (sortOffs cnt lensF (s + 1))
            = mapsto .Mint16unsigned pw workB
                (Integers.Ptrofs.unsigned workO
                  + 2 * ((sortOffs cnt lensF s (d + 1) : Nat) : _root_.Int))
                (.Vint (Integers.Int.repr ((s : Nat))))
              ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
                 ∗ (arrayOfRest (u16elt pw workB workF) 2
                      (Integers.Ptrofs.unsigned workO) codes
                      (sortOffs cnt lensF s (d + 1))
                    ∗ HoffsAt bo (sortOffs cnt lensF (s + 1))))
          from by
            show arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) codes lensF
                  ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) codes
                       (fun j => if j = sortOffs cnt lensF s (d + 1) then s
                                 else workF j)
                     ∗ HoffsAt bo (sortOffs cnt lensF (s + 1))) = _
            rw [hupdW]
            sep_cancel]
      refine ⟨h1', h2, hd1', rfl, ?_, hrest⟩
      rw [haddrW] at hm1'
      exact hm1'

/-! ### The sort loop, assembled

`sortOffs` is the loop's offset model; the `work` contents are existential
(safety needs only that the writes land in bounds, not what they store). -/

/-- One full iteration: read `lens[sym]`, and place the symbol if nonzero. -/
theorem iter7_step
    (hpl : permOrder pl .Readable = true)
    (hpw : permOrder pw .Writable = true)
    (hlb : ∀ j, lensF j < 65536)
    (hwb : ∀ j, workF j < 65536)
    (hgb : ∀ j, sortOffs cnt lensF s j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hcnt : cnt = fun j => InflateTable.Model.count lensF codes j)
    (hs : s < codes) (hplaced : Placed lensF workF codes s)
    (l₀ : List (Ident × Val))
    (hmemL : (_lens, .Vptr lensB lensO) ∈ l₀)
    (hmemW : (_work, .Vptr workB workO) ∈ l₀)
    (hmemS : (_sym, .Vint (Integers.Int.repr ((s : _root_.Int)))) ∈ l₀)
    (hT4 : ∀ p ∈ l₀, p.1 ≠ _t'4)
    (hT26 : ∀ p ∈ l₀, p.1 ≠ _t'26)
    (hT27 : ∀ p ∈ l₀, p.1 ≠ _t'27)
    (hT28 : ∀ p ∈ l₀, p.1 ≠ _t'28) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l₀
        (H7 bo pl pw lensB workB lensO workO codes lensF workF
          (sortOffs cnt lensF s)))
      (.Ssequence
        (.Sset _t'26 (.Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
          (.Etempvar _sym tuint) (tptr tushort)) tushort))
        (.Sifthenelse (.Ebinop .One (.Etempvar _t'26 tushort)
            (.Econst_int (Integers.Int.repr 0) tint) tint)
          (.Ssequence
            (.Ssequence
              (.Ssequence
                (.Sset _t'28 (.Ederef (.Ebinop .Oadd
                  (.Etempvar _lens (tptr tushort))
                  (.Etempvar _sym tuint) (tptr tushort)) tushort))
                (.Sset _t'4 (.Ederef (.Ebinop .Oadd
                  (.Evar _offs (tarray tushort 16))
                  (.Etempvar _t'28 tushort) (tptr tushort)) tushort)))
              (.Ssequence
                (.Sset _t'27 (.Ederef (.Ebinop .Oadd
                  (.Etempvar _lens (tptr tushort))
                  (.Etempvar _sym tuint) (tptr tushort)) tushort))
                (.Sassign
                  (.Ederef (.Ebinop .Oadd (.Evar _offs (tarray tushort 16))
                    (.Etempvar _t'27 tushort) (tptr tushort)) tushort)
                  (.Ebinop .Oadd (.Etempvar _t'4 tushort)
                    (.Econst_int (Integers.Int.repr 1) tint) tint))))
            (.Sassign
              (.Ederef (.Ebinop .Oadd (.Etempvar _work (tptr tushort))
                (.Etempvar _t'4 tushort) (tptr tushort)) tushort)
              (.Ecast (.Etempvar _sym tuint) tushort)))
          .Sskip))
      (.only (fun e le hp => ∃ wF : Nat → Nat, ∃ _ : ∀ j, wF j < 65536,
        ∃ _ : Placed lensF wF codes (s + 1),
        ∃ lx : List (Ident × Val), ∃ _ : ∀ p ∈ l₀, p ∈ lx,
          LocalSt (envOf bh bc bo) lx
            (H7 bo pl pw lensB workB lensO workO codes lensF wF
              (sortOffs cnt lensF (s + 1))) e le hp)) := by
  -- the C's write index IS `Model.posOf`
  have hpos : ∀ d : Nat, lensF s = d + 1 →
      sortOffs cnt lensF s (d + 1) = InflateTable.Model.posOf lensF codes s := by
    intro d hd
    show offsC cnt (d + 1) + InflateTable.Model.count lensF s (d + 1)
      = InflateTable.Model.offs lensF codes (lensF s)
        + InflateTable.Model.count lensF s (lensF s)
    rw [hd, hcnt, offsC_count_eq lensF codes (d + 1)]
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'26, .Vint (Integers.Int.repr ((lensF s : Nat)))) :: l₀)
      (H7 bo pl pw lensB workB lensO workO codes lensF workF
        (sortOffs cnt lensF s))) _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _ _t'26 _
      (.Vint (Integers.Int.repr ((lensF s : Nat))))
      (fun p hp => hp) hT26
      (fun le m hp hTx hH hag => by
        obtain ⟨hL, hR, hdLR, heq, harrL, hrest⟩ := hH
        subst heq
        exact eval_index_u16 (e := envOf bh bc bo) hpl harrL
          (Heap.Agrees_union_left hag) hs hlb
          (EvalExpr.Etempvar _lens (tptr tushort) _ (hTx.get hmemL))
          (EvalExpr.Etempvar _sym tuint _ (hTx.get hmemS)) rfl
          (u16Ofs_unsigned ge.genv_cenv .Unsigned lensO s (by omega)
            (no_wrap_mono lensO codes s hnoL (by omega))))) ?_
  by_cases hnz : lensF s = 0
  · -- zero length: nothing placed, the offsets are unchanged
    refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hTx _ _ => ?_) ?_
    · have h := ne0_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
        _t'26 (lensF s) (hlb _) (hTx.get List.mem_cons_self)
      rw [show decide (lensF s ≠ 0) = false from by
            rw [decide_eq_false_iff_not]; exact fun hne => hne hnz] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_skip ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      obtain ⟨henv, hTx, hH⟩ := hx
      refine ⟨workF, hwb,
        (fun t ht hnzt => by
          rcases Nat.lt_or_ge t s with h | h
          · exact hplaced t h hnzt
          · exact absurd hnz (by rw [show s = t from by omega]; exact hnzt)),
        (_t'26, .Vint (Integers.Int.repr ((lensF s : Nat)))) :: l₀,
        fun p hp => List.mem_cons_of_mem _ hp, henv, hTx, ?_⟩
      -- the offsets do not move: only cells `1..15` are observed, and this
      -- symbol has length 0
      rw [show H7 bo pl pw lensB workB lensO workO codes lensF workF
              (sortOffs cnt lensF (s + 1))
            = H7 bo pl pw lensB workB lensO workO codes lensF workF
              (sortOffs cnt lensF s) from by
            show _ ∗ (_ ∗ (undefBytes .Freeable bo 0 2
                    ∗ arrayU16 .Freeable bo 2 15
                        (fun j => sortOffs cnt lensF (s + 1) (j + 1)))) = _
            rw [show (fun j => sortOffs cnt lensF (s + 1) (j + 1))
                  = (fun j => sortOffs cnt lensF s (j + 1)) from by
                  funext j
                  show offsC cnt (j + 1)
                        + InflateTable.Model.count lensF (s + 1) (j + 1)
                     = offsC cnt (j + 1)
                        + InflateTable.Model.count lensF s (j + 1)
                  rw [InflateTable.Model.count_succ,
                      if_neg (show ¬(lensF s = j + 1) from by omega)]]]
      exact hH
  · -- nonzero: place it
    obtain ⟨d, hd⟩ : ∃ d, lensF s = d + 1 := ⟨lensF s - 1, by omega⟩
    refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hTx _ _ => ?_) ?_
    · have h := ne0_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
        _t'26 (lensF s) (hlb _) (hTx.get List.mem_cons_self)
      rw [show decide (lensF s ≠ 0) = true from by
            rw [decide_eq_true_eq]; exact hnz] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (sort_place_step ge fe bh bc bo pl pw lensB workB lensO workO codes
          lensF workF cnt hpl hpw hlb hwb hgb hlens15 hc16 hnoL hnoW
          hcnt hs d hd (by have := hlens15 s hs; omega)
          ((_t'26, .Vint (Integers.Int.repr ((lensF s : Nat)))) :: l₀)
          (List.mem_cons_of_mem _ hmemL) (List.mem_cons_of_mem _ hmemW)
          (List.mem_cons_of_mem _ hmemS)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _t'26 ≠ _t'4; decide
            · exact hT4 p hp2)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _t'26 ≠ _t'27; decide
            · exact hT27 p hp2)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _t'26 ≠ _t'28; decide
            · exact hT28 p hp2))
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      exact ⟨fun j => if j = sortOffs cnt lensF s (d + 1) then s else workF j,
        fun j => by
          show (if j = sortOffs cnt lensF s (d + 1) then s else workF j) < 65536
          by_cases hj : j = sortOffs cnt lensF s (d + 1)
          · rw [if_pos hj]; omega
          · rw [if_neg hj]; exact hwb j,
        (fun t ht hnzt => by
          show (if InflateTable.Model.posOf lensF codes t
                  = sortOffs cnt lensF s (d + 1)
                then s else workF _) = t
          rw [hpos d hd]
          rcases Nat.lt_or_ge t s with h | h
          · rw [if_neg (InflateTable.Model.posOf_ne lensF codes t s h hs hnzt
                  hnz)]
            exact hplaced t h hnzt
          · have hts : t = s := by omega
            subst hts
            rw [if_pos rfl]),
        (_t'27, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
          :: (_t'4, .Vint (Integers.Int.repr
               ((sortOffs cnt lensF s (d + 1) : Nat))))
          :: (_t'28, .Vint (Integers.Int.repr (((d + 1 : Nat)) : _root_.Int)))
          :: (_t'26, .Vint (Integers.Int.repr ((lensF s : Nat)))) :: l₀,
        fun p hp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))), hx⟩

/-! ### The sort loop, assembled

The `work` contents and the extra temporaries are existentially quantified in
the invariant: safety needs only that the writes land in bounds. -/

abbrev guard7 : Expr :=
  .Ebinop .Olt (.Etempvar _sym tuint) (.Etempvar _codes tuint) tint

abbrev iter7 : Stmt :=
  .Ssequence
    (.Sset _t'26 (.Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
      (.Etempvar _sym tuint) (tptr tushort)) tushort))
    (.Sifthenelse (.Ebinop .One (.Etempvar _t'26 tushort)
        (.Econst_int (Integers.Int.repr 0) tint) tint)
      (.Ssequence
        (.Ssequence
          (.Ssequence
            (.Sset _t'28 (.Ederef (.Ebinop .Oadd
              (.Etempvar _lens (tptr tushort))
              (.Etempvar _sym tuint) (tptr tushort)) tushort))
            (.Sset _t'4 (.Ederef (.Ebinop .Oadd
              (.Evar _offs (tarray tushort 16))
              (.Etempvar _t'28 tushort) (tptr tushort)) tushort)))
          (.Ssequence
            (.Sset _t'27 (.Ederef (.Ebinop .Oadd
              (.Etempvar _lens (tptr tushort))
              (.Etempvar _sym tuint) (tptr tushort)) tushort))
            (.Sassign
              (.Ederef (.Ebinop .Oadd (.Evar _offs (tarray tushort 16))
                (.Etempvar _t'27 tushort) (tptr tushort)) tushort)
              (.Ebinop .Oadd (.Etempvar _t'4 tushort)
                (.Econst_int (Integers.Int.repr 1) tint) tint))))
        (.Sassign
          (.Ederef (.Ebinop .Oadd (.Etempvar _work (tptr tushort))
            (.Etempvar _t'4 tushort) (tptr tushort)) tushort)
          (.Ecast (.Etempvar _sym tuint) tushort)))
      .Sskip)

abbrev loop7 : Stmt :=
  .Sloop (.Ssequence (.Sifthenelse guard7 .Sskip .Sbreak) iter7) incr2

/-- The loop state after `s` symbols: some `work` contents (safety does not
    constrain them), the offsets at `sortOffs … s`, tracked list normalized. -/
def St7 (s : Nat) : Sep.Assn := fun e le hp =>
  ∃ wF : Nat → Nat, ∃ _ : ∀ j, wF j < 65536,
    ∃ _ : Placed lensF wF codes s,
    LocalSt (envOf bh bc bo)
      ((_sym, .Vint (Integers.Int.repr ((s : _root_.Int)))) :: T)
      (H7 bo pl pw lensB workB lensO workO codes lensF wF
        (sortOffs cnt lensF s)) e le hp

/-- Mid-state: the iteration ran, leaving an unspecified longer tracked list. -/
def Mid7 (s : Nat) : Sep.Assn := fun e le hp =>
  ∃ wF : Nat → Nat, ∃ _ : ∀ j, wF j < 65536,
    ∃ _ : Placed lensF wF codes (s + 1),
    ∃ lx : List (Ident × Val),
      ∃ _ : ∀ p ∈ (_sym, Val.Vint (Integers.Int.repr ((s : _root_.Int)))) :: T,
         p ∈ lx,
      LocalSt (envOf bh bc bo) lx
          (H7 bo pl pw lensB workB lensO workO codes lensF wF
            (sortOffs cnt lensF (s + 1))) e le hp

def Inv7 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ _ : n ≤ codes, St7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T
    (codes - n) e le hp

def JAssn7 (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ m, ∃ _ : n = m + 1, ∃ _ : m + 1 ≤ codes,
    Mid7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T
      (codes - (m + 1)) e le hp

def Post7 : Sep.Assn :=
  St7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T codes

theorem body7_triple
    (hpl : permOrder pl .Readable = true)
    (hpw : permOrder pw .Writable = true)
    (hlb : ∀ j, lensF j < 65536)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs cnt lensF s j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hcnt : cnt = fun j => InflateTable.Model.count lensF codes j)
    (hmemL : (_lens, .Vptr lensB lensO) ∈ T)
    (hmemW : (_work, .Vptr workB workO) ∈ T)
    (hmemC : (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))) ∈ T)
    (hTt : ∀ p ∈ T, p.1 ≠ _t'4 ∧ p.1 ≠ _t'26 ∧ p.1 ≠ _t'27 ∧ p.1 ≠ _t'28)
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table
      (Inv7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T n)
      (.Ssequence (.Sifthenelse guard7 .Sskip .Sbreak) iter7)
      { normal := JAssn7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt
                    T n,
        brk := Post7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T,
        cont := JAssn7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt
                  T n,
        ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hn : n ≤ codes) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (wF : Nat → Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hwb : ∀ j, wF j < 65536) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hplaced : Placed lensF wF codes (codes - n)) => ?_)
  match n with
  | 0 =>
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hTx _ _ => ?_) ?_
      · have h := guard2_eval ge codes (e := envOf bh bc bo) (m := mm)
          (codes - 0) (by omega) (by omega)
          (hTx.get List.mem_cons_self)
          (hTx.get (List.mem_cons_of_mem _ hmemC))
        rw [show decide (codes - 0 < codes) = false from by
              rw [decide_eq_false_iff_not]; omega] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        refine ⟨wF, hwb, ?_, ?_⟩
        · rw [show (codes : Nat) = codes - 0 from by omega]; exact hplaced
        · rw [show ((codes : Nat) : _root_.Int) = ((codes - 0 : Nat) : _root_.Int)
                from by omega,
              show (codes : Nat) = codes - 0 from by omega]
          exact hx
  | m + 1 =>
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_sym, .Vint (Integers.Int.repr
              (((codes - (m + 1) : Nat) : _root_.Int)))) :: T)
          (H7 bo pl pw lensB workB lensO workO codes lensF wF
            (sortOffs cnt lensF (codes - (m + 1))))) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hTx _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        have h := guard2_eval ge codes (e := envOf bh bc bo) (m := mm)
          (codes - (m + 1)) (by omega) (by omega)
          (hTx.get List.mem_cons_self)
          (hTx.get (List.mem_cons_of_mem _ hmemC))
        rw [show decide (codes - (m + 1) < codes) = true from by
              rw [decide_eq_true_eq]; omega] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (iter7_step ge fe bh bc bo pl pw lensB workB lensO workO codes lensF
            wF cnt hpl hpw hlb hwb (hgb (codes - (m + 1)) (by omega)) hlens15 hc16 hnoL
            hnoW hcnt (by omega) hplaced
            ((_sym, .Vint (Integers.Int.repr
                (((codes - (m + 1) : Nat) : _root_.Int)))) :: T)
            (List.mem_cons_of_mem _ hmemL) (List.mem_cons_of_mem _ hmemW)
            List.mem_cons_self
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _sym ≠ _t'4; decide
              · exact (hTt p hp2).1)
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _sym ≠ _t'26; decide
              · exact (hTt p hp2).2.1)
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _sym ≠ _t'27; decide
              · exact (hTt p hp2).2.2.1)
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _sym ≠ _t'28; decide
              · exact (hTt p hp2).2.2.2))
          (fun e le hp x => x) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        obtain ⟨wF', hwb', hpl', lx, hsub, hL⟩ := hx
        exact ⟨m, rfl, by omega, wF', hwb', hpl', lx, hsub, hL⟩

theorem incr7_triple
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table
      (JAssn7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T n) incr2
      { normal := fun e le hp => ∃ n', n' < n ∧
          Inv7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T n'
            e le hp,
        brk := Post7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T,
        cont := Assn.no, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (m : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hnm : n = m + 1) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hmc : m + 1 ≤ codes) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (wF : Nat → Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hwb : ∀ j, wF j < 65536) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hplaced : Placed lensF wF codes (codes - (m + 1) + 1)) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (lx : List (Ident × Val)) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hsub : ∀ p ∈ (_sym, Val.Vint (Integers.Int.repr
        (((codes - (m + 1) : Nat) : _root_.Int)))) :: T, p ∈ lx) => ?_)
  subst hnm
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) lx T _ _sym _
      (.Vint (Integers.Int.repr (((codes - m : Nat) : _root_.Int))))
      (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) hTsym
      (fun le mm hp hTx _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr (((codes - (m + 1) : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _sym tuint _ (hTx.get (hsub _ List.mem_cons_self)))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_uint_int]
    show some (Val.Vint (Integers.Int.add
              (Integers.Int.repr (((codes - (m + 1) : Nat) : _root_.Int)))
              (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
    rw [u32_add, show codes - (m + 1) + 1 = codes - m from by omega]
  · obtain ⟨henv, hTx, hH⟩ := hx
    rw [show codes - (m + 1) + 1 = codes - m from by omega] at hplaced hH
    exact ⟨m, by omega, by omega, wF, hwb, hplaced, henv, hTx, hH⟩

/-- **The sort loop.**  Every symbol placed, every write in bounds. -/
theorem loop7_triple
    (hpl : permOrder pl .Readable = true)
    (hpw : permOrder pw .Writable = true)
    (hlb : ∀ j, lensF j < 65536)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs cnt lensF s j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hcnt : cnt = fun j => InflateTable.Model.count lensF codes j)
    (hmemL : (_lens, .Vptr lensB lensO) ∈ T)
    (hmemW : (_work, .Vptr workB workO) ∈ T)
    (hmemC : (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))) ∈ T)
    (hTt : ∀ p ∈ T, p.1 ≠ _t'4 ∧ p.1 ≠ _t'26 ∧ p.1 ≠ _t'27 ∧ p.1 ≠ _t'28)
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (Inv7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T codes)
      loop7
      { normal := Post7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _
    (Inv7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T)
    (JAssn7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T) _ _
    (body7_triple ge fe bh bc bo pl pw lensB workB lensO workO codes lensF cnt T
      hpl hpw hlb hgb hlens15 hc16 hnoL hnoW hcnt hmemL hmemW hmemC hTt hTsym _)
    (incr7_triple ge fe bh bc bo pl pw lensB workB lensO workO codes lensF cnt T
      hTsym _) codes

/-- **`fullBody` segment 17**: `sym = 0;` then the sort loop.

    The counterpart of `seg3_triple`/`seg4_triple`/`seg6_triple` for `loop7`,
    which had only the bare-loop lemma.  `Placed lensF wF codes 0` is vacuous,
    and `sortOffs cnt lensF 0 = offsC cnt` is what §11 leaves in `offs`. -/
theorem seg7_triple
    (hpl : permOrder pl .Readable = true)
    (hpw : permOrder pw .Writable = true)
    (hlb : ∀ j, lensF j < 65536)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs cnt lensF s j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hcnt : cnt = fun j => InflateTable.Model.count lensF codes j)
    (hmemL : (_lens, .Vptr lensB lensO) ∈ T)
    (hmemW : (_work, .Vptr workB workO) ∈ T)
    (hmemC : (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))) ∈ T)
    (hTt : ∀ p ∈ T, p.1 ≠ _t'4 ∧ p.1 ≠ _t'26 ∧ p.1 ≠ _t'27 ∧ p.1 ≠ _t'28)
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym)
    (wF : Nat → Nat) (hwb : ∀ j, wF j < 65536)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T
        (H7 bo pl pw lensB workB lensO workO codes lensF wF
          (sortOffs cnt lensF 0)))
      (.Ssequence (.Sset _sym (.Econst_int (Integers.Int.repr 0) tint)) loop7)
      { normal := Post7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (Inv7 bh bc bo pl pw lensB workB lensO workO codes lensF cnt T codes) _ _ _ ?_
    (loop7_triple ge fe bh bc bo pl pw lensB workB lensO workO codes lensF cnt T
      hpl hpw hlb hgb hlens15 hc16 hnoL hnoW hcnt hmemL hmemW hmemC hTt hTsym R)
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) T
      (H7 bo pl pw lensB workB lensO workO codes lensF wF
        (sortOffs cnt lensF 0)) _sym 0 hTsym)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  obtain ⟨henv, hT', hH⟩ := hx
  refine ⟨Nat.le_refl codes, wF, hwb, ?_, ?_⟩
  · intro t ht
    rw [show codes - codes = 0 from by omega] at ht
    exact absurd ht (Nat.not_lt_zero t)
  · rw [show codes - codes = 0 from by omega]
    exact ⟨henv, hT', hH⟩

end SortLoop



/-! ## §13 The `max == 0` block — struct writes and the table copies
    (inftrees.c:126-134; AST 553-625)

        here.op = (unsigned char)64;
        here.bits = (unsigned char)1;
        here.val = (unsigned short)0;
        *(*table)++ = here;     /* twice */
        *bits = 1;
        return 0;

The two `*(*table)++ = here` are **struct assignments** (`accessMode = By_copy`),
so they go through `triple_assign_copy` rather than `triple_assign` — the first
use of the copy rule in this development. -/

/-- A struct field as an l-value — what a field *write* needs (`eval_field_scalar`
    is the read side). -/
theorem eval_field_lvalue {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {a : Expr} {fld : Ident} {ty : Ty} {sid : Ident} {att : Attr}
    {co : Composite} {b : Block} {ofs : Integers.Ptrofs} {delta : Z}
    (hstruct : typeof a = .Tstruct sid att)
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv fld co.co_members = .OK (delta, .Full))
    (hptr : EvalExpr ge e le m a (.Vptr b ofs)) :
    EvalLvalue ge e le m (.Efield a fld ty) b
      (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) .Full :=
  EvalLvalue.Efield_struct a fld ty b ofs sid co att delta .Full
    hptr hstruct hco hfld

section MaxZero

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)

/-- The `here` local's address (array-free `Evar`, `By_copy` decay). -/
theorem eval_here_base {le : TempEnv} {m : Mem} :
    EvalExpr ge (envOf bh bc bo) le m (.Evar _here (Ty.Tstruct __1353 noattr))
      (.Vptr bh Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ bh Integers.Ptrofs.zero .Full _
    (eval_var_local (envOf_here bh bc bo)) (DerefLoc.copy (by decide))

/-- The `here` local as an l-value. -/
theorem eval_here_lvalue {le : TempEnv} {m : Mem} :
    EvalLvalue ge (envOf bh bc bo) le m
      (.Evar _here (Ty.Tstruct __1353 noattr)) bh Integers.Ptrofs.zero .Full :=
  eval_var_local (envOf_here bh bc bo)

/-- Writing one scalar field of `here`, at chunk `chunk` and offset `delta`. -/
theorem here_field_write
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (fld : Ident) (fty : Ty) (chunk : Chunk) (delta : Z)
    (hacc : accessMode fty = .By_value chunk)
    (hfld : fieldOffset Inftrees.prog.prog_comp_env fld
              InflateTable.Layout.codeCo.co_members = .OK (delta, .Full))
    (haddr : Integers.Ptrofs.unsigned
        (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta))
      = delta)
    (l : List (Ident × Val)) (Hrest : HProp)
    (vold vnew : Val) (rhs : Expr)
    (hev : ∀ (le : TempEnv) (m : Mem), TempsHold l le → ∃ v,
      EvalExpr ge (envOf bh bc bo) le m rhs v
      ∧ Cop.semCast v (typeof rhs) fty m = some vnew) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto chunk .Freeable bh delta vold ∗ Hrest))
      (.Sassign (.Efield (.Evar _here (Ty.Tstruct __1353 noattr)) fld fty) rhs)
      (.only (LocalSt (envOf bh bc bo) l
        (mapsto chunk .Freeable bh delta vnew ∗ Hrest))) := by
  have hco : ge.genv_cenv.get __1353 = some InflateTable.Layout.codeCo := by
    rw [hcenv]
    show Inftrees.prog.prog_comp_env.get __1353 = _
    show _ = some (match Inftrees.prog.prog_comp_env.get __1353 with
      | some co => co
      | none => { co_su := .Struct, co_members := [], co_attr := noattr,
                  co_sizeof := 0, co_alignof := 1, co_rank := 0 })
    rw [show Inftrees.prog.prog_comp_env.get __1353
          = some InflateTable.Layout.codeCo from by decide]
  refine triple_assign ge fe f_inflate_table _ _ _ _ chunk .Freeable bh
    (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta))
    (by decide) (by simpa only [typeof] using hacc) ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  obtain ⟨v, hevv, hcast⟩ := hev le m hT
  refine ⟨vold, vnew, h1, h2, hd12, heq, ?_, ?_, ⟨v, hevv, hcast⟩, ?_⟩
  · rw [haddr]; exact hm1
  · exact eval_field_lvalue rfl hco (by rw [hcenv]; exact hfld)
      (eval_here_base ge bh bc bo)
  · intro h1' hm1' hd1'
    refine ⟨rfl, hT, h1', h2, hd1', rfl, ?_, hrest⟩
    rw [haddr] at hm1'
    exact hm1'

/-! ### The struct copy `*(*table)++ = here`

`here`'s three fields, assembled into the 4-byte source run
`triple_assign_copy` consumes.  `struct code` has no padding: 1 + 1 + 2 = 4. -/

/-- The bytes of a fully-written `here`. -/
def hereBytes (op bits val : Nat) : List MemVal :=
  encodeVal .Mint8unsigned (.Vint (Integers.Int.repr ((op : Nat))))
  ++ (encodeVal .Mint8unsigned (.Vint (Integers.Int.repr ((bits : Nat))))
      ++ encodeVal .Mint16unsigned (.Vint (Integers.Int.repr ((val : Nat)))))

theorem hereBytes_length (op bits val : Nat) :
    (hereBytes op bits val).length = 4 := by
  show (List.length (encodeVal .Mint8unsigned
      (.Vint (Integers.Int.repr ((op : Nat))))
    ++ (encodeVal .Mint8unsigned (.Vint (Integers.Int.repr ((bits : Nat))))
        ++ encodeVal .Mint16unsigned
             (.Vint (Integers.Int.repr ((val : Nat))))))) = 4
  rw [List.length_append, List.length_append, length_encodeVal, length_encodeVal,
      length_encodeVal]
  rfl

/-- **The three field `mapsto`s ARE the 4-byte run.**  An equality, so it also
    takes the struct apart when a later phase needs the fields back. -/
theorem here_assemble (bh : Block) (op bits val : Nat) :
    mapsto .Mint8unsigned .Freeable bh 0
        (.Vint (Integers.Int.repr ((op : Nat))))
      ∗ (mapsto .Mint8unsigned .Freeable bh 1
           (.Vint (Integers.Int.repr ((bits : Nat))))
         ∗ mapsto .Mint16unsigned .Freeable bh 2
             (.Vint (Integers.Int.repr ((val : Nat)))))
    = bytesPtsTo bh .Freeable 0 (hereBytes op bits val) := by
  rw [mapsto_eq_bytes (chunk := .Mint8unsigned) (by decide),
      mapsto_eq_bytes (chunk := .Mint8unsigned) (by decide),
      mapsto_eq_bytes (chunk := .Mint16unsigned) (by decide),
      hereBytes, bytesPtsTo_append, bytesPtsTo_append, length_encodeVal,
      length_encodeVal]
  show _ = bytesPtsTo bh .Freeable 0 _
            ∗ (bytesPtsTo bh .Freeable (0 + ((1 : Nat) : _root_.Int)) _
               ∗ bytesPtsTo bh .Freeable
                   (0 + ((1 : Nat) : _root_.Int) + ((1 : Nat) : _root_.Int)) _)
  rw [show (0 : _root_.Int) + ((1 : Nat) : _root_.Int) = 1 from by omega,
      show (1 : _root_.Int) + ((1 : Nat) : _root_.Int) = 2 from by omega]

/-- **One table entry written by struct copy**: `*p = here`, where `p` is a
    `tptr (struct code)` temporary and the destination is four owned bytes. -/
theorem copy_entry_step
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pr : Permission) (hpr : permOrder pr .Writable = true)
    (tB : Block) (tO : Integers.Ptrofs)
    (op bits val : Nat) (oldBytes : List MemVal) (hold : oldBytes.length = 4)
    (hal : Integers.Ptrofs.unsigned tO % 2 = 0)
    (pid : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemP : (pid, .Vptr tB tO) ∈ l) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
      (.Sassign
        (.Ederef (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          (Ty.Tstruct __1353 noattr))
        (.Evar _here (Ty.Tstruct __1353 noattr)))
      (.only (LocalSt (envOf bh bc bo) l
        (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
            (hereBytes op bits val)
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))) := by
  have hsz : sizeof ge.genv_cenv (Ty.Tstruct __1353 noattr) = 4 := by
    rw [hcenv]; exact InflateTable.Layout.code_sizeof
  have halb : alignofBlockcopy ge.genv_cenv (Ty.Tstruct __1353 noattr) = 2 := by
    rw [hcenv]; exact InflateTable.Layout.code_alignofBlockcopy
  refine triple_assign_copy ge fe f_inflate_table _ _ _ _ .Freeable pr
    bh Integers.Ptrofs.zero tB tO (hereBytes op bits val) oldBytes
    (by decide) hpr
    (by simpa only [typeof] using InflateTable.Layout.code_accessMode)
    (by simp only [typeof]; rw [hereBytes_length, hsz]; rfl)
    (by rw [hold, hereBytes_length])
    (by simp only [typeof]; rw [halb, ptrofs_unsigned_zero]; intro _; rfl)
    (by simp only [typeof]; rw [halb]; intro _; exact hal)
    ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  -- reassociate: destination outermost, as the rule wants
  obtain ⟨hD, hSR, hdDS, heq, hbD, hSR'⟩ := hH
  subst heq
  obtain ⟨hS, hR, hdSR, heq2, hbS, hbR⟩ := hSR'
  subst heq2
  refine ⟨hS, hD, hR, ?_, ?_, ?_, hbS, hbD, ?_, ?_, ?_, ?_⟩
  · -- hS ⊥ hR
    exact hdSR
  · -- hD ⊥ (hS ∪ hR)
    exact hdDS
  · rfl
  · exact EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)) _ (hT.get hmemP))
  · exact eval_here_base ge bh bc bo
  · simp only [typeof]
    exact semCast_struct_same bh Integers.Ptrofs.zero __1353 noattr noattr m
  · intro hD' hbD' hd'
    exact ⟨rfl, hT, hD', Heap.union hS hR, hd', rfl, hbD', hS, hR, hdSR, rfl,
           hbS, hbR⟩

/-! ### `*table` bumps, `*bits`, and the block's exit -/

theorem loadResult_Mptr (b : Block) (o : Integers.Ptrofs) :
    Val.loadResult Mptr (.Vptr b o) = .Vptr b o := rfl

theorem semCast_ptr_same (b : Block) (o : Integers.Ptrofs) (m : Mem) :
    Cop.semCast (.Vptr b o) (tptr (Ty.Tstruct __1353 noattr))
      (tptr (Ty.Tstruct __1353 noattr)) m = some (.Vptr b o) := rfl

theorem semCast_int_uint (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tint tuint m = some (.Vint x) := rfl

/-- `p = *table;` — a pointer load through the `table` parameter. -/
theorem read_table_triple
    (pt : Permission) (tblB : Block) (tblO : Integers.Ptrofs)
    (tB : Block) (tO : Integers.Ptrofs)
    (hpt : permOrder pt .Readable = true)
    (pid : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ pid) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ Hrest))
      (.Sset pid (.Ederef (.Etempvar _table
        (tptr (tptr (Ty.Tstruct __1353 noattr))))
        (tptr (Ty.Tstruct __1353 noattr))))
      (.only (LocalSt (envOf bh bc bo) ((pid, .Vptr tB tO) :: l)
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ Hrest))) :=
  triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l _ pid _ _
    (fun _ hp => hp) hne
    (fun le m hp hT hH hag => by
      obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
      subst heq
      have h := eval_deref_mapsto (ge := ge) (e := envOf bh bc bo)
        (ty := tptr (Ty.Tstruct __1353 noattr))
        rfl hpt hm1 (Heap.Agrees_union_left hag)
        (EvalExpr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))) _
          (hT.get hmemT))
      rw [loadResult_Mptr] at h
      exact h)

/-- `*table = p + 1;` — the pointer bump.  The new value's offset is
    `idxOfs` at stride `sizeof (struct code) = 4`. -/
theorem bump_table_triple
    (pt : Permission) (tblB : Block) (tblO : Integers.Ptrofs)
    (tB : Block) (tO : Integers.Ptrofs)
    (hpt : permOrder pt .Writable = true)
    (pid : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hmemP : (pid, .Vptr tB tO) ∈ l) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ Hrest))
      (.Sassign
        (.Ederef (.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
          (tptr (Ty.Tstruct __1353 noattr)))
        (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          (.Econst_int (Integers.Int.repr 1) tint)
          (tptr (Ty.Tstruct __1353 noattr))))
      (.only (LocalSt (envOf bh bc bo) l
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
            (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
              tO (Integers.Int.repr 1)))
         ∗ Hrest))) := by
  refine triple_assign ge fe f_inflate_table _ _ _ _ Mptr pt tblB tblO
    hpt (show accessMode (typeof (.Ederef
      (.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
      (tptr (Ty.Tstruct __1353 noattr)))) = .By_value Mptr from rfl) ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨.Vptr tB tO,
          .Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
            (Integers.Int.repr 1)),
          h1, h2, hd12, heq, hm1, ?_, ?_, ?_⟩
  · exact EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Etempvar _table _ _ (hT.get hmemT))
  · refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ (.Vptr tB tO)
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar pid _ _ (hT.get hmemP)) (EvalExpr.Econst_int _ _)
      (semAdd_ptr_int _ _ _ _ _ rfl), ?_⟩
    simp only [typeof]
    exact semCast_ptr_same _ _ m
  · intro h1' hm1' hd1'
    exact ⟨rfl, hT, h1', h2, hd1', rfl, hm1', hrest⟩

/-- `*table = p + k;` with the offset in a temporary — the epilogue's
    `*table += used` (`bump_table_triple` covers only the `+1` of the
    `max == 0` block). -/
theorem bump_table_var_triple
    (pt : Permission) (tblB : Block) (tblO : Integers.Ptrofs)
    (tB : Block) (tO : Integers.Ptrofs) (k : Nat)
    (hpt : permOrder pt .Writable = true)
    (pid : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hmemP : (pid, .Vptr tB tO) ∈ l)
    (hmemU : (_used, .Vint (Integers.Int.repr ((k : _root_.Int)))) ∈ l) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ Hrest))
      (.Sassign
        (.Ederef (.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
          (tptr (Ty.Tstruct __1353 noattr)))
        (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          (.Etempvar _used tuint)
          (tptr (Ty.Tstruct __1353 noattr))))
      (.only (LocalSt (envOf bh bc bo) l
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
            (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned
              tO (Integers.Int.repr ((k : _root_.Int)))))
         ∗ Hrest))) := by
  refine triple_assign ge fe f_inflate_table _ _ _ _ Mptr pt tblB tblO
    hpt (show accessMode (typeof (.Ederef
      (.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
      (tptr (Ty.Tstruct __1353 noattr)))) = .By_value Mptr from rfl) ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨.Vptr tB tO,
          .Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO
            (Integers.Int.repr ((k : _root_.Int)))),
          h1, h2, hd12, heq, hm1, ?_, ?_, ?_⟩
  · exact EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Etempvar _table _ _ (hT.get hmemT))
  · refine ⟨_, EvalExpr.Ebinop .Oadd _ _ _ (.Vptr tB tO)
      (.Vint (Integers.Int.repr ((k : _root_.Int)))) _
      (EvalExpr.Etempvar pid _ _ (hT.get hmemP))
      (EvalExpr.Etempvar _used tuint _ (hT.get hmemU))
      (semAdd_ptr_int _ _ _ _ _ rfl), ?_⟩
    simp only [typeof]
    exact semCast_ptr_same _ _ m
  · intro h1' hm1' hd1'
    exact ⟨rfl, hT, h1', h2, hd1', rfl, hm1', hrest⟩

/-- `*bits = r;` from a temporary — the epilogue's `*bits = root`. -/
theorem write_bits_var_triple
    (pb : Permission) (bitsB : Block) (bitsO : Integers.Ptrofs)
    (hpb : permOrder pb .Writable = true)
    (vold : Val) (r : Nat)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemB : (_bits, .Vptr bitsB bitsO) ∈ l)
    (hmemR : (_root, .Vint (Integers.Int.repr ((r : _root_.Int)))) ∈ l) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vold ∗ Hrest))
      (.Sassign (.Ederef (.Etempvar _bits (tptr tuint)) tuint)
        (.Etempvar _root tuint))
      (.only (LocalSt (envOf bh bc bo) l
        (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
            (.Vint (Integers.Int.repr ((r : _root_.Int))))
         ∗ Hrest))) := by
  refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint32 pb bitsB bitsO
    hpb (show accessMode (typeof (.Ederef (.Etempvar _bits (tptr tuint)) tuint))
      = .By_value .Mint32 from rfl) ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨vold, .Vint (Integers.Int.repr ((r : _root_.Int))),
          h1, h2, hd12, heq, hm1, ?_, ?_, ?_⟩
  · exact EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Etempvar _bits _ _ (hT.get hmemB))
  · exact ⟨_, EvalExpr.Etempvar _root tuint _ (hT.get hmemR), by
      simp only [typeof]; rfl⟩
  · intro h1' hm1' hd1'
    exact ⟨rfl, hT, h1', h2, hd1', rfl, hm1', hrest⟩

/-- `*bits = c;` — an `unsigned` store through the `bits` parameter. -/
theorem write_bits_triple
    (pb : Permission) (bitsB : Block) (bitsO : Integers.Ptrofs)
    (hpb : permOrder pb .Writable = true)
    (vold : Val) (c : _root_.Int)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemB : (_bits, .Vptr bitsB bitsO) ∈ l) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vold ∗ Hrest))
      (.Sassign (.Ederef (.Etempvar _bits (tptr tuint)) tuint)
        (.Econst_int (Integers.Int.repr c) tint))
      (.only (LocalSt (envOf bh bc bo) l
        (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
            (.Vint (Integers.Int.repr c))
         ∗ Hrest))) := by
  refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint32 pb bitsB bitsO
    hpb (show accessMode (typeof (.Ederef (.Etempvar _bits (tptr tuint)) tuint))
      = .By_value .Mint32 from rfl) ?_
  intro e le hp m hP _
  obtain ⟨henv, hT, hH⟩ := hP
  subst henv
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
  refine ⟨vold, .Vint (Integers.Int.repr c), h1, h2, hd12, heq, hm1, ?_, ?_, ?_⟩
  · exact EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Etempvar _bits _ _ (hT.get hmemB))
  · exact ⟨_, EvalExpr.Econst_int _ _, by
      simp only [typeof]; exact semCast_int_uint m _⟩
  · intro h1' hm1' hd1'
    exact ⟨rfl, hT, h1', h2, hd1', rfl, hm1', hrest⟩

/-! ### The `max == 0` block, assembled (AST 554-625)

`here.op = 64; here.bits = 1; here.val = 0;` then twice
`{p = *table; *table = p+1; *p = here;}`, then `*bits = 1; return 0;`.

Capacity ≥ 2 entries is assumption A4's unconditional part: this block writes
two entries with **no** runtime check, which is exactly why `cap_min` is in
the assumption set. -/

abbrev fieldW (fld : Ident) (fty : Ty) (c : _root_.Int) : Stmt :=
  .Sassign (.Efield (.Evar _here (Ty.Tstruct __1353 noattr)) fld fty)
    (.Ecast (.Econst_int (Integers.Int.repr c) tint) fty)

abbrev entryW (pid : Ident) : Stmt :=
  .Ssequence
    (.Ssequence
      (.Sset pid (.Ederef
        (.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
        (tptr (Ty.Tstruct __1353 noattr))))
      (.Sassign
        (.Ederef (.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
          (tptr (Ty.Tstruct __1353 noattr)))
        (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          (.Econst_int (Integers.Int.repr 1) tint)
          (tptr (Ty.Tstruct __1353 noattr)))))
    (.Sassign
      (.Ederef (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
        (Ty.Tstruct __1353 noattr))
      (.Evar _here (Ty.Tstruct __1353 noattr)))

abbrev maxZeroBlock : Stmt :=
  .Ssequence (fieldW _op tuchar 64)
    (.Ssequence (fieldW _bits tuchar 1)
      (.Ssequence (fieldW _val tushort 0)
        (.Ssequence (entryW _t'1)
          (.Ssequence (entryW _t'2)
            (.Ssequence
              (.Sassign (.Ederef (.Etempvar _bits (tptr tuint)) tuint)
                (.Econst_int (Integers.Int.repr 1) tint))
              (.Sreturn (some (.Econst_int (Integers.Int.repr 0) tint))))))))

/-- The `here` local carved into its three fields, at any contents. -/
abbrev hereFields (bh : Block) (op bits val : Nat) : HProp :=
  mapsto .Mint8unsigned .Freeable bh 0 (.Vint (Integers.Int.repr ((op : Nat))))
  ∗ (mapsto .Mint8unsigned .Freeable bh 1
       (.Vint (Integers.Int.repr ((bits : Nat))))
     ∗ mapsto .Mint16unsigned .Freeable bh 2
         (.Vint (Integers.Int.repr ((val : Nat)))))

/-- The fresh `here` block, carved into three undefined field cells. -/
theorem here_carve (bh : Block) :
    undefBytes .Freeable bh 0 4
      = mapsto .Mint8unsigned .Freeable bh 0 .Vundef
        ∗ (mapsto .Mint8unsigned .Freeable bh 1 .Vundef
           ∗ mapsto .Mint16unsigned .Freeable bh 2 .Vundef) := by
  rw [show (4 : Nat) = 1 + 3 from rfl, undefBytes_append .Freeable bh 0 1 3,
      show (0 : _root_.Int) + ((1 : Nat) : _root_.Int) = 1 from by omega,
      show (3 : Nat) = 1 + 2 from rfl, undefBytes_append .Freeable bh 1 1 2,
      show (1 : _root_.Int) + ((1 : Nat) : _root_.Int) = 2 from by omega,
      show undefBytes .Freeable bh 0 1
          = mapsto .Mint8unsigned .Freeable bh 0 .Vundef from
        undefBytes_mapsto (chunk := .Mint8unsigned) .Freeable bh 0
          undefEncoded_Mint8unsigned (by decide),
      show undefBytes .Freeable bh 1 1
          = mapsto .Mint8unsigned .Freeable bh 1 .Vundef from
        undefBytes_mapsto (chunk := .Mint8unsigned) .Freeable bh 1
          undefEncoded_Mint8unsigned (by decide),
      show undefBytes .Freeable bh 2 2
          = mapsto .Mint16unsigned .Freeable bh 2 .Vundef from
        undefBytes_mapsto (chunk := .Mint16unsigned) .Freeable bh 2
          undefEncoded_Mint16unsigned (by decide)]

/-- **One entry written and `*table` advanced**: `p = *table; *table = p+1;
    *p = here;` — the read/bump/copy triple, composed. -/
theorem entry_write_step
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pt pr : Permission)
    (tblB : Block) (tblO : Integers.Ptrofs) (tB : Block) (tO : Integers.Ptrofs)
    (hptR : permOrder pt .Readable = true)
    (hptW : permOrder pt .Writable = true)
    (hpr : permOrder pr .Writable = true)
    (op bits val : Nat) (oldBytes : List MemVal) (hold : oldBytes.length = 4)
    (hal : Integers.Ptrofs.unsigned tO % 2 = 0)
    (pid : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ pid) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
            ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))))
      (entryW pid)
      (.only (LocalSt (envOf bh bc bo) ((pid, .Vptr tB tO) :: l)
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
            (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
              tO (Integers.Int.repr 1)))
         ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
              (hereBytes op bits val)
            ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val)
               ∗ Hrest))))) := by
  -- the statement nests left: `(p = *table; *table = p+1); *p = here`
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) ((pid, .Vptr tB tO) :: l)
      (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
          (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
            tO (Integers.Int.repr 1)))
       ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))))
    _ _ _ ?_ ?_
  · -- p = *table; *table = p + 1
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo) ((pid, .Vptr tB tO) :: l)
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))))
      _ _ _
      (read_table_triple ge fe bh bc bo pt tblB tblO tB tO hptR pid l
        (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))
        hmemT hne)
      (bump_table_triple ge fe bh bc bo pt tblB tblO tB tO hptW pid
        ((pid, .Vptr tB tO) :: l)
        (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))
        (List.mem_cons_of_mem _ hmemT) List.mem_cons_self)
  · -- *p = here (the struct copy); the `table` cell rides in `Hrest`
    refine triple_conseq ge fe f_inflate_table
      (copy_entry_step ge fe bh bc bo hcenv pr hpr tB tO op bits val oldBytes
        hold hal pid ((pid, .Vptr tB tO) :: l)
        (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
            (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
              tO (Integers.Int.repr 1)))
         ∗ Hrest)
        List.mem_cons_self)
      (fun e le hp hx => ?_) (fun e le hp hx => ?_)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ hx => hx.elim)
    · obtain ⟨henv, hT, hH⟩ := hx
      refine ⟨henv, hT, ?_⟩
      rw [show mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
              (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
                tO (Integers.Int.repr 1)))
            ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
               ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))
          = bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) oldBytes
            ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val)
               ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
                    (.Vptr tB (idxOfs ge.genv_cenv
                      (Ty.Tstruct __1353 noattr) .Signed tO
                      (Integers.Int.repr 1)))
                  ∗ Hrest)) from by sep_cancel] at hH
      exact hH
    · obtain ⟨henv, hT, hH⟩ := hx
      refine ⟨henv, hT, ?_⟩
      rw [show bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                (hereBytes op bits val)
            ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val)
               ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
                    (.Vptr tB (idxOfs ge.genv_cenv
                      (Ty.Tstruct __1353 noattr) .Signed tO
                      (Integers.Int.repr 1)))
                  ∗ Hrest))
          = mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
              (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
                tO (Integers.Int.repr 1)))
            ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                 (hereBytes op bits val)
               ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))
          from by sep_cancel] at hH
      exact hH

/-- A `∗`-permutation of the heap component of a `LocalSt`, as a triple
    transformer — the one piece of bookkeeping the block chain needs
    repeatedly.  `sep_cancel` proves the equalities. -/
theorem localst_perm (E : Env) (lx : List (Ident × Val)) (H H' : HProp)
    (heq : H = H') (s : Stmt) (R : Sep.ExitConds)
    (h : Triple ge fe f_inflate_table (LocalSt E lx H') s R) :
    Triple ge fe f_inflate_table (LocalSt E lx H) s R := by
  rw [heq]; exact h

/-- **The `max == 0` block.**  Writes the two invalid-code entries, advances
    `*table` past them, sets `*bits = 1`, and returns 0.

    The footprint arrives already carved and in the order the statements
    consume it — the caller (InflateTableChain.lean) does the `here_carve` and
    the `anyBytes_split` of the two table entries once. -/
theorem maxzero_block_triple
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hdbc : bh ≠ bc) (hdbo : bh ≠ bo) (hdco : bc ≠ bo)
    (pt pb pr : Permission)
    (tblB bitsB tB : Block) (tblO bitsO tO : Integers.Ptrofs)
    (hptR : permOrder pt .Readable = true)
    (hptW : permOrder pt .Writable = true)
    (hpb : permOrder pb .Writable = true)
    (hpr : permOrder pr .Writable = true)
    (e0 e1 : List MemVal) (he0 : e0.length = 4) (he1 : e1.length = 4)
    (bv : Val) (vc vo : List MemVal)
    (hvc : vc.length = 32) (hvo : vo.length = 32)
    (hal0 : Integers.Ptrofs.unsigned tO % 2 = 0)
    (haddr1 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
        (Integers.Int.repr 1)) = Integers.Ptrofs.unsigned tO + 4)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hmemB : (_bits, .Vptr bitsB bitsO) ∈ l)
    (hT1 : ∀ p ∈ l, p.1 ≠ _t'1) (hT2 : ∀ p ∈ l, p.1 ≠ _t'2)
    (Ret : Val → HProp)
    (hret : ∀ hr,
      (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
          (.Vint (Integers.Int.repr 1))
       ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
            (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
              (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                (Integers.Int.repr 1)) (Integers.Int.repr 1)))
          ∗ (bytesPtsTo tB pr
               (Integers.Ptrofs.unsigned
                 (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                   (Integers.Int.repr 1))) (hereBytes 64 1 0)
             ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                  (hereBytes 64 1 0) ∗ Hrest)))) hr →
      Ret (.Vint (Integers.Int.repr 0)) hr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (mapsto .Mint8unsigned .Freeable bh 0 .Vundef
         ∗ (mapsto .Mint8unsigned .Freeable bh 1 .Vundef
            ∗ (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
               ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
                    (.Vptr tB tO)
                  ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
                     ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
                        ∗ (mapsto .Mint32 pb bitsB
                             (Integers.Ptrofs.unsigned bitsO) bv
                           ∗ (bytesPtsTo bc .Freeable 0 vc
                              ∗ (bytesPtsTo bo .Freeable 0 vo
                                 ∗ Hrest))))))))))
      maxZeroBlock
      { normal := Assn.no, brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
  have hco := InflateTable.Layout.op_offset
  -- ── here.op = 64 ──────────────────────────────────────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) l
      (mapsto .Mint8unsigned .Freeable bh 0
          (.Vint (Integers.Int.repr ((64 : Nat))))
       ∗ (mapsto .Mint8unsigned .Freeable bh 1 .Vundef
          ∗ (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
             ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
        ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
           ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))))
    _ _ _
    (here_field_write ge fe bh bc bo hcenv _op tuchar .Mint8unsigned 0 rfl
      InflateTable.Layout.op_offset (by decide) l _ _ _ _
      (fun le m _ => ⟨.Vint (Integers.Int.repr ((64 : Nat))),
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, rfl⟩)) ?_
  -- ── here.bits = 1 (swap fields 0 and 1 to the front) ─────────────────────
  refine localst_perm ge fe _ _ _
    (mapsto .Mint8unsigned .Freeable bh 1 .Vundef
     ∗ (mapsto .Mint8unsigned .Freeable bh 0
          (.Vint (Integers.Int.repr ((64 : Nat))))
        ∗ (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
           ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
        ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
           ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))) (by sep_cancel) _ _ ?_
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) l
      (mapsto .Mint8unsigned .Freeable bh 1
          (.Vint (Integers.Int.repr ((1 : Nat))))
       ∗ (mapsto .Mint8unsigned .Freeable bh 0
            (.Vint (Integers.Int.repr ((64 : Nat))))
          ∗ (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
             ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
        ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
           ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))))
    _ _ _
    (here_field_write ge fe bh bc bo hcenv _bits tuchar .Mint8unsigned 1 rfl
      InflateTable.Layout.bits_offset (by decide) l _ _ _ _
      (fun le m _ => ⟨.Vint (Integers.Int.repr ((1 : Nat))),
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, rfl⟩)) ?_
  -- ── here.val = 0 (bring field 2 to the front) ────────────────────────────
  refine localst_perm ge fe _ _ _
    (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
     ∗ (mapsto .Mint8unsigned .Freeable bh 0
          (.Vint (Integers.Int.repr ((64 : Nat))))
        ∗ (mapsto .Mint8unsigned .Freeable bh 1
             (.Vint (Integers.Int.repr ((1 : Nat))))
           ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
        ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
           ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))) (by sep_cancel) _ _ ?_
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) l
      (mapsto .Mint16unsigned .Freeable bh 2
          (.Vint (Integers.Int.repr ((0 : Nat))))
       ∗ (mapsto .Mint8unsigned .Freeable bh 0
            (.Vint (Integers.Int.repr ((64 : Nat))))
          ∗ (mapsto .Mint8unsigned .Freeable bh 1
               (.Vint (Integers.Int.repr ((1 : Nat))))
             ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
        ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
           ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))))
    _ _ _
    (here_field_write ge fe bh bc bo hcenv _val tushort .Mint16unsigned 2 rfl
      InflateTable.Layout.val_offset (by decide) l _ _ _ _
      (fun le m _ => ⟨.Vint (Integers.Int.repr ((0 : Nat))),
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, rfl⟩)) ?_
  -- ── assemble `here` into its 4-byte run, table cell to the front ─────────
  refine localst_perm ge fe _ _ _
    (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
     ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
        ∗ (bytesPtsTo bh .Freeable 0 (hereBytes 64 1 0)
           ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))))))
    (by rw [← here_assemble bh 64 1 0]; sep_cancel) _ _ ?_
  -- ── entry 1: p = *table; *table = p+1; *p = here ─────────────────────────
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) ((_t'1, .Vptr tB tO) :: l)
      (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
          (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
            tO (Integers.Int.repr 1)))
       ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) (hereBytes 64 1 0)
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes 64 1 0)
             ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
                ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))
    _ _ _
    (entry_write_step ge fe bh bc bo hcenv pt pr tblB tblO tB tO hptR hptW hpr
      64 1 0 e0 he0 hal0 _t'1 l _ hmemT hT1) ?_
  -- ── entry 2: same, at the bumped pointer ─────────────────────────────────
  refine localst_perm ge fe _ _ _
    (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
        (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
          tO (Integers.Int.repr 1)))
     ∗ (bytesPtsTo tB pr
          (Integers.Ptrofs.unsigned
            (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
              (Integers.Int.repr 1))) e1
        ∗ (bytesPtsTo bh .Freeable 0 (hereBytes 64 1 0)
           ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) (hereBytes 64 1 0)
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))))))
    (by rw [haddr1]; sep_cancel) _ _ ?_
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'2, .Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
          tO (Integers.Int.repr 1))) :: (_t'1, .Vptr tB tO) :: l)
      (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
          (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
            (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
              (Integers.Int.repr 1)) (Integers.Int.repr 1)))
       ∗ (bytesPtsTo tB pr
            (Integers.Ptrofs.unsigned
              (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                (Integers.Int.repr 1))) (hereBytes 64 1 0)
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes 64 1 0)
             ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                  (hereBytes 64 1 0)
                ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))
    _ _ _
    (entry_write_step ge fe bh bc bo hcenv pt pr tblB tblO tB
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
        (Integers.Int.repr 1))
      hptR hptW hpr 64 1 0 e1 he1
      (by rw [haddr1]
          obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned tO = A :=
            ⟨_, rfl⟩
          rw [hA] at hal0 ⊢
          have h2 : A % (2 : _root_.Int) = 0 := hal0
          show (A + 4) % (2 : _root_.Int) = 0
          omega) _t'2
      ((_t'1, .Vptr tB tO) :: l) _
      (List.mem_cons_of_mem _ hmemT)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _t'1 ≠ _t'2; decide
        · exact hT2 p hp2)) ?_
  -- ── *bits = 1 ────────────────────────────────────────────────────────────
  refine localst_perm ge fe _ _ _
    (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
     ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
          (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
            (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
              (Integers.Int.repr 1)) (Integers.Int.repr 1)))
        ∗ (bytesPtsTo tB pr
             (Integers.Ptrofs.unsigned
               (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                 (Integers.Int.repr 1))) (hereBytes 64 1 0)
           ∗ (bytesPtsTo bh .Freeable 0 (hereBytes 64 1 0)
              ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                   (hereBytes 64 1 0)
                 ∗ (bytesPtsTo bc .Freeable 0 vc
                    ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))))))
    (by sep_cancel) _ _ ?_
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'2, .Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
          tO (Integers.Int.repr 1))) :: (_t'1, .Vptr tB tO) :: l)
      (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
          (.Vint (Integers.Int.repr 1))
       ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
            (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
              (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                (Integers.Int.repr 1)) (Integers.Int.repr 1)))
          ∗ (bytesPtsTo tB pr
               (Integers.Ptrofs.unsigned
                 (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                   (Integers.Int.repr 1))) (hereBytes 64 1 0)
             ∗ (bytesPtsTo bh .Freeable 0 (hereBytes 64 1 0)
                ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                     (hereBytes 64 1 0)
                   ∗ (bytesPtsTo bc .Freeable 0 vc
                      ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))))))
    _ _ _
    (write_bits_triple ge fe bh bc bo pb bitsB bitsO hpb bv 1 _ _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemB))) ?_
  -- ── return 0 ─────────────────────────────────────────────────────────────
  refine localst_perm ge fe _ _ _
    (bytesPtsTo bh .Freeable 0 (hereBytes 64 1 0)
     ∗ (bytesPtsTo bc .Freeable 0 vc
        ∗ (bytesPtsTo bo .Freeable 0 vo
           ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
                (.Vint (Integers.Int.repr 1))
              ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
                   (.Vptr tB (idxOfs ge.genv_cenv
                     (Ty.Tstruct __1353 noattr) .Signed
                     (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                       (Integers.Int.repr 1)) (Integers.Int.repr 1)))
                 ∗ (bytesPtsTo tB pr
                      (Integers.Ptrofs.unsigned
                        (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
                          tO (Integers.Int.repr 1))) (hereBytes 64 1 0)
                    ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                         (hereBytes 64 1 0) ∗ Hrest)))))))
    (by sep_cancel) _ _ ?_
  exact return_const_triple ge fe bh bc bo _ (hereBytes 64 1 0) vc vo _ _
    (Integers.Int.repr 0) Ret hcenv hdbc hdbo hdco (hereBytes_length 64 1 0)
    hvc hvo (fun le m => EvalExpr.Econst_int _ _) (fun m => rfl)
    hret

end MaxZero








/-! ## §14 `switch (type)` (inftrees.c:190-202; AST 864-890)

        switch (type) {
        case CODES:  match = 20; break;
        case LENS:   base = lbase; extra = lext; match = 257; break;
        case DISTS:  base = dbase; extra = dext;
        }

Three labelled cases, **no default arm**, `LSnil` tail.  The proof pins the
scrutinee with `triple_switch_const` (the `∀ n` version would demand triples
for the unreachable arms too), using the `semSwitchArg` facts verified in
`InflateTableLayout.lean`.

Note the C fall-through: `selectSwitch 1` selects the LENS case *and
everything after it*, so the LENS arm's `break` is what stops it. -/

abbrev switchArms : LStmts :=
  .LScons (some 0)
    (.Ssequence (.Sset _match (.Econst_int (Integers.Int.repr 20) tint)) .Sbreak)
    (.LScons (some 1)
      (.Ssequence (.Sset _base (.Evar _lbase (tarray tushort 31)))
        (.Ssequence (.Sset _extra (.Evar _lext (tarray tushort 31)))
          (.Ssequence
            (.Sset _match (.Econst_int (Integers.Int.repr 257) tint))
            .Sbreak)))
      (.LScons (some 2)
        (.Ssequence (.Sset _base (.Evar _dbase (tarray tushort 32)))
          (.Sset _extra (.Evar _dext (tarray tushort 32))))
        .LSnil))

abbrev switchStmt : Stmt := .Sswitch (.Etempvar _type tint) switchArms

section Switch

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (l : List (Ident × Val)) (H : HProp)

/-- Reading a readonly global array's address. -/
theorem eval_global_array {le : TempEnv} {m : Mem} (id : Ident) (n : Z)
    (gb : Block)
    (hno : (envOf bh bc bo).get id = none)
    (hsym : Genv.findSymbol ge.genv_genv id = some gb) :
    EvalExpr ge (envOf bh bc bo) le m (.Evar id (tarray tushort n))
      (.Vptr gb Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ gb Integers.Ptrofs.zero .Full _
    (eval_var_global hno hsym) (DerefLoc.reference rfl)

/-- The scrutinee's selection fact, for each of the three enum values. -/
theorem switch_sel (ty : _root_.Int) (n : Z)
    (hsw : Cop.semSwitchArg (.Vint (Integers.Int.repr ty)) tint = some n)
    (hmemTy : (_type, .Vint (Integers.Int.repr ty)) ∈ l) :
    ∀ e le hp m, LocalSt (envOf bh bc bo) l H e le hp → Heap.Agrees hp m →
      ∃ v, EvalExpr ge e le m (.Etempvar _type tint) v
        ∧ Cop.semSwitchArg v (typeof (.Etempvar _type tint)) = some n := by
  intro e le hp m hP _
  obtain ⟨henv, hT, _⟩ := hP
  subst henv
  exact ⟨_, EvalExpr.Etempvar _type tint _ (hT.get hmemTy), hsw⟩

/-- **CODES.**  `match = 20`, then `break` leaves the switch. -/
theorem switch_CODES_triple
    (hmemTy : (_type, .Vint (Integers.Int.repr 0)) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ _match)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H) switchStmt
      { normal := LocalSt (envOf bh bc bo)
          ((_match, .Vint (Integers.Int.repr 20)) :: l) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_switch_const ge fe f_inflate_table _ _ _ _ 0 ?_
    (switch_sel ge bh bc bo l H 0 0
      InflateTable.Layout.semSwitchArg_zero hmemTy)
  -- `selectSwitch 0` is the CODES arm followed by the rest (C fall-through);
  -- the arm's `break` stops before the LENS statements run
  show Sep.Triple ge fe f_inflate_table _
    (.Ssequence
      (.Ssequence (.Sset _match (.Econst_int (Integers.Int.repr 20) tint))
        .Sbreak)
      (seqOfLabeledStatement (selectSwitch 1 switchArms))) _
  refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
    (triple_vacuous _ _ _ _ _)
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) ((_match, .Vint (Integers.Int.repr 20)) :: l) H)
    _ _ _
    (set_const_triple ge fe (envOf bh bc bo) l H _match 20 hne) ?_
  refine triple_conseq ge fe f_inflate_table
    (triple_break ge fe f_inflate_table _)
    (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => hx)
    (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- **LENS.**  `base = lbase; extra = lext; match = 257;` then `break`. -/
theorem switch_LENS_triple
    (lbB lxB : Block)
    (hnoL : (envOf bh bc bo).get _lbase = none)
    (hnoX : (envOf bh bc bo).get _lext = none)
    (hsymL : Genv.findSymbol ge.genv_genv _lbase = some lbB)
    (hsymX : Genv.findSymbol ge.genv_genv _lext = some lxB)
    (hmemTy : (_type, .Vint (Integers.Int.repr 1)) ∈ l)
    (hneB : ∀ p ∈ l, p.1 ≠ _base)
    (hneX : ∀ p ∈ l, p.1 ≠ _extra)
    (hneM : ∀ p ∈ l, p.1 ≠ _match)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H) switchStmt
      { normal := LocalSt (envOf bh bc bo)
          ((_match, .Vint (Integers.Int.repr 257))
            :: (_extra, .Vptr lxB Integers.Ptrofs.zero)
            :: (_base, .Vptr lbB Integers.Ptrofs.zero) :: l) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_switch_const ge fe f_inflate_table _ _ _ _ 1 ?_
    (switch_sel ge bh bc bo l H 1 1
      InflateTable.Layout.semSwitchArg_one hmemTy)
  show Sep.Triple ge fe f_inflate_table _
    (.Ssequence
      (.Ssequence (.Sset _base (.Evar _lbase (tarray tushort 31)))
        (.Ssequence (.Sset _extra (.Evar _lext (tarray tushort 31)))
          (.Ssequence
            (.Sset _match (.Econst_int (Integers.Int.repr 257) tint))
            .Sbreak)))
      (seqOfLabeledStatement (selectSwitch 2 switchArms))) _
  refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
    (triple_vacuous _ _ _ _ _)
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_base, .Vptr lbB Integers.Ptrofs.zero) :: l) H) _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l H _base _ _
      (fun _ hp => hp) hneB
      (fun le m hp hT _ _ =>
        eval_global_array ge bh bc bo _lbase 31 lbB hnoL hsymL)) ?_
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_extra, .Vptr lxB Integers.Ptrofs.zero)
        :: (_base, .Vptr lbB Integers.Ptrofs.zero) :: l) H) _ _ _
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ H _extra _ _
      (fun _ hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _base ≠ _extra; decide
        · exact hneX p hp2)
      (fun le m hp hT _ _ =>
        eval_global_array ge bh bc bo _lext 31 lxB hnoX hsymX)) ?_
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_match, .Vint (Integers.Int.repr 257))
        :: (_extra, .Vptr lxB Integers.Ptrofs.zero)
        :: (_base, .Vptr lbB Integers.Ptrofs.zero) :: l) H) _ _ _
    (set_const_triple ge fe (envOf bh bc bo) _ H _match 257
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _extra ≠ _match; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _base ≠ _match; decide
        · exact hneM p hp3)) ?_
  refine triple_conseq ge fe f_inflate_table
    (triple_break ge fe f_inflate_table _)
    (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => hx)
    (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- **DISTS.**  `base = dbase; extra = dext;` — no `break`, but it is the last
    arm, so the switch ends by falling off `LSnil`. -/
theorem switch_DISTS_triple
    (dbB dxB : Block)
    (hnoD : (envOf bh bc bo).get _dbase = none)
    (hnoX : (envOf bh bc bo).get _dext = none)
    (hsymD : Genv.findSymbol ge.genv_genv _dbase = some dbB)
    (hsymX : Genv.findSymbol ge.genv_genv _dext = some dxB)
    (hmemTy : (_type, .Vint (Integers.Int.repr 2)) ∈ l)
    (hneB : ∀ p ∈ l, p.1 ≠ _base)
    (hneX : ∀ p ∈ l, p.1 ≠ _extra)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H) switchStmt
      { normal := LocalSt (envOf bh bc bo)
          ((_extra, .Vptr dxB Integers.Ptrofs.zero)
            :: (_base, .Vptr dbB Integers.Ptrofs.zero) :: l) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_switch_const ge fe f_inflate_table _ _ _ _ 2 ?_
    (switch_sel ge bh bc bo l H 2 2
      InflateTable.Layout.semSwitchArg_two hmemTy)
  show Sep.Triple ge fe f_inflate_table _
    (.Ssequence
      (.Ssequence (.Sset _base (.Evar _dbase (tarray tushort 32)))
        (.Sset _extra (.Evar _dext (tarray tushort 32))))
      (seqOfLabeledStatement (selectSwitch 3 switchArms))) _
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_extra, .Vptr dxB Integers.Ptrofs.zero)
        :: (_base, .Vptr dbB Integers.Ptrofs.zero) :: l) H) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_base, .Vptr dbB Integers.Ptrofs.zero) :: l) H) _ _ _
      (triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l H _base _ _
        (fun _ hp => hp) hneB
        (fun le m hp hT _ _ =>
          eval_global_array ge bh bc bo _dbase 32 dbB hnoD hsymD)) ?_
    exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ H
      _extra _ _ (fun _ hp => hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _base ≠ _extra; decide
        · exact hneX p hp2)
      (fun le m hp hT _ _ =>
        eval_global_array ge bh bc bo _dext 32 dxB hnoX hsymX)
  · -- `selectSwitch 3` on a default-less chain is `LSnil`, i.e. `Sskip`
    show Sep.Triple ge fe f_inflate_table _ Stmt.Sskip _
    refine triple_conseq ge fe f_inflate_table
      (triple_skip ge fe f_inflate_table _)
      (fun _ _ _ x => x) (fun e le hp hx => hx)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ hx => hx.elim)

end Switch


/-! ## §15 The main loop's setup and the ENOUGH check
    (inftrees.c:204-218; AST 892-968)

        sym = 0; len = min; next = *table; curr = root; drop = 0;
        low = (unsigned)(-1); used = 1U << root; mask = used - 1;
        if ((type == LENS && used > ENOUGH_LENS) ||
            (type == DISTS && used > ENOUGH_DISTS)) return 1;

**This check is the reason the ENOUGH exhaustive-search theorem is not needed
for memory safety** (fv/memory-safety.md, "key discovery"): `used` is compared
against the constants at runtime *before* any entry is written, so the table
writes are bounded by a checked quantity rather than by a combinatorial
argument about Huffman codes. -/

/-- `x << y` at `(tuint, tuint)`, given the shift amount is in range. -/
theorem semBinop_shl_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int)
    (h : Integers.Int.ltu y Integers.Int.iwordsize = true) :
    Cop.semBinaryOperation cenv .Oshl (.Vint x) tuint (.Vint y) tuint m
      = some (.Vint (Integers.Int.shl x y)) := by
  show (if Integers.Int.ltu y Integers.Int.iwordsize
        then some (Val.Vint (Integers.Int.shl x y)) else none) = _
  rw [h]; rfl

/-- `x > c` at `(tuint, tint)`. -/
theorem semBinop_gt_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Ogt (.Vint x) tuint (.Vint c) tint m
      = some (Val.ofBool (Integers.Int.ltu c x)) := rfl

/-- A shift amount below 32 passes the guard. -/
theorem ltu_iwordsize (r : Nat) (hr : r < 32) :
    Integers.Int.ltu (Integers.Int.repr ((r : _root_.Int)))
      Integers.Int.iwordsize = true := by
  show Integers.Int.ltu (Integers.Int.repr ((r : _root_.Int)))
      (Integers.Int.repr ((32 : _root_.Int))) = true
  rw [show ((32 : _root_.Int)) = ((32 : Nat) : _root_.Int) from rfl,
      ltu_nat32 r 32 (by omega) (by omega), decide_eq_true_eq]
  omega

/-- `1U << r = 2^r`, for `r < 32`. -/
theorem shl_one_pow (r : Nat) (hr : r < 32) :
    Integers.Int.shl (Integers.Int.repr ((1 : _root_.Int)))
        (Integers.Int.repr ((r : _root_.Int)))
      = Integers.Int.repr (((2 ^ r : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show ((Integers.Int.repr ((1 : _root_.Int)))
        <<< ((Integers.Int.repr ((r : _root_.Int))).toNat) : BitVec 32).toNat = _
  rw [BitVec.toNat_shiftLeft, u32_toNat_repr, u32_toNat_repr,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : r < 4294967296)]
  have hp : (2 : Nat) ^ r < 4294967296 :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) hr) (by decide)
  rw [show BitVec.toNat (Integers.Int.repr ((1 : _root_.Int))) = 1 from rfl,
      show ((2 : Nat) ^ (32 : Nat)) = 4294967296 from rfl,
      Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by omega : 1 * 2 ^ r < 4294967296)]
  omega

section Enough

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (l : List (Ident × Val)) (H : HProp)

/-- `used = 1U << root;` -/
theorem set_used_triple (r : Nat) (hr : r < 32)
    (hmemR : (_root, .Vint (Integers.Int.repr ((r : _root_.Int)))) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ _used) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H)
      (.Sset _used (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
        (.Etempvar _root tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        ((_used, .Vint (Integers.Int.repr (((2 ^ r : Nat) : _root_.Int)))) :: l)
        H)) :=
  triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l H _used _ _
    (fun _ hp => hp) hne
    (fun le m hp hT _ _ => by
      refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
        (.Vint (Integers.Int.repr ((r : _root_.Int)))) _
        (EvalExpr.Econst_int _ _)
        (EvalExpr.Etempvar _root tuint _ (hT.get hmemR)) ?_
      simp only [typeof]
      rw [semBinop_shl_uint _ _ _ _ (ltu_iwordsize r hr),
          show (1 : _root_.Int) = ((1 : _root_.Int)) from rfl,
          shl_one_pow r hr])

/-- `mask = used - 1;` -/
theorem set_mask_triple (u : Nat) (hu : 1 ≤ u)
    (hmemU : (_used, .Vint (Integers.Int.repr ((u : _root_.Int)))) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ _mask) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H)
      (.Sset _mask (.Ebinop .Osub (.Etempvar _used tuint)
        (.Econst_int (Integers.Int.repr 1) tint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        ((_mask, .Vint (Integers.Int.repr (((u - 1 : Nat) : _root_.Int)))) :: l)
        H)) :=
  triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l H _mask _ _
    (fun _ hp => hp) hne
    (fun le m hp hT _ _ => by
      refine EvalExpr.Ebinop .Osub _ _ _
        (.Vint (Integers.Int.repr ((u : _root_.Int))))
        (.Vint (Integers.Int.repr 1)) _
        (EvalExpr.Etempvar _used tuint _ (hT.get hmemU))
        (EvalExpr.Econst_int _ _) ?_
      simp only [typeof]
      rw [semBinop_sub_uint_int]
      obtain ⟨k, hk⟩ : ∃ k, u = k + 1 := ⟨u - 1, by omega⟩
      subst hk
      show some (Val.Vint (Integers.Int.sub
                (Integers.Int.repr (((k + 1 : Nat) : _root_.Int)))
                (Integers.Int.repr (((1 : Nat) : _root_.Int))))) = _
      rw [u32_sub_one, show k + 1 - 1 = k from by omega])

/-! ### The ENOUGH capacity check

`if ((type == LENS && used > 852) || (type == DISTS && used > 592)) return 1;`

clightgen compiles the short-circuit into nested ifs over `_t'5`/`_t'6`.  The
pass-through records the negation — for LENS, `used ≤ 852`; for DISTS,
`used ≤ 592`; for CODES, nothing (the check is vacuous there, which is
precisely why assumption A5 exists). -/

abbrev enoughChk (ea eb : Ident) : Stmt :=
  .Ssequence
    (.Ssequence
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar _type tint)
          (.Econst_int (Integers.Int.repr 1) tint) tint)
        (.Sset ea (.Ecast (.Ebinop .Ogt (.Etempvar _used tuint)
            (.Econst_int (Integers.Int.repr 852) tint) tint) tbool))
        (.Sset ea (.Econst_int (Integers.Int.repr 0) tint)))
      (.Sifthenelse (.Etempvar ea tint)
        (.Sset eb (.Econst_int (Integers.Int.repr 1) tint))
        (.Sifthenelse (.Ebinop .Oeq (.Etempvar _type tint)
            (.Econst_int (Integers.Int.repr 2) tint) tint)
          (.Ssequence
            (.Sset eb (.Ecast (.Ebinop .Ogt (.Etempvar _used tuint)
                (.Econst_int (Integers.Int.repr 592) tint) tint) tbool))
            (.Sset eb (.Ecast (.Etempvar eb tint) tbool)))
          (.Sset eb (.Ecast (.Econst_int (Integers.Int.repr 0) tint) tbool)))))
    (.Sifthenelse (.Etempvar eb tint)
      (.Sreturn (some (.Econst_int (Integers.Int.repr 1) tint))) .Sskip)

/-- `used > c` on a tracked `tuint`, decided by the values. -/
theorem gt_uint_eval {e : Env} {le : TempEnv} {m : Mem} (u c : Nat)
    (hu : u < 4294967296) (hc : c < 4294967296)
    (hmemU : le.get _used
      = some (.Vint (Integers.Int.repr ((u : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m
        (.Ebinop .Ogt (.Etempvar _used tuint)
          (.Econst_int (Integers.Int.repr ((c : _root_.Int))) tint) tint) v
      ∧ Cop.boolVal v tint m = some (decide (c < u)) := by
  refine ⟨Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((c : _root_.Int)))
            (Integers.Int.repr ((u : _root_.Int)))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Ogt _ _ _ _ _ _
      (EvalExpr.Etempvar _used tuint _ hmemU) (EvalExpr.Econst_int _ _)
      (semBinop_gt_uint_int _ _ _ _)
  · simp only [boolVal_ofBool_int]
    rw [ltu_nat32 c u hc hu]

/-- **The ENOUGH check, LENS case.**  Either `used ≤ 852` and execution
    continues, or the table would not fit and `1` is returned. -/
theorem enough_LENS_triple (ea eb : Ident) (hab : ea ≠ eb)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hdbc : bh ≠ bc) (hdbo : bh ≠ bo) (hdco : bc ≠ bo)
    (vh vc vo : List MemVal)
    (hvh : vh.length = 4) (hvc : vc.length = 32) (hvo : vo.length = 32)
    (Hrest : HProp) (u : Nat) (hu : u < 4294967296)
    (hmemTy : (_type, .Vint (Integers.Int.repr 1)) ∈ l)
    (hmemU : (_used, .Vint (Integers.Int.repr ((u : _root_.Int)))) ∈ l)
    (hT5 : ∀ p ∈ l, p.1 ≠ ea) (hT6 : ∀ p ∈ l, p.1 ≠ eb)
    (Ret : Val → HProp)
    (hret : ∀ hr, Hrest hr → Ret (.Vint (Integers.Int.repr 1)) hr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))
      (enoughChk ea eb)
      { normal := fun e le hp => u ≤ 852 ∧
          ∃ lx : List (Ident × Val), ∃ _ : ∀ p ∈ l, p ∈ lx,
            LocalSt (envOf bh bc bo) lx
              (bytesPtsTo bh .Freeable 0 vh
               ∗ (bytesPtsTo bc .Freeable 0 vc
                  ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))) e le hp,
        brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
  have hTy : ∀ (le : TempEnv) (m : Mem), TempsHold l le →
      ∃ v, EvalExpr ge (envOf bh bc bo) le m
          (.Ebinop .Oeq (.Etempvar _type tint)
            (.Econst_int (Integers.Int.repr 1) tint) tint) v
        ∧ Cop.boolVal v tint m = some true := by
    intro le m hT
    refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr 1)
              (Integers.Int.repr 1)), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
        (EvalExpr.Etempvar _type tint _ (hT.get hmemTy))
        (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
    · rfl
  by_cases hgt : 852 < u
  · -- over capacity: t'5 = 1, t'6 = 1, return 1
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((eb, .Vint (Integers.Int.repr 1))
          :: (ea, .Vint (Integers.Int.repr 1)) :: l)
        (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))) _ _ _ ?_ ?_
    · refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((ea, .Vint (Integers.Int.repr 1)) :: l)
          (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT _ _ => hTy le mm hT) ?_
        exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l
          (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))
          ea _ _ (fun _ hp => hp) hT5
          (fun le mm hp hT _ _ => by
            refine EvalExpr.Ecast _ _
              (Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((852 : Nat)))
                (Integers.Int.repr ((u : _root_.Int))))) _
              (EvalExpr.Ebinop .Ogt _ _ _ _ _ _
                (EvalExpr.Etempvar _used tuint _ (hT.get hmemU))
                (EvalExpr.Econst_int _ _) (semBinop_gt_uint_int _ _ _ _)) ?_
            rw [ltu_nat32 852 u (by omega) hu,
                show decide (852 < u) = true from by
                  rw [decide_eq_true_eq]; exact hgt]
            rfl)
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT _ _ =>
            ⟨.Vint (Integers.Int.repr 1),
             EvalExpr.Etempvar ea tint _ (hT.get List.mem_cons_self), rfl⟩) ?_
        exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _
          (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))
          eb _ _ (fun _ hp => hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact hab
            · exact hT6 p hp2)
          (fun le mm hp hT _ _ => EvalExpr.Econst_int _ _)
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT _ _ =>
          ⟨.Vint (Integers.Int.repr 1),
           EvalExpr.Etempvar eb tint _ (hT.get List.mem_cons_self), rfl⟩) ?_
      refine triple_conseq ge fe f_inflate_table
        (return_const_triple ge fe bh bc bo
          ((eb, .Vint (Integers.Int.repr 1))
            :: (ea, .Vint (Integers.Int.repr 1)) :: l) vh vc vo Hrest
          (.Econst_int (Integers.Int.repr 1) tint)
          (Integers.Int.repr 1) Ret hcenv hdbc hdbo hdco hvh hvc hvo
          (fun le m => EvalExpr.Econst_int _ _) (fun m => rfl) hret)
        (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx)
  · -- within capacity: t'5 = 0, t'6 = 0, fall through
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((eb, .Vint (Integers.Int.repr 0))
          :: (ea, .Vint (Integers.Int.repr 0)) :: l)
        (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))) _ _ _ ?_ ?_
    · refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((ea, .Vint (Integers.Int.repr 0)) :: l)
          (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT _ _ => hTy le mm hT) ?_
        exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l
          (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))
          ea _ _ (fun _ hp => hp) hT5
          (fun le mm hp hT _ _ => by
            refine EvalExpr.Ecast _ _
              (Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((852 : Nat)))
                (Integers.Int.repr ((u : _root_.Int))))) _
              (EvalExpr.Ebinop .Ogt _ _ _ _ _ _
                (EvalExpr.Etempvar _used tuint _ (hT.get hmemU))
                (EvalExpr.Econst_int _ _) (semBinop_gt_uint_int _ _ _ _)) ?_
            rw [ltu_nat32 852 u (by omega) hu,
                show decide (852 < u) = false from by
                  rw [decide_eq_false_iff_not]; exact hgt]
            rfl)
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
          (fun le mm hp hT _ _ =>
            ⟨.Vint (Integers.Int.repr 0),
             EvalExpr.Etempvar ea tint _ (hT.get List.mem_cons_self), rfl⟩) ?_
        -- type == DISTS is false (type is LENS), so t'6 = 0
        refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
          (fun le mm hp hT _ _ => ?_) ?_
        · refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr 1)
              (Integers.Int.repr 2)), ?_, rfl⟩
          exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
            (EvalExpr.Etempvar _type tint _
              (hT.get (List.mem_cons_of_mem _ hmemTy)))
            (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
        · exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _
            (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))
            eb _ _ (fun _ hp => hp)
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · exact hab
              · exact hT6 p hp2)
            (fun le mm hp hT _ _ =>
              EvalExpr.Ecast _ _ (.Vint (Integers.Int.repr 0)) _
                (EvalExpr.Econst_int _ _) rfl)
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT _ _ =>
          ⟨.Vint (Integers.Int.repr 0),
           EvalExpr.Etempvar eb tint _ (hT.get List.mem_cons_self), rfl⟩) ?_
      refine triple_conseq ge fe f_inflate_table
        (triple_skip ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      exact ⟨by omega, _, fun p hp =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp), hx⟩

end Enough


/-! ## §16 Writing one entry inside the table region

The fill loop writes `next[(huff >> drop) + fill] = here` repeatedly.  For
**safety** we need only that each write lands inside the region — not what it
stores — so the written entry is re-absorbed afterwards and the loop
invariant's heap is *constant*.  That is what keeps the fill loop tractable: no
per-iteration table contents to track.

The region is carried as a chain of `codeCell`s rather than as raw `anyBytes`,
because the root back-pointer writes (§19) assign a *single field* and
`triple_assign` needs that field's `mapsto`.  See the `codeCell` block below
for why the raw-bytes form cannot be converted back. -/

/-- Carve entry `i` out of a region of `n` code entries. -/
theorem anyBytes_carve (p : Permission) (b : Block) (ofs : _root_.Int)
    (n i : Nat) (hi : i < n) :
    anyBytes p b ofs (4 * n)
      = anyBytes p b ofs (4 * i)
        ∗ (anyBytes p b (ofs + 4 * (i : _root_.Int)) 4
           ∗ anyBytes p b (ofs + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1))) := by
  rw [show 4 * n = 4 * i + (4 + 4 * (n - i - 1)) from by omega,
      anyBytes_split p b ofs (4 * i) (4 + 4 * (n - i - 1)),
      anyBytes_split p b (ofs + ((4 * i : Nat) : _root_.Int)) 4 (4 * (n - i - 1)),
      show ofs + ((4 * i : Nat) : _root_.Int) = ofs + 4 * (i : _root_.Int)
        from by omega,
      show ofs + 4 * (i : _root_.Int) + ((4 : Nat) : _root_.Int)
        = ofs + 4 * (i : _root_.Int) + 4 from by omega]

/-- `∃` distributes out of a `∗` on the left. -/
theorem hexists_sep_eq {α : Sort u} (f : α → HProp) (Q : HProp) :
    (HProp.hexists f) ∗ Q = HProp.hexists (fun x => f x ∗ Q) := by
  funext h
  refine propext ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨h1, h2, hd, heq, ⟨x, hf⟩, hq⟩ := hx
    exact ⟨x, h1, h2, hd, heq, hf, hq⟩
  · obtain ⟨x, h1, h2, hd, heq, hf, hq⟩ := hx
    exact ⟨h1, h2, hd, heq, ⟨x, hf⟩, hq⟩

/-- `anyBytes` as a nested `∃` — contents, then the length proof.  This is the
    form `triple_exists` peels, and it avoids the pure conjunct in
    `anyBytes`'s own definition. -/
theorem anyBytes_hexists (p : Permission) (b : Block) (ofs : _root_.Int)
    (n : Nat) :
    anyBytes p b ofs n
      = HProp.hexists (fun ob : List MemVal =>
          HProp.hexists (fun _ : ob.length = n => bytesPtsTo b p ofs ob)) := by
  funext h
  refine propext ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨ob, hob⟩ := hx
    obtain ⟨hlen, hb⟩ := pure_sep_elim hob
    exact ⟨ob, hlen, hb⟩
  · obtain ⟨ob, hlen, hb⟩ := hx
    exact ⟨ob, pure_sep_intro hlen hb⟩

/-- `∃` in a `LocalSt`'s heap slot is an `∃` over assertions — the form
    `triple_exists` can peel. -/
theorem localst_hexists {α : Sort u} (E : Env) (l : List (Ident × Val))
    (f : α → HProp) :
    LocalSt E l (HProp.hexists f)
      = fun e le hp => ∃ x, LocalSt E l (f x) e le hp := by
  funext e le hp
  refine propext ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨henv, hT, ⟨x, hf⟩⟩ := hx
    exact ⟨x, henv, hT, hf⟩
  · obtain ⟨x, henv, hT, hf⟩ := hx
    exact ⟨henv, hT, ⟨x, hf⟩⟩

/-! ### The table region as a chain of *cells*

Raw `anyBytes` supports a whole-entry struct copy but **not** a single-field
write: `triple_assign` wants the target field's `mapsto`, and an arbitrary
4-byte run is not an encoded entry (bytes may be `Undef` or pointer fragments),
so `here_assemble` cannot be run backwards.  The root back-pointer writes
(inftrees.c:291-293) are exactly such field writes.

The fix is to carry the region as a chain of *cells*, each cell being the three
field slots with their contents existentially quantified.  A cell entails
`anyBytes` (so the struct copy still goes through), and a concrete `hereBytes`
run entails a cell (so the copy's result restores the chain) — the two
directions that are actually needed, without claiming the false equality. -/

/-- Generalised `here_assemble`: three field `mapsto`s at an arbitrary
    (block, permission, offset) are the 4-byte run of their encodings. -/
theorem codeCell_eq_bytes (p : Permission) (b : Block) (ofs : _root_.Int)
    (hal : ofs % 4 = 0) (v1 v2 v3 : Val) :
    mapsto .Mint8unsigned p b ofs v1
      ∗ (mapsto .Mint8unsigned p b (ofs + 1) v2
         ∗ mapsto .Mint16unsigned p b (ofs + 2) v3)
    = bytesPtsTo b p ofs
        (encodeVal .Mint8unsigned v1
         ++ (encodeVal .Mint8unsigned v2 ++ encodeVal .Mint16unsigned v3)) := by
  rw [mapsto_eq_bytes (chunk := .Mint8unsigned)
        (show ofs % alignChunk .Mint8unsigned = 0 from by
          show ofs % (1 : _root_.Int) = 0; omega),
      mapsto_eq_bytes (chunk := .Mint8unsigned)
        (show (ofs + 1) % alignChunk .Mint8unsigned = 0 from by
          show (ofs + 1) % (1 : _root_.Int) = 0; omega),
      mapsto_eq_bytes (chunk := .Mint16unsigned)
        (show (ofs + 2) % alignChunk .Mint16unsigned = 0 from by
          show (ofs + 2) % (2 : _root_.Int) = 0; omega),
      bytesPtsTo_append, bytesPtsTo_append, length_encodeVal, length_encodeVal]
  show _ = bytesPtsTo b p ofs _
            ∗ (bytesPtsTo b p (ofs + ((1 : Nat) : _root_.Int)) _
               ∗ bytesPtsTo b p
                   (ofs + ((1 : Nat) : _root_.Int) + ((1 : Nat) : _root_.Int)) _)
  rw [show ofs + ((1 : Nat) : _root_.Int) = ofs + 1 from by omega,
      show ofs + 1 + ((1 : Nat) : _root_.Int) = ofs + 2 from by omega]

/-! `anyCell`, `codeCell` and `codeRegion` were moved to `InflateTableSpec.lean`
so that `preHeap`/`postHeap` and the body agree on the region's footprint — see
the `codeRegion` docstring there for why it cannot be `anyBytes`. -/

theorem codeRegion_zero (p : Permission) (b : Block) (ofs : _root_.Int) :
    codeRegion p b ofs 0 = HProp.emp := rfl

theorem codeRegion_succ (p : Permission) (b : Block) (ofs : _root_.Int)
    (n : Nat) :
    codeRegion p b ofs (n + 1) = codeCell p b ofs ∗ codeRegion p b (ofs + 4) n :=
  rfl

/-- A cell's bytes are *some* four bytes — the direction a whole-entry struct
    copy needs.  The converse is false, which is the whole reason the region is
    carried as cells rather than as `anyBytes`. -/
theorem codeCell_anyBytes (p : Permission) (b : Block) (ofs : _root_.Int)
    (hal : ofs % 4 = 0) : codeCell p b ofs ⊢ anyBytes p b ofs 4 := by
  intro h hc
  obtain ⟨h1, hr, hd, heq, ⟨v1, hm1⟩, h2, h3, hd2, heq2, ⟨v2, hm2⟩, ⟨v3, hm3⟩⟩ :=
    hc
  refine ⟨_, pure_sep_intro
    (show (encodeVal .Mint8unsigned v1
            ++ (encodeVal .Mint8unsigned v2
                ++ encodeVal .Mint16unsigned v3)).length = 4 from by
      rw [List.length_append, List.length_append, length_encodeVal,
          length_encodeVal, length_encodeVal]; rfl) ?_⟩
  rw [← codeCell_eq_bytes p b ofs hal v1 v2 v3]
  exact ⟨h1, hr, hd, heq, hm1, h2, h3, hd2, heq2, hm2, hm3⟩

/-- **The converse, at a written entry.**  After a struct copy the destination's
    bytes are concretely `hereBytes`, so the three field `mapsto`s *can* be
    recovered — which is what restores the region's cell structure. -/
theorem hereBytes_codeCell (p : Permission) (b : Block) (ofs : _root_.Int)
    (hal : ofs % 4 = 0) (op bits val : Nat) :
    bytesPtsTo b p ofs (hereBytes op bits val) ⊢ codeCell p b ofs := by
  intro h hb
  rw [show hereBytes op bits val
        = encodeVal .Mint8unsigned (.Vint (Integers.Int.repr ((op : Nat))))
          ++ (encodeVal .Mint8unsigned (.Vint (Integers.Int.repr ((bits : Nat))))
              ++ encodeVal .Mint16unsigned
                   (.Vint (Integers.Int.repr ((val : Nat))))) from rfl,
      ← codeCell_eq_bytes p b ofs hal] at hb
  obtain ⟨h1, hr, hd, heq, hm1, h2, h3, hd2, heq2, hm2, hm3⟩ := hb
  exact ⟨h1, hr, hd, heq, ⟨_, hm1⟩, h2, h3, hd2, heq2, ⟨_, hm2⟩, ⟨_, hm3⟩⟩

/-- A one-entry region. -/
theorem codeRegion_one (p : Permission) (b : Block) (ofs : _root_.Int) :
    codeRegion p b ofs 1 = codeCell p b ofs := by
  show codeCell p b ofs ∗ codeRegion p b (ofs + 4) 0 = _
  rw [codeRegion_zero, sep_emp_eq]

/-- Splitting a region anywhere. -/
theorem codeRegion_split (p : Permission) (b : Block) :
    ∀ (i : Nat) (ofs : _root_.Int) (j : Nat),
      codeRegion p b ofs (i + j)
        = codeRegion p b ofs i
          ∗ codeRegion p b (ofs + 4 * (i : _root_.Int)) j := by
  intro i
  induction i with
  | zero =>
      intro ofs j
      rw [Nat.zero_add, codeRegion_zero, emp_sep_eq,
          show ofs + 4 * ((0 : Nat) : _root_.Int) = ofs from by omega]
  | succ i ih =>
      intro ofs j
      rw [show i + 1 + j = (i + j) + 1 from by omega, codeRegion_succ,
          ih (ofs + 4) j, codeRegion_succ, sep_assoc_eq,
          show ofs + 4 + 4 * (i : _root_.Int)
            = ofs + 4 * ((i + 1 : Nat) : _root_.Int) from by push_cast; omega]

/-- Carve entry `i` out of a region of `n` entries — the `codeRegion` analogue
    of `anyBytes_carve`. -/
theorem codeRegion_carve (p : Permission) (b : Block) (ofs : _root_.Int)
    (n i : Nat) (hi : i < n) :
    codeRegion p b ofs n
      = codeCell p b (ofs + 4 * (i : _root_.Int))
        ∗ (codeRegion p b ofs i
           ∗ codeRegion p b (ofs + 4 * (i : _root_.Int) + 4) (n - i - 1)) := by
  have h1 : codeRegion p b (ofs + 4 * (i : _root_.Int)) (1 + (n - i - 1))
      = codeCell p b (ofs + 4 * (i : _root_.Int))
        ∗ codeRegion p b (ofs + 4 * (i : _root_.Int) + 4) (n - i - 1) := by
    rw [codeRegion_split p b 1 (ofs + 4 * (i : _root_.Int)) (n - i - 1),
        codeRegion_one,
        show ofs + 4 * (i : _root_.Int) + 4 * ((1 : Nat) : _root_.Int)
          = ofs + 4 * (i : _root_.Int) + 4 from by omega]
  conv => lhs; rw [show n = i + (1 + (n - i - 1)) from by omega]
  rw [codeRegion_split p b i ofs (1 + (n - i - 1)), h1]
  sep_cancel

section RegionWrite

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)

/-- The inner form: the destination entry as a concrete byte run. -/
theorem region_entry_write_bytes
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pr : Permission) (hpr : permOrder pr .Writable = true)
    (nB : Block) (nO : Integers.Ptrofs) (i : Nat)
    (op bits val : Nat) (oldBytes : List MemVal) (hold : oldBytes.length = 4)
    (haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
        (Integers.Int.repr ((i : _root_.Int))))
      = Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int))
    (haltgt : (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) % 2 = 0)
    (pid : Ident) (idxE : Expr)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemP : (pid, .Vptr nB nO) ∈ l)
    (hidx : ∀ (le : TempEnv) (m : Mem), TempsHold l le →
      EvalExpr ge (envOf bh bc bo) le m idxE
        (.Vint (Integers.Int.repr ((i : _root_.Int)))))
    (hcls : Cop.classifyAdd (tptr (Ty.Tstruct __1353 noattr)) (typeof idxE)
      = .pi (Ty.Tstruct __1353 noattr) .Unsigned) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int))
            oldBytes
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
      (.Sassign
        (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          idxE (tptr (Ty.Tstruct __1353 noattr))) (Ty.Tstruct __1353 noattr))
        (.Evar _here (Ty.Tstruct __1353 noattr)))
      (.only (LocalSt (envOf bh bc bo) l
        (bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int))
            (hereBytes op bits val)
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))) := by
  have hsz : sizeof ge.genv_cenv (Ty.Tstruct __1353 noattr) = 4 := by
    rw [hcenv]; exact InflateTable.Layout.code_sizeof
  have halb : alignofBlockcopy ge.genv_cenv (Ty.Tstruct __1353 noattr) = 2 := by
    rw [hcenv]; exact InflateTable.Layout.code_alignofBlockcopy
  refine triple_conseq ge fe f_inflate_table
    (triple_assign_copy ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (bytesPtsTo nB pr
            (Integers.Ptrofs.unsigned
              (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
                (Integers.Int.repr ((i : _root_.Int))))) oldBytes
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
      (LocalSt (envOf bh bc bo) l
        (bytesPtsTo nB pr
            (Integers.Ptrofs.unsigned
              (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
                (Integers.Int.repr ((i : _root_.Int)))))
            (hereBytes op bits val)
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
      _ _ .Freeable pr bh Integers.Ptrofs.zero nB
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
        (Integers.Int.repr ((i : _root_.Int))))
      (hereBytes op bits val) oldBytes
      (by decide) hpr
      (by simpa only [typeof] using InflateTable.Layout.code_accessMode)
      (by simp only [typeof]; rw [hereBytes_length, hsz]; rfl)
      (by rw [hold, hereBytes_length])
      (by simp only [typeof]; rw [halb, ptrofs_unsigned_zero]; intro _; rfl)
      (by simp only [typeof]; rw [halb, haddr]; intro _; exact haltgt)
      (fun e le hp m hP _ => by
        obtain ⟨henv, hT, hH⟩ := hP
        subst henv
        obtain ⟨hD, hSR, hdDS, heq, hbD, hSR'⟩ := hH
        subst heq
        obtain ⟨hS, hR, hdSR, heq2, hbS, hbR⟩ := hSR'
        subst heq2
        refine ⟨hS, hD, hR, hdSR, hdDS, rfl, hbS, hbD, ?_, ?_, ?_, ?_⟩
        · exact EvalLvalue.Ederef _ _ _ _
            (EvalExpr.Ebinop .Oadd _ _ _ (.Vptr nB nO)
              (.Vint (Integers.Int.repr ((i : _root_.Int)))) _
              (EvalExpr.Etempvar pid _ _ (hT.get hmemP)) (hidx le m hT)
              (semAdd_ptr_int _ _ _ _ _ hcls))
        · exact eval_here_base ge bh bc bo
        · simp only [typeof]
          exact semCast_struct_same bh Integers.Ptrofs.zero __1353 noattr noattr m
        · intro hD' hbD' hd'
          exact ⟨rfl, hT, hD', Heap.union hS hR, hd', rfl, hbD',
                 hS, hR, hdSR, rfl, hbS, hbR⟩))
    (fun e le hp hx => by rw [haddr]; exact hx)
    (fun e le hp hx => by rw [haddr] at hx; exact hx)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! ### Picking one field out of a cell

Three orientations of the same `∗`-triple: each names one field slot as the
head, which is the shape a single-field `triple_assign` consumes.  The `+ ↑d`
form (rather than the literal offset) is what the write rule's `hcarve`
hypothesis expects. -/

theorem codeCell_carve_op (p : Permission) (b : Block) (ofs : _root_.Int) :
    codeCell p b ofs
      = anyCell .Mint8unsigned p b (ofs + ((0 : Nat) : _root_.Int))
        ∗ (anyCell .Mint8unsigned p b (ofs + 1)
           ∗ anyCell .Mint16unsigned p b (ofs + 2)) := by
  rw [show ofs + ((0 : Nat) : _root_.Int) = ofs from by omega]; rfl

theorem codeCell_carve_bits (p : Permission) (b : Block) (ofs : _root_.Int) :
    codeCell p b ofs
      = anyCell .Mint8unsigned p b (ofs + ((1 : Nat) : _root_.Int))
        ∗ (anyCell .Mint8unsigned p b ofs
           ∗ anyCell .Mint16unsigned p b (ofs + 2)) := by
  rw [show ofs + ((1 : Nat) : _root_.Int) = ofs + 1 from by omega]
  show anyCell .Mint8unsigned p b ofs
        ∗ (anyCell .Mint8unsigned p b (ofs + 1)
           ∗ anyCell .Mint16unsigned p b (ofs + 2)) = _
  sep_cancel

theorem codeCell_carve_val (p : Permission) (b : Block) (ofs : _root_.Int) :
    codeCell p b ofs
      = anyCell .Mint16unsigned p b (ofs + ((2 : Nat) : _root_.Int))
        ∗ (anyCell .Mint8unsigned p b ofs
           ∗ anyCell .Mint8unsigned p b (ofs + 1)) := by
  rw [show ofs + ((2 : Nat) : _root_.Int) = ofs + 2 from by omega]
  show anyCell .Mint8unsigned p b ofs
        ∗ (anyCell .Mint8unsigned p b (ofs + 1)
           ∗ anyCell .Mint16unsigned p b (ofs + 2)) = _
  sep_cancel

/-- **The write, at four anonymous bytes.**  `region_entry_write_bytes` needs the
    destination's *concrete* contents; this peels `anyBytes`' two binders once
    and for all, so both region flavours reduce to a carve plus a frame
    rearrangement. -/
theorem region_entry_write_at
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pr : Permission) (hpr : permOrder pr .Writable = true)
    (nB : Block) (nO : Integers.Ptrofs) (i : Nat)
    (op bits val : Nat)
    (haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
        (Integers.Int.repr ((i : _root_.Int))))
      = Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int))
    (haltgt : (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) % 2 = 0)
    (pid : Ident) (idxE : Expr)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemP : (pid, .Vptr nB nO) ∈ l)
    (hidx : ∀ (le : TempEnv) (m : Mem), TempsHold l le →
      EvalExpr ge (envOf bh bc bo) le m idxE
        (.Vint (Integers.Int.repr ((i : _root_.Int)))))
    (hcls : Cop.classifyAdd (tptr (Ty.Tstruct __1353 noattr)) (typeof idxE)
      = .pi (Ty.Tstruct __1353 noattr) .Unsigned) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) 4
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
      (.Sassign
        (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          idxE (tptr (Ty.Tstruct __1353 noattr))) (Ty.Tstruct __1353 noattr))
        (.Evar _here (Ty.Tstruct __1353 noattr)))
      (.only (LocalSt (envOf bh bc bo) l
        (bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int))
            (hereBytes op bits val)
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))) := by
  refine localst_perm ge fe (envOf bh bc bo) l _
    (HProp.hexists (fun ob =>
      (fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 =>
        bytesPtsTo nB pr
          (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ob
      ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
    (by rw [anyBytes_hexists pr nB
              (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) 4,
            hexists_sep_eq]) _ _ ?_
  rw [localst_hexists]
  refine triple_exists ge fe f_inflate_table _ _ _ (fun ob => ?_)
  refine localst_perm ge fe (envOf bh bc bo) l _
    (HProp.hexists (fun _ : ob.length = 4 =>
      bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob
      ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
    (by show HProp.hexists (fun _ : ob.length = 4 =>
              bytesPtsTo nB pr
                (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)
            ∗ _ = _
        rw [hexists_sep_eq]) _ _ ?_
  rw [localst_hexists]
  refine triple_exists ge fe f_inflate_table _ _ _ (fun hlen => ?_)
  exact region_entry_write_bytes ge fe bh bc bo hcenv pr hpr nB nO i op bits val
    ob hlen haddr haltgt pid idxE l Hrest hmemP hidx hcls

/-- **One entry written inside a raw-bytes table region.**

    `*(p + i) = here` with the region `n` code entries at `p` and `i < n` —
    that bound is the entire safety content of the fill loop.

    **Superseded** by `codeRegion_entry_write` below, which is what the fill
    loop uses: an `anyBytes` region cannot support the single-field writes of
    §19.  Kept as the raw-bytes form of the same argument. -/
theorem region_entry_write
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pr : Permission) (hpr : permOrder pr .Writable = true)
    (nB : Block) (nO : Integers.Ptrofs) (n i : Nat) (hi : i < n)
    (hn31 : (n : _root_.Int) < 2147483648)
    (op bits val : Nat)
    (hal : Integers.Ptrofs.unsigned nO % 4 = 0)
    (hno : Integers.Ptrofs.unsigned nO + 4 * (n : _root_.Int)
             < 18446744073709551616)
    (pid : Ident) (idxE : Expr)
    (hcls : Cop.classifyAdd (tptr (Ty.Tstruct __1353 noattr)) (typeof idxE)
      = .pi (Ty.Tstruct __1353 noattr) .Unsigned)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemP : (pid, .Vptr nB nO) ∈ l)
    (hidx : ∀ (le : TempEnv) (m : Mem), TempsHold l le →
      EvalExpr ge (envOf bh bc bo) le m idxE
        (.Vint (Integers.Int.repr ((i : _root_.Int))))) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * n)
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
      (.Sassign
        (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          idxE (tptr (Ty.Tstruct __1353 noattr))) (Ty.Tstruct __1353 noattr))
        (.Evar _here (Ty.Tstruct __1353 noattr)))
      (.only (LocalSt (envOf bh bc bo) l
        (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * n)
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))) := by
  have hsz : sizeof ge.genv_cenv (Ty.Tstruct __1353 noattr) = 4 := by
    rw [hcenv]; exact InflateTable.Layout.code_sizeof
  have haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
        (Integers.Int.repr ((i : _root_.Int))))
      = Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) := by
    refine idxOfs_unsigned ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
      i 4 hsz (by decide) (by omega) ?_
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned nO = A := ⟨_, rfl⟩
    rw [hA] at hno ⊢
    have h2 : A + 4 * ((n : Nat) : _root_.Int)
        < (18446744073709551616 : _root_.Int) := hno
    show A + ((4 : Nat) : _root_.Int) * ((i : Nat) : _root_.Int)
          < (18446744073709551616 : _root_.Int)
    omega
  have haltgt : (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) % 2 = 0 := by
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned nO = A := ⟨_, rfl⟩
    rw [hA] at hal ⊢
    have h2 : A % (4 : _root_.Int) = 0 := hal
    show (A + 4 * ((i : Nat) : _root_.Int)) % (2 : _root_.Int) = 0
    omega
  have hcarve := anyBytes_carve pr nB (Integers.Ptrofs.unsigned nO) n i hi
  -- the region's heap with the target entry's `∃` pushed outermost
  -- (this reassociation pattern was settled on a toy instance first)
  have hpre : (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * n)
      ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))
      = HProp.hexists (fun ob => (fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 => bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ob
          ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)) ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i) ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))) := by
    rw [hcarve, anyBytes_hexists pr nB
          (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) 4,
        show HProp.hexists (fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 => bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1))
          = HProp.hexists (fun ob => (fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 => bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ob ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)))
          from hexists_sep_eq _ _,
        show anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i) ∗ HProp.hexists (fun ob => (fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 => bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ob
              ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)))
          = HProp.hexists (fun ob => ((fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 => bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ob ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)))
              ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i)) from by
          rw [sep_comm_eq]; exact hexists_sep_eq _ _,
        show HProp.hexists (fun ob => ((fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 => bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ob ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)))
              ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i)) ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)
          = HProp.hexists (fun ob => (((fun ob : List MemVal => HProp.hexists (fun _ : ob.length = 4 => bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)) ob ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)))
              ∗ anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i)) ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)) from hexists_sep_eq _ _]
    refine congrArg HProp.hexists ?_
    funext ob
    sep_cancel
  -- rewrite the precondition, then peel the two binders
  refine localst_perm ge fe (envOf bh bc bo) l _ _ hpre _ _ ?_
  rw [localst_hexists]
  refine triple_exists ge fe f_inflate_table _ _ _ (fun ob => ?_)
  -- the length proof is the inner `∃`; peel it the same way
  refine localst_perm ge fe (envOf bh bc bo) l _
    (HProp.hexists (fun _ : ob.length = 4 =>
      bytesPtsTo nB pr (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob
      ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)) ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i) ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))))
    (by show HProp.hexists (fun _ : ob.length = 4 =>
              bytesPtsTo nB pr
                (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob)
            ∗ _ = _
        rw [hexists_sep_eq]) _ _ ?_
  rw [localst_hexists]
  refine triple_exists ge fe f_inflate_table _ _ _ (fun hlen => ?_)
  -- now apply the concrete-bytes form, and rejoin the region afterwards
  refine triple_conseq ge fe f_inflate_table
    (region_entry_write_bytes ge fe bh bc bo hcenv pr hpr nB nO i op bits val
      ob hlen haddr haltgt pid idxE l
      (anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)) ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i) ∗ Hrest))
      hmemP hidx hcls)
    (fun e le hp hx => ?_) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · obtain ⟨henv, hT, hH⟩ := hx
    refine ⟨henv, hT, ?_⟩
    rw [show bytesPtsTo nB pr
              (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob
            ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)) ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i) ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
          = bytesPtsTo nB pr
              (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) ob
            ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val)
               ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)) ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i) ∗ Hrest)))
        from by sep_cancel] at hH
    exact hH
  · -- the written entry weakens back into `anyBytes`, and the region rejoins
    obtain ⟨henv, hT, hH⟩ := hx
    refine ⟨henv, hT, ?_⟩
    obtain ⟨hE, hR, hdER, heq, hbE, hR'⟩ := hH
    subst heq
    obtain ⟨hHere, hR2, hd2, heq2, hbHere, hR2'⟩ := hR'
    subst heq2
    obtain ⟨hSuf, hR3, hd3, heq3, hbSuf, hR3'⟩ := hR2'
    subst heq3
    obtain ⟨hPre, hRest2, hd4, heq4, hbPre, hbRest⟩ := hR3'
    subst heq4
    have hbE' : anyBytes pr nB
        (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) 4 hE := by
      have h := anyBytes_of_bytesPtsTo hbE
      rw [hereBytes_length] at h
      exact h
    -- reassemble: the region as a whole, then the caller's rest
    rw [show anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * n)
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)
        = anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) 4
          ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val)
             ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4) (4 * (n - i - 1)) ∗ (anyBytes pr nB (Integers.Ptrofs.unsigned nO) (4 * i) ∗ Hrest)))
        from by rw [hcarve]; sep_cancel]
    exact ⟨hE, _, hdER, rfl, hbE',
           hHere, _, hd2, rfl, hbHere,
           hSuf, _, hd3, rfl, hbSuf, hPre, hRest2, hd4, rfl, hbPre, hbRest⟩

/-- **One entry written inside a *cell-structured* region.**

    Same statement as `region_entry_write`, but the region is a `codeRegion`, so
    the entry's three field slots survive the write.  That is what lets the main
    loop write a whole entry here and a single field there (the root
    back-pointer, inftrees.c:291-293) against one invariant. -/
theorem codeRegion_entry_write
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pr : Permission) (hpr : permOrder pr .Writable = true)
    (nB : Block) (nO : Integers.Ptrofs) (n i : Nat) (hi : i < n)
    (hn31 : (n : _root_.Int) < 2147483648)
    (op bits val : Nat)
    (hal : Integers.Ptrofs.unsigned nO % 4 = 0)
    (hno : Integers.Ptrofs.unsigned nO + 4 * (n : _root_.Int)
             < 18446744073709551616)
    (pid : Ident) (idxE : Expr)
    (hcls : Cop.classifyAdd (tptr (Ty.Tstruct __1353 noattr)) (typeof idxE)
      = .pi (Ty.Tstruct __1353 noattr) .Unsigned)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemP : (pid, .Vptr nB nO) ∈ l)
    (hidx : ∀ (le : TempEnv) (m : Mem), TempsHold l le →
      EvalExpr ge (envOf bh bc bo) le m idxE
        (.Vint (Integers.Int.repr ((i : _root_.Int))))) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (codeRegion pr nB (Integers.Ptrofs.unsigned nO) n
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))
      (.Sassign
        (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
          idxE (tptr (Ty.Tstruct __1353 noattr))) (Ty.Tstruct __1353 noattr))
        (.Evar _here (Ty.Tstruct __1353 noattr)))
      (.only (LocalSt (envOf bh bc bo) l
        (codeRegion pr nB (Integers.Ptrofs.unsigned nO) n
         ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)))) := by
  have hsz : sizeof ge.genv_cenv (Ty.Tstruct __1353 noattr) = 4 := by
    rw [hcenv]; exact InflateTable.Layout.code_sizeof
  have haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
        (Integers.Int.repr ((i : _root_.Int))))
      = Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) := by
    refine idxOfs_unsigned ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
      i 4 hsz (by decide) (by omega) ?_
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned nO = A := ⟨_, rfl⟩
    rw [hA] at hno ⊢
    have h2 : A + 4 * ((n : Nat) : _root_.Int)
        < (18446744073709551616 : _root_.Int) := hno
    show A + ((4 : Nat) : _root_.Int) * ((i : Nat) : _root_.Int)
          < (18446744073709551616 : _root_.Int)
    omega
  have halI : (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) % 4 = 0 := by
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned nO = A := ⟨_, rfl⟩
    rw [hA] at hal ⊢
    have h2 : A % (4 : _root_.Int) = 0 := hal
    show (A + 4 * ((i : Nat) : _root_.Int)) % (4 : _root_.Int) = 0
    omega
  have haltgt : (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int)) % 2 = 0 := by
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned nO = A := ⟨_, rfl⟩
    rw [hA] at hal ⊢
    have h2 : A % (4 : _root_.Int) = 0 := hal
    show (A + 4 * ((i : Nat) : _root_.Int)) % (2 : _root_.Int) = 0
    omega
  have hre : (codeRegion pr nB (Integers.Ptrofs.unsigned nO) n
        ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest))
      = codeCell pr nB (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int))
        ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val)
           ∗ (codeRegion pr nB (Integers.Ptrofs.unsigned nO) i
              ∗ (codeRegion pr nB
                   (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4)
                   (n - i - 1) ∗ Hrest))) := by
    rw [codeRegion_carve pr nB (Integers.Ptrofs.unsigned nO) n i hi]
    sep_cancel
  refine triple_conseq ge fe f_inflate_table
    (region_entry_write_at ge fe bh bc bo hcenv pr hpr nB nO i op bits val
      haddr haltgt pid idxE l
      (codeRegion pr nB (Integers.Ptrofs.unsigned nO) i
       ∗ (codeRegion pr nB
            (Integers.Ptrofs.unsigned nO + 4 * (i : _root_.Int) + 4)
            (n - i - 1) ∗ Hrest))
      hmemP hidx hcls)
    (fun e le hp hx => ?_) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · obtain ⟨henv, hT, hH⟩ := hx
    refine ⟨henv, hT, ?_⟩
    rw [hre] at hH
    exact sep_mono (codeCell_anyBytes pr nB _ halI) (entails_refl _) hp hH
  · obtain ⟨henv, hT, hH⟩ := hx
    refine ⟨henv, hT, ?_⟩
    rw [hre]
    exact sep_mono (hereBytes_codeCell pr nB _ halI op bits val)
      (entails_refl _) hp hH

end RegionWrite

/-! ### Framing a `LocalSt`

`Sep.triple_frame` adds a heap-only frame `Q`, but produces `fun e le => P e le ∗ Q`
rather than a `LocalSt` — equivalent, since `LocalSt`'s environment and
temporaries conditions do not mention the heap, but not syntactically equal.
`localst_frame_only` does the conversion once, for the `.only`-postcondition
shape the straight-line segments have.  The chain needs it wherever a
segment's footprint is *smaller* than the ambient one — `readRoot`, whose
triple mentions only the `*bits` cell, is the first. -/

theorem localst_sep (E : Env) (l : List (Ident × Val)) (H Q : HProp)
    (e : Env) (le : TempEnv) (hp : Heap) :
    (LocalSt E l H e le ∗ Q) hp ↔ LocalSt E l (H ∗ Q) e le hp := by
  constructor
  · rintro ⟨h1, h2, hd, heq, ⟨henv, hT, hH⟩, hQ⟩
    exact ⟨henv, hT, h1, h2, hd, heq, hH, hQ⟩
  · rintro ⟨henv, hT, h1, h2, hd, heq, hH, hQ⟩
    exact ⟨h1, h2, hd, heq, ⟨henv, hT, hH⟩, hQ⟩

theorem localst_frame_only (ge : CGenv) (fe : EntryRel) (E : Env)
    (l l' : List (Ident × Val)) (H H' Q : HProp) (s : Stmt)
    (h : Triple ge fe f_inflate_table (LocalSt E l H) s
      (.only (LocalSt E l' H'))) :
    Triple ge fe f_inflate_table (LocalSt E l (H ∗ Q)) s
      (.only (LocalSt E l' (H' ∗ Q))) := by
  refine triple_conseq ge fe f_inflate_table
    (triple_frame ge fe f_inflate_table _ s _ Q h)
    (fun e le hp hx => (localst_sep E l H Q e le hp).mpr hx)
    (fun e le hp hx => (localst_sep E l' H' Q e le hp).mp hx)
    (fun _ _ _ hx => ?_) (fun _ _ _ hx => ?_) (fun _ _ hx => ?_) ?_
  · obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim
  · obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim
  · obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim
  · intro _ _ _ _ hx
    obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim

/-- **Framing a straight-line segment.**  The segments that cannot `return`
    state their postcondition as `{ normal := …, brk := R.brk, … }` for an
    arbitrary `R`, so they hold in particular at the all-`no` exit conditions;
    there `Sep.triple_frame` applies and the frame can be added.  Widening the
    exits back to the ambient `R` afterwards is free, because `no` entails
    everything.

    Segments that *can* return are **not** framed this way — they are already
    heap-polymorphic in an explicit `Hrest`, and their `hret` receives exactly
    the residual the `return` hands back (§8).  Framing them would wrongly
    put the frame inside `Ret`. -/
theorem frame_seg (ge : CGenv) (fe : EntryRel) (E : Env)
    (l l' : List (Ident × Val)) (H H' Q : HProp) (s : Stmt)
    (R : Sep.ExitConds)
    (h : ∀ R' : Sep.ExitConds, Triple ge fe f_inflate_table (LocalSt E l H) s
      { normal := LocalSt E l' H', brk := R'.brk, cont := R'.cont,
        ret := R'.ret, goto := R'.goto }) :
    Triple ge fe f_inflate_table (LocalSt E l (H ∗ Q)) s
      { normal := LocalSt E l' (H' ∗ Q), brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (localst_frame_only ge fe E l l' H H' Q s
      (h { normal := LocalSt E l' H', brk := Assn.no, cont := Assn.no,
           ret := fun _ _ => False, goto := fun _ => Assn.no }))
    (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
    (fun _ _ _ _ hx => hx.elim)

/-- **The general framing rule.**  `frame_seg` requires the segment's `normal`
    exit to be a bare `LocalSt`, but several are existentials over one
    (`Post3`/`Post4` quantify the scanned bound, `Post5` carries a pure fact).
    Here the caller supplies the post implication, whose only real content is
    pushing the frame `Q` inside the existential with `localst_sep`. -/
theorem frame_seg_gen (ge : CGenv) (fe : EntryRel) (E : Env)
    (l : List (Ident × Val)) (H Q : HProp) (s : Stmt)
    (Nrm Nrm' : Sep.Assn) (R : Sep.ExitConds)
    (h : ∀ R' : Sep.ExitConds, Triple ge fe f_inflate_table (LocalSt E l H) s
      { normal := Nrm, brk := R'.brk, cont := R'.cont, ret := R'.ret,
        goto := R'.goto })
    (hn : ∀ e le hp, (Nrm e le ∗ Q) hp → Nrm' e le hp) :
    Triple ge fe f_inflate_table (LocalSt E l (H ∗ Q)) s
      { normal := Nrm', brk := R.brk, cont := R.cont, ret := R.ret,
        goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (triple_frame ge fe f_inflate_table _ s
      { normal := Nrm, brk := Assn.no, cont := Assn.no,
        ret := fun _ _ => False, goto := fun _ => Assn.no } Q
      (h { normal := Nrm, brk := Assn.no, cont := Assn.no,
           ret := fun _ _ => False, goto := fun _ => Assn.no }))
    (fun e le hp hx => (localst_sep E l H Q e le hp).mpr hx) hn
    (fun _ _ _ hx => ?_) (fun _ _ _ hx => ?_) (fun _ _ hx => ?_) ?_
  · obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim
  · obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim
  · obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim
  · intro _ _ _ _ hx
    obtain ⟨_, _, _, _, hf, _⟩ := hx; exact hf.elim

/-- The `.only`-postcondition variant of `frame_seg`, for the segments whose
    triple is stated with `Sep.ExitConds.only` rather than a pass-through `R`
    (`read_root_triple`, the two clamps). -/
theorem frame_seg_only (ge : CGenv) (fe : EntryRel) (E : Env)
    (l l' : List (Ident × Val)) (H H' Q : HProp) (s : Stmt)
    (R : Sep.ExitConds)
    (h : Triple ge fe f_inflate_table (LocalSt E l H) s
      (.only (LocalSt E l' H'))) :
    Triple ge fe f_inflate_table (LocalSt E l (H ∗ Q)) s
      { normal := LocalSt E l' (H' ∗ Q), brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (localst_frame_only ge fe E l l' H H' Q s h)
    (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
    (fun _ _ _ _ hx => hx.elim)

/-! ### `fullBody` segment 9 — the `max == 0` `if`

`maxzero_block_triple` (§13) proves the block itself, but wants its footprint
already carved: `here` as three field cells and the first two table entries as
concrete byte runs.  Doing that carve in the chain would mean carrying
the carved shape through every other segment, so it is done **here**, inside
the `if`, and only on the branch that needs it.  The `max ≠ 0` branch is
`Sskip` and keeps the uncarved footprint, which is what §6 and §9-§12 expect. -/

section MaxZeroIf

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (pt pb pr : Permission)
variable (tblB bitsB tB : Block) (tblO bitsO tO : Integers.Ptrofs)
variable (k : Nat) (bv : Val) (vc vo : List MemVal) (Hrest : HProp)

/-- The footprint the `if` is entered with — `here` and the table region whole. -/
abbrev MZpre : HProp :=
  undefBytes .Freeable bh 0 4
    ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
      ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) (2 + k)
        ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
          ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo
              ∗ (Hrest))))))

/-- The footprint `maxzero_block_triple` consumes, with the region's remaining
    `k` entries folded into its frame. -/
abbrev MZcar (e0 e1 : List MemVal) : HProp :=
  mapsto .Mint8unsigned .Freeable bh 0 .Vundef
    ∗ (mapsto .Mint8unsigned .Freeable bh 1 .Vundef
      ∗ (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
        ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
          ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO) e0
            ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO + 4) e1
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                ∗ (bytesPtsTo bc .Freeable 0 vc
                  ∗ (bytesPtsTo bo .Freeable 0 vo
                    ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO + 8) k
                      ∗ (Hrest))))))))))

/-- Two entries off the front of a region. -/
theorem mz_region_split (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat) :
    codeRegion p b ofs (2 + n)
      = codeCell p b ofs ∗ (codeCell p b (ofs + 4) ∗ codeRegion p b (ofs + 8) n) := by
  rw [codeRegion_split p b 2 ofs n, codeRegion_succ, codeRegion_one,
      show ofs + 4 * ((2 : Nat) : _root_.Int) = ofs + 8 from by omega,
      sep_assoc_eq]

/-- The carve, as an implication between assertions — the form `triple_conseq`
    takes.  The two `anyBytes` existentials are peeled with `pure_sep_elim`, and
    the heap decomposition is *reassembled unchanged*: only the two cells'
    predicates weaken, so the witness tuple is literally the same. -/
theorem mz_carve (l : List (Ident × Val))
    (hal : Integers.Ptrofs.unsigned tO % 4 = 0) :
    ∀ e le hp,
      LocalSt (envOf bh bc bo) l
        (MZpre bh bc bo pt pb pr tblB bitsB tB tblO bitsO tO k bv vc vo Hrest) e le hp →
      ∃ e0 e1 : List MemVal, ∃ _ : e0.length = 4, ∃ _ : e1.length = 4,
        LocalSt (envOf bh bc bo) l
          (MZcar bh bc bo pt pb pr tblB bitsB tB tblO bitsO tO k bv vc vo Hrest e0 e1)
          e le hp := by
  intro e le hp hx
  obtain ⟨henv, hT, hH⟩ := hx
  rw [show MZpre bh bc bo pt pb pr tblB bitsB tB tblO bitsO tO k bv vc vo Hrest
        = mapsto .Mint8unsigned .Freeable bh 0 .Vundef
              ∗ (mapsto .Mint8unsigned .Freeable bh 1 .Vundef
                ∗ (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
                  ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
                    ∗ (codeCell pr tB (Integers.Ptrofs.unsigned tO)
                      ∗ (codeCell pr tB (Integers.Ptrofs.unsigned tO + 4)
                        ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                          ∗ (bytesPtsTo bc .Freeable 0 vc
                            ∗ (bytesPtsTo bo .Freeable 0 vo
                              ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO + 8) k
                                ∗ (Hrest))))))))))
      from by
        show undefBytes .Freeable bh 0 4 ∗ _ = _
        rw [here_carve bh, mz_region_split pr tB (Integers.Ptrofs.unsigned tO) k]
        sep_cancel] at hH
  have hH2 : (mapsto .Mint8unsigned .Freeable bh 0 .Vundef
          ∗ (mapsto .Mint8unsigned .Freeable bh 1 .Vundef
            ∗ (mapsto .Mint16unsigned .Freeable bh 2 .Vundef
              ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
                ∗ (anyBytes pr tB (Integers.Ptrofs.unsigned tO) 4
                  ∗ (anyBytes pr tB (Integers.Ptrofs.unsigned tO + 4) 4
                    ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) bv
                      ∗ (bytesPtsTo bc .Freeable 0 vc
                        ∗ (bytesPtsTo bo .Freeable 0 vo
                          ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO + 8) k
                            ∗ (Hrest))))))))))) hp := by
    refine sep_mono (entails_refl _) (sep_mono (entails_refl _)
      (sep_mono (entails_refl _) (sep_mono (entails_refl _)
        (sep_mono (codeCell_anyBytes pr tB _ hal)
          (sep_mono (codeCell_anyBytes pr tB _
              -- `hal` is stated at `CC.Z`, where `omega` cannot see it (see
              -- `no_wrap_mono`); re-elaborate it at `_root_.Int` first.
              (by obtain ⟨A, hA⟩ : ∃ A : _root_.Int,
                    Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
                  have hal' : A % (4 : _root_.Int) = 0 := by rw [← hA]; exact hal
                  rw [hA]
                  omega))
            (entails_refl _)))))) hp hH
  obtain ⟨h1, r1, d1, q1, m1, hH2⟩ := hH2
  obtain ⟨h2, r2, d2, q2, m2, hH2⟩ := hH2
  obtain ⟨h3, r3, d3, q3, m3, hH2⟩ := hH2
  obtain ⟨h4, r4, d4, q4, m4, hH2⟩ := hH2
  obtain ⟨h5, r5, d5, q5, ⟨b0, hb0⟩, hH2⟩ := hH2
  obtain ⟨h6, r6, d6, q6, ⟨b1, hb1⟩, hrest⟩ := hH2
  obtain ⟨hl0, hb0⟩ := pure_sep_elim hb0
  obtain ⟨hl1, hb1⟩ := pure_sep_elim hb1
  refine ⟨b0, b1, hl0, hl1, henv, hT, ?_⟩
  subst q1; subst q2; subst q3; subst q4; subst q5; subst q6
  exact ⟨h1, _, d1, rfl, m1, h2, _, d2, rfl, m2, h3, _, d3, rfl, m3,
         h4, _, d4, rfl, m4, h5, _, d5, rfl, hb0, h6, _, d6, rfl, hb1, hrest⟩

/-- **`fullBody` segment 9.**  `if (max == 0) { … return 0; }`

    The block never falls through (`maxzero_block_triple`'s `normal` is `no`),
    so the `normal` exit of the whole `if` carries `max ≠ 0` — which is exactly
    what §6's `min` scan and everything after it need. -/
theorem maxzero_if_triple (M : Nat) (hM32 : M < 4294967296)
    (l : List (Ident × Val))
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hdbc : bh ≠ bc) (hdbo : bh ≠ bo) (hdco : bc ≠ bo)
    (hptR : permOrder pt .Readable = true)
    (hptW : permOrder pt .Writable = true)
    (hpb : permOrder pb .Writable = true)
    (hpr : permOrder pr .Writable = true)
    (hvc : vc.length = 32) (hvo : vo.length = 32)
    (hal : Integers.Ptrofs.unsigned tO % 4 = 0)
    (haddr1 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
        (Integers.Int.repr 1)) = Integers.Ptrofs.unsigned tO + 4)
    (hmemM : (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) ∈ l)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hmemB : (_bits, .Vptr bitsB bitsO) ∈ l)
    (hT1 : ∀ p ∈ l, p.1 ≠ _t'1) (hT2 : ∀ p ∈ l, p.1 ≠ _t'2)
    (Ret : Val → HProp)
    (hret : ∀ hr,
      (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
          (.Vint (Integers.Int.repr 1))
       ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
            (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed
              (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                (Integers.Int.repr 1)) (Integers.Int.repr 1)))
          ∗ (bytesPtsTo tB pr
               (Integers.Ptrofs.unsigned
                 (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed tO
                   (Integers.Int.repr 1))) (hereBytes 64 1 0)
             ∗ (bytesPtsTo tB pr (Integers.Ptrofs.unsigned tO)
                  (hereBytes 64 1 0)
                ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO + 8) k
                   ∗ Hrest))))) hr →
      Ret (.Vint (Integers.Int.repr 0)) hr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (MZpre bh bc bo pt pb pr tblB bitsB tB tblO bitsO tO k bv vc vo Hrest))
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar _max tuint)
        (.Econst_int (Integers.Int.repr 0) tint) tint) maxZeroBlock .Sskip)
      { normal := fun e le hp => M ≠ 0 ∧
          LocalSt (envOf bh bc bo) l
            (MZpre bh bc bo pt pb pr tblB bitsB tB tblO bitsO tO k bv vc vo
              Hrest) e le hp,
        brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
  by_cases hM0 : M = 0
  · -- `max == 0`: the block runs and returns; `normal` is unreachable
    refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => by
        have h := eqz_uint_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
          _max M hM32 (hT'.get hmemM)
        rw [show decide (M = 0) = true from by rw [decide_eq_true_eq]; exact hM0]
          at h
        exact h) ?_
    refine triple_conseq ge fe f_inflate_table
      (triple_exists ge fe f_inflate_table _ _ _ (fun (e0 : List MemVal) =>
        triple_exists ge fe f_inflate_table _ _ _ (fun (e1 : List MemVal) =>
          triple_exists ge fe f_inflate_table _ _ _ (fun (h0 : e0.length = 4) =>
            triple_exists ge fe f_inflate_table _ _ _
              (fun (h1 : e1.length = 4) =>
                maxzero_block_triple ge fe bh bc bo hcenv hdbc hdbo hdco pt pb pr
                  tblB bitsB tB tblO bitsO tO hptR hptW hpb hpr e0 e1 h0 h1 bv
                  vc vo hvc hvo
                  (by obtain ⟨A, hA⟩ : ∃ A : _root_.Int,
                        Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
                      have hal' : A % (4 : _root_.Int) = 0 := by
                        rw [← hA]; exact hal
                      rw [hA]
                      show A % (2 : _root_.Int) = 0
                      omega)
                  haddr1 l
                  (codeRegion pr tB (Integers.Ptrofs.unsigned tO + 8) k ∗ Hrest)
                  hmemT hmemB hT1 hT2 Ret hret)))))
      (mz_carve bh bc bo pt pb pr tblB bitsB tB tblO bitsO tO k bv vc vo Hrest
        l hal)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ _ hx => hx.elim) (fun _ _ x => x)
  · -- `max ≠ 0`: `Sskip`, and the footprint is handed on untouched
    refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => by
        have h := eqz_uint_eval (ge := ge) (e := envOf bh bc bo) (m := mm)
          _max M hM32 (hT'.get hmemM)
        rw [show decide (M = 0) = false from by
              rw [decide_eq_false_iff_not]; exact hM0] at h
        exact h) ?_
    refine triple_conseq ge fe f_inflate_table
      (triple_skip ge fe f_inflate_table _)
      (fun _ _ _ x => x) (fun e le hp hx => ⟨hM0, hx⟩)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

end MaxZeroIf


/-! ## §17 The fill loop (inftrees.c:238-244; AST 1108-1157)

        incr = 1U << (len - drop);
        fill = 1U << curr;
        min = fill;                 /* save offset to next table */
        do {
            fill -= incr;
            next[(huff >> drop) + fill] = here;
        } while (fill != 0);

The safety content is entirely `Model.fill_offset_lt`: at iteration `k` the
counter is `fill = 2^curr − k·incr`, and the write index
`(huff >> drop) + fill` is below `2^curr` because the dropped prefix is below
`incr`.  `codeRegion_entry_write` (§16) then gives the consumed cell back
*unchanged*, so this loop's invariant heap is constant. -/

theorem semBinop_shr_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int)
    (h : Integers.Int.ltu y Integers.Int.iwordsize = true) :
    Cop.semBinaryOperation cenv .Oshr (.Vint x) tuint (.Vint y) tuint m
      = some (.Vint (Integers.Int.shru x y)) := by
  show (if Integers.Int.ltu y Integers.Int.iwordsize
        then some (Val.Vint (Integers.Int.shru x y)) else none) = _
  rw [h]; rfl

/-- `x - y` at `(tuint, tuint)`. -/
theorem semBinop_sub_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vint x) tuint (.Vint y) tuint m
      = some (.Vint (Integers.Int.sub x y)) := rfl

/-- `x >>> k = x / 2^k` on `Nat`-valued words. -/
theorem shru_nat (a k : Nat) (ha : a < 4294967296) (hk : k < 32) :
    Integers.Int.shru (Integers.Int.repr ((a : _root_.Int)))
        (Integers.Int.repr ((k : _root_.Int)))
      = Integers.Int.repr (((a / 2 ^ k : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show ((Integers.Int.repr ((a : _root_.Int)))
        >>> ((Integers.Int.repr ((k : _root_.Int))).toNat) : BitVec 32).toNat = _
  rw [BitVec.toNat_ushiftRight, u32_toNat_repr, u32_toNat_repr, u32_toNat_repr,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : k < 4294967296)]
  have hd : a / 2 ^ k < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self a (2 ^ k)) ha
  rw [Nat.mod_eq_of_lt hd, Nat.shiftRight_eq_div_pow]

/-- `x != 0` on a tracked `tuint` temporary, decided by its value. -/
theorem ne0_eval_uint {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    (id : Ident) (v : Nat) (hv : v < 4294967296)
    (hid : le.get id = some (.Vint (Integers.Int.repr ((v : _root_.Int))))) :
    ∃ w, EvalExpr ge e le m
        (.Ebinop .One (.Etempvar id tuint)
          (.Econst_int (Integers.Int.repr 0) tint) tint) w
      ∧ Cop.boolVal w tint m = some (decide (v ≠ 0)) := by
  refine ⟨Val.ofBool (!(Integers.Int.eq (Integers.Int.repr ((v : _root_.Int)))
            (Integers.Int.repr 0))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .One _ _ _
      (.Vint (Integers.Int.repr ((v : _root_.Int))))
      (.Vint (Integers.Int.repr 0)) _
      (EvalExpr.Etempvar id tuint _ hid) (EvalExpr.Econst_int _ _)
      (semBinop_ne_uint_int _ _ _ _)
  · simp only [boolVal_ofBool_int]
    rw [show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
        eq_nat32 v 0 hv (by omega)]
    by_cases h : v = 0
    · subst h; simp
    · simp [h]

abbrev fillIdx : Expr :=
  .Ebinop .Oadd
    (.Ebinop .Oshr (.Etempvar _huff tuint) (.Etempvar _drop tuint) tuint)
    (.Etempvar _fill tuint) tuint

abbrev fillBody : Stmt :=
  .Ssequence
    (.Sset _fill (.Ebinop .Osub (.Etempvar _fill tuint)
      (.Etempvar _incr tuint) tuint))
    (.Sassign
      (.Ederef (.Ebinop .Oadd (.Etempvar _next (tptr (Ty.Tstruct __1353 noattr)))
        fillIdx (tptr (Ty.Tstruct __1353 noattr))) (Ty.Tstruct __1353 noattr))
      (.Evar _here (Ty.Tstruct __1353 noattr)))

abbrev fillTest : Stmt :=
  .Sifthenelse (.Ebinop .One (.Etempvar _fill tuint)
    (.Econst_int (Integers.Int.repr 0) tint) tint) .Sskip .Sbreak

abbrev fillLoop : Stmt := .Sloop fillBody fillTest

section Fill

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (pr : Permission) (nB : Block) (nO : Integers.Ptrofs)
variable (op bits val : Nat) (Hrest : HProp)
variable (huff drop curr lmd : Nat)

/-- The fill loop's footprint: the current (sub)table as a chain of cells, plus
    the assembled `here` and the caller's rest.  **Constant across the loop** —
    each write consumes one cell and gives it back (§16). -/
abbrev Hfill (pr : Permission) (nB : Block) (nO : Integers.Ptrofs) (curr : Nat)
    (bh : Block) (op bits val : Nat) (Hrest : HProp) : HProp :=
  codeRegion pr nB (Integers.Ptrofs.unsigned nO) (2 ^ curr)
  ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val) ∗ Hrest)

/-- The tracked temporaries the loop reads: `huff`, `drop`, `next`, `incr`,
    and the moving `fill`. -/
abbrev fillTemps (nB : Block) (nO : Integers.Ptrofs)
    (huff drop lmd f : Nat) (T : List (Ident × Val)) : List (Ident × Val) :=
  [(_fill, .Vint (Integers.Int.repr ((f : _root_.Int)))),
   (_incr, .Vint (Integers.Int.repr (((2 ^ lmd : Nat) : _root_.Int)))),
   (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))),
   (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))),
   (_next, .Vptr nB nO)] ++ T

/-- The index `(huff >> drop) + fill` evaluates to its model value. -/
theorem fillIdx_eval {e : Env} {le : TempEnv} {m : Mem}
    (hh : huff < 4294967296) (hd32 : drop < 32) (f : Nat)
    (hf : f < 4294967296) (hsum : huff / 2 ^ drop + f < 4294967296)
    (hhuffT : le.get _huff
      = some (.Vint (Integers.Int.repr ((huff : _root_.Int)))))
    (hdropT : le.get _drop
      = some (.Vint (Integers.Int.repr ((drop : _root_.Int)))))
    (hfillT : le.get _fill
      = some (.Vint (Integers.Int.repr ((f : _root_.Int))))) :
    EvalExpr ge e le m fillIdx
      (.Vint (Integers.Int.repr (((huff / 2 ^ drop + f : Nat) : _root_.Int)))) := by
  refine EvalExpr.Ebinop .Oadd _ _ _
    (.Vint (Integers.Int.repr (((huff / 2 ^ drop : Nat) : _root_.Int))))
    (.Vint (Integers.Int.repr ((f : _root_.Int)))) _ ?_
    (EvalExpr.Etempvar _fill tuint _ hfillT) ?_
  · refine EvalExpr.Ebinop .Oshr _ _ _
      (.Vint (Integers.Int.repr ((huff : _root_.Int))))
      (.Vint (Integers.Int.repr ((drop : _root_.Int)))) _
      (EvalExpr.Etempvar _huff tuint _ hhuffT)
      (EvalExpr.Etempvar _drop tuint _ hdropT) ?_
    simp only [typeof]
    rw [semBinop_shr_uint _ _ _ _ (ltu_iwordsize drop hd32),
        shru_nat huff drop hh hd32]
  · simp only [typeof]
    show Cop.semBinaryOperation ge.genv_cenv .Oadd
          (.Vint (Integers.Int.repr (((huff / 2 ^ drop : Nat) : _root_.Int))))
          tuint (.Vint (Integers.Int.repr ((f : _root_.Int)))) tuint m = _
    rw [show Cop.semBinaryOperation ge.genv_cenv .Oadd
            (.Vint (Integers.Int.repr (((huff / 2 ^ drop : Nat) : _root_.Int))))
            tuint (.Vint (Integers.Int.repr ((f : _root_.Int)))) tuint m
          = some (.Vint (Integers.Int.add
              (Integers.Int.repr (((huff / 2 ^ drop : Nat) : _root_.Int)))
              (Integers.Int.repr ((f : _root_.Int))))) from rfl,
        u32_add]

/-- **One fill iteration**: `fill -= incr; next[(huff>>drop)+fill] = here;`

    At entry `fill = 2^curr − k·incr` with `k` the number of writes already
    done; at exit `k+1`.  The write is in bounds by `Model.fill_offset_lt`
    and the region comes back unchanged (§16). -/
theorem fill_iter_step
    (T : List (Ident × Val)) (hTfill : ∀ p ∈ T, p.1 ≠ _fill)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpr : permOrder pr .Writable = true)
    (hal : Integers.Ptrofs.unsigned nO % 4 = 0)
    (hno : Integers.Ptrofs.unsigned nO + 4 * ((2 ^ curr : Nat) : _root_.Int)
             < 18446744073709551616)
    (hcurr : curr ≤ 15) (hlmd : lmd ≤ curr) (hd32 : drop < 32)
    (hhuff : huff / 2 ^ drop < 2 ^ lmd) (hh : huff < 4294967296)
    (k : Nat) (hk1 : 1 ≤ k + 1) (hk2 : (k + 1) * 2 ^ lmd ≤ 2 ^ curr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (fillTemps nB nO huff drop lmd (2 ^ curr - k * 2 ^ lmd) T)
        (Hfill pr nB nO curr bh op bits val Hrest))
      fillBody
      (.only (LocalSt (envOf bh bc bo)
        (fillTemps nB nO huff drop lmd (2 ^ curr - (k + 1) * 2 ^ lmd) T)
        (Hfill pr nB nO curr bh op bits val Hrest))) := by
  have hpow15 : (2 : Nat) ^ curr ≤ 32768 :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) hcurr) (by omega)
  have hlmdpow : (2 : Nat) ^ lmd ≤ 2 ^ curr :=
    Nat.pow_le_pow_right (by omega) hlmd
  -- fill -= incr
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      (fillTemps nB nO huff drop lmd (2 ^ curr - (k + 1) * 2 ^ lmd) T)
      (Hfill pr nB nO curr bh op bits val Hrest)) _ _ _ ?_ ?_
  · refine triple_conseq ge fe f_inflate_table
      (triple_set_local ge fe f_inflate_table (envOf bh bc bo)
        (fillTemps nB nO huff drop lmd (2 ^ curr - k * 2 ^ lmd) T)
        ([(_incr, .Vint (Integers.Int.repr (((2 ^ lmd : Nat) : _root_.Int)))),
         (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))),
         (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))),
         (_next, .Vptr nB nO)] ++ T) _ _fill _
        (.Vint (Integers.Int.repr
          (((2 ^ curr - (k + 1) * 2 ^ lmd : Nat) : _root_.Int))))
        (fun p hp => List.mem_cons_of_mem _ hp)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _incr ≠ _fill; decide
          rcases List.mem_cons.mp hp2 with rfl | hp3
          · show _huff ≠ _fill; decide
          rcases List.mem_cons.mp hp3 with rfl | hp4
          · show _drop ≠ _fill; decide
          rcases List.mem_cons.mp hp4 with rfl | hp5
          · show _next ≠ _fill; decide
          · exact hTfill p hp5)
        (fun le mm hp hT _ _ => ?_))
      (fun _ _ _ x => by exact x) (fun e le hp hx => by exact hx)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ hx => hx.elim)
    refine EvalExpr.Ebinop .Osub _ _ _
      (.Vint (Integers.Int.repr
        (((2 ^ curr - k * 2 ^ lmd : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr (((2 ^ lmd : Nat) : _root_.Int)))) _
      (EvalExpr.Etempvar _fill tuint _ (hT.get List.mem_cons_self))
      (EvalExpr.Etempvar _incr tuint _
        (hT.get (List.mem_cons_of_mem _ List.mem_cons_self))) ?_
    simp only [typeof]
    rw [semBinop_sub_uint]
    show some (Val.Vint (Integers.Int.sub
              (Integers.Int.repr (((2 ^ curr - k * 2 ^ lmd : Nat) : _root_.Int)))
              (Integers.Int.repr (((2 ^ lmd : Nat) : _root_.Int))))) = _
    rw [i32_sub_repr,
        show ((2 ^ curr - k * 2 ^ lmd : Nat) : _root_.Int)
              - ((2 ^ lmd : Nat) : _root_.Int)
            = ((2 ^ curr - (k + 1) * 2 ^ lmd : Nat) : _root_.Int) from by
          -- omega cannot multiply variables: turn the products into atoms
          obtain ⟨I, hI⟩ : ∃ I, 2 ^ lmd = I := ⟨_, rfl⟩
          obtain ⟨C, hC⟩ : ∃ C, 2 ^ curr = C := ⟨_, rfl⟩
          rw [hI, hC] at hk2 ⊢
          rw [show (k + 1) * I = k * I + I from by
                rw [Nat.add_mul, Nat.one_mul]] at hk2 ⊢
          obtain ⟨KI, hKI⟩ : ∃ KI, k * I = KI := ⟨_, rfl⟩
          rw [hKI] at hk2 ⊢
          omega]
  · -- the write
    have hidxlt : huff / 2 ^ drop + (2 ^ curr - (k + 1) * 2 ^ lmd) < 2 ^ curr :=
      InflateTable.Model.fill_offset_lt huff drop curr lmd (k + 1) hhuff hk1 hk2
    refine codeRegion_entry_write ge fe bh bc bo hcenv pr hpr nB nO (2 ^ curr)
      (huff / 2 ^ drop + (2 ^ curr - (k + 1) * 2 ^ lmd)) hidxlt
      (by omega) op bits val hal hno _next fillIdx rfl _ Hrest
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
      (fun le m hT => ?_)
    exact fillIdx_eval ge huff drop hh hd32
      (2 ^ curr - (k + 1) * 2 ^ lmd) (by omega) (by have := hidxlt; omega)
      (hT.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))
      (hT.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
      (hT.get List.mem_cons_self)

/-! ### The fill loop, assembled

`do { … } while (fill != 0)` — the test sits in `Sloop`'s second slot.  The
measure is the number of writes still to do; the heap is constant, so the
only moving part is the `fill` counter. -/

/-- After `k` writes: `fill = 2^curr − k·incr`, and `k·incr ≤ 2^curr`. -/
def FillInv (T : List (Ident × Val)) (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ k, ∃ _ : 1 ≤ n, ∃ _ : k + n = 2 ^ curr / 2 ^ lmd,
    ∃ _ : k * 2 ^ lmd ≤ 2 ^ curr,
    LocalSt (envOf bh bc bo)
      (fillTemps nB nO huff drop lmd (2 ^ curr - k * 2 ^ lmd) T)
      (Hfill pr nB nO curr bh op bits val Hrest) e le hp

/-- After the write, before the test. -/
def FillMid (T : List (Ident × Val)) (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ k, ∃ _ : k + n = 2 ^ curr / 2 ^ lmd, ∃ _ : 1 ≤ k,
    ∃ _ : k * 2 ^ lmd ≤ 2 ^ curr,
    LocalSt (envOf bh bc bo)
      (fillTemps nB nO huff drop lmd (2 ^ curr - k * 2 ^ lmd) T)
      (Hfill pr nB nO curr bh op bits val Hrest) e le hp

/-- Exit: `fill = 0`, every entry of the (sub)table written. -/
def FillPost (T : List (Ident × Val)) : Sep.Assn :=
  LocalSt (envOf bh bc bo) (fillTemps nB nO huff drop lmd 0 T)
    (Hfill pr nB nO curr bh op bits val Hrest)

theorem fill_body_triple
    (T : List (Ident × Val)) (hTfill : ∀ p ∈ T, p.1 ≠ _fill)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpr : permOrder pr .Writable = true)
    (hal : Integers.Ptrofs.unsigned nO % 4 = 0)
    (hno : Integers.Ptrofs.unsigned nO + 4 * ((2 ^ curr : Nat) : _root_.Int)
             < 18446744073709551616)
    (hcurr : curr ≤ 15) (hlmd : lmd ≤ curr) (hd32 : drop < 32)
    (hhuff : huff / 2 ^ drop < 2 ^ lmd) (hh : huff < 4294967296)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table
      (FillInv bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T n)
      fillBody
      { normal := FillMid bh bc bo pr nB nO op bits val Hrest huff drop curr
                    lmd T (n - 1),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (k : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hn1 : 1 ≤ n) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hkn : k + n = 2 ^ curr / 2 ^ lmd) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hkc : k * 2 ^ lmd ≤ 2 ^ curr) => ?_)
  have hdvd : 2 ^ lmd ∣ 2 ^ curr := Nat.pow_dvd_pow 2 hlmd
  have hmul : (2 ^ curr / 2 ^ lmd) * 2 ^ lmd = 2 ^ curr :=
    Nat.div_mul_cancel hdvd
  -- `n ≥ 1` means one more write fits
  have hkm : k + 1 ≤ 2 ^ curr / 2 ^ lmd := by omega
  have hk2 : (k + 1) * 2 ^ lmd ≤ 2 ^ curr := by
    calc (k + 1) * 2 ^ lmd ≤ (2 ^ curr / 2 ^ lmd) * 2 ^ lmd :=
          Nat.mul_le_mul_right _ hkm
      _ = 2 ^ curr := hmul
  refine triple_conseq ge fe f_inflate_table
    (fill_iter_step ge fe bh bc bo pr nB nO op bits val Hrest huff drop
      curr lmd T hTfill hcenv hpr hal hno hcurr hlmd hd32 hhuff hh k (by omega) hk2)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
    (fun _ _ hx => hx.elim)
  exact ⟨k + 1, by omega, by omega, hk2, hx⟩

/-- The `while (fill != 0)` test: continue with one fewer write remaining,
    or break out with `fill = 0`. -/
theorem fill_test_triple
    (T : List (Ident × Val))
    (hcurr : curr ≤ 15) (hlmd : lmd ≤ curr)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table
      (FillMid bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T n)
      fillTest
      { normal := fun e le hp => ∃ n', n' < n + 1 ∧
          FillInv bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T n'
            e le hp,
        brk := FillPost bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T,
        cont := Assn.no, ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (k : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hkn : k + n = 2 ^ curr / 2 ^ lmd) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hk1 : 1 ≤ k) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hkc : k * 2 ^ lmd ≤ 2 ^ curr) => ?_)
  have hIpos : 0 < 2 ^ lmd := Nat.two_pow_pos _
  have hpow15 : (2 : Nat) ^ curr ≤ 32768 :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) hcurr) (by omega)
  have hdvd : 2 ^ lmd ∣ 2 ^ curr := Nat.pow_dvd_pow 2 hlmd
  have hmul : (2 ^ curr / 2 ^ lmd) * 2 ^ lmd = 2 ^ curr :=
    Nat.div_mul_cancel hdvd
  by_cases hz : 2 ^ curr - k * 2 ^ lmd = 0
  · -- fill == 0: leave the loop
    refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT _ _ => ?_) ?_
    · have h := ne0_eval_uint (ge := ge) (e := envOf bh bc bo) (m := mm)
        _fill (2 ^ curr - k * 2 ^ lmd) (by omega)
        (hT.get List.mem_cons_self)
      rw [show decide (2 ^ curr - k * 2 ^ lmd ≠ 0) = false from by
            rw [decide_eq_false_iff_not]; exact fun hne => hne hz] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_break ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
      show FillPost bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T
        e le hp
      rw [hz] at hx
      exact hx
  · -- fill != 0: another write remains
    refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT _ _ => ?_) ?_
    · have h := ne0_eval_uint (ge := ge) (e := envOf bh bc bo) (m := mm)
        _fill (2 ^ curr - k * 2 ^ lmd) (by omega)
        (hT.get List.mem_cons_self)
      rw [show decide (2 ^ curr - k * 2 ^ lmd ≠ 0) = true from by
            rw [decide_eq_true_eq]; exact hz] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_skip ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      -- `k` writes done, `n` remain, and `n ≥ 1` because `fill ≠ 0`
      -- n ≥ 1: otherwise k = K and `fill` would already be 0
      have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with hn0 | hpos
        · exfalso
          refine hz ?_
          rw [show k = 2 ^ curr / 2 ^ lmd from by omega, hmul]
          omega
        · exact hpos
      exact ⟨n, by omega, k, hn1, hkn, hkc, hx⟩

/-- **The fill loop.**  From no writes to all `2^curr / incr` entries of the
    current (sub)table written — every write in bounds, the region's
    `anyBytes` unchanged. -/
theorem fill_loop_triple
    (T : List (Ident × Val)) (hTfill : ∀ p ∈ T, p.1 ≠ _fill)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpr : permOrder pr .Writable = true)
    (hal : Integers.Ptrofs.unsigned nO % 4 = 0)
    (hno : Integers.Ptrofs.unsigned nO + 4 * ((2 ^ curr : Nat) : _root_.Int)
             < 18446744073709551616)
    (hcurr : curr ≤ 15) (hlmd : lmd ≤ curr) (hd32 : drop < 32)
    (hhuff : huff / 2 ^ drop < 2 ^ lmd) (hh : huff < 4294967296)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (FillInv bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T
        (2 ^ curr / 2 ^ lmd))
      fillLoop
      { normal := FillPost bh bc bo pr nB nO op bits val Hrest huff drop curr
                    lmd T,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_loop ge fe f_inflate_table _
    (FillInv bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T)
    (fun n => FillMid bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T
      (n - 1)) _ _
    (fun n => fill_body_triple ge fe bh bc bo pr nB nO op bits val Hrest huff
      drop curr lmd T hTfill hcenv hpr hal hno hcurr hlmd hd32 hhuff hh
      { normal := Assn.no,
        brk := FillPost bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T,
        cont := FillMid bh bc bo pr nB nO op bits val Hrest huff drop curr lmd T
          (n - 1),
        ret := R.ret, goto := R.goto } n)
    (fun n => ?_) (2 ^ curr / 2 ^ lmd)
  match n with
  | 0 =>
      -- `FillMid` at measure -1 is `FillMid (0-1) = FillMid 0`; the test
      -- can still run, and its `normal` exit needs `n' < 0`, impossible —
      -- so this case is closed by the test's own break-only behaviour
      refine triple_conseq ge fe f_inflate_table
        (fill_test_triple ge fe bh bc bo pr nB nO op bits val Hrest huff drop
          curr lmd T hcurr hlmd _ 0)
        (fun _ _ _ x => x) (fun e le hp hx => ?_) (fun _ _ _ x => x)
        (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx)
      -- `n' < 1` forces `n' = 0`, and `FillInv 0` carries `1 ≤ 0`
      obtain ⟨n', hlt, k, hn1, _⟩ := hx
      exact absurd hn1 (by omega)
  | m + 1 =>
      refine triple_conseq ge fe f_inflate_table
        (fill_test_triple ge fe bh bc bo pr nB nO op bits val Hrest huff drop
          curr lmd T hcurr hlmd _ m)
        (fun _ _ _ x => x) (fun e le hp hx => ?_) (fun _ _ _ x => x)
        (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx)
      obtain ⟨n', hlt, hI⟩ := hx
      exact ⟨n', by omega, hI⟩

end Fill




/-! ## §18 The ENOUGH check, DISTS case

`type == DISTS` makes the first disjunct false and the second live, so the
`_t'5`/`_t'6` chain takes the mirror path through the same statement.  Same
structure as §15's LENS case; the constant is 592. -/

section EnoughD

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (l : List (Ident × Val))

/-- **The ENOUGH check, DISTS case.**  Either `used ≤ 592` and execution
    continues, or `1` is returned. -/
theorem enough_DISTS_triple (ea eb : Ident) (hab : ea ≠ eb)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hdbc : bh ≠ bc) (hdbo : bh ≠ bo) (hdco : bc ≠ bo)
    (vh vc vo : List MemVal)
    (hvh : vh.length = 4) (hvc : vc.length = 32) (hvo : vo.length = 32)
    (Hrest : HProp) (u : Nat) (hu : u < 4294967296)
    (hmemTy : (_type, .Vint (Integers.Int.repr 2)) ∈ l)
    (hmemU : (_used, .Vint (Integers.Int.repr ((u : _root_.Int)))) ∈ l)
    (hT5 : ∀ p ∈ l, p.1 ≠ ea) (hT6 : ∀ p ∈ l, p.1 ≠ eb)
    (Ret : Val → HProp)
    (hret : ∀ hr, Hrest hr → Ret (.Vint (Integers.Int.repr 1)) hr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))))
      (enoughChk ea eb)
      { normal := fun e le hp => u ≤ 592 ∧
          ∃ lx : List (Ident × Val), ∃ _ : ∀ p ∈ l, p ∈ lx,
            LocalSt (envOf bh bc bo) lx
              (bytesPtsTo bh .Freeable 0 vh
               ∗ (bytesPtsTo bc .Freeable 0 vc
                  ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest))) e le hp,
        brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
  -- `type == LENS` is false, so `ea = 0` and the second disjunct decides
  have hTyL : ∀ (le : TempEnv) (m : Mem), TempsHold l le →
      ∃ v, EvalExpr ge (envOf bh bc bo) le m
          (.Ebinop .Oeq (.Etempvar _type tint)
            (.Econst_int (Integers.Int.repr 1) tint) tint) v
        ∧ Cop.boolVal v tint m = some false := by
    intro le m hT
    refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr 2)
              (Integers.Int.repr 1)), ?_, rfl⟩
    exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
      (EvalExpr.Etempvar _type tint _ (hT.get hmemTy))
      (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
  have hTyD : ∀ (lx : List (Ident × Val)) (le : TempEnv) (m : Mem),
      TempsHold lx le → ((_type, .Vint (Integers.Int.repr 2)) ∈ lx) →
      ∃ v, EvalExpr ge (envOf bh bc bo) le m
          (.Ebinop .Oeq (.Etempvar _type tint)
            (.Econst_int (Integers.Int.repr 2) tint) tint) v
        ∧ Cop.boolVal v tint m = some true := by
    intro lx le m hT hm
    refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr 2)
              (Integers.Int.repr 2)), ?_, rfl⟩
    exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
      (EvalExpr.Etempvar _type tint _ (hT.get hm))
      (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
  -- `ea = 0` on both paths (the LENS disjunct is dead for DISTS)
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((eb, .Vint (Integers.Int.repr (if 592 < u then 1 else 0)))
        :: (ea, .Vint (Integers.Int.repr 0)) :: l)
      (bytesPtsTo bh .Freeable 0 vh
       ∗ (bytesPtsTo bc .Freeable 0 vc
          ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((ea, .Vint (Integers.Int.repr 0)) :: l)
        (bytesPtsTo bh .Freeable 0 vh
         ∗ (bytesPtsTo bc .Freeable 0 vc
            ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))) _ _ _ ?_ ?_
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT _ _ => hTyL le mm hT) ?_
      exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l _
        ea _ _ (fun _ hp => hp) hT5
        (fun le mm hp hT _ _ => EvalExpr.Econst_int _ _)
    · -- t'5 = 0, so the outer `if` falls to the DISTS test
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT _ _ =>
          ⟨.Vint (Integers.Int.repr 0),
           EvalExpr.Etempvar ea tint _ (hT.get List.mem_cons_self), rfl⟩) ?_
      refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT _ _ =>
          hTyD _ le mm hT (List.mem_cons_of_mem _ hmemTy)) ?_
      -- t'6 = (used > 592), then the redundant re-cast
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((eb, .Vint (Integers.Int.repr (if 592 < u then 1 else 0)))
            :: (ea, .Vint (Integers.Int.repr 0)) :: l)
          (bytesPtsTo bh .Freeable 0 vh
           ∗ (bytesPtsTo bc .Freeable 0 vc
              ∗ (bytesPtsTo bo .Freeable 0 vo ∗ Hrest)))) _ _ _ ?_ ?_
      · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
          eb _ _ (fun _ hp => hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact hab
            · exact hT6 p hp2)
          (fun le mm hp hT _ _ => ?_)
        refine EvalExpr.Ecast _ _
          (Val.ofBool (Integers.Int.ltu (Integers.Int.repr ((592 : Nat)))
            (Integers.Int.repr ((u : _root_.Int))))) _
          (EvalExpr.Ebinop .Ogt _ _ _ _ _ _
            (EvalExpr.Etempvar _used tuint _
              (hT.get (List.mem_cons_of_mem _ hmemU)))
            (EvalExpr.Econst_int _ _) (semBinop_gt_uint_int _ _ _ _)) ?_
        rw [ltu_nat32 592 u (by omega) hu]
        by_cases hgt : 592 < u
        · rw [show decide (592 < u) = true from by
                rw [decide_eq_true_eq]; exact hgt, if_pos hgt]
          rfl
        · rw [show decide (592 < u) = false from by
                rw [decide_eq_false_iff_not]; exact hgt, if_neg hgt]
          rfl
      · -- the re-cast `t'6 = (bool) t'6` is the identity on 0/1
        refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
          ((ea, .Vint (Integers.Int.repr 0)) :: l) _ eb _ _
          (fun p hp => List.mem_cons_of_mem _ hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact hab
            · exact hT6 p hp2)
          (fun le mm hp hT _ _ => ?_)
        refine EvalExpr.Ecast _ _
          (.Vint (Integers.Int.repr (if 592 < u then 1 else 0))) _
          (EvalExpr.Etempvar eb tint _ (hT.get List.mem_cons_self)) ?_
        by_cases hgt : 592 < u
        · rw [if_pos hgt]; rfl
        · rw [if_neg hgt]; rfl
  · -- the final test on eb
    by_cases hgt : 592 < u
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT _ _ => ?_) ?_
      · have hv := hT.get List.mem_cons_self
        rw [if_pos hgt] at hv
        exact ⟨.Vint (Integers.Int.repr 1),
          EvalExpr.Etempvar eb tint _ hv, rfl⟩
      · refine triple_conseq ge fe f_inflate_table
          (return_const_triple ge fe bh bc bo
            ((eb, .Vint (Integers.Int.repr (if 592 < u then 1 else 0)))
              :: (ea, .Vint (Integers.Int.repr 0)) :: l) vh vc vo Hrest
            (.Econst_int (Integers.Int.repr 1) tint)
            (Integers.Int.repr 1) Ret hcenv hdbc hdbo hdco hvh hvc hvo
            (fun le m => EvalExpr.Econst_int _ _) (fun m => rfl) hret)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx)
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT _ _ => ?_) ?_
      · have hv := hT.get List.mem_cons_self
        rw [if_neg hgt] at hv
        exact ⟨.Vint (Integers.Int.repr 0),
          EvalExpr.Etempvar eb tint _ hv, rfl⟩
      · refine triple_conseq ge fe f_inflate_table
          (triple_skip ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        exact ⟨by omega, _, fun p hp =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp), hx⟩

end EnoughD

/-! ## §19 Addressing a *field of a table element*
    (inftrees.c:291-293; AST 1410-1470)

        (*table)[low].op   = (unsigned char)curr;
        (*table)[low].bits = (unsigned char)root;
        (*table)[low].val  = (unsigned short)(next - *table);

The l-value is `Efield (Ederef (Ebinop Oadd p low)) fld` — a field of an
array element, which neither `eval_index_lvalue` nor `eval_field_lvalue`
covers alone.  Composing them gives the address `p + 4·low + delta`; the
safety bound on `low` is `Model.low_lt_pow` (`huff & mask < 2^root`).

Two further ingredients live here: `ptrofs_add_unsigned` (the field offset does
not wrap) and `codeRegion_field_write` (the write rule itself, which consumes
one field slot of one cell and gives it back).  `root_backptr_triple` then runs
the three statements, including the `next - *table` pointer difference — which
CompCert leaves undefined across blocks, so `next`'s block equality is a real
side condition, not bookkeeping. -/

abbrev derefTable : Expr :=
  .Ederef (.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
    (tptr (Ty.Tstruct __1353 noattr))

abbrev backFieldW (tmp fld : Ident) (fty : Ty) (rhs : Expr) : Stmt :=
  .Sassign
    (.Efield
      (.Ederef (.Ebinop .Oadd (.Etempvar tmp (tptr (Ty.Tstruct __1353 noattr)))
        (.Etempvar _low tuint) (tptr (Ty.Tstruct __1353 noattr)))
        (Ty.Tstruct __1353 noattr))
      fld fty)
    rhs

/-- The whole back-pointer block (AST 1414-1475). -/
abbrev backPtrBlock : Stmt :=
  .Ssequence
    (.Ssequence (.Sset _t'15 derefTable)
      (backFieldW _t'15 _op tuchar (.Ecast (.Etempvar _curr tuint) tuchar)))
    (.Ssequence
      (.Ssequence (.Sset _t'14 derefTable)
        (backFieldW _t'14 _bits tuchar (.Ecast (.Etempvar _root tuint) tuchar)))
      (.Ssequence (.Sset _t'12 derefTable)
        (.Ssequence (.Sset _t'13 derefTable)
          (backFieldW _t'12 _val tushort
            (.Ecast (.Ebinop .Osub
              (.Etempvar _next (tptr (Ty.Tstruct __1353 noattr)))
              (.Etempvar _t'13 (tptr (Ty.Tstruct __1353 noattr))) tlong)
              tushort)))))

theorem semBinop_sub_pp (m : Mem) (b : Block) (o1 o2 : Integers.Ptrofs) :
    Cop.semBinaryOperation Inftrees.prog.prog_comp_env .Osub (.Vptr b o1)
      (tptr (Ty.Tstruct __1353 noattr)) (.Vptr b o2)
      (tptr (Ty.Tstruct __1353 noattr)) m
    = some (Val.Vptrofs (Integers.MI.divs (Integers.Ptrofs.sub o1 o2)
        (Integers.Ptrofs.repr 4))) := by
  show (if b = b then _ else _) = _
  rw [if_pos rfl]
  rfl

theorem semCast_uint_uchar (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tuint tuchar m
      = some (.Vint (Integers.Int.zero_ext 8 x)) := rfl

theorem semCast_uchar_uchar (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tuchar tuchar m
      = some (.Vint (Integers.Int.zero_ext 8 x)) := rfl

theorem semCast_ptrofs_ushort (m : Mem) (x : Integers.Ptrofs) :
    Cop.semCast (Val.Vptrofs x) tlong tushort m
      = some (.Vint (Integers.Int.zero_ext 16
          (Integers.Int.repr (Integers.Int64.unsigned x)))) := rfl

theorem semCast_ushort_ushort (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tushort tushort m
      = some (.Vint (Integers.Int.zero_ext 16 x)) := rfl

private theorem add_arith (A d : Nat)
    (hno : (A : _root_.Int) + (d : _root_.Int) < 18446744073709551616) :
    (((A + d) % 18446744073709551616 : Nat) : _root_.Int)
      = (A : _root_.Int) + (d : _root_.Int) := by
  omega

/-- **`Ptrofs.add` with a small offset does not wrap.**  The field-offset
    analogue of `idxOfs_unsigned`, and built the same way: its `simp only` set
    leaves an `Int`-vs-`Nat` goal that `omega` takes only after the modulus is
    peeled by hand (`hd`) and the remainder is restated over `_root_.Int`
    (`add_arith`) — at `CC.Z` the atoms are silently dropped. -/
theorem ptrofs_add_unsigned (x : Integers.Ptrofs) (d : Nat)
    (hdlt : d < 18446744073709551616)
    (hno : Integers.Ptrofs.unsigned x + (d : _root_.Int)
             < 18446744073709551616) :
    Integers.Ptrofs.unsigned
        (Integers.Ptrofs.add x (Integers.Ptrofs.repr ((d : _root_.Int))))
      = Integers.Ptrofs.unsigned x + (d : _root_.Int) := by
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  simp only [Integers.Ptrofs.add, Integers.Ptrofs.unsigned,
             Integers.Ptrofs.repr, Integers.MI.add, Integers.MI.repr,
             Integers.MI.unsigned, BitVec.toNat_add, BitVec.toNat_ofInt,
             hw] at hno ⊢
  have hd : (((d : Nat) : _root_.Int)
      % ((18446744073709551616 : Nat) : _root_.Int)).toNat = d := by
    have h : d < 18446744073709551616 := hdlt
    omega
  rw [hd]
  exact add_arith _ _ hno

section RootPtr

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)

/-- A table element read as an expression yields its address (`By_copy`). -/
theorem eval_elem_addr {e : Env} {le : TempEnv} {m : Mem}
    {b : Block} {o : Integers.Ptrofs} {base idx : Expr} {iv : Integers.Int}
    (hptr : EvalExpr ge e le m base (.Vptr b o))
    (hidx : EvalExpr ge e le m idx (.Vint iv))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx)
      = .pi (Ty.Tstruct __1353 noattr) .Unsigned) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd base idx (tptr (Ty.Tstruct __1353 noattr)))
        (Ty.Tstruct __1353 noattr))
      (.Vptr b (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned o iv)) :=
  EvalExpr.Elvalue _ b _ .Full _
    (eval_index_lvalue hptr hidx hcls)
    (DerefLoc.copy InflateTable.Layout.code_accessMode)

/-- **A field of a table element, as an l-value.**  The composition
    `eval_index_lvalue` ⨟ `eval_field_lvalue`: address `p + 4·i + delta`. -/
theorem eval_elem_field_lvalue {e : Env} {le : TempEnv} {m : Mem}
    {b : Block} {o : Integers.Ptrofs} {base idx : Expr} {iv : Integers.Int}
    {fld : Ident} {fty : Ty} {delta : Z}
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hfld : fieldOffset Inftrees.prog.prog_comp_env fld
              InflateTable.Layout.codeCo.co_members = .OK (delta, .Full))
    (hptr : EvalExpr ge e le m base (.Vptr b o))
    (hidx : EvalExpr ge e le m idx (.Vint iv))
    (hcls : Cop.classifyAdd (typeof base) (typeof idx)
      = .pi (Ty.Tstruct __1353 noattr) .Unsigned) :
    EvalLvalue ge e le m
      (.Efield
        (.Ederef (.Ebinop .Oadd base idx (tptr (Ty.Tstruct __1353 noattr)))
          (Ty.Tstruct __1353 noattr)) fld fty)
      b (Integers.Ptrofs.add
          (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned o iv)
          (Integers.Ptrofs.repr delta)) .Full := by
  have hco : ge.genv_cenv.get __1353 = some InflateTable.Layout.codeCo := by
    rw [hcenv]
    show Inftrees.prog.prog_comp_env.get __1353 = _
    show _ = some (match Inftrees.prog.prog_comp_env.get __1353 with
      | some co => co
      | none => { co_su := .Struct, co_members := [], co_attr := noattr,
                  co_sizeof := 0, co_alignof := 1, co_rank := 0 })
    rw [show Inftrees.prog.prog_comp_env.get __1353
          = some InflateTable.Layout.codeCo from by decide]
  exact eval_field_lvalue rfl hco (by rw [hcenv]; exact hfld)
    (eval_elem_addr ge hptr hidx hcls)

/-- **One *field* of one table entry written.**

    `(*table)[low].fld = e` — the root back-pointer writes of inftrees.c:291-293.
    The entry is picked out of the region by `codeRegion_carve`, the field out
    of the entry by the caller's `hcarve` (one of `codeCell_carve_{op,bits,val}`);
    the slot's old contents are existentially quantified, so nothing is assumed
    about what was there, and the new value is re-absorbed, so the region comes
    back **unchanged**.

    The safety content is `hi : i < n` — for these three writes, `i = low` and
    `Model.low_lt_pow` supplies it. -/
theorem codeRegion_field_write
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pr : Permission) (hpr : permOrder pr .Writable = true)
    (tB : Block) (tO : Integers.Ptrofs) (n i : Nat) (hi : i < n)
    (hn31 : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned tO + 4 * (n : _root_.Int)
             < 18446744073709551616)
    (fld : Ident) (fty : Ty) (chunk : Chunk) (delta : Nat) (hdlt : delta < 4)
    (hacc : accessMode fty = .By_value chunk)
    (hfld : fieldOffset Inftrees.prog.prog_comp_env fld
              InflateTable.Layout.codeCo.co_members
            = .OK (((delta : Nat) : _root_.Int), .Full))
    (Hother : HProp)
    (hcarve : codeCell pr tB (Integers.Ptrofs.unsigned tO + 4 * (i : _root_.Int))
      = anyCell chunk pr tB (Integers.Ptrofs.unsigned tO
          + 4 * (i : _root_.Int) + ((delta : Nat) : _root_.Int)) ∗ Hother)
    (pid : Ident) (idxE : Expr)
    (hcls : Cop.classifyAdd (tptr (Ty.Tstruct __1353 noattr)) (typeof idxE)
      = .pi (Ty.Tstruct __1353 noattr) .Unsigned)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemP : (pid, .Vptr tB tO) ∈ l)
    (hidx : ∀ (le : TempEnv) (m : Mem), TempsHold l le →
      EvalExpr ge (envOf bh bc bo) le m idxE
        (.Vint (Integers.Int.repr ((i : _root_.Int)))))
    (rhs : Expr) (vnew : Val)
    (hev : ∀ (le : TempEnv) (m : Mem), TempsHold l le → ∃ v,
      EvalExpr ge (envOf bh bc bo) le m rhs v
      ∧ Cop.semCast v (typeof rhs) fty m = some vnew) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n ∗ Hrest))
      (.Sassign
        (.Efield
          (.Ederef (.Ebinop .Oadd (.Etempvar pid (tptr (Ty.Tstruct __1353 noattr)))
            idxE (tptr (Ty.Tstruct __1353 noattr))) (Ty.Tstruct __1353 noattr))
          fld fty)
        rhs)
      (.only (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n ∗ Hrest))) := by
  have hsz : sizeof ge.genv_cenv (Ty.Tstruct __1353 noattr) = 4 := by
    rw [hcenv]; exact InflateTable.Layout.code_sizeof
  have haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO
        (Integers.Int.repr ((i : _root_.Int))))
      = Integers.Ptrofs.unsigned tO + 4 * (i : _root_.Int) := by
    refine idxOfs_unsigned ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO
      i 4 hsz (by decide) (by omega) ?_
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
    rw [hA] at hno ⊢
    have h2 : A + 4 * ((n : Nat) : _root_.Int)
        < (18446744073709551616 : _root_.Int) := hno
    show A + ((4 : Nat) : _root_.Int) * ((i : Nat) : _root_.Int)
          < (18446744073709551616 : _root_.Int)
    omega
  have haddr2 : Integers.Ptrofs.unsigned
      (Integers.Ptrofs.add
        (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO
          (Integers.Int.repr ((i : _root_.Int))))
        (Integers.Ptrofs.repr (((delta : Nat) : _root_.Int))))
      = Integers.Ptrofs.unsigned tO + 4 * (i : _root_.Int)
        + ((delta : Nat) : _root_.Int) := by
    rw [ptrofs_add_unsigned _ delta (by omega) ?_, haddr]
    rw [haddr]
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
    rw [hA] at hno ⊢
    have h2 : A + 4 * ((n : Nat) : _root_.Int)
        < (18446744073709551616 : _root_.Int) := hno
    show A + 4 * ((i : Nat) : _root_.Int) + ((delta : Nat) : _root_.Int)
          < (18446744073709551616 : _root_.Int)
    omega
  have hre : (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n ∗ Hrest)
      = anyCell chunk pr tB (Integers.Ptrofs.unsigned tO
            + 4 * (i : _root_.Int) + ((delta : Nat) : _root_.Int))
        ∗ (Hother
           ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) i
              ∗ (codeRegion pr tB
                   (Integers.Ptrofs.unsigned tO + 4 * (i : _root_.Int) + 4)
                   (n - i - 1) ∗ Hrest))) := by
    rw [codeRegion_carve pr tB (Integers.Ptrofs.unsigned tO) n i hi, hcarve]
    sep_cancel
  refine localst_perm ge fe (envOf bh bc bo) l _
    (HProp.hexists (fun v : Val =>
      mapsto chunk pr tB (Integers.Ptrofs.unsigned tO
          + 4 * (i : _root_.Int) + ((delta : Nat) : _root_.Int)) v
      ∗ (Hother
         ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) i
            ∗ (codeRegion pr tB
                 (Integers.Ptrofs.unsigned tO + 4 * (i : _root_.Int) + 4)
                 (n - i - 1) ∗ Hrest)))))
    (by rw [hre]; exact hexists_sep_eq _ _) _ _ ?_
  rw [localst_hexists]
  refine triple_exists ge fe f_inflate_table _ _ _ (fun vold => ?_)
  refine triple_conseq ge fe f_inflate_table
    (triple_assign ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo) l
        (mapsto chunk pr tB (Integers.Ptrofs.unsigned tO
            + 4 * (i : _root_.Int) + ((delta : Nat) : _root_.Int)) vnew
         ∗ (Hother
            ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) i
               ∗ (codeRegion pr tB
                    (Integers.Ptrofs.unsigned tO + 4 * (i : _root_.Int) + 4)
                    (n - i - 1) ∗ Hrest)))))
      _ _ chunk pr tB
      (Integers.Ptrofs.add
        (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO
          (Integers.Int.repr ((i : _root_.Int))))
        (Integers.Ptrofs.repr (((delta : Nat) : _root_.Int))))
      hpr (by simpa only [typeof] using hacc) ?_)
    (fun _ _ _ x => x) (fun e le hp hx => ?_)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  · intro e le hp m hP _
    obtain ⟨henv, hT, hH⟩ := hP
    subst henv
    obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
    obtain ⟨v, hevv, hcast⟩ := hev le m hT
    refine ⟨vold, vnew, h1, h2, hd12, heq, ?_, ?_, ⟨v, hevv, hcast⟩, ?_⟩
    · rw [haddr2]; exact hm1
    · exact eval_elem_field_lvalue ge hcenv hfld
        (EvalExpr.Etempvar pid _ _ (hT.get hmemP)) (hidx le m hT) hcls
    · intro h1' hm1' hd1'
      refine ⟨rfl, hT, h1', h2, hd1', rfl, ?_, hrest⟩
      rw [haddr2] at hm1'
      exact hm1'
  · obtain ⟨henv, hT, hH⟩ := hx
    refine ⟨henv, hT, ?_⟩
    rw [hre]
    exact sep_mono (fun h hm => ⟨vnew, hm⟩) (entails_refl _) hp hH

theorem read_table_triple'
    (pt pr : Permission) (tblB : Block) (tblO : Integers.Ptrofs)
    (tB : Block) (tO : Integers.Ptrofs) (n : Nat)
    (hpt : permOrder pt .Readable = true)
    (tmp : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ tmp) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest)))
      (.Sset tmp derefTable)
      (.only (LocalSt (envOf bh bc bo) ((tmp, .Vptr tB tO) :: l)
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest)))) := by
  have hperm : (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
        ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
           ∗ Hrest))
      = (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n ∗ Hrest)) := by
    sep_cancel
  refine triple_conseq ge fe f_inflate_table
    (read_table_triple ge fe bh bc bo pt tblB tblO tB tO hpt tmp l
      (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n ∗ Hrest) hmemT hne)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hperm]; exact hx.2.2⟩)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [hperm]; exact hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- One back-pointer field write, with the field selected by `hcarve`. -/
theorem backptr_write_triple
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pr : Permission) (hpr : permOrder pr .Writable = true)
    (tB : Block) (tO : Integers.Ptrofs) (n low : Nat) (hlow : low < n)
    (hn31 : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned tO + 4 * (n : _root_.Int)
             < 18446744073709551616)
    (fld : Ident) (fty : Ty) (chunk : Chunk) (delta : Nat) (hdlt : delta < 4)
    (hacc : accessMode fty = .By_value chunk)
    (hfld : fieldOffset Inftrees.prog.prog_comp_env fld
              InflateTable.Layout.codeCo.co_members
            = .OK (((delta : Nat) : _root_.Int), .Full))
    (Hother : HProp)
    (hcarve : codeCell pr tB
        (Integers.Ptrofs.unsigned tO + 4 * (low : _root_.Int))
      = anyCell chunk pr tB (Integers.Ptrofs.unsigned tO
          + 4 * (low : _root_.Int) + ((delta : Nat) : _root_.Int)) ∗ Hother)
    (tmp : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemP : (tmp, .Vptr tB tO) ∈ l)
    (hmemLow : (_low, .Vint (Integers.Int.repr ((low : _root_.Int)))) ∈ l)
    (rhs : Expr) (vnew : Val)
    (hev : ∀ (le : TempEnv) (m : Mem), TempsHold l le → ∃ v,
      EvalExpr ge (envOf bh bc bo) le m rhs v
      ∧ Cop.semCast v (typeof rhs) fty m = some vnew) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n ∗ Hrest))
      (backFieldW tmp fld fty rhs)
      (.only (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n ∗ Hrest))) :=
  codeRegion_field_write ge fe bh bc bo hcenv pr hpr tB tO n low hlow hn31 hno
    fld fty chunk delta hdlt hacc hfld Hother hcarve tmp
    (.Etempvar _low tuint) rfl l Hrest hmemP
    (fun le m hT => EvalExpr.Etempvar _low tuint _ (hT.get hmemLow))
    rhs vnew hev

/-- **The root back-pointer block** (inftrees.c:291-293; AST 1414-1475).

    `next` is required to live in the *same block* as `*table` — the C computes
    `next - *table`, and CompCert's pointer subtraction is `None` across blocks,
    so this is a genuine side condition, not bookkeeping. -/
theorem root_backptr_triple
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pt pr : Permission) (hpt : permOrder pt .Readable = true)
    (hpr : permOrder pr .Writable = true)
    (tblB : Block) (tblO : Integers.Ptrofs)
    (tB : Block) (tO nO : Integers.Ptrofs)
    (n low curr root : Nat) (hlow : low < n)
    (hn31 : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned tO + 4 * (n : _root_.Int)
             < 18446744073709551616)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hmemLow : (_low, .Vint (Integers.Int.repr ((low : _root_.Int)))) ∈ l)
    (hmemCurr : (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) ∈ l)
    (hmemRoot : (_root, .Vint (Integers.Int.repr ((root : _root_.Int)))) ∈ l)
    (hmemNext : (_next, .Vptr tB nO) ∈ l)
    (hfr : ∀ p ∈ l, p.1 ≠ _t'15 ∧ p.1 ≠ _t'14 ∧ p.1 ≠ _t'12 ∧ p.1 ≠ _t'13) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest)))
      backPtrBlock
      (.only (LocalSt (envOf bh bc bo)
        ((_t'13, .Vptr tB tO) :: (_t'12, .Vptr tB tO) :: (_t'14, .Vptr tB tO)
          :: (_t'15, .Vptr tB tO) :: l)
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest)))) := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo) ((_t'15, .Vptr tB tO) :: l)
      (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
       ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
          ∗ Hrest))) _ _ _ ?_ ?_
  -- (*table)[low].op = (unsigned char)curr;
  · refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo) ((_t'15, .Vptr tB tO) :: l)
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest))) _ _ _
      (read_table_triple' ge fe bh bc bo pt pr tblB tblO tB tO n hpt _t'15 l
        Hrest hmemT (fun p hp => (hfr p hp).1)) ?_
    exact backptr_write_triple ge fe bh bc bo hcenv pr hpr tB tO n low hlow
      hn31 hno _op tuchar .Mint8unsigned 0 (by omega) rfl
      InflateTable.Layout.op_offset _
      (codeCell_carve_op pr tB
        (Integers.Ptrofs.unsigned tO + 4 * (low : _root_.Int)))
      _t'15 _
      (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
       ∗ Hrest)
      List.mem_cons_self (List.mem_cons_of_mem _ hmemLow) _
      (.Vint (Integers.Int.zero_ext 8
        (Integers.Int.zero_ext 8 (Integers.Int.repr ((curr : _root_.Int))))))
      (fun le m hT => ⟨.Vint (Integers.Int.zero_ext 8
          (Integers.Int.repr ((curr : _root_.Int)))),
        EvalExpr.Ecast _ _ _ _
          (EvalExpr.Etempvar _curr tuint _
            (hT.get (List.mem_cons_of_mem _ hmemCurr)))
          (by simp only [typeof]; exact semCast_uint_uchar m _),
        by simp only [typeof]; exact semCast_uchar_uchar m _⟩)
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'14, .Vptr tB tO) :: (_t'15, .Vptr tB tO) :: l)
      (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
       ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
          ∗ Hrest))) _ _ _ ?_ ?_
  -- (*table)[low].bits = (unsigned char)root;
  · refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'14, .Vptr tB tO) :: (_t'15, .Vptr tB tO) :: l)
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest))) _ _ _
      (read_table_triple' ge fe bh bc bo pt pr tblB tblO tB tO n hpt _t'14
        ((_t'15, .Vptr tB tO) :: l) Hrest
        (List.mem_cons_of_mem _ hmemT)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _t'15 ≠ _t'14; decide
          · exact (hfr p hp2).2.1)) ?_
    exact backptr_write_triple ge fe bh bc bo hcenv pr hpr tB tO n low hlow
      hn31 hno _bits tuchar .Mint8unsigned 1 (by omega) rfl
      InflateTable.Layout.bits_offset _
      (codeCell_carve_bits pr tB
        (Integers.Ptrofs.unsigned tO + 4 * (low : _root_.Int)))
      _t'14 _
      (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
       ∗ Hrest)
      List.mem_cons_self
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemLow)) _
      (.Vint (Integers.Int.zero_ext 8
        (Integers.Int.zero_ext 8 (Integers.Int.repr ((root : _root_.Int))))))
      (fun le m hT => ⟨.Vint (Integers.Int.zero_ext 8
          (Integers.Int.repr ((root : _root_.Int)))),
        EvalExpr.Ecast _ _ _ _
          (EvalExpr.Etempvar _root tuint _
            (hT.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemRoot))))
          (by simp only [typeof]; exact semCast_uint_uchar m _),
        by simp only [typeof]; exact semCast_uchar_uchar m _⟩)
  -- (*table)[low].val = (unsigned short)(next - *table);
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'12, .Vptr tB tO) :: (_t'14, .Vptr tB tO) :: (_t'15, .Vptr tB tO) :: l)
      (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
       ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
          ∗ Hrest))) _ _ _
    (read_table_triple' ge fe bh bc bo pt pr tblB tblO tB tO n hpt _t'12
      ((_t'14, .Vptr tB tO) :: (_t'15, .Vptr tB tO) :: l) Hrest
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemT))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _t'14 ≠ _t'12; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _t'15 ≠ _t'12; decide
        · exact (hfr p hp3).2.2.1)) ?_
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'13, .Vptr tB tO) :: (_t'12, .Vptr tB tO) :: (_t'14, .Vptr tB tO)
        :: (_t'15, .Vptr tB tO) :: l)
      (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
       ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
          ∗ Hrest))) _ _ _
    (read_table_triple' ge fe bh bc bo pt pr tblB tblO tB tO n hpt _t'13
      ((_t'12, .Vptr tB tO) :: (_t'14, .Vptr tB tO) :: (_t'15, .Vptr tB tO) :: l)
      Hrest
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hmemT)))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _t'12 ≠ _t'13; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _t'14 ≠ _t'13; decide
        rcases List.mem_cons.mp hp3 with rfl | hp4
        · show _t'15 ≠ _t'13; decide
        · exact (hfr p hp4).2.2.2)) ?_
  exact backptr_write_triple ge fe bh bc bo hcenv pr hpr tB tO n low hlow
    hn31 hno _val tushort .Mint16unsigned 2 (by omega) tushort_byvalue
    InflateTable.Layout.val_offset _
    (codeCell_carve_val pr tB
      (Integers.Ptrofs.unsigned tO + 4 * (low : _root_.Int)))
    _t'12 _
    (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
     ∗ Hrest)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemLow)))) _
    (.Vint (Integers.Int.zero_ext 16 (Integers.Int.zero_ext 16
      (Integers.Int.repr (Integers.Int64.unsigned
        (Integers.MI.divs (Integers.Ptrofs.sub nO tO)
          (Integers.Ptrofs.repr 4)))))))
    (fun le m hT => ⟨.Vint (Integers.Int.zero_ext 16
        (Integers.Int.repr (Integers.Int64.unsigned
          (Integers.MI.divs (Integers.Ptrofs.sub nO tO)
            (Integers.Ptrofs.repr 4))))),
      EvalExpr.Ecast _ _ _ _
        (EvalExpr.Ebinop .Osub _ _ _ (.Vptr tB nO) (.Vptr tB tO) _
          (EvalExpr.Etempvar _next _ _
            (hT.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemNext))))))
          (EvalExpr.Etempvar _t'13 _ _ (hT.get List.mem_cons_self))
          (by simp only [typeof]; rw [hcenv]; exact semBinop_sub_pp m tB nO tO))
        (by simp only [typeof]; exact semCast_ptrofs_ushort m _),
      by simp only [typeof]; exact semCast_ushort_ushort m _⟩)

/-- The same block with the four `*table` re-reads forgotten again — the form
    the main loop composes with (`TempsHold` is monotone in the tracked list). -/
theorem root_backptr_triple_forget
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (pt pr : Permission) (hpt : permOrder pt .Readable = true)
    (hpr : permOrder pr .Writable = true)
    (tblB : Block) (tblO : Integers.Ptrofs)
    (tB : Block) (tO nO : Integers.Ptrofs)
    (n low curr root : Nat) (hlow : low < n)
    (hn31 : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned tO + 4 * (n : _root_.Int)
             < 18446744073709551616)
    (l : List (Ident × Val)) (Hrest : HProp)
    (hmemT : (_table, .Vptr tblB tblO) ∈ l)
    (hmemLow : (_low, .Vint (Integers.Int.repr ((low : _root_.Int)))) ∈ l)
    (hmemCurr : (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) ∈ l)
    (hmemRoot : (_root, .Vint (Integers.Int.repr ((root : _root_.Int)))) ∈ l)
    (hmemNext : (_next, .Vptr tB nO) ∈ l)
    (hfr : ∀ p ∈ l, p.1 ≠ _t'15 ∧ p.1 ≠ _t'14 ∧ p.1 ≠ _t'12 ∧ p.1 ≠ _t'13) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest)))
      backPtrBlock
      (.only (LocalSt (envOf bh bc bo) l
        (codeRegion pr tB (Integers.Ptrofs.unsigned tO) n
         ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
            ∗ Hrest)))) :=
  triple_conseq ge fe f_inflate_table
    (root_backptr_triple ge fe bh bc bo hcenv pt pr hpt hpr tblB tblO tB tO nO
      n low curr root hlow hn31 hno l Hrest hmemT hmemLow hmemCurr hmemRoot
      hmemNext hfr)
    (fun _ _ _ x => x)
    (fun e le hp hx => ⟨hx.1, TempsHold_mono (fun p hp2 =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2)))) hx.2.1,
      hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

end RootPtr

/-! ## §20 The backwards code increment (inftrees.c:246-255; AST 1157-1198)

        incr = 1U << (len - 1);
        while (huff & incr) incr >>= 1;
        if (incr) { huff &= incr - 1; huff += incr; } else huff = 0;

**This block touches no memory** — it is pure temporary arithmetic — so it
contributes nothing to stuck-freedom on its own.  It is here because the main
loop's invariant has to know the value of `huff` afterwards, and that value is
`Model.bwInc huff len`, whose bound `Model.bwInc_lt` is what keeps every later
table index in range.

The C loop is exactly the unfolding of `Model.bwIncGo` with the bit position as
fuel, so the loop invariant is the *equation* "what is left to compute has not
changed", plus `incr = incrOf f`. -/

open InflateTable.Model

theorem nat_and_two_pow (a k : Nat) :
    a &&& 2 ^ k = if Nat.testBit a k then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases h : i = k
  · subst h
    by_cases hb : Nat.testBit a i
    · simp [hb]
    · simp [hb]
  · by_cases hb : Nat.testBit a k
    · simp [hb, Ne.symm h]
    · simp only [hb, Bool.false_eq_true, if_false, Nat.zero_testBit,
        Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inr (fun hk => h hk.symm)

theorem nat_and_two_pow_ne_zero (a k : Nat) :
    (a &&& 2 ^ k ≠ 0) ↔ a / 2 ^ k % 2 = 1 := by
  rw [nat_and_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : a / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]

theorem nat_and_lt (a b : Nat) (ha : a < 4294967296) : a &&& b < 4294967296 :=
  Nat.lt_of_le_of_lt (Nat.and_le_left) ha

theorem u32_and (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
    Integers.Int.and (Integers.Int.repr ((a : _root_.Int)))
        (Integers.Int.repr ((b : _root_.Int)))
      = Integers.Int.repr (((a &&& b : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show ((Integers.Int.repr ((a : _root_.Int)))
        &&& (Integers.Int.repr ((b : _root_.Int))) : BitVec 32).toNat = _
  rw [BitVec.toNat_and, u32_toNat_repr, u32_toNat_repr, u32_toNat_repr,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (nat_and_lt a b ha)]

theorem semBinop_and_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oand (.Vint x) tuint (.Vint y) tuint m
      = some (.Vint (Integers.Int.and x y)) := rfl

theorem semBinop_shr_uint_int (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int)
    (h : Integers.Int.ltu y Integers.Int.iwordsize = true) :
    Cop.semBinaryOperation cenv .Oshr (.Vint x) tuint (.Vint y) tint m
      = some (.Vint (Integers.Int.shru x y)) := by
  show (if Integers.Int.ltu y Integers.Int.iwordsize
        then some (Val.Vint (Integers.Int.shru x y)) else none) = _
  rw [h]; rfl

theorem boolVal_vint_uint (m : Mem) (x : Integers.Int) :
    Cop.boolVal (.Vint x) tuint m
      = some (!(Integers.Int.eq x (Integers.Int.repr 0))) := rfl

theorem bwIncGo_succ (huff k : Nat) :
    bwIncGo huff (k + 1)
      = if huff / 2 ^ k % 2 = 1 then bwIncGo huff k else huff % 2 ^ k + 2 ^ k :=
  rfl

def incrOf : Nat → Nat
  | 0 => 0
  | k + 1 => 2 ^ k

theorem incrOf_lt (f : Nat) (hf : f ≤ 16) : incrOf f < 4294967296 := by
  cases f with
  | zero => decide
  | succ k =>
      show (2 : Nat) ^ k < 4294967296
      exact Nat.lt_of_le_of_lt
        (Nat.pow_le_pow_right (by omega) (by omega : k ≤ 15)) (by omega)

theorem incrOf_shift (k : Nat) : incrOf (k + 1) / 2 = incrOf k := by
  cases k with
  | zero => rfl
  | succ j =>
      show (2 : Nat) ^ (j + 1) / 2 = 2 ^ j
      rw [Nat.pow_succ]
      omega

/-! ### The AST -/

abbrev incrInit : Stmt :=
  .Sset _incr (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
    (.Ebinop .Osub (.Etempvar _len tuint)
      (.Econst_int (Integers.Int.repr 1) tint) tuint) tuint)

abbrev incrGuard : Expr :=
  .Ebinop .Oand (.Etempvar _huff tuint) (.Etempvar _incr tuint) tuint

abbrev incrBody : Stmt :=
  .Sset _incr (.Ebinop .Oshr (.Etempvar _incr tuint)
    (.Econst_int (Integers.Int.repr 1) tint) tuint)

abbrev incrLoop : Stmt := swhile incrGuard incrBody

abbrev incrFix : Stmt :=
  .Sifthenelse (.Ebinop .One (.Etempvar _incr tuint)
    (.Econst_int (Integers.Int.repr 0) tint) tint)
    (.Ssequence
      (.Sset _huff (.Ebinop .Oand (.Etempvar _huff tuint)
        (.Ebinop .Osub (.Etempvar _incr tuint)
          (.Econst_int (Integers.Int.repr 1) tint) tuint) tuint))
      (.Sset _huff (.Ebinop .Oadd (.Etempvar _huff tuint)
        (.Etempvar _incr tuint) tuint)))
    (.Sset _huff (.Econst_int (Integers.Int.repr 0) tint))

abbrev bwIncBlock : Stmt := .Ssequence incrInit (.Ssequence incrLoop incrFix)

section BwInc

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (huff len : Nat) (T : List (Ident × Val)) (H : HProp)

theorem incrGuard_eval {e : Env} {le : TempEnv} {m : Mem} (f : Nat)
    (hh : huff < 4294967296) (hf : f ≤ 16)
    (hhuffT : le.get _huff
      = some (.Vint (Integers.Int.repr ((huff : _root_.Int)))))
    (hincrT : le.get _incr
      = some (.Vint (Integers.Int.repr (((incrOf f : Nat) : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m incrGuard v
      ∧ Cop.boolVal v (typeof incrGuard) m
        = some (decide (huff &&& incrOf f ≠ 0)) := by
  refine ⟨.Vint (Integers.Int.and (Integers.Int.repr ((huff : _root_.Int)))
      (Integers.Int.repr (((incrOf f : Nat) : _root_.Int)))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Oand _ _ _ _ _ _
      (EvalExpr.Etempvar _huff tuint _ hhuffT)
      (EvalExpr.Etempvar _incr tuint _ hincrT)
      (semBinop_and_uint _ _ _ _)
  · simp only [typeof]
    rw [u32_and huff (incrOf f) hh (incrOf_lt f hf), boolVal_vint_uint,
        show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
        eq_nat32 _ 0 (nat_and_lt huff _ hh) (by omega)]
    by_cases h : huff &&& incrOf f = 0
    · simp [h]
    · simp [h]

/-! ### The loop invariant

`f` is the remaining fuel; the C variable `incr` is `incrOf f`.  The invariant
carries the *equation* `bwIncGo huff len = bwIncGo huff f`: the loop is exactly
the unfolding of `bwIncGo`, so what is left to compute never changes. -/

def IncInv (f : Nat) : Sep.Assn := fun e le hp =>
  ∃ _ : f ≤ len, ∃ _ : bwIncGo huff len = bwIncGo huff f,
    LocalSt (envOf bh bc bo)
      ((_incr, .Vint (Integers.Int.repr (((incrOf f : Nat) : _root_.Int))))
        :: (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) :: T)
      H e le hp

def JInc (f : Nat) : Sep.Assn := fun e le hp =>
  ∃ f', f' < f ∧ IncInv bh bc bo huff len T H f' e le hp

def IncPost : Sep.Assn := fun e le hp =>
  ∃ f, ∃ _ : f ≤ len, ∃ _ : bwIncGo huff len = bwIncGo huff f,
    ∃ _ : ∀ k, f = k + 1 → huff / 2 ^ k % 2 = 0,
    LocalSt (envOf bh bc bo)
      ((_incr, .Vint (Integers.Int.repr (((incrOf f : Nat) : _root_.Int))))
        :: (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) :: T)
      H e le hp

theorem incbody_triple
    (hh : huff < 4294967296) (hlen15 : len ≤ 15)
    (hTincr : ∀ p ∈ T, p.1 ≠ _incr)
    (R : Sep.ExitConds) (f : Nat) :
    Triple ge fe f_inflate_table (IncInv bh bc bo huff len T H f)
      (.Ssequence (.Sifthenelse incrGuard .Sskip .Sbreak) incrBody)
      { normal := JInc bh bc bo huff len T H f,
        brk := IncPost bh bc bo huff len T H,
        cont := JInc bh bc bo huff len T H f,
        ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hfl : f ≤ len) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hgo : bwIncGo huff len = bwIncGo huff f) => ?_)
  match f with
  | 0 =>
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := incrGuard_eval ge huff (e := envOf bh bc bo) (m := mm) 0 hh
          (by omega)
          (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
          (hT'.get List.mem_cons_self)
        rw [show decide (huff &&& incrOf 0 ≠ 0) = false from by
              rw [decide_eq_false_iff_not]
              show ¬ (huff &&& 0 ≠ 0)
              simp] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        exact ⟨0, hfl, hgo, fun k hk => by omega, hx⟩
  | k + 1 =>
      by_cases hbit : huff / 2 ^ k % 2 = 1
      · refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_incr, .Vint (Integers.Int.repr
                (((incrOf (k + 1) : Nat) : _root_.Int))))
              :: (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) :: T)
            H) _ _ _ ?_ ?_
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
            (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
          have h := incrGuard_eval ge huff (e := envOf bh bc bo) (m := mm)
            (k + 1) hh (by omega)
            (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
            (hT'.get List.mem_cons_self)
          rw [show decide (huff &&& incrOf (k + 1) ≠ 0) = true from by
                rw [decide_eq_true_eq]
                show huff &&& 2 ^ k ≠ 0
                exact (nat_and_two_pow_ne_zero huff k).mpr hbit] at h
          exact h
        · refine triple_conseq ge fe f_inflate_table
            (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
              ((_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) :: T)
              H _incr _
              (.Vint (Integers.Int.repr (((incrOf k : Nat) : _root_.Int))))
              (fun p hp => List.mem_cons_of_mem _ hp)
              (fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp2
                · show _huff ≠ _incr; decide
                · exact hTincr p hp2)
              (fun le mm hp hT' _ _ => ?_))
            (fun _ _ _ x => x) (fun e le hp hx => ?_)
            (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
            (fun _ _ hx => hx.elim)
          · refine EvalExpr.Ebinop .Oshr _ _ _
              (.Vint (Integers.Int.repr
                (((incrOf (k + 1) : Nat) : _root_.Int))))
              (.Vint (Integers.Int.repr 1)) _
              (EvalExpr.Etempvar _incr tuint _ (hT'.get List.mem_cons_self))
              (EvalExpr.Econst_int _ _) ?_
            simp only [typeof]
            rw [semBinop_shr_uint_int _ _ _ _ (by decide)]
            show some (Val.Vint (Integers.Int.shru
                  (Integers.Int.repr (((incrOf (k + 1) : Nat) : _root_.Int)))
                  (Integers.Int.repr 1))) = _
            rw [show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl,
                shru_nat (incrOf (k + 1)) 1 (incrOf_lt (k + 1) (by omega))
                  (by omega),
                show incrOf (k + 1) / 2 ^ 1 = incrOf k from by
                  rw [Nat.pow_one]; exact incrOf_shift k]
          · exact ⟨k, by omega, by omega, by rw [hgo, bwIncGo_succ, if_pos hbit],
                   hx⟩
      · refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
          (triple_vacuous _ _ _ _ _)
        refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
          (fun le mm hp hT' _ _ => ?_) ?_
        · have h := incrGuard_eval ge huff (e := envOf bh bc bo) (m := mm)
            (k + 1) hh (by omega)
            (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
            (hT'.get List.mem_cons_self)
          rw [show decide (huff &&& incrOf (k + 1) ≠ 0) = false from by
                rw [decide_eq_false_iff_not]
                show ¬ (huff &&& 2 ^ k ≠ 0)
                intro hne
                exact hbit ((nat_and_two_pow_ne_zero huff k).mp hne)] at h
          exact h
        · refine triple_conseq ge fe f_inflate_table
            (triple_break ge fe f_inflate_table _)
            (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
            (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
          refine ⟨k + 1, hfl, hgo, ?_, hx⟩
          intro k' hk'
          have : k' = k := by omega
          subst this
          omega

theorem incskip_triple (R : Sep.ExitConds) (f : Nat) :
    Triple ge fe f_inflate_table (JInc bh bc bo huff len T H f) .Sskip
      { normal := fun e le hp =>
          ∃ f', f' < f ∧ IncInv bh bc bo huff len T H f' e le hp,
        brk := IncPost bh bc bo huff len T H, cont := Assn.no,
        ret := R.ret, goto := R.goto } :=
  triple_conseq ge fe f_inflate_table (triple_skip ge fe f_inflate_table _)
    (fun _ _ _ x => x) (fun _ _ _ hx => hx)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

theorem incrLoop_triple
    (hh : huff < 4294967296) (hlen15 : len ≤ 15)
    (hTincr : ∀ p ∈ T, p.1 ≠ _incr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table (IncInv bh bc bo huff len T H len) incrLoop
      { normal := IncPost bh bc bo huff len T H, brk := R.brk, cont := R.cont,
        ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _ (IncInv bh bc bo huff len T H)
    (JInc bh bc bo huff len T H) _ _
    (incbody_triple ge fe bh bc bo huff len T H hh hlen15 hTincr _)
    (incskip_triple ge fe bh bc bo huff len T H _) len

/-- `incr = 1U << (len - 1);` -/
theorem incrInit_triple
    (hlen1 : 1 ≤ len) (hlen15 : len ≤ 15)
    (hTincr : ∀ p ∈ T, p.1 ≠ _incr)
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ T)
    (stale : Val) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_incr, stale)
          :: (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) :: T) H)
      incrInit
      (.only (IncInv bh bc bo huff len T H len)) := by
  obtain ⟨j, rfl⟩ : ∃ j, len = j + 1 := ⟨len - 1, by omega⟩
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
      ((_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) :: T) H _incr _
      (.Vint (Integers.Int.repr (((incrOf (j + 1) : Nat) : _root_.Int))))
      (fun p hp => List.mem_cons_of_mem _ hp)
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _huff ≠ _incr; decide
        · exact hTincr p hp2)
      (fun le mm hp hT' _ _ => ?_))
    (fun _ _ _ x => x) (fun e le hp hx => ⟨by omega, rfl, hx⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
  refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
    (.Vint (Integers.Int.repr ((j : _root_.Int)))) _ (EvalExpr.Econst_int _ _)
    ?_ ?_
  · refine EvalExpr.Ebinop .Osub _ _ _
      (.Vint (Integers.Int.repr (((j + 1 : Nat) : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _len tuint _
        (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemLen))))
      (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_sub_uint_int]
    show some (Val.Vint (Integers.Int.sub
              (Integers.Int.repr (((j + 1 : Nat) : _root_.Int)))
              (Integers.Int.repr 1))) = _
    rw [show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl, u32_sub_one]
  · simp only [typeof]
    rw [semBinop_shl_uint _ _ _ _ (ltu_iwordsize j (by omega)),
        shl_one_pow j (by omega)]
    rfl

/-- `if (incr) { huff &= incr - 1; huff += incr; } else huff = 0;` -/
theorem incrFix_triple
    (hh : huff < 4294967296) (hlen15 : len ≤ 15)
    (hThuff : ∀ p ∈ T, p.1 ≠ _huff) :
    Triple ge fe f_inflate_table (IncPost bh bc bo huff len T H) incrFix
      (.only (fun e le hp => ∃ f : Nat,
        LocalSt (envOf bh bc bo)
          ((_huff, .Vint (Integers.Int.repr
              (((bwInc huff len : Nat) : _root_.Int))))
            :: (_incr, .Vint (Integers.Int.repr
                 (((incrOf f : Nat) : _root_.Int)))) :: T) H e le hp)) := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (f : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hfl : f ≤ len) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hgo : bwIncGo huff len = bwIncGo huff f) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hbit : ∀ k, f = k + 1 → huff / 2 ^ k % 2 = 0) => ?_)
  have hbw : bwInc huff len = bwIncGo huff f := hgo
  match f with
  | 0 =>
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := ne0_eval_uint (ge := ge) (e := envOf bh bc bo) (m := mm)
          _incr (incrOf 0) (by decide) (hT'.get List.mem_cons_self)
        rw [show decide (incrOf 0 ≠ 0) = false from by
              rw [decide_eq_false_iff_not]; exact fun hne => hne rfl] at h
        exact h
      · refine triple_conseq ge fe f_inflate_table
          (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
            ((_incr, .Vint (Integers.Int.repr
                (((incrOf 0 : Nat) : _root_.Int)))) :: T) H _huff _
            (.Vint (Integers.Int.repr (((bwInc huff len : Nat) : _root_.Int))))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _incr ≠ _huff; decide
              · exact hThuff p hp2)
            (fun le mm hp hT' _ _ => ?_))
          (fun _ _ _ x => x) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        · rw [show ((bwInc huff len : Nat) : _root_.Int) = 0 from by
                rw [hbw]; rfl]
          exact EvalExpr.Econst_int _ _
        · obtain ⟨henv, hT', hH⟩ := hx
          exact ⟨0, henv, hT', hH⟩
  | k + 1 =>
      have hbit0 : huff / 2 ^ k % 2 = 0 := hbit k rfl
      have hval : bwInc huff len = huff % 2 ^ k + 2 ^ k := by
        rw [hbw, bwIncGo_succ, if_neg (by omega)]
      obtain ⟨q, hq⟩ : ∃ q, (2 : Nat) ^ k = q + 1 :=
        ⟨2 ^ k - 1, by have := Nat.two_pow_pos k; omega⟩
      have hpk : (2 : Nat) ^ k < 4294967296 :=
        Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega : k ≤ 15))
          (by omega)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · have h := ne0_eval_uint (ge := ge) (e := envOf bh bc bo) (m := mm)
          _incr (incrOf (k + 1)) (incrOf_lt (k + 1) (by omega))
          (hT'.get List.mem_cons_self)
        rw [show decide (incrOf (k + 1) ≠ 0) = true from by
              rw [decide_eq_true_eq]
              show (2 : Nat) ^ k ≠ 0
              exact Nat.ne_of_gt (Nat.two_pow_pos k)] at h
        exact h
      · refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_huff, .Vint (Integers.Int.repr
                (((huff % 2 ^ k : Nat) : _root_.Int))))
              :: (_incr, .Vint (Integers.Int.repr
                   (((incrOf (k + 1) : Nat) : _root_.Int)))) :: T) H) _ _ _ ?_ ?_
        · -- huff &= incr - 1
          refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
            ((_incr, .Vint (Integers.Int.repr
                (((incrOf (k + 1) : Nat) : _root_.Int)))) :: T) H _huff _
            (.Vint (Integers.Int.repr (((huff % 2 ^ k : Nat) : _root_.Int))))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _incr ≠ _huff; decide
              · exact hThuff p hp2)
            (fun le mm hp hT' _ _ => ?_)
          refine EvalExpr.Ebinop .Oand _ _ _
            (.Vint (Integers.Int.repr ((huff : _root_.Int))))
            (.Vint (Integers.Int.repr ((q : _root_.Int)))) _
            (EvalExpr.Etempvar _huff tuint _
              (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))) ?_ ?_
          · refine EvalExpr.Ebinop .Osub _ _ _
              (.Vint (Integers.Int.repr
                (((incrOf (k + 1) : Nat) : _root_.Int))))
              (.Vint (Integers.Int.repr 1)) _
              (EvalExpr.Etempvar _incr tuint _ (hT'.get List.mem_cons_self))
              (EvalExpr.Econst_int _ _) ?_
            simp only [typeof]
            rw [semBinop_sub_uint_int]
            show some (Val.Vint (Integers.Int.sub
                      (Integers.Int.repr
                        (((incrOf (k + 1) : Nat) : _root_.Int)))
                      (Integers.Int.repr 1))) = _
            rw [show incrOf (k + 1) = q + 1 from hq,
                show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl,
                u32_sub_one]
          · simp only [typeof]
            rw [semBinop_and_uint, u32_and huff q hh (by omega),
                show huff &&& q = huff % 2 ^ k from by
                  rw [show q = 2 ^ k - 1 from by omega]
                  exact Nat.and_two_pow_sub_one_eq_mod huff k]
        · -- huff += incr
          refine triple_conseq ge fe f_inflate_table
            (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
              ((_incr, .Vint (Integers.Int.repr
                  (((incrOf (k + 1) : Nat) : _root_.Int)))) :: T) H _huff _
              (.Vint (Integers.Int.repr
                (((bwInc huff len : Nat) : _root_.Int))))
              (fun p hp => List.mem_cons_of_mem _ hp)
              (fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp2
                · show _incr ≠ _huff; decide
                · exact hThuff p hp2)
              (fun le mm hp hT' _ _ => ?_))
            (fun _ _ _ x => x) (fun e le hp hx => ?_)
            (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
            (fun _ _ hx => hx.elim)
          · refine EvalExpr.Ebinop .Oadd _ _ _
              (.Vint (Integers.Int.repr (((huff % 2 ^ k : Nat) : _root_.Int))))
              (.Vint (Integers.Int.repr
                (((incrOf (k + 1) : Nat) : _root_.Int)))) _
              (EvalExpr.Etempvar _huff tuint _ (hT'.get List.mem_cons_self))
              (EvalExpr.Etempvar _incr tuint _
                (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))) ?_
            simp only [typeof]
            show Cop.semBinaryOperation ge.genv_cenv .Oadd
                  (.Vint (Integers.Int.repr
                    (((huff % 2 ^ k : Nat) : _root_.Int)))) tuint
                  (.Vint (Integers.Int.repr
                    (((incrOf (k + 1) : Nat) : _root_.Int)))) tuint mm = _
            rw [show Cop.semBinaryOperation ge.genv_cenv .Oadd
                    (.Vint (Integers.Int.repr
                      (((huff % 2 ^ k : Nat) : _root_.Int)))) tuint
                    (.Vint (Integers.Int.repr
                      (((incrOf (k + 1) : Nat) : _root_.Int)))) tuint mm
                  = some (.Vint (Integers.Int.add
                      (Integers.Int.repr (((huff % 2 ^ k : Nat) : _root_.Int)))
                      (Integers.Int.repr
                        (((incrOf (k + 1) : Nat) : _root_.Int))))) from rfl,
                u32_add, hval]
            rfl
          · obtain ⟨henv, hT', hH⟩ := hx
            exact ⟨k + 1, henv, hT', hH⟩

/-- **The backwards code increment** (inftrees.c:246-255; AST 1157-1198).
    Touches no memory; the safety-relevant consequence is `Model.bwInc_lt`. -/
theorem bwinc_block_triple
    (hh : huff < 4294967296) (hlen1 : 1 ≤ len) (hlen15 : len ≤ 15)
    (hTincr : ∀ p ∈ T, p.1 ≠ _incr) (hThuff : ∀ p ∈ T, p.1 ≠ _huff)
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ T)
    (stale : Val) (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_incr, stale)
          :: (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) :: T) H)
      bwIncBlock
      { normal := fun e le hp => ∃ f : Nat,
          LocalSt (envOf bh bc bo)
            ((_huff, .Vint (Integers.Int.repr
                (((bwInc huff len : Nat) : _root_.Int))))
              :: (_incr, .Vint (Integers.Int.repr
                   (((incrOf f : Nat) : _root_.Int)))) :: T) H e le hp,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (IncInv bh bc bo huff len T H len) _ _ _
    (incrInit_triple ge fe bh bc bo huff len T H hlen1 hlen15 hTincr hmemLen
      stale) ?_
  refine triple_seq ge fe f_inflate_table _
    (IncPost bh bc bo huff len T H) _ _ _
    (incrLoop_triple ge fe bh bc bo huff len T H hh hlen15 hTincr _)
    (triple_conseq ge fe f_inflate_table
      (incrFix_triple ge fe bh bc bo huff len T H hh hlen15 hThuff)
      (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ hx => hx.elim))

end BwInc


/-! ## §21 The look-ahead loop (inftrees.c:276-281; AST 1309-1352)

        curr = len - drop;
        left = (int)(1 << curr);
        while (curr + drop < max) {
            left -= count[curr + drop];
            if (left <= 0) break;
            curr++;
            left <<= 1;
        }

The loop reads `count[curr + drop]`, and its own guard supplies the bound:
`curr + drop < max ≤ 15`.  `left` is signed 32-bit and is carried **opaque** —
its value picks the exit, but both exits are safe, so nothing about it needs to
be known.  What the invariant does carry is `1 ≤ curr` and `curr + drop ≤ max`;
the second is what later gives `curr ≤ 15`, which `1U << curr` needs (a shift
by 32 or more is `None` in `Cop`, i.e. stuck). -/

theorem semBinop_add_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tuint (.Vint y) tuint m
      = some (.Vint (Integers.Int.add x y)) := rfl

theorem semBinop_le_int_int (cenv : CompositeEnv) (m : Mem)
    (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Ole (.Vint x) tint (.Vint c) tint m
      = some (Val.ofBool (!Integers.Int.lt c x)) := rfl

/-! ### The AST (inftrees.c:276-281; AST 1309-1352) -/

abbrev currDrop : Expr :=
  .Ebinop .Oadd (.Etempvar _curr tuint) (.Etempvar _drop tuint) tuint

abbrev lookGuard : Expr :=
  .Ebinop .Olt currDrop (.Etempvar _max tuint) tint

abbrev lookBody : Stmt :=
  .Ssequence
    (.Ssequence
      (.Sset _t'16 (.Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
        currDrop (tptr tushort)) tushort))
      (.Sset _left (.Ebinop .Osub (.Etempvar _left tint)
        (.Etempvar _t'16 tushort) tint)))
    (.Ssequence
      (.Sifthenelse (.Ebinop .Ole (.Etempvar _left tint)
        (.Econst_int (Integers.Int.repr 0) tint) tint) .Sbreak .Sskip)
      (.Ssequence
        (.Sset _curr (.Ebinop .Oadd (.Etempvar _curr tuint)
          (.Econst_int (Integers.Int.repr 1) tint) tuint))
        (.Sset _left (.Ebinop .Oshl (.Etempvar _left tint)
          (.Econst_int (Integers.Int.repr 1) tint) tint))))

abbrev lookLoop : Stmt := swhile lookGuard lookBody

section Look

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (cnt : Nat → Nat) (drop max c0 : Nat)
variable (T : List (Ident × Val)) (Hrest : HProp)

theorem currDrop_eval {e : Env} {le : TempEnv} {m : Mem} (curr : Nat)
    (hcurrT : le.get _curr
      = some (.Vint (Integers.Int.repr ((curr : _root_.Int)))))
    (hdropT : le.get _drop
      = some (.Vint (Integers.Int.repr ((drop : _root_.Int))))) :
    EvalExpr ge e le m currDrop
      (.Vint (Integers.Int.repr (((curr + drop : Nat) : _root_.Int)))) := by
  refine EvalExpr.Ebinop .Oadd _ _ _
    (.Vint (Integers.Int.repr ((curr : _root_.Int))))
    (.Vint (Integers.Int.repr ((drop : _root_.Int)))) _
    (EvalExpr.Etempvar _curr tuint _ hcurrT)
    (EvalExpr.Etempvar _drop tuint _ hdropT) ?_
  simp only [typeof]
  rw [semBinop_add_uint, u32_add]

theorem lookGuard_eval {e : Env} {le : TempEnv} {m : Mem} (curr : Nat)
    (hcd : curr + drop < 4294967296) (hmax : max < 4294967296)
    (hcurrT : le.get _curr
      = some (.Vint (Integers.Int.repr ((curr : _root_.Int)))))
    (hdropT : le.get _drop
      = some (.Vint (Integers.Int.repr ((drop : _root_.Int)))))
    (hmaxT : le.get _max
      = some (.Vint (Integers.Int.repr ((max : _root_.Int))))) :
    ∃ v, EvalExpr ge e le m lookGuard v
      ∧ Cop.boolVal v (typeof lookGuard) m
        = some (decide (curr + drop < max)) := by
  refine ⟨Val.ofBool (Integers.Int.ltu
      (Integers.Int.repr (((curr + drop : Nat) : _root_.Int)))
      (Integers.Int.repr ((max : _root_.Int)))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Olt _ _ _ _ _ _
      (currDrop_eval ge drop curr hcurrT hdropT)
      (EvalExpr.Etempvar _max tuint _ hmaxT)
      (semBinop_lt_uint _ _ _ _)
  · simp only [typeof, boolVal_ofBool_int]
    rw [ltu_nat32 (curr + drop) max hcd hmax]

/-! ### The invariant

`left` is tracked **exactly**: at the loop head it is
`2^curr - hsum cnt (c0 + drop) (curr - c0)`, where `c0` is the width the loop
entered with (so `c0 + drop` is the current code length and `curr - c0` the
number of widths already examined).  Every exit is safe regardless of `left`,
but the `left ≤ 0` exit is the **sub-table-fit fact** (`LoopFacts.subfit`)
that I2 needs, so the value can no longer be opaque.  The head value is
positive (`hsum < 2^curr`) — that is exactly "the loop has not broken yet" —
which is also what keeps the signed 32-bit word faithful. -/

abbrev Hlook (bc : Block) (cnt : Nat → Nat) (Hrest : HProp) : HProp :=
  arrayU16 .Freeable bc 0 16 cnt ∗ Hrest

def LookInv (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ curr : Nat,
    ∃ _ : c0 ≤ curr, ∃ _ : curr + drop ≤ max, ∃ _ : n = max - (curr + drop),
    ∃ _ : hsum cnt (c0 + drop) (curr - c0) < 2 ^ curr,
      LocalSt (envOf bh bc bo)
        ((_left, .Vint (Integers.Int.repr
            (((2 ^ curr : Nat) : _root_.Int)
              - ((hsum cnt (c0 + drop) (curr - c0) : Nat) : _root_.Int))))
          :: (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) :: T)
        (Hlook bc cnt Hrest) e le hp

def JLook (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ n', n' < n ∧ LookInv bh bc bo cnt drop max c0 T Hrest n' e le hp

def LookPost : Sep.Assn := fun e le hp =>
  ∃ curr : Nat, ∃ lv : Integers.Int, ∃ _ : c0 ≤ curr, ∃ _ : curr + drop ≤ max,
    ∃ _ : curr + drop = max ∨ 2 ^ curr ≤ wsum cnt (c0 + drop) (curr - c0),
      LocalSt (envOf bh bc bo)
        ((_left, .Vint lv)
          :: (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) :: T)
        (Hlook bc cnt Hrest) e le hp

theorem lookbody_triple
    (hcb : ∀ j, cnt j < 65536) (hmax15 : max ≤ 15)
    (hTleft : ∀ p ∈ T, p.1 ≠ _left) (hTcurr : ∀ p ∈ T, p.1 ≠ _curr)
    (hTt16 : ∀ p ∈ T, p.1 ≠ _t'16)
    (hmemDrop : (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) ∈ T)
    (hmemMax : (_max, .Vint (Integers.Int.repr ((max : _root_.Int)))) ∈ T)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (LookInv bh bc bo cnt drop max c0 T Hrest n)
      (.Ssequence (.Sifthenelse lookGuard .Sskip .Sbreak) lookBody)
      { normal := JLook bh bc bo cnt drop max c0 T Hrest n,
        brk := LookPost bh bc bo cnt drop max c0 T Hrest,
        cont := JLook bh bc bo cnt drop max c0 T Hrest n,
        ret := R.ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (curr : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hcc0 : c0 ≤ curr) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hcm : curr + drop ≤ max) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hn : n = max - (curr + drop)) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hpos : hsum cnt (c0 + drop) (curr - c0) < 2 ^ curr) => ?_)
  have hp15 : (2 : Nat) ^ curr ≤ 32768 :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega : curr ≤ 15))
      (by decide)
  obtain ⟨L, hL⟩ : ∃ L : _root_.Int,
      ((2 ^ curr : Nat) : _root_.Int)
        - ((hsum cnt (c0 + drop) (curr - c0) : Nat) : _root_.Int) = L :=
    ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by omega
  have hL2 : L ≤ 32768 := by omega
  rw [hL]
  by_cases hg : curr + drop < max
  · -- the guard holds: read `count[curr+drop]`, then maybe break
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_left, .Vint (Integers.Int.repr L))
          :: (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) :: T)
        (Hlook bc cnt Hrest)) _ _ _ ?_ ?_
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
      have h := lookGuard_eval ge drop max (e := envOf bh bc bo) (m := mm) curr
        (by omega) (by omega)
        (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
        (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemDrop)))
        (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemMax)))
      rw [show decide (curr + drop < max) = true from by
            rw [decide_eq_true_eq]; exact hg] at h
      exact h
    -- `t'16 = count[curr+drop]; left -= t'16;`
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_left, .Vint (Integers.Int.sub (Integers.Int.repr L)
            (Integers.Int.repr (((cnt (curr + drop) : Nat) : _root_.Int)))))
          :: (_t'16, .Vint (Integers.Int.repr
               (((cnt (curr + drop) : Nat) : _root_.Int))))
          :: (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) :: T)
        (Hlook bc cnt Hrest)) _ _ _ ?_ ?_
    · refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'16, .Vint (Integers.Int.repr
              (((cnt (curr + drop) : Nat) : _root_.Int))))
            :: (_left, .Vint (Integers.Int.repr L))
            :: (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) :: T)
          (Hlook bc cnt Hrest)) _ _ _ ?_ ?_
      · -- the array read
        refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
          _t'16 _ (.Vint (Integers.Int.repr
            (((cnt (curr + drop) : Nat) : _root_.Int))))
          (fun p hp => hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _left ≠ _t'16; decide
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · show _curr ≠ _t'16; decide
            · exact hTt16 p hp3)
          (fun le mm hp hT' hH hag => ?_)
        obtain ⟨h1, h2, hd12, heq, harr, hrest⟩ := hH
        subst heq
        exact eval_index_u16 (by decide) harr (Heap.Agrees_union_left hag)
          (by omega : curr + drop < 16) hcb (eval_count_base bh bc bo)
          (currDrop_eval ge drop curr
            (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
            (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemDrop))))
          rfl (cnt_addr0 ge .Unsigned (curr + drop) (by omega))
      · -- left -= t'16
        refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
          ((_t'16, .Vint (Integers.Int.repr
              (((cnt (curr + drop) : Nat) : _root_.Int))))
            :: (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) :: T)
          _ _left _ _
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2))
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _t'16 ≠ _left; decide
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · show _curr ≠ _left; decide
            · exact hTleft p hp3)
          (fun le mm hp hT' _ _ => ?_)
        refine EvalExpr.Ebinop .Osub _ _ _ (.Vint (Integers.Int.repr L))
          (.Vint (Integers.Int.repr
            (((cnt (curr + drop) : Nat) : _root_.Int)))) _
          (EvalExpr.Etempvar _left tint _
            (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self)))
          (EvalExpr.Etempvar _t'16 tushort _ (hT'.get List.mem_cons_self)) ?_
        simp only [typeof]
        rw [semBinop_sub_int_ushort]
    -- `if (left <= 0) break;` then `curr++; left <<= 1;`
    obtain ⟨bb, hbb⟩ : ∃ bb, (!Integers.Int.lt (Integers.Int.repr 0)
        (Integers.Int.sub (Integers.Int.repr L) (Integers.Int.repr
          (((cnt (curr + drop) : Nat) : _root_.Int))))) = bb := ⟨_, rfl⟩
    cases bb with
    | true =>
        have hbb' := hbb
        rw [i32_sub_repr, i32_lt_int 0
              (L - ((cnt (curr + drop) : Nat) : _root_.Int)) (by omega)
              (by omega) (by have := hcb (curr + drop); omega)
              (by have := hcb (curr + drop); omega)] at hbb'
        have hle : ¬ ((0 : _root_.Int)
            < L - ((cnt (curr + drop) : Nat) : _root_.Int)) := by
          intro hgt
          rw [decide_eq_true hgt] at hbb'
          exact absurd hbb' (by decide)
        have hexit : 2 ^ curr ≤ wsum cnt (c0 + drop) (curr - c0) := by
          rw [wsum_hsum, show c0 + drop + (curr - c0) = curr + drop from by
                omega]
          omega
        refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
          (triple_vacuous _ _ _ _ _)
        refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
          (fun le mm hp hT' _ _ => ?_) ?_
        · refine ⟨Val.ofBool (!Integers.Int.lt (Integers.Int.repr 0)
              (Integers.Int.sub (Integers.Int.repr L) (Integers.Int.repr
                (((cnt (curr + drop) : Nat) : _root_.Int))))), ?_, ?_⟩
          · exact EvalExpr.Ebinop .Ole _ _ _ _ _ _
              (EvalExpr.Etempvar _left tint _ (hT'.get List.mem_cons_self))
              (EvalExpr.Econst_int _ _) (semBinop_le_int_int _ _ _ _)
          · simp only [typeof, boolVal_ofBool_int, hbb]
        · refine triple_conseq ge fe f_inflate_table
            (triple_break ge fe f_inflate_table _)
            (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
            (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
          obtain ⟨henv, hT', hH⟩ := hx
          exact ⟨curr, _, hcc0, hcm, Or.inr hexit, henv,
            TempsHold_mono (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · exact List.mem_cons_self
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  List.mem_cons_self)
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ hp3))) hT', hH⟩
    | false =>
        refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_left, .Vint (Integers.Int.sub (Integers.Int.repr L)
                (Integers.Int.repr (((cnt (curr + drop) : Nat) : _root_.Int)))))
              :: (_t'16, .Vint (Integers.Int.repr
                   (((cnt (curr + drop) : Nat) : _root_.Int))))
              :: (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) :: T)
            (Hlook bc cnt Hrest)) _ _ _ ?_ ?_
        · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
            (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
          refine ⟨Val.ofBool (!Integers.Int.lt (Integers.Int.repr 0)
              (Integers.Int.sub (Integers.Int.repr L) (Integers.Int.repr
                (((cnt (curr + drop) : Nat) : _root_.Int))))), ?_, ?_⟩
          · exact EvalExpr.Ebinop .Ole _ _ _ _ _ _
              (EvalExpr.Etempvar _left tint _ (hT'.get List.mem_cons_self))
              (EvalExpr.Econst_int _ _) (semBinop_le_int_int _ _ _ _)
          · simp only [typeof, boolVal_ofBool_int, hbb]
        -- curr++
        refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_curr, .Vint (Integers.Int.repr
                (((curr + 1 : Nat) : _root_.Int))))
              :: (_left, .Vint (Integers.Int.sub (Integers.Int.repr L)
                   (Integers.Int.repr
                     (((cnt (curr + drop) : Nat) : _root_.Int)))))
              :: (_t'16, .Vint (Integers.Int.repr
                   (((cnt (curr + drop) : Nat) : _root_.Int)))) :: T)
            (Hlook bc cnt Hrest)) _ _ _ ?_ ?_
        · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
            ((_left, .Vint (Integers.Int.sub (Integers.Int.repr L)
                (Integers.Int.repr (((cnt (curr + drop) : Nat) : _root_.Int)))))
              :: (_t'16, .Vint (Integers.Int.repr
                   (((cnt (curr + drop) : Nat) : _root_.Int)))) :: T)
            _ _curr _ _
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · exact List.mem_cons_self
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · exact List.mem_cons_of_mem _ List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ hp3)))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _left ≠ _curr; decide
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · show _t'16 ≠ _curr; decide
              · exact hTcurr p hp3)
            (fun le mm hp hT' _ _ => ?_)
          refine EvalExpr.Ebinop .Oadd _ _ _
            (.Vint (Integers.Int.repr ((curr : _root_.Int))))
            (.Vint (Integers.Int.repr 1)) _
            (EvalExpr.Etempvar _curr tuint _
              (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                List.mem_cons_self))))
            (EvalExpr.Econst_int _ _) ?_
          simp only [typeof]
          rw [semBinop_add_uint_int]
          show some (Val.Vint (Integers.Int.add
                    (Integers.Int.repr ((curr : _root_.Int)))
                    (Integers.Int.repr 1))) = _
          rw [show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl, u32_add]
        -- left <<= 1
        refine triple_conseq ge fe f_inflate_table
          (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
            ((_curr, .Vint (Integers.Int.repr
                (((curr + 1 : Nat) : _root_.Int))))
              :: (_t'16, .Vint (Integers.Int.repr
                   (((cnt (curr + drop) : Nat) : _root_.Int)))) :: T)
            _ _left _
            (.Vint (Integers.Int.shl (Integers.Int.sub (Integers.Int.repr L)
              (Integers.Int.repr (((cnt (curr + drop) : Nat) : _root_.Int))))
              (Integers.Int.repr 1)))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _curr ≠ _left; decide
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · show _t'16 ≠ _left; decide
              · exact hTleft p hp3)
            (fun le mm hp hT' _ _ => ?_))
          (fun _ _ _ x => x) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        · refine EvalExpr.Ebinop .Oshl _ _ _
            (.Vint (Integers.Int.sub (Integers.Int.repr L) (Integers.Int.repr
              (((cnt (curr + drop) : Nat) : _root_.Int)))))
            (.Vint (Integers.Int.repr 1)) _
            (EvalExpr.Etempvar _left tint _
              (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self)))
            (EvalExpr.Econst_int _ _) ?_
          simp only [typeof]
          rw [semBinop_shl_int_one]
        · obtain ⟨henv, hT', hH⟩ := hx
          have hbb' := hbb
          rw [i32_sub_repr, i32_lt_int 0
                (L - ((cnt (curr + drop) : Nat) : _root_.Int)) (by omega)
                (by omega) (by have := hcb (curr + drop); omega)
                (by have := hcb (curr + drop); omega)] at hbb'
          have hgt : (0 : _root_.Int)
              < L - ((cnt (curr + drop) : Nat) : _root_.Int) := by
            by_cases hq : (0 : _root_.Int)
                < L - ((cnt (curr + drop) : Nat) : _root_.Int)
            · exact hq
            · rw [decide_eq_false hq] at hbb'
              exact absurd hbb' (by decide)
          have hrec : hsum cnt (c0 + drop) (curr + 1 - c0)
              = 2 * (hsum cnt (c0 + drop) (curr - c0) + cnt (curr + drop)) := by
            rw [show curr + 1 - c0 = (curr - c0) + 1 from by omega]
            show 2 * wsum cnt (c0 + drop) (curr - c0) = _
            rw [wsum_hsum, show c0 + drop + (curr - c0) = curr + drop from by
                  omega]
          have hposn : hsum cnt (c0 + drop) (curr + 1 - c0) < 2 ^ (curr + 1) := by
            rw [hrec, show (2 : Nat) ^ (curr + 1) = 2 * 2 ^ curr from by
                  rw [Nat.pow_succ]; omega]
            omega
          have harg : 2 * (L - ((cnt (curr + drop) : Nat) : _root_.Int))
              = ((2 ^ (curr + 1) : Nat) : _root_.Int)
                - ((hsum cnt (c0 + drop) (curr + 1 - c0) : Nat)
                    : _root_.Int) := by
            rw [hrec, show (2 : Nat) ^ (curr + 1) = 2 * 2 ^ curr from by
                  rw [Nat.pow_succ]; omega]
            omega
          have hval : Integers.Int.shl (Integers.Int.sub (Integers.Int.repr L)
                (Integers.Int.repr (((cnt (curr + drop) : Nat) : _root_.Int))))
                (Integers.Int.repr 1)
              = Integers.Int.repr (((2 ^ (curr + 1) : Nat) : _root_.Int)
                  - ((hsum cnt (c0 + drop) (curr + 1 - c0) : Nat)
                      : _root_.Int)) := by
            rw [i32_sub_repr, i32_shl_one, harg]
          rw [hval] at hT'
          refine ⟨max - (curr + 1 + drop), by omega, curr + 1,
            by omega, by omega, by omega, hposn, henv, ?_, hH⟩
          exact TempsHold_mono (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact List.mem_cons_self
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hp3))) hT'
  · -- the guard fails: leave the loop with `curr` as it stands
    refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
      (triple_vacuous _ _ _ _ _)
    refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · have h := lookGuard_eval ge drop max (e := envOf bh bc bo) (m := mm) curr
        (by omega) (by omega)
        (hT'.get (List.mem_cons_of_mem _ List.mem_cons_self))
        (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemDrop)))
        (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemMax)))
      rw [show decide (curr + drop < max) = false from by
            rw [decide_eq_false_iff_not]; exact hg] at h
      exact h
    · refine triple_conseq ge fe f_inflate_table
        (triple_break ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
      obtain ⟨henv, hT', hH⟩ := hx
      exact ⟨curr, _, hcc0, hcm, Or.inl (by omega), henv, hT', hH⟩

theorem lookskip_triple (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (JLook bh bc bo cnt drop max c0 T Hrest n)
      .Sskip
      { normal := fun e le hp =>
          ∃ n', n' < n ∧ LookInv bh bc bo cnt drop max c0 T Hrest n' e le hp,
        brk := LookPost bh bc bo cnt drop max c0 T Hrest, cont := Assn.no,
        ret := R.ret, goto := R.goto } :=
  triple_conseq ge fe f_inflate_table (triple_skip ge fe f_inflate_table _)
    (fun _ _ _ x => x) (fun _ _ _ hx => hx)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- **The look-ahead loop** (inftrees.c:276-281). -/
theorem lookLoop_triple
    (hcb : ∀ j, cnt j < 65536) (hmax15 : max ≤ 15)
    (hTleft : ∀ p ∈ T, p.1 ≠ _left) (hTcurr : ∀ p ∈ T, p.1 ≠ _curr)
    (hTt16 : ∀ p ∈ T, p.1 ≠ _t'16)
    (hmemDrop : (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) ∈ T)
    (hmemMax : (_max, .Vint (Integers.Int.repr ((max : _root_.Int)))) ∈ T)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table (LookInv bh bc bo cnt drop max c0 T Hrest n)
      lookLoop
      { normal := LookPost bh bc bo cnt drop max c0 T Hrest, brk := R.brk,
        cont := R.cont, ret := R.ret, goto := R.goto } :=
  triple_loop ge fe f_inflate_table _ (LookInv bh bc bo cnt drop max c0 T Hrest)
    (JLook bh bc bo cnt drop max c0 T Hrest) _ _
    (lookbody_triple ge fe bh bc bo cnt drop max c0 T Hrest hcb hmax15 hTleft
      hTcurr hTt16 hmemDrop hmemMax _)
    (lookskip_triple ge fe bh bc bo cnt drop max c0 T Hrest _) n

end Look


/-! ## §22 The sub-table transition's straight-line statements
    (inftrees.c:265-294; AST 1281-1308 and 1353-1413)

        if (drop == 0) drop = root;
        next += min;
        curr = len - drop;
        left = (int)(1 << curr);
        …look-ahead loop (§21)…
        used += 1U << curr;
        …ENOUGH check (§15/§18)…
        low = huff & mask;
        …root back-pointer writes (§19)…

One statement per lemma, each over an abstract tracked list `T` with the
written temporary at the head, so the main-loop assembly (§26) can chain
them without re-deriving anything.

Only two of these carry a stuck-freedom obligation, and both are the same one:
`1 << curr` needs `curr < 32`, because `Cop`'s shift is `None` at a shift count
of 32 or more.  `curr = len - drop ≤ 15` supplies it, and the look-ahead loop's
`curr + drop ≤ max ≤ 15` preserves it.  Everything else here is total —
in particular `next += min` is pointer arithmetic, which never gets stuck; its
*bound* matters only later, for the region the fill loop writes into. -/

/-- `a - b` on 32-bit words, when `b ≤ a`. -/
theorem u32_sub_nat (a b : Nat) (hba : b ≤ a) (ha : a < 4294967296) :
    Integers.Int.sub (Integers.Int.repr ((a : _root_.Int)))
        (Integers.Int.repr ((b : _root_.Int)))
      = Integers.Int.repr (((a - b : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  show (_ - _ : BitVec 32).toNat = _
  rw [BitVec.toNat_sub, u32_toNat_repr, u32_toNat_repr, u32_toNat_repr,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 4294967296),
      Nat.mod_eq_of_lt (by omega : a - b < 4294967296)]
  omega

theorem semBinop_eq_uint_int (cenv : CompositeEnv) (m : Mem) (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tuint (.Vint c) tint m
      = some (Val.ofBool (Integers.Int.eq x c)) := rfl

theorem semBinop_shl_int_uint (cenv : CompositeEnv) (m : Mem) (x y : Integers.Int)
    (h : Integers.Int.ltu y Integers.Int.iwordsize = true) :
    Cop.semBinaryOperation cenv .Oshl (.Vint x) tint (.Vint y) tuint m
      = some (.Vint (Integers.Int.shl x y)) := by
  show (if Integers.Int.ltu y Integers.Int.iwordsize
        then some (Val.Vint (Integers.Int.shl x y)) else none) = _
  rw [h]; rfl

section Sub

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (T : List (Ident × Val)) (H : HProp)

/-- `if (drop == 0) drop = root;`  Either way `drop` ends up equal to `root`,
    because on entry it is `0` or already `root`. -/
theorem drop_init_triple (drop root : Nat)
    (hdr : drop = 0 ∨ drop = root) (hd32 : drop < 4294967296)
    (hTdrop : ∀ p ∈ T, p.1 ≠ _drop)
    (hmemRoot : (_root, .Vint (Integers.Int.repr ((root : _root_.Int)))) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) :: T) H)
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar _drop tuint)
        (.Econst_int (Integers.Int.repr 0) tint) tint)
        (.Sset _drop (.Etempvar _root tuint)) .Sskip)
      (.only (LocalSt (envOf bh bc bo)
        ((_drop, .Vint (Integers.Int.repr ((root : _root_.Int)))) :: T) H)) := by
  have hguard : ∀ (le : TempEnv) (mm : Mem),
      TempsHold ((_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) :: T) le →
      ∃ v, EvalExpr ge (envOf bh bc bo) le mm
          (.Ebinop .Oeq (.Etempvar _drop tuint)
            (.Econst_int (Integers.Int.repr 0) tint) tint) v
        ∧ Cop.boolVal v tint mm = some (decide (drop = 0)) := by
    intro le mm hT'
    refine ⟨Val.ofBool (Integers.Int.eq
        (Integers.Int.repr ((drop : _root_.Int))) (Integers.Int.repr 0)), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
        (EvalExpr.Etempvar _drop tuint _ (hT'.get List.mem_cons_self))
        (EvalExpr.Econst_int _ _) (semBinop_eq_uint_int _ _ _ _)
    · simp only [boolVal_ofBool_int]
      rw [show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
          eq_nat32 drop 0 hd32 (by omega)]
  by_cases hz : drop = 0
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => by
        have h := hguard le mm hT'
        rw [show decide (drop = 0) = true from by
              rw [decide_eq_true_eq]; exact hz] at h
        exact h) ?_
    exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _drop _ _
      (fun p hp => List.mem_cons_of_mem _ hp) hTdrop
      (fun le mm hp hT' _ _ =>
        EvalExpr.Etempvar _root tuint _
          (hT'.get (List.mem_cons_of_mem _ hmemRoot)))
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => by
        have h := hguard le mm hT'
        rw [show decide (drop = 0) = false from by
              rw [decide_eq_false_iff_not]; exact hz] at h
        exact h) ?_
    have hdr' : drop = root := by
      rcases hdr with h | h
      · exact absurd h hz
      · exact h
    subst hdr'
    exact triple_skip ge fe f_inflate_table _

/-- `next += min;` — a pointer bump *inside the same block*, which is what makes
    `next - *table` (§19) well defined. -/
theorem next_bump_triple
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (nB : Block) (nO : Integers.Ptrofs) (mn : Nat)
    (hmn31 : (mn : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned nO + 4 * (mn : _root_.Int)
             < 18446744073709551616)
    (hTnext : ∀ p ∈ T, p.1 ≠ _next)
    (hmemMin : (_min, .Vint (Integers.Int.repr ((mn : _root_.Int)))) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) ((_next, .Vptr nB nO) :: T) H)
      (.Sset _next (.Ebinop .Oadd
        (.Etempvar _next (tptr (Ty.Tstruct __1353 noattr)))
        (.Etempvar _min tuint) (tptr (Ty.Tstruct __1353 noattr))))
      (.only (LocalSt (envOf bh bc bo)
        ((_next, .Vptr nB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr)
            .Unsigned nO (Integers.Int.repr ((mn : _root_.Int))))) :: T) H)) :=
  triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _next _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTnext
    (fun le mm hp hT' _ _ =>
      EvalExpr.Ebinop .Oadd _ _ _ (.Vptr nB nO)
        (.Vint (Integers.Int.repr ((mn : _root_.Int)))) _
        (EvalExpr.Etempvar _next _ _ (hT'.get List.mem_cons_self))
        (EvalExpr.Etempvar _min tuint _
          (hT'.get (List.mem_cons_of_mem _ hmemMin)))
        (semAdd_ptr_int _ _ _ _ _ rfl))

/-- The bumped pointer's offset, in `Nat` form. -/
theorem next_bump_addr
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (nO : Integers.Ptrofs) (mn : Nat)
    (hmn31 : (mn : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned nO + 4 * (mn : _root_.Int)
             < 18446744073709551616) :
    Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
        (Integers.Int.repr ((mn : _root_.Int))))
      = Integers.Ptrofs.unsigned nO + 4 * (mn : _root_.Int) := by
  have hsz : sizeof ge.genv_cenv (Ty.Tstruct __1353 noattr) = 4 := by
    rw [hcenv]; exact InflateTable.Layout.code_sizeof
  refine idxOfs_unsigned ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned nO
    mn 4 hsz (by decide) hmn31 ?_
  obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned nO = A := ⟨_, rfl⟩
  rw [hA] at hno ⊢
  have h2 : A + 4 * ((mn : Nat) : _root_.Int)
      < (18446744073709551616 : _root_.Int) := hno
  show A + ((4 : Nat) : _root_.Int) * ((mn : Nat) : _root_.Int)
        < (18446744073709551616 : _root_.Int)
  omega

/-- `curr = len - drop;` -/
theorem curr_set_triple (len drop : Nat)
    (hdl : drop ≤ len) (hl32 : len < 4294967296)
    (hTcurr : ∀ p ∈ T, p.1 ≠ _curr)
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ T)
    (hmemDrop : (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) ∈ T)
    (old : Val) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) ((_curr, old) :: T) H)
      (.Sset _curr (.Ebinop .Osub (.Etempvar _len tuint)
        (.Etempvar _drop tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        ((_curr, .Vint (Integers.Int.repr (((len - drop : Nat) : _root_.Int))))
          :: T) H)) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _curr _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTcurr
    (fun le mm hp hT' _ _ => ?_)
  refine EvalExpr.Ebinop .Osub _ _ _
    (.Vint (Integers.Int.repr ((len : _root_.Int))))
    (.Vint (Integers.Int.repr ((drop : _root_.Int)))) _
    (EvalExpr.Etempvar _len tuint _
      (hT'.get (List.mem_cons_of_mem _ hmemLen)))
    (EvalExpr.Etempvar _drop tuint _
      (hT'.get (List.mem_cons_of_mem _ hmemDrop))) ?_
  simp only [typeof]
  rw [semBinop_sub_uint, u32_sub_nat len drop hdl hl32]

/-- `left = (int)(1 << curr);` — the shift needs `curr < 32`, and a shift by 32
    or more is `None` in `Cop`, i.e. **stuck**.  That is the one safety
    obligation in this statement. -/
theorem left_init_triple (curr : Nat) (hc32 : curr < 32)
    (hTleft : ∀ p ∈ T, p.1 ≠ _left)
    (hmemCurr : (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) ∈ T)
    (old : Val) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) ((_left, old) :: T) H)
      (.Sset _left (.Ecast (.Ebinop .Oshl
        (.Econst_int (Integers.Int.repr 1) tint) (.Etempvar _curr tuint) tint)
        tint))
      (.only (LocalSt (envOf bh bc bo)
        ((_left, .Vint (Integers.Int.repr (((2 ^ curr : Nat) : _root_.Int))))
          :: T) H)) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _left _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTleft
    (fun le mm hp hT' _ _ => ?_)
  refine EvalExpr.Ecast _ _ _ _ ?_ (by simp only [typeof]; exact semCast_int_int mm _)
  refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
    (.Vint (Integers.Int.repr ((curr : _root_.Int)))) _
    (EvalExpr.Econst_int _ _)
    (EvalExpr.Etempvar _curr tuint _
      (hT'.get (List.mem_cons_of_mem _ hmemCurr))) ?_
  simp only [typeof]
  rw [semBinop_shl_int_uint _ _ _ _ (ltu_iwordsize curr hc32),
      shl_one_pow curr hc32]

/-- `used += 1U << curr;` — same shift obligation. -/
theorem used_add_triple (used curr : Nat) (hc32 : curr < 32)
    (hTused : ∀ p ∈ T, p.1 ≠ _used)
    (hmemCurr : (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_used, .Vint (Integers.Int.repr ((used : _root_.Int)))) :: T) H)
      (.Sset _used (.Ebinop .Oadd (.Etempvar _used tuint)
        (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
          (.Etempvar _curr tuint) tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        ((_used, .Vint (Integers.Int.repr
            (((used + 2 ^ curr : Nat) : _root_.Int)))) :: T) H)) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _used _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTused
    (fun le mm hp hT' _ _ => ?_)
  refine EvalExpr.Ebinop .Oadd _ _ _
    (.Vint (Integers.Int.repr ((used : _root_.Int))))
    (.Vint (Integers.Int.repr (((2 ^ curr : Nat) : _root_.Int)))) _
    (EvalExpr.Etempvar _used tuint _ (hT'.get List.mem_cons_self)) ?_ ?_
  · refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
      (.Vint (Integers.Int.repr ((curr : _root_.Int)))) _
      (EvalExpr.Econst_int _ _)
      (EvalExpr.Etempvar _curr tuint _
        (hT'.get (List.mem_cons_of_mem _ hmemCurr))) ?_
    simp only [typeof]
    rw [semBinop_shl_uint _ _ _ _ (ltu_iwordsize curr hc32),
        shl_one_pow curr hc32]
  · simp only [typeof]
    rw [semBinop_add_uint, u32_add]

/-- `low = huff & mask;` with `mask = 2^root - 1`, so `low = huff % 2^root`. -/
theorem low_set_triple (huff root : Nat) (hh32 : huff < 4294967296)
    (hr32 : root < 32)
    (hTlow : ∀ p ∈ T, p.1 ≠ _low)
    (hmemHuff : (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) ∈ T)
    (hmemMask : (_mask, .Vint (Integers.Int.repr
      (((2 ^ root - 1 : Nat) : _root_.Int)))) ∈ T)
    (old : Val) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) ((_low, old) :: T) H)
      (.Sset _low (.Ebinop .Oand (.Etempvar _huff tuint)
        (.Etempvar _mask tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        ((_low, .Vint (Integers.Int.repr
            (((huff % 2 ^ root : Nat) : _root_.Int)))) :: T) H)) := by
  have hp2 : (2 : Nat) ^ root < 4294967296 :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) hr32) (by decide)
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _low _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTlow
    (fun le mm hp hT' _ _ => ?_)
  refine EvalExpr.Ebinop .Oand _ _ _
    (.Vint (Integers.Int.repr ((huff : _root_.Int))))
    (.Vint (Integers.Int.repr (((2 ^ root - 1 : Nat) : _root_.Int)))) _
    (EvalExpr.Etempvar _huff tuint _
      (hT'.get (List.mem_cons_of_mem _ hmemHuff)))
    (EvalExpr.Etempvar _mask tuint _
      (hT'.get (List.mem_cons_of_mem _ hmemMask))) ?_
  simp only [typeof]
  rw [semBinop_and_uint, u32_and huff (2 ^ root - 1) hh32 (by omega),
      Nat.and_two_pow_sub_one_eq_mod]

end Sub


/-! ## §23 Building one table entry (inftrees.c:222-234; AST 974-1109)

        here.bits = (unsigned char)(len - drop);
        if (work[sym] + 1U < match) { here.op = 0;  here.val = work[sym]; }
        else if (work[sym] >= match) {
            here.op  = (unsigned char)(extra[work[sym] - match]);
            here.val = base[work[sym] - match];
        }
        else { here.op = 32 + 64; here.val = 0; }

**This is where assumption A3 earns its keep.**  The middle branch indexes the
readonly globals `base`/`extra` at `work[sym] - match`, and the C checks
nothing: the branch guard gives `work[sym] ≥ match`, so the index is a
well-defined `Nat`, but nothing in the function bounds it above.  A3 is exactly
that missing bound, and `read_global_triple` is where it is consumed.

`work[sym]` itself is bounded by the sort loop's `sym < nlive`. -/

/-! ### Bridges -/

theorem zero_ext8_mod (c : Nat) :
    Integers.Int.zero_ext 8 (Integers.Int.repr ((c : _root_.Int)))
      = Integers.Int.repr (((c % 256 : Nat) : _root_.Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Integers.Int.zero_ext, Integers.MI.zero_ext, ge_iff_le,
             show ¬ (32 ≤ 8) from by omega, if_false]
  rw [BitVec.toNat_and, u32_toNat_repr]
  show _ &&& (BitVec.allOnes 32 >>> (32 - 8)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_allOnes,
      show ((2 ^ 32 - 1 : Nat) >>> (32 - 8)) = 2 ^ 8 - 1 from by rfl,
      Nat.and_two_pow_sub_one_eq_mod, u32_toNat_repr]
  omega

theorem semCast_int_uchar (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tint tuchar m
      = some (.Vint (Integers.Int.zero_ext 8 x)) := rfl

theorem semCast_ushort_uchar (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tushort tuchar m
      = some (.Vint (Integers.Int.zero_ext 8 x)) := rfl

theorem semBinop_add_int_int (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tint (.Vint y) tint m
      = some (.Vint (Integers.Int.add x y)) := rfl

theorem semBinop_add_ushort_uint (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vint x) tushort (.Vint y) tuint m
      = some (.Vint (Integers.Int.add x y)) := rfl

theorem semBinop_sub_ushort_uint (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vint x) tushort (.Vint y) tuint m
      = some (.Vint (Integers.Int.sub x y)) := rfl

theorem semBinop_ge_ushort_uint (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oge (.Vint x) tushort (.Vint y) tuint m
      = some (Val.ofBool (!Integers.Int.ltu x y)) := rfl

/-! ### The AST -/

abbrev workIdx : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _work (tptr tushort))
    (.Etempvar _sym tuint) (tptr tushort)) tushort

abbrev gIdx (arr tmp : Ident) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar arr (tptr tushort))
    (.Ebinop .Osub (.Etempvar tmp tushort) (.Etempvar _match tuint) tuint)
    (tptr tushort)) tushort

abbrev hereW (fld : Ident) (fty : Ty) (rhs : Expr) : Stmt :=
  .Sassign (.Efield (.Evar _here (Ty.Tstruct __1353 noattr)) fld fty) rhs

section Entry

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)

/-- `tmp = work[sym];` -/
theorem read_work_triple
    (pw : Permission) (hpw : permOrder pw .Readable = true)
    (workB : Block) (workO : Integers.Ptrofs) (nwork : Nat) (workF : Nat → Nat)
    (hwb : ∀ j, workF j < 65536)
    (sym : Nat) (hs : sym < nwork) (hn31 : (nwork : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned workO + 2 * (nwork : _root_.Int)
             < 18446744073709551616)
    (tmp : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemSym : (_sym, .Vint (Integers.Int.repr ((sym : _root_.Int)))) ∈ l)
    (hmemWork : (_work, .Vptr workB workO) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ tmp) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
         ∗ Hrest))
      (.Sset tmp workIdx)
      (.only (LocalSt (envOf bh bc bo)
        ((tmp, .Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int))))
          :: l)
        (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
         ∗ Hrest))) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ l _ tmp _ _
    (fun p hp => hp) hne (fun le mm hp hT' hH hag => ?_)
  obtain ⟨h1, h2, hd12, heq, harr, hrest⟩ := hH
  subst heq
  exact eval_index_u16 hpw harr (Heap.Agrees_union_left hag) hs hwb
    (EvalExpr.Etempvar _work _ _ (hT'.get hmemWork))
    (EvalExpr.Etempvar _sym tuint _ (hT'.get hmemSym))
    rfl
    (u16Ofs_unsigned ge.genv_cenv .Unsigned workO sym (by omega)
      (no_wrap_mono workO nwork sym hno (by omega)))

/-- `tmp2 = arr[tmp - match];` for the readonly globals `base` / `extra`.
    The index bound `v - match < n` is **assumption A3** — the C checks
    nothing here. -/
theorem read_global_triple
    (pg : Permission) (hpg : permOrder pg .Readable = true)
    (gB : Block) (ng : Nat) (gF : Nat → Nat) (hgb : ∀ j, gF j < 65536)
    (v mtch : Nat) (hge : mtch ≤ v) (hidx : v - mtch < ng)
    (hn31 : (ng : _root_.Int) < 2147483648)
    (hv32 : v < 4294967296)
    (arr tmp tmp2 : Ident) (l : List (Ident × Val)) (Hrest : HProp)
    (hmemArr : (arr, .Vptr gB Integers.Ptrofs.zero) ∈ l)
    (hmemTmp : (tmp, .Vint (Integers.Int.repr ((v : _root_.Int)))) ∈ l)
    (hmemM : (_match, .Vint (Integers.Int.repr ((mtch : _root_.Int)))) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ tmp2) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (arrayU16 pg gB 0 ng gF ∗ Hrest))
      (.Sset tmp2 (gIdx arr tmp))
      (.only (LocalSt (envOf bh bc bo)
        ((tmp2, .Vint (Integers.Int.repr
            (((gF (v - mtch) : Nat) : _root_.Int)))) :: l)
        (arrayU16 pg gB 0 ng gF ∗ Hrest))) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ l _ tmp2 _ _
    (fun p hp => hp) hne (fun le mm hp hT' hH hag => ?_)
  obtain ⟨h1, h2, hd12, heq, harr, hrest⟩ := hH
  subst heq
  have hidxE : EvalExpr ge (envOf bh bc bo) le mm
      (.Ebinop .Osub (.Etempvar tmp tushort) (.Etempvar _match tuint) tuint)
      (.Vint (Integers.Int.repr (((v - mtch : Nat) : _root_.Int)))) := by
    refine EvalExpr.Ebinop .Osub _ _ _
      (.Vint (Integers.Int.repr ((v : _root_.Int))))
      (.Vint (Integers.Int.repr ((mtch : _root_.Int)))) _
      (EvalExpr.Etempvar tmp tushort _ (hT'.get hmemTmp))
      (EvalExpr.Etempvar _match tuint _ (hT'.get hmemM)) ?_
    simp only [typeof]
    rw [semBinop_sub_ushort_uint, u32_sub_nat v mtch hge hv32]
  refine eval_index_u16 hpg (by rw [ptrofs_unsigned_zero]; exact harr)
    (Heap.Agrees_union_left hag) hidx hgb
    (EvalExpr.Etempvar arr _ _ (hT'.get hmemArr)) hidxE rfl ?_
  exact u16Ofs_unsigned ge.genv_cenv .Unsigned Integers.Ptrofs.zero (v - mtch)
    (by omega)
    (by rw [ptrofs_unsigned_zero]
        show (0 : _root_.Int) + 2 * (((v - mtch : Nat)) : _root_.Int)
              < 18446744073709551616
        omega)

end Entry


/-! ### The footprint, and the statements against it

`Hentry` fixes one canonical order for the six components this block touches,
so every intermediate state in the chain is written the same way; each statement
lemma below permutes internally (`localst_perm`-style, via `triple_conseq` and
`sep_cancel`) rather than making the caller do it. -/

section Entry2

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (pw : Permission) (workB : Block) (workO : Integers.Ptrofs)
variable (nwork : Nat) (workF : Nat → Nat)
variable (pg : Permission) (xB bB : Block) (nx nb : Nat)
variable (extraF baseF : Nat → Nat) (Hrest : HProp)

/-- The entry-construction footprint, in one canonical order: the three arrays
    that are read, then `here`'s three field slots, then the caller's rest. -/
abbrev Hentry (v0 v1 v2 : Val) : HProp :=
  arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
  ∗ (arrayU16 pg xB 0 nx extraF
     ∗ (arrayU16 pg bB 0 nb baseF
        ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
           ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
              ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2 ∗ Hrest)))))

/-- `here.op = e;` against the canonical footprint. -/
theorem entry_op_write
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (v0 v1 v2 vnew : Val) (rhs : Expr) (l : List (Ident × Val))
    (hev : ∀ (le : TempEnv) (m : Mem), TempsHold l le → ∃ v,
      EvalExpr ge (envOf bh bc bo) le m rhs v
      ∧ Cop.semCast v (typeof rhs) tuchar m = some vnew) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      (.Sassign (.Efield (.Evar _here (Ty.Tstruct __1353 noattr)) _op tuchar)
        rhs)
      (.only (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          vnew v1 v2))) := by
  have hperm : ∀ w : Val,
      Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          w v1 v2
      = mapsto .Mint8unsigned .Freeable bh 0 w
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
           ∗ (arrayU16 pg xB 0 nx extraF
              ∗ (arrayU16 pg bB 0 nb baseF
                 ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
                    ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
                       ∗ Hrest))))) := by
    intro w; sep_cancel
  refine triple_conseq ge fe f_inflate_table
    (here_field_write ge fe bh bc bo hcenv _op tuchar .Mint8unsigned 0 rfl
      InflateTable.Layout.op_offset (by decide) l _ v0 vnew rhs hev)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hperm]; exact hx.2.2⟩)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [hperm]; exact hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- `here.bits = e;` -/
theorem entry_bits_write
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (v0 v1 v2 vnew : Val) (rhs : Expr) (l : List (Ident × Val))
    (hev : ∀ (le : TempEnv) (m : Mem), TempsHold l le → ∃ v,
      EvalExpr ge (envOf bh bc bo) le m rhs v
      ∧ Cop.semCast v (typeof rhs) tuchar m = some vnew) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      (.Sassign (.Efield (.Evar _here (Ty.Tstruct __1353 noattr)) _bits tuchar)
        rhs)
      (.only (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 vnew v2))) := by
  have hperm : ∀ w : Val,
      Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 w v2
      = mapsto .Mint8unsigned .Freeable bh 1 w
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
           ∗ (arrayU16 pg xB 0 nx extraF
              ∗ (arrayU16 pg bB 0 nb baseF
                 ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
                    ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
                       ∗ Hrest))))) := by
    intro w; sep_cancel
  refine triple_conseq ge fe f_inflate_table
    (here_field_write ge fe bh bc bo hcenv _bits tuchar .Mint8unsigned 1 rfl
      InflateTable.Layout.bits_offset (by decide) l _ v1 vnew rhs hev)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hperm]; exact hx.2.2⟩)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [hperm]; exact hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- `here.val = e;` -/
theorem entry_val_write
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (v0 v1 v2 vnew : Val) (rhs : Expr) (l : List (Ident × Val))
    (hev : ∀ (le : TempEnv) (m : Mem), TempsHold l le → ∃ v,
      EvalExpr ge (envOf bh bc bo) le m rhs v
      ∧ Cop.semCast v (typeof rhs) tushort m = some vnew) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      (.Sassign (.Efield (.Evar _here (Ty.Tstruct __1353 noattr)) _val tushort)
        rhs)
      (.only (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 vnew))) := by
  have hperm : ∀ w : Val,
      Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 w
      = mapsto .Mint16unsigned .Freeable bh 2 w
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
           ∗ (arrayU16 pg xB 0 nx extraF
              ∗ (arrayU16 pg bB 0 nb baseF
                 ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
                    ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
                       ∗ Hrest))))) := by
    intro w; sep_cancel
  refine triple_conseq ge fe f_inflate_table
    (here_field_write ge fe bh bc bo hcenv _val tushort .Mint16unsigned 2
      tushort_byvalue InflateTable.Layout.val_offset (by decide) l _ v2 vnew rhs
      hev)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hperm]; exact hx.2.2⟩)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [hperm]; exact hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- `tmp = work[sym];` against the canonical footprint (the array is already at
    the head). -/
theorem entry_read_work
    (hpw : permOrder pw .Readable = true) (hwb : ∀ j, workF j < 65536)
    (sym : Nat) (hs : sym < nwork) (hn31 : (nwork : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned workO + 2 * (nwork : _root_.Int)
             < 18446744073709551616)
    (v0 v1 v2 : Val) (tmp : Ident) (l : List (Ident × Val))
    (hmemSym : (_sym, .Vint (Integers.Int.repr ((sym : _root_.Int)))) ∈ l)
    (hmemWork : (_work, .Vptr workB workO) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ tmp) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      (.Sset tmp workIdx)
      (.only (LocalSt (envOf bh bc bo)
        ((tmp, .Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int))))
          :: l)
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))) :=
  read_work_triple ge fe bh bc bo pw hpw workB workO nwork workF hwb sym hs
    hn31 hno tmp l _ hmemSym hmemWork hne

/-- `tmp2 = extra[tmp - match];` -/
theorem entry_read_extra
    (hpg : permOrder pg .Readable = true) (hxb : ∀ j, extraF j < 65536)
    (v mtch : Nat) (hge : mtch ≤ v) (hidx : v - mtch < nx)
    (hnx31 : (nx : _root_.Int) < 2147483648) (hv32 : v < 4294967296)
    (v0 v1 v2 : Val) (tmp tmp2 : Ident) (l : List (Ident × Val))
    (hmemArr : (_extra, .Vptr xB Integers.Ptrofs.zero) ∈ l)
    (hmemTmp : (tmp, .Vint (Integers.Int.repr ((v : _root_.Int)))) ∈ l)
    (hmemM : (_match, .Vint (Integers.Int.repr ((mtch : _root_.Int)))) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ tmp2) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      (.Sset tmp2 (gIdx _extra tmp))
      (.only (LocalSt (envOf bh bc bo)
        ((tmp2, .Vint (Integers.Int.repr
            (((extraF (v - mtch) : Nat) : _root_.Int)))) :: l)
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))) := by
  have hperm :
      Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2
      = arrayU16 pg xB 0 nx extraF
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
           ∗ (arrayU16 pg bB 0 nb baseF
              ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
                 ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
                    ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
                       ∗ Hrest))))) := by
    sep_cancel
  refine triple_conseq ge fe f_inflate_table
    (read_global_triple ge fe bh bc bo pg hpg xB nx extraF hxb v mtch hge hidx
      hnx31 hv32 _extra tmp tmp2 l _ hmemArr hmemTmp hmemM hne)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hperm]; exact hx.2.2⟩)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [hperm]; exact hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- `tmp2 = base[tmp - match];` -/
theorem entry_read_base
    (hpg : permOrder pg .Readable = true) (hbb : ∀ j, baseF j < 65536)
    (v mtch : Nat) (hge : mtch ≤ v) (hidx : v - mtch < nb)
    (hnb31 : (nb : _root_.Int) < 2147483648) (hv32 : v < 4294967296)
    (v0 v1 v2 : Val) (tmp tmp2 : Ident) (l : List (Ident × Val))
    (hmemArr : (_base, .Vptr bB Integers.Ptrofs.zero) ∈ l)
    (hmemTmp : (tmp, .Vint (Integers.Int.repr ((v : _root_.Int)))) ∈ l)
    (hmemM : (_match, .Vint (Integers.Int.repr ((mtch : _root_.Int)))) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ tmp2) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      (.Sset tmp2 (gIdx _base tmp))
      (.only (LocalSt (envOf bh bc bo)
        ((tmp2, .Vint (Integers.Int.repr
            (((baseF (v - mtch) : Nat) : _root_.Int)))) :: l)
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))) := by
  have hperm :
      Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2
      = arrayU16 pg bB 0 nb baseF
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
           ∗ (arrayU16 pg xB 0 nx extraF
              ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
                 ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
                    ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
                       ∗ Hrest))))) := by
    sep_cancel
  refine triple_conseq ge fe f_inflate_table
    (read_global_triple ge fe bh bc bo pg hpg bB nb baseF hbb v mtch hge hidx
      hnb31 hv32 _base tmp tmp2 l _ hmemArr hmemTmp hmemM hne)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hperm]; exact hx.2.2⟩)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [hperm]; exact hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! ### The two guards -/

theorem guardA_eval {e : Env} {le : TempEnv} {m : Mem} (v mtch : Nat)
    (hv : v < 4294967295) (hm : mtch < 4294967296)
    (hvT : le.get _t'19 = some (.Vint (Integers.Int.repr ((v : _root_.Int)))))
    (hmT : le.get _match
      = some (.Vint (Integers.Int.repr ((mtch : _root_.Int))))) :
    ∃ w, EvalExpr ge e le m
        (.Ebinop .Olt (.Ebinop .Oadd (.Etempvar _t'19 tushort)
          (.Econst_int (Integers.Int.repr 1) tuint) tuint)
          (.Etempvar _match tuint) tint) w
      ∧ Cop.boolVal w tint m = some (decide (v + 1 < mtch)) := by
  refine ⟨Val.ofBool (Integers.Int.ltu
      (Integers.Int.repr (((v + 1 : Nat) : _root_.Int)))
      (Integers.Int.repr ((mtch : _root_.Int)))), ?_, ?_⟩
  · refine EvalExpr.Ebinop .Olt _ _ _ _ _ _ ?_
      (EvalExpr.Etempvar _match tuint _ hmT) (semBinop_lt_uint _ _ _ _)
    refine EvalExpr.Ebinop .Oadd _ _ _
      (.Vint (Integers.Int.repr ((v : _root_.Int))))
      (.Vint (Integers.Int.repr 1)) _
      (EvalExpr.Etempvar _t'19 tushort _ hvT) (EvalExpr.Econst_int _ _) ?_
    simp only [typeof]
    rw [semBinop_add_ushort_uint,
        show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl, u32_add]
  · simp only [typeof, boolVal_ofBool_int]
    rw [ltu_nat32 (v + 1) mtch (by omega) hm]

theorem guardB_eval {e : Env} {le : TempEnv} {m : Mem} (v mtch : Nat)
    (hv : v < 4294967296) (hm : mtch < 4294967296)
    (hvT : le.get _t'20 = some (.Vint (Integers.Int.repr ((v : _root_.Int)))))
    (hmT : le.get _match
      = some (.Vint (Integers.Int.repr ((mtch : _root_.Int))))) :
    ∃ w, EvalExpr ge e le m
        (.Ebinop .Oge (.Etempvar _t'20 tushort) (.Etempvar _match tuint) tint) w
      ∧ Cop.boolVal w tint m = some (decide (mtch ≤ v)) := by
  refine ⟨Val.ofBool (!Integers.Int.ltu
      (Integers.Int.repr ((v : _root_.Int)))
      (Integers.Int.repr ((mtch : _root_.Int)))), ?_, ?_⟩
  · exact EvalExpr.Ebinop .Oge _ _ _ _ _ _
      (EvalExpr.Etempvar _t'20 tushort _ hvT)
      (EvalExpr.Etempvar _match tuint _ hmT) (semBinop_ge_ushort_uint _ _ _ _)
  · simp only [typeof, boolVal_ofBool_int]
    rw [ltu_nat32 v mtch hv hm]
    by_cases h : mtch ≤ v
    · rw [show decide (v < mtch) = false from by
            rw [decide_eq_false_iff_not]; omega,
          show decide (mtch ≤ v) = true from by
            rw [decide_eq_true_eq]; exact h]
      rfl
    · rw [show decide (v < mtch) = true from by
            rw [decide_eq_true_eq]; omega,
          show decide (mtch ≤ v) = false from by
            rw [decide_eq_false_iff_not]; exact h]
      rfl

end Entry2


/-! ### The branch, assembled

`entryChoose` is the `if / else if / else` of inftrees.c:223-234, with
`entryBitsStmt` (the `here.bits` write) separate because the generated AST
sequences it *outside* the pair `Ssequence (Sset _t'19 …) (Sifthenelse …)`.

The postcondition is deliberately **existential**: after the block `here` holds
*some* entry (`op < 256`, `val < 65536`).  Which one is a
functional-correctness question; the fill loop only needs that an entry is
there. -/

abbrev entryThen : Stmt :=
  .Ssequence
    (hereW _op tuchar (.Ecast (.Econst_int (Integers.Int.repr 0) tint) tuchar))
    (.Ssequence (.Sset _t'25 workIdx)
      (hereW _val tushort (.Etempvar _t'25 tushort)))

abbrev entryElseThen : Stmt :=
  .Ssequence
    (.Ssequence (.Sset _t'23 workIdx)
      (.Ssequence (.Sset _t'24 (gIdx _extra _t'23))
        (hereW _op tuchar (.Ecast (.Etempvar _t'24 tushort) tuchar))))
    (.Ssequence (.Sset _t'21 workIdx)
      (.Ssequence (.Sset _t'22 (gIdx _base _t'21))
        (hereW _val tushort (.Etempvar _t'22 tushort))))

abbrev entryElseElse : Stmt :=
  .Ssequence
    (hereW _op tuchar (.Ecast (.Ebinop .Oadd
      (.Econst_int (Integers.Int.repr 32) tint)
      (.Econst_int (Integers.Int.repr 64) tint) tint) tuchar))
    (hereW _val tushort (.Econst_int (Integers.Int.repr 0) tint))

abbrev entryElse : Stmt :=
  .Ssequence (.Sset _t'20 workIdx)
    (.Sifthenelse
      (.Ebinop .Oge (.Etempvar _t'20 tushort) (.Etempvar _match tuint) tint)
      entryElseThen entryElseElse)

abbrev entryChoose : Stmt :=
  .Ssequence (.Sset _t'19 workIdx)
    (.Sifthenelse (.Ebinop .Olt (.Ebinop .Oadd (.Etempvar _t'19 tushort)
        (.Econst_int (Integers.Int.repr 1) tuint) tuint)
        (.Etempvar _match tuint) tint)
      entryThen entryElse)

abbrev entryBitsStmt : Stmt :=
  hereW _bits tuchar (.Ecast (.Ebinop .Osub (.Etempvar _len tuint)
    (.Etempvar _drop tuint) tuint) tuchar)

section Entry3

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (pw : Permission) (workB : Block) (workO : Integers.Ptrofs)
variable (nwork : Nat) (workF : Nat → Nat)
variable (pg : Permission) (xB bB : Block) (nx nb : Nat)
variable (extraF baseF : Nat → Nat) (Hrest : HProp)
variable (sym mtch : Nat) (l : List (Ident × Val))

/-- After the `if/else if/else`: `here` holds *some* entry.  That existential is
    all the fill loop needs; the exact contents are a functional-correctness
    question, not a safety one. -/
def ChoosePost (v1 : Val) : Sep.Assn := fun e le hp =>
  ∃ op val : Nat, ∃ _ : op < 256, ∃ _ : val < 65536,
    LocalSt (envOf bh bc bo) l
      (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
        (.Vint (Integers.Int.repr ((op : _root_.Int)))) v1
        (.Vint (Integers.Int.repr ((val : _root_.Int))))) e le hp

/-- **The entry's `op`/`val`** (inftrees.c:223-234). -/
theorem entry_choose_triple
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpw : permOrder pw .Readable = true) (hwb : ∀ j, workF j < 65536)
    (hpg : permOrder pg .Readable = true)
    (hxb : ∀ j, extraF j < 65536) (hbb : ∀ j, baseF j < 65536)
    (hs : sym < nwork) (hn31 : (nwork : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned workO + 2 * (nwork : _root_.Int)
             < 18446744073709551616)
    (hnx31 : (nx : _root_.Int) < 2147483648)
    (hnb31 : (nb : _root_.Int) < 2147483648)
    (hm32 : mtch < 4294967296)
    -- **A3**: the `base`/`extra` index is in range whenever the branch is taken
    (hA3x : mtch ≤ workF sym → workF sym - mtch < nx)
    (hA3b : mtch ≤ workF sym → workF sym - mtch < nb)
    (v0 v1 v2 : Val)
    (hmemSym : (_sym, .Vint (Integers.Int.repr ((sym : _root_.Int)))) ∈ l)
    (hmemWork : (_work, .Vptr workB workO) ∈ l)
    (hmemM : (_match, .Vint (Integers.Int.repr ((mtch : _root_.Int)))) ∈ l)
    -- **CODES**: `base`/`extra` are never assigned (the CODES arm of the
    -- `switch` only sets `match`), so they stay `nullv` and these two are NOT
    -- available unconditionally.  They are needed only on the branch that
    -- reads them, and A3-CODES makes that branch unreachable — hence the
    -- guard, which mirrors `hA3x`/`hA3b` above.
    (hmemX : mtch ≤ workF sym → (_extra, .Vptr xB Integers.Ptrofs.zero) ∈ l)
    (hmemB : mtch ≤ workF sym → (_base, .Vptr bB Integers.Ptrofs.zero) ∈ l)
    (hfr : ∀ p ∈ l, p.1 ≠ _t'19 ∧ p.1 ≠ _t'20 ∧ p.1 ≠ _t'21 ∧ p.1 ≠ _t'22
      ∧ p.1 ≠ _t'23 ∧ p.1 ≠ _t'24 ∧ p.1 ≠ _t'25) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      entryChoose
      (.only (ChoosePost bh bc bo pw workB workO nwork workF pg xB bB nx nb
        extraF baseF Hrest l v1)) := by
  have hv32 : workF sym < 65536 := hwb sym
  -- t'19 = work[sym]
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'19, .Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int))))
        :: l)
      (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
        v0 v1 v2)) _ _ _
    (entry_read_work ge fe bh bc bo pw workB workO nwork workF pg xB bB nx nb
      extraF baseF Hrest hpw hwb sym hs hn31 hno v0 v1 v2 _t'19 l hmemSym
      hmemWork (fun p hp => (hfr p hp).1)) ?_
  by_cases hA : workF sym + 1 < mtch
  · -- work[sym] + 1 < match : a literal, `here.val = work[sym]`
    refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => by
        have h := guardA_eval ge (e := envOf bh bc bo) (m := mm) (workF sym)
          mtch (by omega) hm32 (hT'.get List.mem_cons_self)
          (hT'.get (List.mem_cons_of_mem _ hmemM))
        rw [show decide (workF sym + 1 < mtch) = true from by
              rw [decide_eq_true_eq]; exact hA] at h
        exact h) ?_
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'19, .Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int))))
          :: l)
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))) v1 v2)) _ _ _
      (entry_op_write ge fe bh bc bo pw workB workO nwork workF pg xB bB nx nb
        extraF baseF Hrest hcenv v0 v1 v2 _ _ _
        (fun le mm _ => ⟨.Vint (Integers.Int.zero_ext 8
            (Integers.Int.repr 0)), EvalExpr.Ecast _ _ _ _
          (EvalExpr.Econst_int _ _)
          (by simp only [typeof]; exact semCast_int_uchar mm _), by
            simp only [typeof]
            rw [semCast_uchar_uchar,
                show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
                zero_ext8_repr 0 (by omega), zero_ext8_repr 0 (by omega)]⟩)) ?_
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'25, .Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int))))
          :: (_t'19, .Vint (Integers.Int.repr
               (((workF sym : Nat) : _root_.Int)))) :: l)
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))) v1 v2)) _ _ _
      (entry_read_work ge fe bh bc bo pw workB workO nwork workF pg xB bB nx nb
        extraF baseF Hrest hpw hwb sym hs hn31 hno _ v1 v2 _t'25 _
        (List.mem_cons_of_mem _ hmemSym) (List.mem_cons_of_mem _ hmemWork)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _t'19 ≠ _t'25; decide
          · exact (hfr p hp2).2.2.2.2.2.2)) ?_
    refine triple_conseq ge fe f_inflate_table
      (entry_val_write ge fe bh bc bo pw workB workO nwork workF pg xB bB nx nb
        extraF baseF Hrest hcenv _ v1 v2
        (.Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int)))) _ _
        (fun le mm hT' => ⟨.Vint (Integers.Int.repr
            (((workF sym : Nat) : _root_.Int))),
          EvalExpr.Etempvar _t'25 tushort _ (hT'.get List.mem_cons_self), by
            simp only [typeof]
            rw [semCast_ushort_ushort, zero_ext16_repr _ hv32]⟩))
      (fun _ _ _ x => x) (fun e le hp hx => ?_)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
    obtain ⟨henv, hT', hH⟩ := hx
    exact ⟨0, workF sym, by omega, hv32, henv,
      TempsHold_mono (fun p hp => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hp)) hT', hH⟩
  · -- otherwise: t'20 = work[sym], then the inner test
    refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => by
        have h := guardA_eval ge (e := envOf bh bc bo) (m := mm) (workF sym)
          mtch (by omega) hm32 (hT'.get List.mem_cons_self)
          (hT'.get (List.mem_cons_of_mem _ hmemM))
        rw [show decide (workF sym + 1 < mtch) = false from by
              rw [decide_eq_false_iff_not]; exact hA] at h
        exact h) ?_
    refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'20, .Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int))))
          :: (_t'19, .Vint (Integers.Int.repr
               (((workF sym : Nat) : _root_.Int)))) :: l)
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2)) _ _ _
      (entry_read_work ge fe bh bc bo pw workB workO nwork workF pg xB bB nx nb
        extraF baseF Hrest hpw hwb sym hs hn31 hno v0 v1 v2 _t'20 _
        (List.mem_cons_of_mem _ hmemSym) (List.mem_cons_of_mem _ hmemWork)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _t'19 ≠ _t'20; decide
          · exact (hfr p hp2).2.1)) ?_
    by_cases hB : mtch ≤ workF sym
    · -- `here.op = extra[…]; here.val = base[…]` — where A3 is consumed
      refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT' _ _ => by
          have h := guardB_eval ge (e := envOf bh bc bo) (m := mm) (workF sym)
            mtch (by omega) hm32 (hT'.get List.mem_cons_self)
            (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemM)))
          rw [show decide (mtch ≤ workF sym) = true from by
                rw [decide_eq_true_eq]; exact hB] at h
          exact h) ?_
      -- t'23 = work[sym]; t'24 = extra[t'23 - match]; here.op = (uchar)t'24
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'24, .Vint (Integers.Int.repr
              (((extraF (workF sym - mtch) : Nat) : _root_.Int))))
            :: (_t'23, .Vint (Integers.Int.repr
                 (((workF sym : Nat) : _root_.Int))))
            :: (_t'20, .Vint (Integers.Int.repr
                 (((workF sym : Nat) : _root_.Int))))
            :: (_t'19, .Vint (Integers.Int.repr
                 (((workF sym : Nat) : _root_.Int)))) :: l)
          (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF
            Hrest (.Vint (Integers.Int.repr
              (((extraF (workF sym - mtch) % 256 : Nat) : _root_.Int))))
            v1 v2)) _ _ _ ?_ ?_
      · refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_t'23, .Vint (Integers.Int.repr
                (((workF sym : Nat) : _root_.Int))))
              :: (_t'20, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'19, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int)))) :: l)
            (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF
              Hrest v0 v1 v2)) _ _ _
          (entry_read_work ge fe bh bc bo pw workB workO nwork workF pg xB bB
            nx nb extraF baseF Hrest hpw hwb sym hs hn31 hno v0 v1 v2 _t'23 _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemSym))
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemWork))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _t'20 ≠ _t'23; decide
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · show _t'19 ≠ _t'23; decide
              · exact (hfr p hp3).2.2.2.2.1)) ?_
        refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_t'24, .Vint (Integers.Int.repr
                (((extraF (workF sym - mtch) : Nat) : _root_.Int))))
              :: (_t'23, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'20, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'19, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int)))) :: l)
            (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF
              Hrest v0 v1 v2)) _ _ _
          (entry_read_extra ge fe bh bc bo pw workB workO nwork workF pg xB bB
            nx nb extraF baseF Hrest hpg hxb (workF sym) mtch hB (hA3x hB)
            hnx31 (by omega) v0 v1 v2 _t'23 _t'24 _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (hmemX hB))))
            List.mem_cons_self
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hmemM)))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _t'23 ≠ _t'24; decide
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · show _t'20 ≠ _t'24; decide
              rcases List.mem_cons.mp hp3 with rfl | hp4
              · show _t'19 ≠ _t'24; decide
              · exact (hfr p hp4).2.2.2.2.2.1)) ?_
        exact entry_op_write ge fe bh bc bo pw workB workO nwork workF pg xB bB
          nx nb extraF baseF Hrest hcenv v0 v1 v2 _ _ _
          (fun le mm hT' => ⟨.Vint (Integers.Int.zero_ext 8
              (Integers.Int.repr
                (((extraF (workF sym - mtch) : Nat) : _root_.Int)))),
            EvalExpr.Ecast _ _ _ _
              (EvalExpr.Etempvar _t'24 tushort _ (hT'.get List.mem_cons_self))
              (by simp only [typeof]; exact semCast_ushort_uchar mm _), by
              simp only [typeof]
              rw [semCast_uchar_uchar, zero_ext8_mod,
                  zero_ext8_repr _ (by omega)]⟩)
      · -- t'21 = work[sym]; t'22 = base[t'21 - match]; here.val = t'22
        refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_t'21, .Vint (Integers.Int.repr
                (((workF sym : Nat) : _root_.Int))))
              :: (_t'24, .Vint (Integers.Int.repr
                   (((extraF (workF sym - mtch) : Nat) : _root_.Int))))
              :: (_t'23, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'20, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'19, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int)))) :: l)
            (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF
              Hrest (.Vint (Integers.Int.repr
                (((extraF (workF sym - mtch) % 256 : Nat) : _root_.Int))))
              v1 v2)) _ _ _
          (entry_read_work ge fe bh bc bo pw workB workO nwork workF pg xB bB
            nx nb extraF baseF Hrest hpw hwb sym hs hn31 hno _ v1 v2 _t'21 _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemSym))))
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemWork))))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _t'24 ≠ _t'21; decide
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · show _t'23 ≠ _t'21; decide
              rcases List.mem_cons.mp hp3 with rfl | hp4
              · show _t'20 ≠ _t'21; decide
              rcases List.mem_cons.mp hp4 with rfl | hp5
              · show _t'19 ≠ _t'21; decide
              · exact (hfr p hp5).2.2.1)) ?_
        refine triple_seq_fwd ge fe f_inflate_table _
          (LocalSt (envOf bh bc bo)
            ((_t'22, .Vint (Integers.Int.repr
                (((baseF (workF sym - mtch) : Nat) : _root_.Int))))
              :: (_t'21, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'24, .Vint (Integers.Int.repr
                   (((extraF (workF sym - mtch) : Nat) : _root_.Int))))
              :: (_t'23, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'20, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int))))
              :: (_t'19, .Vint (Integers.Int.repr
                   (((workF sym : Nat) : _root_.Int)))) :: l)
            (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF
              Hrest (.Vint (Integers.Int.repr
                (((extraF (workF sym - mtch) % 256 : Nat) : _root_.Int))))
              v1 v2)) _ _ _
          (entry_read_base ge fe bh bc bo pw workB workO nwork workF pg xB bB
            nx nb extraF baseF Hrest hpg hbb (workF sym) mtch hB (hA3b hB)
            hnb31 (by omega) _ v1 v2 _t'21 _t'22 _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (hmemB hB))))))
            List.mem_cons_self
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hmemM)))))
            (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp2
              · show _t'21 ≠ _t'22; decide
              rcases List.mem_cons.mp hp2 with rfl | hp3
              · show _t'24 ≠ _t'22; decide
              rcases List.mem_cons.mp hp3 with rfl | hp4
              · show _t'23 ≠ _t'22; decide
              rcases List.mem_cons.mp hp4 with rfl | hp5
              · show _t'20 ≠ _t'22; decide
              rcases List.mem_cons.mp hp5 with rfl | hp6
              · show _t'19 ≠ _t'22; decide
              · exact (hfr p hp6).2.2.2.1)) ?_
        refine triple_conseq ge fe f_inflate_table
          (entry_val_write ge fe bh bc bo pw workB workO nwork workF pg xB
            bB nx nb extraF baseF Hrest hcenv _ v1 v2
            (.Vint (Integers.Int.repr
              (((baseF (workF sym - mtch) : Nat) : _root_.Int)))) _ _
            (fun le mm hT' => ⟨.Vint (Integers.Int.repr
                (((baseF (workF sym - mtch) : Nat) : _root_.Int))),
              EvalExpr.Etempvar _t'22 tushort _ (hT'.get List.mem_cons_self), by
                simp only [typeof]
                rw [semCast_ushort_ushort, zero_ext16_repr _ (hbb _)]⟩))
          (fun _ _ _ x => x) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
          (fun _ _ hx => hx.elim)
        obtain ⟨henv, hT', hH⟩ := hx
        exact ⟨extraF (workF sym - mtch) % 256, baseF (workF sym - mtch),
          by omega, hbb _, henv,
          TempsHold_mono (fun p hp => List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hp)))))) hT', hH⟩
    · -- end of block: `here.op = 96; here.val = 0;`
      refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => by
          have h := guardB_eval ge (e := envOf bh bc bo) (m := mm) (workF sym)
            mtch (by omega) hm32 (hT'.get List.mem_cons_self)
            (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemM)))
          rw [show decide (mtch ≤ workF sym) = false from by
                rw [decide_eq_false_iff_not]; exact hB] at h
          exact h) ?_
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'20, .Vint (Integers.Int.repr (((workF sym : Nat) : _root_.Int))))
            :: (_t'19, .Vint (Integers.Int.repr
                 (((workF sym : Nat) : _root_.Int)))) :: l)
          (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF
            Hrest (.Vint (Integers.Int.repr (((96 : Nat) : _root_.Int))))
            v1 v2)) _ _ _
        (entry_op_write ge fe bh bc bo pw workB workO nwork workF pg xB bB nx
          nb extraF baseF Hrest hcenv v0 v1 v2 _ _ _
          (fun le mm _ => ⟨.Vint (Integers.Int.zero_ext 8
              (Integers.Int.add (Integers.Int.repr 32)
                (Integers.Int.repr 64))),
            EvalExpr.Ecast _ _ _ _
              (EvalExpr.Ebinop .Oadd _ _ _ (.Vint (Integers.Int.repr 32))
                (.Vint (Integers.Int.repr 64)) _ (EvalExpr.Econst_int _ _)
                (EvalExpr.Econst_int _ _) (semBinop_add_int_int _ _ _ _))
              (by simp only [typeof]; exact semCast_int_uchar mm _), by
              simp only [typeof]
              rw [semCast_uchar_uchar,
                  show (32 : _root_.Int) = ((32 : Nat) : _root_.Int) from rfl,
                  show (64 : _root_.Int) = ((64 : Nat) : _root_.Int) from rfl,
                  u32_add, zero_ext8_repr 96 (by omega),
                  zero_ext8_repr 96 (by omega)]⟩)) ?_
      refine triple_conseq ge fe f_inflate_table
        (entry_val_write ge fe bh bc bo pw workB workO nwork workF pg xB bB nx
          nb extraF baseF Hrest hcenv _ v1 v2
          (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))) _ _
          (fun le mm _ => ⟨.Vint (Integers.Int.repr 0),
            EvalExpr.Econst_int _ _, by
              simp only [typeof]
              rw [semCast_int_ushort,
                  show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
                  zero_ext16_repr 0 (by omega)]⟩))
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      obtain ⟨henv, hT', hH⟩ := hx
      exact ⟨96, 0, by omega, by omega, henv,
        TempsHold_mono (fun p hp => List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hp)) hT', hH⟩

/-- `here.bits = (unsigned char)(len - drop);` -/
theorem entry_bits_triple
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (len drop : Nat) (hdl : drop ≤ len) (hl32 : len < 4294967296)
    (v0 v1 v2 : Val)
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ l)
    (hmemDrop : (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) ∈ l) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 v1 v2))
      entryBitsStmt
      (.only (LocalSt (envOf bh bc bo) l
        (Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF Hrest
          v0 (.Vint (Integers.Int.repr
            ((((len - drop) % 256 : Nat) : _root_.Int)))) v2))) :=
  entry_bits_write ge fe bh bc bo pw workB workO nwork workF pg xB bB nx nb
    extraF baseF Hrest hcenv v0 v1 v2 _ _ l
    (fun le mm hT' => ⟨.Vint (Integers.Int.zero_ext 8
        (Integers.Int.repr ((((len - drop : Nat)) : _root_.Int)))),
      EvalExpr.Ecast _ _ _ _
        (EvalExpr.Ebinop .Osub _ _ _
          (.Vint (Integers.Int.repr ((len : _root_.Int))))
          (.Vint (Integers.Int.repr ((drop : _root_.Int)))) _
          (EvalExpr.Etempvar _len tuint _ (hT'.get hmemLen))
          (EvalExpr.Etempvar _drop tuint _ (hT'.get hmemDrop))
          (by simp only [typeof]
              rw [semBinop_sub_uint, u32_sub_nat len drop hdl hl32]))
        (by simp only [typeof]; exact semCast_uint_uchar mm _), by
        simp only [typeof]
        rw [semCast_uchar_uchar, zero_ext8_mod, zero_ext8_repr _ (by omega)]⟩)

end Entry3


/-! ## §24 The symbol advance (inftrees.c:257-262; AST 1199-1258)

        sym++;
        if (--(count[len]) == 0) {
            if (len == max) break;
            len = lens[work[sym]];
        }

Three memory accesses: `count[len]` read *and* written (the decrement, which
clightgen splits into `_t'18` / `_t'7` / store), and — only when the length is
exhausted and the loop does not end — `work[sym]` and `lens[work[sym]]`.

The `break` here is **the main loop's only exit**, so this chunk's triple has a
real `brk` postcondition (`AdvBrk`, which also records `len = max`).

Two obligations are left to the main loop, and both are *conditional on the deep
path being taken* — `hsymlt` and `hlenslt`.  Neither is checked by the C: after
`sym++` the index is used again, and `work[sym]` is used as an index into
`lens`.  Stating them as implications keeps the other paths obligation-free.

`len'` in the normal postcondition is existential with only `len' ≤ 15`
recorded, which is what the next iteration's `count[len]` needs; that bound
comes from A2 (`hlens15`). -/

theorem semBinop_sub_ushort_int (cenv : CompositeEnv) (m : Mem)
    (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Osub (.Vint x) tushort (.Vint c) tint m
      = some (.Vint (Integers.Int.sub x c)) := rfl

theorem semBinop_eq_ushort_int (cenv : CompositeEnv) (m : Mem)
    (x c : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tushort (.Vint c) tint m
      = some (Val.ofBool (Integers.Int.eq x c)) := rfl

theorem semBinop_eq_uint_uint (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tuint (.Vint y) tuint m
      = some (Val.ofBool (Integers.Int.eq x y)) := rfl

abbrev lensIdx : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _lens (tptr tushort))
    (.Etempvar _t'17 tushort) (tptr tushort)) tushort

abbrev nextLenStmt : Stmt :=
  .Ssequence
    (.Sifthenelse (.Ebinop .Oeq (.Etempvar _len tuint) (.Etempvar _max tuint)
      tint) .Sbreak .Sskip)
    (.Ssequence (.Sset _t'17 workIdx) (.Sset _len lensIdx))

abbrev advIfStmt : Stmt :=
  .Sifthenelse (.Ebinop .Oeq (.Etempvar _t'7 tushort)
    (.Econst_int (Integers.Int.repr 0) tint) tint) nextLenStmt .Sskip

abbrev symIncrStmt : Stmt :=
  .Sset _sym (.Ebinop .Oadd (.Etempvar _sym tuint)
    (.Econst_int (Integers.Int.repr 1) tint) tuint)

abbrev countIdx : Expr :=
  .Ederef (.Ebinop .Oadd (.Evar _count (tarray tushort 16))
    (.Etempvar _len tuint) (tptr tushort)) tushort

abbrev countDecStmt : Stmt :=
  .Ssequence
    (.Ssequence (.Sset _t'18 countIdx)
      (.Sset _t'7 (.Ecast (.Ebinop .Osub (.Etempvar _t'18 tushort)
        (.Econst_int (Integers.Int.repr 1) tint) tint) tushort)))
    (.Sassign countIdx (.Etempvar _t'7 tushort))

section Adv

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (pw : Permission) (workB : Block) (workO : Integers.Ptrofs)
variable (nwork : Nat) (workF : Nat → Nat)
variable (pl : Permission) (lensB : Block) (lensO : Integers.Ptrofs)
variable (ncodes : Nat) (lensF : Nat → Nat) (Hrest : HProp)

/-- The symbol-advance footprint: `count` (read and written), then `work` and
    `lens` (read on the "next length" path). -/
abbrev Hadv (cntF : Nat → Nat) : HProp :=
  arrayU16 .Freeable bc 0 16 cntF
  ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
     ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
        ∗ Hrest))

/-- `--count[len];` in clightgen's three-statement form: read into `_t'18`,
    compute `_t'7`, store back. -/
theorem count_dec_triple
    (cntF : Nat → Nat) (hcb : ∀ j, cntF j < 65536)
    (len : Nat) (hlen15 : len ≤ 15) (hcl : 1 ≤ cntF len)
    (l : List (Ident × Val))
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ l)
    (hfr : ∀ p ∈ l, p.1 ≠ _t'18 ∧ p.1 ≠ _t'7) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
          cntF))
      countDecStmt
      (.only (LocalSt (envOf bh bc bo)
        ((_t'7, .Vint (Integers.Int.repr
            (((cntF len - 1 : Nat) : _root_.Int))))
          :: (_t'18, .Vint (Integers.Int.repr
               (((cntF len : Nat) : _root_.Int)))) :: l)
        (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
          (fun j => if j = len then cntF len - 1 else cntF j)))) := by
  have hi16 : len < 16 := by omega
  have hcl' : cntF len - 1 < 65536 := by have := hcb len; omega
  have haddr0 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
        (Integers.Int.repr ((len : _root_.Int))))
      = Integers.Ptrofs.unsigned Integers.Ptrofs.zero
          + 2 * ((len : Nat) : _root_.Int) :=
    cnt_addr0 ge .Unsigned len hlen15
  have haddr : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
        (Integers.Int.repr ((len : _root_.Int))))
      = 2 * ((len : Nat) : _root_.Int) := by
    rw [haddr0, ptrofs_unsigned_zero]
    show (0 : _root_.Int) + 2 * ((len : Nat) : _root_.Int)
          = 2 * ((len : Nat) : _root_.Int)
    omega
  -- _t'18 = count[len]
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_t'7, .Vint (Integers.Int.repr (((cntF len - 1 : Nat) : _root_.Int))))
        :: (_t'18, .Vint (Integers.Int.repr
             (((cntF len : Nat) : _root_.Int)))) :: l)
      (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
        cntF)) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge fe f_inflate_table _
      (LocalSt (envOf bh bc bo)
        ((_t'18, .Vint (Integers.Int.repr (((cntF len : Nat) : _root_.Int))))
          :: l)
        (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
          cntF)) _ _ _ ?_ ?_
    · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ l _
        _t'18 _ _ (fun p hp => hp) (fun p hp => (hfr p hp).1)
        (fun le mm hp hT' hH hag => ?_)
      obtain ⟨h1, h2, hd12, heq, harr, hrest⟩ := hH
      subst heq
      exact eval_index_u16 (by decide) harr (Heap.Agrees_union_left hag) hi16
        hcb (eval_count_base bh bc bo)
        (EvalExpr.Etempvar _len tuint _ (hT'.get hmemLen)) rfl haddr0
    · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
        _t'7 _ _ (fun p hp => hp)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp2
          · show _t'18 ≠ _t'7; decide
          · exact (hfr p hp2).2)
        (fun le mm hp hT' _ _ => ?_)
      refine EvalExpr.Ecast _ _ _ _
        (EvalExpr.Ebinop .Osub _ _ _
          (.Vint (Integers.Int.repr (((cntF len : Nat) : _root_.Int))))
          (.Vint (Integers.Int.repr 1)) _
          (EvalExpr.Etempvar _t'18 tushort _ (hT'.get List.mem_cons_self))
          (EvalExpr.Econst_int _ _)
          (by simp only [typeof]; exact semBinop_sub_ushort_int _ _ _ _)) ?_
      simp only [typeof]
      rw [semCast_int_ushort,
          show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl,
          u32_sub_nat (cntF len) 1 hcl (by have := hcb len; omega),
          zero_ext16_repr _ hcl']
  -- count[len] = _t'7
  · have hsplit := arrayU16_split .Freeable bc 0 16 cntF len hi16
    rw [show (0 : _root_.Int) + 2 * ((len : Nat) : _root_.Int)
          = 2 * ((len : Nat) : _root_.Int) from by omega] at hsplit
    have hupd := arrayU16_update .Freeable bc 0 16 cntF len (cntF len - 1) hi16
    rw [show (0 : _root_.Int) + 2 * ((len : Nat) : _root_.Int)
          = 2 * ((len : Nat) : _root_.Int) from by omega] at hupd
    refine triple_assign ge fe f_inflate_table _ _ _ _ .Mint16unsigned .Freeable
      bc (idxOfs ge.genv_cenv tushort .Unsigned Integers.Ptrofs.zero
        (Integers.Int.repr ((len : _root_.Int))))
      (by decide) (by simpa only [typeof] using tushort_byvalue) ?_
    intro e le hp m hP hag
    obtain ⟨henv, hT', hH⟩ := hP
    subst henv
    rw [show Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF
              Hrest cntF
          = mapsto .Mint16unsigned .Freeable bc
              (2 * ((len : Nat) : _root_.Int))
              (.Vint (Integers.Int.repr (((cntF len : Nat) : _root_.Int))))
            ∗ (arrayOfRest (u16elt .Freeable bc cntF) 2 0 16 len
               ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
                  ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes
                       lensF ∗ Hrest)))
        from by rw [show Hadv bc pw workB workO nwork workF pl lensB lensO
                          ncodes lensF Hrest cntF
                      = arrayU16 .Freeable bc 0 16 cntF
                        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO)
                             nwork workF
                           ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO)
                                ncodes lensF ∗ Hrest)) from rfl,
                  hsplit]
                sep_cancel] at hH
    obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := hH
    refine ⟨.Vint (Integers.Int.repr (((cntF len : Nat) : _root_.Int))),
            .Vint (Integers.Int.repr (((cntF len - 1 : Nat) : _root_.Int))),
            h1, h2, hd12, heq, ?_, ?_, ?_, ?_⟩
    · rw [haddr]; exact hm1
    · exact eval_index_lvalue (eval_count_base bh bc bo)
        (EvalExpr.Etempvar _len tuint _
          (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemLen))))
        rfl
    · refine ⟨.Vint (Integers.Int.repr (((cntF len - 1 : Nat) : _root_.Int))),
        EvalExpr.Etempvar _t'7 tushort _ (hT'.get List.mem_cons_self), ?_⟩
      simp only [typeof]
      rw [semCast_ushort_ushort, zero_ext16_repr _ hcl']
    · intro h1' hm1' hd1'
      refine ⟨rfl, hT', ?_⟩
      rw [show Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF
                Hrest (fun j => if j = len then cntF len - 1 else cntF j)
            = mapsto .Mint16unsigned .Freeable bc
                (2 * ((len : Nat) : _root_.Int))
                (.Vint (Integers.Int.repr
                  (((cntF len - 1 : Nat) : _root_.Int))))
              ∗ (arrayOfRest (u16elt .Freeable bc cntF) 2 0 16 len
                 ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork
                      workF
                    ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes
                         lensF ∗ Hrest)))
          from by rw [show Hadv bc pw workB workO nwork workF pl lensB lensO
                            ncodes lensF Hrest
                            (fun j => if j = len then cntF len - 1 else cntF j)
                        = arrayU16 .Freeable bc 0 16
                            (fun j => if j = len then cntF len - 1 else cntF j)
                          ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO)
                               nwork workF
                             ∗ (arrayU16 pl lensB
                                  (Integers.Ptrofs.unsigned lensO) ncodes lensF
                                ∗ Hrest)) from rfl,
                    hupd]
                  sep_cancel]
      rw [haddr] at hm1'
      exact ⟨h1', h2, hd1', rfl, hm1', hrest⟩

/-- `sym++;` -/
theorem sym_incr_triple (sym : Nat) (hs32 : sym < 4294967295)
    (H : HProp) (T : List (Ident × Val)) (hTsym : ∀ p ∈ T, p.1 ≠ _sym) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_sym, .Vint (Integers.Int.repr ((sym : _root_.Int)))) :: T) H)
      symIncrStmt
      (.only (LocalSt (envOf bh bc bo)
        ((_sym, .Vint (Integers.Int.repr (((sym + 1 : Nat) : _root_.Int))))
          :: T) H)) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _sym _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTsym (fun le mm hp hT' _ _ => ?_)
  refine EvalExpr.Ebinop .Oadd _ _ _
    (.Vint (Integers.Int.repr ((sym : _root_.Int))))
    (.Vint (Integers.Int.repr 1)) _
    (EvalExpr.Etempvar _sym tuint _ (hT'.get List.mem_cons_self))
    (EvalExpr.Econst_int _ _) ?_
  simp only [typeof]
  rw [semBinop_add_uint_int]
  show some (Val.Vint (Integers.Int.add
            (Integers.Int.repr ((sym : _root_.Int)))
            (Integers.Int.repr 1))) = _
  rw [show (1 : _root_.Int) = ((1 : Nat) : _root_.Int) from rfl, u32_add]

/-- After `--count[len]`: either the loop exits, or `len` moves to the next
    symbol's length.  `len'` is existential — safety needs only `len' ≤ 15`. -/
def AdvPost (cntF : Nat → Nat) (len max sym : Nat) (T : List (Ident × Val)) :
    Sep.Assn := fun e le hp =>
  ∃ len' : Nat, ∃ _ : len' ≤ 15, ∃ _ : len' ≤ max,
  ∃ _ : (len' = len ∧ 2 ≤ cntF len)
        ∨ (cntF len = 1 ∧ len ≠ max ∧ len' = lensF (workF sym)),
    LocalSt (envOf bh bc bo)
      ((_len, .Vint (Integers.Int.repr ((len' : _root_.Int)))) :: T)
      (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
        (fun j => if j = len then cntF len - 1 else cntF j)) e le hp

/-- The `break` exit — the only way out of the main loop. -/
def AdvBrk (cntF : Nat → Nat) (len max : Nat) (T : List (Ident × Val)) :
    Sep.Assn := fun e le hp =>
  ∃ _ : len = max, ∃ _ : cntF len = 1,
    LocalSt (envOf bh bc bo)
      ((_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) :: T)
      (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
        (fun j => if j = len then cntF len - 1 else cntF j)) e le hp

/-- `if (--count[len] == 0) { if (len == max) break; len = lens[work[sym]]; }`
    — the tail of the symbol advance.

    Two obligations, both **conditional on the deep path being taken**, and both
    for the main loop to supply: `sym` is still a live index into `work`, and
    `work[sym]` is a live index into `lens`.  Neither is checked by the C. -/
theorem adv_if_triple
    (cntF : Nat → Nat) (len max sym : Nat)
    (hlen15 : len ≤ 15) (hcb : ∀ j, cntF j < 65536) (hcl : 1 ≤ cntF len)
    (hmax15 : max ≤ 15)
    (hwb : ∀ j, workF j < 65536) (hlb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ j, lensF j ≤ 15) (hlensmax : ∀ j, lensF j ≤ max)
    (hlenmax : len ≤ max)
    (hn31 : (nwork : _root_.Int) < 2147483648)
    (hnow : Integers.Ptrofs.unsigned workO + 2 * (nwork : _root_.Int)
             < 18446744073709551616)
    (hc31 : (ncodes : _root_.Int) < 2147483648)
    (hnol : Integers.Ptrofs.unsigned lensO + 2 * (ncodes : _root_.Int)
             < 18446744073709551616)
    (hpw : permOrder pw .Readable = true) (hpl : permOrder pl .Readable = true)
    (hsymlt : cntF len = 1 → len ≠ max → sym < nwork)
    (hlenslt : cntF len = 1 → len ≠ max → workF sym < ncodes)
    (T : List (Ident × Val))
    (hmemMax : (_max, .Vint (Integers.Int.repr ((max : _root_.Int)))) ∈ T)
    (hmemSym : (_sym, .Vint (Integers.Int.repr ((sym : _root_.Int)))) ∈ T)
    (hmemWork : (_work, .Vptr workB workO) ∈ T)
    (hmemLens : (_lens, .Vptr lensB lensO) ∈ T)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (hfr : ∀ p ∈ T, p.1 ≠ _t'7 ∧ p.1 ≠ _t'17 ∧ p.1 ≠ _t'18)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_t'7, .Vint (Integers.Int.repr (((cntF len - 1 : Nat) : _root_.Int))))
          :: (_t'18, .Vint (Integers.Int.repr
               (((cntF len : Nat) : _root_.Int))))
          :: (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) :: T)
        (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
          (fun j => if j = len then cntF len - 1 else cntF j)))
      advIfStmt
      { normal := AdvPost bh bc bo pw workB workO nwork workF pl lensB lensO
          ncodes lensF Hrest cntF len max sym T,
        brk := AdvBrk bh bc bo pw workB workO nwork workF pl lensB lensO ncodes
          lensF Hrest cntF len max T,
        cont := R.cont, ret := R.ret, goto := R.goto } := by
  have hcl' : cntF len - 1 < 65536 := by have := hcb len; omega
  have hguard : ∀ (le : TempEnv) (mm : Mem),
      TempsHold ((_t'7, .Vint (Integers.Int.repr
          (((cntF len - 1 : Nat) : _root_.Int))))
        :: (_t'18, .Vint (Integers.Int.repr
             (((cntF len : Nat) : _root_.Int))))
        :: (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) :: T) le →
      ∃ w, EvalExpr ge (envOf bh bc bo) le mm
          (.Ebinop .Oeq (.Etempvar _t'7 tushort)
            (.Econst_int (Integers.Int.repr 0) tint) tint) w
        ∧ Cop.boolVal w tint mm = some (decide (cntF len - 1 = 0)) := by
    intro le mm hT'
    refine ⟨Val.ofBool (Integers.Int.eq
        (Integers.Int.repr (((cntF len - 1 : Nat) : _root_.Int)))
        (Integers.Int.repr 0)), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
        (EvalExpr.Etempvar _t'7 tushort _ (hT'.get List.mem_cons_self))
        (EvalExpr.Econst_int _ _) (semBinop_eq_ushort_int _ _ _ _)
    · simp only [boolVal_ofBool_int]
      rw [show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
          eq_nat32 _ 0 (by omega) (by omega)]
  by_cases hz : cntF len - 1 = 0
  · -- the length is exhausted
    refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => by
        have h := hguard le mm hT'
        rw [show decide (cntF len - 1 = 0) = true from by
              rw [decide_eq_true_eq]; exact hz] at h
        exact h) ?_
    have hc1 : cntF len = 1 := by omega
    by_cases hm : len = max
    · -- len == max : leave the loop
      refine triple_seq ge fe f_inflate_table _ Assn.no _ _ _ ?_
        (triple_vacuous _ _ _ _ _)
      refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · refine ⟨Val.ofBool (Integers.Int.eq
            (Integers.Int.repr ((len : _root_.Int)))
            (Integers.Int.repr ((max : _root_.Int)))), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
            (EvalExpr.Etempvar _len tuint _
              (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                List.mem_cons_self))))
            (EvalExpr.Etempvar _max tuint _
              (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hmemMax)))))
            (semBinop_eq_uint_uint _ _ _ _)
        · simp only [typeof, boolVal_ofBool_int]
          rw [eq_nat32 len max (by omega) (by omega),
              show decide (len = max) = true from by
                rw [decide_eq_true_eq]; exact hm]
      · refine triple_conseq ge fe f_inflate_table
          (triple_break ge fe f_inflate_table _)
          (fun _ _ _ x => x) (fun _ _ _ hx => hx.elim) (fun e le hp hx => ?_)
          (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
        obtain ⟨henv, hT', hH⟩ := hx
        exact ⟨hm, hc1, henv, TempsHold_mono (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                List.mem_cons_self)
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hp2))) hT', hH⟩
    · -- len != max : read the next symbol's length
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'7, .Vint (Integers.Int.repr
              (((cntF len - 1 : Nat) : _root_.Int))))
            :: (_t'18, .Vint (Integers.Int.repr
                 (((cntF len : Nat) : _root_.Int))))
            :: (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) :: T)
          (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
            (fun j => if j = len then cntF len - 1 else cntF j))) _ _ _ ?_ ?_
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
          (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _)
        refine ⟨Val.ofBool (Integers.Int.eq
            (Integers.Int.repr ((len : _root_.Int)))
            (Integers.Int.repr ((max : _root_.Int)))), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
            (EvalExpr.Etempvar _len tuint _
              (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                List.mem_cons_self))))
            (EvalExpr.Etempvar _max tuint _
              (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hmemMax)))))
            (semBinop_eq_uint_uint _ _ _ _)
        · simp only [typeof, boolVal_ofBool_int]
          rw [eq_nat32 len max (by omega) (by omega),
              show decide (len = max) = false from by
                rw [decide_eq_false_iff_not]; exact hm]
      -- _t'17 = work[sym]
      refine triple_seq_fwd ge fe f_inflate_table _
        (LocalSt (envOf bh bc bo)
          ((_t'17, .Vint (Integers.Int.repr
              (((workF sym : Nat) : _root_.Int))))
            :: (_t'7, .Vint (Integers.Int.repr
                 (((cntF len - 1 : Nat) : _root_.Int))))
            :: (_t'18, .Vint (Integers.Int.repr
                 (((cntF len : Nat) : _root_.Int))))
            :: (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) :: T)
          (Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF Hrest
            (fun j => if j = len then cntF len - 1 else cntF j))) _ _ _ ?_ ?_
      · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ _ _
          _t'17 _ _ (fun p hp => hp)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _t'7 ≠ _t'17; decide
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · show _t'18 ≠ _t'17; decide
            rcases List.mem_cons.mp hp3 with rfl | hp4
            · show _len ≠ _t'17; decide
            · exact (hfr p hp4).2.1)
          (fun le mm hp hT' hH hag => ?_)
        obtain ⟨hC, hR, hd1, heq1, harrC, hR'⟩ := hH
        subst heq1
        obtain ⟨hW, hR2, hd2, heq2, harrW, hR2'⟩ := hR'
        subst heq2
        exact eval_index_u16 hpw harrW
          (Heap.Agrees_union_left (Heap.Agrees_union_right hd1 hag))
          (hsymlt hc1 hm) hwb
          (EvalExpr.Etempvar _work _ _
            (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hmemWork)))))
          (EvalExpr.Etempvar _sym tuint _
            (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hmemSym)))))
          rfl
          (u16Ofs_unsigned ge.genv_cenv .Unsigned workO sym (by omega)
            (no_wrap_mono workO nwork sym hnow (by have := hsymlt hc1 hm; omega)))
      -- len = lens[t'17]
      refine triple_conseq ge fe f_inflate_table
        (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
          ((_t'17, .Vint (Integers.Int.repr
              (((workF sym : Nat) : _root_.Int))))
            :: (_t'7, .Vint (Integers.Int.repr
                 (((cntF len - 1 : Nat) : _root_.Int))))
            :: (_t'18, .Vint (Integers.Int.repr
                 (((cntF len : Nat) : _root_.Int)))) :: T) _ _len _
          (.Vint (Integers.Int.repr
            (((lensF (workF sym) : Nat) : _root_.Int))))
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact List.mem_cons_self
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            rcases List.mem_cons.mp hp3 with rfl | hp4
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                List.mem_cons_self)
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))))
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · show _t'17 ≠ _len; decide
            rcases List.mem_cons.mp hp2 with rfl | hp3
            · show _t'7 ≠ _len; decide
            rcases List.mem_cons.mp hp3 with rfl | hp4
            · show _t'18 ≠ _len; decide
            · exact hTlen p hp4)
          (fun le mm hp hT' hH hag => ?_))
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      · obtain ⟨hC, hR, hd1, heq1, harrC, hR'⟩ := hH
        subst heq1
        obtain ⟨hW, hR2, hd2, heq2, harrW, hR2'⟩ := hR'
        subst heq2
        obtain ⟨hL, hR3, hd3, heq3, harrL, hR3'⟩ := hR2'
        subst heq3
        exact eval_index_u16 hpl harrL
          (Heap.Agrees_union_left
            (Heap.Agrees_union_right hd2 (Heap.Agrees_union_right hd1 hag)))
          (hlenslt hc1 hm) hlb
          (EvalExpr.Etempvar _lens _ _
            (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemLens))))))
          (EvalExpr.Etempvar _t'17 tushort _ (hT'.get List.mem_cons_self))
          rfl
          (u16Ofs_unsigned ge.genv_cenv .Signed lensO (workF sym) (by omega)
            (no_wrap_mono lensO ncodes (workF sym) hnol
              (by have := hlenslt hc1 hm; omega)))
      · obtain ⟨henv, hT', hH⟩ := hx
        exact ⟨lensF (workF sym), hlens15 _, hlensmax _, Or.inr ⟨hc1, hm, rfl⟩,
          henv,
          TempsHold_mono (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp2)))) hT',
          hH⟩
  · -- the length is not exhausted: nothing happens
    refine triple_conseq ge fe f_inflate_table
      (triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => by
          have h := hguard le mm hT'
          rw [show decide (cntF len - 1 = 0) = false from by
                rw [decide_eq_false_iff_not]; exact hz] at h
          exact h) (triple_skip ge fe f_inflate_table _))
      (fun _ _ _ x => x) (fun e le hp hx => ?_)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
    obtain ⟨henv, hT', hH⟩ := hx
    exact ⟨len, hlen15, hlenmax, Or.inl ⟨rfl, by omega⟩, henv,
      TempsHold_mono (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            List.mem_cons_self)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hp2))) hT', hH⟩

end Adv


/-! ## §25 The last two statement groups of the main loop
    (inftrees.c:236-238 and 265; AST 1110-1127 and 1261-1285)

        incr = 1U << (len - drop);
        fill = 1U << curr;
        min  = fill;
        …
        if (len > root && (huff & mask) != low) { … }

The three `fill` setup statements carry two more of the same shift obligation
as §22: `Cop`'s shift is `None` at a count of 32 or more, so `len - drop < 32`
and `curr < 32` are genuine.

They are proved **both** ways.  `fill_setup_triple` bundles them as
`Ssequence A (Ssequence B C)`, which is convenient but is *not* how the
generated AST associates them — there the tail is `Ssequence C rest`, so the
bundle cannot be chained without re-associating `Ssequence`.  The main loop
therefore uses the three separate statement lemmas below
(`incr_set_triple`, `fill_set_triple`, `min_set_triple`), each of which is a
subterm of the AST; the bundle is kept only as a readable statement of what the
group does.

`t10_set_triple` is the short-circuit `&&`, which clightgen normalises into a
nested `if` writing `_t'10` — the same shape as the ENOUGH check's `_t'5`/`_t'6`
chain.  The tracked result is `if root < len ∧ huff % 2^root ≠ low then 1 else
0`, so the enclosing `if (t'10)` is decided by that `Nat` and needs no further
bit reasoning.  (`huff & mask` is `huff % 2^root` because `mask = 2^root - 1` —
`Nat.and_two_pow_sub_one_eq_mod`, as in §22's `low_set_triple`.)

**With these, every statement of `inflate_table` has a triple.**  The main
loop's invariant is §26; the chaining is InflateTableChain.lean. -/

theorem semBinop_ne_uint_uint (cenv : CompositeEnv) (m : Mem)
    (x y : Integers.Int) :
    Cop.semBinaryOperation cenv .One (.Vint x) tuint (.Vint y) tuint m
      = some (Val.ofBool (!Integers.Int.eq x y)) := rfl

theorem semCast_int_bool (m : Mem) (x : Integers.Int) :
    Cop.semCast (.Vint x) tint tbool m
      = some (.Vint (if Integers.Int.eq x Integers.Int.zero
                     then Integers.Int.zero else Integers.Int.one)) := rfl

abbrev fillSetup : Stmt :=
  .Ssequence
    (.Sset _incr (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
      (.Ebinop .Osub (.Etempvar _len tuint) (.Etempvar _drop tuint) tuint)
      tuint))
    (.Ssequence
      (.Sset _fill (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
        (.Etempvar _curr tuint) tuint))
      (.Sset _min (.Etempvar _fill tuint)))

abbrev t10Stmt : Stmt :=
  .Sifthenelse (.Ebinop .Ogt (.Etempvar _len tuint) (.Etempvar _root tuint) tint)
    (.Sset _t'10 (.Ecast (.Ebinop .One
      (.Ebinop .Oand (.Etempvar _huff tuint) (.Etempvar _mask tuint) tuint)
      (.Etempvar _low tuint) tint) tbool))
    (.Sset _t'10 (.Econst_int (Integers.Int.repr 0) tint))

section C

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (H : HProp) (T : List (Ident × Val))

/-- `incr = 1U << (len - drop); fill = 1U << curr; min = fill;`

    Both shifts need their count below 32 — `Cop`'s shift is `None` at 32 or
    more, i.e. stuck.  `len - drop ≤ 15` and `curr ≤ 15` supply it. -/
theorem fill_setup_triple
    (len drop curr : Nat) (hdl : drop ≤ len) (hl15 : len ≤ 15)
    (hc32 : curr < 32)
    (oi of om : Val)
    (hTincr : ∀ p ∈ T, p.1 ≠ _incr) (hTfill : ∀ p ∈ T, p.1 ≠ _fill)
    (hTmin : ∀ p ∈ T, p.1 ≠ _min)
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ T)
    (hmemDrop : (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) ∈ T)
    (hmemCurr : (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_min, om) :: (_fill, of) :: (_incr, oi) :: T) H)
      fillSetup
      (.only (LocalSt (envOf bh bc bo)
        ((_min, .Vint (Integers.Int.repr (((2 ^ curr : Nat) : _root_.Int))))
          :: (_fill, .Vint (Integers.Int.repr
               (((2 ^ curr : Nat) : _root_.Int))))
          :: (_incr, .Vint (Integers.Int.repr
               (((2 ^ (len - drop) : Nat) : _root_.Int)))) :: T) H)) := by
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_incr, .Vint (Integers.Int.repr
          (((2 ^ (len - drop) : Nat) : _root_.Int))))
        :: (_min, om) :: (_fill, of) :: T) H) _ _ _ ?_ ?_
  · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
      ((_min, om) :: (_fill, of) :: T) H _incr _ _
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · exact List.mem_cons_self
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hp3)))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _min ≠ _incr; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _fill ≠ _incr; decide
        · exact hTincr p hp3)
      (fun le mm hp hT' _ _ => ?_)
    refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
      (.Vint (Integers.Int.repr (((len - drop : Nat) : _root_.Int)))) _
      (EvalExpr.Econst_int _ _) ?_ ?_
    · refine EvalExpr.Ebinop .Osub _ _ _
        (.Vint (Integers.Int.repr ((len : _root_.Int))))
        (.Vint (Integers.Int.repr ((drop : _root_.Int)))) _
        (EvalExpr.Etempvar _len tuint _
          (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hmemLen)))))
        (EvalExpr.Etempvar _drop tuint _
          (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hmemDrop))))) ?_
      simp only [typeof]
      rw [semBinop_sub_uint, u32_sub_nat len drop hdl (by omega)]
    · simp only [typeof]
      rw [semBinop_shl_uint _ _ _ _ (ltu_iwordsize (len - drop) (by omega)),
          shl_one_pow (len - drop) (by omega)]
  refine triple_seq_fwd ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((_fill, .Vint (Integers.Int.repr (((2 ^ curr : Nat) : _root_.Int))))
        :: (_incr, .Vint (Integers.Int.repr
             (((2 ^ (len - drop) : Nat) : _root_.Int))))
        :: (_min, om) :: T) H) _ _ _ ?_ ?_
  · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
      ((_incr, .Vint (Integers.Int.repr
          (((2 ^ (len - drop) : Nat) : _root_.Int))))
        :: (_min, om) :: T) H _fill _ _
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · exact List.mem_cons_self
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hp3)))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _incr ≠ _fill; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _min ≠ _fill; decide
        · exact hTfill p hp3)
      (fun le mm hp hT' _ _ => ?_)
    refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
      (.Vint (Integers.Int.repr ((curr : _root_.Int)))) _
      (EvalExpr.Econst_int _ _)
      (EvalExpr.Etempvar _curr tuint _
        (hT'.get (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hmemCurr))))) ?_
    simp only [typeof]
    rw [semBinop_shl_uint _ _ _ _ (ltu_iwordsize curr hc32),
        shl_one_pow curr hc32]
  refine triple_conseq ge fe f_inflate_table
    (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
      ((_fill, .Vint (Integers.Int.repr (((2 ^ curr : Nat) : _root_.Int))))
        :: (_incr, .Vint (Integers.Int.repr
             (((2 ^ (len - drop) : Nat) : _root_.Int)))) :: T) H _min _ _
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · exact List.mem_cons_self
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hp3)))
      (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp2
        · show _fill ≠ _min; decide
        rcases List.mem_cons.mp hp2 with rfl | hp3
        · show _incr ≠ _min; decide
        · exact hTmin p hp3)
      (fun le mm hp hT' _ _ =>
        EvalExpr.Etempvar _fill tuint _ (hT'.get List.mem_cons_self)))
    (fun _ _ _ x => x) (fun e le hp hx => hx)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- The short-circuit `len > root && (huff & mask) != low`, which clightgen
    normalises into a nested `if` writing `_t'10`. -/
theorem t10_set_triple
    (len root huff low : Nat)
    (hl32 : len < 4294967296) (hr32 : root < 32) (hh32 : huff < 4294967296)
    (hlow32 : low < 4294967296)
    (hT10 : ∀ p ∈ T, p.1 ≠ _t'10)
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ T)
    (hmemRoot : (_root, .Vint (Integers.Int.repr ((root : _root_.Int)))) ∈ T)
    (hmemHuff : (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))) ∈ T)
    (hmemMask : (_mask, .Vint (Integers.Int.repr
      (((2 ^ root - 1 : Nat) : _root_.Int)))) ∈ T)
    (hmemLow : (_low, .Vint (Integers.Int.repr ((low : _root_.Int)))) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T H)
      t10Stmt
      (.only (LocalSt (envOf bh bc bo)
        ((_t'10, .Vint (Integers.Int.repr
            (((if root < len ∧ huff % 2 ^ root ≠ low then 1 else 0 : Nat))
              : _root_.Int))) :: T) H)) := by
  have hp2 : (2 : Nat) ^ root < 4294967296 :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) hr32) (by decide)
  have hmod : huff % 2 ^ root < 4294967296 := by
    have := Nat.mod_lt huff (Nat.two_pow_pos root); omega
  by_cases hgt : root < len
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · refine ⟨Val.ofBool (Integers.Int.ltu
          (Integers.Int.repr ((root : _root_.Int)))
          (Integers.Int.repr ((len : _root_.Int)))), ?_, ?_⟩
      · exact EvalExpr.Ebinop .Ogt _ _ _ _ _ _
          (EvalExpr.Etempvar _len tuint _ (hT'.get hmemLen))
          (EvalExpr.Etempvar _root tuint _ (hT'.get hmemRoot))
          (semBinop_gt_uint _ _ _ _)
      · simp only [typeof, boolVal_ofBool_int]
        rw [ltu_nat32 root len (by omega) hl32,
            show decide (root < len) = true from by
              rw [decide_eq_true_eq]; exact hgt]
    · refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H
        _t'10 _ _ (fun p hp => hp) hT10
        (fun le mm hp hT' _ _ => ?_)
      refine EvalExpr.Ecast _ _ _ _
        (EvalExpr.Ebinop .One _ _ _
          (.Vint (Integers.Int.repr (((huff % 2 ^ root : Nat) : _root_.Int))))
          (.Vint (Integers.Int.repr ((low : _root_.Int)))) _ ?_
          (EvalExpr.Etempvar _low tuint _ (hT'.get hmemLow))
          (by simp only [typeof]; exact semBinop_ne_uint_uint _ _ _ _)) ?_
      · refine EvalExpr.Ebinop .Oand _ _ _
          (.Vint (Integers.Int.repr ((huff : _root_.Int))))
          (.Vint (Integers.Int.repr (((2 ^ root - 1 : Nat) : _root_.Int)))) _
          (EvalExpr.Etempvar _huff tuint _ (hT'.get hmemHuff))
          (EvalExpr.Etempvar _mask tuint _ (hT'.get hmemMask)) ?_
        simp only [typeof]
        rw [semBinop_and_uint, u32_and huff (2 ^ root - 1) hh32 (by omega),
            Nat.and_two_pow_sub_one_eq_mod]
      · simp only [typeof, Val.ofBool]
        by_cases hne : huff % 2 ^ root = low
        · rw [show (Integers.Int.eq
                (Integers.Int.repr (((huff % 2 ^ root : Nat) : _root_.Int)))
                (Integers.Int.repr ((low : _root_.Int)))) = true from by
                rw [eq_nat32 _ low hmod hlow32, decide_eq_true_eq]; exact hne]
          rw [show (if root < len ∧ huff % 2 ^ root ≠ low then 1 else 0 : Nat)
                = 0 from by
                rw [if_neg]; intro h; exact h.2 hne]
          rfl
        · rw [show (Integers.Int.eq
                (Integers.Int.repr (((huff % 2 ^ root : Nat) : _root_.Int)))
                (Integers.Int.repr ((low : _root_.Int)))) = false from by
                rw [eq_nat32 _ low hmod hlow32, decide_eq_false_iff_not]
                exact hne]
          rw [show (if root < len ∧ huff % 2 ^ root ≠ low then 1 else 0 : Nat)
                = 1 from by rw [if_pos ⟨hgt, hne⟩]]
          rfl
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · refine ⟨Val.ofBool (Integers.Int.ltu
          (Integers.Int.repr ((root : _root_.Int)))
          (Integers.Int.repr ((len : _root_.Int)))), ?_, ?_⟩
      · exact EvalExpr.Ebinop .Ogt _ _ _ _ _ _
          (EvalExpr.Etempvar _len tuint _ (hT'.get hmemLen))
          (EvalExpr.Etempvar _root tuint _ (hT'.get hmemRoot))
          (semBinop_gt_uint _ _ _ _)
      · simp only [typeof, boolVal_ofBool_int]
        rw [ltu_nat32 root len (by omega) hl32,
            show decide (root < len) = false from by
              rw [decide_eq_false_iff_not]; exact hgt]
    · refine triple_conseq ge fe f_inflate_table
        (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H
          _t'10 _ (.Vint (Integers.Int.repr 0))
          (fun p hp => hp) hT10
          (fun le mm hp hT' _ _ => EvalExpr.Econst_int _ _))
        (fun _ _ _ x => x) (fun e le hp hx => ?_)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
      rw [show (if root < len ∧ huff % 2 ^ root ≠ low then 1 else 0 : Nat) = 0
            from by rw [if_neg]; intro h; exact hgt h.1,
          show ((0 : Nat) : _root_.Int) = 0 from rfl]
      exact hx

/-- `incr = 1U << (len - drop);` -/
theorem incr_set_triple (len drop : Nat) (hdl : drop ≤ len) (hl15 : len ≤ 15)
    (oi : Val) (hTincr : ∀ p ∈ T, p.1 ≠ _incr)
    (hmemLen : (_len, .Vint (Integers.Int.repr ((len : _root_.Int)))) ∈ T)
    (hmemDrop : (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) ((_incr, oi) :: T) H)
      (.Sset _incr (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
        (.Ebinop .Osub (.Etempvar _len tuint) (.Etempvar _drop tuint) tuint)
        tuint))
      (.only (LocalSt (envOf bh bc bo)
        ((_incr, .Vint (Integers.Int.repr
            (((2 ^ (len - drop) : Nat) : _root_.Int)))) :: T) H)) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _incr _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTincr (fun le mm hp hT' _ _ => ?_)
  refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
    (.Vint (Integers.Int.repr (((len - drop : Nat) : _root_.Int)))) _
    (EvalExpr.Econst_int _ _) ?_ ?_
  · refine EvalExpr.Ebinop .Osub _ _ _
      (.Vint (Integers.Int.repr ((len : _root_.Int))))
      (.Vint (Integers.Int.repr ((drop : _root_.Int)))) _
      (EvalExpr.Etempvar _len tuint _
        (hT'.get (List.mem_cons_of_mem _ hmemLen)))
      (EvalExpr.Etempvar _drop tuint _
        (hT'.get (List.mem_cons_of_mem _ hmemDrop))) ?_
    simp only [typeof]
    rw [semBinop_sub_uint, u32_sub_nat len drop hdl (by omega)]
  · simp only [typeof]
    rw [semBinop_shl_uint _ _ _ _ (ltu_iwordsize (len - drop) (by omega)),
        shl_one_pow (len - drop) (by omega)]

/-- `fill = 1U << curr;` -/
theorem fill_set_triple (curr : Nat) (hc32 : curr < 32)
    (of : Val) (hTfill : ∀ p ∈ T, p.1 ≠ _fill)
    (hmemCurr : (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) ((_fill, of) :: T) H)
      (.Sset _fill (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
        (.Etempvar _curr tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        ((_fill, .Vint (Integers.Int.repr (((2 ^ curr : Nat) : _root_.Int))))
          :: T) H)) := by
  refine triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _fill _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTfill (fun le mm hp hT' _ _ => ?_)
  refine EvalExpr.Ebinop .Oshl _ _ _ (.Vint (Integers.Int.repr 1))
    (.Vint (Integers.Int.repr ((curr : _root_.Int)))) _
    (EvalExpr.Econst_int _ _)
    (EvalExpr.Etempvar _curr tuint _
      (hT'.get (List.mem_cons_of_mem _ hmemCurr))) ?_
  simp only [typeof]
  rw [semBinop_shl_uint _ _ _ _ (ltu_iwordsize curr hc32), shl_one_pow curr hc32]

/-- `min = fill;` -/
theorem min_set_triple (v : Val) (om : Val) (hTmin : ∀ p ∈ T, p.1 ≠ _min)
    (hmemFill : (_fill, v) ∈ T) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) ((_min, om) :: T) H)
      (.Sset _min (.Etempvar _fill tuint))
      (.only (LocalSt (envOf bh bc bo) ((_min, v) :: T) H)) :=
  triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ T H _min _ _
    (fun p hp => List.mem_cons_of_mem _ hp) hTmin
    (fun le mm hp hT' _ _ =>
      EvalExpr.Etempvar _fill tuint _
        (hT'.get (List.mem_cons_of_mem _ hmemFill)))

end C


/-! ## §26 The main loop: adapters, state, invariant

Statement coverage is complete (§2-§25); what is left is the loop's invariant
and the chaining of the chunks into `Sloop`.  This section lays the two things
that has to rest on.

**The adapters.**  Every chunk lemma demands *its* target temporary at the head
of the tracked list, and one iteration writes twelve different ones.  `TempsHold`
is order-insensitive (`TempsHold_mono`), so a permutation is a sublist inclusion
in both directions — `localst_adapt` packages that together with the heap
re-association `localst_perm` already did, which is what keeps a twelve-step
chain readable.

**The state.**  `Tmut ++ Tfix` splits the tracked list into the twelve the body
writes and the twelve it never does; only the prefix is permuted, and `Tfix`
supplies every membership hypothesis unchanged.  `HLoop` fixes one order for the
eleven owned heap components.

Note on arity: `Tfix` and `HLoop` are section-variable-applied, so their real
argument lists are

    Tfix  tblB tblO bitsB bitsO workB workO lensB lensO vx vb ty codes root max mtch
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
          workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
          extraF baseF Hrest cntF offsF v0 v1 v2 vbits

— read off the *declaration* order of the `variable` lines, not the order they
appear in the body. -/

section Adapt

variable (ge : CGenv) (fe : EntryRel)

/-- **Adapt a chunk's precondition to the enclosing state**: reorder or shrink
    the tracked list and re-associate the heap, in one step.

    `TempsHold` is order-insensitive (`TempsHold_mono`), so a *permutation* of
    the tracked list is a sublist inclusion in both directions; that is what
    lets each statement lemma demand its own target at the head while the loop
    keeps one canonical order. -/
theorem localst_adapt (E : Env) (l l' : List (Ident × Val)) (H H' : HProp)
    (hsub : ∀ p ∈ l', p ∈ l) (heq : H = H') (s : Stmt) (R : Sep.ExitConds)
    (h : Triple ge fe f_inflate_table (LocalSt E l' H') s R) :
    Triple ge fe f_inflate_table (LocalSt E l H) s R :=
  triple_conseq ge fe f_inflate_table h
    (fun e le hp hx => ⟨hx.1, TempsHold_mono hsub hx.2.1, heq ▸ hx.2.2⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- The postcondition side: a chunk that lands in `LocalSt E l H` also lands in
    any sublist/re-association of it. -/
theorem localst_post_adapt (E : Env) (l l' : List (Ident × Val)) (H H' : HProp)
    (hsub : ∀ p ∈ l', p ∈ l) (heq : H = H') (P : Sep.Assn) (s : Stmt)
    (h : Triple ge fe f_inflate_table P s (.only (LocalSt E l H))) :
    Triple ge fe f_inflate_table P s (.only (LocalSt E l' H')) :=
  triple_conseq ge fe f_inflate_table h (fun _ _ _ x => x)
    (fun e le hp hx => ⟨hx.1, TempsHold_mono hsub hx.2.1, heq ▸ hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- Both ends at once — the shape a chunk in the middle of a chain needs. -/
theorem localst_adapt_both (E : Env)
    (l l' m m' : List (Ident × Val)) (H H' G G' : HProp)
    (hsubP : ∀ p ∈ l', p ∈ l) (heqP : H = H')
    (hsubQ : ∀ p ∈ m', p ∈ m) (heqQ : G = G') (s : Stmt)
    (h : Triple ge fe f_inflate_table (LocalSt E l' H') s
      (.only (LocalSt E m G))) :
    Triple ge fe f_inflate_table (LocalSt E l H) s
      (.only (LocalSt E m' G')) :=
  triple_conseq ge fe f_inflate_table h
    (fun e le hp hx => ⟨hx.1, TempsHold_mono hsubP hx.2.1, heqP ▸ hx.2.2⟩)
    (fun e le hp hx => ⟨hx.1, TempsHold_mono hsubQ hx.2.1, heqQ ▸ hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

end Adapt

/-- The mutable state of one iteration of the main loop: the twelve tracked
    temporaries the body writes, the residual `count`, and the `here`/`offs`
    contents the body does not constrain. -/
structure LoopSt where
  len : Nat
  sym : Nat
  curr : Nat
  drop : Nat
  used : Nat
  huff : Nat
  low : Nat
  mn : Nat
  nOff : Nat
  nO : Integers.Ptrofs
  cntF : Nat → Nat
  offsF : Nat → Nat
  vi : Val
  vf : Val
  vl : Integers.Int
  v0 : Val
  v1 : Val
  v2 : Val
  vbits : Val

/-- The invariant's **pure** content, as one structure rather than thirty
    nested `∃ _ : …` binders — so the body proof peels two binders, not thirty,
    and reads the clauses by name.

    I1 `len15`-`root1` — lengths in range and consistent.
    I2 `symlt`-`lensnext` — the four index bounds the chunk lemmas left
       conditional.  **The C checks none of them**; re-establishing them is the
       real content of preservation.
    I3 `hufflt` — `huff < 2 ^ len`, preserved by `Model.bwInc_lt`.
    I4 `nOaddr`-`mncap` — `next` is `nOff` entries into `*table`'s block with
       `2 ^ curr` still available; `used` within capacity.
    I5 `cnt1`, `cntb` — the residual count. -/
structure LoopFacts (n max root nwork ncodes nx nb mtch nlive cap : Nat)
    (workF lensF : Nat → Nat) (tO : Integers.Ptrofs) (s : LoopSt) : Prop where
  measure  : n + s.sym = nlive
  len1     : 1 ≤ s.len
  len15    : s.len ≤ 15
  lenmax   : s.len ≤ max
  droplen  : s.drop ≤ s.len
  droproot : s.drop = 0 ∨ s.drop = root
  curr1    : 1 ≤ s.curr
  currmax  : s.curr + s.drop ≤ max
  lmdcurr  : s.len - s.drop ≤ s.curr
  root15   : root ≤ 15
  max15    : max ≤ 15
  root1    : 1 ≤ root
  symlt    : s.sym < nwork
  a3x      : mtch ≤ workF s.sym → workF s.sym - mtch < nx
  a3b      : mtch ≤ workF s.sym → workF s.sym - mtch < nb
  symnext  : s.cntF s.len = 1 → s.len ≠ max → s.sym + 1 < nwork
  lensnext : s.cntF s.len = 1 → s.len ≠ max → workF (s.sym + 1) < ncodes
  hufflt   : s.huff < 2 ^ s.len
  nOaddr   : Integers.Ptrofs.unsigned s.nO
               = Integers.Ptrofs.unsigned tO + 4 * (s.nOff : _root_.Int)
  room     : s.nOff + 2 ^ s.curr ≤ cap
  usedcap  : s.used ≤ cap
  mncap    : s.mn ≤ cap
  cnt1     : 1 ≤ s.cntF s.len
  cntb     : ∀ j, s.cntF j < 65536
  /-- `offs` is dead after the sort loop but still owned, and the `return`
      needs its range to present it as a byte run. -/
  offsb    : ∀ j, s.offsF j < 65536
  -- I2's structural core: the loop consumes the sorted `work` array in order.
  symlive  : s.sym < nlive
  lenw     : s.len = lensF (workF s.sym)
  cntc     : ∀ j, 1 ≤ j →
               s.cntF j = cntSeg (fun k => lensF (workF k)) s.sym nlive j
  -- The consumed Kraft mass IS the current code, read in reversed bit order.
  hJ       : massBelow (fun k => lensF (workF k)) s.sym
               = rev s.len s.huff * 2 ^ (15 - s.len)
  -- `used` tracks the extent of the current (sub)table.
  useq     : s.used = s.nOff + 2 ^ s.curr
  /-- `low`'s range.  Needed because `main_loop_triple` must bound it and
      nothing else in the invariant does: `low` is `(unsigned)(-1)` while
      `drop = 0` and `huff % 2^root` afterwards, both below `2^32`. -/
  low32    : s.low < 4294967296
  -- In the root table, `curr` still is `root` and `low` its `-1` sentinel.
  dzcurr   : s.drop = 0 → s.curr = root
  dzlow    : s.drop = 0 → s.low = 4294967295
  -- a sub-table exists only if the code is longer than the root table;
  -- with `max = 1` this makes `drop = 0` at the loop's exit, which is what
  -- keeps the epilogue's `next[huff]` write in bounds (§26c).
  dropfired : s.drop = root → root < max
  dzoff    : s.drop = 0 → s.nOff = 0
  -- The look-ahead loop's promise: a code too long for the current sub-table
  -- can only appear after a full root-prefix of mass has been consumed —
  -- i.e. outside this sub-table.  Re-established by `subfit_from_look`.
  subfit   : s.drop = root → root + s.curr = max ∨
               ∀ i, s.sym ≤ i → i < nlive →
                 root + s.curr < lensF (workF i) →
                 (rev root s.low + 1) * 2 ^ (15 - root)
                   ≤ massBelow (fun k => lensF (workF k)) i

/-- **What the sort loop guarantees about `work[]`** — everything the I2 step
    needs about the loop-constant data.  All of it is a property of
    `(lensF, workF, nlive)` alone, so it is ambient, not part of the loop
    invariant.  `workchar_of_placed` (§26a) constructs it from the sort loop's
    postcondition and from A2/A3/kraftOk. -/
structure WorkChar (nwork ncodes nlive max mtch nx nb : Nat)
    (workF lensF : Nat → Nat) (vx vb : Val) (xB bB : Block) : Prop where
  hnl    : nlive ≤ nwork
  hwlt   : ∀ i, i < nlive → workF i < ncodes
  hsort  : ∀ i j, i ≤ j → j < nlive → lensF (workF i) ≤ lensF (workF j)
  hlive  : ∀ i, i < nlive → 1 ≤ lensF (workF i)
  hlmax  : ∀ i, i < nlive → lensF (workF i) ≤ max
  hlast  : 0 < nlive → lensF (workF (nlive - 1)) = max
  hmass  : massBelow (fun k => lensF (workF k)) nlive ≤ 2 ^ 15
  ha3x   : ∀ i, i < nlive → mtch ≤ workF i → workF i - mtch < nx
  ha3b   : ∀ i, i < nlive → mtch ≤ workF i → workF i - mtch < nb
  /-- `base`/`extra` are genuine pointers exactly when some live symbol reaches
      the branch that reads them.  For LENS/DISTS the `switch` assigns them and
      this is unconditional; for **CODES** the `switch` assigns only `match`, so
      they keep the prologue's `nullv` — and `hwlt` + A3-CODES (`ncodes ≤ 20 =
      mtch`) make the hypothesis vacuous because no live symbol reaches `mtch`. -/
  hvx    : ∀ i, i < nlive → mtch ≤ workF i → vx = .Vptr xB Integers.Ptrofs.zero
  hvb    : ∀ i, i < nlive → mtch ≤ workF i → vb = .Vptr bB Integers.Ptrofs.zero

/-- `here`'s three fields as one byte run, at arbitrary contents. -/
abbrev hereRun (v0 v1 v2 : Val) : List MemVal :=
  encodeVal .Mint8unsigned v0
  ++ (encodeVal .Mint8unsigned v1 ++ encodeVal .Mint16unsigned v2)

theorem hereRun_length (v0 v1 v2 : Val) : (hereRun v0 v1 v2).length = 4 := by
  show (encodeVal .Mint8unsigned v0
        ++ (encodeVal .Mint8unsigned v1
            ++ encodeVal .Mint16unsigned v2)).length = 4
  rw [List.length_append, List.length_append, length_encodeVal,
      length_encodeVal, length_encodeVal]
  rfl

/-- Where `next += min` lands.  Named so it fits inside a `{ s with … }` update
    — a multi-line term there does not parse. -/
abbrev bumpOfs (ge : CGenv) (nO : Integers.Ptrofs) (mn : Nat) :
    Integers.Ptrofs :=
  idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) Signedness.Unsigned nO
    (Integers.Int.repr ((mn : _root_.Int)))

section CODES

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)

/-- **The ENOUGH check, CODES case.**  For `type == CODES` both disjuncts are
    false, so the statement falls through without returning — but the proof
    still has to step over it, and that is why this third lemma exists
    alongside `enough_LENS_triple` / `enough_DISTS_triple`.

    Because there is no `return` on this path, nothing has to be freed, so the
    heap stays **opaque** — unlike the other two, which need the three locals as
    freeable byte runs. -/
theorem enough_CODES_triple (ea eb : Ident) (hab : ea ≠ eb)
    (l : List (Ident × Val)) (H : HProp)
    (hmemTy : (_type, .Vint (Integers.Int.repr 0)) ∈ l)
    (hT5 : ∀ p ∈ l, p.1 ≠ ea) (hT6 : ∀ p ∈ l, p.1 ≠ eb)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l H)
      (enoughChk ea eb)
      { normal := LocalSt (envOf bh bc bo) l H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  -- t'5 := 0  (type ≠ LENS)
  refine triple_seq ge fe f_inflate_table _
    (LocalSt (envOf bh bc bo)
      ((eb, .Vint Integers.Int.zero)
        :: (ea, .Vint (Integers.Int.repr 0)) :: l) H) _ _ _ ?_ ?_
  · refine triple_seq_only ge fe f_inflate_table
      (Q := LocalSt (envOf bh bc bo)
        ((ea, .Vint (Integers.Int.repr 0)) :: l) H) ?_ ?_
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr 0)
            (Integers.Int.repr 1)), ?_, ?_⟩
        · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
            (EvalExpr.Etempvar _type tint _ (hT'.get hmemTy))
            (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
        · simp only [typeof, boolVal_ofBool_int]
          decide
      · exact triple_set_local ge fe f_inflate_table (envOf bh bc bo) _ l H
          ea _ _ (fun p hp => hp) hT5
          (fun le mm hp hT' _ _ => EvalExpr.Econst_int _ _)
    -- t'6 := (bool)0  (t'5 = 0, and type ≠ DISTS)
    · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) ?_
      · exact ⟨.Vint (Integers.Int.repr 0),
          EvalExpr.Etempvar ea tint _ (hT'.get List.mem_cons_self),
          by simp only [typeof]; exact boolVal_vint mm _⟩
      · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
          (fun le mm hp hT' _ _ => ?_) ?_
        · refine ⟨Val.ofBool (Integers.Int.eq (Integers.Int.repr 0)
              (Integers.Int.repr 2)), ?_, ?_⟩
          · exact EvalExpr.Ebinop .Oeq _ _ _ _ _ _
              (EvalExpr.Etempvar _type tint _
                (hT'.get (List.mem_cons_of_mem _ hmemTy)))
              (EvalExpr.Econst_int _ _) (semBinop_eq_int _ _ _ _)
          · simp only [typeof, boolVal_ofBool_int]
            decide
        · refine triple_conseq ge fe f_inflate_table
            (triple_set_local ge fe f_inflate_table (envOf bh bc bo) _
              ((ea, .Vint (Integers.Int.repr 0)) :: l) H eb _ _
              (fun p hp => hp)
              (fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp2
                · exact hab
                · exact hT6 p hp2)
              (fun le mm hp hT' _ _ => ?_))
            (fun _ _ _ x => x) (fun _ _ _ x => x)
            (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
            (fun _ _ hx => hx.elim)
          refine EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) ?_
          simp only [typeof]
          rw [semCast_int_bool]
          rfl
  -- if (t'6) return 1;  — not taken
  · refine triple_conseq ge fe f_inflate_table
      (triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
        (fun le mm hp hT' _ _ => ?_) (triple_skip ge fe f_inflate_table _))
      (fun _ _ _ x => x) (fun e le hp hx => ?_)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)
    · exact ⟨.Vint Integers.Int.zero,
        EvalExpr.Etempvar eb tint _ (hT'.get List.mem_cons_self),
        by simp only [typeof]; exact boolVal_vint mm _⟩
    · obtain ⟨henv, hT', hH⟩ := hx
      exact ⟨henv, TempsHold_mono (fun p hp =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)) hT', hH⟩

end CODES

/-- The body of `if (len > root && (huff & mask) != low) { … }`
    (inftrees.c:267-293; AST 1286-1476). -/
abbrev subTableBody : Stmt :=
  .Ssequence
    (.Sifthenelse (.Ebinop .Oeq (.Etempvar _drop tuint)
      (.Econst_int (Integers.Int.repr 0) tint) tint)
      (.Sset _drop (.Etempvar _root tuint)) .Sskip)
    (.Ssequence
      (.Sset _next (.Ebinop .Oadd
        (.Etempvar _next (tptr (Ty.Tstruct __1353 noattr)))
        (.Etempvar _min tuint) (tptr (Ty.Tstruct __1353 noattr))))
      (.Ssequence
        (.Sset _curr (.Ebinop .Osub (.Etempvar _len tuint)
          (.Etempvar _drop tuint) tuint))
        (.Ssequence
          (.Sset _left (.Ecast (.Ebinop .Oshl
            (.Econst_int (Integers.Int.repr 1) tint) (.Etempvar _curr tuint)
            tint) tint))
          (.Ssequence
            lookLoop
            (.Ssequence
              (.Sset _used (.Ebinop .Oadd (.Etempvar _used tuint)
                (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
                  (.Etempvar _curr tuint) tuint) tuint))
              (.Ssequence
                (enoughChk _t'8 _t'9)
                (.Ssequence
                  (.Sset _low (.Ebinop .Oand (.Etempvar _huff tuint)
                    (.Etempvar _mask tuint) tuint))
                  backPtrBlock)))))))

/-- `huff >> drop` fits the sub-table's index width — a consequence of I3
    (`huff < 2 ^ len`), not a separate assumption. -/
theorem huff_shr_lt (huff len drop : Nat) (hdl : drop ≤ len)
    (hh : huff < 2 ^ len) : huff / 2 ^ drop < 2 ^ (len - drop) := by
  have hpos : 0 < 2 ^ drop := Nat.two_pow_pos drop
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add]
  have h2 : drop + (len - drop) = len := by omega
  rw [h2]
  exact hh

/-! ### AST segment names

Generated from `InftreesAST.lean` by walking the `Ssequence` spine of
`fn_body`, so they are correct by construction.  They give the statements
proved by generic single-statement triples rather than a dedicated chunk lemma
(prologue `Set`s, the two clamps, the nine loop-setup `Set`s, the epilogue) a
name, and §27's `body_matches` ties the whole assembly back to the real
program. -/




/-- AST segment 0 (generated from the AST — see the caveat above). -/
abbrev setBase : Stmt :=
  (Stmt.Sset _base
  (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))

/-- AST segment 1 (generated from the AST — see the caveat above). -/
abbrev setExtra : Stmt :=
  (Stmt.Sset _extra
  (Expr.Ecast (Expr.Econst_int (Integers.Int.repr 0) tint) (tptr tvoid)))

/-- AST segment 2 (generated from the AST — see the caveat above). -/
abbrev setMatch : Stmt :=
  (Stmt.Sset _match (Expr.Econst_int (Integers.Int.repr 0) tint))

/-- AST segment 3: the initialiser and `loop1`. -/
abbrev seg3 : Stmt :=
  .Ssequence
    (Stmt.Sset _len (Expr.Econst_int (Integers.Int.repr 0) tint))
    loop1

/-- AST segment 4: the initialiser and `loop2`. -/
abbrev seg4 : Stmt :=
  .Ssequence
    (Stmt.Sset _sym (Expr.Econst_int (Integers.Int.repr 0) tint))
    loop2

/-- AST segment 5 (generated from the AST — see the caveat above). -/
abbrev readRoot : Stmt :=
  (Stmt.Sset _root
  (Expr.Ederef (Expr.Etempvar _bits (tptr tuint)) tuint))

/-- AST segment 6: the initialiser and `loop3`. -/
abbrev seg6 : Stmt :=
  .Ssequence
    (Stmt.Sset _max
    (Expr.Econst_int (Integers.Int.repr 15) tint))
    loop3

/-- AST segment 7 (generated from the AST — see the caveat above). -/
abbrev clamp1Stmt : Stmt :=
  (Stmt.Sifthenelse (Expr.Ebinop Binop.Ogt
  (Expr.Etempvar _root tuint)
  (Expr.Etempvar _max tuint) tint)
  (Stmt.Sset _root (Expr.Etempvar _max tuint))
  Stmt.Sskip)

/-- AST segment 9: the initialiser and `loop4`. -/
abbrev seg9 : Stmt :=
  .Ssequence
    (Stmt.Sset _min
    (Expr.Econst_int (Integers.Int.repr 1) tint))
    loop4

/-- AST segment 10 (generated from the AST — see the caveat above). -/
abbrev clamp2Stmt : Stmt :=
  (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
  (Expr.Etempvar _root tuint)
  (Expr.Etempvar _min tuint) tint)
  (Stmt.Sset _root (Expr.Etempvar _min tuint))
  Stmt.Sskip)

/-- AST segment 11 (generated from the AST — see the caveat above). -/
abbrev initLeft : Stmt :=
  (Stmt.Sset _left
  (Expr.Econst_int (Integers.Int.repr 1) tint))

/-- AST segment 12: the initialiser and `loop5`. -/
abbrev seg12 : Stmt :=
  .Ssequence
    (Stmt.Sset _len
    (Expr.Econst_int (Integers.Int.repr 1) tint))
    loop5

/-- AST segment 15: the initialiser and `loop6`. -/
abbrev seg15 : Stmt :=
  .Ssequence
    (Stmt.Sset _len
    (Expr.Econst_int (Integers.Int.repr 1) tint))
    loop6

/-- AST segment 16: the initialiser and `loop7`. -/
abbrev seg16 : Stmt :=
  .Ssequence
    (Stmt.Sset _sym
    (Expr.Econst_int (Integers.Int.repr 0) tint))
    loop7

/-- AST segment 18 (generated from the AST — see the caveat above). -/
abbrev setHuff0 : Stmt :=
  (Stmt.Sset _huff
  (Expr.Econst_int (Integers.Int.repr 0) tint))

/-- AST segment 19 (generated from the AST — see the caveat above). -/
abbrev setSym0 : Stmt :=
  (Stmt.Sset _sym
  (Expr.Econst_int (Integers.Int.repr 0) tint))

/-- AST segment 20 (generated from the AST — see the caveat above). -/
abbrev setLenMin : Stmt :=
  (Stmt.Sset _len
  (Expr.Etempvar _min tuint))

/-- AST segment 21 (generated from the AST — see the caveat above). -/
abbrev setNextTbl : Stmt :=
  (Stmt.Sset _next
  (Expr.Ederef
  (Expr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
  (tptr (Ty.Tstruct __1353 noattr))))

/-- AST segment 22 (generated from the AST — see the caveat above). -/
abbrev setCurrRoot : Stmt :=
  (Stmt.Sset _curr
  (Expr.Etempvar _root tuint))

/-- AST segment 23 (generated from the AST — see the caveat above). -/
abbrev setDrop0 : Stmt :=
  (Stmt.Sset _drop
  (Expr.Econst_int (Integers.Int.repr 0) tint))

/-- AST segment 24 (generated from the AST — see the caveat above). -/
abbrev setLowM1 : Stmt :=
  (Stmt.Sset _low
  (Expr.Ecast
  (Expr.Eunop Unop.Oneg
  (Expr.Econst_int (Integers.Int.repr 1) tint)
  tint) tuint))

/-- AST segment 25 (generated from the AST — see the caveat above). -/
abbrev setUsed : Stmt :=
  (Stmt.Sset _used
  (Expr.Ebinop Binop.Oshl
  (Expr.Econst_int (Integers.Int.repr 1) tuint)
  (Expr.Etempvar _root tuint)
  tuint))

/-- AST segment 26 (generated from the AST — see the caveat above). -/
abbrev setMask : Stmt :=
  (Stmt.Sset _mask
  (Expr.Ebinop Binop.Osub
  (Expr.Etempvar _used tuint)
  (Expr.Econst_int (Integers.Int.repr 1) tint)
  tuint))

/-- AST segment 29 (generated from the AST — see the caveat above). -/
abbrev epilogueIf : Stmt :=
  (Stmt.Sifthenelse
  (Expr.Ebinop Binop.One
  (Expr.Etempvar _huff tuint)
  (Expr.Econst_int (Integers.Int.repr 0) tint)
  tint)
  (Stmt.Ssequence
  (Stmt.Sassign
  (Expr.Efield
  (Expr.Evar _here (Ty.Tstruct __1353 noattr))
  _op
  tuchar)
  (Expr.Ecast
  (Expr.Econst_int (Integers.Int.repr 64) tint)
  tuchar))
  (Stmt.Ssequence
  (Stmt.Sassign
  (Expr.Efield
  (Expr.Evar _here (Ty.Tstruct __1353 noattr))
  _bits
  tuchar)
  (Expr.Ecast
  (Expr.Ebinop Binop.Osub
  (Expr.Etempvar _len tuint)
  (Expr.Etempvar _drop tuint)
  tuint)
  tuchar))
  (Stmt.Ssequence
  (Stmt.Sassign
  (Expr.Efield
  (Expr.Evar _here (Ty.Tstruct __1353 noattr))
  _val
  tushort)
  (Expr.Ecast
  (Expr.Econst_int (Integers.Int.repr 0) tint)
  tushort))
  (Stmt.Sassign
  (Expr.Ederef
  (Expr.Ebinop Binop.Oadd
  (Expr.Etempvar _next (tptr (Ty.Tstruct __1353 noattr)))
  (Expr.Etempvar _huff tuint)
  (tptr (Ty.Tstruct __1353 noattr)))
  (Ty.Tstruct __1353 noattr))
  (Expr.Evar _here (Ty.Tstruct __1353 noattr))))))
  Stmt.Sskip)

/-- AST segment 30 (generated from the AST — see the caveat above). -/
abbrev bumpTableUsed : Stmt :=
  (Stmt.Ssequence
  (Stmt.Sset _t'11
  (Expr.Ederef
  (Expr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
  (tptr (Ty.Tstruct __1353 noattr))))
  (Stmt.Sassign
  (Expr.Ederef
  (Expr.Etempvar _table (tptr (tptr (Ty.Tstruct __1353 noattr))))
  (tptr (Ty.Tstruct __1353 noattr)))
  (Expr.Ebinop Binop.Oadd
  (Expr.Etempvar _t'11 (tptr (Ty.Tstruct __1353 noattr)))
  (Expr.Etempvar _used tuint)
  (tptr (Ty.Tstruct __1353 noattr)))))

/-- AST segment 31 (generated from the AST — see the caveat above). -/
abbrev setBitsRoot : Stmt :=
  (Stmt.Sassign
  (Expr.Ederef
  (Expr.Etempvar _bits (tptr tuint))
  tuint)
  (Expr.Etempvar _root tuint))

/-- AST segment 32 (generated from the AST — see the caveat above). -/
abbrev retZero : Stmt :=
  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint)))

open InflateTable.Model in
/-- The main loop's state on entry: `sym = 0`, `huff = 0`, `drop = 0`,
    `curr = root`, `used = 2^root`, `next = *table`, `low = (unsigned)(-1)`,
    and `len = min`.  The three temporaries the loop body writes before
    reading (`incr`, `fill`, `left`) are arbitrary. -/
def entrySt (mn0 root : Nat) (tO : Integers.Ptrofs) (lensF workF : Nat → Nat)
    (codes : Nat) (offsF : Nat → Nat) (vi vf : Val) (vl : Integers.Int)
    (v0 v1 v2 vbits : Val) : LoopSt :=
  { len := mn0, sym := 0, curr := root, drop := 0, used := 2 ^ root,
    huff := 0, low := 4294967295, mn := mn0, nOff := 0, nO := tO,
    cntF := fun j => count lensF codes j, offsF := offsF,
    vi := vi, vf := vf, vl := vl, v0 := v0, v1 := v1, v2 := v2,
    vbits := vbits }

/-! ## §26a The main loop's setup statements (inftrees.c:204-214)

        huff = 0; sym = 0; len = min; next = *table;
        curr = root; drop = 0; low = (unsigned)(-1);
        used = 1U << root; mask = used - 1;

Nine `Sset`s, then the first ENOUGH check.  `set_used_triple` and
`set_mask_triple` (§15) already cover the last two; the two general shapes
missing were a temporary-to-temporary copy and the `(unsigned)(-1)` idiom. -/

section SetupStmts

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (l : List (Ident × Val)) (H : HProp)

/-- `dst = src;` for two temporaries — `len = min` and `curr = root`. -/
theorem set_copy_triple (dst src : Ident) (t : Ty) (v : Val)
    (hmem : (src, v) ∈ l) (hne : ∀ p ∈ l, p.1 ≠ dst) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H)
      (.Sset dst (.Etempvar src t))
      (.only (LocalSt (envOf bh bc bo) ((dst, v) :: l) H)) :=
  triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l H dst _ v
    (fun _ hp => hp) hne
    (fun le m hp hT _ _ => EvalExpr.Etempvar src t _ (hT.get hmem))

/-- `low = (unsigned)(-1);` — the sentinel that makes the first sub-table test
    fire.  `Ptrofs`-free: it is just `Int.repr (-1)`, which as a 32-bit word
    IS `4294967295`, and that is the form `Tmut` tracks. -/
theorem set_low_m1_triple (hne : ∀ p ∈ l, p.1 ≠ _low) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H)
      setLowM1
      (.only (LocalSt (envOf bh bc bo)
        ((_low, .Vint (Integers.Int.repr (((4294967295 : Nat) : _root_.Int))))
          :: l) H)) :=
  triple_set_local ge fe f_inflate_table (envOf bh bc bo) l l H _low _ _
    (fun _ hp => hp) hne
    (fun le m hp hT _ _ => by
      refine EvalExpr.Ecast _ _ (.Vint (Integers.Int.repr (-1))) _
        neg_one_eval ?_
      simp only [typeof]
      rw [show Cop.semCast (.Vint (Integers.Int.repr (-1))) tint tuint m
            = some (.Vint (Integers.Int.repr (-1))) from rfl]
      -- `Int.repr (-1)` and `Int.repr 4294967295` are the same 32-bit word
      congr 2)

end SetupStmts

open InflateTable.Model in
/-- What the loop's `break` leaves.  Not `LoopFacts`: `cnt1` is false at exit
    (the count just hit zero), and `hJ` is replaced by `hzero`, which is the
    only consequence of the mass invariant the epilogue needs. -/
structure ExitFacts (max root cap nlv : Nat) (workF lensF : Nat → Nat)
    (tO : Integers.Ptrofs) (s : LoopSt) : Prop where
  lenmax   : s.len = max
  hufflt   : s.huff < 2 ^ max
  hzero    : s.huff ≠ 0 →
               massBelow (fun k => lensF (workF k)) nlv < 2 ^ 15
  droproot : s.drop = 0 ∨ s.drop = root
  dropfired : s.drop = root → root < max
  dzoff    : s.drop = 0 → s.nOff = 0
  dzcurr   : s.drop = 0 → s.curr = root
  room     : s.nOff + 2 ^ s.curr ≤ cap
  usedcap  : s.used ≤ cap
  root1    : 1 ≤ root
  rootmax  : root ≤ max
  max15    : max ≤ 15
  nOaddr   : Integers.Ptrofs.unsigned s.nO
               = Integers.Ptrofs.unsigned tO + 4 * (s.nOff : _root_.Int)
  /-- `count` and `offs` are still u16 arrays.  The epilogue turns both into
      byte runs for the `return`, so it needs their ranges — carried here
      rather than as `∀ s : LoopSt` hypotheses, which no caller could
      discharge. -/
  cntb     : ∀ j, s.cntF j < 65536
  offsb    : ∀ j, s.offsF j < 65536

section MainLoop

variable (ge : CGenv) (fe : EntryRel)
variable (bh bc bo : Block)
-- permissions and blocks that never change
variable (pt pb pr pw pl pg : Permission)
variable (tblB : Block) (tblO : Integers.Ptrofs)
variable (bitsB : Block) (bitsO : Integers.Ptrofs)
variable (tB : Block) (tO : Integers.Ptrofs) (cap : Nat)
variable (workB : Block) (workO : Integers.Ptrofs) (nwork : Nat)
variable (workF : Nat → Nat)
variable (lensB : Block) (lensO : Integers.Ptrofs) (ncodes : Nat)
variable (lensF : Nat → Nat)
variable (xB bB : Block) (vx vb : Val) (nx nb : Nat) (extraF baseF : Nat → Nat)
variable (ty codes root max mtch nlive : Nat) (Hrest : HProp)

/-- The twelve temporaries the loop body writes.  Only this prefix is ever
    permuted; `localst_adapt` moves whichever one a statement needs to the
    head. -/
abbrev Tmut (len sym curr drop used huff low mn : Nat)
    (nO : Integers.Ptrofs) (vi vf : Val) (vl : Integers.Int) :
    List (Ident × Val) :=
  [(_len,  .Vint (Integers.Int.repr ((len : _root_.Int)))),
   (_sym,  .Vint (Integers.Int.repr ((sym : _root_.Int)))),
   (_curr, .Vint (Integers.Int.repr ((curr : _root_.Int)))),
   (_drop, .Vint (Integers.Int.repr ((drop : _root_.Int)))),
   (_used, .Vint (Integers.Int.repr ((used : _root_.Int)))),
   (_huff, .Vint (Integers.Int.repr ((huff : _root_.Int)))),
   (_low,  .Vint (Integers.Int.repr ((low : _root_.Int)))),
   (_min,  .Vint (Integers.Int.repr ((mn : _root_.Int)))),
   (_next, .Vptr tB nO),
   (_incr, vi), (_fill, vf), (_left, .Vint vl)]

/-- The twelve the loop body never writes: the six parameters, the three
    root/max/mask constants, and the three the `switch` set. -/
abbrev Tfix : List (Ident × Val) :=
  [(_type,  .Vint (Integers.Int.repr ((ty : _root_.Int)))),
   (_lens,  .Vptr lensB lensO),
   (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))),
   (_table, .Vptr tblB tblO),
   (_bits,  .Vptr bitsB bitsO),
   (_work,  .Vptr workB workO),
   (_root,  .Vint (Integers.Int.repr ((root : _root_.Int)))),
   (_max,   .Vint (Integers.Int.repr ((max : _root_.Int)))),
   (_mask,  .Vint (Integers.Int.repr (((2 ^ root - 1 : Nat) : _root_.Int)))),
   (_base,  vb),
   (_extra, vx),
   (_match, .Vint (Integers.Int.repr ((mtch : _root_.Int))))]

/-- The eleven heap components the loop body owns, in one canonical order.
    `offs` is dead after the sort loop but still owned — it has to be, to be
    freed at return. -/
abbrev HLoop (cntF offsF : Nat → Nat) (v0 v1 v2 vbits : Val) : HProp :=
  arrayU16 .Freeable bc 0 16 cntF
  ∗ (HoffsAt bo offsF
     ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
        ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
           ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
              ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
                 ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
                      (.Vptr tB tO)
                    ∗ (mapsto .Mint32 pb bitsB
                         (Integers.Ptrofs.unsigned bitsO) vbits
                       ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO)
                            nwork workF
                          ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO)
                               ncodes lensF
                             ∗ (arrayU16 pg xB 0 nx extraF
                                ∗ (arrayU16 pg bB 0 nb baseF
                                   ∗ Hrest)))))))))))

/-- The tracked list at the loop head. -/
abbrev TLoop (s : LoopSt) : List (Ident × Val) :=
  Tmut tB s.len s.sym s.curr s.drop s.used s.huff s.low s.mn s.nO s.vi s.vf s.vl
  ++ Tfix tblB tblO bitsB bitsO workB workO lensB lensO vx vb ty codes root max
       mtch

/-- **The main loop's invariant.**  Measure `n = nlive - sym`. -/
def LoopInv (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ s : LoopSt,
  ∃ _ : LoopFacts n max root nwork ncodes nx nb mtch nlive cap workF lensF tO s,
    LocalSt (envOf bh bc bo) (TLoop tblB tblO bitsB bitsO tB workB workO lensB
      lensO vx vb ty codes root max mtch s)
      (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF s.v0 s.v1 s.v2 s.vbits) e le hp
/-! ### Footprint bridges

Each chunk lemma has its own canonical heap order with an opaque `Hrest` tail,
so every boundary in the chain is "instantiate `Hrest` with the rest of `HLoop`,
then rewrite".  These are those rewrites, one per chunk family.

Two things worth knowing before writing more of them:

* `sep_cancel` alone does **not** unfold a named `abbrev` heap on the left —
  prefix it with `simp only [HLoop, …]`.  Without that the left side stays
  folded and the goal survives normalisation.
* `simp only` sometimes closes the goal on its own, so the trailing
  `sep_cancel` must be `try sep_cancel`.

The one boundary that is *not* a permutation is the fill loop's
(`HLoop_as_Hfill`): `Hfill` wants `codeRegion` at `next` with `2 ^ curr` entries
and `here` as an assembled byte run, so that step needs `codeRegion_split` twice
— justified by `LoopFacts.room` and `LoopFacts.nOaddr` — plus `here_assemble`.
It is the only one where the `Hrest` instantiation carries *two* leftover
fragments (the table before and after the sub-table). -/

/-- `HLoop`'s tail as `Hentry` sees it: everything except `work`, `extra`,
    `base` and `here`'s three fields. -/
abbrev HentryRest (cntF offsF : Nat → Nat) (vbits : Val) : HProp :=
  arrayU16 .Freeable bc 0 16 cntF
  ∗ (HoffsAt bo offsF
     ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
        ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
           ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vbits
              ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
                 ∗ Hrest)))))

/-- The heap re-association the entry-construction chunks need: `HLoop` is
    `Hentry` with the other six components pushed into its opaque tail. -/
theorem HLoop_as_Hentry (cntF offsF : Nat → Nat) (v0 v1 v2 vbits : Val) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF v0 v1 v2 vbits
    = Hentry bh pw workB workO nwork workF pg xB bB nx nb extraF baseF
        (HentryRest bc bo pt pb pr pl tblB tblO bitsB bitsO tB tO cap lensB
          lensO ncodes lensF Hrest cntF offsF vbits) v0 v1 v2 := by
  simp only [HLoop, HentryRest, Hentry]
  try sep_cancel

/-- `HLoop`'s tail as the symbol-advance chunks see it. -/
abbrev HadvRest (v0 v1 v2 vbits : Val) (offsF : Nat → Nat) : HProp :=
  HoffsAt bo offsF
  ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
     ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
        ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
           ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
              ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
                   (.Vptr tB tO)
                 ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
                      vbits
                    ∗ (arrayU16 pg xB 0 nx extraF
                       ∗ (arrayU16 pg bB 0 nb baseF ∗ Hrest))))))))

theorem HLoop_as_Hadv (cntF offsF : Nat → Nat) (v0 v1 v2 vbits : Val) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF v0 v1 v2 vbits
    = Hadv bc pw workB workO nwork workF pl lensB lensO ncodes lensF
        (HadvRest bh bo pt pb pr pg tblB tblO bitsB bitsO tB tO cap xB bB nx nb
          extraF baseF Hrest v0 v1 v2 vbits offsF) cntF := by
  simp only [HLoop, HadvRest, Hadv]
  try sep_cancel

/-- `HLoop`'s tail as the look-ahead loop sees it (it touches only `count`). -/
abbrev HlookRest (v0 v1 v2 vbits : Val) (offsF : Nat → Nat) : HProp :=
  HoffsAt bo offsF
  ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
     ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
        ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
           ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
              ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO)
                   (.Vptr tB tO)
                 ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
                      vbits
                    ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork
                         workF
                       ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO)
                            ncodes lensF
                          ∗ (arrayU16 pg xB 0 nx extraF
                             ∗ (arrayU16 pg bB 0 nb baseF ∗ Hrest))))))))))

theorem HLoop_as_Hlook (cntF offsF : Nat → Nat) (v0 v1 v2 vbits : Val) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF v0 v1 v2 vbits
    = Hlook bc cntF
        (HlookRest bh bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
          workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
          baseF Hrest v0 v1 v2 vbits offsF) := by
  simp only [HLoop, HlookRest, Hlook]
  try sep_cancel

/-- `HLoop` as the root back-pointer block sees it: the whole table region and
    the `table` cell in front. -/
abbrev HbpRest (cntF offsF : Nat → Nat) (v0 v1 v2 vbits : Val) : HProp :=
  arrayU16 .Freeable bc 0 16 cntF
  ∗ (HoffsAt bo offsF
     ∗ (mapsto .Mint8unsigned .Freeable bh 0 v0
        ∗ (mapsto .Mint8unsigned .Freeable bh 1 v1
           ∗ (mapsto .Mint16unsigned .Freeable bh 2 v2
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vbits
                 ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork
                      workF
                    ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO)
                         ncodes lensF
                       ∗ (arrayU16 pg xB 0 nx extraF
                          ∗ (arrayU16 pg bB 0 nb baseF ∗ Hrest)))))))))

theorem HLoop_as_backptr (cntF offsF : Nat → Nat) (v0 v1 v2 vbits : Val) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF v0 v1 v2 vbits
    = codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
         ∗ HbpRest bh bc bo pb pw pl pg bitsB bitsO workB workO nwork workF
             lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest cntF offsF
             v0 v1 v2 vbits) := by
  simp only [HLoop, HbpRest]
  try sep_cancel

/-- Carve the sub-table the fill loop writes out of the whole region.  The two
    splits are justified by `LoopFacts.room` (`nOff + 2 ^ curr ≤ cap`) and the
    address by `LoopFacts.nOaddr`. -/
theorem codeRegion_carve_sub (nOff curr : Nat) (nO : Integers.Ptrofs)
    (hroom : nOff + 2 ^ curr ≤ cap)
    (haddr : Integers.Ptrofs.unsigned nO
               = Integers.Ptrofs.unsigned tO + 4 * (nOff : _root_.Int)) :
    codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      = codeRegion pr tB (Integers.Ptrofs.unsigned tO) nOff
        ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned nO) (2 ^ curr)
           ∗ codeRegion pr tB
               (Integers.Ptrofs.unsigned nO + 4 * ((2 ^ curr : Nat) : _root_.Int))
               (cap - nOff - 2 ^ curr)) := by
  conv => lhs; rw [show cap = nOff + (2 ^ curr + (cap - nOff - 2 ^ curr)) from by
    omega]
  rw [codeRegion_split pr tB nOff (Integers.Ptrofs.unsigned tO)
        (2 ^ curr + (cap - nOff - 2 ^ curr)),
      codeRegion_split pr tB (2 ^ curr)
        (Integers.Ptrofs.unsigned tO + 4 * (nOff : _root_.Int))
        (cap - nOff - 2 ^ curr),
      ← haddr]

/-- `HLoop`'s tail as the fill loop sees it: the two table fragments the
    sub-table is carved from, and everything else. -/
abbrev HfillRest (cntF offsF : Nat → Nat) (vbits : Val)
    (nOff curr : Nat) (nO : Integers.Ptrofs) : HProp :=
  codeRegion pr tB (Integers.Ptrofs.unsigned tO) nOff
  ∗ (codeRegion pr tB
       (Integers.Ptrofs.unsigned nO + 4 * ((2 ^ curr : Nat) : _root_.Int))
       (cap - nOff - 2 ^ curr)
     ∗ (arrayU16 .Freeable bc 0 16 cntF
        ∗ (HoffsAt bo offsF
           ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vbits
                 ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork
                      workF
                    ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes
                         lensF
                       ∗ (arrayU16 pg xB 0 nx extraF
                          ∗ (arrayU16 pg bB 0 nb baseF ∗ Hrest)))))))))

/-- **The fill loop's boundary** — the one chain boundary that is not a
    permutation.  `Hfill` wants the sub-table at `next` and `here` as an
    assembled byte run, so this needs `codeRegion_split` twice *and*
    `here_assemble`. -/
theorem HLoop_as_Hfill (cntF offsF : Nat → Nat) (vbits : Val)
    (op bits val nOff curr : Nat) (nO : Integers.Ptrofs)
    (hroom : nOff + 2 ^ curr ≤ cap)
    (haddr : Integers.Ptrofs.unsigned nO
               = Integers.Ptrofs.unsigned tO + 4 * (nOff : _root_.Int)) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF (.Vint (Integers.Int.repr ((op : Nat))))
      (.Vint (Integers.Int.repr ((bits : Nat))))
      (.Vint (Integers.Int.repr ((val : Nat)))) vbits
    = Hfill pr tB nO curr bh op bits val
        (HfillRest bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
          workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
          baseF Hrest cntF offsF vbits nOff curr nO) := by
  simp only [HLoop, HfillRest, Hfill]
  rw [codeRegion_carve_sub pr tB tO cap nOff curr nO hroom haddr,
      ← here_assemble bh op bits val]
  try sep_cancel

/-! ### The chain, link by link

Each link lifts one chunk lemma to the loop's footprint.  The recipe:

    refine localst_adapt … (fun p hp => hp) (HLoop_as_X …) _ _ ?_
    refine localst_post_adapt … (fun p hp => hp) (HLoop_as_X …).symm _ _ ?_
    exact <chunk lemma> … (XRest …) (TLoop …) … (by temps_mem) …

The tracked list needs **no** adaptation — every chunk takes an arbitrary `l`,
so it is instantiated at `TLoop` directly and `fun p hp => hp` discharges the
inclusion.  Only the heap is re-associated.

When a chunk's post is existential (`ChoosePost`), `localst_post_adapt` does not
apply; use `triple_conseq` and rebuild the existential with the bridge rewritten
inside it — `loop_entry_choose` is the model.

**Freshness over an appended list.**  `temps_ne` handles `∀ p ∈ l, p.1 ≠ id`,
but not a *conjunction* of seven disequalities over `Tmut ++ Tfix`: the append
blocks `List.forall_mem_cons`, and after splitting it the 24×7 conjunction is
too big for one `Decidable` instance.  The recipe that works:

    simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
    exact ⟨by decide, …⟩        -- one per list element, 24 of them
-/

/-- `here.bits = (unsigned char)(len - drop);` against the loop's footprint. -/
theorem loop_entry_bits
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (s : LoopSt) (hdl : s.drop ≤ s.len) (hl15 : s.len ≤ 15) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF s.v0 s.v1 s.v2 s.vbits))
      entryBitsStmt
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF s.v0
          (.Vint (Integers.Int.repr
            ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) s.v2
          s.vbits))) := by
  have hbr := HLoop_as_Hentry bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s.cntF s.offsF
  refine localst_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun p hp => hp)
    (hbr s.v0 s.v1 s.v2 s.vbits) _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun p hp => hp)
    (hbr s.v0 _ s.v2 s.vbits).symm _ _ ?_
  exact entry_bits_triple ge fe bh bc bo pw workB workO nwork workF pg xB bB nx
    nb extraF baseF
    (HentryRest bc bo pt pb pr pl tblB tblO bitsB bitsO tB tO cap lensB lensO
      ncodes lensF Hrest s.cntF s.offsF s.vbits)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    hcenv s.len s.drop hdl (by omega) s.v0 s.v1 s.v2 (by temps_mem) (by temps_mem)

/-- After the entry `if`/`else if`/`else`, against the loop's footprint. -/
def LoopChoosePost (s : LoopSt) (v1 : Val) : Sep.Assn := fun e le hp =>
  ∃ op val : Nat, ∃ _ : op < 256, ∃ _ : val < 65536,
    LocalSt (envOf bh bc bo)
      (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
        root max mtch s)
      (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF (.Vint (Integers.Int.repr ((op : Nat)))) v1
        (.Vint (Integers.Int.repr ((val : Nat)))) s.vbits) e le hp

/-- `entryChoose` against the loop's footprint. -/
theorem loop_entry_choose
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpw : permOrder pw .Readable = true) (hwb : ∀ j, workF j < 65536)
    (hpg : permOrder pg .Readable = true)
    (hxb : ∀ j, extraF j < 65536) (hbb : ∀ j, baseF j < 65536)
    (hn31 : (nwork : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned workO + 2 * (nwork : _root_.Int)
             < 18446744073709551616)
    (hnx31 : (nx : _root_.Int) < 2147483648)
    (hnb31 : (nb : _root_.Int) < 2147483648)
    (hm32 : mtch < 4294967296)
    (s : LoopSt) (v1 : Val)
    (hs : s.sym < nwork)
    (hA3x : mtch ≤ workF s.sym → workF s.sym - mtch < nx)
    (hA3b : mtch ≤ workF s.sym → workF s.sym - mtch < nb)
    -- `base`/`extra` are genuine pointers only when the branch that reads them
    -- is reachable; for CODES they stay `nullv` and the branch never runs.
    (hvx : mtch ≤ workF s.sym → vx = .Vptr xB Integers.Ptrofs.zero)
    (hvb : mtch ≤ workF s.sym → vb = .Vptr bB Integers.Ptrofs.zero) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF s.v0 v1 s.v2 s.vbits))
      entryChoose
      (.only (LoopChoosePost bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
        tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
        extraF baseF ty codes root max mtch Hrest s v1)) := by
  have hbr := HLoop_as_Hentry bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s.cntF s.offsF
  refine triple_conseq ge fe f_inflate_table
    (entry_choose_triple ge fe bh bc bo pw workB workO nwork workF pg xB bB nx
      nb extraF baseF
      (HentryRest bc bo pt pb pr pl tblB tblO bitsB bitsO tB tO cap lensB lensO
        ncodes lensF Hrest s.cntF s.offsF s.vbits)
      s.sym mtch
      (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
        root max mtch s)
      hcenv hpw hwb hpg hxb hbb hs hn31 hno hnx31 hnb31 hm32 hA3x hA3b
      s.v0 v1 s.v2 (by temps_mem) (by temps_mem) (by temps_mem)
      (fun hB => by rw [← hvx hB]; temps_mem)
      (fun hB => by rw [← hvb hB]; temps_mem)
      (by simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
          exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩))
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hbr s.v0 v1 s.v2 s.vbits]
                                         exact hx.2.2⟩)
    (fun e le hp hx => by
      obtain ⟨op, val, hop, hval, hst⟩ := hx
      exact ⟨op, val, hop, hval, hst.1, hst.2.1, by
        rw [hbr _ v1 _ s.vbits]; exact hst.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! #### Links whose target is not at the head of `TLoop`

`TLoop` has one canonical order, but a plain `Sset` lemma wants its target at
the head.  The rotation is `setLocal`/`dropId`, which **compute** on the literal
list — so neither the rotated list nor its freshness side condition has to be
written out:

    refine localst_adapt … (TLoop … s) (setLocal (TLoop … s) _x oldv)
      _ _ (by simp +decide) rfl _ _ ?_
    refine localst_post_adapt … (setLocal (TLoop … s) _x newv)
      (TLoop … { s with … }) _ _ (by simp +decide) rfl _ _ ?_
    exact <chunk> … (dropId _x (TLoop … s)) … (fun p hp => (mem_dropId hp).2) …

Two things this depends on.  The lists must be given **explicitly** — with `_`
they are still metavariables when the side-condition tactic runs, and it fails
on a goal full of `?m`.  And the tactic must be `simp +decide`, not `temps_mem`:
`dropId` leaves `if _len = _incr then …` guards that plain `simp` will not
reduce. -/

/-- `incr = 1U << (len - drop);` against the loop's tracked list.

    The target is not at the head of `TLoop`, so the list is rotated with
    `dropId` — which *computes* on the literal list, so neither the rotated list
    nor its freshness side condition has to be written out. -/
theorem loop_incr_set (s : LoopSt) (v0 v1 v2 : Val)
    (hdl : s.drop ≤ s.len) (hl15 : s.len ≤ 15) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _incr (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
        (.Ebinop .Osub (.Etempvar _len tuint) (.Etempvar _drop tuint) tuint)
        tuint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch
          { s with vi := .Vint (Integers.Int.repr
              (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))) })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
      codes root max mtch s) _incr s.vi)
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
      codes root max mtch s) _incr
      (.Vint (Integers.Int.repr (((2 ^ (s.len - s.drop) : Nat) : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with vi := .Vint (Integers.Int.repr
          (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))) })
    _ _ (by simp +decide) rfl _ _ ?_
  exact incr_set_triple ge fe bh bc bo _
    (dropId _incr (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb
      ty codes root max mtch s))
    s.len s.drop hdl hl15 s.vi (fun p hp => (mem_dropId hp).2)
    (by simp +decide) (by simp +decide)

/-- `fill = 1U << curr;` against the loop's tracked list. -/
theorem loop_fill_set (s : LoopSt) (v0 v1 v2 : Val) (hc32 : s.curr < 32) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _fill (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
        (.Etempvar _curr tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with vf := .Vint (Integers.Int.repr
          (((2 ^ s.curr : Nat) : _root_.Int))) })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _fill s.vf)
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _fill
      (.Vint (Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with vf := .Vint (Integers.Int.repr
          (((2 ^ s.curr : Nat) : _root_.Int))) })
    _ _ (by simp +decide) rfl _ _ ?_
  exact fill_set_triple ge fe bh bc bo _
    (dropId _fill (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s))
    s.curr hc32 s.vf (fun p hp => (mem_dropId hp).2) (by simp +decide)


/-- `min = fill;` against the loop's tracked list. -/
theorem loop_min_set (s : LoopSt) (v0 v1 v2 : Val) (mnew : Nat)
    (hvf : s.vf = .Vint (Integers.Int.repr ((mnew : _root_.Int)))) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _min (.Etempvar _fill tuint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with mn := mnew })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _min (.Vint (Integers.Int.repr ((s.mn : _root_.Int)))))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _min
      (.Vint (Integers.Int.repr ((mnew : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with mn := mnew })
    _ _ (by simp +decide) rfl _ _ ?_
  exact min_set_triple ge fe bh bc bo _
    (dropId _min (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s))
    (.Vint (Integers.Int.repr ((mnew : _root_.Int))))
    (.Vint (Integers.Int.repr ((s.mn : _root_.Int))))
    (fun p hp => (mem_dropId hp).2) (by rw [← hvf]; simp +decide)


/-- `sym++;` against the loop's tracked list. -/
theorem loop_sym_incr (s : LoopSt) (v0 v1 v2 : Val) (hs32 : s.sym < 4294967295) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _sym (.Ebinop .Oadd (.Etempvar _sym tuint)
        (.Econst_int (Integers.Int.repr 1) tint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with sym := s.sym + 1 })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _sym (.Vint (Integers.Int.repr ((s.sym : _root_.Int)))))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _sym
      (.Vint (Integers.Int.repr (((s.sym + 1 : Nat) : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with sym := s.sym + 1 })
    _ _ (by simp +decide) rfl _ _ ?_
  exact sym_incr_triple ge fe bh bc bo s.sym hs32 _
    (dropId _sym (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s))
    (fun p hp => (mem_dropId hp).2)

/-- The sub-table short-circuit against the loop's tracked list.  `_t'10` is a
    compiler temporary that is not in `TLoop` — it is *prepended* by this link
    and consumed by the `if` that follows. -/
theorem loop_t10_set (s : LoopSt) (v0 v1 v2 : Val)
    (hl32 : s.len < 4294967296) (hr32 : root < 32)
    (hh32 : s.huff < 4294967296) (hlow32 : s.low < 4294967296) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      t10Stmt
      (.only (LocalSt (envOf bh bc bo)
        ((_t'10, .Vint (Integers.Int.repr
            (((if root < s.len ∧ s.huff % 2 ^ root ≠ s.low then 1 else 0 : Nat))
              : _root_.Int)))
          :: TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
               codes root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) :=
  t10_set_triple ge fe bh bc bo _
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    s.len root s.huff s.low hl32 hr32 hh32 hlow32
    (by simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
        decide)
    (by simp +decide) (by simp +decide) (by simp +decide) (by simp +decide)
    (by simp +decide)

/-- The nineteen temporaries the fill loop does not touch. -/
abbrev TfillTail (s : LoopSt) : List (Ident × Val) :=
  dropId _fill (dropId _incr (dropId _huff (dropId _drop (dropId _next
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)))))

/-- **The fill loop against the loop's footprint.**  The five temporaries it
    reads come to the front; the other nineteen ride along in `fillTemps`'
    tail (§17, generalised for exactly this). -/
theorem loop_fill_loop (s : LoopSt) (op bits val nOff : Nat)
    (hvi : s.vi = .Vint (Integers.Int.repr
      (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))))
    (hvf : s.vf = .Vint (Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int))))
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpr : permOrder pr .Writable = true)
    (htO4 : Integers.Ptrofs.unsigned tO % 4 = 0)
    (hnoCap : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
                < 18446744073709551616)
    (hroom : nOff + 2 ^ s.curr ≤ cap)
    (haddr : Integers.Ptrofs.unsigned s.nO
               = Integers.Ptrofs.unsigned tO + 4 * (nOff : _root_.Int))
    (hcurr : s.curr ≤ 15) (hlmd : s.len - s.drop ≤ s.curr) (hd32 : s.drop < 32)
    (hhuff : s.huff / 2 ^ s.drop < 2 ^ (s.len - s.drop))
    (hh : s.huff < 4294967296)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF (.Vint (Integers.Int.repr ((op : Nat))))
          (.Vint (Integers.Int.repr ((bits : Nat))))
          (.Vint (Integers.Int.repr ((val : Nat)))) s.vbits))
      fillLoop
      { normal := LocalSt (envOf bh bc bo)
          (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
            root max mtch
            { s with vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))) })
          (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
            workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
            baseF Hrest s.cntF s.offsF (.Vint (Integers.Int.repr ((op : Nat))))
            (.Vint (Integers.Int.repr ((bits : Nat))))
            (.Vint (Integers.Int.repr ((val : Nat)))) s.vbits),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  have hnoSub : Integers.Ptrofs.unsigned s.nO
      + 4 * (((2 ^ s.curr : Nat)) : _root_.Int) < 18446744073709551616 := by
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
    rw [hA] at hnoCap haddr
    rw [haddr]
    have h2 : A + 4 * ((cap : Nat) : _root_.Int)
        < (18446744073709551616 : _root_.Int) := hnoCap
    have h3 : nOff + 2 ^ s.curr ≤ cap := hroom
    show A + 4 * ((nOff : Nat) : _root_.Int)
          + 4 * (((2 ^ s.curr : Nat)) : _root_.Int)
        < (18446744073709551616 : _root_.Int)
    omega
  have hal4 : Integers.Ptrofs.unsigned s.nO % 4 = 0 := by
    obtain ⟨A, hA⟩ : ∃ A : _root_.Int, Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
    rw [hA] at htO4 haddr
    rw [haddr]
    have h2 : A % (4 : _root_.Int) = 0 := htO4
    show (A + 4 * ((nOff : Nat) : _root_.Int)) % (4 : _root_.Int) = 0
    omega
  have hbr := HLoop_as_Hfill bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s.cntF s.offsF s.vbits op bits val nOff s.curr s.nO
    hroom haddr
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (fillTemps tB s.nO s.huff s.drop (s.len - s.drop) (2 ^ s.curr)
      (TfillTail tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
        root max mtch s))
    _ _ (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp2
      · rw [← hvf]; simp
      rcases List.mem_cons.mp hp2 with rfl | hp3
      · rw [← hvi]; simp
      rcases List.mem_cons.mp hp3 with rfl | hp4
      · simp
      rcases List.mem_cons.mp hp4 with rfl | hp5
      · simp
      rcases List.mem_cons.mp hp5 with rfl | hp6
      · simp
      · exact (mem_dropId (mem_dropId (mem_dropId (mem_dropId
          (mem_dropId hp6).1).1).1).1).1) hbr _ _ ?_
  refine triple_conseq ge fe f_inflate_table
    (fill_loop_triple ge fe bh bc bo pr tB s.nO op bits val
      (HfillRest bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF s.vbits nOff s.curr s.nO)
      s.huff s.drop s.curr (s.len - s.drop)
      (TfillTail tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
        root max mtch s)
      (fun p hp => (mem_dropId hp).2)
      hcenv hpr hal4 hnoSub hcurr hlmd hd32 hhuff hh R)
    (fun e le hp hx => ⟨0, by
        have h1 : (1 : Nat) ≤ 2 ^ s.curr / 2 ^ (s.len - s.drop) :=
          (Nat.one_le_div_iff (Nat.two_pow_pos _)).mpr
            (Nat.pow_le_pow_right (by omega) hlmd)
        omega, by omega, by simp, by simpa using hx⟩)
    (fun e le hp hx => by
      refine ⟨hx.1, ?_, ?_⟩
      · exact TempsHold_mono (by simp +decide [TfillTail, hvi]) hx.2.1
      · rw [hbr]; exact hx.2.2)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- **The backwards code increment against the loop's footprint.**  Touches no
    memory, so the heap is carried unchanged and only the tracked list moves —
    `_incr` and `_huff` are both rotated to the head with a nested `setLocal`.

    `_incr`'s exit value is whatever the inner `while` left, so it is
    existential here; `LoopInv` quantifies the whole `LoopSt` anyway, and no
    later statement reads `_incr` before the next iteration overwrites it. -/
theorem loop_bwinc (s : LoopSt) (v0 v1 v2 : Val)
    (hh : s.huff < 4294967296) (hlen1 : 1 ≤ s.len) (hlen15 : s.len ≤ 15)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      bwIncBlock
      { normal := fun e le hp => ∃ vi' : Val,
          LocalSt (envOf bh bc bo)
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
              codes root max mtch
              { s with huff := bwInc s.huff s.len, vi := vi' })
            (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
              workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
              extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits) e le hp,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (bwinc_block_triple ge fe bh bc bo s.huff s.len
      (dropId _incr (dropId _huff
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)))
      (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF v0 v1 v2 s.vbits)
      hh hlen1 hlen15
      (fun p hp => (mem_dropId hp).2)
      (fun p hp => (mem_dropId (mem_dropId hp).1).2)
      (by simp +decide) s.vi R)
    (fun e le hp hx => ⟨hx.1, TempsHold_mono (by simp +decide) hx.2.1, hx.2.2⟩)
    (fun e le hp hx => by
      obtain ⟨f, hst⟩ := hx
      exact ⟨.Vint (Integers.Int.repr (((incrOf f : Nat) : _root_.Int))),
        hst.1, TempsHold_mono (by simp +decide) hst.2.1, hst.2.2⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-! #### The backwards increment, as the generated AST associates it

`bwIncBlock` bundles `incrInit; incrLoop; incrFix` into one `Ssequence`, but
clightgen emits the three **flat** in the loop body's right-nested chain.
`Ssequence` is a constructor, not an associative operator, so the bundled form
is a *different statement* — `fn_body = fullBody := rfl` is what caught this,
and it is the same trap `fill_setup_triple` fell into earlier.  The three links
below consume the three slots separately, with `IncInv`/`IncPost` (the block
proof's own internal seams) as the intermediate assertions. -/

/-- `incr = 1U << (len - 1);` against the loop's footprint. -/
theorem loop_incr_init (s : LoopSt) (v0 v1 v2 : Val)
    (hlen1 : 1 ≤ s.len) (hlen15 : s.len ≤ 15) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      incrInit
      (.only (IncInv bh bc bo s.huff s.len
        (dropId _incr (dropId _huff
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)))
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF v0 v1 v2 s.vbits) s.len)) := by
  refine triple_conseq ge fe f_inflate_table
    (incrInit_triple ge fe bh bc bo s.huff s.len _ _ hlen1 hlen15
      (fun p hp => (mem_dropId hp).2) (by simp +decide) s.vi)
    (fun e le hp hx => ⟨hx.1, TempsHold_mono (by simp +decide) hx.2.1, hx.2.2⟩)
    (fun _ _ _ x => x)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- `while (huff & incr) incr >>= 1;` against the loop's footprint. -/
theorem loop_incr_loop (s : LoopSt) (v0 v1 v2 : Val)
    (hh : s.huff < 4294967296) (hlen15 : s.len ≤ 15) (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (IncInv bh bc bo s.huff s.len
        (dropId _incr (dropId _huff
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)))
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF v0 v1 v2 s.vbits) s.len)
      incrLoop
      { normal := IncPost bh bc bo s.huff s.len
          (dropId _incr (dropId _huff
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)))
          (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF v0 v1 v2 s.vbits),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } :=
  incrLoop_triple ge fe bh bc bo s.huff s.len _ _ hh hlen15
    (fun p hp => (mem_dropId hp).2) R

/-- `if (incr) huff = (huff & (incr-1)) + incr; else huff = 0;` against the
    loop's footprint. -/
theorem loop_incr_fix (s : LoopSt) (v0 v1 v2 : Val)
    (hh : s.huff < 4294967296) (hlen15 : s.len ≤ 15) :
    Triple ge fe f_inflate_table
      (IncPost bh bc bo s.huff s.len
        (dropId _incr (dropId _huff
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)))
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      incrFix
      (.only (fun e le hp => ∃ vi' : Val,
        LocalSt (envOf bh bc bo)
          (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
            codes root max mtch
            { s with huff := bwInc s.huff s.len, vi := vi' })
          (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits) e le hp)) := by
  refine triple_conseq ge fe f_inflate_table
    (incrFix_triple ge fe bh bc bo s.huff s.len _ _ hh hlen15
      (fun p hp => (mem_dropId (mem_dropId hp).1).2))
    (fun _ _ _ x => x)
    (fun e le hp hx => by
      obtain ⟨f, hst⟩ := hx
      exact ⟨.Vint (Integers.Int.repr (((incrOf f : Nat) : _root_.Int))),
        hst.1, TempsHold_mono (by simp +decide) hst.2.1, hst.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- **`--count[len]` and the length step, against the loop's footprint.**

    This is the link that carries the loop's *only* `brk`, so its exit
    conditions are not `.only` and `localst_post_adapt` does not apply — the
    whole thing goes through `triple_conseq` with a `brk` implication of its
    own. -/
theorem loop_count_dec_adv (s : LoopSt) (v0 v1 v2 : Val)
    (hcb : ∀ j, s.cntF j < 65536) (hcl : 1 ≤ s.cntF s.len)
    (hlen15 : s.len ≤ 15) (hmax15 : max ≤ 15)
    (hwb : ∀ j, workF j < 65536) (hlb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ j, lensF j ≤ 15) (hlensmax : ∀ j, lensF j ≤ max)
    (hlenmax : s.len ≤ max)
    (hn31 : (nwork : _root_.Int) < 2147483648)
    (hnow : Integers.Ptrofs.unsigned workO + 2 * (nwork : _root_.Int)
             < 18446744073709551616)
    (hc31 : (ncodes : _root_.Int) < 2147483648)
    (hnol : Integers.Ptrofs.unsigned lensO + 2 * (ncodes : _root_.Int)
             < 18446744073709551616)
    (hpw : permOrder pw .Readable = true) (hpl : permOrder pl .Readable = true)
    (hsymlt : s.cntF s.len = 1 → s.len ≠ max → s.sym < nwork)
    (hlenslt : s.cntF s.len = 1 → s.len ≠ max → workF s.sym < ncodes)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Ssequence countDecStmt advIfStmt)
      { normal := fun e le hp => ∃ len' : Nat, ∃ _ : len' ≤ 15,
          ∃ _ : len' ≤ max,
          ∃ _ : (len' = s.len ∧ 2 ≤ s.cntF s.len)
                ∨ (s.cntF s.len = 1 ∧ s.len ≠ max
                   ∧ len' = lensF (workF s.sym)),
          LocalSt (envOf bh bc bo)
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
              codes root max mtch
              { s with len := len',
                       cntF := fun j => if j = s.len then s.cntF s.len - 1
                                        else s.cntF j })
            (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
              workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
              extraF baseF Hrest
              (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j)
              s.offsF v0 v1 v2 s.vbits) e le hp,
        brk := fun e le hp => ∃ _ : s.len = max, ∃ _ : s.cntF s.len = 1,
          LocalSt (envOf bh bc bo)
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
              codes root max mtch
              { s with cntF := fun j => if j = s.len then s.cntF s.len - 1
                                        else s.cntF j })
            (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
              workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
              extraF baseF Hrest
              (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j)
              s.offsF v0 v1 v2 s.vbits) e le hp,
        cont := R.cont, ret := R.ret, goto := R.goto } := by
  have hfrT : ∀ p ∈ TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx
      vb ty codes root max mtch s,
      p.1 ≠ _t'7 ∧ p.1 ≠ _t'17 ∧ p.1 ≠ _t'18 := by
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hbr := fun (cf : Nat → Nat) =>
    HLoop_as_Hadv bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
      workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
      Hrest cf s.offsF v0 v1 v2 s.vbits
  refine triple_conseq ge fe f_inflate_table
    (triple_seq_only ge fe f_inflate_table
      (count_dec_triple ge fe bh bc bo pw workB workO nwork workF pl lensB
        lensO ncodes lensF
        (HadvRest bh bo pt pb pr pg tblB tblO bitsB bitsO tB tO cap xB bB nx nb
          extraF baseF Hrest v0 v1 v2 s.vbits s.offsF)
        s.cntF hcb s.len hlen15 hcl
        (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb
          ty codes root max mtch s) _len
          (.Vint (Integers.Int.repr ((s.len : _root_.Int)))))
        (by simp +decide)
        (by intro p hp
            rcases List.mem_cons.mp hp with rfl | hp2
            · exact ⟨by show _len ≠ _t'18; decide,
                      by show _len ≠ _t'7; decide⟩
            · exact ⟨(hfrT p (mem_dropId hp2).1).2.2,
                     (hfrT p (mem_dropId hp2).1).1⟩))
      (adv_if_triple ge fe bh bc bo pw workB workO nwork workF pl lensB lensO
        ncodes lensF
        (HadvRest bh bo pt pb pr pg tblB tblO bitsB bitsO tB tO cap xB bB nx nb
          extraF baseF Hrest v0 v1 v2 s.vbits s.offsF)
        s.cntF s.len max s.sym hlen15 hcb hcl hmax15 hwb hlb hlens15 hlensmax
        hlenmax hn31 hnow hc31 hnol hpw hpl hsymlt hlenslt
        (dropId _len (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx
          vb ty codes root max mtch s))
        (by simp +decide) (by simp +decide) (by simp +decide) (by simp +decide)
        (fun p hp => (mem_dropId hp).2)
        (fun p hp => hfrT p (mem_dropId hp).1)
        R))
    (fun e le hp hx => ⟨hx.1, TempsHold_mono (by simp +decide) hx.2.1, by
       rw [← hbr s.cntF]; exact hx.2.2⟩)
    (fun e le hp hx => by
       obtain ⟨len', hle, hlm, hbrn, hst⟩ := hx
       exact ⟨len', hle, hlm, hbrn, hst.1,
         TempsHold_mono (by simp +decide) hst.2.1, by
         rw [hbr _]; exact hst.2.2⟩)
    (fun e le hp hx => by
       obtain ⟨heq, hone, hst⟩ := hx
       exact ⟨heq, hone, hst.1, TempsHold_mono (by simp +decide) hst.2.1, by
         rw [hbr _]; exact hst.2.2⟩)
    (fun _ _ _ x => x) (fun _ _ x => x)

/-! #### The sub-table branch's statements, lifted

All five take the heap opaquely (they touch no memory), so `heq := rfl` and only
the tracked list rotates — the same `setLocal`/`dropId` recipe as above. -/

/-- `if (drop == 0) drop = root;` — either way `drop` ends up `root`. -/
theorem loop_drop_init (s : LoopSt) (v0 v1 v2 : Val) (hdr : s.drop = 0 ∨ s.drop = root) (hd32 : s.drop < 4294967296) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar _drop tuint)
        (.Econst_int (Integers.Int.repr 0) tint) tint)
        (.Sset _drop (.Etempvar _root tuint)) .Sskip)
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with drop := root })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _drop (.Vint (Integers.Int.repr ((s.drop : _root_.Int)))))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _drop (.Vint (Integers.Int.repr ((root : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with drop := root })
    _ _ (by simp +decide) rfl _ _ ?_
  exact drop_init_triple ge fe bh bc bo
    (dropId _drop (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)) _
    s.drop root hdr hd32 (fun p hp => (mem_dropId hp).2) (by simp +decide)


/-- `curr = len - drop;` -/
theorem loop_curr_set (s : LoopSt) (v0 v1 v2 : Val) (hdl : s.drop ≤ s.len) (hl32 : s.len < 4294967296) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _curr (.Ebinop .Osub (.Etempvar _len tuint)
        (.Etempvar _drop tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with curr := s.len - s.drop })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _curr (.Vint (Integers.Int.repr ((s.curr : _root_.Int)))))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _curr (.Vint (Integers.Int.repr (((s.len - s.drop : Nat) : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with curr := s.len - s.drop })
    _ _ (by simp +decide) rfl _ _ ?_
  exact curr_set_triple ge fe bh bc bo
    (dropId _curr (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)) _
    s.len s.drop hdl hl32 (fun p hp => (mem_dropId hp).2) (by simp +decide)
    (by simp +decide) (.Vint (Integers.Int.repr ((s.curr : _root_.Int))))


/-- `left = (int)(1 << curr);` -/
theorem loop_left_init (s : LoopSt) (v0 v1 v2 : Val) (hc32 : s.curr < 32) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _left (.Ecast (.Ebinop .Oshl
        (.Econst_int (Integers.Int.repr 1) tint) (.Etempvar _curr tuint) tint)
        tint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with vl := Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int)) })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _left (.Vint s.vl))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _left (.Vint (Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with vl := Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int)) })
    _ _ (by simp +decide) rfl _ _ ?_
  exact left_init_triple ge fe bh bc bo
    (dropId _left (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)) _
    s.curr hc32 (fun p hp => (mem_dropId hp).2) (by simp +decide) (.Vint s.vl)


/-- `used += 1U << curr;` -/
theorem loop_used_add (s : LoopSt) (v0 v1 v2 : Val) (hc32 : s.curr < 32) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _used (.Ebinop .Oadd (.Etempvar _used tuint)
        (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
          (.Etempvar _curr tuint) tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with used := s.used + 2 ^ s.curr })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _used (.Vint (Integers.Int.repr ((s.used : _root_.Int)))))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _used (.Vint (Integers.Int.repr (((s.used + 2 ^ s.curr : Nat) : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with used := s.used + 2 ^ s.curr })
    _ _ (by simp +decide) rfl _ _ ?_
  exact used_add_triple ge fe bh bc bo
    (dropId _used (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)) _
    s.used s.curr hc32 (fun p hp => (mem_dropId hp).2) (by simp +decide)


/-- `low = huff & mask;`  with `mask = 2^root - 1`. -/
theorem loop_low_set (s : LoopSt) (v0 v1 v2 : Val) (hh32 : s.huff < 4294967296) (hr32 : root < 32) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _low (.Ebinop .Oand (.Etempvar _huff tuint)
        (.Etempvar _mask tuint) tuint))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
          { s with low := s.huff % 2 ^ root })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _low (.Vint (Integers.Int.repr ((s.low : _root_.Int)))))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s) _low (.Vint (Integers.Int.repr (((s.huff % 2 ^ root : Nat) : _root_.Int)))))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with low := s.huff % 2 ^ root })
    _ _ (by simp +decide) rfl _ _ ?_
  exact low_set_triple ge fe bh bc bo
    (dropId _low (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)) _
    s.huff root hh32 hr32 (fun p hp => (mem_dropId hp).2) (by simp +decide)
    (by simp +decide) (.Vint (Integers.Int.repr ((s.low : _root_.Int))))

/-! #### The three locals as freeable byte runs

Every `return` inside the loop frees the locals, so `triple_return` (and hence
`return_const_triple`, and hence `enough_LENS/DISTS_triple`) needs them as
`bytesPtsTo` runs of the right length.  In `HLoop` the same components are three
`mapsto`s and two `arrayU16`s.

No new CCLib lemma was needed: `arrayU16_bytes` (CCLib/Locals.lean:497) is
already an **equality** `arrayU16 p b ofs n f = bytesPtsTo b p ofs (u16Bytes f
n)`, and `codeCell_eq_bytes` (§16) does `here`. -/

/-- `HLoop` minus the three locals — what stays behind when a `return` frees
    them. -/
abbrev HenoughRest (vbits : Val) : HProp :=
  codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
  ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
     ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vbits
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
           ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
              ∗ (arrayU16 pg xB 0 nx extraF
                 ∗ (arrayU16 pg bB 0 nb baseF ∗ Hrest))))))

/-- **The three locals as freeable byte runs.**  This is the shape every
    `return` inside the loop needs, because `triple_return` has to `freeList`
    them.  `count`/`offs` come across by CCLib's `arrayU16_bytes` (an equality,
    not just an entailment) and `here` by `codeCell_eq_bytes`. -/
theorem HLoop_as_enough (cntF offsF : Nat → Nat) (v0 v1 v2 vbits : Val) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF v0 v1 v2 vbits
    = bytesPtsTo bh .Freeable 0 (hereRun v0 v1 v2)
      ∗ (bytesPtsTo bc .Freeable 0 (u16Bytes cntF 16)
         ∗ (bytesPtsTo bo .Freeable 0 (offsBytes offsF)
            ∗ HenoughRest pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
                workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
                extraF baseF Hrest vbits)) := by
  simp only [HLoop, HenoughRest, hereRun]
  rw [arrayU16_bytes .Freeable bc 0 cntF (by omega) 16,
      HoffsAt_bytes bo offsF,
      ← codeCell_eq_bytes .Freeable bh 0 (by omega) v0 v1 v2]
  try sep_cancel

/-- `next += min;` against the loop's tracked list.  Heap-opaque, so only the
    list rotates; `next_bump_addr` is what turns the resulting `idxOfs` into
    `LoopFacts.nOaddr`'s form at assembly time. -/
theorem loop_next_bump (s : LoopSt) (v0 v1 v2 : Val)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hmn31 : (s.mn : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned s.nO + 4 * (s.mn : _root_.Int)
             < 18446744073709551616) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sset _next (.Ebinop .Oadd
        (.Etempvar _next (tptr (Ty.Tstruct __1353 noattr)))
        (.Etempvar _min tuint) (tptr (Ty.Tstruct __1353 noattr))))
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch
          { s with nO := bumpOfs ge s.nO s.mn })
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  refine localst_adapt ge fe (envOf bh bc bo)
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
      codes root max mtch s) _next (.Vptr tB s.nO))
    _ _ (by simp +decide) rfl _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo)
    (setLocal (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
      codes root max mtch s) _next (.Vptr tB (bumpOfs ge s.nO s.mn)))
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch
      { s with nO := bumpOfs ge s.nO s.mn })
    _ _ (by simp +decide) rfl _ _ ?_
  exact next_bump_triple ge fe bh bc bo
    (dropId _next (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb
      ty codes root max mtch s)) _
    hcenv tB s.nO s.mn hmn31 hno (fun p hp => (mem_dropId hp).2)
    (by simp +decide)

/-- **The look-ahead loop against the loop's footprint.**  It reads only
    `count`, so `HLoop_as_Hlook` puts that in front and everything else rides in
    the tail; `_left` and `_curr` rotate to the head of the tracked list. -/
theorem loop_look_loop (s : LoopSt) (v0 v1 v2 : Val)
    (hcb : ∀ j, s.cntF j < 65536) (hmax15 : max ≤ 15)
    (hc1 : 1 ≤ s.curr) (hcm : s.curr + s.drop ≤ max)
    (hvl : s.vl = Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int)))
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      lookLoop
      { normal := fun e le hp => ∃ curr' : Nat, ∃ _ : 1 ≤ curr',
          ∃ _ : curr' + s.drop ≤ max, ∃ _ : s.curr ≤ curr',
          ∃ _ : curr' + s.drop = max
            ∨ 2 ^ curr' ≤ wsum s.cntF (s.curr + s.drop) (curr' - s.curr),
          ∃ vl' : Integers.Int,
          LocalSt (envOf bh bc bo)
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
              codes root max mtch { s with curr := curr', vl := vl' })
            (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
              workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
              extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits) e le hp,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  have hfr16 : ∀ p ∈ TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx
      vb ty codes root max mtch s, p.1 ≠ _t'16 := by
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hbr := HLoop_as_Hlook bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits
  have hv0 : s.vl = Integers.Int.repr
      (((2 ^ s.curr : Nat) : _root_.Int)
        - ((hsum s.cntF (s.curr + s.drop) (s.curr - s.curr) : Nat)
            : _root_.Int)) := by
    rw [hvl, Nat.sub_self,
        show hsum s.cntF (s.curr + s.drop) 0 = 0 from rfl]
    congr 1
  refine triple_conseq ge fe f_inflate_table
    (lookLoop_triple ge fe bh bc bo s.cntF s.drop max s.curr
      (dropId _left (dropId _curr
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)))
      (HlookRest bh bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest v0 v1 v2 s.vbits s.offsF)
      hcb hmax15 (fun p hp => (mem_dropId hp).2)
      (fun p hp => (mem_dropId (mem_dropId hp).1).2)
      (fun p hp => hfr16 p (mem_dropId (mem_dropId hp).1).1)
      (by simp +decide) (by simp +decide) R
      (max - (s.curr + s.drop)))
    (fun e le hp hx => ⟨s.curr, Nat.le_refl _, hcm, by omega,
      by rw [Nat.sub_self]; exact Nat.two_pow_pos _, hx.1,
      by rw [← hv0]; exact TempsHold_mono (by simp +decide) hx.2.1,
      by rw [← hbr]; exact hx.2.2⟩)
    (fun e le hp hx => by
      obtain ⟨curr', lv', hcc0', hcm', hexit, hst⟩ := hx
      exact ⟨curr', by omega, hcm', hcc0', hexit, lv', hst.1,
        TempsHold_mono (by simp +decide) hst.2.1, by rw [hbr]; exact hst.2.2⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- **The root back-pointer block against the loop's footprint.**  The whole
    table region and the `table` cell come to the front (`HLoop_as_backptr`);
    the tracked list is used as-is, since the block takes an arbitrary one. -/
theorem loop_backptr (s : LoopSt) (v0 v1 v2 : Val)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpt : permOrder pt .Readable = true)
    (hpr : permOrder pr .Writable = true)
    (hlow : s.low < cap) (hn31 : (cap : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
             < 18446744073709551616) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      backPtrBlock
      (.only (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))) := by
  have hbr := HLoop_as_backptr bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits
  refine localst_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun p hp => hp) hbr _ _ ?_
  refine localst_post_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun p hp => hp)
    hbr.symm _ _ ?_
  exact root_backptr_triple_forget ge fe bh bc bo hcenv pt pr hpt hpr tblB tblO
    tB tO s.nO cap s.low s.curr root hlow hn31 hno
    (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes root
      max mtch s)
    (HbpRest bh bc bo pb pw pl pg bitsB bitsO workB workO nwork workF lensB
      lensO ncodes lensF xB bB nx nb extraF baseF Hrest s.cntF s.offsF v0 v1 v2
      s.vbits)
    (by simp +decide) (by simp +decide) (by simp +decide) (by simp +decide)
    (by simp +decide)
    (by simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
        exact ⟨by decide, by decide, by decide, by decide, by decide,
               by decide, by decide, by decide, by decide, by decide,
               by decide, by decide, by decide, by decide, by decide,
               by decide, by decide, by decide, by decide, by decide,
               by decide, by decide, by decide, by decide⟩)

/-- **The ENOUGH check against the loop's footprint**, all three code types.

    LENS and DISTS return `1` when the table would not fit, so their footprint
    is the three locals as freeable byte runs (`HLoop_as_enough`); CODES has no
    check at all, which is why `hA5` — **assumption A5** — has to supply
    `used ≤ cap` on that path.  This is the only place A5 is consumed. -/
theorem loop_enough (s : LoopSt) (ea eb : Ident) (hab : ea ≠ eb)
    (hfr56 : ∀ p ∈ TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx
      vb ty codes root max mtch s, p.1 ≠ ea ∧ p.1 ≠ eb)
    (v0 v1 v2 : Val) (Ret : Val → HProp)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hu : s.used < 4294967296)
    (hty : ty = 0 ∨ ty = 1 ∨ ty = 2)
    -- `≤`, not `=`: A4 says the caller supplies *at least* ENOUGH, and the
    -- runtime check compares against the literal
    (hcapL : ty = 1 → 852 ≤ cap) (hcapD : ty = 2 → 592 ≤ cap)
    (hA5 : ty = 0 → s.used ≤ cap)
    (hret : ∀ hr, HenoughRest pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
        workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
        baseF Hrest s.vbits hr →
      Ret (.Vint (Integers.Int.repr 1)) hr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (enoughChk ea eb)
      { normal := fun e le hp => ∃ _ : s.used ≤ cap,
          LocalSt (envOf bh bc bo)
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
              codes root max mtch s)
            (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
              workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
              extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits) e le hp,
        brk := R.brk, cont := R.cont, ret := Ret, goto := R.goto } := by
  have hbr := HLoop_as_enough bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits
  rcases hty with h0 | h1 | h2
  · -- CODES: the check falls through; A5 supplies the bound
    subst h0
    refine triple_conseq ge fe f_inflate_table
      (enough_CODES_triple ge fe bh bc bo ea eb hab _ _ (by simp +decide)
        (fun p hp => (hfr56 p hp).1) (fun p hp => (hfr56 p hp).2)
        { normal := R.normal, brk := R.brk, cont := R.cont, ret := Ret,
          goto := R.goto })
      (fun _ _ _ x => x) (fun e le hp hx => ⟨hA5 rfl, hx⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  · -- LENS
    subst h1
    refine triple_conseq ge fe f_inflate_table
      (enough_LENS_triple ge fe bh bc bo _ ea eb hab hcenv hd1 hd2 hd3
        (hereRun v0 v1 v2) (u16Bytes s.cntF 16) (offsBytes s.offsF)
        (hereRun_length v0 v1 v2) (u16Bytes_length s.cntF 16)
        (offsBytes_length s.offsF) _ s.used hu (by simp +decide)
        (by simp +decide) (fun p hp => (hfr56 p hp).1)
        (fun p hp => (hfr56 p hp).2) Ret hret)
      (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hbr]; exact hx.2.2⟩)
      (fun e le hp hx => by
        obtain ⟨hle, lx, hsub, hst⟩ := hx
        exact ⟨Nat.le_trans hle (hcapL rfl), hst.1,
          TempsHold_mono hsub hst.2.1, by rw [hbr]; exact hst.2.2⟩)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ x => x)
  · -- DISTS
    subst h2
    refine triple_conseq ge fe f_inflate_table
      (enough_DISTS_triple ge fe bh bc bo _ ea eb hab hcenv hd1 hd2 hd3
        (hereRun v0 v1 v2) (u16Bytes s.cntF 16) (offsBytes s.offsF)
        (hereRun_length v0 v1 v2) (u16Bytes_length s.cntF 16)
        (offsBytes_length s.offsF) _ s.used hu (by simp +decide)
        (by simp +decide) (fun p hp => (hfr56 p hp).1)
        (fun p hp => (hfr56 p hp).2) Ret hret)
      (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hbr]; exact hx.2.2⟩)
      (fun e le hp hx => by
        obtain ⟨hle, lx, hsub, hst⟩ := hx
        exact ⟨Nat.le_trans hle (hcapD rfl), hst.1,
          TempsHold_mono hsub hst.2.1, by rw [hbr]; exact hst.2.2⟩)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ x => x)

/-! #### The eleventh link: the sub-table branch

`loop_subtable` chains §22's statements, §21's look-ahead loop, the ENOUGH check
and §19's back-pointer block in AST order; `loop_subtable_if` puts the guard on
top.  Its postcondition is uniform across the two branches — whatever happened,
the state still satisfies the four `LoopFacts` clauses this branch can disturb —
which is what lets the loop invariant consume it without a case split.

**With this every statement of the loop body has a lifted triple.** -/

/-- **The sub-table transition, whole.**  The last of the eleven chain links:
    §22's statements, §21's look-ahead loop, the ENOUGH check and §19's
    back-pointer block, in AST order. -/
theorem loop_subtable (s : LoopSt) (v0 v1 v2 : Val) (Ret : Val → HProp)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hpt : permOrder pt .Readable = true)
    (hpr : permOrder pr .Writable = true)
    (hdr : s.drop = 0 ∨ s.drop = root) (hd32 : s.drop < 4294967296)
    (hrl : root < s.len) (hlmax : s.len ≤ max) (hmax15 : max ≤ 15)
    (hr32 : root < 32) (hh32 : s.huff < 4294967296)
    (hcb : ∀ j, s.cntF j < 65536)
    (hmn31 : (s.mn : _root_.Int) < 2147483648)
    (hnoN : Integers.Ptrofs.unsigned s.nO + 4 * (s.mn : _root_.Int)
              < 18446744073709551616)
    (hn31 : (cap : _root_.Int) < 2147483648)
    (hnoC : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
              < 18446744073709551616)
    (hlowcap : s.huff % 2 ^ root < cap)
    (huc : ∀ c : Nat, c ≤ 15 → s.used + 2 ^ c < 4294967296)
    (hty : ty = 0 ∨ ty = 1 ∨ ty = 2)
    -- `≤`, not `=`: A4 says the caller supplies *at least* ENOUGH, and the
    -- runtime check compares against the literal
    (hcapL : ty = 1 → 852 ≤ cap) (hcapD : ty = 2 → 592 ≤ cap)
    -- **A5, in a satisfiable form.**  `∀ u : Nat, ty = 0 → u ≤ cap` is false;
    -- what A5-CODES actually gives is that for CODES no code is longer than the
    -- root table, i.e. `root = max`, which makes this branch unreachable.
    (hA5 : ty = 0 → max ≤ root)
    (hret : ∀ hr, HenoughRest pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
        workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
        baseF Hrest s.vbits hr →
      Ret (.Vint (Integers.Int.repr 1)) hr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      subTableBody
      { normal := fun e le hp => ∃ curr' : Nat, ∃ vl' : Integers.Int,
          ∃ _ : 1 ≤ curr', ∃ _ : curr' + root ≤ max,
          ∃ _ : s.used + 2 ^ curr' ≤ cap,
          ∃ _ : s.len - root ≤ curr',
          ∃ _ : curr' + root = max
                ∨ 2 ^ curr' ≤ wsum s.cntF s.len (curr' - (s.len - root)),
          LocalSt (envOf bh bc bo)
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
              codes root max mtch
              { s with drop := root, nO := bumpOfs ge s.nO s.mn,
                       curr := curr', vl := vl',
                       used := s.used + 2 ^ curr',
                       low := s.huff % 2 ^ root })
            (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
              workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
              extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits) e le hp,
        brk := R.brk, cont := R.cont, ret := Ret, goto := R.goto } := by
  have hrle : root ≤ s.len := by omega
  -- drop := root
  refine triple_seq_only ge fe f_inflate_table
    (loop_drop_init ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest s v0 v1 v2 hdr hd32) ?_
  -- next += min
  refine triple_seq_only ge fe f_inflate_table
    (loop_next_bump ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest { s with drop := root } v0 v1 v2
      hcenv hmn31 hnoN) ?_
  -- curr := len - drop
  refine triple_seq_only ge fe f_inflate_table
    (loop_curr_set ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest
      { s with drop := root, nO := bumpOfs ge s.nO s.mn } v0 v1 v2 hrle
      (by show s.len < 4294967296; omega)) ?_
  -- left := 1 << curr
  refine triple_seq_only ge fe f_inflate_table
    (loop_left_init ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest
      { s with drop := root, nO := bumpOfs ge s.nO s.mn,
               curr := s.len - root } v0 v1 v2
      (by show s.len - root < 32; omega)) ?_
  -- the look-ahead loop
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (loop_look_loop ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest
      { s with drop := root, nO := bumpOfs ge s.nO s.mn,
               curr := s.len - root,
               vl := Integers.Int.repr (((2 ^ (s.len - root) : Nat)
                       : _root_.Int)) }
      v0 v1 v2 hcb hmax15 (by show 1 ≤ s.len - root; omega)
      (by show s.len - root + root ≤ max; omega) rfl
      { normal := R.normal, brk := R.brk, cont := R.cont, ret := Ret,
        goto := R.goto }) ?_
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (curr' : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hc1 : 1 ≤ curr') => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hcm : curr' + root ≤ max) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hlc : s.len - root ≤ curr') => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hexit : curr' + root = max
      ∨ 2 ^ curr' ≤ wsum s.cntF (s.len - root + root)
          (curr' - (s.len - root))) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (vl' : Integers.Int) => ?_)
  -- used += 1 << curr
  refine triple_seq_only ge fe f_inflate_table
    (loop_used_add ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest
      { s with drop := root, nO := bumpOfs ge s.nO s.mn, curr := curr',
               vl := vl' } v0 v1 v2 (by show curr' < 32; omega)) ?_
  -- the ENOUGH check
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (loop_enough ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO
      cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF
      baseF ty codes root max mtch Hrest
      { s with drop := root, nO := bumpOfs ge s.nO s.mn, curr := curr',
               vl := vl', used := s.used + 2 ^ curr' } _t'8 _t'9 (by decide)
      (by simp only [List.cons_append, List.nil_append, List.forall_mem_cons]
          exact ⟨by decide, by decide, by decide, by decide, by decide,
                 by decide, by decide, by decide, by decide, by decide,
                 by decide, by decide, by decide, by decide, by decide,
                 by decide, by decide, by decide, by decide, by decide,
                 by decide, by decide, by decide, by decide⟩)
      v0 v1 v2 Ret hcenv hd1
      hd2 hd3 (by show s.used + 2 ^ curr' < 4294967296
                  exact huc curr' (by omega)) hty hcapL hcapD
      (fun h0 => absurd (hA5 h0) (by omega)) hret
      { normal := R.normal, brk := R.brk, cont := R.cont, ret := Ret,
        goto := R.goto }) ?_
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hcapok : s.used + 2 ^ curr' ≤ cap) => ?_)
  -- low := huff & mask
  refine triple_seq_only ge fe f_inflate_table
    (loop_low_set ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO
      cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF
      baseF ty codes root max mtch Hrest
      { s with drop := root, nO := bumpOfs ge s.nO s.mn, curr := curr',
               vl := vl', used := s.used + 2 ^ curr' } v0 v1 v2 hh32 hr32) ?_
  -- the root back-pointer writes
  refine triple_conseq ge fe f_inflate_table
    (loop_backptr ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO
      cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF
      baseF ty codes root max mtch Hrest
      { s with drop := root, nO := bumpOfs ge s.nO s.mn, curr := curr',
               vl := vl', used := s.used + 2 ^ curr',
               low := s.huff % 2 ^ root } v0 v1 v2 hcenv hpt hpr hlowcap hn31
      hnoC)
    (fun _ _ _ x => x)
    (fun e le hp hx => ⟨curr', vl', hc1, hcm, hcapok, hlc,
      by rwa [show s.len - root + root = s.len from by omega] at hexit, hx⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-- The sub-table branch, guard and all — `if (len > root && (huff & mask) !=
    low) { … }` with `_t'10` already computed by `loop_t10_set`.

    **This completes the eleventh and last chain link.**  The postcondition is
    uniform across the two branches: whatever happened, the loop state still
    satisfies the four clauses of `LoopFacts` that this branch can disturb. -/
theorem loop_subtable_if (s : LoopSt) (v0 v1 v2 : Val) (Ret : Val → HProp)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hpt : permOrder pt .Readable = true)
    (hpr : permOrder pr .Writable = true)
    (hdr : s.drop = 0 ∨ s.drop = root) (hd32 : s.drop < 4294967296)
    (hlmax : s.len ≤ max) (hmax15 : max ≤ 15)
    (hr32 : root < 32) (hh32 : s.huff < 4294967296)
    (hcb : ∀ j, s.cntF j < 65536)
    (hmn31 : (s.mn : _root_.Int) < 2147483648)
    (hnoN : Integers.Ptrofs.unsigned s.nO + 4 * (s.mn : _root_.Int)
              < 18446744073709551616)
    (hn31 : (cap : _root_.Int) < 2147483648)
    (hnoC : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
              < 18446744073709551616)
    (hlowcap : s.huff % 2 ^ root < cap)
    (huc : ∀ c : Nat, c ≤ 15 → s.used + 2 ^ c < 4294967296)
    (hty : ty = 0 ∨ ty = 1 ∨ ty = 2)
    -- `≤`, not `=`: A4 says the caller supplies *at least* ENOUGH, and the
    -- runtime check compares against the literal
    (hcapL : ty = 1 → 852 ≤ cap) (hcapD : ty = 2 → 592 ≤ cap)
    -- **A5, in a satisfiable form.**  `∀ u : Nat, ty = 0 → u ≤ cap` is false;
    -- what A5-CODES actually gives is that for CODES no code is longer than the
    -- root table, i.e. `root = max`, which makes this branch unreachable.
    (hA5 : ty = 0 → max ≤ root)
    -- the invariant clauses the *skip* branch has to hand back unchanged
    (hc1s : 1 ≤ s.curr) (hcms : s.curr + s.drop ≤ max) (hus : s.used ≤ cap)
    (hret : ∀ hr, HenoughRest pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
        workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
        baseF Hrest s.vbits hr →
      Ret (.Vint (Integers.Int.repr 1)) hr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_t'10, .Vint (Integers.Int.repr
            (((if root < s.len ∧ s.huff % 2 ^ root ≠ s.low then 1 else 0 : Nat))
              : _root_.Int)))
          :: TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
               codes root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF v0 v1 v2 s.vbits))
      (.Sifthenelse (.Etempvar _t'10 tint) subTableBody .Sskip)
      { normal := fun e le hp =>
          ∃ drop' curr' used' low' : Nat, ∃ vl' : Integers.Int,
          ∃ nO' : Integers.Ptrofs,
          ∃ _ : 1 ≤ curr', ∃ _ : curr' + drop' ≤ max, ∃ _ : used' ≤ cap,
          ∃ _ : drop' = 0 ∨ drop' = root,
          ∃ _ : (drop' = s.drop ∧ curr' = s.curr ∧ used' = s.used
                  ∧ low' = s.low ∧ nO' = s.nO
                  ∧ ¬(root < s.len ∧ s.huff % 2 ^ root ≠ s.low))
                ∨ (root < s.len ∧ s.huff % 2 ^ root ≠ s.low
                  ∧ drop' = root ∧ low' = s.huff % 2 ^ root
                  ∧ used' = s.used + 2 ^ curr'
                  ∧ s.len - root ≤ curr'
                  ∧ (curr' + root = max
                      ∨ 2 ^ curr' ≤ wsum s.cntF s.len (curr' - (s.len - root)))
                  ∧ Integers.Ptrofs.unsigned nO'
                      = Integers.Ptrofs.unsigned s.nO
                        + 4 * ((s.mn : Nat) : _root_.Int)),
          LocalSt (envOf bh bc bo)
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
              codes root max mtch
              { s with drop := drop', nO := nO', curr := curr', vl := vl',
                       used := used', low := low' })
            (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
              workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
              extraF baseF Hrest s.cntF s.offsF v0 v1 v2 s.vbits) e le hp,
        brk := R.brk, cont := R.cont, ret := Ret, goto := R.goto } := by
  by_cases hg : root < s.len ∧ s.huff % 2 ^ root ≠ s.low
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · refine ⟨.Vint (Integers.Int.repr
          (((if root < s.len ∧ s.huff % 2 ^ root ≠ s.low then 1 else 0 : Nat))
            : _root_.Int)),
        EvalExpr.Etempvar _t'10 tint _ (hT'.get List.mem_cons_self), ?_⟩
      simp only [typeof]
      rw [boolVal_vint,
          show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
          eq_nat32 _ 0 (by rw [if_pos hg]; omega) (by omega),
          show (if root < s.len ∧ s.huff % 2 ^ root ≠ s.low then 1 else 0 : Nat)
            = 1 from by rw [if_pos hg]]
      rfl
    · refine triple_conseq ge fe f_inflate_table
        (localst_adapt ge fe (envOf bh bc bo) _
          (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
            codes root max mtch s) _ _
          (fun p hp => List.mem_cons_of_mem _ hp) rfl _ _
          (loop_subtable ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
            tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx
            nb extraF baseF ty codes root max mtch Hrest s v0 v1 v2 Ret hcenv
            hd1 hd2 hd3 hpt hpr hdr hd32 hg.1 hlmax hmax15 hr32 hh32 hcb hmn31
            hnoN hn31 hnoC hlowcap huc hty hcapL hcapD hA5 hret R))
        (fun _ _ _ x => x)
        (fun e le hp hx => by
          obtain ⟨curr', vl', hc1, hcm, hcapok, hlc, hexit, hst⟩ := hx
          exact ⟨root, curr', s.used + 2 ^ curr', s.huff % 2 ^ root, vl',
            bumpOfs ge s.nO s.mn, hc1, hcm, hcapok, Or.inr rfl,
            Or.inr ⟨hg.1, hg.2, rfl, rfl, rfl, hlc, hexit,
              next_bump_addr ge hcenv s.nO s.mn hmn31 hnoN⟩, hst⟩)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  · refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · refine ⟨.Vint (Integers.Int.repr
          (((if root < s.len ∧ s.huff % 2 ^ root ≠ s.low then 1 else 0 : Nat))
            : _root_.Int)),
        EvalExpr.Etempvar _t'10 tint _ (hT'.get List.mem_cons_self), ?_⟩
      simp only [typeof]
      rw [boolVal_vint,
          show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
          eq_nat32 _ 0 (by rw [if_neg hg]; omega) (by omega),
          show (if root < s.len ∧ s.huff % 2 ^ root ≠ s.low then 1 else 0 : Nat)
            = 0 from by rw [if_neg hg]]
      rfl
    · refine triple_conseq ge fe f_inflate_table
        (triple_skip ge fe f_inflate_table _)
        (fun _ _ _ x => x)
        (fun e le hp hx => ⟨s.drop, s.curr, s.used, s.low, s.vl, s.nO, hc1s,
          hcms, hus, hdr, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hg⟩, hx.1,
          TempsHold_mono (by simp +decide) hx.2.1, hx.2.2⟩)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! #### Closing the loop

`LoopEnv` bundles everything about the environment that does not change across
the loop, so the eleven links do not each need twenty hypotheses threaded by
hand.  Note it must be *applied* explicitly when used as a binder type —
section variables are auto-applied to the declaration being elaborated, not to
a structure mentioned in one of its binders.

`body_prefix` is a staging post: it checks that `LoopInv`'s two binders peel
and that the first link threads.  The remaining ten links follow the same
shape; what is *not* mechanical is the final step, re-establishing `LoopInv` at
a smaller measure — that is I2, which rests on the reversed-code mass model of
InflateTableInvariants.lean (`Model.subfit_from_look`). -/

/-- Everything about the environment that does not change across the loop:
    gathered once so the eleven links do not each need twenty hypotheses. -/
structure LoopEnv : Prop where
  hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env
  hd1 : bh ≠ bc
  hd2 : bh ≠ bo
  hd3 : bc ≠ bo
  hpt : permOrder pt .Readable = true
  hptW : permOrder pt .Writable = true
  hpb : permOrder pb .Writable = true
  hpr : permOrder pr .Writable = true
  hpw : permOrder pw .Readable = true
  hpl : permOrder pl .Readable = true
  hpg : permOrder pg .Readable = true
  hwb : ∀ j, workF j < 65536
  hlb : ∀ j, lensF j < 65536
  hlens15 : ∀ j, lensF j ≤ 15
  hlensmax : ∀ j, lensF j ≤ max
  hxb : ∀ j, extraF j < 65536
  hbb : ∀ j, baseF j < 65536
  hn31 : (nwork : _root_.Int) < 2147483648
  hnow : Integers.Ptrofs.unsigned workO + 2 * (nwork : _root_.Int)
           < 18446744073709551616
  hc31 : (ncodes : _root_.Int) < 2147483648
  hnol : Integers.Ptrofs.unsigned lensO + 2 * (ncodes : _root_.Int)
           < 18446744073709551616
  hnx31 : (nx : _root_.Int) < 2147483648
  hnb31 : (nb : _root_.Int) < 2147483648
  hm32 : mtch < 4294967296
  hcap31 : (cap : _root_.Int) < 2147483648
  hnoC : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
           < 18446744073709551616
  htO4 : Integers.Ptrofs.unsigned tO % 4 = 0
  hmax15 : max ≤ 15
  hroot15 : root ≤ 15
  hroot1 : 1 ≤ root
  hr32 : root < 32
  hty : ty = 0 ∨ ty = 1 ∨ ty = 2
  hcapL : ty = 1 → 852 ≤ cap
  hcapD : ty = 2 → 592 ≤ cap

/-- The loop body, up to `entryChoose`.  A staging post while the full chain is
    assembled: it checks that `LoopInv`'s two binders peel and that the first
    links thread. -/
theorem body_prefix
    (henv : LoopEnv ge bh bc bo pt pb pr pw pl pg tO cap workO nwork workF
      lensO ncodes lensF nx nb extraF baseF ty root max mtch)
    (n : Nat) :
    Triple ge fe f_inflate_table
      (LoopInv bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
        codes root max mtch nlive Hrest n)
      (.Ssequence .Sskip entryBitsStmt)
      (.only (fun e le hp => ∃ s : LoopSt,
        ∃ _ : LoopFacts n max root nwork ncodes nx nb mtch nlive cap workF lensF tO s,
        LocalSt (envOf bh bc bo)
          (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
            root max mtch s)
          (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
            workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
            baseF Hrest s.cntF s.offsF s.v0
            (.Vint (Integers.Int.repr
              ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) s.v2 s.vbits)
          e le hp)) := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (s : LoopSt) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hf : LoopFacts n max root nwork ncodes nx nb mtch nlive cap workF lensF tO
      s) => ?_)
  refine triple_seq_only ge fe f_inflate_table
    (triple_skip ge fe f_inflate_table _) ?_
  refine triple_conseq ge fe f_inflate_table
    (loop_entry_bits ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest henv.hcenv s hf.droplen
      hf.len15)
    (fun _ _ _ x => x) (fun e le hp hx => ⟨s, hf, hx⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! #### The loop body statement, its exit, and the state it leaves

`loopBody` is the `Sloop`'s first slot, exactly as the AST associates it.
`LoopExit` is the `break` out of `advIfStmt` — the loop's only way out — and
`BodyPost` records the state one pass leaves behind.  Turning `BodyPost` into
`LoopInv n'` is the I2 step; the chain from `LoopInv n` to `BodyPost` is what
the eleven links compose to. -/

abbrev loopBody : Stmt :=
  .Ssequence .Sskip
    (.Ssequence entryBitsStmt
      (.Ssequence entryChoose
        (.Ssequence
          (.Sset _incr (.Ebinop .Oshl (.Econst_int (Integers.Int.repr 1) tuint)
            (.Ebinop .Osub (.Etempvar _len tuint) (.Etempvar _drop tuint) tuint)
            tuint))
          (.Ssequence
            (.Sset _fill (.Ebinop .Oshl
              (.Econst_int (Integers.Int.repr 1) tuint)
              (.Etempvar _curr tuint) tuint))
            (.Ssequence (.Sset _min (.Etempvar _fill tuint))
              (.Ssequence fillLoop
                (.Ssequence incrInit (.Ssequence incrLoop (.Ssequence incrFix
                  (.Ssequence symIncrStmt
                    (.Ssequence (.Ssequence countDecStmt advIfStmt)
                      (.Ssequence t10Stmt
                        (.Sifthenelse (.Etempvar _t'10 tint) subTableBody
                          .Sskip)))))))))))))

/-- The loop's normal exit: `break` out of `advIfStmt`, with `len = max`. -/
def LoopExit : Sep.Assn := fun e le hp =>
  ∃ s : LoopSt, ∃ w0 w1 w2 : Val,
  ∃ _ : ExitFacts max root cap nlive workF lensF tO s,
    LocalSt (envOf bh bc bo) (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s) (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF w0 w1 w2 s.vbits)
      e le hp

/-- The state the body leaves behind.  Turning this into `LoopInv n'` is the
    I2 step; the chain itself is what this records. -/
def BodyPost (s : LoopSt) : Sep.Assn := fun e le hp =>
  ∃ op val len' drop' curr' used' low' : Nat, ∃ vi' : Val,
  ∃ vl' : Integers.Int, ∃ nO' : Integers.Ptrofs,
  ∃ _ : op < 256, ∃ _ : val < 65536, ∃ _ : len' ≤ 15, ∃ _ : len' ≤ max,
  ∃ _ : 1 ≤ curr', ∃ _ : curr' + drop' ≤ max, ∃ _ : used' ≤ cap,
  ∃ _ : drop' = 0 ∨ drop' = root,
  -- which way the symbol advance went
  ∃ _ : (len' = s.len ∧ 2 ≤ s.cntF s.len)
        ∨ (s.cntF s.len = 1 ∧ s.len ≠ max ∧ len' = lensF (workF (s.sym + 1))),
  -- which way the sub-table branch went (the guard reads the *advanced* state)
  ∃ _ : (drop' = s.drop ∧ curr' = s.curr ∧ used' = s.used ∧ low' = s.low
          ∧ nO' = s.nO
          ∧ ¬(root < len' ∧ bwInc s.huff s.len % 2 ^ root ≠ s.low))
        ∨ (root < len' ∧ bwInc s.huff s.len % 2 ^ root ≠ s.low
          ∧ drop' = root ∧ low' = bwInc s.huff s.len % 2 ^ root
          ∧ used' = s.used + 2 ^ curr'
          ∧ len' - root ≤ curr'
          ∧ (curr' + root = max
              ∨ 2 ^ curr' ≤ wsum
                  (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j)
                  len' (curr' - (len' - root)))
          ∧ Integers.Ptrofs.unsigned nO' = Integers.Ptrofs.unsigned s.nO
              + 4 * (((2 ^ s.curr : Nat)) : _root_.Int)),
    LocalSt (envOf bh bc bo)
      (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
            root max mtch
        { s with v0 := .Vint (Integers.Int.repr ((op : _root_.Int))),
                 v1 := .Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int))),
                 v2 := .Vint (Integers.Int.repr ((val : _root_.Int))),
                 vi := vi', vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))), mn := 2 ^ s.curr,
                 huff := bwInc s.huff s.len, sym := s.sym + 1,
                 len := len', cntF := (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j),
                 drop := drop', nO := nO', curr := curr', vl := vl',
                 used := used', low := low' })
      (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
            workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
            baseF Hrest (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j) s.offsF
        (.Vint (Integers.Int.repr ((op : _root_.Int))))
        (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int))))
        (.Vint (Integers.Int.repr ((val : _root_.Int)))) s.vbits) e le hp

/-- **The loop body, chained.**  Eleven links from `LoopInv n` to `BodyPost s`;
    `break` out of `advIfStmt` is the loop's only exit. -/
theorem loop_body_triple
    (henv : LoopEnv ge bh bc bo pt pb pr pw pl pg tO cap workO nwork workF
      lensO ncodes lensF nx nb extraF baseF ty root max mtch)
    (hwc : WorkChar nwork ncodes nlive max mtch nx nb workF lensF vx vb xB bB)
    (Ret : Val → HProp)
    (hret : ∀ (s : LoopSt) hr, HenoughRest pt pb pr pw pl pg tblB tblO bitsB
        bitsO tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB
        nx nb extraF baseF Hrest s.vbits hr →
      Ret (.Vint (Integers.Int.repr 1)) hr)
    -- **Two facts about the fixed parameters**, replacing seven hypotheses that
    -- were quantified over *all* `LoopSt` — a record with unconstrained `Nat`
    -- fields, so those were false and the lemma was vacuous.  Everything the
    -- body needs about the *current* state is derived from `hf`/`henv` below.
    (hrootcap : 2 ^ root ≤ cap)
    (hA5 : ty = 0 → max ≤ root)
    (n : Nat) (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LoopInv bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
        codes root max mtch nlive Hrest n)
      loopBody
      { normal := fun e le hp => ∃ s : LoopSt,
          ∃ _ : LoopFacts n max root nwork ncodes nx nb mtch nlive cap workF
            lensF tO s,
          BodyPost bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
            workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF
            baseF ty codes root max mtch Hrest s e le hp,
        brk := LoopExit bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO
          cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
          extraF baseF ty codes root max mtch nlive Hrest,
        cont := Assn.no, ret := Ret, goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (s : LoopSt) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hf : LoopFacts n max root nwork ncodes nx nb mtch nlive cap workF lensF tO
      s) => ?_)
  have hcurr15 : s.curr ≤ 15 := by have := hf.currmax; have := hf.max15; omega
  have hd32 : s.drop < 32 := by
    have := hf.droplen; have := hf.len15; omega
  -- Sskip
  refine triple_seq_only ge fe f_inflate_table
    (triple_skip ge fe f_inflate_table _) ?_
  -- here.bits
  refine triple_seq_only ge fe f_inflate_table
    (loop_entry_bits ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest henv.hcenv s hf.droplen hf.len15) ?_
  -- the entry if/else if/else
  refine triple_seq_only ge fe f_inflate_table
    (loop_entry_choose ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest henv.hcenv henv.hpw henv.hwb henv.hpg henv.hxb
      henv.hbb henv.hn31 henv.hnow henv.hnx31 henv.hnb31 henv.hm32 s
      (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) hf.symlt hf.a3x hf.a3b
      (hwc.hvx s.sym hf.symlive) (hwc.hvb s.sym hf.symlive)) ?_
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (op : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (val : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (hop : op < 256) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hval : val < 65536) => ?_)
  -- incr = 1U << (len - drop)
  refine triple_seq_only ge fe f_inflate_table
    (loop_incr_set ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest s (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int)))) hf.droplen hf.len15) ?_
  -- fill = 1U << curr
  refine triple_seq_only ge fe f_inflate_table
    (loop_fill_set ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest { s with vi := .Vint (Integers.Int.repr (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))) } (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int)))) (by show s.curr < 32; omega)) ?_
  -- min = fill
  refine triple_seq_only ge fe f_inflate_table
    (loop_min_set ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest { s with vi := .Vint (Integers.Int.repr (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))), vf := .Vint (Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int))) } (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int)))) (2 ^ s.curr) rfl) ?_
  -- the fill loop
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (loop_fill_loop ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest { s with vi := .Vint (Integers.Int.repr (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))), vf := .Vint (Integers.Int.repr (((2 ^ s.curr : Nat) : _root_.Int))), mn := 2 ^ s.curr } op ((s.len - s.drop) % 256) val s.nOff rfl rfl
      henv.hcenv henv.hpr henv.htO4 henv.hnoC hf.room hf.nOaddr
      (by show s.curr ≤ 15; omega) (by show s.len - s.drop ≤ s.curr
                                       exact hf.lmdcurr)
      (by show s.drop < 32; omega)
      (by show s.huff / 2 ^ s.drop < 2 ^ (s.len - s.drop)
          exact huff_shr_lt s.huff s.len s.drop hf.droplen hf.hufflt)
      (by show s.huff < 4294967296
          have h1 := hf.hufflt
          have h2 : (2 : Nat) ^ s.len ≤ 2 ^ 15 :=
            Nat.pow_le_pow_right (by omega) hf.len15
          omega)
      { normal := R.normal, brk := LoopExit bh bc bo pt pb pr pw pl pg tblB
           tblO bitsB bitsO tB tO cap workB workO nwork workF lensB lensO ncodes
           lensF xB bB vx vb nx nb extraF baseF ty codes root max mtch nlive Hrest,
         cont := Assn.no, ret := Ret, goto := R.goto }) ?_
  -- the backwards code increment: three flat slots, as clightgen emits them
  refine triple_seq_only ge fe f_inflate_table
    (loop_incr_init ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest { s with vi := .Vint (Integers.Int.repr (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))), vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))), mn := 2 ^ s.curr } (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int))))
      (by show 1 ≤ s.len; exact hf.len1)
      (by show s.len ≤ 15; exact hf.len15)) ?_
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (loop_incr_loop ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest { s with vi := .Vint (Integers.Int.repr (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))), vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))), mn := 2 ^ s.curr } (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int))))
      (by show s.huff < 4294967296
          have h1 := hf.hufflt
          have h2 : (2 : Nat) ^ s.len ≤ 2 ^ 15 :=
            Nat.pow_le_pow_right (by omega) hf.len15
          omega)
      (by show s.len ≤ 15; exact hf.len15)
      { normal := R.normal, brk := LoopExit bh bc bo pt pb pr pw pl pg tblB
           tblO bitsB bitsO tB tO cap workB workO nwork workF lensB lensO ncodes
           lensF xB bB vx vb nx nb extraF baseF ty codes root max mtch nlive Hrest,
         cont := Assn.no, ret := Ret, goto := R.goto }) ?_
  refine triple_seq_only ge fe f_inflate_table
    (loop_incr_fix ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest { s with vi := .Vint (Integers.Int.repr (((2 ^ (s.len - s.drop) : Nat) : _root_.Int))), vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))), mn := 2 ^ s.curr } (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int))))
      (by show s.huff < 4294967296
          have h1 := hf.hufflt
          have h2 : (2 : Nat) ^ s.len ≤ 2 ^ 15 :=
            Nat.pow_le_pow_right (by omega) hf.len15
          omega)
      (by show s.len ≤ 15; exact hf.len15)) ?_
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (vi' : Val) => ?_)
  -- sym++
  refine triple_seq_only ge fe f_inflate_table
    (loop_sym_incr ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest { s with vi := vi', vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))), mn := 2 ^ s.curr, huff := bwInc s.huff s.len } (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int))))
      (by show s.sym < 4294967295
          have h1 := hf.symlt
          have h2 := henv.hn31
          omega)) ?_
  -- --count[len]; and the length step (the loop's only exit is its `break`)
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (loop_count_dec_adv ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest
        { s with vi := vi', vf := (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))), mn := 2 ^ s.curr, huff := bwInc s.huff s.len, sym := s.sym + 1 }
        (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int))))
        (by show ∀ j, s.cntF j < 65536; exact hf.cntb)
        (by show 1 ≤ s.cntF s.len; exact hf.cnt1)
        (by show s.len ≤ 15; exact hf.len15) henv.hmax15 henv.hwb henv.hlb
        henv.hlens15 henv.hlensmax (by show s.len ≤ max; exact hf.lenmax)
        henv.hn31 henv.hnow henv.hc31 henv.hnol henv.hpw henv.hpl
        (by show s.cntF s.len = 1 → s.len ≠ max → s.sym + 1 < nwork
            exact hf.symnext)
        (by show s.cntF s.len = 1 → s.len ≠ max → workF (s.sym + 1) < ncodes
            exact hf.lensnext)
        { normal := R.normal, brk := LoopExit bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO
           cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
           extraF baseF ty codes root max mtch nlive Hrest,
           cont := Assn.no, ret := Ret, goto := R.goto })
      (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun e le hp hx => by
        obtain ⟨heq, hone, hst⟩ := hx
        -- the break IS the last symbol: sortedness leaves nothing longer
        have hg : lensF (workF s.sym) = max := by rw [← hf.lenw]; exact heq
        have hcs : s.cntF s.len
            = cntSeg (fun k => lensF (workF k)) s.sym nlive s.len :=
          hf.cntc s.len hf.len1
        have hsymall : s.sym + 1 = nlive := by
          refine sym_last_of_count_one (fun k => lensF (workF k)) s.sym nlive max
            hwc.hsort hf.symlive (fun k hk => hwc.hlmax k hk) hg ?_
          rw [← heq]; rw [hcs] at hone; exact hone
        refine ⟨{ s with vi := vi', vf := (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))), mn := 2 ^ s.curr, huff := bwInc s.huff s.len, sym := s.sym + 1, cntF := (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j) }, (.Vint (Integers.Int.repr ((op : _root_.Int)))), (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))), (.Vint (Integers.Int.repr ((val : _root_.Int)))), ?_, hst⟩
        exact {
          lenmax := by show s.len = max; exact heq
          hufflt := by
            show bwInc s.huff s.len < 2 ^ max
            rw [← heq]; exact bwInc_lt s.huff s.len hf.hufflt
          hzero := by
            show bwInc s.huff s.len ≠ 0 →
              massBelow (fun k => lensF (workF k)) nlive < 2 ^ 15
            intro hne
            rw [← hsymall]
            exact mass_lt_of_bwInc_ne_zero (fun k => lensF (workF k)) s.sym
              s.len s.huff hf.len15 hf.lenw.symm hf.hJ hne
          droproot := hf.droproot
          dropfired := hf.dropfired
          dzoff := hf.dzoff
          dzcurr := hf.dzcurr
          room := hf.room
          usedcap := hf.usedcap
          -- the count of the exhausted length was decremented, so this is the
          -- updated function, not `s.cntF`
          cntb := by
            intro j
            show (if j = s.len then s.cntF s.len - 1 else s.cntF j) < 65536
            by_cases hj : j = s.len
            · rw [if_pos hj]; have := hf.cntb s.len; omega
            · rw [if_neg hj]; exact hf.cntb j
          offsb := hf.offsb
          root1 := hf.root1
          rootmax := by
            rcases hf.droproot with h | h
            · have := hf.dzcurr h; have := hf.currmax; omega
            · have := hf.currmax; have := hf.curr1; omega
          max15 := hf.max15
          nOaddr := hf.nOaddr })
      (fun _ _ _ x => x) (fun _ _ x => x)) ?_
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (len' : Nat) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hlen15' : len' ≤ 15) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hlenmax' : len' ≤ max) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hadv : (len' = s.len ∧ 2 ≤ s.cntF s.len)
      ∨ (s.cntF s.len = 1 ∧ s.len ≠ max
         ∧ len' = lensF (workF (s.sym + 1)))) => ?_)
  have hbw15 : bwInc s.huff s.len < 4294967296 := by
    have h1 := bwInc_lt s.huff s.len hf.hufflt
    have h2 : (2 : Nat) ^ s.len ≤ 2 ^ 15 :=
      Nat.pow_le_pow_right (by omega) hf.len15
    omega
  have hupdb : ∀ j, (if j = s.len then s.cntF s.len - 1 else s.cntF j) < 65536 := by
    intro j
    by_cases hj : j = s.len
    · rw [if_pos hj]; have := hf.cntb s.len; omega
    · rw [if_neg hj]; exact hf.cntb j
  -- the `_t'10` guard
  refine triple_seq_only ge fe f_inflate_table
    (loop_t10_set ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest
      { s with vi := vi', vf := (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))), mn := 2 ^ s.curr, huff := bwInc s.huff s.len, sym := s.sym + 1, len := len', cntF := (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j) }
      (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int))))
      (by show len' < 4294967296; omega) henv.hr32
      (by show bwInc s.huff s.len < 4294967296; exact hbw15)
      (by show s.low < 4294967296; exact hf.low32)) ?_
  -- the sub-table branch
  refine triple_conseq ge fe f_inflate_table
    (loop_subtable_if ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest
      { s with vi := vi', vf := (.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))), mn := 2 ^ s.curr, huff := bwInc s.huff s.len, sym := s.sym + 1, len := len', cntF := (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j) }
      (.Vint (Integers.Int.repr ((op : _root_.Int)))) (.Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int)))) (.Vint (Integers.Int.repr ((val : _root_.Int)))) Ret henv.hcenv henv.hd1 henv.hd2 henv.hd3 henv.hpt
      henv.hpr (by show s.drop = 0 ∨ s.drop = root; exact hf.droproot)
      (by show s.drop < 4294967296; omega)
      (by show len' ≤ max; exact hlenmax') henv.hmax15 henv.hr32
      (by show bwInc s.huff s.len < 4294967296; exact hbw15)
      (by show ∀ j, (if j = s.len then s.cntF s.len - 1 else s.cntF j) < 65536
          exact hupdb)
      (by show ((2 ^ s.curr : Nat) : _root_.Int) < 2147483648
          have : (2 : Nat) ^ s.curr ≤ 2 ^ 15 :=
            Nat.pow_le_pow_right (by omega) hcurr15
          omega)
      (by show Integers.Ptrofs.unsigned s.nO
              + 4 * (((2 ^ s.curr : Nat)) : _root_.Int) < 18446744073709551616
          obtain ⟨X, hX⟩ : ∃ X : _root_.Int,
            Integers.Ptrofs.unsigned tO = X := ⟨_, rfl⟩
          have h1 := hf.nOaddr
          have h2 := hf.room
          have h3 := henv.hnoC
          rw [hX] at h1 h3
          rw [h1]
          obtain ⟨P, hP⟩ : ∃ P : Nat, 2 ^ s.curr = P := ⟨_, rfl⟩
          rw [hP] at h2 ⊢
          have h3' : X + 4 * ((cap : Nat) : _root_.Int)
              < (18446744073709551616 : _root_.Int) := h3
          have h2' : s.nOff + P ≤ cap := h2
          show X + 4 * ((s.nOff : Nat) : _root_.Int) + 4 * ((P : Nat) : _root_.Int)
              < (18446744073709551616 : _root_.Int)
          omega)
      henv.hcap31 henv.hnoC
      (by show bwInc s.huff s.len % 2 ^ root < cap
          have h1 : bwInc s.huff s.len % 2 ^ root < 2 ^ root :=
            Nat.mod_lt _ (Nat.two_pow_pos root)
          omega)
      (by show ∀ c : Nat, c ≤ 15 → s.used + 2 ^ c < 4294967296
          intro c hc
          have h1 := hf.usedcap
          have h2 := henv.hcap31
          have h3 : (2 : Nat) ^ c ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hc
          omega)
      henv.hty henv.hcapL henv.hcapD
      hA5 (by show 1 ≤ s.curr; exact hf.curr1)
      (by show s.curr + s.drop ≤ max; exact hf.currmax)
      (by show s.used ≤ cap; exact hf.usedcap) (hret _)
      { normal := R.normal, brk := LoopExit bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO
           cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
           extraF baseF ty codes root max mtch nlive Hrest,
        cont := Assn.no, ret := Ret, goto := R.goto })
    (fun _ _ _ x => x)
    (fun e le hp hx => by
      obtain ⟨drop', curr', used', low', vl', nO', hc1', hcm', hus', hdr',
        hsub, hst⟩ := hx
      exact ⟨s, hf, op, val, len', drop', curr', used', low', vi', vl', nO',
        hop, hval, hlen15', hlenmax', hc1', hcm', hus', hdr', hadv, hsub, hst⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- **I2 — one pass re-establishes the invariant at a smaller measure.**

    `BodyPost` records everything heap- and temp-shaped; what this theorem adds
    is the model reasoning.  The structural clauses survive
    `sym++`/`count[len]--` because `work[]` is sorted (`WorkChar`); the code
    clause survives because `bwInc` advances the consumed mass by exactly
    `2^(15-len)` (`massBelow_step_rev`); and the two sub-table clauses —
    `lmdcurr` preserved, `subfit` re-established — are the two halves of the
    mass argument (`rev_prefix_bounds` at use, `subfit_from_look` at
    creation).  The new state differs from `BodyPost`'s only in the ghost
    `nOff` field, which neither `TLoop` nor `HLoop` reads. -/
theorem bodypost_loopinv
    (hwc : WorkChar nwork ncodes nlive max mtch nx nb workF lensF vx vb xB bB)
    (n : Nat) (s : LoopSt)
    (hf : LoopFacts n max root nwork ncodes nx nb mtch nlive cap workF lensF
      tO s)
    (e : Env) (le : TempEnv) (hp : Heap)
    (hb : BodyPost bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
      workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF
      baseF ty codes root max mtch Hrest s e le hp) :
    ∃ n', n' < n ∧ LoopInv bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
      tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch nlive Hrest n' e le hp := by
  obtain ⟨op, val, len', drop', curr', used', low', vi', vl', nO', hop, hval,
    hlen15', hlenmax', hc1', hcm', hus', hdr', hadv, hsub, hst⟩ := hb
  have hn1 : 1 ≤ n := by have h1 := hf.measure; have h2 := hf.symlive; omega
  have hgs : lensF (workF s.sym) = s.len := hf.lenw.symm
  -- the advance: the next symbol exists and has length `len'`
  have hstep : s.sym + 1 < nlive ∧ len' = lensF (workF (s.sym + 1)) := by
    rcases hadv with ⟨hle, h2c⟩ | ⟨hcnt1, hnm, hlv⟩
    · have hcs : cntSeg (fun k => lensF (workF k)) s.sym nlive s.len
          = (if lensF (workF s.sym) = s.len then 1 else 0)
            + cntSeg (fun k => lensF (workF k)) (s.sym + 1) nlive s.len :=
        cntSeg_succ _ _ _ _ hf.symlive
      rw [if_pos hgs] at hcs
      have hc := hf.cntc s.len hf.len1
      have h1 : 1 ≤ cntSeg (fun k => lensF (workF k)) (s.sym + 1) nlive
          (lensF (workF s.sym)) := by rw [hgs]; omega
      obtain ⟨hlt, heq⟩ :=
        sorted_stable (fun k => lensF (workF k)) s.sym nlive hwc.hsort
          hf.symlive h1
      exact ⟨hlt, by rw [hle, hf.lenw]; exact heq.symm⟩
    · have hlt : s.sym + 1 < nlive := by
        rcases Nat.lt_or_ge (s.sym + 1) nlive with h | h
        · exact h
        · exfalso
          have hσ : s.sym = nlive - 1 := by have := hf.symlive; omega
          have hml := hwc.hlast (by have := hf.symlive; omega)
          rw [← hσ] at hml
          exact hnm (by rw [hf.lenw, hml])
      exact ⟨hlt, hlv⟩
  obtain ⟨hsym1, hlenw'⟩ := hstep
  have hlen1' : 1 ≤ len' := by rw [hlenw']; exact hwc.hlive _ hsym1
  have hlen_le : s.len ≤ len' := by
    rw [hf.lenw, hlenw']
    exact hwc.hsort s.sym (s.sym + 1) (by omega) hsym1
  -- the decremented counts are the interval counts one symbol later
  have hcntc' : ∀ j, 1 ≤ j →
      (if j = s.len then s.cntF s.len - 1 else s.cntF j)
        = cntSeg (fun k => lensF (workF k)) (s.sym + 1) nlive j := by
    intro j hj
    have hcs : cntSeg (fun k => lensF (workF k)) s.sym nlive j
        = (if lensF (workF s.sym) = j then 1 else 0)
          + cntSeg (fun k => lensF (workF k)) (s.sym + 1) nlive j :=
      cntSeg_succ _ _ _ _ hf.symlive
    have hc := hf.cntc j hj
    by_cases hjl : j = s.len
    · subst hjl
      rw [if_pos rfl]
      rw [if_pos hgs] at hcs
      omega
    · rw [if_neg hjl]
      rw [if_neg (by rw [hgs]; omega)] at hcs
      omega
  -- the mass clause survives the `bwInc` step
  have hcap' : massBelow (fun k => lensF (workF k)) (s.sym + 1) < 2 ^ 15 := by
    have h1 : massBelow (fun k => lensF (workF k)) (s.sym + 2)
        ≤ massBelow (fun k => lensF (workF k)) nlive :=
      massBelow_le _ _ _ (by omega)
    have h2 : massBelow (fun k => lensF (workF k)) (s.sym + 2)
        = massBelow (fun k => lensF (workF k)) (s.sym + 1)
          + 2 ^ (15 - lensF (workF (s.sym + 1))) := rfl
    have h3 := hwc.hmass
    have h4 : (0 : Nat) < 2 ^ (15 - lensF (workF (s.sym + 1))) :=
      Nat.two_pow_pos _
    omega
  have hJ' : massBelow (fun k => lensF (workF k)) (s.sym + 1)
      = rev len' (bwInc s.huff s.len) * 2 ^ (15 - len') :=
    massBelow_step_rev _ s.sym s.len len' s.huff hgs hlen_le hlen15' hf.hJ
      hcap'
  have hufflt' : bwInc s.huff s.len < 2 ^ len' :=
    lt_pow_mono _ s.len len' (bwInc_lt s.huff s.len hf.hufflt) hlen_le
  have hcnt1' : 1 ≤ (if len' = s.len then s.cntF s.len - 1 else s.cntF len')
      := by
    rw [hcntc' len' hlen1']
    exact cntSeg_pos _ (s.sym + 1) nlive len' (s.sym + 1) (Nat.le_refl _)
      hsym1 hlenw'.symm
  have hcntb' : ∀ j,
      (if j = s.len then s.cntF s.len - 1 else s.cntF j) < 65536 := by
    intro j
    by_cases hj : j = s.len
    · rw [if_pos hj]; have := hf.cntb s.len; omega
    · rw [if_neg hj]; exact hf.cntb j
  have hnotlast : len' ≠ max → s.sym + 1 + 1 < nlive := by
    intro hnm
    have hne : s.sym + 1 ≠ nlive - 1 := by
      intro hEq
      exact hnm (by rw [hlenw', hEq]; exact hwc.hlast (by omega))
    omega
  rcases hsub with ⟨hdq, hcq, huq, hlq, hnq, hng⟩ |
    ⟨hrl', hne', hdq, hlq, huq, hlc, hexit, hnOu⟩
  · -- the guard did not fire: everything sub-table-shaped is unchanged
    subst hdq; subst hcq; subst huq; subst hlq; subst hnq
    have hlmd' : len' - s.drop ≤ s.curr := by
      by_cases hrl : root < len'
      · have hpre : bwInc s.huff s.len % 2 ^ root = s.low := by
          by_cases hq : bwInc s.huff s.len % 2 ^ root = s.low
          · exact hq
          · exact absurd ⟨hrl, hq⟩ hng
        rcases hf.droproot with hd0 | hdr
        · exfalso
          have h1 : bwInc s.huff s.len % 2 ^ root < 2 ^ root :=
            Nat.mod_lt _ (Nat.two_pow_pos _)
          have h2 : (2 : Nat) ^ root ≤ 2 ^ 15 :=
            Nat.pow_le_pow_right (by omega) hf.root15
          have h3 := hf.dzlow hd0
          have h4 : (2 : Nat) ^ 15 = 32768 := by decide
          omega
        · rcases Nat.lt_or_ge s.curr (len' - root) with hbig | hok
          · exfalso
            rcases hf.subfit hdr with hcmx | hall
            · omega
            · have hB := hall (s.sym + 1) (by omega) hsym1
                (by rw [← hlenw']; omega)
              have hup := (rev_prefix_bounds len' root (bwInc s.huff s.len)
                (by omega) hlen15').2
              have hm : bwInc s.huff s.len % 2 ^ root = s.low % 2 ^ root := by
                rw [← hpre, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
              rw [rev_congr_mod root (bwInc s.huff s.len) s.low hm] at hup
              rw [hJ'] at hB
              exact absurd hB (Nat.not_le.mpr hup)
          · omega
      · rcases hf.droproot with hd0 | hdr
        · have := hf.dzcurr hd0; omega
        · have := hf.curr1; omega
    have hsubfit' : s.drop = root → root + s.curr = max ∨
        ∀ i, s.sym + 1 ≤ i → i < nlive →
          root + s.curr < lensF (workF i) →
          (rev root s.low + 1) * 2 ^ (15 - root)
            ≤ massBelow (fun k => lensF (workF k)) i := by
      intro hdr
      rcases hf.subfit hdr with h | h
      · exact Or.inl h
      · exact Or.inr (fun i hi1 hi2 hi3 => h i (by omega) hi2 hi3)
    refine ⟨n - 1, by omega,
      { s with v0 := .Vint (Integers.Int.repr ((op : _root_.Int))), v1 := .Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int))), v2 := .Vint (Integers.Int.repr ((val : _root_.Int))), vi := vi', vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))), mn := 2 ^ s.curr, huff := bwInc s.huff s.len, sym := s.sym + 1, len := len', cntF := (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j), drop := s.drop, nO := s.nO, curr := s.curr, vl := vl', used := s.used, low := s.low },
      ?_, hst⟩
    exact {
      measure := by
        show n - 1 + (s.sym + 1) = nlive
        have := hf.measure; omega
      len1 := hlen1'
      len15 := hlen15'
      lenmax := hlenmax'
      low32 := by show s.low < 4294967296; exact hf.low32
      offsb := by show ∀ j, s.offsF j < 65536; exact hf.offsb
      droplen := by show s.drop ≤ len'; have := hf.droplen; omega
      droproot := hdr'
      curr1 := hc1'
      currmax := hcm'
      lmdcurr := hlmd'
      root15 := hf.root15
      max15 := hf.max15
      root1 := hf.root1
      symlt := by show s.sym + 1 < nwork; have := hwc.hnl; omega
      a3x := hwc.ha3x _ hsym1
      a3b := hwc.ha3b _ hsym1
      symnext := by
        show _ = 1 → len' ≠ max → s.sym + 1 + 1 < nwork
        intro _ hnm
        have := hnotlast hnm; have := hwc.hnl; omega
      lensnext := by
        show _ = 1 → len' ≠ max → workF (s.sym + 1 + 1) < ncodes
        intro _ hnm
        exact hwc.hwlt _ (hnotlast hnm)
      hufflt := hufflt'
      nOaddr := hf.nOaddr
      room := hf.room
      usedcap := hus'
      mncap := by show 2 ^ s.curr ≤ cap; have := hf.room; omega
      cnt1 := hcnt1'
      cntb := hcntb'
      symlive := hsym1
      lenw := hlenw'
      cntc := hcntc'
      hJ := hJ'
      useq := hf.useq
      dzcurr := hf.dzcurr
      dzlow := hf.dzlow
      dropfired := hf.dropfired
      dzoff := hf.dzoff
      subfit := hsubfit' }
  · -- the guard fired: a fresh sub-table.  `drop' = root` must NOT be `subst`ed
    -- — `root` is a section variable, so `subst` would eliminate *it* and every
    -- later mention of `root` becomes an unknown identifier.  Rewrite instead.
    subst hlq; subst huq
    rw [hdq] at hst hcm'
    have hmncap : 2 ^ s.curr ≤ cap := by have := hf.room; omega
    have hlow_bound :
        rev root (bwInc s.huff s.len % 2 ^ root) * 2 ^ (15 - root)
          ≤ massBelow (fun k => lensF (workF k)) (s.sym + 1) := by
      rw [rev_mod, hJ']
      exact (rev_prefix_bounds len' root (bwInc s.huff s.len) (by omega)
        hlen15').1
    refine ⟨n - 1, by omega,
      { s with v0 := .Vint (Integers.Int.repr ((op : _root_.Int))), v1 := .Vint (Integers.Int.repr ((((s.len - s.drop) % 256 : Nat) : _root_.Int))), v2 := .Vint (Integers.Int.repr ((val : _root_.Int))), vi := vi', vf := .Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))), mn := 2 ^ s.curr, huff := bwInc s.huff s.len, sym := s.sym + 1, len := len', cntF := (fun j => if j = s.len then s.cntF s.len - 1 else s.cntF j), drop := root, nO := nO', curr := curr', vl := vl', used := s.used + 2 ^ curr', low := bwInc s.huff s.len % 2 ^ root, nOff := s.nOff + 2 ^ s.curr },
      ?_, hst⟩
    exact {
      measure := by
        show n - 1 + (s.sym + 1) = nlive
        have := hf.measure; omega
      len1 := hlen1'
      len15 := hlen15'
      lenmax := hlenmax'
      offsb := by show ∀ j, s.offsF j < 65536; exact hf.offsb
      -- `low = huff & mask = huff % 2^root`, and `root ≤ 15`
      low32 := by
        show bwInc s.huff s.len % 2 ^ root < 4294967296
        have h1 : bwInc s.huff s.len % 2 ^ root < 2 ^ root :=
          Nat.mod_lt _ (Nat.two_pow_pos root)
        have h2 : (2 : Nat) ^ root ≤ 2 ^ 15 :=
          Nat.pow_le_pow_right (by omega) hf.root15
        omega
      droplen := by show root ≤ len'; omega
      droproot := Or.inr rfl
      curr1 := hc1'
      currmax := hcm'
      lmdcurr := hlc
      root15 := hf.root15
      max15 := hf.max15
      root1 := hf.root1
      symlt := by show s.sym + 1 < nwork; have := hwc.hnl; omega
      a3x := hwc.ha3x _ hsym1
      a3b := hwc.ha3b _ hsym1
      symnext := by
        show _ = 1 → len' ≠ max → s.sym + 1 + 1 < nwork
        intro _ hnm
        have := hnotlast hnm; have := hwc.hnl; omega
      lensnext := by
        show _ = 1 → len' ≠ max → workF (s.sym + 1 + 1) < ncodes
        intro _ hnm
        exact hwc.hwlt _ (hnotlast hnm)
      hufflt := hufflt'
      nOaddr := by
        show Integers.Ptrofs.unsigned nO' = Integers.Ptrofs.unsigned tO
          + 4 * (((s.nOff + 2 ^ s.curr : Nat)) : _root_.Int)
        obtain ⟨P, hP⟩ : ∃ P : Nat, 2 ^ s.curr = P := ⟨_, rfl⟩
        obtain ⟨A, hA⟩ : ∃ A : _root_.Int,
          Integers.Ptrofs.unsigned nO' = A := ⟨_, rfl⟩
        obtain ⟨B, hB⟩ : ∃ B : _root_.Int,
          Integers.Ptrofs.unsigned s.nO = B := ⟨_, rfl⟩
        obtain ⟨C, hC⟩ : ∃ C : _root_.Int,
          Integers.Ptrofs.unsigned tO = C := ⟨_, rfl⟩
        rw [hP] at hnOu ⊢
        rw [hA, hB] at hnOu
        have h2 := hf.nOaddr
        rw [hB, hC] at h2
        rw [hA, hC]
        have h1' : A = B + 4 * ((P : Nat) : _root_.Int) := hnOu
        have h2' : B = C + 4 * ((s.nOff : Nat) : _root_.Int) := h2
        show A = C + 4 * (((s.nOff + P : Nat)) : _root_.Int)
        omega
      room := by
        show s.nOff + 2 ^ s.curr + 2 ^ curr' ≤ cap
        have h1 := hf.useq
        have h2 : s.used + 2 ^ curr' ≤ cap := hus'
        omega
      usedcap := hus'
      mncap := hmncap
      cnt1 := hcnt1'
      cntb := hcntb'
      symlive := hsym1
      lenw := hlenw'
      cntc := hcntc'
      hJ := hJ'
      useq := by
        show s.used + 2 ^ curr' = s.nOff + 2 ^ s.curr + 2 ^ curr'
        have := hf.useq; omega
      dzcurr := by
        show root = 0 → curr' = root
        intro h; exfalso; have := hf.root1; omega
      dzlow := by
        show root = 0 → bwInc s.huff s.len % 2 ^ root = 4294967295
        intro h; exfalso; have := hf.root1; omega
      dropfired := by
        show root = root → root < max
        intro _; omega
      dzoff := by
        show root = 0 → s.nOff + 2 ^ s.curr = 0
        intro h; exfalso; have := hf.root1; omega
      subfit := by
        show root = root → root + curr' = max ∨
          ∀ i, s.sym + 1 ≤ i → i < nlive →
            root + curr' < lensF (workF i) →
            (rev root (bwInc s.huff s.len % 2 ^ root) + 1) * 2 ^ (15 - root)
              ≤ massBelow (fun k => lensF (workF k)) i
        intro _
        rcases hexit with hcmx | hws
        · exact Or.inl (by omega)
        · refine Or.inr (fun i hi1 hi2 hi3 => ?_)
          rw [wsum_congr _ (cntSeg (fun k => lensF (workF k)) (s.sym + 1)
                nlive) len' _
                (fun k _ => hcntc' (len' + k) (by omega))] at hws
          have hall := subfit_from_look (fun k => lensF (workF k)) nlive
            (s.sym + 1) root curr' len' hwc.hsort hlenw'.symm hrl' hlc
            (by have := hf.max15; omega) hws
          have hBi := hall i hi1 hi2 (by omega)
          rw [Nat.succ_mul]
          omega }

/-! #### The `Sloop`

The AST's loop is `Sloop loopBody Sskip`, so `triple_loop`'s second statement is
the trivial one and `J n` is just "the body has run and left `BodyPost`".  The
`brk` of the body is the loop's `normal`, which is why `LoopExit` appears on
both sides. -/

/-- The invariant halfway through: the body has run, and `bodypost_loopinv` can
    turn the result back into `LoopInv` at a smaller measure. -/
def JBody (n : Nat) : Sep.Assn := fun e le hp =>
  ∃ s : LoopSt,
  ∃ _ : LoopFacts n max root nwork ncodes nx nb mtch nlive cap workF lensF tO s,
    BodyPost bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch Hrest s e le hp

/-- **The main table-building loop** (inftrees.c:221-295).

    `triple_loop` at measure `n = nlive - sym`, with `bodypost_loopinv` as the
    step.  Its normal exit is the `break` at inftrees.c:263 — the only way
    out. -/
theorem main_loop_triple
    (henv : LoopEnv ge bh bc bo pt pb pr pw pl pg tO cap workO nwork workF
      lensO ncodes lensF nx nb extraF baseF ty root max mtch)
    (hwc : WorkChar nwork ncodes nlive max mtch nx nb workF lensF vx vb xB bB)
    (Ret : Val → HProp)
    (hret : ∀ (s : LoopSt) hr, HenoughRest pt pb pr pw pl pg tblB tblO bitsB
        bitsO tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB
        nx nb extraF baseF Hrest s.vbits hr →
      Ret (.Vint (Integers.Int.repr 1)) hr)
    -- **Two facts about the fixed parameters**, replacing seven hypotheses that
    -- were quantified over *all* `LoopSt` — a record with unconstrained `Nat`
    -- fields, so those were false and the lemma was vacuous.  Everything the
    -- body needs about the *current* state is derived from `hf`/`henv` below.
    (hrootcap : 2 ^ root ≤ cap)
    (hA5 : ty = 0 → max ≤ root)
    (R : Sep.ExitConds) (n : Nat) :
    Triple ge fe f_inflate_table
      (LoopInv bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
        codes root max mtch nlive Hrest n)
      (.Sloop loopBody .Sskip)
      { normal := LoopExit bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB
          tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
          extraF baseF ty codes root max mtch nlive Hrest,
        brk := R.brk, cont := R.cont, ret := Ret, goto := R.goto } := by
  refine triple_loop ge fe f_inflate_table _
    (LoopInv bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch nlive Hrest)
    (JBody bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF baseF ty
      codes root max mtch nlive Hrest)
    _ _ (fun k => ?_) (fun k => ?_) n
  · -- the body: the eleven links, then repackage as `JBody`
    exact triple_conseq ge fe f_inflate_table
      (loop_body_triple ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
        tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
        extraF baseF ty codes root max mtch nlive Hrest henv hwc Ret hret
        hrootcap hA5 k R)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ hx => hx.elim) (fun _ _ x => x)
  · -- `Sskip`: the measure step is I2
    refine triple_conseq ge fe f_inflate_table
      (triple_skip ge fe f_inflate_table _)
      (fun _ _ _ x => x)
      (fun e le hp hx => by
        obtain ⟨s, hf, hb⟩ := hx
        exact bodypost_loopinv bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
          tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx
          nb extraF baseF ty codes root max mtch nlive Hrest hwc k s hf e le hp
          hb)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! #### The setup statements, against the loop's footprint

The nine `Sset`s of inftrees.c:204-214 plus the first ENOUGH check, landing on
`TLoop`/`HLoop` — i.e. exactly `main_loop_triple`'s precondition, modulo the
`LoopFacts` bundle that `loopfacts_entry` supplies.

The tracked list is abstract: the caller gives the three values the setup
*reads* (`min`, `root`, `*table`), freshness for the nine it *writes*, and
`hsub` — that the resulting list covers `TLoop`'s twenty-four entries.  `hsub`
is one `simp +decide` once the prologue's list is concrete. -/

theorem loop_setup_triple
    (mn0 : Nat) (l : List (Ident × Val)) (s0 : LoopSt)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hpt : permOrder pt .Readable = true)
    (hr32 : root < 32)
    (hmemMin : (_min, .Vint (Integers.Int.repr ((mn0 : _root_.Int)))) ∈ l)
    (hmemRoot : (_root, .Vint (Integers.Int.repr ((root : _root_.Int)))) ∈ l)
    (hmemTbl : (_table, .Vptr tblB tblO) ∈ l)
    (hfr : ∀ p ∈ l, p.1 ≠ _huff ∧ p.1 ≠ _sym ∧ p.1 ≠ _len ∧ p.1 ≠ _next
            ∧ p.1 ≠ _curr ∧ p.1 ≠ _drop ∧ p.1 ≠ _low ∧ p.1 ≠ _used
            ∧ p.1 ≠ _mask)
    (hsub : ∀ q ∈ TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb
      ty codes root max mtch s0,
      q ∈ (_mask, Val.Vint (Integers.Int.repr (((2 ^ root - 1 : Nat) : _root_.Int))))
        :: (_used, Val.Vint (Integers.Int.repr (((2 ^ root : Nat) : _root_.Int))))
        :: (_low, Val.Vint (Integers.Int.repr (((4294967295 : Nat) : _root_.Int))))
        :: (_drop, Val.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))))
        :: (_curr, Val.Vint (Integers.Int.repr ((root : _root_.Int))))
        :: (_next, Val.Vptr tB tO)
        :: (_len, Val.Vint (Integers.Int.repr ((mn0 : _root_.Int))))
        :: (_sym, Val.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))))
        :: (_huff, Val.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int)))) :: l)
    (hfrT : ∀ q ∈ TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb
      ty codes root max mtch s0, q.1 ≠ _t'5 ∧ q.1 ≠ _t'6)
    (hty : ty = 0 ∨ ty = 1 ∨ ty = 2)
    -- `≤`, not `=`: A4 says the caller supplies *at least* ENOUGH, and the
    -- runtime check compares against the literal
    (hcapL : ty = 1 → 852 ≤ cap) (hcapD : ty = 2 → 592 ≤ cap)
    (hA5 : ty = 0 → s0.used ≤ cap) (hu32 : s0.used < 4294967296)
    (Ret : Val → HProp)
    (hret : ∀ hr, HenoughRest pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
        workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
        baseF Hrest s0.vbits hr →
      Ret (.Vint (Integers.Int.repr 1)) hr)
    (R : Sep.ExitConds) (tail : Stmt)
    -- **Tail form.**  `fullBody`'s spine has `enoughChk` followed by the main
    -- loop, so a triple for the ten statements as a *closed* block would be
    -- about a statement the program does not contain (`Ssequence` is a
    -- constructor, not an associative operator — the trap `bwIncBlock` and
    -- `seg6_triple` both fell into).
    (htail : Triple ge fe f_inflate_table
      (fun e le hp => ∃ _ : s0.used ≤ cap,
        LocalSt (envOf bh bc bo)
          (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
            codes root max mtch s0)
          (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
            workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
            extraF baseF Hrest s0.cntF s0.offsF s0.v0 s0.v1 s0.v2 s0.vbits)
          e le hp)
      tail { normal := R.normal, brk := R.brk, cont := R.cont, ret := Ret,
             goto := R.goto }) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s0.cntF s0.offsF s0.v0 s0.v1 s0.v2 s0.vbits))
      (.Ssequence setHuff0 (.Ssequence setSym0 (.Ssequence setLenMin
        (.Ssequence setNextTbl (.Ssequence setCurrRoot (.Ssequence setDrop0
          (.Ssequence setLowM1 (.Ssequence setUsed (.Ssequence setMask
            (.Ssequence (enoughChk _t'5 _t'6) tail))))))))))
      { normal := R.normal,
        brk := R.brk, cont := R.cont, ret := Ret, goto := R.goto } := by
  refine triple_seq_only ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) _ _ _huff ((0 : Nat) : _root_.Int)
      (fun p hp => (hfr p hp).1)) ?_
  refine triple_seq_only ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) _ _ _sym ((0 : Nat) : _root_.Int)
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h
          · show _huff ≠ _sym; decide
          · exact (hfr p h).2.1)) ?_
  refine triple_seq_only ge fe f_inflate_table
    (set_copy_triple ge fe bh bc bo _ _ _len _min tuint _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmemMin))
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h1
          · show _sym ≠ _len; decide
          rcases List.mem_cons.mp h1 with rfl | h2
          · show _huff ≠ _len; decide
          · exact (hfr p h2).2.2.1)) ?_
  have hbp := HLoop_as_backptr bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s0.cntF s0.offsF s0.v0 s0.v1 s0.v2 s0.vbits
  refine triple_seq_only ge fe f_inflate_table
    (Q := LocalSt (envOf bh bc bo)
      ((_next, Val.Vptr tB tO)
        :: (_len, Val.Vint (Integers.Int.repr ((mn0 : _root_.Int))))
        :: (_sym, Val.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))))
        :: (_huff, Val.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int))))
        :: l)
      (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s0.cntF s0.offsF s0.v0 s0.v1 s0.v2 s0.vbits)) ?_ ?_
  · refine localst_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun p hp => hp) hbp
      _ _ ?_
    refine localst_post_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun p hp => hp)
      hbp.symm _ _ ?_
    exact read_table_triple' ge fe bh bc bo pt pr tblB tblO tB tO cap hpt _next
      _ _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hmemTbl)))
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h1
          · show _len ≠ _next; decide
          rcases List.mem_cons.mp h1 with rfl | h2
          · show _sym ≠ _next; decide
          rcases List.mem_cons.mp h2 with rfl | h3
          · show _huff ≠ _next; decide
          · exact (hfr p h3).2.2.2.1)
  refine triple_seq_only ge fe f_inflate_table
    (set_copy_triple ge fe bh bc bo _ _ _curr _root tuint _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hmemRoot))))
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h1
          · show _next ≠ _curr; decide
          rcases List.mem_cons.mp h1 with rfl | h2
          · show _len ≠ _curr; decide
          rcases List.mem_cons.mp h2 with rfl | h3
          · show _sym ≠ _curr; decide
          rcases List.mem_cons.mp h3 with rfl | h4
          · show _huff ≠ _curr; decide
          · exact (hfr p h4).2.2.2.2.1)) ?_
  refine triple_seq_only ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) _ _ _drop ((0 : Nat) : _root_.Int)
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h1
          · show _curr ≠ _drop; decide
          rcases List.mem_cons.mp h1 with rfl | h2
          · show _next ≠ _drop; decide
          rcases List.mem_cons.mp h2 with rfl | h3
          · show _len ≠ _drop; decide
          rcases List.mem_cons.mp h3 with rfl | h4
          · show _sym ≠ _drop; decide
          rcases List.mem_cons.mp h4 with rfl | h5
          · show _huff ≠ _drop; decide
          · exact (hfr p h5).2.2.2.2.2.1)) ?_
  refine triple_seq_only ge fe f_inflate_table
    (set_low_m1_triple ge fe bh bc bo _ _
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h1
          · show _drop ≠ _low; decide
          rcases List.mem_cons.mp h1 with rfl | h2
          · show _curr ≠ _low; decide
          rcases List.mem_cons.mp h2 with rfl | h3
          · show _next ≠ _low; decide
          rcases List.mem_cons.mp h3 with rfl | h4
          · show _len ≠ _low; decide
          rcases List.mem_cons.mp h4 with rfl | h5
          · show _sym ≠ _low; decide
          rcases List.mem_cons.mp h5 with rfl | h6
          · show _huff ≠ _low; decide
          · exact (hfr p h6).2.2.2.2.2.2.1)) ?_
  refine triple_seq_only ge fe f_inflate_table
    (set_used_triple ge fe bh bc bo _ _ root hr32
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hmemRoot)))))))
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h1
          · show _low ≠ _used; decide
          rcases List.mem_cons.mp h1 with rfl | h2
          · show _drop ≠ _used; decide
          rcases List.mem_cons.mp h2 with rfl | h3
          · show _curr ≠ _used; decide
          rcases List.mem_cons.mp h3 with rfl | h4
          · show _next ≠ _used; decide
          rcases List.mem_cons.mp h4 with rfl | h5
          · show _len ≠ _used; decide
          rcases List.mem_cons.mp h5 with rfl | h6
          · show _sym ≠ _used; decide
          rcases List.mem_cons.mp h6 with rfl | h7
          · show _huff ≠ _used; decide
          · exact (hfr p h7).2.2.2.2.2.2.2.1)) ?_
  refine triple_seq_only ge fe f_inflate_table
    (set_mask_triple ge fe bh bc bo _ _ (2 ^ root) Nat.one_le_two_pow
      List.mem_cons_self
      (by intro p hp
          rcases List.mem_cons.mp hp with rfl | h1
          · show _used ≠ _mask; decide
          rcases List.mem_cons.mp h1 with rfl | h2
          · show _low ≠ _mask; decide
          rcases List.mem_cons.mp h2 with rfl | h3
          · show _drop ≠ _mask; decide
          rcases List.mem_cons.mp h3 with rfl | h4
          · show _curr ≠ _mask; decide
          rcases List.mem_cons.mp h4 with rfl | h5
          · show _next ≠ _mask; decide
          rcases List.mem_cons.mp h5 with rfl | h6
          · show _len ≠ _mask; decide
          rcases List.mem_cons.mp h6 with rfl | h7
          · show _sym ≠ _mask; decide
          rcases List.mem_cons.mp h7 with rfl | h8
          · show _huff ≠ _mask; decide
          · exact (hfr p h8).2.2.2.2.2.2.2.2)) ?_
  -- now weaken the accumulated list to `TLoop s0`, then the ENOUGH check,
  -- then hand off to the tail
  refine triple_seq ge fe f_inflate_table _
    (fun e le hp => ∃ _ : s0.used ≤ cap,
      LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
          codes root max mtch s0)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
          workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
          extraF baseF Hrest s0.cntF s0.offsF s0.v0 s0.v1 s0.v2 s0.vbits)
        e le hp) _ _ _
    (triple_conseq ge fe f_inflate_table
      (loop_enough ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO
        cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
        extraF baseF ty codes root max mtch Hrest s0 _t'5 _t'6 (by decide) hfrT
        s0.v0 s0.v1 s0.v2 Ret hcenv hd1 hd2 hd3 hu32 hty hcapL hcapD hA5 hret R)
      (fun e le hp hx => ⟨hx.1, TempsHold_mono hsub hx.2.1, hx.2.2⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x))
    htail

/-! #### The epilogue (inftrees.c:298-310)

        if (huff != 0) { here.op = 64; here.bits = len - drop;
                         here.val = 0; next[huff] = here; }
        *table += used; *bits = root; return 0;

The `if` is where `exit_write_inbounds` (§26c) is spent: on the taken branch it
pins `huff = 1`, `drop = 0`, `nOff = 0` and `2 ≤ cap`, so `next[huff]` is entry
one of the root table.  The three field writes go through `Hentry`
(`HLoop_as_Hentry`); the copy needs the fields *assembled*
(`here_assemble`), which is the same shape as the fill loop's boundary. -/

/-- `HLoop` with `here`'s three fields at concrete values, re-associated for
    the whole-table entry write: region first, then `here` as one byte run. -/
abbrev HepiRest (cntF offsF : Nat → Nat) (vbits : Val) : HProp :=
  arrayU16 .Freeable bc 0 16 cntF
  ∗ (HoffsAt bo offsF
     ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB tO)
        ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vbits
           ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
              ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
                 ∗ (arrayU16 pg xB 0 nx extraF
                    ∗ (arrayU16 pg bB 0 nb baseF ∗ Hrest)))))))

theorem HLoop_as_epi (cntF offsF : Nat → Nat) (vbits : Val)
    (op bits val : Nat) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF (.Vint (Integers.Int.repr ((op : Nat))))
      (.Vint (Integers.Int.repr ((bits : Nat))))
      (.Vint (Integers.Int.repr ((val : Nat)))) vbits
    = codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      ∗ (bytesPtsTo bh .Freeable 0 (hereBytes op bits val)
         ∗ HepiRest bc bo pt pb pw pl pg tblB tblO bitsB bitsO tB tO workB
             workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
             Hrest cntF offsF vbits) := by
  simp only [HLoop, HepiRest]
  rw [← here_assemble bh op bits val]
  try sep_cancel

/-- **The epilogue's `if`.**  On the taken branch `exit_write_inbounds` has
    pinned `huff = 1`, `drop = 0`, `nOff = 0`, `2 ≤ cap`, so the write lands on
    entry one of the root table.  Both branches leave the same assertion: the
    footprint back, with `here`'s three fields existentially quantified (the
    epilogue is the last thing that touches them). -/
theorem epilogue_if_triple (s : LoopSt) (w0 w1 w2 : Val)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpr : permOrder pr .Writable = true)
    (hcap31 : (cap : _root_.Int) < 2147483648)
    (htO4 : Integers.Ptrofs.unsigned tO % 4 = 0)
    (hnoC : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
              < 18446744073709551616)
    (hl15 : s.len ≤ 15) (hdl : s.drop ≤ s.len) (hh32 : s.huff < 4294967296)
    (hinb : s.huff ≠ 0 → s.drop = 0 ∧ s.nOff = 0 ∧ s.huff = 1 ∧ 2 ≤ cap)
    (hno : Integers.Ptrofs.unsigned s.nO
             = Integers.Ptrofs.unsigned tO + 4 * (s.nOff : _root_.Int))
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF w0 w1 w2 s.vbits))
      epilogueIf
      (.only (fun e le hp => ∃ u0 u1 u2 : Val,
        LocalSt (envOf bh bc bo)
          (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
            root max mtch s)
          (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap
            workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF
            baseF Hrest s.cntF s.offsF u0 u1 u2 s.vbits) e le hp)) := by
  have hent := HLoop_as_Hentry bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
    extraF baseF Hrest s.cntF s.offsF
  by_cases hz : s.huff = 0
  · -- not taken: nothing happens
    refine triple_if_local ge fe f_inflate_table _ _ _ _ false _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · have h := ne0_eval_uint (ge := ge) (e := envOf bh bc bo) (m := mm)
        _huff s.huff hh32 (hT'.get (by temps_mem))
      rw [show decide (s.huff ≠ 0) = false from by
            rw [decide_eq_false_iff_not]; exact fun hne => hne hz] at h
      exact h
    · exact triple_conseq ge fe f_inflate_table
        (triple_skip ge fe f_inflate_table _)
        (fun _ _ _ x => x) (fun e le hp hx => ⟨w0, w1, w2, hx⟩)
        (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
        (fun _ _ hx => hx.elim)
  · -- taken: the three field writes, then the copy at entry `huff = 1`
    obtain ⟨hdrop, hoff, hh1, hcap2⟩ := hinb hz
    refine triple_if_local ge fe f_inflate_table _ _ _ _ true _ _ _
      (fun le mm hp hT' _ _ => ?_) ?_
    · have h := ne0_eval_uint (ge := ge) (e := envOf bh bc bo) (m := mm)
        _huff s.huff hh32 (hT'.get (by temps_mem))
      rw [show decide (s.huff ≠ 0) = true from by
            rw [decide_eq_true_eq]; exact hz] at h
      exact h
    -- here.op = (unsigned char)64
    refine triple_seq_only ge fe f_inflate_table
      (localst_adapt_both ge fe (envOf bh bc bo) _ _ _ _ _ _ _ _
        (fun _ hq => hq) (hent w0 w1 w2 s.vbits) (fun _ hq => hq)
        (hent _ w1 w2 s.vbits).symm _
        (entry_op_write ge fe bh bc bo pw workB workO nwork workF pg xB bB nx nb
          extraF baseF
          (HentryRest bc bo pt pb pr pl tblB tblO bitsB bitsO tB tO cap lensB
            lensO ncodes lensF Hrest s.cntF s.offsF s.vbits)
          hcenv w0 w1 w2 _ _ _
          (fun le mm _ => ⟨.Vint (Integers.Int.zero_ext 8
              (Integers.Int.repr 64)), EvalExpr.Ecast _ _ _ _
            (EvalExpr.Econst_int _ _)
            (by simp only [typeof]; exact semCast_int_uchar mm _), by
              simp only [typeof]
              rw [semCast_uchar_uchar,
                  show (64 : _root_.Int) = ((64 : Nat) : _root_.Int) from rfl,
                  zero_ext8_repr 64 (by omega),
                  zero_ext8_repr 64 (by omega)]⟩))) ?_
    -- here.bits = (unsigned char)(len - drop)
    refine triple_seq_only ge fe f_inflate_table
      (localst_adapt_both ge fe (envOf bh bc bo) _ _ _ _ _ _ _ _
        (fun _ hq => hq) (hent _ w1 w2 s.vbits) (fun _ hq => hq)
        (hent _ _ w2 s.vbits).symm _
        (entry_bits_triple ge fe bh bc bo pw workB workO nwork workF pg xB bB nx
          nb extraF baseF
          (HentryRest bc bo pt pb pr pl tblB tblO bitsB bitsO tB tO cap lensB
            lensO ncodes lensF Hrest s.cntF s.offsF s.vbits)
          _ hcenv s.len s.drop hdl (by omega) _ w1 w2 (by temps_mem)
          (by temps_mem))) ?_
    -- here.val = (unsigned short)0
    refine triple_seq_only ge fe f_inflate_table
      (localst_adapt_both ge fe (envOf bh bc bo) _ _ _ _ _ _ _ _
        (fun _ hq => hq) (hent _ _ w2 s.vbits) (fun _ hq => hq)
        (hent _ _ _ s.vbits).symm _
        (entry_val_write ge fe bh bc bo pw workB workO nwork workF pg xB bB nx
          nb extraF baseF
          (HentryRest bc bo pt pb pr pl tblB tblO bitsB bitsO tB tO cap lensB
            lensO ncodes lensF Hrest s.cntF s.offsF s.vbits)
          hcenv _ _ w2 _ _ _
          (fun le mm _ => ⟨.Vint (Integers.Int.zero_ext 16
              (Integers.Int.repr 0)), EvalExpr.Ecast _ _ _ _
            (EvalExpr.Econst_int _ _)
            (by simp only [typeof]; exact semCast_int_ushort mm _), by
              simp only [typeof]
              rw [semCast_ushort_ushort,
                  show (0 : _root_.Int) = ((0 : Nat) : _root_.Int) from rfl,
                  zero_ext16_repr 0 (by omega),
                  zero_ext16_repr 0 (by omega)]⟩))) ?_
    -- next[huff] = here
    have hepi := HLoop_as_epi bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
      tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB nx nb
      extraF baseF Hrest s.cntF s.offsF s.vbits 64 ((s.len - s.drop) % 256) 0
    have hnO : Integers.Ptrofs.unsigned s.nO = Integers.Ptrofs.unsigned tO := by
      rw [hno, hoff]
      obtain ⟨A, hA⟩ : ∃ A : _root_.Int,
        Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
      rw [hA]; show A + 4 * ((0 : Nat) : _root_.Int) = A; omega
    -- `next` and `*table` coincide here (`nOff = 0`), so the region the write
    -- rule wants is the whole table region
    have hepi2 := hepi
    rw [← hnO] at hepi2
    refine triple_conseq ge fe f_inflate_table
      (localst_adapt_both ge fe (envOf bh bc bo) _ _ _ _ _ _ _ _
        (fun _ hq => hq) hepi2 (fun _ hq => hq) hepi2.symm _
        (codeRegion_entry_write ge fe bh bc bo hcenv pr hpr tB s.nO cap s.huff
          (by omega) hcap31 64 ((s.len - s.drop) % 256) 0
          (by rw [hnO]; exact htO4) (by rw [hnO]; exact hnoC)
          _next (.Etempvar _huff tuint) rfl
          (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
            root max mtch s)
          (HepiRest bc bo pt pb pw pl pg tblB tblO bitsB bitsO tB tO workB
            workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
            Hrest s.cntF s.offsF s.vbits)
          (by temps_mem)
          (fun le mm hT' =>
            EvalExpr.Etempvar _huff tuint _ (hT'.get (by temps_mem)))))
      (fun _ _ _ x => x)
      (fun e le hp hx => ⟨_, _, _, hx⟩)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ hx => hx.elim)

/-! #### The epilogue's trailing three statements

`*table += used`, `*bits = root`, `return 0`.  None can fault — the first is
pointer arithmetic, the second a scalar store into an owned cell, the third the
§8 return machinery — so all that is left is heap bookkeeping: each statement
wants a different component at the head.

`HLoop` pins the `table` cell to `.Vptr tB tO`, and the epilogue *changes* it,
so these are stated over `HLoopT`, which takes the cell's value as a
parameter.  (Generated rather than hand-written: deep `∗`-chains are easy to
mis-parenthesise.) -/

/-- `HLoop` with the `*table` cell's value generalised. -/
abbrev HLoopT (cntF offsF : Nat → Nat) (u0 u1 u2 vb tv : Val) : HProp :=
  arrayU16 .Freeable bc 0 16 cntF
  ∗ (HoffsAt bo offsF
  ∗ (mapsto .Mint8unsigned .Freeable bh 0 u0
  ∗ (mapsto .Mint8unsigned .Freeable bh 1 u1
  ∗ (mapsto .Mint16unsigned .Freeable bh 2 u2
  ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
  ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) tv
  ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vb
  ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
  ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
  ∗ (arrayU16 pg xB 0 nx extraF
  ∗ (arrayU16 pg bB 0 nb baseF
  ∗ (Hrest))))))))))))

theorem HLoop_eq_HLoopT (cntF offsF : Nat → Nat) (u0 u1 u2 vb : Val) :
    HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
      workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF Hrest
      cntF offsF u0 u1 u2 vb
    = HLoopT bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest cntF offsF u0 u1 u2 vb (.Vptr tB tO) := rfl

/-- `HLoopT` with the `bits` cell at the head — for `*bits = root`. -/
theorem HLoopT_as_bits (cntF offsF : Nat → Nat) (u0 u1 u2 vb tv : Val) :
    HLoopT bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest cntF offsF u0 u1 u2 vb tv
    = mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vb
      ∗ (arrayU16 .Freeable bc 0 16 cntF
      ∗ (HoffsAt bo offsF
      ∗ (mapsto .Mint8unsigned .Freeable bh 0 u0
      ∗ (mapsto .Mint8unsigned .Freeable bh 1 u1
      ∗ (mapsto .Mint16unsigned .Freeable bh 2 u2
      ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) tv
      ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
      ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
      ∗ (arrayU16 pg xB 0 nx extraF
      ∗ (arrayU16 pg bB 0 nb baseF
      ∗ (Hrest)))))))))))) := by
  simp only [HLoopT]
  try sep_cancel

/-- `HLoopT` in the shape the §8 return machinery needs. -/
theorem HLoopT_as_ret (cntF offsF : Nat → Nat) (u0 u1 u2 vb tv : Val) :
    HLoopT bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest cntF offsF u0 u1 u2 vb tv
    = bytesPtsTo bh .Freeable 0 (hereRun u0 u1 u2)
      ∗ (bytesPtsTo bc .Freeable 0 (u16Bytes cntF 16)
      ∗ (bytesPtsTo bo .Freeable 0 (offsBytes offsF)
      ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) tv
      ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vb
      ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
      ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
      ∗ (arrayU16 pg xB 0 nx extraF
      ∗ (arrayU16 pg bB 0 nb baseF
      ∗ (Hrest)))))))))) := by
  simp only [HLoopT, hereRun]
  rw [arrayU16_bytes .Freeable bc 0 cntF (by omega) 16,
      HoffsAt_bytes bo offsF,
      ← codeCell_eq_bytes .Freeable bh 0 (by omega) u0 u1 u2]
  try sep_cancel

/-- `HLoopT` in `read_table_triple'`'s shape: region, then the `table` cell. -/
theorem HLoopT_as_read (cntF offsF : Nat → Nat) (u0 u1 u2 vb tv : Val) :
    HLoopT bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest cntF offsF u0 u1 u2 vb tv
    = codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) tv
      ∗ (arrayU16 .Freeable bc 0 16 cntF
      ∗ (HoffsAt bo offsF
      ∗ (mapsto .Mint8unsigned .Freeable bh 0 u0
      ∗ (mapsto .Mint8unsigned .Freeable bh 1 u1
      ∗ (mapsto .Mint16unsigned .Freeable bh 2 u2
      ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vb
      ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
      ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
      ∗ (arrayU16 pg xB 0 nx extraF
      ∗ (arrayU16 pg bB 0 nb baseF
      ∗ (Hrest)))))))))))) := by
  simp only [HLoopT]
  try sep_cancel

/-- `HLoopT` with the `table` cell at the head — for `*table += used`. -/
theorem HLoopT_as_tbl (cntF offsF : Nat → Nat) (u0 u1 u2 vb tv : Val) :
    HLoopT bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest cntF offsF u0 u1 u2 vb tv
    = mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) tv
      ∗ (arrayU16 .Freeable bc 0 16 cntF
      ∗ (HoffsAt bo offsF
      ∗ (mapsto .Mint8unsigned .Freeable bh 0 u0
      ∗ (mapsto .Mint8unsigned .Freeable bh 1 u1
      ∗ (mapsto .Mint16unsigned .Freeable bh 2 u2
      ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) vb
      ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
      ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
      ∗ (arrayU16 pg xB 0 nx extraF
      ∗ (arrayU16 pg bB 0 nb baseF
      ∗ (Hrest)))))))))))) := by
  simp only [HLoopT]
  try sep_cancel

/-- **The epilogue, whole** (inftrees.c:298-310): the `if`, then
    `*table += used`, `*bits = root`, `return 0`.

    All the safety content is the `if`'s write (`epilogue_if_triple`, resting on
    `exit_write_inbounds`); the three trailing statements cannot fault, so they
    are pure heap bookkeeping through the five `HLoopT_as_*` bridges. -/
theorem epilogue_triple (s : LoopSt) (w0 w1 w2 : Val) (Ret : Val → HProp)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hpr : permOrder pr .Writable = true)
    (hpt : permOrder pt .Readable = true)
    (hptW : permOrder pt .Writable = true)
    (hpb : permOrder pb .Writable = true)
    (hcap31 : (cap : _root_.Int) < 2147483648)
    (htO4 : Integers.Ptrofs.unsigned tO % 4 = 0)
    (hnoC : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
              < 18446744073709551616)
    (hl15 : s.len ≤ 15) (hdl : s.drop ≤ s.len) (hh32 : s.huff < 4294967296)
    (hinb : s.huff ≠ 0 → s.drop = 0 ∧ s.nOff = 0 ∧ s.huff = 1 ∧ 2 ≤ cap)
    (hno : Integers.Ptrofs.unsigned s.nO
             = Integers.Ptrofs.unsigned tO + 4 * (s.nOff : _root_.Int))
    (hcb : ∀ j, s.cntF j < 65536) (hob : ∀ j, s.offsF j < 65536)
    -- the §8 return machinery frees the three locals, so the
    -- postcondition receives only the residual footprint
    (hret : ∀ hr, (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
        ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))
        ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
          (.Vint (Integers.Int.repr ((root : _root_.Int))))
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
        ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
        ∗ (arrayU16 pg xB 0 nx extraF
        ∗ (arrayU16 pg bB 0 nb baseF
        ∗ (Hrest)))))))) hr →
      Ret (.Vint (Integers.Int.repr 0)) hr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
          root max mtch s)
        (HLoop bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
          workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
          Hrest s.cntF s.offsF w0 w1 w2 s.vbits))
      (.Ssequence epilogueIf (.Ssequence bumpTableUsed
        (.Ssequence setBitsRoot retZero)))
      { normal := R.normal, brk := R.brk, cont := R.cont, ret := Ret,
        goto := R.goto } := by
  refine triple_seq_only ge fe f_inflate_table
    (epilogue_if_triple ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
      tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
      extraF baseF ty codes root max mtch Hrest s w0 w1 w2 hcenv hpr hcap31
      htO4 hnoC hl15 hdl hh32 hinb hno R) ?_
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (u0 : Val) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (u1 : Val) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (u2 : Val) => ?_)
  have hT := HLoop_eq_HLoopT bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF u0 u1 u2 s.vbits
  have hrd := fun (tv : Val) => HLoopT_as_read bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF u0 u1 u2
    s.vbits tv
  have htb := fun (tv : Val) => HLoopT_as_tbl bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF u0 u1 u2
    s.vbits tv
  -- `bumpTableUsed` is ONE AST segment (`Ssequence` of the read and the
  -- store), so it has to be proved as a unit, not as two chain slots.
  refine triple_seq_only ge fe f_inflate_table
    (triple_seq_only ge fe f_inflate_table
    -- `t'11 = *table`
      (localst_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun q hq => hq)
        (hT.trans (hrd (.Vptr tB tO))) _ _
        (localst_post_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun q hq => hq)
          (hrd (.Vptr tB tO)).symm _ _
          (read_table_triple' ge fe bh bc bo pt pr tblB tblO tB tO cap hpt _t'11
            (TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty codes
              root max mtch s)
            (arrayU16 .Freeable bc 0 16 s.cntF
              ∗ (HoffsAt bo s.offsF
              ∗ (mapsto .Mint8unsigned .Freeable bh 0 u0
              ∗ (mapsto .Mint8unsigned .Freeable bh 1 u1
              ∗ (mapsto .Mint16unsigned .Freeable bh 2 u2
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) s.vbits
              ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
              ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
              ∗ (arrayU16 pg xB 0 nx extraF
              ∗ (arrayU16 pg bB 0 nb baseF
              ∗ (Hrest))))))))))) (by temps_mem)
            (by simp only [List.cons_append, List.nil_append,
                  List.forall_mem_cons]
                exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩))))
    -- `*table = t'11 + used`
      (localst_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun q hq => hq)
        (htb (.Vptr tB tO)) _ _
        (localst_post_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun q hq => hq)
          (htb (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))).symm _ _
          (bump_table_var_triple ge fe bh bc bo pt tblB tblO tB tO s.used hptW
            _t'11 ((_t'11, Val.Vptr tB tO)
              :: TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
                   codes root max mtch s)
            (arrayU16 .Freeable bc 0 16 s.cntF
              ∗ (HoffsAt bo s.offsF
              ∗ (mapsto .Mint8unsigned .Freeable bh 0 u0
              ∗ (mapsto .Mint8unsigned .Freeable bh 1 u1
              ∗ (mapsto .Mint16unsigned .Freeable bh 2 u2
              ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
              ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) s.vbits
              ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
              ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
              ∗ (arrayU16 pg xB 0 nx extraF
              ∗ (arrayU16 pg bB 0 nb baseF
              ∗ (Hrest)))))))))))) (by temps_mem) List.mem_cons_self
            (by temps_mem))))) ?_
  -- `*bits = root`
  have hbt := fun (vb tv : Val) => HLoopT_as_bits bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF u0 u1 u2
    vb tv
  refine triple_seq_only ge fe f_inflate_table
    (localst_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun q hq => hq)
      (hbt s.vbits (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))) _ _
      (localst_post_adapt ge fe (envOf bh bc bo) _ _ _ _ (fun q hq => hq)
        (hbt (.Vint (Integers.Int.repr ((root : _root_.Int)))) (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))).symm _ _
        (write_bits_var_triple ge fe bh bc bo pb bitsB bitsO hpb s.vbits root
          ((_t'11, Val.Vptr tB tO)
            :: TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
                 codes root max mtch s)
          (arrayU16 .Freeable bc 0 16 s.cntF
            ∗ (HoffsAt bo s.offsF
            ∗ (mapsto .Mint8unsigned .Freeable bh 0 u0
            ∗ (mapsto .Mint8unsigned .Freeable bh 1 u1
            ∗ (mapsto .Mint16unsigned .Freeable bh 2 u2
            ∗ (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
            ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))
            ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
            ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
            ∗ (arrayU16 pg xB 0 nx extraF
            ∗ (arrayU16 pg bB 0 nb baseF
            ∗ (Hrest)))))))))))) (by temps_mem) (by temps_mem)))) ?_
  -- `return 0`
  have hrt := HLoopT_as_ret bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB nx nb extraF baseF
        Hrest s.cntF s.offsF u0 u1 u2
    (.Vint (Integers.Int.repr ((root : _root_.Int)))) (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))
  refine triple_conseq ge fe f_inflate_table
    (return_const_triple ge fe bh bc bo ((_t'11, Val.Vptr tB tO)
            :: TLoop tblB tblO bitsB bitsO tB workB workO lensB lensO vx vb ty
                 codes root max mtch s) (hereRun u0 u1 u2)
      (u16Bytes s.cntF 16) (offsBytes s.offsF)
      (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
      ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))
      ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO) (.Vint (Integers.Int.repr ((root : _root_.Int))))
      ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
      ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
      ∗ (arrayU16 pg xB 0 nx extraF
      ∗ (arrayU16 pg bB 0 nb baseF
      ∗ (Hrest)))))))) _ (Integers.Int.repr 0) Ret
      hcenv hd1 hd2 hd3 (hereRun_length u0 u1 u2) (u16Bytes_length s.cntF 16)
      (offsBytes_length s.offsF)
      (fun le m => EvalExpr.Econst_int _ _)
      (fun m => semCast_int_int m _)
      hret)
    (fun e le hp hx => ⟨hx.1, hx.2.1, by rw [← hrt]; exact hx.2.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
    (fun _ _ _ hx => hx.elim) (fun _ _ x => x)

/-- **The loop's exit meets the epilogue.**  `main_loop_triple` leaves
    `LoopExit`, which existentially quantifies the final state and `here`'s three
    stale bytes; `epilogue_triple` wants them named.  Everything else the
    epilogue needs comes out of `ExitFacts`, except the in-bounds fact for the
    `next[huff]` write, which is `exit_write_inbounds` — the one place the
    incomplete-code argument is consumed. -/
theorem exit_epilogue (Ret : Val → HProp)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hpr : permOrder pr .Writable = true)
    (hpt : permOrder pt .Readable = true)
    (hptW : permOrder pt .Writable = true)
    (hpb : permOrder pb .Writable = true)
    (hcap31 : (cap : _root_.Int) < 2147483648)
    (htO4 : Integers.Ptrofs.unsigned tO % 4 = 0)
    (hnoC : Integers.Ptrofs.unsigned tO + 4 * (cap : _root_.Int)
              < 18446744073709551616)

    -- the `next[huff]` write's in-bounds fact.  Taken as a hypothesis rather
    -- than derived here: `exit_write_inbounds` needs `Model.nlive` unshadowed
    -- and so lives outside `section MainLoop`, while `LoopExit` lives inside.
    -- The caller supplies it; that is where the incomplete-code argument goes.
    (hinb : ∀ s : LoopSt, ExitFacts max root cap nlive workF lensF tO s →
      s.huff ≠ 0 → s.drop = 0 ∧ s.nOff = 0 ∧ s.huff = 1 ∧ 2 ≤ cap)
    (hret : ∀ (s : LoopSt) hr, (codeRegion pr tB (Integers.Ptrofs.unsigned tO) cap
        ∗ (mapsto Mptr pt tblB (Integers.Ptrofs.unsigned tblO) (.Vptr tB (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Unsigned tO (Integers.Int.repr ((s.used : _root_.Int)))))
        ∗ (mapsto .Mint32 pb bitsB (Integers.Ptrofs.unsigned bitsO)
          (.Vint (Integers.Int.repr ((root : _root_.Int))))
        ∗ (arrayU16 pw workB (Integers.Ptrofs.unsigned workO) nwork workF
        ∗ (arrayU16 pl lensB (Integers.Ptrofs.unsigned lensO) ncodes lensF
        ∗ (arrayU16 pg xB 0 nx extraF
        ∗ (arrayU16 pg bB 0 nb baseF
        ∗ (Hrest)))))))) hr →
      Ret (.Vint (Integers.Int.repr 0)) hr)
    (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LoopExit bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO tB tO cap workB
        workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb extraF
        baseF ty codes root max mtch nlive Hrest)
      (.Ssequence epilogueIf (.Ssequence bumpTableUsed
        (.Ssequence setBitsRoot retZero)))
      { normal := R.normal, brk := R.brk, cont := R.cont, ret := Ret,
        goto := R.goto } := by
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (s : LoopSt) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (w0 : Val) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (w1 : Val) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (w2 : Val) => ?_)
  refine triple_exists ge fe f_inflate_table _ _ _
    (fun (hef : ExitFacts max root cap nlive workF lensF tO s) => ?_)
  refine epilogue_triple ge fe bh bc bo pt pb pr pw pl pg tblB tblO bitsB bitsO
    tB tO cap workB workO nwork workF lensB lensO ncodes lensF xB bB vx vb nx nb
    extraF baseF ty codes root max mtch Hrest s w0 w1 w2 Ret hcenv hd1 hd2 hd3
    hpr hpt hptW hpb hcap31 htO4 hnoC
    (by have := hef.lenmax; have := hef.max15; omega)
    (by have := hef.droproot; have := hef.rootmax; have := hef.lenmax; omega)
    (by have := hef.hufflt; have := hef.max15
        have h2 : (2 : Nat) ^ max ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
        omega)
    -- `cntb`/`offsb` come out of `ExitFacts`, not from `∀ s : LoopSt`
    -- hypotheses, which no caller could discharge
    (hinb s hef) hef.nOaddr hef.cntb hef.offsb (hret s) R

end MainLoop

/-! #### `WorkChar` from the sort loop's postcondition

`main_loop_triple` assumes `WorkChar`; this is what discharges it.  The only
program-derived input is `Placed lensF workF codes codes` — the sort loop's
strengthened postcondition (§12 `Post7`), saying every live symbol sits at its
own `Model.posOf` slot.  Everything else is ambient: A2 (`lens ≤ 15`), the
over-subscription check (`kraftOk`, from §9's `Post5`), the max scan's
`max = maxLen` (§5), and A3.

The work is all in `Model.place_len`, which inverts the placement map: it turns
"symbol `t` went to slot `posOf t`" into "slot `i` holds a symbol whose length
is `i`'s block index" — and *that* is what makes `work[]` sorted. -/

open InflateTable.Model in
/-- **The sort loop's output has every property the main loop needs.** -/
theorem workchar_of_placed
    (nwork ncodes maxv mtch nx nb codes : Nat) (workF lensF : Nat → Nat)
    (hb : ∀ i, i < codes → lensF i ≤ 15)
    (hplaced : Placed lensF workF codes codes)
    (hkraft : kraftOk lensF codes)
    (hmax : maxv = maxLen lensF codes)
    (hnw : nlive lensF codes ≤ nwork)
    (hnc : codes ≤ ncodes)
    (ha3x : ∀ i, i < codes → mtch ≤ i → i - mtch < nx)
    (ha3b : ∀ i, i < codes → mtch ≤ i → i - mtch < nb)
    -- stated over symbol *values* like `ha3x`/`ha3b`, since that is the form
    -- A3 comes in; `hwlt` converts to slot indices
    (hvx : ∀ i, i < codes → mtch ≤ i → vx = .Vptr xB Integers.Ptrofs.zero)
    (hvb : ∀ i, i < codes → mtch ≤ i → vb = .Vptr bB Integers.Ptrofs.zero) :
    WorkChar nwork ncodes (nlive lensF codes) maxv mtch nx nb workF lensF vx vb xB bB := by
  have hpl := fun i (hi : i < nlive lensF codes) =>
    place_len lensF workF codes i hb hplaced hi
  have hwlt : ∀ i, i < nlive lensF codes → workF i < codes := by
    intro i hi
    obtain ⟨_, _, _, _, _, _, h⟩ := hpl i hi
    exact h
  refine { hnl := hnw, hwlt := fun i hi => by
             have := hwlt i hi; omega,
           hsort := ?_, hlive := ?_, hlmax := ?_, hlast := ?_, hmass := ?_,
           ha3x := fun i hi => ha3x _ (hwlt i hi),
           ha3b := fun i hi => ha3b _ (hwlt i hi),
           hvx := fun i hi => hvx _ (hwlt i hi),
           hvb := fun i hi => hvb _ (hwlt i hi) }
  · -- sorted: block indices are monotone, and blocks do not overlap
    intro i j hij hj
    obtain ⟨li, _, _, hi3, hi4, hi5, _⟩ := hpl i (by omega)
    obtain ⟨lj, _, _, hj3, hj4, hj5, _⟩ := hpl j hj
    rw [hi5, hj5]
    rcases Nat.lt_or_ge lj li with h | h
    · exfalso
      have := offs_mono lensF codes (show lj + 1 ≤ li from by omega)
      omega
    · exact h
  · intro i hi
    obtain ⟨_, h1, _, _, _, h5, _⟩ := hpl i hi
    omega
  · intro i hi
    have hlt := hwlt i hi
    obtain ⟨_, h1, _, _, _, h5, _⟩ := hpl i hi
    have := (lens_between lensF codes (workF i) hlt (by omega)).2
    omega
  · -- the last slot holds a longest code
    intro hpos
    obtain ⟨l, hl1, hl15, hl3, hl4, hl5, _⟩ := hpl (nlive lensF codes - 1)
      (by omega)
    have h16 : offs lensF codes 16 = nlive lensF codes :=
      offs_16_eq_nlive lensF codes hb
    have hup : offs lensF codes (l + 1) ≤ nlive lensF codes := by
      have := offs_mono lensF codes (show l + 1 ≤ 16 from by omega); omega
    have hfull : offs lensF codes (l + 1) = nlive lensF codes := by omega
    rw [hl5, hmax]
    refine maxLen_char lensF codes l hb hl15 (fun l' hl' hl'15 => ?_) ?_
    · have h1 := offs_succ lensF codes l' (by omega)
      have h2 := offs_mono lensF codes (show l + 1 ≤ l' from by omega)
      have h3 := offs_mono lensF codes (show l' + 1 ≤ 16 from by omega)
      omega
    · refine Or.inr (fun hz => ?_)
      have h1 := offs_succ lensF codes l hl1
      omega
  · -- Kraft: regroup the position-indexed mass by length, then apply the check
    have hrange : ∀ i, i < nlive lensF codes →
        1 ≤ lensF (workF i) ∧ lensF (workF i) ≤ 15 := by
      intro i hi
      obtain ⟨_, h1, h2, _, _, h5, _⟩ := hpl i hi
      omega
    rw [massBelow_eq_massSum (fun k => lensF (workF k)) (nlive lensF codes)
          hrange,
        massSum_congr _ (count lensF codes)
          (fun l hl1 hl15 => cntSeg_place lensF workF codes l hb hplaced hl1
            hl15)]
    have := massSum_count_le lensF codes hkraft
    show massSum (count lensF codes) ≤ 2 ^ 15
    omega





/-! ## §26b The loop's entry state

`main_loop_triple` needs `LoopInv … n` to hold when the loop starts.  This is
that instance: the state the setup statements (inftrees.c:204-214) leave, and
the proof that it satisfies all thirty `LoopFacts` fields.

Nothing here is about the program — it is pure model reasoning, so it lives
outside the `MainLoop` section (where `nlive` is a section variable that
shadows `Model.nlive`). -/

open InflateTable.Model in
/-- **The loop invariant holds on entry.**

    The measure starts at `nlive`.  Most fields are immediate; the four worth
    naming are `lenw` (`min` is the first sorted symbol's length —
    `first_slot_minLen`), `cntc` (the counting loop's `count[]` re-indexed as a
    position count — `cntSeg_place`), `hJ` (no mass consumed and `rev l 0 = 0`,
    so the code invariant holds trivially), and `subfit`, which is vacuous
    because `drop = 0 ≠ root`. -/
theorem loopfacts_entry
    (nwork ncodes max mtch nx nb cap codes root : Nat) (lensF workF : Nat → Nat)
    (tO : Integers.Ptrofs) (offsF : Nat → Nat) (vi vf : Val)
    (vl : Integers.Int) (v0 v1 v2 vbits : Val)
    (hwc : WorkChar nwork ncodes (nlive lensF codes) max mtch nx nb workF lensF vx vb xB bB)
    (hb : ∀ i, i < codes → lensF i ≤ 15)
    (hplaced : Placed lensF workF codes codes)
    (hmaxdef : max = maxLen lensF codes) (hmaxnz : max ≠ 0)
    (hroot1 : 1 ≤ root) (hroot15 : root ≤ 15) (hrootmax : root ≤ max)
    (hminroot : minLen lensF codes ≤ root)
    (hc16 : codes < 65536)
    (hoffsb : ∀ j, offsF j < 65536)
    (hused : 2 ^ root ≤ cap) :
    LoopFacts (nlive lensF codes) max root nwork ncodes nx nb mtch
      (nlive lensF codes) cap workF lensF tO
      (entrySt (minLen lensF codes) root tO lensF workF codes offsF vi vf vl
        v0 v1 v2 vbits) := by
  have hpos : 0 < nlive lensF codes :=
    nlive_pos_of_maxLen lensF codes (by rw [← hmaxdef]; exact hmaxnz)
  have hfirst : lensF (workF 0) = minLen lensF codes :=
    first_slot_minLen lensF workF codes hb hplaced hwc.hsort hpos
  have hmn1 : 1 ≤ minLen lensF codes := by
    rw [← hfirst]; exact hwc.hlive 0 hpos
  have hmn15 : minLen lensF codes ≤ 15 := by
    rw [← hfirst]; have := hwc.hlmax 0 hpos; have := hwc.hnl; omega
  have hmnmax : minLen lensF codes ≤ max := by
    rw [← hfirst]; exact hwc.hlmax 0 hpos
  have hrootpow : root ≤ 2 ^ root := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hcnt1 : 1 ≤ count lensF codes (minLen lensF codes) := by
    have hc := hwc.hsort 0 0 (Nat.le_refl _) hpos
    have := cntSeg_place lensF workF codes (minLen lensF codes) hb hplaced
      hmn1 hmn15
    rw [← this]
    exact cntSeg_pos _ 0 (nlive lensF codes) _ 0 (Nat.le_refl _) hpos hfirst
  have hnotlast : minLen lensF codes ≠ max → 0 + 1 < nlive lensF codes := by
    intro hnm
    rcases Nat.lt_or_ge 1 (nlive lensF codes) with h | h
    · exact h
    · exfalso
      have h1 : nlive lensF codes = 1 := by omega
      have := hwc.hlast hpos
      rw [h1] at this
      exact hnm (by rw [← hfirst]; simpa using this)
  exact {
    measure := by show nlive lensF codes + 0 = nlive lensF codes; omega
    len1 := hmn1
    len15 := hmn15
    lenmax := hmnmax
    low32 := by show (4294967295 : Nat) < 4294967296; omega
    offsb := hoffsb
    droplen := by show 0 ≤ minLen lensF codes; omega
    droproot := Or.inl rfl
    curr1 := hroot1
    currmax := by show root + 0 ≤ max; omega
    lmdcurr := by show minLen lensF codes - 0 ≤ root; omega
    root15 := hroot15
    max15 := by rw [hmaxdef]; exact maxLen_le lensF codes hb
    root1 := hroot1
    symlt := by show 0 < nwork; have := hwc.hnl; omega
    a3x := hwc.ha3x 0 hpos
    a3b := hwc.ha3b 0 hpos
    symnext := by
      show _ = 1 → minLen lensF codes ≠ max → 0 + 1 < nwork
      intro _ hnm; have := hnotlast hnm; have := hwc.hnl; omega
    lensnext := by
      show _ = 1 → minLen lensF codes ≠ max → workF (0 + 1) < ncodes
      intro _ hnm; exact hwc.hwlt _ (hnotlast hnm)
    hufflt := by show 0 < 2 ^ minLen lensF codes; exact Nat.two_pow_pos _
    nOaddr := by
      show Integers.Ptrofs.unsigned tO
        = Integers.Ptrofs.unsigned tO + 4 * ((0 : Nat) : _root_.Int)
      obtain ⟨A, hA⟩ : ∃ A : _root_.Int,
        Integers.Ptrofs.unsigned tO = A := ⟨_, rfl⟩
      rw [hA]; show A = A + 4 * ((0 : Nat) : _root_.Int); omega
    room := by show 0 + 2 ^ root ≤ cap; omega
    usedcap := hused
    mncap := by show minLen lensF codes ≤ cap; omega
    cnt1 := by show 1 ≤ count lensF codes (minLen lensF codes); exact hcnt1
    cntb := by
      intro j
      show count lensF codes j < 65536
      have := count_le lensF codes j; omega
    symlive := hpos
    lenw := by show minLen lensF codes = lensF (workF 0); exact hfirst.symm
    cntc := by
      intro j hj
      show count lensF codes j
        = cntSeg (fun k => lensF (workF k)) 0 (nlive lensF codes) j
      by_cases hj15 : j ≤ 15
      · exact (cntSeg_place lensF workF codes j hb hplaced hj hj15).symm
      · -- nothing is that long, on either side
        rw [cntSeg_zero_eq]
        rw [InflateTable.Model.count_eq_zero lensF codes j (fun i hi he => by
              have := hb i hi; omega)]
        refine (List.length_eq_zero_iff.mpr (List.filter_eq_nil_iff.mpr
          (fun k hk => ?_))).symm
        simp only [decide_eq_true_eq]
        intro hcon
        have h1 := hwc.hlmax k (List.mem_range.mp hk)
        have hm : max ≤ 15 := by rw [hmaxdef]; exact maxLen_le lensF codes hb
        omega
    hJ := by
      show massBelow (fun k => lensF (workF k)) 0
        = rev (minLen lensF codes) 0 * 2 ^ (15 - minLen lensF codes)
      rw [rev_zero, Nat.zero_mul]
      rfl
    useq := by show 2 ^ root = 0 + 2 ^ root; omega
    dzcurr := fun _ => rfl
    dzlow := fun _ => rfl
    dropfired := by
      show (0 : Nat) = root → root < max
      intro h; exact absurd h (by omega)
    dzoff := fun _ => rfl
    subfit := by
      show (0 : Nat) = root → _
      intro h; exact absurd h (by omega) }

/-! ## §26c The loop's exit, and why the epilogue's write is in bounds

        if (huff != 0) { here.op = 64; here.bits = len - drop;
                         here.val = 0; next[huff] = here; }

`next[huff]` indexes the *current sub-table* by the *whole* code, which is out
of bounds unless `drop = 0`.  The C's own comment says why it is safe —
"guaranteed to have at most one remaining entry, since if the code is
incomplete, the maximum code length that was allowed to get this far is one
bit" — so the bound is a theorem about Huffman codes, not a check.

The chain is:

* `huff ≠ 0` at exit ⟹ the consumed mass is **not** full (`ExitFacts.hzero`).
  This is where the reversed-code invariant pays off a second time: a full
  code space forces `rev max huff + 1 = 2^max`, hence `bwInc` wraps to a code
  whose reversal is `0`, hence (`rev_eq_zero`) to `huff = 0` itself.
* mass not full ⟹ `leftAt 15 > 0` (`leftAt_15_massSum`: `left` *is* the unused
  mass) ⟹ the code is incomplete.
* incomplete, having passed the test at inftrees.c:146-147, ⟹ `max = 1`.
* `max = 1` ⟹ `drop = 0` (a sub-table needs `root < max`, and `root ≥ 1`),
  so `nOff = 0`, `curr = root = 1`, and `huff < 2^1` with `huff ≠ 0` pins
  `huff = 1` — entry 1 of a table with `2 ≤ cap` entries. -/

open InflateTable.Model in
/-- **The epilogue's write is in bounds.**  See the section header for the
    argument; `hchk` is what §10's `chk6_triple` records (the incomplete-set
    test passed), and `hplaced`/`hb` are the sort loop's output as usual. -/
theorem exit_write_inbounds
    (max root cap codes ty : Nat) (workF lensF : Nat → Nat)
    (tO : Integers.Ptrofs) (s : LoopSt)
    (hef : ExitFacts max root cap (nlive lensF codes) workF lensF tO s)
    (hb : ∀ i, i < codes → lensF i ≤ 15)
    (hplaced : Placed lensF workF codes codes)
    (hchk : 0 < leftAt lensF codes 15 → ty ≠ 0 ∧ max = 1)
    (hne0 : s.huff ≠ 0) :
    max = 1 ∧ s.drop = 0 ∧ s.nOff = 0 ∧ s.curr = root ∧ s.huff = 1
      ∧ 2 ≤ cap := by
  -- the mass is not full, so `left` is positive, so the code is incomplete
  have hlt := hef.hzero hne0
  have hmass : massBelow (fun k => lensF (workF k)) (nlive lensF codes)
      = massSum (count lensF codes) := by
    refine (massBelow_eq_massSum (fun k => lensF (workF k))
      (nlive lensF codes) (fun i hi => ?_)).trans ?_
    · obtain ⟨_, h1, h2, _, _, h5, _⟩ :=
        place_len lensF workF codes i hb hplaced hi
      omega
    · exact massSum_congr _ _ (fun l hl1 hl15 =>
        cntSeg_place lensF workF codes l hb hplaced hl1 hl15)
  have hleft : 0 < leftAt lensF codes 15 := by
    rw [leftAt_15_massSum]
    rw [hmass] at hlt
    have h215 : (2 : Nat) ^ 15 = 32768 := by decide
    rw [h215] at hlt
    omega
  obtain ⟨_, hmax1⟩ := hchk hleft
  -- `max = 1` leaves no room for a sub-table, so `drop` never moved
  have hdrop : s.drop = 0 := by
    rcases hef.droproot with h | h
    · exact h
    · exfalso; have := hef.dropfired h; have := hef.root1; omega
  have hoff := hef.dzoff hdrop
  have hcurr := hef.dzcurr hdrop
  have hroot : root = 1 := by
    have h1 := hef.root1
    have h2 := hef.rootmax
    omega
  have hh : s.huff = 1 := by
    have := hef.hufflt
    rw [hmax1] at this
    omega
  refine ⟨hmax1, hdrop, hoff, hcurr, hh, ?_⟩
  have := hef.room
  rw [hcurr, hoff, hroot] at this
  omega

/-! ## §27 The AST guard

Every chunk above is a hand transcription of a sub-term of
`f_inflate_table.fn_body`.  `body_matches` pins **all of them at once**, at
their real positions, with a single `rfl`.  It works by definitional equality:
both sides are closed terms, so `rfl` succeeds exactly when they are the same
term after unfolding the `abbrev`s.  No tactics, no axioms.

**What this does and does not certify.**  The segment `abbrev`s above whose
docstring says "generated from the AST" were produced *from the AST text
itself*, so those parts of the guard are tautological and certify nothing;
they exist to give the chain named handles for statements proved by generic
single-statement triples.  The guard's real content is the **named chunks** —
`loop1`-`loop7`, `maxZeroBlock`, `chk6`, `offs1Init`, `switchStmt`,
`enoughChk`, `loopBody` — and transitively everything nested inside them
(`entryChoose`, `fillLoop`, `subTableBody`, `backPtrBlock`, `lookLoop`,
`incrInit`/`incrLoop`/`incrFix`, `advIfStmt`, `t10Stmt`, …).

During development it caught two chunks that were transcriptions of the
*wrong statement*. -/
/-- The whole function body, reassembled from the verified chunks. -/
abbrev fullBody : Stmt :=
  .Ssequence setBase
  (.Ssequence setExtra
  (.Ssequence setMatch
  (.Ssequence seg3
  (.Ssequence seg4
  (.Ssequence readRoot
  (.Ssequence seg6
  (.Ssequence clamp1Stmt
  (.Ssequence (.Sifthenelse (.Ebinop .Oeq (.Etempvar _max tuint)
    (.Econst_int (Integers.Int.repr 0) tint) tint) maxZeroBlock .Sskip)
  (.Ssequence seg9
  (.Ssequence clamp2Stmt
  (.Ssequence initLeft
  (.Ssequence seg12
  (.Ssequence (chk6)
  (.Ssequence (offs1Init)
  (.Ssequence seg15
  (.Ssequence seg16
  (.Ssequence (switchStmt)
  (.Ssequence setHuff0
  (.Ssequence setSym0
  (.Ssequence setLenMin
  (.Ssequence setNextTbl
  (.Ssequence setCurrRoot
  (.Ssequence setDrop0
  (.Ssequence setLowM1
  (.Ssequence setUsed
  (.Ssequence setMask
  (.Ssequence (enoughChk _t'5 _t'6)
  (.Ssequence (.Sloop loopBody .Sskip)
  (.Ssequence epilogueIf
  (.Ssequence bumpTableUsed
  (.Ssequence setBitsRoot
  (retZero))))))))))))))))))))))))))))))))

/-- **THE AST GUARD.** -/
theorem body_matches : f_inflate_table.fn_body = fullBody := rfl

end InflateTable.Body
