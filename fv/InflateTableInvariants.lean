/-
  The pure counting model of `inflate_table` (inftrees.c:46-311), and the
  arithmetic lemmas its memory-safety loop invariants need.

  Everything in this file is semantics-free: plain functions on `Nat` mirroring
  the quantities the C code computes (`count[]`, `offs[]`, `left`, `max`, the
  backwards code increment), so each lemma can be proved — and reviewed — in
  isolation from the Clight machinery.  The safety proof in
  InflateTableSafety.lean consumes these through its loop invariants.

  Status: all statements PROVED (Phase 1 complete).  No Mathlib, no axioms
  beyond Lean's standard three, no `native_decide`.  None of these depends on
  the ENOUGH/Kraft exhaustive-search bound — see fv/memory-safety.md ("key
  discovery"): the runtime checks make that theorem unnecessary for safety.
-/

namespace InflateTable.Model

/-! ## The quantities the C code computes -/

/-- `count[l]` after the counting loop (inftrees.c:115-119): the number of
    symbols with code length exactly `l`. -/
def count (lensF : Nat → Nat) (codes l : Nat) : Nat :=
  ((List.range codes).filter (fun i => lensF i = l)).length

/-- The number of live (nonzero-length) symbols — exactly the entries the sort
    loop (inftrees.c:155-156) writes into `work[]`. -/
def nlive (lensF : Nat → Nat) (codes : Nat) : Nat :=
  ((List.range codes).filter (fun i => lensF i ≠ 0)).length

/-- `offs[l]` after the offsets loop (inftrees.c:150-152):
    `offs[1] = 0`, `offs[l+1] = offs[l] + count[l]`; equivalently the number of
    symbols with length in `[1, l)`. -/
def offs (lensF : Nat → Nat) (codes l : Nat) : Nat :=
  ((List.range codes).filter (fun i => 0 < lensF i ∧ lensF i < l)).length

/-- `max` (inftrees.c:123-124): the largest used code length (0 if none). -/
def maxLen (lensF : Nat → Nat) (codes : Nat) : Nat :=
  (List.range codes).foldl (fun m i => Nat.max m (lensF i)) 0

/-- `min` (inftrees.c:135-136): the smallest nonzero code length
    (meaningful only when `maxLen ≠ 0`). -/
def minLen (lensF : Nat → Nat) (codes : Nat) : Nat :=
  (List.range codes).foldl
    (fun m i => if lensF i = 0 then m else Nat.min m (lensF i)) 16

/-- `left` after processing lengths `1..l` (inftrees.c:140-145):
    `left₀ = 1`, `left_{l+1} = 2·left_l − count[l+1]`.  Over-subscription is
    `left < 0` at some step; incompleteness is `left > 0` at `l = 15`. -/
def leftAt (lensF : Nat → Nat) (codes : Nat) : Nat → _root_.Int
  | 0 => 1
  | l + 1 => 2 * leftAt lensF codes l - (count lensF codes (l + 1) : _root_.Int)

/-- The over-subscription check passed (the loop at inftrees.c:140-145 did not
    return −1). -/
def kraftOk (lensF : Nat → Nat) (codes : Nat) : Prop :=
  ∀ l, l ≤ 15 → 0 ≤ leftAt lensF codes l

/-! ## The backwards code increment (inftrees.c:246-255)

    incr = 1 << (len-1); while (huff & incr) incr >>= 1;
    if (incr) huff = (huff & (incr-1)) + incr; else huff = 0;

Modelled with the bit position as fuel: at fuel `k` the C variable `incr`
is `2^(k-1)`, and `huff & (incr-1) = huff % incr` for a power of two. -/

def bwIncGo (huff : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      let incr := 2 ^ k
      if huff / incr % 2 = 1 then bwIncGo huff k
      else huff % incr + incr

/-- The next `len`-bit code after `huff`, in deflate's reversed-bit order. -/
def bwInc (huff len : Nat) : Nat := bwIncGo huff len

/-! ## Auxiliary facts (private)

Filter-length algebra and `foldl` min/max facts, over plain lists so each is a
five-line induction.  Everything below instantiates them at `List.range codes`. -/

/-- A filter and its complement partition the length. -/
private theorem length_filter_not_add {α : Type u} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun a => !(p a))).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases hp : p a <;> simp [List.filter_cons, hp] <;> omega

/-- Filtering with a weaker predicate keeps at least as many elements. -/
private theorem length_filter_mono {α : Type u} (p q : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = true → q a = true) →
      (l.filter p).length ≤ (l.filter q).length := by
  intro l
  induction l with
  | nil => intro _; exact Nat.le_refl 0
  | cons a t ih =>
      intro h
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      cases hp : p a
      · cases hq : q a <;> simp [List.filter_cons, hp, hq] <;> omega
      · have hq := h a List.mem_cons_self hp
        simp [List.filter_cons, hp, hq]
        omega

/-- A filter whose predicate splits as a disjoint disjunction splits its
    length as a sum. -/
private theorem length_filter_or {α : Type u} (p q r : α → Bool) :
    ∀ l : List α, (∀ a ∈ l, p a = (q a || r a)) →
      (∀ a ∈ l, ¬(q a = true ∧ r a = true)) →
      (l.filter p).length = (l.filter q).length + (l.filter r).length := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a t ih =>
      intro h hx
      have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
                    (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      have ha := h a List.mem_cons_self
      cases hq : q a
      · cases hr : r a
        · have hp : p a = false := by rw [ha, hq, hr]; rfl
          simp [List.filter_cons, hp, hq, hr] <;> omega
        · have hp : p a = true := by rw [ha, hq, hr]; rfl
          simp [List.filter_cons, hp, hq, hr] <;> omega
      · cases hr : r a
        · have hp : p a = true := by rw [ha, hq, hr]; rfl
          simp [List.filter_cons, hp, hq, hr] <;> omega
        · exact absurd ⟨hq, hr⟩ (hx a List.mem_cons_self)

/-- A `count` vanishes when nothing has that length. -/
theorem count_eq_zero (lensF : Nat → Nat) (codes l : Nat)
    (h : ∀ i, i < codes → lensF i ≠ l) : count lensF codes l = 0 := by
  unfold count
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro i hi
  simp only [decide_eq_true_eq]
  exact h i (List.mem_range.mp hi)

/-- A `count` is positive when a witness has that length. -/
private theorem count_pos (lensF : Nat → Nat) (codes l i : Nat)
    (hi : i < codes) (he : lensF i = l) : 0 < count lensF codes l := by
  unfold count
  exact List.length_pos_of_mem
    (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [he]⟩)

/-- The initial accumulator never exceeds a max-fold. -/
private theorem foldl_max_init_le (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat),
      a ≤ l.foldl (fun m i => Nat.max m (f i)) a := by
  intro l
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons j t ih =>
      intro a
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- Every element is below a max-fold. -/
private theorem foldl_max_mem_le (f : Nat → Nat) :
    ∀ (l : List Nat) (a x : Nat), x ∈ l →
      f x ≤ l.foldl (fun m i => Nat.max m (f i)) a := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons j t ih =>
      intro a x hx
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with he | hmem
      · subst he
        exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_init_le f t _)
      · exact ih _ x hmem

/-- A max-fold stays below any common upper bound. -/
private theorem foldl_max_le (f : Nat → Nat) :
    ∀ (l : List Nat) (a c : Nat), a ≤ c → (∀ x ∈ l, f x ≤ c) →
      l.foldl (fun m i => Nat.max m (f i)) a ≤ c := by
  intro l
  induction l with
  | nil => intro _ _ ha _; exact ha
  | cons j t ih =>
      intro a c ha h
      simp only [List.foldl_cons]
      refine ih _ c ?_ (fun x hx => h x (List.mem_cons_of_mem _ hx))
      exact Nat.max_le.mpr ⟨ha, h j List.mem_cons_self⟩

/-- A max-fold is the initial accumulator or is attained by an element. -/
private theorem foldl_max_attained (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat),
      l.foldl (fun m i => Nat.max m (f i)) a = a
      ∨ ∃ x ∈ l, l.foldl (fun m i => Nat.max m (f i)) a = f x := by
  intro l
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons j t ih =>
      intro a
      simp only [List.foldl_cons]
      rcases ih (Nat.max a (f j)) with h | ⟨x, hx, he⟩
      · rcases Nat.le_total a (f j) with hle | hle
        · exact Or.inr ⟨j, List.mem_cons_self, by rw [h]; exact Nat.max_eq_right hle⟩
        · exact Or.inl (by rw [h]; exact Nat.max_eq_left hle)
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, he⟩

/-- A nonzero `maxLen` is attained by some symbol. -/
private theorem exists_eq_maxLen (lensF : Nat → Nat) (codes : Nat)
    (h : maxLen lensF codes ≠ 0) :
    ∃ i, i < codes ∧ lensF i = maxLen lensF codes := by
  rcases foldl_max_attained lensF (List.range codes) 0 with h0 | ⟨x, hx, he⟩
  · exact absurd h0 h
  · exact ⟨x, List.mem_range.mp hx, he.symm⟩

/-- A guarded min-fold never exceeds its initial accumulator. -/
private theorem foldl_min_le_init (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat),
      l.foldl (fun m i => if f i = 0 then m else Nat.min m (f i)) a ≤ a := by
  intro l
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons j t ih =>
      intro a
      simp only [List.foldl_cons]
      by_cases hj : f j = 0
      · rw [if_pos hj]; exact ih a
      · rw [if_neg hj]
        exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

/-- A guarded min-fold is below every element its guard admits. -/
private theorem foldl_min_le_mem (f : Nat → Nat) :
    ∀ (l : List Nat) (a x : Nat), x ∈ l → f x ≠ 0 →
      l.foldl (fun m i => if f i = 0 then m else Nat.min m (f i)) a ≤ f x := by
  intro l
  induction l with
  | nil => intro _ x hx _; cases hx
  | cons j t ih =>
      intro a x hx hnz
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with he | hmem
      · subst he
        rw [if_neg hnz]
        exact Nat.le_trans (foldl_min_le_init f t _) (Nat.min_le_right _ _)
      · exact ih _ x hmem hnz

/-- A guarded min-fold stays above any common lower bound. -/
private theorem foldl_min_ge (f : Nat → Nat) :
    ∀ (l : List Nat) (a c : Nat), c ≤ a → (∀ x ∈ l, f x ≠ 0 → c ≤ f x) →
      c ≤ l.foldl (fun m i => if f i = 0 then m else Nat.min m (f i)) a := by
  intro l
  induction l with
  | nil => intro _ _ ha _; exact ha
  | cons j t ih =>
      intro a c ha h
      simp only [List.foldl_cons]
      refine ih _ c ?_ (fun x hx => h x (List.mem_cons_of_mem _ hx))
      by_cases hj : f j = 0
      · rw [if_pos hj]; exact ha
      · rw [if_neg hj]
        exact Nat.le_min.mpr ⟨ha, h j List.mem_cons_self hj⟩

/-! ## Lemmas feeding the loop invariants

Each is labelled with the access(es) of the inventory table in
fv/memory-safety.md it protects. -/

/-- Partition: zero-length symbols plus live symbols exhaust `codes`. -/
theorem count_zero_add_nlive (lensF : Nat → Nat) (codes : Nat) :
    count lensF codes 0 + nlive lensF codes = codes := by
  have h := length_filter_not_add (fun i => decide (lensF i = 0)) (List.range codes)
  rw [List.length_range] at h
  unfold count nlive
  have he : (fun i => decide (lensF i ≠ 0))
      = (fun a => !(decide (lensF a = 0))) := by
    funext a; simp [ne_eq, decide_not]
  rw [he]
  exact h

/-- Access #6/#7: at most `codes` entries are ever placed in `work[]`. -/
theorem nlive_le_codes (lensF : Nat → Nat) (codes : Nat) :
    nlive lensF codes ≤ codes := by
  have h := List.length_filter_le (fun i => decide (lensF i ≠ 0)) (List.range codes)
  simpa [nlive, List.length_range] using h

/-- The recurrence the offsets loop implements (inftrees.c:150-152). -/
theorem offs_succ (lensF : Nat → Nat) (codes l : Nat) (hl : 1 ≤ l) :
    offs lensF codes (l + 1) = offs lensF codes l + count lensF codes l := by
  unfold offs count
  refine length_filter_or _ _ _ (List.range codes) (fun i _ => ?_) (fun i _ => ?_)
  · rw [← Bool.decide_or, decide_eq_decide]
    omega
  · simp only [decide_eq_true_eq]
    omega

/-- Every offset is bounded by the live count.  (The A2 hypothesis turned out
    to be unnecessary — the bound is a pure subset argument; the binder is kept
    for interface stability with the plan.) -/
theorem offs_le_nlive (lensF : Nat → Nat) (codes l : Nat)
    (_hb : ∀ i, i < codes → lensF i ≤ 15) :
    offs lensF codes l ≤ nlive lensF codes := by
  unfold offs nlive
  refine length_filter_mono _ _ (List.range codes) (fun i _ hi => ?_)
  simp only [decide_eq_true_eq] at hi ⊢
  omega

/-- Access #6, the sort-loop write bound: when the `k`-th symbol of length `l`
    is placed (0-indexed, `k < count[l]`), the write index `offs[l] + k` is
    strictly below `nlive ≤ codes`.  This is the exact index
    `work[offs[lens[sym]]++]` uses at inftrees.c:156. -/
theorem sort_write_lt_nlive (lensF : Nat → Nat) (codes l k : Nat)
    (hb : ∀ i, i < codes → lensF i ≤ 15)
    (hl : 1 ≤ l) (_hl15 : l ≤ 15) (hk : k < count lensF codes l) :
    offs lensF codes l + k < nlive lensF codes := by
  have h1 := offs_succ lensF codes l hl
  have h2 := offs_le_nlive lensF codes (l + 1) hb
  omega

/-- Access #9/#11, code-bound preservation: the backwards increment keeps a
    `len`-bit code `len`-bit.  (`bwInc huff len = 0` models the C `huff = 0`
    wrap when all bits are set.)  In fact the bound needs no hypothesis at
    all — `bwIncGo` produces a `len`-bit value for ANY input. -/
theorem bwIncGo_lt (huff : Nat) : ∀ k, bwIncGo huff k < 2 ^ k := by
  intro k
  induction k with
  | zero => simp [bwIncGo]
  | succ n ih =>
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
        rw [Nat.pow_succ]; omega
      simp only [bwIncGo]
      by_cases h : huff / 2 ^ n % 2 = 1
      · rw [if_pos h]; omega
      · rw [if_neg h]
        have hm : huff % 2 ^ n < 2 ^ n := Nat.mod_lt _ hpos
        omega

theorem bwInc_lt (huff len : Nat) (_h : huff < 2 ^ len) :
    bwInc huff len < 2 ^ len :=
  bwIncGo_lt huff len

/-- Monotone in truncation: dropping to a longer length keeps the bound (the
    main loop grows `len` while `huff` keeps its value; inftrees.c:261). -/
theorem lt_pow_mono (huff len len' : Nat) (h : huff < 2 ^ len) (hle : len ≤ len') :
    huff < 2 ^ len' :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hle)

/-- Access #12 (`next[huff]` at inftrees.c:304), part 1: if the code is
    incomplete (`left > 0` after all 15 lengths) and passed the check at
    inftrees.c:146-147 with `max = 1`, there is exactly one live symbol, and
    it has length 1. -/
theorem incomplete_count_one (lensF : Nat → Nat) (codes : Nat)
    (hmax : maxLen lensF codes = 1)
    (hincpl : 0 < leftAt lensF codes 15) :
    count lensF codes 1 = 1 := by
  -- every length is ≤ 1, so count[l] = 0 for l ≥ 2
  have hub : ∀ i, i < codes → lensF i ≤ 1 := by
    intro i hi
    have h : lensF i ≤ maxLen lensF codes :=
      foldl_max_mem_le lensF (List.range codes) 0 i (List.mem_range.mpr hi)
    omega
  have hc : ∀ l, 2 ≤ l → count lensF codes l = 0 := by
    intro l hl
    refine count_eq_zero lensF codes l (fun i hi he => ?_)
    have := hub i hi
    omega
  -- maxLen = 1 is attained, so count[1] ≥ 1
  have hge : 0 < count lensF codes 1 := by
    obtain ⟨i, hi, he⟩ := exists_eq_maxLen lensF codes (by rw [hmax]; omega)
    exact count_pos lensF codes 1 i hi (by rw [he, hmax])
  -- unfold the recurrence: leftAt 15 = 2^14 * (2 - count[1])
  have u : ∀ l : Nat, leftAt lensF codes (l + 1)
      = 2 * leftAt lensF codes l - (count lensF codes (l + 1) : _root_.Int) :=
    fun _ => rfl
  have z : leftAt lensF codes 0 = 1 := rfl
  have c2 := hc 2 (by omega);   have c3 := hc 3 (by omega)
  have c4 := hc 4 (by omega);   have c5 := hc 5 (by omega)
  have c6 := hc 6 (by omega);   have c7 := hc 7 (by omega)
  have c8 := hc 8 (by omega);   have c9 := hc 9 (by omega)
  have c10 := hc 10 (by omega); have c11 := hc 11 (by omega)
  have c12 := hc 12 (by omega); have c13 := hc 13 (by omega)
  have c14 := hc 14 (by omega); have c15 := hc 15 (by omega)
  have e0 : leftAt lensF codes 1
      = 2 * leftAt lensF codes 0 - (count lensF codes 1 : _root_.Int) := u 0
  have e1 : leftAt lensF codes 2
      = 2 * leftAt lensF codes 1 - (count lensF codes 2 : _root_.Int) := u 1
  have e2 : leftAt lensF codes 3
      = 2 * leftAt lensF codes 2 - (count lensF codes 3 : _root_.Int) := u 2
  have e3 : leftAt lensF codes 4
      = 2 * leftAt lensF codes 3 - (count lensF codes 4 : _root_.Int) := u 3
  have e4 : leftAt lensF codes 5
      = 2 * leftAt lensF codes 4 - (count lensF codes 5 : _root_.Int) := u 4
  have e5 : leftAt lensF codes 6
      = 2 * leftAt lensF codes 5 - (count lensF codes 6 : _root_.Int) := u 5
  have e6 : leftAt lensF codes 7
      = 2 * leftAt lensF codes 6 - (count lensF codes 7 : _root_.Int) := u 6
  have e7 : leftAt lensF codes 8
      = 2 * leftAt lensF codes 7 - (count lensF codes 8 : _root_.Int) := u 7
  have e8 : leftAt lensF codes 9
      = 2 * leftAt lensF codes 8 - (count lensF codes 9 : _root_.Int) := u 8
  have e9 : leftAt lensF codes 10
      = 2 * leftAt lensF codes 9 - (count lensF codes 10 : _root_.Int) := u 9
  have e10 : leftAt lensF codes 11
      = 2 * leftAt lensF codes 10 - (count lensF codes 11 : _root_.Int) := u 10
  have e11 : leftAt lensF codes 12
      = 2 * leftAt lensF codes 11 - (count lensF codes 12 : _root_.Int) := u 11
  have e12 : leftAt lensF codes 13
      = 2 * leftAt lensF codes 12 - (count lensF codes 13 : _root_.Int) := u 12
  have e13 : leftAt lensF codes 14
      = 2 * leftAt lensF codes 13 - (count lensF codes 14 : _root_.Int) := u 13
  have e14 : leftAt lensF codes 15
      = 2 * leftAt lensF codes 14 - (count lensF codes 15 : _root_.Int) := u 14
  omega

/-- Access #12, part 2: with exactly one length-1 symbol the main loop runs
    once, leaves `huff = bwInc 0 1 = 1`, `drop = 0`, `used = 2^root = 2`
    (root clamped to `max = 1`), so the fill write `next[1]` is the second and
    last entry of the two-entry table — in bounds. -/
theorem bwInc_zero_one : bwInc 0 1 = 1 := by
  decide

/-- A5 elimination (CODES): if every length is ≤ Lc and the requested root
    `b0 ≥ Lc`, then the clamped root equals `maxLen ≤ Lc`, hence no symbol is
    longer than the root table and the sub-table branch (inftrees.c:265) is
    unreachable.  Stated at the model level as: the clamp of `b0` into
    `[minLen, maxLen]` is `maxLen`. -/
theorem clamp_eq_max (lensF : Nat → Nat) (codes b0 Lc : Nat)
    (hLc : ∀ i, i < codes → lensF i ≤ Lc) (hb0 : Lc ≤ b0)
    (_hnz : maxLen lensF codes ≠ 0) :
    Nat.min b0 (maxLen lensF codes) = maxLen lensF codes := by
  have h1 : maxLen lensF codes ≤ Lc :=
    foldl_max_le lensF (List.range codes) 0 Lc (Nat.zero_le _)
      (fun x hx => hLc x (List.mem_range.mp hx))
  exact Nat.min_eq_right (by omega)

/-- Every length in the array is at most `maxLen` — the public form of
    `foldl_max_mem_le`.  `LoopEnv.hlensmax` needs it at the *normalised* `lens`,
    where it then holds for every index. -/
theorem le_maxLen (lensF : Nat → Nat) (codes i : Nat) (hi : i < codes) :
    lensF i ≤ maxLen lensF codes :=
  foldl_max_mem_le lensF (List.range codes) 0 i (List.mem_range.mpr hi)

/-- Every used length lies in `[minLen, maxLen]`; with A2 both ends are ≤ 15.
    Feeds every shift-amount obligation (`1U << root`, `1U << curr`,
    `1U << (len-1)`, `1U << (len-drop)` all < 2^15 < 2^31). -/
theorem lens_between (lensF : Nat → Nat) (codes i : Nat)
    (hi : i < codes) (hnz : lensF i ≠ 0) :
    minLen lensF codes ≤ lensF i ∧ lensF i ≤ maxLen lensF codes :=
  ⟨foldl_min_le_mem lensF (List.range codes) 16 i (List.mem_range.mpr hi) hnz,
   foldl_max_mem_le lensF (List.range codes) 0 i (List.mem_range.mpr hi)⟩

/-- `maxLen` is bounded by A2. -/
theorem maxLen_le (lensF : Nat → Nat) (codes : Nat)
    (hb : ∀ i, i < codes → lensF i ≤ 15) :
    maxLen lensF codes ≤ 15 :=
  foldl_max_le lensF (List.range codes) 0 15 (by omega)
    (fun x hx => hb x (List.mem_range.mp hx))

/-! ## The counting loop's invariant algebra (inftrees.c:118-119)

The loop's `count[]` array holds, after processing symbols `0..s-1`, exactly
`count lensF s` — these three lemmas are the step, the bound (which keeps every
cell below 2^16 given `codes < 2^16`), and the update-function identity the
`arrayU16_update` rewrite produces. -/

/-- Every count is bounded by the number of symbols processed. -/
theorem count_le (lensF : Nat → Nat) (codes l : Nat) :
    count lensF codes l ≤ codes := by
  have h := List.length_filter_le (fun i => decide (lensF i = l)) (List.range codes)
  simpa [count, List.length_range] using h

/-- Processing one more symbol bumps exactly its length's count. -/
theorem count_succ (lensF : Nat → Nat) (s l : Nat) :
    count lensF (s + 1) l
      = if lensF s = l then count lensF s l + 1 else count lensF s l := by
  unfold count
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : lensF s = l
  · simp [h]
  · simp [h]

/-- The shape `arrayU16_update` leaves equals the model at `s + 1`. -/
theorem count_update_fun (lensF : Nat → Nat) (s : Nat) :
    (fun j => if j = lensF s then count lensF s (lensF s) + 1
              else count lensF s j)
      = fun l => count lensF (s + 1) l := by
  funext j
  by_cases h : j = lensF s
  · subst h; simp [count_succ]
  · rw [if_neg h, count_succ, if_neg (fun hh => h hh.symm)]

/-! ## The max-scan's exit characterization (inftrees.c:123-124)

The scan leaves `max` = the largest length with a nonzero count (or 0).  This
identifies that exit value with the model's `maxLen`, which the incomplete-code
lemma (`incomplete_count_one`) and the CODES clamp (`clamp_eq_max`) speak
about. -/

/-- A positive count is witnessed by a symbol of that length. -/
theorem exists_of_count_pos (lensF : Nat → Nat) (codes l : Nat)
    (h : 0 < count lensF codes l) : ∃ i, i < codes ∧ lensF i = l := by
  unfold count at h
  obtain ⟨i, hi⟩ := List.exists_mem_of_length_pos h
  have hm := List.mem_filter.mp hi
  exact ⟨i, List.mem_range.mp hm.1, by simpa using hm.2⟩

/-- What the max scan establishes — `M ≤ 15`, counts above `M` all zero, and
    `M` itself zero or counted — pins `M = maxLen`. -/
theorem maxLen_char (lensF : Nat → Nat) (codes M : Nat)
    (hb : ∀ i, i < codes → lensF i ≤ 15) (hM : M ≤ 15)
    (hzero : ∀ l, M < l → l ≤ 15 → count lensF codes l = 0)
    (hnz : M = 0 ∨ count lensF codes M ≠ 0) :
    M = maxLen lensF codes := by
  have hmax15 := maxLen_le lensF codes hb
  rcases hnz with rfl | hnz
  · rcases Nat.eq_zero_or_pos (maxLen lensF codes) with h0 | h0
    · omega
    · obtain ⟨i, hi, he⟩ := exists_eq_maxLen lensF codes (by omega)
      have hc := count_pos lensF codes (maxLen lensF codes) i hi he
      have hz := hzero (maxLen lensF codes) (by omega) (by omega)
      omega
  · have hpos : 0 < count lensF codes M := Nat.pos_of_ne_zero hnz
    obtain ⟨i, hi, he⟩ := exists_of_count_pos lensF codes M hpos
    have hle : M ≤ maxLen lensF codes := by
      rw [← he]
      exact foldl_max_mem_le lensF (List.range codes) 0 i (List.mem_range.mpr hi)
    rcases Nat.lt_or_ge M (maxLen lensF codes) with hlt | hge
    · obtain ⟨j, hj, hej⟩ := exists_eq_maxLen lensF codes (by omega)
      have hcm := count_pos lensF codes (maxLen lensF codes) j hj hej
      have hz := hzero (maxLen lensF codes) hlt hmax15
      omega
    · omega

/-! ## The offsets loop and the sort loop (inftrees.c:150-156) -/

/-- No length is below zero. -/
theorem offs_zero (lensF : Nat → Nat) (codes : Nat) :
    offs lensF codes 0 = 0 := by
  unfold offs
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro i _
  simp only [decide_eq_true_eq]
  omega

/-- No nonzero length is below one. -/
theorem offs_one (lensF : Nat → Nat) (codes : Nat) :
    offs lensF codes 1 = 0 := by
  unfold offs
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro i _
  simp only [decide_eq_true_eq]
  omega

/-- Counting over a longer prefix counts at least as much. -/
theorem count_mono (lensF : Nat → Nat) (l : Nat) :
    ∀ {a b : Nat}, a ≤ b → count lensF a l ≤ count lensF b l := by
  intro a b hab
  induction b with
  | zero =>
      rw [show a = 0 from by omega]
      exact Nat.le_refl _
  | succ n ih =>
      rcases Nat.lt_or_ge a (n + 1) with h | h
      · have h1 := ih (by omega)
        rw [count_succ]
        split <;> omega
      · rw [show a = n + 1 from by omega]
        exact Nat.le_refl _


/-- The symbol at position `s` itself makes its length's full count strictly
    larger than the prefix count — the sort loop's write index is fresh. -/
theorem count_prefix_lt (lensF : Nat → Nat) (s codes l : Nat)
    (hs : s < codes) (hl : lensF s = l) :
    count lensF s l < count lensF codes l := by
  have h1 : count lensF (s + 1) l = count lensF s l + 1 := by
    rw [count_succ, if_pos hl]
  have h2 := count_mono lensF l (show s + 1 ≤ codes from by omega)
  omega

/-! ## Phase 4 — the main table-building loop (inftrees.c:221-295)

The loop fills the decoding table.  Its memory-safety obligations are:

  * every fill write `next[(huff >> drop) + fill]` lands inside the region
    already accounted for by `used`, which the runtime checks bound;
  * the root-table back-pointer write `(*table)[low]` lands in `[0, 2^root)`;
  * the shift amounts (`1U << (len - drop)`, `1U << curr`, `1U << (len-1)`)
    stay below 32.

The quantities below model the loop's state.  Note that NONE of this needs the
`ENOUGH` exhaustive-search bound: `used` is checked against the constants at
runtime (inftrees.c:216-218, 284-287) before each table is written. -/

/-- **The fill-loop's write offset is inside the current (sub)table.**

    The C loop runs `fill = 2^curr; do { fill -= incr; … } while (fill != 0);`
    with `incr = 2^(len-drop)`, so `fill = 2^curr - k·incr` for
    `k = 1, 2, …, 2^curr / incr`.  Since the code's dropped prefix
    `huff >> drop` is below `incr`, the offset stays below `2^curr`. -/
theorem fill_offset_lt (huff drop curr lenmdrop k : Nat)
    (hhuff : huff / 2 ^ drop < 2 ^ lenmdrop)
    (hk1 : 1 ≤ k) (hk2 : k * 2 ^ lenmdrop ≤ 2 ^ curr) :
    huff / 2 ^ drop + (2 ^ curr - k * 2 ^ lenmdrop) < 2 ^ curr := by
  have h1 : 2 ^ lenmdrop ≤ k * 2 ^ lenmdrop :=
    Nat.le_mul_of_pos_left _ hk1
  omega

/-- The root-table back-pointer index `huff & mask` is below `2^root`
    (`mask = 2^root - 1`). -/
theorem low_lt_pow (huff root : Nat) :
    huff % 2 ^ root < 2 ^ root :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- `used` after the root table and `k` sub-tables of sizes `cs`. -/
def usedAfter (root : Nat) (cs : List Nat) : Nat :=
  2 ^ root + (cs.map (fun c => 2 ^ c)).sum

theorem usedAfter_nil (root : Nat) : usedAfter root [] = 2 ^ root := by
  simp [usedAfter]

theorem usedAfter_cons (root c : Nat) (cs : List Nat) :
    usedAfter root (cs ++ [c]) = usedAfter root cs + 2 ^ c := by
  simp [usedAfter, List.map_append, List.sum_append]
  omega

/-- Monotonicity: `used` only grows, so a check that passed at the end
    bounds every earlier table's extent. -/
theorem usedAfter_le (root c : Nat) (cs : List Nat) :
    usedAfter root cs ≤ usedAfter root (cs ++ [c]) := by
  rw [usedAfter_cons]
  exact Nat.le_add_right _ _

/-! ## Phase 4b — the reversed-code mass model (I2)

The main loop's index-bound clauses (I2) and the fill loop's in-table bound
(`len - drop ≤ curr`) are re-established across an iteration by a *mass*
argument, not by prefix-freeness of the generated codes:

  * `massBelow g σ` is the Kraft mass (in units of `2^-15`, so an integer) of
    the symbols already consumed — `Σ_{i<σ} 2^(15 - g i)` where
    `g i = lens[work[i]]`.
  * `rev l h` is `h` bit-reversed at width `l`.  The loop invariant carries
    `massBelow g sym = rev len huff * 2^(15-len)`: the current code, read
    MSB-first, is exactly the mass consumed so far.  `bwInc_rev` shows one
    `huff = bwInc huff len` step advances the mass by exactly `2^(15-len)`.
  * The look-ahead loop's `left ≤ 0` exit says the remaining symbols with
    lengths in `[len, curr+root]` carry mass ≥ `2^(15-root)` (`wsum`, the
    loop's own weighted count sum).  Since codes are consumed in sorted order,
    by the time a longer code appears all of that mass is consumed
    (`wsum_mass`), so the root-prefix of the mass — hence of the code — has
    moved past `low`: a code that would overflow the sub-table cannot still
    be in it.  That is `subfit_from_look`, and it is the whole safety argument
    for the fill write. -/

/-- `h` bit-reversed at width `l` (bit `k` of `h` goes to position `l-1-k`;
    only the low `l` bits of `h` are read). -/
def rev : Nat → Nat → Nat
  | 0, _ => 0
  | l + 1, h => h % 2 * 2 ^ l + rev l (h / 2)

theorem rev_lt (l : Nat) : ∀ h, rev l h < 2 ^ l := by
  induction l with
  | zero => intro h; simp [rev]
  | succ n ih =>
      intro h
      have h1 : h % 2 ≤ 1 := by omega
      have h2 : rev n (h / 2) < 2 ^ n := ih (h / 2)
      have h3 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
      simp only [rev]
      have h4 : h % 2 * 2 ^ n ≤ 2 ^ n := by
        calc h % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ h1
        _ = 2 ^ n := Nat.one_mul _
      omega

/-- `rev` reads only the low `l` bits. -/
theorem rev_mod (l : Nat) : ∀ h, rev l (h % 2 ^ l) = rev l h := by
  induction l with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      have hm : h % 2 ^ (n + 1) % 2 = h % 2 := by
        rw [Nat.mod_mod_of_dvd _ ⟨2 ^ n, by rw [Nat.pow_succ]; omega⟩]
      have hd : h % 2 ^ (n + 1) / 2 = h / 2 % 2 ^ n := by
        rw [show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n from by rw [Nat.pow_succ]; omega]
        exact Nat.mod_mul_right_div_self h 2 (2 ^ n)
      simp only [rev, hm, hd, ih (h / 2)]

/-- Peel the *top* position instead of the bottom bit. -/
theorem rev_succ_top (l : Nat) : ∀ h, rev (l + 1) h = 2 * rev l h + h / 2 ^ l % 2 := by
  induction l with
  | zero => intro h; simp [rev]
  | succ n ih =>
      intro h
      show h % 2 * 2 ^ (n + 1) + rev (n + 1) (h / 2)
            = 2 * (h % 2 * 2 ^ n + rev n (h / 2)) + h / 2 ^ (n + 1) % 2
      rw [ih (h / 2), show h / 2 / 2 ^ n = h / 2 ^ (n + 1) from by
            rw [Nat.div_div_eq_div_mul]
            congr 1
            rw [Nat.pow_succ]
            omega]
      have : h % 2 * 2 ^ (n + 1) = 2 * (h % 2 * 2 ^ n) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm 2 (h % 2 * 2 ^ n)]
      omega

/-- Widening the field: a value below `2 ^ l` reversed at width `l + d` is the
    width-`l` reversal shifted up. -/
theorem rev_shift (l d : Nat) (h : Nat) (hh : h < 2 ^ l) :
    rev (l + d) h = rev l h * 2 ^ d := by
  induction d with
  | zero => simp
  | succ k ih =>
      have hz : h / 2 ^ (l + k) = 0 :=
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hh (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [show l + (k + 1) = (l + k) + 1 from rfl, rev_succ_top, ih, hz]
      rw [Nat.zero_mod, Nat.add_zero, Nat.pow_succ, ← Nat.mul_assoc,
          Nat.mul_comm 2 (rev l h), Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k)]

/-- The top `r` positions of a width-`l` reversal are the width-`r` reversal
    (of the low `r` bits). -/
theorem rev_div_prefix (r : Nat) : ∀ l h, r ≤ l → rev l h / 2 ^ (l - r) = rev r h := by
  induction r with
  | zero =>
      intro l h _
      exact Nat.div_eq_of_lt (by simpa using rev_lt l h)
  | succ n ih =>
      intro l h hrl
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hnl : n ≤ l' := by omega
      have hsplit : (2 : Nat) ^ l' = 2 ^ (l' - n) * 2 ^ n := by
        rw [← Nat.pow_add]; congr 1; omega
      show (h % 2 * 2 ^ l' + rev l' (h / 2)) / 2 ^ (l' + 1 - (n + 1)) = rev (n + 1) h
      rw [show l' + 1 - (n + 1) = l' - n from by omega, hsplit, ← Nat.mul_assoc,
          Nat.mul_comm (h % 2) (2 ^ (l' - n)), Nat.mul_assoc,
          Nat.mul_add_div (Nat.two_pow_pos (l' - n)), ih l' (h / 2) hnl]
      rfl

/-- **The backwards increment is `+1` on the reversed code** (with wrap-around
    to `0` when the code was all-ones).  No hypothesis: both sides read only
    the low `l` bits. -/
theorem bwIncGo_rev (l : Nat) : ∀ h, rev l (bwIncGo h l) = (rev l h + 1) % 2 ^ l := by
  induction l with
  | zero => intro h; simp [rev]
  | succ n ih =>
      intro h
      show rev (n + 1) (if h / 2 ^ n % 2 = 1 then bwIncGo h n else h % 2 ^ n + 2 ^ n)
            = (rev (n + 1) h + 1) % 2 ^ (n + 1)
      rw [rev_succ_top n h]
      by_cases hbit : h / 2 ^ n % 2 = 1
      · rw [if_pos hbit, hbit,
            show rev (n + 1) (bwIncGo h n) = rev n (bwIncGo h n) * 2 from by
              rw [rev_shift n 1 (bwIncGo h n) (bwIncGo_lt h n), Nat.pow_one],
            ih h,
            show 2 * rev n h + 1 + 1 = 2 * (rev n h + 1) from by omega,
            show (2 : Nat) ^ (n + 1) = 2 * 2 ^ n from by rw [Nat.pow_succ]; omega,
            Nat.mul_mod_mul_left]
        omega
      · have hbit0 : h / 2 ^ n % 2 = 0 := by omega
        rw [if_neg hbit, hbit0, rev_succ_top n (h % 2 ^ n + 2 ^ n),
            show (h % 2 ^ n + 2 ^ n) / 2 ^ n = 1 from by
              rw [Nat.add_div_right _ (Nat.two_pow_pos n),
                  Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos n))],
            show rev n (h % 2 ^ n + 2 ^ n) = rev n h from by
              rw [← rev_mod n (h % 2 ^ n + 2 ^ n), Nat.add_mod_right,
                  Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), rev_mod]]
        have h1 := rev_lt n h
        have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
        have hlt : 2 * rev n h + 0 + 1 < 2 ^ (n + 1) := by omega
        rw [Nat.mod_eq_of_lt hlt]

theorem bwInc_rev (h l : Nat) : rev l (bwInc h l) = (rev l h + 1) % 2 ^ l :=
  bwIncGo_rev l h

theorem rev_congr_mod (r h h' : Nat) (hm : h % 2 ^ r = h' % 2 ^ r) :
    rev r h = rev r h' := by
  rw [← rev_mod r h, hm, rev_mod]

/-- `x < (x/d + 1) * d`. -/
theorem lt_div_succ_mul (x d : Nat) (hd : 0 < d) : x < (x / d + 1) * d := by
  have h1 := Nat.div_add_mod x d
  have h2 := Nat.mod_lt x hd
  rw [Nat.succ_mul, Nat.mul_comm (x / d) d]
  omega

/-- A width-`l` reversed code, placed on the 15-bit mass line, sits inside the
    slot of its width-`r` prefix: `[P·2^(15-r), (P+1)·2^(15-r))` where
    `P = rev r h`.  Both halves of the sub-table-fit argument are this. -/
theorem rev_prefix_bounds (l r h : Nat) (hrl : r ≤ l) (hl15 : l ≤ 15) :
    rev r h * 2 ^ (15 - r) ≤ rev l h * 2 ^ (15 - l)
    ∧ rev l h * 2 ^ (15 - l) < (rev r h + 1) * 2 ^ (15 - r) := by
  have hd : (0 : Nat) < 2 ^ (l - r) := Nat.two_pow_pos _
  have hq : rev l h / 2 ^ (l - r) = rev r h := rev_div_prefix r l h hrl
  have hlow : rev r h * 2 ^ (l - r) ≤ rev l h := by
    rw [← hq]; exact Nat.div_mul_le_self _ _
  have hhigh : rev l h < (rev r h + 1) * 2 ^ (l - r) := by
    rw [← hq]; exact lt_div_succ_mul _ _ hd
  have hpow : 2 ^ (l - r) * 2 ^ (15 - l) = 2 ^ (15 - r) := by
    rw [← Nat.pow_add]; congr 1; omega
  constructor
  · calc rev r h * 2 ^ (15 - r)
        = rev r h * 2 ^ (l - r) * 2 ^ (15 - l) := by
          rw [Nat.mul_assoc, hpow]
      _ ≤ rev l h * 2 ^ (15 - l) := Nat.mul_le_mul_right _ hlow
  · calc rev l h * 2 ^ (15 - l)
        < (rev r h + 1) * 2 ^ (l - r) * 2 ^ (15 - l) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhigh
      _ = (rev r h + 1) * 2 ^ (15 - r) := by rw [Nat.mul_assoc, hpow]

/-! ### Interval counts and the consumed mass -/

/-- The number of indices `i ∈ [σ, N)` with `g i = j`: the remaining `count[j]`
    when the main loop has consumed `work[0..σ)`. -/
def cntSeg (g : Nat → Nat) (σ N j : Nat) : Nat :=
  ((List.range (N - σ)).filter (fun k => g (σ + k) = j)).length

/-- Consuming one symbol decrements exactly its own length's count. -/
theorem cntSeg_succ (g : Nat → Nat) (σ N j : Nat) (hσ : σ < N) :
    cntSeg g σ N j = (if g σ = j then 1 else 0) + cntSeg g (σ + 1) N j := by
  unfold cntSeg
  rw [show N - σ = (N - (σ + 1)) + 1 from by omega, List.range_succ_eq_map,
      List.filter_cons]
  have hmap : (List.map Nat.succ (List.range (N - (σ + 1)))).filter
        (fun k => decide (g (σ + k) = j))
      = List.map Nat.succ ((List.range (N - (σ + 1))).filter
        (fun k => decide (g (σ + 1 + k) = j))) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro k _
    show decide (g (σ + Nat.succ k) = j) = decide (g (σ + 1 + k) = j)
    rw [show σ + Nat.succ k = σ + 1 + k from by omega]
  simp only [Nat.add_zero]
  by_cases hg : g σ = j
  · rw [if_pos (by simpa using hg)]
    simp only [List.length_cons, hmap, List.length_map]
    rw [if_pos hg]
    omega
  · rw [if_neg (by simpa using hg)]
    simp only [hmap, List.length_map]
    rw [if_neg hg]
    omega

/-- A witness makes the count positive. -/
theorem cntSeg_pos (g : Nat → Nat) (σ N j i : Nat)
    (h1 : σ ≤ i) (h2 : i < N) (h3 : g i = j) : 1 ≤ cntSeg g σ N j := by
  unfold cntSeg
  refine List.length_pos_of_mem (a := i - σ) (List.mem_filter.mpr ⟨?_, ?_⟩)
  · exact List.mem_range.mpr (by omega)
  · simp only [decide_eq_true_eq]
    rw [show σ + (i - σ) = i from by omega]
    exact h3

/-- A positive count yields a witness. -/
theorem cntSeg_exists (g : Nat → Nat) (σ N j : Nat)
    (h : 1 ≤ cntSeg g σ N j) : ∃ i, σ ≤ i ∧ i < N ∧ g i = j := by
  unfold cntSeg at h
  obtain ⟨k, hk⟩ := List.exists_mem_of_length_pos h
  obtain ⟨hkr, hkg⟩ := List.mem_filter.mp hk
  refine ⟨σ + k, by omega, ?_, by simpa using hkg⟩
  have := List.mem_range.mp hkr
  omega

/-- The count vanishes when nothing in the interval has that length. -/
theorem cntSeg_eq_zero (g : Nat → Nat) (σ N j : Nat)
    (h : ∀ i, σ ≤ i → i < N → g i ≠ j) : cntSeg g σ N j = 0 := by
  unfold cntSeg
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro k hk
  simp only [decide_eq_true_eq]
  exact h (σ + k) (by omega) (by have := List.mem_range.mp hk; omega)

/-- In sorted order, if another symbol of the current length remains, the very
    next symbol has that length (and exists). -/
theorem sorted_stable (g : Nat → Nat) (σ N : Nat)
    (hsort : ∀ i j, i ≤ j → j < N → g i ≤ g j) (hσ : σ < N)
    (h1 : 1 ≤ cntSeg g (σ + 1) N (g σ)) : σ + 1 < N ∧ g (σ + 1) = g σ := by
  obtain ⟨i, hi1, hi2, hi3⟩ := cntSeg_exists g (σ + 1) N (g σ) h1
  have hN : σ + 1 < N := by omega
  have h4 : g (σ + 1) ≤ g i := hsort _ _ hi1 hi2
  have h5 : g σ ≤ g (σ + 1) := hsort _ _ (by omega) hN
  exact ⟨hN, by omega⟩

/-- The Kraft mass (in units of `2^-15`) of the first `σ` symbols. -/
def massBelow (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | σ + 1 => massBelow g σ + 2 ^ (15 - g σ)

theorem massBelow_le (g : Nat → Nat) (σ τ : Nat) (h : σ ≤ τ) :
    massBelow g σ ≤ massBelow g τ := by
  induction τ with
  | zero => rw [show σ = 0 from by omega]; exact Nat.le_refl _
  | succ t ih =>
      by_cases hσ : σ = t + 1
      · rw [hσ]; exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- **One `huff = bwInc huff len` step advances the mass by exactly
    `2^(15-len)`** — provided the total mass has room, which excludes the
    all-ones wrap. -/
theorem massBelow_step_rev (g : Nat → Nat) (σ len len' h : Nat)
    (hlen : g σ = len) (hle : len ≤ len') (hl15 : len' ≤ 15)
    (hJ : massBelow g σ = rev len h * 2 ^ (15 - len))
    (hcap : massBelow g (σ + 1) < 2 ^ 15) :
    massBelow g (σ + 1) = rev len' (bwInc h len) * 2 ^ (15 - len') := by
  have hm1 : massBelow g (σ + 1) = (rev len h + 1) * 2 ^ (15 - len) := by
    show massBelow g σ + 2 ^ (15 - g σ) = _
    rw [hJ, hlen, Nat.succ_mul]
  have hrl : rev len h < 2 ^ len := rev_lt len h
  have hnw : rev len h + 1 < 2 ^ len := by
    rcases Nat.lt_or_ge (rev len h + 1) (2 ^ len) with hlt | hge
    · exact hlt
    · exfalso
      have heq : rev len h + 1 = 2 ^ len := by omega
      rw [hm1, heq, ← Nat.pow_add,
          show len + (15 - len) = 15 from by omega] at hcap
      omega
  have hbw : rev len (bwInc h len) = rev len h + 1 := by
    rw [bwInc_rev, Nat.mod_eq_of_lt hnw]
  have hsh : rev len' (bwInc h len)
      = rev len (bwInc h len) * 2 ^ (len' - len) := by
    have h0 := rev_shift len (len' - len) (bwInc h len) (bwIncGo_lt h len)
    rwa [show len + (len' - len) = len' from by omega] at h0
  rw [hsh, hbw, Nat.mul_assoc, ← Nat.pow_add,
      show len' - len + (15 - len') = 15 - len from by omega, hm1]

/-! ### The look-ahead loop's weighted count sum

`wsum cnt lo w = Σ_{k ≤ w} cnt (lo+k) · 2^(w-k)` is what the C look-ahead loop
subtracts from `2^curr`; `hsum` is the partial sum at the loop *head* (before
the current width's count is subtracted).  Both are defined by the loop's own
recurrence so the heap-level proof unfolds them definitionally. -/

def wsum (cnt : Nat → Nat) (lo : Nat) : Nat → Nat
  | 0 => cnt lo
  | w + 1 => 2 * wsum cnt lo w + cnt (lo + (w + 1))

def hsum (cnt : Nat → Nat) (lo : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => 2 * wsum cnt lo w

theorem wsum_hsum (cnt : Nat → Nat) (lo w : Nat) :
    wsum cnt lo w = hsum cnt lo w + cnt (lo + w) := by
  cases w with
  | zero => simp [wsum, hsum]
  | succ v => simp [wsum, hsum]

theorem wsum_congr (cnt₁ cnt₂ : Nat → Nat) (lo : Nat) :
    ∀ w, (∀ k, k ≤ w → cnt₁ (lo + k) = cnt₂ (lo + k)) →
      wsum cnt₁ lo w = wsum cnt₂ lo w := by
  intro w
  induction w with
  | zero =>
      intro h
      have := h 0 (by omega)
      simpa [wsum] using this
  | succ v ih =>
      intro h
      simp only [wsum]
      rw [ih (fun k hk => h k (by omega)), h (v + 1) (by omega)]

theorem wsum_add (a b : Nat → Nat) (lo : Nat) :
    ∀ w, wsum (fun j => a j + b j) lo w = wsum a lo w + wsum b lo w := by
  intro w
  induction w with
  | zero => simp [wsum]
  | succ v ih => simp only [wsum]; omega

theorem wsum_zero (lo : Nat) : ∀ w, wsum (fun _ => 0) lo w = 0 := by
  intro w
  induction w with
  | zero => rfl
  | succ v ih => simp only [wsum]; omega

/-- The weighted sum of a point mass. -/
theorem wsum_indicator (v lo : Nat) :
    ∀ w, wsum (fun j => if v = j then 1 else 0) lo w
      = if lo ≤ v ∧ v ≤ lo + w then 2 ^ (lo + w - v) else 0 := by
  intro w
  induction w with
  | zero =>
      by_cases hv : v = lo
      · subst hv; simp [wsum]
      · rw [show wsum (fun j => if v = j then 1 else 0) lo 0
              = (if v = lo then 1 else 0) from rfl, if_neg hv,
            if_neg (by omega)]
  | succ u ih =>
      simp only [wsum, ih]
      by_cases h1 : v = lo + (u + 1)
      · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]
        rw [show lo + (u + 1) - v = 0 from by omega]
      · rw [if_neg h1]
        by_cases h2 : lo ≤ v ∧ v ≤ lo + u
        · rw [if_pos h2, if_pos (by omega)]
          rw [show lo + (u + 1) - v = (lo + u - v) + 1 from by omega,
              Nat.pow_succ]
          omega
        · rw [if_neg h2, if_neg (by omega)]

/-- Consuming one symbol removes its weight from the look sum. -/
theorem wsum_cntSeg_succ (g : Nat → Nat) (σ N lo w : Nat) (hσ : σ < N) :
    wsum (cntSeg g σ N) lo w
      = wsum (cntSeg g (σ + 1) N) lo w
        + (if lo ≤ g σ ∧ g σ ≤ lo + w then 2 ^ (lo + w - g σ) else 0) := by
  rw [wsum_congr (cntSeg g σ N)
        (fun j => (if g σ = j then 1 else 0) + cntSeg g (σ + 1) N j) lo w
        (fun k _ => cntSeg_succ g σ N (lo + k) hσ),
      wsum_add, wsum_indicator]
  omega

/-- Nothing left at or below `lo + w` ⟹ the look sum is zero. -/
theorem wsum_cntSeg_zero (g : Nat → Nat) (σ N lo w : Nat)
    (h : ∀ k, σ ≤ k → k < N → lo + w < g k) :
    wsum (cntSeg g σ N) lo w = 0 := by
  rw [wsum_congr (cntSeg g σ N) (fun _ => 0) lo w
        (fun k hk => cntSeg_eq_zero g σ N (lo + k)
          (fun i hi1 hi2 => by have := h i hi1 hi2; omega)),
      wsum_zero]

/-- **The mass argument.**  If every symbol from `i` on is longer than
    `lo + w`, then by index `i` the whole look sum's mass has been consumed. -/
theorem wsum_mass (g : Nat → Nat) (N lo w : Nat) (hlow : lo + w ≤ 15) :
    ∀ d σ i, i - σ ≤ d → σ ≤ i → i < N →
      (∀ k, i ≤ k → k < N → lo + w < g k) →
      massBelow g σ + wsum (cntSeg g σ N) lo w * 2 ^ (15 - (lo + w))
        ≤ massBelow g i := by
  intro d
  induction d with
  | zero =>
      intro σ i hd hσi hiN hk
      rw [show σ = i from by omega, wsum_cntSeg_zero g i N lo w hk]
      omega
  | succ d ih =>
      intro σ i hd hσi hiN hk
      by_cases hσi' : σ = i
      · rw [hσi', wsum_cntSeg_zero g i N lo w hk]
        omega
      · have hσN : σ < N := by omega
        have hih := ih (σ + 1) i (by omega) (by omega) hiN hk
        rw [wsum_cntSeg_succ g σ N lo w hσN, Nat.add_mul]
        by_cases hgσ : lo ≤ g σ ∧ g σ ≤ lo + w
        · rw [if_pos hgσ, ← Nat.pow_add,
              show lo + w - g σ + (15 - (lo + w)) = 15 - g σ from by omega]
          have hms : massBelow g (σ + 1) = massBelow g σ + 2 ^ (15 - g σ) := rfl
          omega
        · rw [if_neg hgσ]
          have hms : massBelow g (σ + 1) = massBelow g σ + 2 ^ (15 - g σ) := rfl
          have hpos : 0 < 2 ^ (15 - g σ) := Nat.two_pow_pos _
          omega

/-- **The sub-table-fit clause, established from the look-ahead loop's exit.**

    At sub-table creation (current symbol `σ`, length `len = g σ > root`), the
    look loop exited with `2^C ≤ wsum (remaining counts) len (C - (len-root))`
    — the C's `left ≤ 0`.  Then any later symbol longer than `C + root` can
    only appear after mass `2^(15-root)` — one full root-prefix — has been
    consumed past `massBelow σ`. -/
theorem subfit_from_look (g : Nat → Nat) (N σ root C len : Nat)
    (hsort : ∀ i j, i ≤ j → j < N → g i ≤ g j)
    (hlen : g σ = len) (hrl : root < len) (hlC : len - root ≤ C)
    (hC15 : C + root ≤ 15)
    (hsum : 2 ^ C ≤ wsum (cntSeg g σ N) len (C - (len - root))) :
    ∀ i, σ ≤ i → i < N → C + root < g i →
      massBelow g σ + 2 ^ (15 - root) ≤ massBelow g i := by
  intro i hσi hiN hgi
  have hlw : len + (C - (len - root)) = C + root := by omega
  have hmass := wsum_mass g N len (C - (len - root)) (by omega) (i - σ) σ i
    (by omega) hσi hiN
    (fun k hk1 hk2 => by
      have := hsort i k hk1 hk2
      omega)
  have hle : 2 ^ C * 2 ^ (15 - (len + (C - (len - root))))
      ≤ wsum (cntSeg g σ N) len (C - (len - root))
        * 2 ^ (15 - (len + (C - (len - root)))) :=
    Nat.mul_le_mul_right _ hsum
  rw [← Nat.pow_add, hlw, show C + (15 - (C + root)) = 15 - root from by omega]
    at hle
  rw [hlw] at hmass
  omega

/-! ## Phase 5 — what the sort loop's output looks like

`WorkChar` (InflateTableBody §26) is everything the main loop assumes about
`work[]`.  The sort loop's own proof records only **where** it wrote:
`work[posOf t] = t` for every live symbol `t`, with

    posOf t = offs[lens t] + (number of earlier symbols of the same length)

— the C's `work[offs[lens[sym]]++]`.  Everything else is recovered here from
the placement map alone.  Three steps:

* `posOf t` lands in `[offs l, offs (l+1))`, the block of its own length
  (`posOf_block`);
* **every** position below `nlive` is hit (`posOf_surj`).  Proved by
  *constructing* the `k`-th symbol of a given length (`exists_nth_of_count`),
  not by a pigeonhole argument — which would need cardinality machinery this
  file deliberately avoids;
* hence position `i` carries length `l` exactly when `offs l ≤ i < offs (l+1)`
  (`place_len`, `place_len_unique`), so the position-indexed Kraft mass
  regroups into a `count`-indexed sum (`massBelow_eq_massSum`) and the
  over-subscription check bounds it (`massSum_count_le`). -/

/-- An interval count over `List.range`, from the two-sided filter algebra. -/
private theorem length_filter_ge (a : Nat) : ∀ N,
    ((List.range N).filter (fun k => decide (a ≤ k))).length = N - a := by
  intro N
  induction N with
  | zero => simp
  | succ M ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih]
      by_cases h : a ≤ M
      · rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega),
            List.filter_nil]
        simp only [List.length_cons, List.length_nil]
        omega
      · rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; omega),
            List.filter_nil]
        simp only [List.length_nil]
        omega

private theorem length_filter_interval (a b N : Nat) (hab : a ≤ b)
    (hbN : b ≤ N) :
    ((List.range N).filter (fun k => decide (a ≤ k ∧ k < b))).length
      = b - a := by
  have hsplit := length_filter_or (fun k => decide (a ≤ k))
    (fun k => decide (a ≤ k ∧ k < b)) (fun k => decide (b ≤ k)) (List.range N)
    (fun k _ => by
      rw [← Bool.decide_or, decide_eq_decide]
      constructor
      · intro h; rcases Nat.lt_or_ge k b with hk | hk
        · exact Or.inl ⟨h, hk⟩
        · exact Or.inr hk
      · intro h; rcases h with h | h
        · exact h.1
        · omega)
    (fun k _ => by
      simp only [decide_eq_true_eq]
      intro h
      omega)
  rw [length_filter_ge a N, length_filter_ge b N] at hsplit
  omega

/-- `cntSeg` based at 0 is a plain `List.range` filter. -/
theorem cntSeg_zero_eq (g : Nat → Nat) (N j : Nat) :
    cntSeg g 0 N j = ((List.range N).filter (fun k => g k = j)).length := by
  unfold cntSeg
  rw [Nat.sub_zero]
  congr 1
  apply List.filter_congr
  intro k _
  show decide (g (0 + k) = j) = decide (g k = j)
  rw [Nat.zero_add]

/-- Peel the *last* position (`cntSeg_succ` peels the first). -/
theorem cntSeg_snoc (g : Nat → Nat) (N j : Nat) :
    cntSeg g 0 (N + 1) j
      = cntSeg g 0 N j + (if g N = j then 1 else 0) := by
  rw [cntSeg_zero_eq, cntSeg_zero_eq, List.range_succ, List.filter_append,
      List.length_append]
  by_cases h : g N = j
  · rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact h),
        List.filter_nil, if_pos h]
    simp
  · rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact h),
        List.filter_nil, if_neg h]
    simp

/-- The Kraft mass of a length distribution, in units of `2^-15`.  Written out
    at the fifteen legal lengths so every coefficient is a numeral and `omega`
    can do the arithmetic. -/
def massSum (c : Nat → Nat) : Nat :=
  c 1 * 16384 + c 2 * 8192 + c 3 * 4096 + c 4 * 2048 + c 5 * 1024
  + c 6 * 512 + c 7 * 256 + c 8 * 128 + c 9 * 64 + c 10 * 32
  + c 11 * 16 + c 12 * 8 + c 13 * 4 + c 14 * 2 + c 15

theorem massSum_congr (c c' : Nat → Nat)
    (h : ∀ l, 1 ≤ l → l ≤ 15 → c l = c' l) : massSum c = massSum c' := by
  unfold massSum
  rw [h 1 (by omega) (by omega), h 2 (by omega) (by omega),
      h 3 (by omega) (by omega), h 4 (by omega) (by omega),
      h 5 (by omega) (by omega), h 6 (by omega) (by omega),
      h 7 (by omega) (by omega), h 8 (by omega) (by omega),
      h 9 (by omega) (by omega), h 10 (by omega) (by omega),
      h 11 (by omega) (by omega), h 12 (by omega) (by omega),
      h 13 (by omega) (by omega), h 14 (by omega) (by omega),
      h 15 (by omega) (by omega)]

/-- **Regrouping the mass by length.**  The main loop's mass is indexed by
    *position*; Kraft is indexed by *length*.  This is the bridge. -/
theorem massBelow_eq_massSum (g : Nat → Nat) : ∀ N,
    (∀ i, i < N → 1 ≤ g i ∧ g i ≤ 15) →
      massBelow g N = massSum (cntSeg g 0 N) := by
  intro N
  induction N with
  | zero =>
      intro _
      have hz : ∀ l, cntSeg g 0 0 l = 0 := by
        intro l; rw [cntSeg_zero_eq]; rfl
      show (0 : Nat) = massSum (cntSeg g 0 0)
      unfold massSum
      rw [hz 1, hz 2, hz 3, hz 4, hz 5, hz 6, hz 7, hz 8, hz 9, hz 10, hz 11,
          hz 12, hz 13, hz 14, hz 15]
  | succ M ih =>
      intro hb
      obtain ⟨hg1, hg2⟩ := hb M (by omega)
      have hrec : massBelow g (M + 1) = massBelow g M + 2 ^ (15 - g M) := rfl
      rw [hrec, ih (fun i hi => hb i (by omega))]
      unfold massSum
      simp only [cntSeg_snoc]
      have hcase : g M = 1 ∨ g M = 2 ∨ g M = 3 ∨ g M = 4 ∨ g M = 5 ∨ g M = 6
          ∨ g M = 7 ∨ g M = 8 ∨ g M = 9 ∨ g M = 10 ∨ g M = 11 ∨ g M = 12
          ∨ g M = 13 ∨ g M = 14 ∨ g M = 15 := by omega
      rcases hcase with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
        rw [h] <;> simp <;> omega

/-- Where the sort loop writes symbol `t` (inftrees.c:156). -/
def posOf (lensF : Nat → Nat) (codes t : Nat) : Nat :=
  offs lensF codes (lensF t) + count lensF t (lensF t)

theorem offs_mono (lensF : Nat → Nat) (codes : Nat) {a b : Nat} (h : a ≤ b) :
    offs lensF codes a ≤ offs lensF codes b := by
  unfold offs
  refine length_filter_mono _ _ (List.range codes) (fun i _ hi => ?_)
  simp only [decide_eq_true_eq] at hi ⊢
  omega

/-- With every length ≤ 15, the offset table's top entry is the live count. -/
theorem offs_16_eq_nlive (lensF : Nat → Nat) (codes : Nat)
    (hb : ∀ i, i < codes → lensF i ≤ 15) :
    offs lensF codes 16 = nlive lensF codes := by
  unfold offs nlive
  congr 1
  apply List.filter_congr
  intro i hi
  have := hb i (List.mem_range.mp hi)
  show decide (0 < lensF i ∧ lensF i < 16) = decide (lensF i ≠ 0)
  rw [decide_eq_decide]
  constructor
  · intro h; omega
  · intro h; omega

/-- A symbol is written inside its own length's block. -/
theorem posOf_block (lensF : Nat → Nat) (codes t : Nat)
    (ht : t < codes) (hlt : lensF t ≠ 0) :
    offs lensF codes (lensF t) ≤ posOf lensF codes t
    ∧ posOf lensF codes t < offs lensF codes (lensF t + 1) := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  have h1 := offs_succ lensF codes (lensF t) (by omega)
  have h2 := count_prefix_lt lensF t codes (lensF t) ht rfl
  unfold posOf
  omega

/-- The `k`-th symbol of a given length exists whenever the count exceeds
    `k` — the constructive replacement for a pigeonhole argument. -/
theorem exists_nth_of_count (lensF : Nat → Nat) (l : Nat) : ∀ codes k,
    k < count lensF codes l →
      ∃ t, t < codes ∧ lensF t = l ∧ count lensF t l = k := by
  intro codes
  induction codes with
  | zero =>
      intro k hk
      rw [show count lensF 0 l = 0 from rfl] at hk
      omega
  | succ c ih =>
      intro k hk
      rw [count_succ] at hk
      by_cases hc : lensF c = l
      · rw [if_pos hc] at hk
        rcases Nat.lt_or_ge k (count lensF c l) with h | h
        · obtain ⟨t, ht1, ht2, ht3⟩ := ih k h
          exact ⟨t, by omega, ht2, ht3⟩
        · exact ⟨c, by omega, hc, by omega⟩
      · rw [if_neg hc] at hk
        obtain ⟨t, ht1, ht2, ht3⟩ := ih k hk
        exact ⟨t, by omega, ht2, ht3⟩

/-- Find the step of a monotone staircase that straddles a value. -/
private theorem exists_step (f : Nat → Nat)
    (hmono : ∀ x y, x ≤ y → f x ≤ f y) (a i : Nat) : ∀ b,
    a ≤ b → f a ≤ i → i < f b →
      ∃ l, a ≤ l ∧ l < b ∧ f l ≤ i ∧ i < f (l + 1) := by
  intro b
  induction b with
  | zero =>
      intro hab h1 h2
      rw [show a = 0 from by omega] at h1
      omega
  | succ m ih =>
      intro hab h1 h2
      have ham : a ≤ m := by
        rcases Nat.lt_or_ge a (m + 1) with hh | hh
        · omega
        · exfalso
          have := hmono (m + 1) a (by omega)
          omega
      rcases Nat.lt_or_ge i (f m) with h | h
      · obtain ⟨l, hl1, hl2, hl3, hl4⟩ := ih ham h1 h
        exact ⟨l, hl1, by omega, hl3, hl4⟩
      · exact ⟨m, ham, by omega, h, h2⟩

/-- **Every position below `nlive` is written.**  This is what lets the main
    loop treat `work[i]` as a real symbol for every `i` it will read. -/
theorem posOf_surj (lensF : Nat → Nat) (codes i : Nat)
    (hb : ∀ j, j < codes → lensF j ≤ 15) (hi : i < nlive lensF codes) :
    ∃ t, t < codes ∧ lensF t ≠ 0 ∧ posOf lensF codes t = i := by
  have h1 : offs lensF codes 1 ≤ i := by rw [offs_one]; omega
  have h2 : i < offs lensF codes 16 := by
    rw [offs_16_eq_nlive lensF codes hb]; exact hi
  obtain ⟨l, hl1, hl2, hl3, hl4⟩ :=
    exists_step (offs lensF codes) (fun x y h => offs_mono lensF codes h) 1 i
      16 (by omega) h1 h2
  have hs := offs_succ lensF codes l (by omega)
  have hk : i - offs lensF codes l < count lensF codes l := by omega
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_nth_of_count lensF l codes _ hk
  refine ⟨t, ht1, by omega, ?_⟩
  unfold posOf
  rw [ht2, ht3]
  omega

/-- Blocks do not overlap, so a position determines its length. -/
theorem place_len_unique (lensF : Nat → Nat) (codes i l l' : Nat)
    (h1 : offs lensF codes l ≤ i) (h2 : i < offs lensF codes (l + 1))
    (h3 : offs lensF codes l' ≤ i) (h4 : i < offs lensF codes (l' + 1)) :
    l = l' := by
  rcases Nat.lt_trichotomy l l' with h | h | h
  · have := offs_mono lensF codes (show l + 1 ≤ l' from by omega); omega
  · exact h
  · have := offs_mono lensF codes (show l' + 1 ≤ l from by omega); omega

/-- **Distinct live symbols get distinct slots.**  Needed by the sort loop
    itself: placing symbol `s` must not clobber an earlier symbol's slot.
    Same length ⇒ different prefix counts; different lengths ⇒ different
    blocks. -/
theorem posOf_ne (lensF : Nat → Nat) (codes t s : Nat)
    (hts : t < s) (hs : s < codes) (ht : lensF t ≠ 0) (hsz : lensF s ≠ 0) :
    posOf lensF codes t ≠ posOf lensF codes s := by
  have htc : t < codes := by omega
  by_cases hl : lensF t = lensF s
  · have h1 : count lensF t (lensF t) < count lensF s (lensF t) :=
      count_prefix_lt lensF t s (lensF t) hts rfl
    unfold posOf
    rw [hl] at h1 ⊢
    omega
  · intro heq
    obtain ⟨ha1, ha2⟩ := posOf_block lensF codes t htc ht
    obtain ⟨hb1, hb2⟩ := posOf_block lensF codes s hs hsz
    rw [heq] at ha1 ha2
    exact hl (place_len_unique lensF codes (posOf lensF codes s)
      (lensF t) (lensF s) ha1 ha2 hb1 hb2)

/-- **What position `i` of `work[]` holds**, given only the placement map. -/
theorem place_len (lensF workF : Nat → Nat) (codes i : Nat)
    (hb : ∀ j, j < codes → lensF j ≤ 15)
    (hplaced : ∀ t, t < codes → lensF t ≠ 0 → workF (posOf lensF codes t) = t)
    (hi : i < nlive lensF codes) :
    ∃ l, 1 ≤ l ∧ l ≤ 15 ∧ offs lensF codes l ≤ i
      ∧ i < offs lensF codes (l + 1) ∧ lensF (workF i) = l
      ∧ workF i < codes := by
  obtain ⟨t, ht1, ht2, ht3⟩ := posOf_surj lensF codes i hb hi
  obtain ⟨hb1, hb2⟩ := posOf_block lensF codes t ht1 ht2
  have hw : workF i = t := by rw [← ht3]; exact hplaced t ht1 ht2
  exact ⟨lensF t, by omega, hb t ht1, by omega, by omega, by rw [hw],
    by rw [hw]; exact ht1⟩

/-- The position-indexed count of a length is that length's `count`. -/
theorem cntSeg_place (lensF workF : Nat → Nat) (codes l : Nat)
    (hb : ∀ j, j < codes → lensF j ≤ 15)
    (hplaced : ∀ t, t < codes → lensF t ≠ 0 → workF (posOf lensF codes t) = t)
    (hl1 : 1 ≤ l) (hl15 : l ≤ 15) :
    cntSeg (fun k => lensF (workF k)) 0 (nlive lensF codes) l
      = count lensF codes l := by
  rw [cntSeg_zero_eq]
  have hoN : offs lensF codes (l + 1) ≤ nlive lensF codes := by
    have h1 := offs_mono lensF codes (show l + 1 ≤ 16 from by omega)
    rw [offs_16_eq_nlive lensF codes hb] at h1
    exact h1
  have hfil : ((List.range (nlive lensF codes)).filter
        (fun k => decide (lensF (workF k) = l))).length
      = ((List.range (nlive lensF codes)).filter
        (fun k => decide (offs lensF codes l ≤ k
                          ∧ k < offs lensF codes (l + 1)))).length := by
    congr 1
    apply List.filter_congr
    intro k hk
    obtain ⟨m, _, _, hm3, hm4, hm5, _⟩ :=
      place_len lensF workF codes k hb hplaced (List.mem_range.mp hk)
    rw [decide_eq_decide]
    constructor
    · intro h
      rw [hm5] at h
      subst h
      exact ⟨hm3, hm4⟩
    · intro h
      rw [hm5]
      exact place_len_unique lensF codes k m l hm3 hm4 h.1 h.2
  rw [hfil, length_filter_interval _ _ _ (offs_mono lensF codes (by omega))
        hoN]
  have := offs_succ lensF codes l hl1
  omega

theorem rev_zero : ∀ l, rev l 0 = 0 := by
  intro l
  induction l with
  | zero => rfl
  | succ n ih => show 0 % 2 * 2 ^ n + rev n (0 / 2) = 0
                 simpa using ih

/-- `minLen` is above any common lower bound on the live lengths. -/
theorem minLen_ge (lensF : Nat → Nat) (codes c : Nat) (hc16 : c ≤ 16)
    (h : ∀ i, i < codes → lensF i ≠ 0 → c ≤ lensF i) :
    c ≤ minLen lensF codes :=
  foldl_min_ge lensF (List.range codes) 16 c hc16
    (fun x hx => h x (List.mem_range.mp hx))

/-- `minLen` is below every live symbol's length. -/
theorem minLen_le (lensF : Nat → Nat) (codes i : Nat) (hi : i < codes)
    (hne : lensF i ≠ 0) : minLen lensF codes ≤ lensF i :=
  foldl_min_le_mem lensF (List.range codes) 16 i (List.mem_range.mpr hi) hne

/-- **`min` is pinned by what the scan finds** — the counterpart of
    `maxLen_char`.  The C's loop 4 stops at the first length with a nonzero
    count, or at `max`; either way that length *is* `minLen`.

    Both `hnz` cases matter: `Mn = M` is the empty-scan case (every count below
    `max` is zero), and there the witness comes from `max` itself. -/
theorem minLen_char (lensF : Nat → Nat) (codes Mn M : Nat)
    (hMn1 : 1 ≤ Mn) (hMn16 : Mn ≤ 16)
    (hM : M = maxLen lensF codes) (hM0 : M ≠ 0)
    (hzero : ∀ j, 1 ≤ j → j < Mn → count lensF codes j = 0)
    (hnz : Mn = M ∨ count lensF codes Mn ≠ 0) :
    Mn = minLen lensF codes := by
  have hmaxne : maxLen lensF codes ≠ 0 := by rw [← hM]; exact hM0
  -- `Mn ≤ minLen`: no live symbol is shorter than `Mn`
  have hge : Mn ≤ minLen lensF codes := by
    refine minLen_ge lensF codes Mn hMn16 (fun i hi hne => ?_)
    -- no `by_contra` without Mathlib
    refine Nat.not_lt.mp (fun hlt => ?_)
    have h1 : 1 ≤ lensF i := Nat.one_le_iff_ne_zero.mpr hne
    have hz := hzero (lensF i) h1 hlt
    have hp := count_pos lensF codes (lensF i) i hi rfl
    omega
  -- `minLen ≤ Mn`: some live symbol has length exactly `Mn`
  have hpos : 0 < count lensF codes Mn := by
    rcases hnz with hEq | hnz
    · obtain ⟨i, hi, he⟩ := exists_eq_maxLen lensF codes hmaxne
      exact count_pos lensF codes Mn i hi (by rw [he, ← hM, ← hEq])
    · exact Nat.pos_of_ne_zero hnz
  obtain ⟨i, hi, he⟩ := exists_of_count_pos lensF codes Mn hpos
  have hle := minLen_le lensF codes i hi (by rw [he]; omega)
  rw [he] at hle
  omega

/-- A nonzero `maxLen` means at least one live symbol. -/
theorem nlive_pos_of_maxLen (lensF : Nat → Nat) (codes : Nat)
    (hmax : maxLen lensF codes ≠ 0) : 0 < nlive lensF codes := by
  obtain ⟨i, hi, he⟩ := exists_eq_maxLen lensF codes (by omega)
  unfold nlive
  exact List.length_pos_of_mem
    (List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [he, hmax]⟩)

/-- **The first slot of `work[]` holds a shortest code** — the entry value of
    the main loop's `len`, since the C sets `len = min`. -/
theorem first_slot_minLen (lensF workF : Nat → Nat) (codes : Nat)
    (hb : ∀ j, j < codes → lensF j ≤ 15)
    (hplaced : ∀ t, t < codes → lensF t ≠ 0 → workF (posOf lensF codes t) = t)
    (hsort : ∀ i j, i ≤ j → j < nlive lensF codes →
      lensF (workF i) ≤ lensF (workF j))
    (hpos : 0 < nlive lensF codes) :
    lensF (workF 0) = minLen lensF codes := by
  obtain ⟨l, hl1, hl15, _, _, hl5, hlt⟩ :=
    place_len lensF workF codes 0 hb hplaced hpos
  have hnz : lensF (workF 0) ≠ 0 := by omega
  have hle : minLen lensF codes ≤ lensF (workF 0) :=
    (lens_between lensF codes (workF 0) hlt hnz).1
  have hge : lensF (workF 0) ≤ minLen lensF codes := by
    refine minLen_ge lensF codes _ (by omega) (fun i hi hiz => ?_)
    -- `i` sits at slot `posOf i`, and slot 0 is the smallest
    have hslot : posOf lensF codes i < nlive lensF codes := by
      obtain ⟨hb1, hb2⟩ := posOf_block lensF codes i hi hiz
      have h16 := offs_16_eq_nlive lensF codes hb
      have hup := offs_mono lensF codes
        (show lensF i + 1 ≤ 16 from by have := hb i hi; omega)
      omega
    have := hsort 0 (posOf lensF codes i) (Nat.zero_le _) hslot
    rwa [hplaced i hi hiz] at this
  omega

/-- `rev` at width `l` is injective at `0` on `[0, 2^l)` — so the C's
    `huff = 0` wrap really does mean "the code space is exactly full". -/
theorem rev_eq_zero : ∀ l x, x < 2 ^ l → rev l x = 0 → x = 0 := by
  intro l
  induction l with
  | zero => intro x hx _; simpa using hx
  | succ n ih =>
      intro x hx h
      have hsplit : x % 2 * 2 ^ n + rev n (x / 2) = 0 := h
      have h1 : x % 2 = 0 := by
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        rcases Nat.eq_zero_or_pos (x % 2) with h0 | h0
        · exact h0
        · exfalso
          have : 2 ^ n ≤ x % 2 * 2 ^ n := Nat.le_mul_of_pos_left _ h0
          omega
      have h2 : rev n (x / 2) = 0 := by omega
      have hxd : x / 2 < 2 ^ n := by
        have : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
        omega
      have := ih (x / 2) hxd h2
      omega

/-- **The `left` counter IS the unused code mass.**  `leftAt 15 = 2^15 −
    massSum`, so "the code is incomplete" (`left > 0`, the test at
    inftrees.c:146-147) and "the mass is not full" are the same statement.
    This is what makes the epilogue's `next[huff]` write provably in bounds. -/
theorem leftAt_15_massSum (lensF : Nat → Nat) (codes : Nat) :
    leftAt lensF codes 15
      = 32768 - (massSum (count lensF codes) : _root_.Int) := by
  have z : leftAt lensF codes 0 = 1 := rfl
  have e0 : leftAt lensF codes 1
      = 2 * leftAt lensF codes 0 - (count lensF codes 1 : _root_.Int) := rfl
  have e1 : leftAt lensF codes 2
      = 2 * leftAt lensF codes 1 - (count lensF codes 2 : _root_.Int) := rfl
  have e2 : leftAt lensF codes 3
      = 2 * leftAt lensF codes 2 - (count lensF codes 3 : _root_.Int) := rfl
  have e3 : leftAt lensF codes 4
      = 2 * leftAt lensF codes 3 - (count lensF codes 4 : _root_.Int) := rfl
  have e4 : leftAt lensF codes 5
      = 2 * leftAt lensF codes 4 - (count lensF codes 5 : _root_.Int) := rfl
  have e5 : leftAt lensF codes 6
      = 2 * leftAt lensF codes 5 - (count lensF codes 6 : _root_.Int) := rfl
  have e6 : leftAt lensF codes 7
      = 2 * leftAt lensF codes 6 - (count lensF codes 7 : _root_.Int) := rfl
  have e7 : leftAt lensF codes 8
      = 2 * leftAt lensF codes 7 - (count lensF codes 8 : _root_.Int) := rfl
  have e8 : leftAt lensF codes 9
      = 2 * leftAt lensF codes 8 - (count lensF codes 9 : _root_.Int) := rfl
  have e9 : leftAt lensF codes 10
      = 2 * leftAt lensF codes 9 - (count lensF codes 10 : _root_.Int) := rfl
  have e10 : leftAt lensF codes 11
      = 2 * leftAt lensF codes 10 - (count lensF codes 11 : _root_.Int) := rfl
  have e11 : leftAt lensF codes 12
      = 2 * leftAt lensF codes 11 - (count lensF codes 12 : _root_.Int) := rfl
  have e12 : leftAt lensF codes 13
      = 2 * leftAt lensF codes 12 - (count lensF codes 13 : _root_.Int) := rfl
  have e13 : leftAt lensF codes 14
      = 2 * leftAt lensF codes 13 - (count lensF codes 14 : _root_.Int) := rfl
  have e14 : leftAt lensF codes 15
      = 2 * leftAt lensF codes 14 - (count lensF codes 15 : _root_.Int) := rfl
  unfold massSum
  omega

/-- **A non-wrapping `bwInc` means the code space is not full.**  The
    contrapositive is the C's `huff = 0` idiom: when the last code exhausts the
    space, the backwards increment carries all the way out and yields `0`. -/
theorem mass_lt_of_bwInc_ne_zero (g : Nat → Nat) (sig len huff : Nat)
    (hl15 : len ≤ 15) (hg : g sig = len)
    (hJ : massBelow g sig = rev len huff * 2 ^ (15 - len))
    (hne : bwInc huff len ≠ 0) :
    massBelow g (sig + 1) < 2 ^ 15 := by
  have hstep : massBelow g (sig + 1) = massBelow g sig + 2 ^ (15 - g sig) := rfl
  rw [hstep, hg, hJ, ← Nat.succ_mul]
  have hpow : 2 ^ len * 2 ^ (15 - len) = 2 ^ 15 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (15 - len) := Nat.two_pow_pos _
  have hrl : rev len huff < 2 ^ len := rev_lt len huff
  rcases Nat.lt_or_ge (rev len huff + 1) (2 ^ len) with h | h
  · calc (rev len huff + 1) * 2 ^ (15 - len)
        < 2 ^ len * 2 ^ (15 - len) := (Nat.mul_lt_mul_right hpos).mpr h
      _ = 2 ^ 15 := hpow
  · exfalso
    have heq : rev len huff + 1 = 2 ^ len := by omega
    exact hne (rev_eq_zero len (bwInc huff len) (bwIncGo_lt huff len)
      (by rw [bwInc_rev, heq, Nat.mod_self]))

/-- **The loop's `break` really is the last symbol.**  If the current symbol
    has the maximal length and only one symbol of that length remains, nothing
    at all remains after it — because sortedness puts every later symbol at
    that same maximal length. -/
theorem sym_last_of_count_one (g : Nat → Nat) (sig N M : Nat)
    (hsort : ∀ i j, i ≤ j → j < N → g i ≤ g j)
    (hsig : sig < N) (hmaxg : ∀ k, k < N → g k ≤ M) (hlen : g sig = M)
    (hone : cntSeg g sig N M = 1) : sig + 1 = N := by
  rcases Nat.lt_or_ge (sig + 1) N with h | h
  · exfalso
    have hnext : g (sig + 1) = M := by
      have h1 := hsort sig (sig + 1) (by omega) h
      have h2 := hmaxg (sig + 1) h
      omega
    have hstep : cntSeg g sig N M
        = (if g sig = M then 1 else 0) + cntSeg g (sig + 1) N M :=
      cntSeg_succ g sig N M hsig
    rw [if_pos hlen] at hstep
    have hz : cntSeg g (sig + 1) N M = 0 := by omega
    have hp : 1 ≤ cntSeg g (sig + 1) N M :=
      cntSeg_pos g (sig + 1) N M (sig + 1) (Nat.le_refl _) h hnext
    omega
  · omega

/-- **Kraft.**  The over-subscription check (inftrees.c:140-145) passing is
    exactly "the total code mass fits in one 15-bit line".  Fifteen unfoldings
    of `leftAt`, then `omega` — the same shape as `incomplete_count_one`. -/
theorem massSum_count_le (lensF : Nat → Nat) (codes : Nat)
    (hk : kraftOk lensF codes) : massSum (count lensF codes) ≤ 32768 := by
  have u : ∀ l : Nat, leftAt lensF codes (l + 1)
      = 2 * leftAt lensF codes l - (count lensF codes (l + 1) : _root_.Int) :=
    fun _ => rfl
  have z : leftAt lensF codes 0 = 1 := rfl
  have h15 := hk 15 (by omega)
  have e0 : leftAt lensF codes 1
      = 2 * leftAt lensF codes 0 - (count lensF codes 1 : _root_.Int) := u 0
  have e1 : leftAt lensF codes 2
      = 2 * leftAt lensF codes 1 - (count lensF codes 2 : _root_.Int) := u 1
  have e2 : leftAt lensF codes 3
      = 2 * leftAt lensF codes 2 - (count lensF codes 3 : _root_.Int) := u 2
  have e3 : leftAt lensF codes 4
      = 2 * leftAt lensF codes 3 - (count lensF codes 4 : _root_.Int) := u 3
  have e4 : leftAt lensF codes 5
      = 2 * leftAt lensF codes 4 - (count lensF codes 5 : _root_.Int) := u 4
  have e5 : leftAt lensF codes 6
      = 2 * leftAt lensF codes 5 - (count lensF codes 6 : _root_.Int) := u 5
  have e6 : leftAt lensF codes 7
      = 2 * leftAt lensF codes 6 - (count lensF codes 7 : _root_.Int) := u 6
  have e7 : leftAt lensF codes 8
      = 2 * leftAt lensF codes 7 - (count lensF codes 8 : _root_.Int) := u 7
  have e8 : leftAt lensF codes 9
      = 2 * leftAt lensF codes 8 - (count lensF codes 9 : _root_.Int) := u 8
  have e9 : leftAt lensF codes 10
      = 2 * leftAt lensF codes 9 - (count lensF codes 10 : _root_.Int) := u 9
  have e10 : leftAt lensF codes 11
      = 2 * leftAt lensF codes 10 - (count lensF codes 11 : _root_.Int) := u 10
  have e11 : leftAt lensF codes 12
      = 2 * leftAt lensF codes 11 - (count lensF codes 12 : _root_.Int) := u 11
  have e12 : leftAt lensF codes 13
      = 2 * leftAt lensF codes 12 - (count lensF codes 13 : _root_.Int) := u 12
  have e13 : leftAt lensF codes 14
      = 2 * leftAt lensF codes 13 - (count lensF codes 14 : _root_.Int) := u 13
  have e14 : leftAt lensF codes 15
      = 2 * leftAt lensF codes 14 - (count lensF codes 15 : _root_.Int) := u 14
  unfold massSum
  omega

end InflateTable.Model
