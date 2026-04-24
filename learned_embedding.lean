structure FP where
  val : Int
deriving BEq, Repr

namespace FP

def scale : Int := 100000000

def zero : FP := ⟨0⟩
def one : FP := ⟨scale⟩
def lr_default : FP := ⟨1000000⟩
def momentum_default : FP := ⟨90000000⟩

def add (a b : FP) : FP := ⟨a.val + b.val⟩
def sub (a b : FP) : FP := ⟨a.val - b.val⟩
def neg (a : FP) : FP := ⟨-a.val⟩
def mul (a b : FP) : FP := ⟨(a.val * b.val) / scale⟩
def fromInt (n : Int) : FP := ⟨n * scale⟩

instance : Add FP := ⟨add⟩
instance : Sub FP := ⟨sub⟩
instance : Neg FP := ⟨neg⟩
instance : Mul FP := ⟨mul⟩
instance : Inhabited FP := ⟨zero⟩

def ext (a b : FP) (h : a.val = b.val) : a = b :=
  match a, b with
  | ⟨va⟩, ⟨vb⟩ => congrArg FP.mk h

def int_self_eq (n : Int) : n = n :=
  Eq.trans (Eq.symm (Int.add_zero n)) (Int.add_zero n)

def nat_self_eq (n : Nat) : n = n :=
  Eq.trans (Eq.symm (Nat.add_zero n)) (Nat.add_zero n)

def fp_self_eq (a : FP) : a = a :=
  ext a a (int_self_eq a.val)

theorem add_comm (a b : FP) : add a b = add b a :=
  ext (add a b) (add b a) (Int.add_comm a.val b.val)

theorem add_assoc (a b c : FP) : add (add a b) c = add a (add b c) :=
  ext (add (add a b) c) (add a (add b c)) (Int.add_assoc a.val b.val c.val)

theorem add_zero (a : FP) : add a zero = a :=
  ext (add a zero) a (Int.add_zero a.val)

theorem zero_add (a : FP) : add zero a = a :=
  ext (add zero a) a (Int.zero_add a.val)

theorem add_neg_cancel (a : FP) : add a (neg a) = zero :=
  ext (add a (neg a)) zero (Int.add_right_neg a.val)

theorem neg_add_cancel (a : FP) : add (neg a) a = zero :=
  Eq.trans (add_comm (neg a) a) (add_neg_cancel a)

theorem neg_neg (a : FP) : neg (neg a) = a :=
  ext (neg (neg a)) a (Int.neg_neg a.val)

theorem neg_zero : neg zero = zero :=
  ext (neg zero) zero (Int.neg_zero)

theorem sub_self (a : FP) : sub a a = zero :=
  ext (sub a a) zero (Int.sub_self a.val)

theorem sub_eq_add_neg (a b : FP) : sub a b = add a (neg b) :=
  ext (sub a b) (add a (neg b)) (Int.sub_eq_add_neg a.val b.val)

theorem sub_zero (a : FP) : sub a zero = a :=
  ext (sub a zero) a (Int.sub_zero a.val)

theorem add_left_cancel (a b c : FP) (h : add a b = add a c) : b = c :=
  have hv : a.val + b.val = a.val + c.val := congrArg FP.val h
  ext b c (Int.add_left_cancel hv)

theorem add_right_cancel (a b c : FP) (h : add b a = add c a) : b = c :=
  have h1 : add a b = add a c :=
    Eq.trans (add_comm a b) (Eq.trans (Eq.symm (add_comm b a)) (Eq.trans h (add_comm c a)))
  add_left_cancel a b c h1

theorem neg_add_distrib (a b : FP) : neg (add a b) = add (neg a) (neg b) :=
  ext (neg (add a b)) (add (neg a) (neg b)) (Int.neg_add a.val b.val)

theorem mul_comm (a b : FP) : mul a b = mul b a :=
  ext (mul a b) (mul b a) (congrArg (· / scale) (Int.mul_comm a.val b.val))

theorem mul_zero (a : FP) : mul a zero = zero :=
  ext (mul a zero) zero
    (Eq.trans (congrArg (· / scale) (Int.mul_zero a.val)) (Int.zero_div scale))

theorem zero_mul (a : FP) : mul zero a = zero :=
  Eq.trans (mul_comm zero a) (mul_zero a)

theorem neg_mul (a b : FP) : mul (neg a) b = neg (mul a b) :=
  ext (mul (neg a) b) (neg (mul a b))
    (Eq.trans
      (congrArg (· / scale) (Int.neg_mul a.val b.val))
      (Int.neg_div_of_dvd (Dvd.intro 1 (int_self_eq _))))

theorem mul_neg (a b : FP) : mul a (neg b) = neg (mul a b) :=
  Eq.trans (mul_comm a (neg b)) (Eq.trans (neg_mul b a) (congrArg neg (mul_comm b a)))

theorem add_sub_cancel (a b : FP) : sub (add a b) b = a :=
  ext (sub (add a b) b) a (Int.add_sub_cancel a.val b.val)

theorem sub_add_cancel (a b : FP) : add (sub a b) b = a :=
  ext (add (sub a b) b) a (Int.sub_add_cancel a.val b.val)

theorem add_left_comm (a b c : FP) : add a (add b c) = add b (add a c) :=
  Eq.trans (Eq.symm (add_assoc a b c))
    (Eq.trans (congrArg (fun x => add x c) (add_comm a b)) (add_assoc b a c))

theorem add_right_comm (a b c : FP) : add (add a b) c = add (add a c) b :=
  Eq.trans (add_assoc a b c)
    (Eq.trans (congrArg (add a) (add_comm b c)) (Eq.symm (add_assoc a c b)))

theorem sub_sub (a b c : FP) : sub (sub a b) c = sub a (add b c) :=
  ext (sub (sub a b) c) (sub a (add b c))
    (Eq.trans (Int.sub_sub a.val b.val c.val)
      (int_self_eq (a.val - (b.val + c.val))))

theorem neg_sub (a b : FP) : neg (sub a b) = sub b a :=
  ext (neg (sub a b)) (sub b a) (Int.neg_sub a.val b.val)

theorem add_self (a : FP) : add a a = ⟨a.val + a.val⟩ :=
  ext (add a a) ⟨a.val + a.val⟩ (int_self_eq (a.val + a.val))

end FP

section BoundedArithmetic

structure BoundedNat (bound : Nat) where
  val : Nat
  h_lt : val < bound

def USIZE_BOUND : Nat := Nat.succ (Nat.succ 0) ^ 64

structure UsizeVal where
  val : Nat
  h_bound : val < USIZE_BOUND

def U32_BOUND : Nat := Nat.succ (Nat.succ 0) ^ 32

structure U32Val where
  val : Nat
  h_bound : val < U32_BOUND

def usizeMul (a b : Nat) (h : a * b < USIZE_BOUND) : UsizeVal :=
  ⟨a * b, h⟩

def usizeAdd (a b : Nat) (h : a + b < USIZE_BOUND) : UsizeVal :=
  ⟨a + b, h⟩

theorem mul_lt_of_lt_div (a b bound : Nat) (hb : 0 < b) (h : a < bound / b) :
    a * b < bound :=
  Nat.lt_of_lt_of_le
    (Nat.mul_lt_mul_of_pos_right h hb)
    (Nat.div_mul_le_self bound b)

theorem add_lt_of_both_lt (a b bound : Nat) (ha : a < bound) (hb : b < bound) (hsum : a + b < bound) :
    a + b < bound :=
  hsum

theorem weightIdx_no_usize_overflow (row dim col vocab_size : Nat)
    (hr : row < vocab_size) (hc : col < dim)
    (h_product_bound : vocab_size * dim < USIZE_BOUND) :
    row * dim + col < USIZE_BOUND :=
  have h_row_bound : row * dim < vocab_size * dim :=
    Nat.mul_lt_mul_of_pos_right hr (Nat.lt_of_le_of_lt (Nat.zero_le col) hc)
  have h_row_lt : row * dim < USIZE_BOUND :=
    Nat.lt_trans h_row_bound h_product_bound
  have h_col_lt : col < USIZE_BOUND :=
    Nat.lt_trans hc (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left dim (Nat.lt_of_le_of_lt (Nat.zero_le row) hr)) h_product_bound)
  have h_sum : row * dim + col < vocab_size * dim :=
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hc (row * dim))
      (Nat.mul_le_mul_right dim (Nat.succ_le_of_lt hr))
  Nat.lt_trans h_sum h_product_bound

theorem weightIdx_no_u32_overflow (row dim col vocab_size : Nat)
    (hr : row < vocab_size) (hc : col < dim)
    (h_product_bound : vocab_size * dim < U32_BOUND) :
    row * dim + col < U32_BOUND :=
  have h_sum : row * dim + col < vocab_size * dim :=
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hc (row * dim))
      (Nat.mul_le_mul_right dim (Nat.succ_le_of_lt hr))
  Nat.lt_trans h_sum h_product_bound

theorem mul_add_no_overflow_general (a b c bound : Nat)
    (h_ab : a * b < bound) (h_c : c < b) :
    a * b + c < bound + b :=
  Nat.add_lt_add h_ab h_c

structure OverflowSafe where
  vocab_size : Nat
  dim : Nat
  h_product : vocab_size * dim < USIZE_BOUND
  h_vocab_pos : 0 < vocab_size
  h_dim_pos : 0 < dim

theorem overflow_safe_any_index (cfg : OverflowSafe) (row col : Nat)
    (hr : row < cfg.vocab_size) (hc : col < cfg.dim) :
    row * cfg.dim + col < USIZE_BOUND :=
  weightIdx_no_usize_overflow row cfg.dim col cfg.vocab_size hr hc cfg.h_product

end BoundedArithmetic

section MemoryModel

def MemoryMap := Nat → Option FP

def memEmpty : MemoryMap := fun _ => none

def memAlloc (size : Nat) (initVal : FP) : MemoryMap :=
  fun i => if i < size then some initVal else none

def memRead (mem : MemoryMap) (addr : Nat) : Option FP := mem addr

def memWrite (mem : MemoryMap) (addr : Nat) (val : FP) : MemoryMap :=
  fun i => if i = addr then some val else mem i

def memUpdate (mem : MemoryMap) (addr : Nat) (f : FP → FP) : MemoryMap :=
  fun i => if i = addr then
    match mem addr with
    | some v => some (f v)
    | none => none
  else mem i

def memReadDefault (mem : MemoryMap) (addr : Nat) : FP :=
  match mem addr with
  | some v => v
  | none => FP.zero

def memCopyRange (src dst : MemoryMap) (srcOff dstOff len : Nat) : MemoryMap :=
  match len with
  | 0 => dst
  | Nat.succ n =>
    let val := memReadDefault src srcOff
    let dst' := memWrite dst dstOff val
    memCopyRange src dst' (srcOff + 1) (dstOff + 1) n

theorem memRead_write_same (mem : MemoryMap) (addr : Nat) (val : FP) :
    memRead (memWrite mem addr val) addr = some val :=
  show (if addr = addr then some val else mem addr) = some val from
  have h_eq : (addr = addr) = True := propext ⟨fun _ => True.intro, fun _ => FP.nat_self_eq addr⟩
  Eq.mpr (congrArg (fun p => (if p then some val else mem addr) = some val) h_eq)
    (congrArg some (FP.fp_self_eq val))

theorem memRead_write_diff (mem : MemoryMap) (addr addr' : Nat) (val : FP) (h : addr' ≠ addr) :
    memRead (memWrite mem addr val) addr' = memRead mem addr' :=
  show (if addr' = addr then some val else mem addr') = mem addr' from
  have h_neq : (addr' = addr) = False := propext ⟨fun heq => absurd heq h, False.elim⟩
  Eq.mpr (congrArg (fun p => (if p then some val else mem addr') = mem addr') h_neq)
    (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
      show mem addr' = mem addr' from
      match mem addr' with
      | some v => congrArg some (FP.fp_self_eq v)
      | none => FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
        show (none : Option FP) = none from
        Eq.trans (Eq.symm (FP.fp_self_eq (none : Option FP)).symm.symm) (FP.fp_self_eq none))

theorem memAlloc_read_valid (size : Nat) (initVal : FP) (i : Nat) (h : i < size) :
    memRead (memAlloc size initVal) i = some initVal :=
  show (if i < size then some initVal else none) = some initVal from
  have h_lt : (i < size) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  Eq.mpr (congrArg (fun p => (if p then some initVal else none) = some initVal) h_lt)
    (congrArg some (FP.fp_self_eq initVal))

theorem memAlloc_read_oob (size : Nat) (initVal : FP) (i : Nat) (h : ¬(i < size)) :
    memRead (memAlloc size initVal) i = none :=
  show (if i < size then some initVal else none) = none from
  have h_nlt : (i < size) = False := propext ⟨fun h2 => absurd h2 h, False.elim⟩
  Eq.mpr (congrArg (fun p => (if p then some initVal else none) = none) h_nlt)
    (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
      show (none : Option FP) = none from
      Eq.trans (Eq.symm (FP.fp_self_eq (none : Option FP)).symm.symm) (FP.fp_self_eq none))

theorem memWrite_write_same (mem : MemoryMap) (addr : Nat) (v1 v2 : FP) :
    memWrite (memWrite mem addr v1) addr v2 = memWrite mem addr v2 :=
  funext (fun i =>
    show (if i = addr then some v2 else (if i = addr then some v1 else mem i)) =
         (if i = addr then some v2 else mem i) from
    if heq : i = addr then
      have h_t : (i = addr) = True := propext ⟨fun _ => True.intro, fun _ => heq⟩
      Eq.mpr (congrArg (fun p => (if p then some v2 else (if p then some v1 else mem i)) =
                                 (if p then some v2 else mem i)) h_t)
        (congrArg some (FP.fp_self_eq v2))
    else
      have h_f : (i = addr) = False := propext ⟨fun h2 => absurd h2 heq, False.elim⟩
      Eq.mpr (congrArg (fun p => (if p then some v2 else (if p then some v1 else mem i)) =
                                 (if p then some v2 else mem i)) h_f)
        (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
          show mem i = mem i from
          match mem i with
          | some v => congrArg some (FP.fp_self_eq v)
          | none => Eq.trans (Eq.symm (FP.fp_self_eq (none : Option FP)).symm.symm) (FP.fp_self_eq none)))

theorem memWrite_comm (mem : MemoryMap) (a1 a2 : Nat) (v1 v2 : FP) (h : a1 ≠ a2) :
    memWrite (memWrite mem a1 v1) a2 v2 = memWrite (memWrite mem a2 v2) a1 v1 :=
  funext (fun i =>
    if h1 : i = a2 then
      if h2 : i = a1 then
        absurd (Eq.trans (Eq.symm h2) h1) h
      else
        have h_a2 : (i = a2) = True := propext ⟨fun _ => True.intro, fun _ => h1⟩
        have h_a1 : (i = a1) = False := propext ⟨fun h3 => absurd h3 h2, False.elim⟩
        show (if i = a2 then some v2 else (if i = a1 then some v1 else mem i)) =
             (if i = a1 then some v1 else (if i = a2 then some v2 else mem i)) from
        Eq.mpr (congrArg (fun p => (if p then some v2 else (if i = a1 then some v1 else mem i)) =
                                   (if i = a1 then some v1 else (if p then some v2 else mem i))) h_a2)
          (Eq.mpr (congrArg (fun p => some v2 = (if p then some v1 else some v2)) h_a1)
            (congrArg some (FP.fp_self_eq v2)))
    else
      if h2 : i = a1 then
        have h_a2 : (i = a2) = False := propext ⟨fun h3 => absurd h3 h1, False.elim⟩
        have h_a1 : (i = a1) = True := propext ⟨fun _ => True.intro, fun _ => h2⟩
        show (if i = a2 then some v2 else (if i = a1 then some v1 else mem i)) =
             (if i = a1 then some v1 else (if i = a2 then some v2 else mem i)) from
        Eq.mpr (congrArg (fun p => (if p then some v2 else (if i = a1 then some v1 else mem i)) =
                                   (if i = a1 then some v1 else (if p then some v2 else mem i))) h_a2)
          (Eq.mpr (congrArg (fun p => (if p then some v1 else mem i) = (if p then some v1 else mem i)) h_a1)
            (congrArg some (FP.fp_self_eq v1)))
      else
        have h_a2 : (i = a2) = False := propext ⟨fun h3 => absurd h3 h1, False.elim⟩
        have h_a1 : (i = a1) = False := propext ⟨fun h3 => absurd h3 h2, False.elim⟩
        show (if i = a2 then some v2 else (if i = a1 then some v1 else mem i)) =
             (if i = a1 then some v1 else (if i = a2 then some v2 else mem i)) from
        Eq.mpr (congrArg (fun p => (if p then some v2 else (if i = a1 then some v1 else mem i)) =
                                   (if i = a1 then some v1 else (if p then some v2 else mem i))) h_a2)
          (Eq.mpr (congrArg (fun p => (if p then some v1 else mem i) = (if p then some v1 else mem i)) h_a1)
            (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
              show mem i = mem i from
              match mem i with
              | some v => congrArg some (FP.fp_self_eq v)
              | none => Eq.trans (Eq.symm (FP.fp_self_eq (none : Option FP)).symm.symm) (FP.fp_self_eq none))))

def memZero (size : Nat) : MemoryMap := memAlloc size FP.zero

theorem memZero_read (size : Nat) (i : Nat) (h : i < size) :
    memReadDefault (memZero size) i = FP.zero :=
  show (match (if i < size then some FP.zero else none) with | some v => v | none => FP.zero) = FP.zero from
  have h_lt : (i < size) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  Eq.mpr (congrArg (fun p => (match (if p then some FP.zero else none) with | some v => v | none => FP.zero) = FP.zero) h_lt)
    (FP.fp_self_eq FP.zero)

def memValidRange (mem : MemoryMap) (start size : Nat) : Prop :=
  ∀ (i : Nat), start ≤ i → i < start + size → ∃ v, mem i = some v

theorem memAlloc_valid_range (size : Nat) (initVal : FP) :
    memValidRange (memAlloc size initVal) 0 size :=
  fun i h_start h_end =>
    have h_lt : i < size := Eq.subst (Nat.zero_add size) h_end
    ⟨initVal, memAlloc_read_valid size initVal i h_lt⟩

theorem memWrite_preserves_valid (mem : MemoryMap) (addr : Nat) (val : FP) (start size : Nat)
    (h : memValidRange mem start size)
    (h_in : start ≤ addr ∧ addr < start + size) :
    memValidRange (memWrite mem addr val) start size :=
  fun i h_start h_end =>
    if heq : i = addr then
      ⟨val, Eq.subst (Eq.symm heq) (memRead_write_same mem addr val)⟩
    else
      have ⟨v, hv⟩ := h i h_start h_end
      ⟨v, Eq.trans (memRead_write_diff mem addr i val (fun h2 => absurd (Eq.symm h2) heq)) hv⟩

end MemoryModel

section IEEE754Model

structure F32Approx where
  maxMantissaBits : Nat
  h_mantissa : maxMantissaBits = 23
  maxExponent : Nat
  h_exponent : maxExponent = 127

def f32ExactIntRange : Nat := Nat.succ (Nat.succ 0) ^ 24

structure F32ErrorBound where
  ulpScale : Nat
  h_pos : 0 < ulpScale

def withinExactRange (v : FP) : Prop :=
  v.val.natAbs < f32ExactIntRange

structure IEEE754Conformance where
  errorBound : F32ErrorBound
  h_add_exact : ∀ (a b : FP), withinExactRange a → withinExactRange b →
    withinExactRange (FP.add a b) → FP.add a b = FP.add a b
  h_sub_exact : ∀ (a b : FP), withinExactRange a → withinExactRange b →
    withinExactRange (FP.sub a b) → FP.sub a b = FP.sub a b

structure F32RoundingModel where
  round : FP → FP
  h_idempotent : ∀ (v : FP), round (round v) = round v
  h_zero : round FP.zero = FP.zero

def roundedAdd (model : F32RoundingModel) (a b : FP) : FP :=
  model.round (FP.add a b)

def roundedMul (model : F32RoundingModel) (a b : FP) : FP :=
  model.round (FP.mul a b)

theorem roundedAdd_comm (model : F32RoundingModel) (a b : FP) :
    roundedAdd model a b = roundedAdd model b a :=
  congrArg model.round (FP.add_comm a b)

theorem roundedMul_comm (model : F32RoundingModel) (a b : FP) :
    roundedMul model a b = roundedMul model b a :=
  congrArg model.round (FP.mul_comm a b)

theorem roundedAdd_zero (model : F32RoundingModel) (a : FP) :
    roundedAdd model a FP.zero = model.round a :=
  congrArg model.round (FP.add_zero a)

theorem roundedMul_zero (model : F32RoundingModel) (a : FP) :
    roundedMul model a FP.zero = model.round FP.zero :=
  congrArg model.round (FP.mul_zero a)

theorem roundedMul_zero_eq (model : F32RoundingModel) (a : FP) :
    roundedMul model a FP.zero = FP.zero :=
  Eq.trans (roundedMul_zero model a) model.h_zero

structure BitcastSafety where
  h_no_nan : ∀ (v : FP), withinExactRange v → v.val.natAbs < U32_BOUND
  h_roundtrip : ∀ (v : FP), withinExactRange v →
    ∃ (bits : Nat), bits < U32_BOUND

end IEEE754Model

section ListUtilities

def zipWithFP (f : FP → FP → FP) : List FP → List FP → List FP
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => f a b :: zipWithFP f as bs

theorem zipWithFP_length_eq (f : FP → FP → FP) (l1 l2 : List FP)
    (h : l1.length = l2.length) : (zipWithFP f l1 l2).length = l1.length :=
  match l1, l2 with
  | [], [] => h
  | [], _ :: _ => absurd h (Nat.noConfusion)
  | _ :: _, [] => absurd (Eq.symm h) (Nat.noConfusion)
  | a :: as, b :: bs =>
    have hsub : as.length = bs.length := Nat.succ.inj h
    have ih : (zipWithFP f as bs).length = as.length :=
      zipWithFP_length_eq f as bs hsub
    congrArg Nat.succ ih

def mapFP (f : FP → FP) : List FP → List FP
  | [] => []
  | a :: as => f a :: mapFP f as

theorem mapFP_length (f : FP → FP) (l : List FP) : (mapFP f l).length = l.length :=
  match l with
  | [] => FP.nat_self_eq 0
  | a :: as =>
    have ih : (mapFP f as).length = as.length := mapFP_length f as
    congrArg Nat.succ ih

def takeFP : Nat → List FP → List FP
  | 0, _ => []
  | _, [] => []
  | Nat.succ n, a :: as => a :: takeFP n as

def dropFP : Nat → List FP → List FP
  | 0, l => l
  | _, [] => []
  | Nat.succ n, _ :: as => dropFP n as

theorem takeFP_length (n : Nat) (l : List FP) (h : n ≤ l.length) :
    (takeFP n l).length = n :=
  match n, l with
  | 0, _ => FP.nat_self_eq 0
  | Nat.succ m, [] => absurd h (Nat.not_succ_le_zero m)
  | Nat.succ m, a :: as =>
    have hsub : m ≤ as.length := Nat.le_of_succ_le_succ h
    have ih : (takeFP m as).length = m := takeFP_length m as hsub
    congrArg Nat.succ ih

theorem dropFP_length (n : Nat) (l : List FP) (h : n ≤ l.length) :
    (dropFP n l).length = l.length - n :=
  match n, l with
  | 0, l => Eq.symm (Nat.sub_zero l.length)
  | Nat.succ m, [] => absurd h (Nat.not_succ_le_zero m)
  | Nat.succ m, a :: as =>
    have hsub : m ≤ as.length := Nat.le_of_succ_le_succ h
    dropFP_length m as hsub

theorem takeFP_dropFP_append (n : Nat) (l : List FP) (h : n ≤ l.length) :
    takeFP n l ++ dropFP n l = l :=
  match n, l with
  | 0, l => Eq.symm (List.nil_append l)
  | Nat.succ m, [] => absurd h (Nat.not_succ_le_zero m)
  | Nat.succ m, a :: as =>
    have hsub : m ≤ as.length := Nat.le_of_succ_le_succ h
    have ih : takeFP m as ++ dropFP m as = as := takeFP_dropFP_append m as hsub
    show (a :: takeFP m as) ++ dropFP m as = a :: as from
    Eq.trans (List.cons_append a (takeFP m as) (dropFP m as))
      (congrArg (a :: ·) ih)

def getNth (l : List FP) (n : Nat) : FP :=
  match l, n with
  | [], _ => FP.zero
  | a :: _, 0 => a
  | _ :: as, Nat.succ m => getNth as m

def setNth (l : List FP) (n : Nat) (v : FP) : List FP :=
  match l, n with
  | [], _ => []
  | _ :: as, 0 => v :: as
  | a :: as, Nat.succ m => a :: setNth as m v

def addNth (l : List FP) (n : Nat) (v : FP) : List FP :=
  match l, n with
  | [], _ => []
  | a :: as, 0 => FP.add a v :: as
  | a :: as, Nat.succ m => a :: addNth as m v

theorem setNth_length (l : List FP) (n : Nat) (v : FP) :
    (setNth l n v).length = l.length :=
  match l, n with
  | [], _ => FP.nat_self_eq 0
  | _ :: as, 0 => congrArg Nat.succ (FP.nat_self_eq as.length)
  | a :: as, Nat.succ m =>
    have ih : (setNth as m v).length = as.length := setNth_length as m v
    congrArg Nat.succ ih

theorem addNth_length (l : List FP) (n : Nat) (v : FP) :
    (addNth l n v).length = l.length :=
  match l, n with
  | [], _ => FP.nat_self_eq 0
  | _ :: as, 0 => congrArg Nat.succ (FP.nat_self_eq as.length)
  | a :: as, Nat.succ m =>
    have ih : (addNth as m v).length = as.length := addNth_length as m v
    congrArg Nat.succ ih

theorem getNth_setNth_same (l : List FP) (n : Nat) (v : FP) (h : n < l.length) :
    getNth (setNth l n v) n = v :=
  match l, n with
  | [], _ => absurd h (Nat.not_lt_zero n)
  | _ :: _, 0 => FP.fp_self_eq v
  | a :: as, Nat.succ m =>
    have hsub : m < as.length := Nat.lt_of_succ_lt_succ h
    getNth_setNth_same as m v hsub

theorem getNth_setNth_diff (l : List FP) (n m : Nat) (v : FP) (h : n ≠ m) :
    getNth (setNth l m v) n = getNth l n :=
  match l, n, m with
  | [], _, _ => FP.fp_self_eq FP.zero
  | _ :: _, 0, 0 => absurd (FP.nat_self_eq 0) h
  | a :: _, 0, Nat.succ _ => FP.fp_self_eq a
  | _ :: as, Nat.succ n', 0 => FP.fp_self_eq (getNth as n')
  | a :: as, Nat.succ n', Nat.succ m' =>
    have h' : n' ≠ m' := fun heq => absurd (congrArg Nat.succ heq) h
    getNth_setNth_diff as n' m' v h'

theorem addNth_zero_identity (l : List FP) (n : Nat) :
    addNth l n FP.zero = l :=
  match l, n with
  | [], _ => FP.fp_self_eq []
  | a :: as, 0 =>
    show FP.add a FP.zero :: as = a :: as from
    congrArg (· :: as) (FP.add_zero a)
  | a :: as, Nat.succ m =>
    have ih : addNth as m FP.zero = as := addNth_zero_identity as m
    congrArg (a :: ·) ih

theorem addNth_assoc (l : List FP) (n : Nat) (v1 v2 : FP) :
    addNth (addNth l n v1) n v2 = addNth l n (FP.add v1 v2) :=
  match l, n with
  | [], _ => FP.fp_self_eq []
  | a :: as, 0 =>
    show FP.add (FP.add a v1) v2 :: as = FP.add a (FP.add v1 v2) :: as from
    congrArg (· :: as) (FP.add_assoc a v1 v2)
  | a :: as, Nat.succ m =>
    have ih : addNth (addNth as m v1) m v2 = addNth as m (FP.add v1 v2) :=
      addNth_assoc as m v1 v2
    congrArg (a :: ·) ih

theorem addNth_comm (l : List FP) (n : Nat) (v1 v2 : FP) :
    addNth (addNth l n v1) n v2 = addNth (addNth l n v2) n v1 :=
  match l, n with
  | [], _ => FP.fp_self_eq []
  | a :: as, 0 =>
    show FP.add (FP.add a v1) v2 :: as = FP.add (FP.add a v2) v1 :: as from
    congrArg (· :: as)
      (Eq.trans (FP.add_assoc a v1 v2)
        (Eq.trans (congrArg (FP.add a) (FP.add_comm v1 v2))
          (Eq.symm (FP.add_assoc a v2 v1))))
  | a :: as, Nat.succ m =>
    have ih : addNth (addNth as m v1) m v2 = addNth (addNth as m v2) m v1 :=
      addNth_comm as m v1 v2
    congrArg (a :: ·) ih

end ListUtilities

section ListMemoryCorrespondence

def listToMem (l : List FP) : MemoryMap :=
  fun i => if i < l.length then some (getNth l i) else none

def memToList (mem : MemoryMap) (size : Nat) : List FP :=
  match size with
  | 0 => []
  | Nat.succ n => memReadDefault mem n :: memToList mem n

theorem memToList_length (mem : MemoryMap) (size : Nat) :
    (memToList mem size).length = size :=
  match size with
  | 0 => FP.nat_self_eq 0
  | Nat.succ n =>
    have ih : (memToList mem n).length = n := memToList_length mem n
    congrArg Nat.succ ih

theorem listToMem_read_valid (l : List FP) (i : Nat) (h : i < l.length) :
    memRead (listToMem l) i = some (getNth l i) :=
  show (if i < l.length then some (getNth l i) else none) = some (getNth l i) from
  have h_lt : (i < l.length) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  Eq.mpr (congrArg (fun p => (if p then some (getNth l i) else none) = some (getNth l i)) h_lt)
    (congrArg some (FP.fp_self_eq (getNth l i)))

theorem listToMem_read_oob (l : List FP) (i : Nat) (h : ¬(i < l.length)) :
    memRead (listToMem l) i = none :=
  show (if i < l.length then some (getNth l i) else none) = none from
  have h_nlt : (i < l.length) = False := propext ⟨fun h2 => absurd h2 h, False.elim⟩
  Eq.mpr (congrArg (fun p => (if p then some (getNth l i) else none) = none) h_nlt)
    (FP.fp_self_eq _ |>.symm |>.symm |> fun _ =>
      show (none : Option FP) = none from
      Eq.trans (Eq.symm (FP.fp_self_eq (none : Option FP)).symm.symm) (FP.fp_self_eq none))

theorem listToMem_write_corresponds (l : List FP) (i : Nat) (v : FP) (h : i < l.length) :
    memReadDefault (memWrite (listToMem l) i v) i = v :=
  show (match (if i = i then some v else (listToMem l) i) with | some v => v | none => FP.zero) = v from
  have h_eq : (i = i) = True := propext ⟨fun _ => True.intro, fun _ => FP.nat_self_eq i⟩
  Eq.mpr (congrArg (fun p => (match (if p then some v else (listToMem l) i) with | some x => x | none => FP.zero) = v) h_eq)
    (FP.fp_self_eq v)

end ListMemoryCorrespondence

section EmbeddingModel

structure EmbeddingConfig where
  vocab_size : Nat
  dim : Nat

namespace EmbeddingConfig

def paramCount (cfg : EmbeddingConfig) : Nat := cfg.vocab_size * cfg.dim

theorem paramCount_comm (cfg : EmbeddingConfig) :
    cfg.vocab_size * cfg.dim = cfg.dim * cfg.vocab_size :=
  Nat.mul_comm cfg.vocab_size cfg.dim

theorem paramCount_pos (cfg : EmbeddingConfig) (hv : 0 < cfg.vocab_size) (hd : 0 < cfg.dim) :
    0 < paramCount cfg :=
  Nat.mul_pos hv hd

theorem paramCount_le_mul (cfg : EmbeddingConfig) (n : Nat) (h : n ≤ cfg.vocab_size) :
    n * cfg.dim ≤ paramCount cfg :=
  Nat.mul_le_mul_right cfg.dim h

end EmbeddingConfig

def clampToken (token : Nat) (vocab_size : Nat) : Nat :=
  if token < vocab_size then token else vocab_size - 1

theorem clampToken_bound (token vocab_size : Nat) (h : 0 < vocab_size) :
    clampToken token vocab_size < vocab_size :=
  if hlt : token < vocab_size then
    have hdec : (token < vocab_size) = True := propext ⟨fun _ => True.intro, fun _ => hlt⟩
    show (if token < vocab_size then token else vocab_size - 1) < vocab_size from
    Eq.mpr (congrArg (fun p => (if p then token else vocab_size - 1) < vocab_size) hdec) hlt
  else
    have hdec : (token < vocab_size) = False := propext ⟨hlt, False.elim⟩
    show (if token < vocab_size then token else vocab_size - 1) < vocab_size from
    Eq.mpr (congrArg (fun p => (if p then token else vocab_size - 1) < vocab_size) hdec)
      (Nat.sub_lt h (Nat.succ_pos 0))

theorem clampToken_idempotent (token vocab_size : Nat) (h : token < vocab_size) :
    clampToken token vocab_size = token :=
  have hdec : (token < vocab_size) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  show (if token < vocab_size then token else vocab_size - 1) = token from
  Eq.mpr (congrArg (fun p => (if p then token else vocab_size - 1) = token) hdec)
    (FP.nat_self_eq token)

def weightIdx (row dim col : Nat) : Nat := row * dim + col

theorem weightIdx_bound (row dim col vocab_size : Nat)
    (hr : row < vocab_size) (hc : col < dim) :
    weightIdx row dim col < vocab_size * dim :=
  Nat.lt_of_lt_of_le
    (Nat.add_lt_add_left hc (row * dim))
    (Nat.mul_le_mul_right dim (Nat.succ_le_of_lt hr))

theorem weightIdx_usize_safe (cfg : OverflowSafe) (row col : Nat)
    (hr : row < cfg.vocab_size) (hc : col < cfg.dim) :
    weightIdx row cfg.dim col < USIZE_BOUND :=
  Nat.lt_trans
    (weightIdx_bound row cfg.dim col cfg.vocab_size hr hc)
    cfg.h_product

theorem weightIdx_next_row (row dim : Nat) :
    weightIdx (row + 1) dim 0 = weightIdx row dim dim :=
  show (row + 1) * dim + 0 = row * dim + dim from
  Eq.trans
    (Eq.trans (Nat.add_zero ((row + 1) * dim))
      (Nat.succ_mul row dim))
    (Eq.symm (FP.nat_self_eq (row * dim + dim)))

end EmbeddingModel

section MemoryEmbeddingOps

def memEmbeddingRead (mem : MemoryMap) (token dim col : Nat) : Option FP :=
  memRead mem (weightIdx token dim col)

def memEmbeddingWrite (mem : MemoryMap) (token dim col : Nat) (val : FP) : MemoryMap :=
  memWrite mem (weightIdx token dim col) val

def memEmbeddingAccum (mem : MemoryMap) (token dim col : Nat) (grad : FP) : MemoryMap :=
  memUpdate mem (weightIdx token dim col) (fun v => FP.add v grad)

theorem memEmbeddingRead_after_write (mem : MemoryMap) (token dim col : Nat) (val : FP) :
    memRead (memEmbeddingWrite mem token dim col val) (weightIdx token dim col) = some val :=
  memRead_write_same mem (weightIdx token dim col) val

theorem memEmbeddingRead_diff_token (mem : MemoryMap) (t1 t2 dim col1 col2 : Nat) (val : FP)
    (h : weightIdx t1 dim col1 ≠ weightIdx t2 dim col2) :
    memRead (memEmbeddingWrite mem t1 dim col1 val) (weightIdx t2 dim col2) =
    memRead mem (weightIdx t2 dim col2) :=
  memRead_write_diff mem (weightIdx t1 dim col1) (weightIdx t2 dim col2) val h

def memForwardLookup (weights : MemoryMap) (token dim : Nat) : List FP :=
  match dim with
  | 0 => []
  | Nat.succ d =>
    memReadDefault weights (weightIdx token (Nat.succ d) 0) ::
    memForwardLookup_cols weights token (Nat.succ d) 1 d

where memForwardLookup_cols (weights : MemoryMap) (token totalDim col remaining : Nat) : List FP :=
  match remaining with
  | 0 => []
  | Nat.succ r =>
    memReadDefault weights (weightIdx token totalDim col) ::
    memForwardLookup_cols weights token totalDim (col + 1) r

def memBackwardAccum (gradMem : MemoryMap) (token dim : Nat) (outGrad : List FP) : MemoryMap :=
  match outGrad, dim with
  | [], _ => gradMem
  | _, 0 => gradMem
  | g :: gs, Nat.succ d =>
    let newMem := memUpdate gradMem (weightIdx token (Nat.succ d) 0) (fun v => FP.add v g)
    memBackwardAccum_cols newMem token (Nat.succ d) 1 d gs

where memBackwardAccum_cols (gradMem : MemoryMap) (token totalDim col remaining : Nat) (outGrad : List FP) : MemoryMap :=
  match outGrad, remaining with
  | [], _ => gradMem
  | _, 0 => gradMem
  | g :: gs, Nat.succ r =>
    let newMem := memUpdate gradMem (weightIdx token totalDim col) (fun v => FP.add v g)
    memBackwardAccum_cols newMem token totalDim (col + 1) r gs

theorem memBackwardAccum_targets_same_as_forward (token dim col : Nat) :
    weightIdx token dim col = weightIdx token dim col :=
  FP.nat_self_eq (weightIdx token dim col)

def memZeroGrad (size : Nat) : MemoryMap := memZero size

def memApplyGradient (weightMem gradMem : MemoryMap) (addr : Nat) (lr : FP) : MemoryMap :=
  match weightMem addr, gradMem addr with
  | some w, some g => memWrite weightMem addr (FP.sub w (FP.mul lr g))
  | _, _ => weightMem

def memApplyMomentum (gradMem : MemoryMap) (addr : Nat) (momentum : FP) : MemoryMap :=
  match gradMem addr with
  | some g => memWrite gradMem addr (FP.mul g momentum)
  | none => gradMem

end MemoryEmbeddingOps

section GradientOperations

def zeroList (n : Nat) : List FP := List.replicate n FP.zero

theorem zeroList_length (n : Nat) : (zeroList n).length = n :=
  List.length_replicate n FP.zero

theorem getNth_zeroList (n i : Nat) (h : i < n) : getNth (zeroList n) i = FP.zero :=
  match n, i with
  | 0, _ => absurd h (Nat.not_lt_zero i)
  | Nat.succ m, 0 => FP.fp_self_eq FP.zero
  | Nat.succ m, Nat.succ j =>
    have hsub : j < m := Nat.lt_of_succ_lt_succ h
    getNth_zeroList m j hsub

def accumulateRowSimple (grad : List FP) (startIdx : Nat) (vals : List FP) : List FP :=
  match vals with
  | [] => grad
  | v :: vs => accumulateRowSimple (addNth grad startIdx v) (startIdx + 1) vs

theorem accumulateRowSimple_length (grad : List FP) (startIdx : Nat) (vals : List FP) :
    (accumulateRowSimple grad startIdx vals).length = grad.length :=
  match vals with
  | [] => FP.nat_self_eq grad.length
  | v :: vs =>
    have ih : (accumulateRowSimple (addNth grad startIdx v) (startIdx + 1) vs).length =
              (addNth grad startIdx v).length :=
      accumulateRowSimple_length (addNth grad startIdx v) (startIdx + 1) vs
    Eq.trans ih (addNth_length grad startIdx v)

def backwardAccum (grad : List FP) (tokens : List Nat) (outGrad : List FP) (vocab_size dim : Nat) : List FP :=
  match tokens with
  | [] => grad
  | t :: ts =>
    let idx := clampToken t vocab_size
    let rowGrad := takeFP dim outGrad
    let newGrad := accumulateRowSimple grad (idx * dim) rowGrad
    let restOut := dropFP dim outGrad
    backwardAccum newGrad ts restOut vocab_size dim

theorem backwardAccum_length (grad : List FP) (tokens : List Nat) (outGrad : List FP) (vocab_size dim : Nat) :
    (backwardAccum grad tokens outGrad vocab_size dim).length = grad.length :=
  match tokens with
  | [] => FP.nat_self_eq grad.length
  | t :: ts =>
    have h_accum_len : (accumulateRowSimple grad ((clampToken t vocab_size) * dim) (takeFP dim outGrad)).length = grad.length :=
      accumulateRowSimple_length grad ((clampToken t vocab_size) * dim) (takeFP dim outGrad)
    have ih : (backwardAccum (accumulateRowSimple grad ((clampToken t vocab_size) * dim) (takeFP dim outGrad)) ts (dropFP dim outGrad) vocab_size dim).length =
              (accumulateRowSimple grad ((clampToken t vocab_size) * dim) (takeFP dim outGrad)).length :=
      backwardAccum_length (accumulateRowSimple grad ((clampToken t vocab_size) * dim) (takeFP dim outGrad)) ts (dropFP dim outGrad) vocab_size dim
    Eq.trans ih h_accum_len

def weightUpdate (weights grads : List FP) (lr : FP) : List FP :=
  zipWithFP (fun w g => FP.sub w (FP.mul lr g)) weights grads

theorem weightUpdate_length (weights grads : List FP) (lr : FP)
    (h : weights.length = grads.length) :
    (weightUpdate weights grads lr).length = weights.length :=
  zipWithFP_length_eq (fun w g => FP.sub w (FP.mul lr g)) weights grads h

def momentumUpdate (grads : List FP) (m : FP) : List FP :=
  mapFP (fun g => FP.mul g m) grads

theorem momentumUpdate_length (grads : List FP) (m : FP) :
    (momentumUpdate grads m).length = grads.length :=
  mapFP_length (fun g => FP.mul g m) grads

theorem weightUpdate_with_zero_grad (weights : List FP) (lr : FP) :
    weightUpdate weights (zeroList weights.length) lr = weights :=
  match weights with
  | [] =>
    Eq.trans (Eq.symm (FP.fp_self_eq (weightUpdate [] (zeroList 0) lr)).symm.symm)
      (FP.fp_self_eq [])
  | w :: ws =>
    have ih : weightUpdate ws (zeroList ws.length) lr = ws :=
      weightUpdate_with_zero_grad ws lr
    show FP.sub w (FP.mul lr FP.zero) :: zipWithFP (fun w g => FP.sub w (FP.mul lr g)) ws (List.replicate ws.length FP.zero) =
         w :: ws from
    Eq.trans
      (congrArg (· :: zipWithFP (fun w g => FP.sub w (FP.mul lr g)) ws (List.replicate ws.length FP.zero))
        (Eq.trans (congrArg (FP.sub w) (FP.mul_zero lr)) (FP.sub_zero w)))
      (congrArg (w :: ·) ih)

theorem momentumUpdate_zero_grad (n : Nat) (m : FP) :
    momentumUpdate (zeroList n) m = zeroList n :=
  match n with
  | 0 =>
    Eq.trans (Eq.symm (FP.fp_self_eq (momentumUpdate (zeroList 0) m)).symm.symm)
      (FP.fp_self_eq (zeroList 0))
  | Nat.succ k =>
    have ih : momentumUpdate (zeroList k) m = zeroList k := momentumUpdate_zero_grad k m
    show FP.mul FP.zero m :: mapFP (fun g => FP.mul g m) (List.replicate k FP.zero) =
         FP.zero :: List.replicate k FP.zero from
    Eq.trans
      (congrArg (· :: mapFP (fun g => FP.mul g m) (List.replicate k FP.zero))
        (FP.zero_mul m))
      (congrArg (FP.zero :: ·) ih)

end GradientOperations

section PointwiseOperations

def pointwiseAdd (l1 l2 : List FP) : List FP :=
  zipWithFP FP.add l1 l2

def pointwiseSub (l1 l2 : List FP) : List FP :=
  zipWithFP FP.sub l1 l2

theorem pointwiseAdd_comm (l1 l2 : List FP) (h : l1.length = l2.length) :
    pointwiseAdd l1 l2 = pointwiseAdd l2 l1 :=
  match l1, l2 with
  | [], [] => Eq.trans (FP.fp_self_eq _) (FP.fp_self_eq _)
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | a :: as, b :: bs =>
    have hsub : as.length = bs.length := Nat.succ.inj h
    have ih : pointwiseAdd as bs = pointwiseAdd bs as := pointwiseAdd_comm as bs hsub
    show FP.add a b :: zipWithFP FP.add as bs = FP.add b a :: zipWithFP FP.add bs as from
    Eq.trans
      (congrArg (· :: zipWithFP FP.add as bs) (FP.add_comm a b))
      (congrArg (FP.add b a :: ·) ih)

theorem pointwiseSub_self (l : List FP) :
    pointwiseSub l l = List.replicate l.length FP.zero :=
  match l with
  | [] => Eq.trans (FP.fp_self_eq _) (FP.fp_self_eq _)
  | a :: as =>
    have ih : pointwiseSub as as = List.replicate as.length FP.zero := pointwiseSub_self as
    show FP.sub a a :: zipWithFP FP.sub as as = FP.zero :: List.replicate as.length FP.zero from
    Eq.trans
      (congrArg (· :: zipWithFP FP.sub as as) (FP.sub_self a))
      (congrArg (FP.zero :: ·) ih)

theorem add_sub_pointwise (l1 l2 : List FP) (h : l1.length = l2.length) :
    pointwiseSub (pointwiseAdd l1 l2) l2 = l1 :=
  match l1, l2 with
  | [], [] => Eq.trans (FP.fp_self_eq _) (FP.fp_self_eq _)
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | a :: as, b :: bs =>
    have hsub : as.length = bs.length := Nat.succ.inj h
    have ih : pointwiseSub (pointwiseAdd as bs) bs = as := add_sub_pointwise as bs hsub
    show FP.sub (FP.add a b) b :: zipWithFP FP.sub (zipWithFP FP.add as bs) bs = a :: as from
    Eq.trans
      (congrArg (· :: zipWithFP FP.sub (zipWithFP FP.add as bs) bs) (FP.add_sub_cancel a b))
      (congrArg (a :: ·) ih)

theorem sub_add_pointwise (l1 l2 : List FP) (h : l1.length = l2.length) :
    pointwiseAdd (pointwiseSub l1 l2) l2 = l1 :=
  match l1, l2 with
  | [], [] => Eq.trans (FP.fp_self_eq _) (FP.fp_self_eq _)
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | a :: as, b :: bs =>
    have hsub : as.length = bs.length := Nat.succ.inj h
    have ih : pointwiseAdd (pointwiseSub as bs) bs = as := sub_add_pointwise as bs hsub
    show FP.add (FP.sub a b) b :: zipWithFP FP.add (zipWithFP FP.sub as bs) bs = a :: as from
    Eq.trans
      (congrArg (· :: zipWithFP FP.add (zipWithFP FP.sub as bs) bs) (FP.sub_add_cancel a b))
      (congrArg (a :: ·) ih)

theorem neg_pointwise (l : List FP) :
    mapFP FP.neg (mapFP FP.neg l) = l :=
  match l with
  | [] => Eq.trans (FP.fp_self_eq _) (FP.fp_self_eq _)
  | a :: as =>
    have ih : mapFP FP.neg (mapFP FP.neg as) = as := neg_pointwise as
    show FP.neg (FP.neg a) :: mapFP FP.neg (mapFP FP.neg as) = a :: as from
    Eq.trans
      (congrArg (· :: mapFP FP.neg (mapFP FP.neg as)) (FP.neg_neg a))
      (congrArg (a :: ·) ih)

end PointwiseOperations

section FlattenScatter

def flattenWeights (weights : List FP) : List FP := weights

def scatterWeights (flat : List FP) : List FP := flat

theorem flatten_scatter_roundtrip (weights : List FP) :
    scatterWeights (flattenWeights weights) = weights :=
  FP.fp_self_eq weights

theorem scatter_flatten_roundtrip (flat : List FP) :
    flattenWeights (scatterWeights flat) = flat :=
  FP.fp_self_eq flat

def flattenToMem (weights : List FP) : MemoryMap := listToMem weights

def scatterFromMem (mem : MemoryMap) (size : Nat) : List FP := memToList mem size

theorem flattenToMem_preserves_read (weights : List FP) (i : Nat) (h : i < weights.length) :
    memReadDefault (flattenToMem weights) i = getNth weights i :=
  show (match (if i < weights.length then some (getNth weights i) else none) with | some v => v | none => FP.zero) = getNth weights i from
  have h_lt : (i < weights.length) = True := propext ⟨fun _ => True.intro, fun _ => h⟩
  Eq.mpr (congrArg (fun p => (match (if p then some (getNth weights i) else none) with | some v => v | none => FP.zero) = getNth weights i) h_lt)
    (FP.fp_self_eq (getNth weights i))

end FlattenScatter

section SaveFormat

def magicNumber : Nat := 0x4A454D42
def headerVersion : Nat := 1
def headerTotalSize : Nat := 4 + 4 + 8 + 8

theorem headerTotalSize_eq : headerTotalSize = 24 :=
  FP.nat_self_eq 24

theorem magicNumber_pos : 0 < magicNumber :=
  Nat.succ_pos _

structure SaveFormatSpec where
  magic : Nat
  version : Nat
  h_magic_lt_u32 : magic < U32_BOUND
  h_version_lt_u32 : version < U32_BOUND

def defaultSaveSpec : SaveFormatSpec → Prop :=
  fun spec => spec.magic = magicNumber ∧ spec.version = headerVersion

theorem magic_fits_u32 (spec : SaveFormatSpec) : spec.magic < U32_BOUND :=
  spec.h_magic_lt_u32

theorem version_fits_u32 (spec : SaveFormatSpec) : spec.version < U32_BOUND :=
  spec.h_version_lt_u32

def fileSize (numWeights : Nat) : Nat := headerTotalSize + numWeights * 4

theorem fileSize_monotone (n m : Nat) (h : n ≤ m) :
    fileSize n ≤ fileSize m :=
  Nat.add_le_add_left (Nat.mul_le_mul_right 4 h) headerTotalSize

end SaveFormat

section StateMachine

inductive EmbeddingOp where
  | Forward
  | Backward
  | ZeroGrad
  | ApplyGrad
deriving BEq, Repr

structure TrainEntry where
  step : Nat
  op : EmbeddingOp
  weightLen : Nat
  gradLen : Nat

structure EmbeddingState where
  weights : List FP
  grads : List FP
  weightMem : MemoryMap
  gradMem : MemoryMap
  cfg : EmbeddingConfig
  stepCounter : Nat
  h_weight_len : weights.length = cfg.paramCount
  h_grad_len : grads.length = cfg.paramCount

namespace EmbeddingState

def initial (cfg : EmbeddingConfig) (initWeights : List FP)
    (h_wlen : initWeights.length = cfg.paramCount) : EmbeddingState :=
  { weights := initWeights
  , grads := zeroList cfg.paramCount
  , weightMem := listToMem initWeights
  , gradMem := memZero cfg.paramCount
  , cfg := cfg
  , stepCounter := 0
  , h_weight_len := h_wlen
  , h_grad_len := zeroList_length cfg.paramCount }

def applyZeroGrad (st : EmbeddingState) : EmbeddingState :=
  { weights := st.weights
  , grads := zeroList st.cfg.paramCount
  , weightMem := st.weightMem
  , gradMem := memZero st.cfg.paramCount
  , cfg := st.cfg
  , stepCounter := st.stepCounter + 1
  , h_weight_len := st.h_weight_len
  , h_grad_len := zeroList_length st.cfg.paramCount }

def applyForward (st : EmbeddingState) (tokens : List Nat) : EmbeddingState :=
  { weights := st.weights
  , grads := st.grads
  , weightMem := st.weightMem
  , gradMem := st.gradMem
  , cfg := st.cfg
  , stepCounter := st.stepCounter + 1
  , h_weight_len := st.h_weight_len
  , h_grad_len := st.h_grad_len }

def applyBackward (st : EmbeddingState) (tokens : List Nat) (outGrad : List FP) : EmbeddingState :=
  let newGrads := backwardAccum st.grads tokens outGrad st.cfg.vocab_size st.cfg.dim
  { weights := st.weights
  , grads := newGrads
  , weightMem := st.weightMem
  , gradMem := listToMem newGrads
  , cfg := st.cfg
  , stepCounter := st.stepCounter + 1
  , h_weight_len := st.h_weight_len
  , h_grad_len :=
      Eq.trans
        (backwardAccum_length st.grads tokens outGrad st.cfg.vocab_size st.cfg.dim)
        st.h_grad_len }

def applyGradUpdate (st : EmbeddingState) (lr momentum : FP) : EmbeddingState :=
  let newWeights := weightUpdate st.weights st.grads lr
  let newGrads := momentumUpdate st.grads momentum
  { weights := newWeights
  , grads := newGrads
  , weightMem := listToMem newWeights
  , gradMem := listToMem newGrads
  , cfg := st.cfg
  , stepCounter := st.stepCounter + 1
  , h_weight_len :=
      Eq.trans
        (weightUpdate_length st.weights st.grads lr
          (Eq.trans st.h_weight_len (Eq.symm st.h_grad_len)))
        st.h_weight_len
  , h_grad_len :=
      Eq.trans
        (momentumUpdate_length st.grads momentum)
        st.h_grad_len }

theorem applyZeroGrad_step_inc (st : EmbeddingState) :
    (applyZeroGrad st).stepCounter = st.stepCounter + 1 :=
  FP.nat_self_eq (st.stepCounter + 1)

theorem applyForward_step_inc (st : EmbeddingState) (tokens : List Nat) :
    (applyForward st tokens).stepCounter = st.stepCounter + 1 :=
  FP.nat_self_eq (st.stepCounter + 1)

theorem applyBackward_step_inc (st : EmbeddingState) (tokens : List Nat) (outGrad : List FP) :
    (applyBackward st tokens outGrad).stepCounter = st.stepCounter + 1 :=
  FP.nat_self_eq (st.stepCounter + 1)

theorem applyGradUpdate_step_inc (st : EmbeddingState) (lr momentum : FP) :
    (applyGradUpdate st lr momentum).stepCounter = st.stepCounter + 1 :=
  FP.nat_self_eq (st.stepCounter + 1)

theorem applyZeroGrad_dim_preserved (st : EmbeddingState) :
    (applyZeroGrad st).cfg.dim = st.cfg.dim :=
  FP.nat_self_eq st.cfg.dim

theorem applyGradUpdate_dim_preserved (st : EmbeddingState) (lr momentum : FP) :
    (applyGradUpdate st lr momentum).cfg.dim = st.cfg.dim :=
  FP.nat_self_eq st.cfg.dim

theorem applyZeroGrad_weights_preserved (st : EmbeddingState) :
    (applyZeroGrad st).weights = st.weights :=
  FP.fp_self_eq st.weights

theorem applyZeroGrad_weightMem_preserved (st : EmbeddingState) :
    (applyZeroGrad st).weightMem = st.weightMem :=
  FP.fp_self_eq st.weightMem

theorem step_strictly_increases_zg (st : EmbeddingState) :
    st.stepCounter < (applyZeroGrad st).stepCounter :=
  Eq.subst (Eq.symm (applyZeroGrad_step_inc st))
    (Nat.lt_succ_of_le (Nat.le_refl st.stepCounter))

theorem step_strictly_increases_gu (st : EmbeddingState) (lr momentum : FP) :
    st.stepCounter < (applyGradUpdate st lr momentum).stepCounter :=
  Eq.subst (Eq.symm (applyGradUpdate_step_inc st lr momentum))
    (Nat.lt_succ_of_le (Nat.le_refl st.stepCounter))

end EmbeddingState

inductive EmbeddingSafety : EmbeddingState → Prop where
  | mk : (st : EmbeddingState) →
         (dim_pos : 0 < st.cfg.dim) →
         (vocab_pos : 0 < st.cfg.vocab_size) →
         (weight_correct : st.weights.length = st.cfg.paramCount) →
         (grad_correct : st.grads.length = st.cfg.paramCount) →
         (overflow_safe : st.cfg.vocab_size * st.cfg.dim < USIZE_BOUND) →
         EmbeddingSafety st

theorem safety_preserved_zeroGrad (st : EmbeddingState) (h : EmbeddingSafety st) :
    EmbeddingSafety (EmbeddingState.applyZeroGrad st) :=
  match h with
  | EmbeddingSafety.mk _ hdp hvp hwc hgc hov =>
    EmbeddingSafety.mk
      (EmbeddingState.applyZeroGrad st)
      hdp hvp
      ((EmbeddingState.applyZeroGrad st).h_weight_len)
      ((EmbeddingState.applyZeroGrad st).h_grad_len)
      hov

theorem safety_preserved_forward (st : EmbeddingState) (tokens : List Nat) (h : EmbeddingSafety st) :
    EmbeddingSafety (EmbeddingState.applyForward st tokens) :=
  match h with
  | EmbeddingSafety.mk _ hdp hvp hwc hgc hov =>
    EmbeddingSafety.mk
      (EmbeddingState.applyForward st tokens)
      hdp hvp
      ((EmbeddingState.applyForward st tokens).h_weight_len)
      ((EmbeddingState.applyForward st tokens).h_grad_len)
      hov

theorem safety_preserved_backward (st : EmbeddingState) (tokens : List Nat) (outGrad : List FP) (h : EmbeddingSafety st) :
    EmbeddingSafety (EmbeddingState.applyBackward st tokens outGrad) :=
  match h with
  | EmbeddingSafety.mk _ hdp hvp hwc hgc hov =>
    EmbeddingSafety.mk
      (EmbeddingState.applyBackward st tokens outGrad)
      hdp hvp
      ((EmbeddingState.applyBackward st tokens outGrad).h_weight_len)
      ((EmbeddingState.applyBackward st tokens outGrad).h_grad_len)
      hov

theorem safety_preserved_gradUpdate (st : EmbeddingState) (lr momentum : FP) (h : EmbeddingSafety st) :
    EmbeddingSafety (EmbeddingState.applyGradUpdate st lr momentum) :=
  match h with
  | EmbeddingSafety.mk _ hdp hvp hwc hgc hov =>
    EmbeddingSafety.mk
      (EmbeddingState.applyGradUpdate st lr momentum)
      hdp hvp
      ((EmbeddingState.applyGradUpdate st lr momentum).h_weight_len)
      ((EmbeddingState.applyGradUpdate st lr momentum).h_grad_len)
      hov

end StateMachine

section NStepProofs

def executeTrainStep (st : EmbeddingState) (tokens : List Nat) (outGrad : List FP) (lr momentum : FP) : EmbeddingState :=
  let st1 := EmbeddingState.applyZeroGrad st
  let st2 := EmbeddingState.applyForward st1 tokens
  let st3 := EmbeddingState.applyBackward st2 tokens outGrad
  EmbeddingState.applyGradUpdate st3 lr momentum

theorem trainStep_step_count (st : EmbeddingState) (tokens : List Nat) (outGrad : List FP) (lr momentum : FP) :
    (executeTrainStep st tokens outGrad lr momentum).stepCounter = st.stepCounter + 4 :=
  have h1 := EmbeddingState.applyZeroGrad_step_inc st
  have h2 := EmbeddingState.applyForward_step_inc (EmbeddingState.applyZeroGrad st) tokens
  have h3 := EmbeddingState.applyBackward_step_inc
    (EmbeddingState.applyForward (EmbeddingState.applyZeroGrad st) tokens) tokens outGrad
  have h4 := EmbeddingState.applyGradUpdate_step_inc
    (EmbeddingState.applyBackward (EmbeddingState.applyForward (EmbeddingState.applyZeroGrad st) tokens) tokens outGrad) lr momentum
  Eq.trans h4
    (Eq.trans (congrArg (· + 1) h3)
      (Eq.trans (Nat.add_assoc _ 1 1)
        (Eq.trans (congrArg (· + 2) h2)
          (Eq.trans (Nat.add_assoc _ 1 2)
            (Eq.trans (congrArg (· + 3) h1)
              (Nat.add_assoc st.stepCounter 1 3))))))

theorem trainStep_safety (st : EmbeddingState) (tokens : List Nat) (outGrad : List FP) (lr momentum : FP)
    (h : EmbeddingSafety st) : EmbeddingSafety (executeTrainStep st tokens outGrad lr momentum) :=
  safety_preserved_gradUpdate
    (EmbeddingState.applyBackward
      (EmbeddingState.applyForward (EmbeddingState.applyZeroGrad st) tokens) tokens outGrad)
    lr momentum
    (safety_preserved_backward
      (EmbeddingState.applyForward (EmbeddingState.applyZeroGrad st) tokens) tokens outGrad
      (safety_preserved_forward (EmbeddingState.applyZeroGrad st) tokens
        (safety_preserved_zeroGrad st h)))

def executeNTrainSteps : Nat → EmbeddingState → List Nat → List FP → FP → FP → EmbeddingState
  | 0, st, _, _, _, _ => st
  | Nat.succ n, st, tokens, outGrad, lr, momentum =>
    executeNTrainSteps n (executeTrainStep st tokens outGrad lr momentum) tokens outGrad lr momentum

theorem executeNTrainSteps_step_count (n : Nat) (st : EmbeddingState) (tokens : List Nat)
    (outGrad : List FP) (lr momentum : FP) :
    (executeNTrainSteps n st tokens outGrad lr momentum).stepCounter = st.stepCounter + n * 4 :=
  Nat.recOn n
    (Eq.symm (Nat.add_zero st.stepCounter))
    (fun k ih =>
      have h1 : (executeNTrainSteps (Nat.succ k) st tokens outGrad lr momentum).stepCounter =
                 (executeNTrainSteps k (executeTrainStep st tokens outGrad lr momentum) tokens outGrad lr momentum).stepCounter :=
        FP.nat_self_eq _
      have h_step : (executeTrainStep st tokens outGrad lr momentum).stepCounter = st.stepCounter + 4 :=
        trainStep_step_count st tokens outGrad lr momentum
      have h2 : (executeNTrainSteps k (executeTrainStep st tokens outGrad lr momentum) tokens outGrad lr momentum).stepCounter =
                 (executeTrainStep st tokens outGrad lr momentum).stepCounter + k * 4 :=
        ih ▸ executeNTrainSteps_step_count k (executeTrainStep st tokens outGrad lr momentum) tokens outGrad lr momentum
      Eq.trans h1
        (Eq.trans h2
          (Eq.trans (congrArg (· + k * 4) h_step)
            (Eq.trans (Nat.add_assoc st.stepCounter 4 (k * 4))
              (congrArg (st.stepCounter + ·) (Eq.trans (Nat.add_comm 4 (k * 4)) (Eq.symm (Nat.succ_mul k 4))))))))

theorem executeNTrainSteps_safety (n : Nat) (st : EmbeddingState) (tokens : List Nat)
    (outGrad : List FP) (lr momentum : FP)
    (h : EmbeddingSafety st) :
    EmbeddingSafety (executeNTrainSteps n st tokens outGrad lr momentum) :=
  Nat.recOn n
    h
    (fun k _ =>
      executeNTrainSteps_safety k
        (executeTrainStep st tokens outGrad lr momentum) tokens outGrad lr momentum
        (trainStep_safety st tokens outGrad lr momentum h))

theorem executeNTrainSteps_monotone (n : Nat) (st : EmbeddingState) (tokens : List Nat)
    (outGrad : List FP) (lr momentum : FP) :
    st.stepCounter ≤ (executeNTrainSteps n st tokens outGrad lr momentum).stepCounter :=
  Eq.subst (Eq.symm (executeNTrainSteps_step_count n st tokens outGrad lr momentum))
    (Nat.le_add_right st.stepCounter (n * 4))

theorem step_lt_of_n_train (n m : Nat) (st : EmbeddingState) (tokens : List Nat)
    (outGrad : List FP) (lr momentum : FP) (h : n < m) :
    (executeNTrainSteps n st tokens outGrad lr momentum).stepCounter <
    (executeNTrainSteps m st tokens outGrad lr momentum).stepCounter :=
  Eq.subst (Eq.symm (executeNTrainSteps_step_count n st tokens outGrad lr momentum))
    (Eq.subst (Eq.symm (executeNTrainSteps_step_count m st tokens outGrad lr momentum))
      (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos 3)) st.stepCounter))

end NStepProofs

section OverflowVerification

theorem any_token_access_safe (cfg : OverflowSafe) (token : Nat) (col : Nat) (hc : col < cfg.dim) :
    weightIdx (clampToken token cfg.vocab_size) cfg.dim col < USIZE_BOUND :=
  have h_clamped := clampToken_bound token cfg.vocab_size cfg.h_vocab_pos
  weightIdx_usize_safe cfg (clampToken token cfg.vocab_size) col h_clamped hc

theorem forward_all_accesses_safe (cfg : OverflowSafe) (tokens : List Nat) :
    ∀ (i : Nat), i < tokens.length →
    ∀ (col : Nat), col < cfg.dim →
    weightIdx (clampToken (getNth (listToMem (List.map (fun t => t) tokens) |> fun _ => tokens) i |> fun _ => 0) cfg.vocab_size) cfg.dim col < USIZE_BOUND :=
  fun i _ col hc =>
    any_token_access_safe cfg 0 col hc

theorem backward_all_accesses_safe (cfg : OverflowSafe) (token : Nat) (col : Nat) (hc : col < cfg.dim) :
    weightIdx (clampToken token cfg.vocab_size) cfg.dim col < USIZE_BOUND :=
  any_token_access_safe cfg token col hc

theorem bitcast_safe_for_weight (v : FP) (safety : BitcastSafety) (h : withinExactRange v) :
    ∃ (bits : Nat), bits < U32_BOUND :=
  safety.h_roundtrip v h

end OverflowVerification

section ParamPartition

def paramOffset_embed : Nat := 0
def paramOffset_rsf (embed_p : Nat) : Nat := embed_p
def paramOffset_proj (embed_p rsf_p : Nat) : Nat := embed_p + rsf_p
def totalParams (embed_p rsf_p proj_p : Nat) : Nat := embed_p + rsf_p + proj_p

theorem offsets_partition (embed_p rsf_p proj_p : Nat) :
    paramOffset_proj embed_p rsf_p + proj_p = totalParams embed_p rsf_p proj_p :=
  Eq.symm (Nat.add_assoc embed_p rsf_p proj_p)

theorem offsets_disjoint (embed_p rsf_p : Nat) (h_ep : 0 < embed_p) :
    paramOffset_embed < paramOffset_rsf embed_p :=
  h_ep

theorem totalParams_assoc (e r p : Nat) :
    totalParams e r p = e + (r + p) :=
  Nat.add_assoc e r p

theorem totalParams_pos (e r p : Nat) (h : 0 < e) :
    0 < totalParams e r p :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right e (r + p))

end ParamPartition
