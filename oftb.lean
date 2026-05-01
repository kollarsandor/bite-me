```lean
import Std.Data.Nat.Basic
import Std.Data.List.Basic

namespace ZigOFTB

structure F32Ops where
  F32 : Type
  lit70710678 : F32
  lit05 : F32
  undefined : F32
  add : F32 → F32 → F32
  mul : F32 → F32 → F32

structure FixedBuffer16384 (α : Type) where
  get : Fin 16384 → α

def FixedBuffer16384.set (α : Type) (buf : FixedBuffer16384 α)
    (i : Fin 16384) (v : α) : FixedBuffer16384 α :=
  { get := fun j => if j = i then v else buf.get j }

def FixedBuffer16384.ofUndefined (ops : F32Ops) : FixedBuffer16384 ops.F32 :=
  { get := fun _ => ops.undefined }

theorem FixedBuffer16384.get_set_eq (α : Type) (buf : FixedBuffer16384 α)
    (i : Fin 16384) (v : α) :
    (FixedBuffer16384.set α buf i v).get i = v :=
  show (if i = i then v else buf.get i) = v from
    match (Nat.decEq i.val i.val) with
    | Decidable.isTrue h  => Eq.refl v
    | Decidable.isFalse h => False.elim (h (Eq.refl i.val))

theorem FixedBuffer16384.get_set_ne (α : Type) (buf : FixedBuffer16384 α)
    (i j : Fin 16384) (h : i ≠ j) (v : α) :
    (FixedBuffer16384.set α buf i v).get j = buf.get j :=
  show (if j = i then v else buf.get j) = buf.get j from
    match (Nat.decEq j.val i.val) with
    | Decidable.isTrue heq =>
        False.elim (h (Fin.eq_of_val_eq heq))
    | Decidable.isFalse _  => Eq.refl (buf.get j)

def mkBufIndex (i : Nat) (h : i < 16384) : Fin 16384 :=
  Fin.mk i h

def boolNot : Bool → Bool
| true => false
| false => true

def boolAnd : Bool → Bool → Bool
| true, b => b
| false, _ => false

def boolOr : Bool → Bool → Bool
| true, _ => true
| false, b => b

theorem boolNot_true : boolNot true = false := Eq.refl false

theorem boolNot_false : boolNot false = true := Eq.refl true

theorem boolAnd_true_left (b : Bool) : boolAnd true b = b := Eq.refl b

theorem boolAnd_false_left (b : Bool) : boolAnd false b = false := Eq.refl false

theorem boolAnd_true_true : boolAnd true true = true := Eq.refl true

theorem boolAnd_true_false : boolAnd true false = false := Eq.refl false

theorem boolAnd_false_true : boolAnd false true = false := Eq.refl false

theorem boolAnd_false_false : boolAnd false false = false := Eq.refl false

theorem boolOr_true_left (b : Bool) : boolOr true b = true := Eq.refl true

theorem boolOr_false_left (b : Bool) : boolOr false b = b := Eq.refl b

theorem boolOr_true_true : boolOr true true = true := Eq.refl true

theorem boolOr_true_false : boolOr true false = true := Eq.refl true

theorem boolOr_false_true : boolOr false true = true := Eq.refl true

theorem boolOr_false_false : boolOr false false = false := Eq.refl false

theorem boolFalseNeTrue (h : false = true) : False :=
  @Eq.rec Bool false (fun x _ => if x then False else True) True.intro true h

def natLeBool : Nat → Nat → Bool
| 0, _ => true
| Nat.succ _, 0 => false
| Nat.succ a, Nat.succ b => natLeBool a b

def natLtBool (a b : Nat) : Bool := natLeBool (Nat.succ a) b

theorem natLeBool_zero_left (n : Nat) : natLeBool 0 n = true := Eq.refl true

theorem natLeBool_succ_zero (n : Nat) : natLeBool (Nat.succ n) 0 = false := Eq.refl false

theorem natLeBool_succ_succ (a b : Nat) : natLeBool (Nat.succ a) (Nat.succ b) = natLeBool a b := Eq.refl (natLeBool a b)

theorem natLtBool_def (a b : Nat) : natLtBool a b = natLeBool (Nat.succ a) b := Eq.refl (natLeBool (Nat.succ a) b)

theorem natLeBool_refl (n : Nat) : natLeBool n n = true :=
match n with
| 0 => Eq.refl true
| Nat.succ k => natLeBool_refl k

theorem natLeBool_left_add_right (n m : Nat) : natLeBool n (n + m) = true :=
match n with
| 0 => Eq.refl true
| Nat.succ k => natLeBool_left_add_right k m

theorem natLeBool_true_trans (a b c : Nat) (hab : natLeBool a b = true) (hbc : natLeBool b c = true) : natLeBool a c = true :=
match a with
| 0 => Eq.refl true
| Nat.succ a1 =>
  match b with
  | 0 => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (natLeBool_succ_zero a1)) hab))
  | Nat.succ b1 =>
    match c with
    | 0 => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (natLeBool_succ_zero b1)) hbc))
    | Nat.succ c1 => natLeBool_true_trans a1 b1 c1 (Eq.trans (natLeBool_succ_succ a1 b1) hab) (Eq.trans (natLeBool_succ_succ b1 c1) hbc)

def mixBufferLen : Nat := 16384

def usizeMax : Nat := 18446744073709551615

def doubleNat (n : Nat) : Nat := n + n

def usizeFits (n : Nat) : Bool := natLeBool n usizeMax

def usizeDoubleFits (n : Nat) : Bool := usizeFits (doubleNat n)

def lenEnough (dim len : Nat) : Bool := natLeBool (doubleNat dim) len

def bufferFits (dim : Nat) : Bool := natLeBool dim mixBufferLen

theorem mixBufferLen_def : mixBufferLen = 16384 := Eq.refl 16384

theorem usizeMax_def : usizeMax = 18446744073709551615 := Eq.refl 18446744073709551615

theorem doubleNat_def (n : Nat) : doubleNat n = n + n := Eq.refl (n + n)

theorem usizeFits_def (n : Nat) : usizeFits n = natLeBool n usizeMax := Eq.refl (natLeBool n usizeMax)

theorem usizeDoubleFits_def (n : Nat) : usizeDoubleFits n = usizeFits (doubleNat n) := Eq.refl (usizeFits (doubleNat n))

theorem lenEnough_def (dim len : Nat) : lenEnough dim len = natLeBool (doubleNat dim) len := Eq.refl (natLeBool (doubleNat dim) len)

theorem bufferFits_def (dim : Nat) : bufferFits dim = natLeBool dim mixBufferLen := Eq.refl (natLeBool dim mixBufferLen)

theorem lenEnough_zero (len : Nat) : lenEnough 0 len = true := natLeBool_zero_left len

theorem bufferFits_zero : bufferFits 0 = true := Eq.refl true

structure SliceDescriptor where
  start : Nat
  len : Nat

def sliceStop (s : SliceDescriptor) : Nat := s.start + s.len

def sliceValidIn (s : SliceDescriptor) (total : Nat) : Bool := natLeBool (sliceStop s) total

def firstSlice (dim : Nat) : SliceDescriptor := { start := 0, len := dim }

def secondSlice (dim : Nat) : SliceDescriptor := { start := dim, len := dim }

theorem firstSlice_start (dim : Nat) : (firstSlice dim).start = 0 := Eq.refl 0

theorem firstSlice_len (dim : Nat) : (firstSlice dim).len = dim := Eq.refl dim

theorem secondSlice_start (dim : Nat) : (secondSlice dim).start = dim := Eq.refl dim

theorem secondSlice_len (dim : Nat) : (secondSlice dim).len = dim := Eq.refl dim

theorem firstSlice_stop (dim : Nat) : sliceStop (firstSlice dim) = dim := Eq.refl dim

theorem secondSlice_stop (dim : Nat) : sliceStop (secondSlice dim) = doubleNat dim := Eq.refl (dim + dim)

theorem secondSlice_valid_eq_lenEnough (dim len : Nat) : sliceValidIn (secondSlice dim) len = lenEnough dim len := Eq.refl (natLeBool (dim + dim) len)

theorem firstSlice_valid_of_lenEnough (dim len : Nat) (h : lenEnough dim len = true) : sliceValidIn (firstSlice dim) len = true :=
natLeBool_true_trans dim (doubleNat dim) len (natLeBool_left_add_right dim dim) h

theorem secondSlice_valid_of_lenEnough (dim len : Nat) (h : lenEnough dim len = true) : sliceValidIn (secondSlice dim) len = true := h

def f32Scale (ops : F32Ops) : ops.F32 := ops.lit70710678

def f32Half (ops : F32Ops) : ops.F32 := ops.lit05

def f32Undefined (ops : F32Ops) : ops.F32 := ops.undefined

def f32Add (ops : F32Ops) (a b : ops.F32) : ops.F32 := ops.add a b

def f32Mul (ops : F32Ops) (a b : ops.F32) : ops.F32 := ops.mul a b

def f32MulScale (ops : F32Ops) (value scale : ops.F32) : ops.F32 := f32Mul ops value scale

def f32MulScaleHalf (ops : F32Ops) (value scale : ops.F32) : ops.F32 := f32Mul ops (f32Mul ops value scale) (f32Half ops)

theorem f32Scale_def (ops : F32Ops) : f32Scale ops = ops.lit70710678 := Eq.refl ops.lit70710678

theorem f32Half_def (ops : F32Ops) : f32Half ops = ops.lit05 := Eq.refl ops.lit05

theorem f32Undefined_def (ops : F32Ops) : f32Undefined ops = ops.undefined := Eq.refl ops.undefined

theorem f32Add_def (ops : F32Ops) (a b : ops.F32) : f32Add ops a b = ops.add a b := Eq.refl (ops.add a b)

theorem f32Mul_def (ops : F32Ops) (a b : ops.F32) : f32Mul ops a b = ops.mul a b := Eq.refl (ops.mul a b)

theorem f32MulScale_def (ops : F32Ops) (value scale : ops.F32) : f32MulScale ops value scale = f32Mul ops value scale := Eq.refl (f32Mul ops value scale)

theorem f32MulScaleHalf_def (ops : F32Ops) (value scale : ops.F32) : f32MulScaleHalf ops value scale = f32Mul ops (f32Mul ops value scale) (f32Half ops) := Eq.refl (f32Mul ops (f32Mul ops value scale) (f32Half ops))

def repeatN {α : Type} (value : α) : Nat → List α
| 0 => []
| Nat.succ n => value :: repeatN value n

theorem repeatN_zero {α : Type} (value : α) : repeatN value 0 = [] := Eq.refl []

theorem repeatN_succ {α : Type} (value : α) (n : Nat) : repeatN value (Nat.succ n) = value :: repeatN value n := Eq.refl (value :: repeatN value n)

theorem repeatN_length {α : Type} (value : α) (n : Nat) : (repeatN value n).length = n :=
match n with
| 0 => Eq.refl 0
| Nat.succ k => congrArg Nat.succ (repeatN_length value k)

def getD {α : Type} (fallback : α) : List α → Nat → α
| [], _ => fallback
| x :: xs, 0 => x
| x :: xs, Nat.succ n => getD fallback xs n

theorem getD_nil {α : Type} (fallback : α) (i : Nat) : getD fallback ([] : List α) i = fallback :=
match i with
| 0 => Eq.refl fallback
| Nat.succ k => Eq.refl fallback

theorem getD_cons_zero {α : Type} (fallback x : α) (xs : List α) : getD fallback (x :: xs) 0 = x := Eq.refl x

theorem getD_cons_succ {α : Type} (fallback x : α) (xs : List α) (i : Nat) : getD fallback (x :: xs) (Nat.succ i) = getD fallback xs i := Eq.refl (getD fallback xs i)

def setAt {α : Type} : List α → Nat → α → List α
| [], _, _ => []
| _ :: xs, 0, value => value :: xs
| x :: xs, Nat.succ i, value => x :: setAt xs i value

theorem setAt_nil {α : Type} (i : Nat) (value : α) : setAt ([] : List α) i value = [] :=
match i with
| 0 => Eq.refl []
| Nat.succ k => Eq.refl []

theorem setAt_cons_zero {α : Type} (x value : α) (xs : List α) : setAt (x :: xs) 0 value = value :: xs := Eq.refl (value :: xs)

theorem setAt_cons_succ {α : Type} (x value : α) (xs : List α) (i : Nat) : setAt (x :: xs) (Nat.succ i) value = x :: setAt xs i value := Eq.refl (x :: setAt xs i value)

theorem setAt_length {α : Type} (xs : List α) (i : Nat) (value : α) : (setAt xs i value).length = xs.length :=
match xs with
| [] => match i with | 0 => Eq.refl 0 | Nat.succ k => Eq.refl 0
| x :: rest => match i with | 0 => Eq.refl (Nat.succ rest.length) | Nat.succ k => congrArg Nat.succ (setAt_length rest k value)

theorem getD_setAt_head_zero {α : Type} (fallback x value : α) (xs : List α) : getD fallback (setAt (x :: xs) 0 value) 0 = value := Eq.refl value

theorem getD_setAt_tail_succ {α : Type} (fallback x value : α) (xs : List α) (i j : Nat) : getD fallback (setAt (x :: xs) (Nat.succ i) value) (Nat.succ j) = getD fallback (setAt xs i value) j := Eq.refl (getD fallback (setAt xs i value) j)

def sliceRead (ops : F32Ops) (data : List ops.F32) (s : SliceDescriptor) (i : Nat) : ops.F32 := getD ops.undefined data (s.start + i)

def sliceWrite (ops : F32Ops) (data : List ops.F32) (s : SliceDescriptor) (i : Nat) (value : ops.F32) : List ops.F32 := setAt data (s.start + i) value

theorem sliceRead_first (ops : F32Ops) (data : List ops.F32) (dim i : Nat) : sliceRead ops data (firstSlice dim) i = getD ops.undefined data i := Eq.refl (getD ops.undefined data i)

theorem sliceRead_second (ops : F32Ops) (data : List ops.F32) (dim i : Nat) : sliceRead ops data (secondSlice dim) i = getD ops.undefined data (dim + i) := Eq.refl (getD ops.undefined data (dim + i))

theorem sliceWrite_first (ops : F32Ops) (data : List ops.F32) (dim i : Nat) (value : ops.F32) : sliceWrite ops data (firstSlice dim) i value = setAt data i value := Eq.refl (setAt data i value)

theorem sliceWrite_second (ops : F32Ops) (data : List ops.F32) (dim i : Nat) (value : ops.F32) : sliceWrite ops data (secondSlice dim) i value = setAt data (dim + i) value := Eq.refl (setAt data (dim + i) value)

theorem sliceWrite_length (ops : F32Ops) (data : List ops.F32) (s : SliceDescriptor) (i : Nat) (value : ops.F32) : (sliceWrite ops data s i value).length = data.length := setAt_length data (s.start + i) value

structure Tensor (ops : F32Ops) where
  data : List ops.F32

namespace Tensor

def dataList (ops : F32Ops) (t : Tensor ops) : List ops.F32 := t.data

def dataLength (ops : F32Ops) (t : Tensor ops) : Nat := t.data.length

def validBool (ops : F32Ops) (t : Tensor ops) : Bool := usizeFits t.data.length

def Valid (ops : F32Ops) (t : Tensor ops) : Prop := validBool ops t = true

def read (ops : F32Ops) (t : Tensor ops) (i : Nat) : ops.F32 := getD ops.undefined t.data i

def write (ops : F32Ops) (t : Tensor ops) (i : Nat) (value : ops.F32) : Tensor ops := { data := setAt t.data i value }

theorem dataList_def (ops : F32Ops) (t : Tensor ops) : dataList ops t = t.data := Eq.refl t.data

theorem dataLength_def (ops : F32Ops) (t : Tensor ops) : dataLength ops t = t.data.length := Eq.refl t.data.length

theorem validBool_def (ops : F32Ops) (t : Tensor ops) : validBool ops t = usizeFits t.data.length := Eq.refl (usizeFits t.data.length)

theorem valid_of_bool (ops : F32Ops) (t : Tensor ops) (h : validBool ops t = true) : Valid ops t := h

theorem constructor_data (ops : F32Ops) (data : List ops.F32) : (Tensor.mk data).data = data := Eq.refl data

theorem constructor_valid_of_length (ops : F32Ops) (data : List ops.F32) (h : usizeFits data.length = true) : Valid ops { data := data } := h

theorem read_def (ops : F32Ops) (t : Tensor ops) (i : Nat) : read ops t i = getD ops.undefined t.data i := Eq.refl (getD ops.undefined t.data i)

theorem write_data (ops : F32Ops) (t : Tensor ops) (i : Nat) (value : ops.F32) : (write ops t i value).data = setAt t.data i value := Eq.refl (setAt t.data i value)

theorem write_length (ops : F32Ops) (t : Tensor ops) (i : Nat) (value : ops.F32) : (write ops t i value).data.length = t.data.length := setAt_length t.data i value

theorem write_validBool (ops : F32Ops) (t : Tensor ops) (i : Nat) (value : ops.F32) : validBool ops (write ops t i value) = validBool ops t := congrArg usizeFits (write_length ops t i value)

end Tensor

structure OFTB (ops : F32Ops) where
  fractal_scale : ops.F32
  dim : Nat

namespace OFTB

def init (ops : F32Ops) (d : Nat) : OFTB ops := { fractal_scale := f32Scale ops, dim := d }

def scale (ops : F32Ops) (self : OFTB ops) : ops.F32 := self.fractal_scale

def dimension (ops : F32Ops) (self : OFTB ops) : Nat := self.dim

def validBool (ops : F32Ops) (self : OFTB ops) : Bool := usizeFits self.dim

def Valid (ops : F32Ops) (self : OFTB ops) : Prop := validBool ops self = true

def doubledDimension (ops : F32Ops) (self : OFTB ops) : Nat := doubleNat self.dim

def arithmeticSafeBool (ops : F32Ops) (self : OFTB ops) : Bool := usizeDoubleFits self.dim

def lenEnoughFor (ops : F32Ops) (self : OFTB ops) (len : Nat) : Bool := lenEnough self.dim len

def bufferFitsSelf (ops : F32Ops) (self : OFTB ops) : Bool := bufferFits self.dim

theorem init_scale (ops : F32Ops) (d : Nat) : (init ops d).fractal_scale = f32Scale ops := Eq.refl (f32Scale ops)

theorem init_scale_literal (ops : F32Ops) (d : Nat) : (init ops d).fractal_scale = ops.lit70710678 := Eq.refl ops.lit70710678

theorem init_dim (ops : F32Ops) (d : Nat) : (init ops d).dim = d := Eq.refl d

theorem scale_def (ops : F32Ops) (self : OFTB ops) : scale ops self = self.fractal_scale := Eq.refl self.fractal_scale

theorem dimension_def (ops : F32Ops) (self : OFTB ops) : dimension ops self = self.dim := Eq.refl self.dim

theorem validBool_def (ops : F32Ops) (self : OFTB ops) : validBool ops self = usizeFits self.dim := Eq.refl (usizeFits self.dim)

theorem valid_of_bool (ops : F32Ops) (self : OFTB ops) (h : validBool ops self = true) : Valid ops self := h

theorem init_valid_of_usize (ops : F32Ops) (d : Nat) (h : usizeFits d = true) : Valid ops (init ops d) := h

theorem doubledDimension_def (ops : F32Ops) (self : OFTB ops) : doubledDimension ops self = doubleNat self.dim := Eq.refl (doubleNat self.dim)

theorem arithmeticSafeBool_def (ops : F32Ops) (self : OFTB ops) : arithmeticSafeBool ops self = usizeDoubleFits self.dim := Eq.refl (usizeDoubleFits self.dim)

theorem lenEnoughFor_def (ops : F32Ops) (self : OFTB ops) (len : Nat) : lenEnoughFor ops self len = lenEnough self.dim len := Eq.refl (lenEnough self.dim len)

theorem bufferFitsSelf_def (ops : F32Ops) (self : OFTB ops) : bufferFitsSelf ops self = bufferFits self.dim := Eq.refl (bufferFits self.dim)

end OFTB

def emptyBuffer (ops : F32Ops) : List ops.F32 := repeatN ops.undefined mixBufferLen

theorem emptyBuffer_length (ops : F32Ops) : (emptyBuffer ops).length = mixBufferLen := repeatN_length ops.undefined mixBufferLen

def copyToBufferLoop (ops : F32Ops) (source : List ops.F32) (sourceBase : Nat) (buffer : List ops.F32) (dest : Nat) (count : Nat) : List ops.F32 :=
match count with
| 0 => buffer
| Nat.succ rest =>
  let value := getD ops.undefined source (sourceBase + dest)
  let bufferNext := setAt buffer dest value
  copyToBufferLoop ops source sourceBase bufferNext (Nat.succ dest) rest

theorem copyToBufferLoop_zero (ops : F32Ops) (source : List ops.F32) (sourceBase : Nat) (buffer : List ops.F32) (dest : Nat) : copyToBufferLoop ops source sourceBase buffer dest 0 = buffer := Eq.refl buffer

theorem copyToBufferLoop_succ (ops : F32Ops) (source : List ops.F32) (sourceBase : Nat) (buffer : List ops.F32) (dest count : Nat) : copyToBufferLoop ops source sourceBase buffer dest (Nat.succ count) = copyToBufferLoop ops source sourceBase (setAt buffer dest (getD ops.undefined source (sourceBase + dest))) (Nat.succ dest) count := Eq.refl (copyToBufferLoop ops source sourceBase (setAt buffer dest (getD ops.undefined source (sourceBase + dest))) (Nat.succ dest) count)

theorem copyToBufferLoop_length (ops : F32Ops) (source : List ops.F32) (sourceBase : Nat) (buffer : List ops.F32) (dest : Nat) (count : Nat) : (copyToBufferLoop ops source sourceBase buffer dest count).length = buffer.length :=
match count with
| 0 => Eq.refl buffer.length
| Nat.succ rest => Eq.trans (copyToBufferLoop_length ops source sourceBase (setAt buffer dest (getD ops.undefined source (sourceBase + dest))) (Nat.succ dest) rest) (setAt_length buffer dest (getD ops.undefined source (sourceBase + dest)))

def copyToFixedBuffer (ops : F32Ops)
    (source : List ops.F32) (sourceBase : Nat)
    (buf : FixedBuffer16384 ops.F32)
    (dest : Nat) (count : Nat) : FixedBuffer16384 ops.F32 :=
  match count with
  | 0           => buf
  | Nat.succ rest =>
    match Nat.decLt dest 16384 with
    | Decidable.isTrue  h =>
      let idx   := mkBufIndex dest h
      let value := getD ops.undefined source (sourceBase + dest)
      let buf'  := FixedBuffer16384.set ops.F32 buf idx value
      copyToFixedBuffer ops source sourceBase buf' (Nat.succ dest) rest
    | Decidable.isFalse _ => buf

theorem copyToFixedBuffer_zero
    (ops : F32Ops) (source : List ops.F32) (sourceBase : Nat)
    (buf : FixedBuffer16384 ops.F32) (dest : Nat) :
    copyToFixedBuffer ops source sourceBase buf dest 0 = buf :=
  Eq.refl buf

theorem copyToFixedBuffer_succ_inbounds
    (ops : F32Ops) (source : List ops.F32) (sourceBase : Nat)
    (buf : FixedBuffer16384 ops.F32) (dest count : Nat)
    (h : dest < 16384) :
    copyToFixedBuffer ops source sourceBase buf dest (Nat.succ count) =
    copyToFixedBuffer ops source sourceBase
      (FixedBuffer16384.set ops.F32 buf (mkBufIndex dest h)
        (getD ops.undefined source (sourceBase + dest)))
      (Nat.succ dest) count :=
  match (Nat.decLt dest 16384) with
  | Decidable.isTrue  h' =>
      show copyToFixedBuffer ops source sourceBase
             (FixedBuffer16384.set ops.F32 buf (mkBufIndex dest h') _)
             (Nat.succ dest) count =
           copyToFixedBuffer ops source sourceBase
             (FixedBuffer16384.set ops.F32 buf (mkBufIndex dest h) _)
             (Nat.succ dest) count from
        congrArg
          (fun idx => copyToFixedBuffer ops source sourceBase
            (FixedBuffer16384.set ops.F32 buf idx
              (getD ops.undefined source (sourceBase + dest)))
            (Nat.succ dest) count)
          (Fin.eq_of_val_eq (Eq.refl dest))
  | Decidable.isFalse hf => False.elim (hf h)

def forwardFirstValue (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) : ops.F32 := f32Add ops (getD ops.undefined data index) (f32Mul ops (getD ops.undefined data (half + index)) scale)

theorem forwardFirstValue_def (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) : forwardFirstValue ops scale half data index = f32Add ops (getD ops.undefined data index) (f32Mul ops (getD ops.undefined data (half + index)) scale) := Eq.refl (f32Add ops (getD ops.undefined data index) (f32Mul ops (getD ops.undefined data (half + index)) scale))

def forwardFirstLoop (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) (count : Nat) : List ops.F32 :=
match count with
| 0 => data
| Nat.succ rest =>
  let value := forwardFirstValue ops scale half data index
  let dataNext := setAt data index value
  forwardFirstLoop ops scale half dataNext (Nat.succ index) rest

theorem forwardFirstLoop_zero (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) : forwardFirstLoop ops scale half data index 0 = data := Eq.refl data

theorem forwardFirstLoop_succ (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index count : Nat) : forwardFirstLoop ops scale half data index (Nat.succ count) = forwardFirstLoop ops scale half (setAt data index (forwardFirstValue ops scale half data index)) (Nat.succ index) count := Eq.refl (forwardFirstLoop ops scale half (setAt data index (forwardFirstValue ops scale half data index)) (Nat.succ index) count)

theorem forwardFirstLoop_length (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) (count : Nat) : (forwardFirstLoop ops scale half data index count).length = data.length :=
match count with
| 0 => Eq.refl data.length
| Nat.succ rest => Eq.trans (forwardFirstLoop_length ops scale half (setAt data index (forwardFirstValue ops scale half data index)) (Nat.succ index) rest) (setAt_length data index (forwardFirstValue ops scale half data index))

def forwardSecondValue (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer : List ops.F32) (data : List ops.F32) (index : Nat) : ops.F32 := f32Add ops (getD ops.undefined data (half + index)) (f32MulScaleHalf ops (getD ops.undefined buffer index) scale)

theorem forwardSecondValue_def (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer data : List ops.F32) (index : Nat) : forwardSecondValue ops scale half buffer data index = f32Add ops (getD ops.undefined data (half + index)) (f32MulScaleHalf ops (getD ops.undefined buffer index) scale) := Eq.refl (f32Add ops (getD ops.undefined data (half + index)) (f32MulScaleHalf ops (getD ops.undefined buffer index) scale))

def forwardSecondLoop (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer : List ops.F32) (data : List ops.F32) (index : Nat) (count : Nat) : List ops.F32 :=
match count with
| 0 => data
| Nat.succ rest =>
  let value := forwardSecondValue ops scale half buffer data index
  let dataNext := setAt data (half + index) value
  forwardSecondLoop ops scale half buffer dataNext (Nat.succ index) rest

theorem forwardSecondLoop_zero (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer data : List ops.F32) (index : Nat) : forwardSecondLoop ops scale half buffer data index 0 = data := Eq.refl data

theorem forwardSecondLoop_succ (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer data : List ops.F32) (index count : Nat) : forwardSecondLoop ops scale half buffer data index (Nat.succ count) = forwardSecondLoop ops scale half buffer (setAt data (half + index) (forwardSecondValue ops scale half buffer data index)) (Nat.succ index) count := Eq.refl (forwardSecondLoop ops scale half buffer (setAt data (half + index) (forwardSecondValue ops scale half buffer data index)) (Nat.succ index) count)

theorem forwardSecondLoop_length (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer data : List ops.F32) (index : Nat) (count : Nat) : (forwardSecondLoop ops scale half buffer data index count).length = data.length :=
match count with
| 0 => Eq.refl data.length
| Nat.succ rest => Eq.trans (forwardSecondLoop_length ops scale half buffer (setAt data (half + index) (forwardSecondValue ops scale half buffer data index)) (Nat.succ index) rest) (setAt_length data (half + index) (forwardSecondValue ops scale half buffer data index))

def backwardSecondValue (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) : ops.F32 := f32Add ops (getD ops.undefined data (half + index)) (f32Mul ops (getD ops.undefined data index) scale)

theorem backwardSecondValue_def (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) : backwardSecondValue ops scale half data index = f32Add ops (getD ops.undefined data (half + index)) (f32Mul ops (getD ops.undefined data index) scale) := Eq.refl (f32Add ops (getD ops.undefined data (half + index)) (f32Mul ops (getD ops.undefined data index) scale))

def backwardSecondLoop (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) (count : Nat) : List ops.F32 :=
match count with
| 0 => data
| Nat.succ rest =>
  let value := backwardSecondValue ops scale half data index
  let dataNext := setAt data (half + index) value
  backwardSecondLoop ops scale half dataNext (Nat.succ index) rest

theorem backwardSecondLoop_zero (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) : backwardSecondLoop ops scale half data index 0 = data := Eq.refl data

theorem backwardSecondLoop_succ (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index count : Nat) : backwardSecondLoop ops scale half data index (Nat.succ count) = backwardSecondLoop ops scale half (setAt data (half + index) (backwardSecondValue ops scale half data index)) (Nat.succ index) count := Eq.refl (backwardSecondLoop ops scale half (setAt data (half + index) (backwardSecondValue ops scale half data index)) (Nat.succ index) count)

theorem backwardSecondLoop_length (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index : Nat) (count : Nat) : (backwardSecondLoop ops scale half data index count).length = data.length :=
match count with
| 0 => Eq.refl data.length
| Nat.succ rest => Eq.trans (backwardSecondLoop_length ops scale half data (setAt data (half + index) (backwardSecondValue ops scale half data index)) (Nat.succ index) rest) (setAt_length data (half + index) (backwardSecondValue ops scale half data index))

def backwardFirstValue (ops : F32Ops) (scale : ops.F32) (buffer : List ops.F32) (data : List ops.F32) (index : Nat) : ops.F32 := f32Add ops (getD ops.undefined data index) (f32MulScaleHalf ops (getD ops.undefined buffer index) scale)

theorem backwardFirstValue_def (ops : F32Ops) (scale : ops.F32) (buffer data : List ops.F32) (index : Nat) : backwardFirstValue ops scale buffer data index = f32Add ops (getD ops.undefined data index) (f32MulScaleHalf ops (getD ops.undefined buffer index) scale) := Eq.refl (f32Add ops (getD ops.undefined data index) (f32MulScaleHalf ops (getD ops.undefined buffer index) scale))

def backwardFirstLoop (ops : F32Ops) (scale : ops.F32) (buffer : List ops.F32) (data : List ops.F32) (index : Nat) (count : Nat) : List ops.F32 :=
match count with
| 0 => data
| Nat.succ rest =>
  let value := backwardFirstValue ops scale buffer data index
  let dataNext := setAt data index value
  backwardFirstLoop ops scale buffer dataNext (Nat.succ index) rest

theorem backwardFirstLoop_zero (ops : F32Ops) (scale : ops.F32) (buffer data : List ops.F32) (index : Nat) : backwardFirstLoop ops scale buffer data index 0 = data := Eq.refl data

theorem backwardFirstLoop_succ (ops : F32Ops) (scale : ops.F32) (buffer data : List ops.F32) (index count : Nat) : backwardFirstLoop ops scale buffer data index (Nat.succ count) = backwardFirstLoop ops scale buffer (setAt data index (backwardFirstValue ops scale buffer data index)) (Nat.succ index) count := Eq.refl (backwardFirstLoop ops scale buffer (setAt data index (backwardFirstValue ops scale buffer data index)) (Nat.succ index) count)

theorem backwardFirstLoop_length (ops : F32Ops) (scale : ops.F32) (buffer data : List ops.F32) (index : Nat) (count : Nat) : (backwardFirstLoop ops scale buffer data index count).length = data.length :=
match count with
| 0 => Eq.refl data.length
| Nat.succ rest => Eq.trans (backwardFirstLoop_length ops scale buffer (setAt data index (backwardFirstValue ops scale buffer data index)) (Nat.succ index) rest) (setAt_length data index (backwardFirstValue ops scale buffer data index))

def forwardCopiedBuffer (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : List ops.F32 := copyToBufferLoop ops data 0 (emptyBuffer ops) 0 self.dim

def forwardAfterFirst (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : List ops.F32 := forwardFirstLoop ops self.fractal_scale self.dim data 0 self.dim

def forwardDataCompleted (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : List ops.F32 := forwardSecondLoop ops self.fractal_scale self.dim (forwardCopiedBuffer ops self data) (forwardAfterFirst ops self data) 0 self.dim

theorem forwardCopiedBuffer_def (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : forwardCopiedBuffer ops self data = copyToBufferLoop ops data 0 (emptyBuffer ops) 0 self.dim := Eq.refl (copyToBufferLoop ops data 0 (emptyBuffer ops) 0 self.dim)

theorem forwardAfterFirst_def (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : forwardAfterFirst ops self data = forwardFirstLoop ops self.fractal_scale self.dim data 0 self.dim := Eq.refl (forwardFirstLoop ops self.fractal_scale self.dim data 0 self.dim)

theorem forwardDataCompleted_def (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : forwardDataCompleted ops self data = forwardSecondLoop ops self.fractal_scale self.dim (forwardCopiedBuffer ops self data) (forwardAfterFirst ops self data) 0 self.dim := Eq.refl (forwardSecondLoop ops self.fractal_scale self.dim (forwardCopiedBuffer ops self data) (forwardAfterFirst ops self data) 0 self.dim)

theorem forwardCopiedBuffer_length (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : (forwardCopiedBuffer ops self data).length = mixBufferLen := Eq.trans (copyToBufferLoop_length ops data 0 (emptyBuffer ops) 0 self.dim) (emptyBuffer_length ops)

theorem forwardAfterFirst_length (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : (forwardAfterFirst ops self data).length = data.length := forwardFirstLoop_length ops self.fractal_scale self.dim data 0 self.dim

theorem forwardDataCompleted_length (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : (forwardDataCompleted ops self data).length = data.length := Eq.trans (forwardSecondLoop_length ops self.fractal_scale self.dim (forwardCopiedBuffer ops self data) (forwardAfterFirst ops self data) 0 self.dim) (forwardAfterFirst_length ops self data)

def backwardCopiedBuffer (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : List ops.F32 := copyToBufferLoop ops data self.dim (emptyBuffer ops) 0 self.dim

def backwardAfterSecond (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : List ops.F32 := backwardSecondLoop ops self.fractal_scale self.dim data 0 self.dim

def backwardDataCompleted (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : List ops.F32 := backwardFirstLoop ops self.fractal_scale (backwardCopiedBuffer ops self data) (backwardAfterSecond ops self data) 0 self.dim

theorem backwardCopiedBuffer_def (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : backwardCopiedBuffer ops self data = copyToBufferLoop ops data self.dim (emptyBuffer ops) 0 self.dim := Eq.refl (copyToBufferLoop ops data self.dim (emptyBuffer ops) 0 self.dim)

theorem backwardAfterSecond_def (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : backwardAfterSecond ops self data = backwardSecondLoop ops self.fractal_scale self.dim data 0 self.dim := Eq.refl (backwardSecondLoop ops self.fractal_scale self.dim data 0 self.dim)

theorem backwardDataCompleted_def (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : backwardDataCompleted ops self data = backwardFirstLoop ops self.fractal_scale (backwardCopiedBuffer ops self data) (backwardAfterSecond ops self data) 0 self.dim := Eq.refl (backwardFirstLoop ops self.fractal_scale (backwardCopiedBuffer ops self data) (backwardAfterSecond ops self data) 0 self.dim)

theorem backwardCopiedBuffer_length (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : (backwardCopiedBuffer ops self data).length = mixBufferLen := Eq.trans (copyToBufferLoop_length ops data self.dim (emptyBuffer ops) 0 self.dim) (emptyBuffer_length ops)

theorem backwardAfterSecond_length (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : (backwardAfterSecond ops self data).length = data.length := backwardSecondLoop_length ops self.fractal_scale self.dim data 0 self.dim

theorem backwardDataCompleted_length (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) : (backwardDataCompleted ops self data).length = data.length := Eq.trans (backwardFirstLoop_length ops self.fractal_scale (backwardCopiedBuffer ops self data) (backwardAfterSecond ops self data) 0 self.dim) (backwardAfterSecond_length ops self data)

inductive RunBranch where
| arithmeticOverflow : RunBranch
| lengthTooShort : RunBranch
| bufferTooSmall : RunBranch
| completed : RunBranch

def branchIsCompleted : RunBranch → Bool
| RunBranch.completed => true
| _ => false

def branchIsNoChangeReturn : RunBranch → Bool
| RunBranch.lengthTooShort => true
| RunBranch.bufferTooSmall => true
| _ => false

def branchIsOverflow : RunBranch → Bool
| RunBranch.arithmeticOverflow => true
| _ => false

theorem branchIsCompleted_completed : branchIsCompleted RunBranch.completed = true := Eq.refl true

theorem branchIsCompleted_overflow : branchIsCompleted RunBranch.arithmeticOverflow = false := Eq.refl false

theorem branchIsCompleted_short : branchIsCompleted RunBranch.lengthTooShort = false := Eq.refl false

theorem branchIsCompleted_buffer : branchIsCompleted RunBranch.bufferTooSmall = false := Eq.refl false

theorem branchIsNoChangeReturn_short : branchIsNoChangeReturn RunBranch.lengthTooShort = true := Eq.refl true

theorem branchIsNoChangeReturn_buffer : branchIsNoChangeReturn RunBranch.bufferTooSmall = true := Eq.refl true

theorem branchIsNoChangeReturn_completed : branchIsNoChangeReturn RunBranch.completed = false := Eq.refl false

theorem branchIsOverflow_overflow : branchIsOverflow RunBranch.arithmeticOverflow = true := Eq.refl true

theorem branchIsOverflow_completed : branchIsOverflow RunBranch.completed = false := Eq.refl false

structure TensorResult (ops : F32Ops) where
  tensor : Tensor ops
  branch : RunBranch

structure BufferResult (ops : F32Ops) where
  data : List ops.F32
  branch : RunBranch

namespace TensorResult

def data (ops : F32Ops) (r : TensorResult ops) : List ops.F32 := r.tensor.data

def length (ops : F32Ops) (r : TensorResult ops) : Nat := r.tensor.data.length

theorem data_def (ops : F32Ops) (r : TensorResult ops) : data ops r = r.tensor.data := Eq.refl r.tensor.data

theorem length_def (ops : F32Ops) (r : TensorResult ops) : length ops r = r.tensor.data.length := Eq.refl r.tensor.data.length

end TensorResult

namespace BufferResult

def length (ops : F32Ops) (r : BufferResult ops) : Nat := r.data.length

theorem length_def (ops : F32Ops) (r : BufferResult ops) : length ops r = r.data.length := Eq.refl r.data.length

end BufferResult

def forwardPreconditionBool (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : Bool := boolAnd (usizeDoubleFits self.dim) (boolAnd (lenEnough self.dim x.data.length) (bufferFits self.dim))

def backwardPreconditionBool (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) : Bool := boolAnd (usizeDoubleFits self.dim) (boolAnd (lenEnough self.dim grad.length) (bufferFits self.dim))

theorem forwardPreconditionBool_def (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : forwardPreconditionBool ops self x = boolAnd (usizeDoubleFits self.dim) (boolAnd (lenEnough self.dim x.data.length) (bufferFits self.dim)) := Eq.refl (boolAnd (usizeDoubleFits self.dim) (boolAnd (lenEnough self.dim x.data.length) (bufferFits self.dim)))

theorem backwardPreconditionBool_def (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) : backwardPreconditionBool ops self grad = boolAnd (usizeDoubleFits self.dim) (boolAnd (lenEnough self.dim grad.length) (bufferFits self.dim)) := Eq.refl (boolAnd (usizeDoubleFits self.dim) (boolAnd (lenEnough self.dim grad.length) (bufferFits self.dim)))

theorem forwardPreconditionBool_true_of_parts (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : forwardPreconditionBool ops self x = true :=
match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl true

theorem backwardPreconditionBool_true_of_parts (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : backwardPreconditionBool ops self grad = true :=
match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl true

def forwardInPlace (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : TensorResult ops :=
match usizeDoubleFits self.dim with
| false => { tensor := x, branch := RunBranch.arithmeticOverflow }
| true =>
  match lenEnough self.dim x.data.length with
  | false => { tensor := x, branch := RunBranch.lengthTooShort }
  | true =>
    match bufferFits self.dim with
    | false => { tensor := x, branch := RunBranch.bufferTooSmall }
    | true => { tensor := { data := forwardDataCompleted ops self x.data }, branch := RunBranch.completed }

def backwardInPlace (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) : BufferResult ops :=
match usizeDoubleFits self.dim with
| false => { data := grad, branch := RunBranch.arithmeticOverflow }
| true =>
  match lenEnough self.dim grad.length with
  | false => { data := grad, branch := RunBranch.lengthTooShort }
  | true =>
    match bufferFits self.dim with
    | false => { data := grad, branch := RunBranch.bufferTooSmall }
    | true => { data := backwardDataCompleted ops self grad, branch := RunBranch.completed }

theorem forwardInPlace_overflow_result (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h : usizeDoubleFits self.dim = false) : forwardInPlace ops self x = { tensor := x, branch := RunBranch.arithmeticOverflow } := match h with | Eq.refl => Eq.refl ({ tensor := x, branch := RunBranch.arithmeticOverflow } : TensorResult ops)

theorem forwardInPlace_overflow_data (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h : usizeDoubleFits self.dim = false) : (forwardInPlace ops self x).tensor.data = x.data := match h with | Eq.refl => Eq.refl x.data

theorem forwardInPlace_overflow_branch (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h : usizeDoubleFits self.dim = false) : (forwardInPlace ops self x).branch = RunBranch.arithmeticOverflow := match h with | Eq.refl => Eq.refl RunBranch.arithmeticOverflow

theorem forwardInPlace_length_too_short_result (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = false) : forwardInPlace ops self x = { tensor := x, branch := RunBranch.lengthTooShort } := match h0 with | Eq.refl => match h1 with | Eq.refl => Eq.refl ({ tensor := x, branch := RunBranch.lengthTooShort } : TensorResult ops)

theorem forwardInPlace_length_too_short_data (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = false) : (forwardInPlace ops self x).tensor.data = x.data := match h0 with | Eq.refl => match h1 with | Eq.refl => Eq.refl x.data

theorem forwardInPlace_length_too_short_branch (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = false) : (forwardInPlace ops self x).branch = RunBranch.lengthTooShort := match h0 with | Eq.refl => match h1 with | Eq.refl => Eq.refl RunBranch.lengthTooShort

theorem forwardInPlace_buffer_too_small_result (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = false) : forwardInPlace ops self x = { tensor := x, branch := RunBranch.bufferTooSmall } := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl ({ tensor := x, branch := RunBranch.bufferTooSmall } : TensorResult ops)

theorem forwardInPlace_buffer_too_small_data (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = false) : (forwardInPlace ops self x).tensor.data = x.data := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl x.data

theorem forwardInPlace_buffer_too_small_branch (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = false) : (forwardInPlace ops self x).branch = RunBranch.bufferTooSmall := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl RunBranch.bufferTooSmall

theorem forwardInPlace_completed_result (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : forwardInPlace ops self x = { tensor := { data := forwardDataCompleted ops self x.data }, branch := RunBranch.completed } := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl ({ tensor := { data := forwardDataCompleted ops self x.data }, branch := RunBranch.completed } : TensorResult ops)

theorem forwardInPlace_completed_data (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardInPlace ops self x).tensor.data = forwardDataCompleted ops self x.data := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl (forwardDataCompleted ops self x.data)

theorem forwardInPlace_completed_branch (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardInPlace ops self x).branch = RunBranch.completed := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl RunBranch.completed

theorem forwardInPlace_length (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : (forwardInPlace ops self x).tensor.data.length = x.data.length :=
match usizeDoubleFits self.dim with
| false => Eq.refl x.data.length
| true =>
  match lenEnough self.dim x.data.length with
  | false => Eq.refl x.data.length
  | true =>
    match bufferFits self.dim with
    | false => Eq.refl x.data.length
    | true => forwardDataCompleted_length ops self x.data

theorem forwardInPlace_completed_length (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardInPlace ops self x).tensor.data.length = x.data.length := forwardInPlace_length ops self x

theorem forward_completed_first_slice_valid (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h : lenEnough self.dim x.data.length = true) : sliceValidIn (firstSlice self.dim) x.data.length = true := firstSlice_valid_of_lenEnough self.dim x.data.length h

theorem forward_completed_second_slice_valid (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h : lenEnough self.dim x.data.length = true) : sliceValidIn (secondSlice self.dim) x.data.length = true := secondSlice_valid_of_lenEnough self.dim x.data.length h

theorem backwardInPlace_overflow_result (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h : usizeDoubleFits self.dim = false) : backwardInPlace ops self grad = { data := grad, branch := RunBranch.arithmeticOverflow } := match h with | Eq.refl => Eq.refl ({ data := grad, branch := RunBranch.arithmeticOverflow } : BufferResult ops)

theorem backwardInPlace_overflow_data (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h : usizeDoubleFits self.dim = false) : (backwardInPlace ops self grad).data = grad := match h with | Eq.refl => Eq.refl grad

theorem backwardInPlace_overflow_branch (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h : usizeDoubleFits self.dim = false) : (backwardInPlace ops self grad).branch = RunBranch.arithmeticOverflow := match h with | Eq.refl => Eq.refl RunBranch.arithmeticOverflow

theorem backwardInPlace_length_too_short_result (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = false) : backwardInPlace ops self grad = { data := grad, branch := RunBranch.lengthTooShort } := match h0 with | Eq.refl => match h1 with | Eq.refl => Eq.refl ({ data := grad, branch := RunBranch.lengthTooShort } : BufferResult ops)

theorem backwardInPlace_length_too_short_data (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = false) : (backwardInPlace ops self grad).data = grad := match h0 with | Eq.refl => match h1 with | Eq.refl => Eq.refl grad

theorem backwardInPlace_length_too_short_branch (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = false) : (backwardInPlace ops self grad).branch = RunBranch.lengthTooShort := match h0 with | Eq.refl => match h1 with | Eq.refl => Eq.refl RunBranch.lengthTooShort

theorem backwardInPlace_buffer_too_small_result (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = false) : backwardInPlace ops self grad = { data := grad, branch := RunBranch.bufferTooSmall } := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl ({ data := grad, branch := RunBranch.bufferTooSmall } : BufferResult ops)

theorem backwardInPlace_buffer_too_small_data (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = false) : (backwardInPlace ops self grad).data = grad := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl grad

theorem backwardInPlace_buffer_too_small_branch (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = false) : (backwardInPlace ops self grad).branch = RunBranch.bufferTooSmall := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl RunBranch.bufferTooSmall

theorem backwardInPlace_completed_result (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : backwardInPlace ops self grad = { data := backwardDataCompleted ops self grad, branch := RunBranch.completed } := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl ({ data := backwardDataCompleted ops self grad, branch := RunBranch.completed } : BufferResult ops)

theorem backwardInPlace_completed_data (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : (backwardInPlace ops self grad).data = backwardDataCompleted ops self grad := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl (backwardDataCompleted ops self grad)

theorem backwardInPlace_completed_branch (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : (backwardInPlace ops self grad).branch = RunBranch.completed := match h0 with | Eq.refl => match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl RunBranch.completed

theorem backwardInPlace_length (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) : (backwardInPlace ops self grad).data.length = grad.length :=
match usizeDoubleFits self.dim with
| false => Eq.refl grad.length
| true =>
  match lenEnough self.dim grad.length with
  | false => Eq.refl grad.length
  | true =>
    match bufferFits self.dim with
    | false => Eq.refl grad.length
    | true => backwardDataCompleted_length ops self grad

theorem backwardInPlace_completed_length (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : (backwardInPlace ops self grad).data.length = grad.length := backwardInPlace_length ops self grad

theorem backward_completed_first_slice_valid (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h : lenEnough self.dim grad.length = true) : sliceValidIn (firstSlice self.dim) grad.length = true := firstSlice_valid_of_lenEnough self.dim grad.length h

theorem backward_completed_second_slice_valid (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h : lenEnough self.dim grad.length = true) : sliceValidIn (secondSlice self.dim) grad.length = true := secondSlice_valid_of_lenEnough self.dim grad.length h

structure PipelineResult (ops : F32Ops) where
  forward : TensorResult ops
  backward : BufferResult ops

def forwardBackwardPipeline (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : PipelineResult ops :=
let first := forwardInPlace ops self x
let second := backwardInPlace ops self first.tensor.data
{ forward := first, backward := second }

theorem forwardBackwardPipeline_forward (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : (forwardBackwardPipeline ops self x).forward = forwardInPlace ops self x := Eq.refl (forwardInPlace ops self x)

theorem forwardBackwardPipeline_backward (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : (forwardBackwardPipeline ops self x).backward = backwardInPlace ops self (forwardInPlace ops self x).tensor.data := Eq.refl (backwardInPlace ops self (forwardInPlace ops self x).tensor.data)

theorem forwardBackwardPipeline_forward_length (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : (forwardBackwardPipeline ops self x).forward.tensor.data.length = x.data.length := forwardInPlace_length ops self x

theorem forwardBackwardPipeline_backward_length (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) : (forwardBackwardPipeline ops self x).backward.data.length = x.data.length := Eq.trans (backwardInPlace_length ops self (forwardInPlace ops self x).tensor.data) (forwardInPlace_length ops self x)

theorem forwardBackwardPipeline_forward_completed_branch (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardBackwardPipeline ops self x).forward.branch = RunBranch.completed := forwardInPlace_completed_branch ops self x h0 h1 h2

theorem forwardBackwardPipeline_backward_completed_branch (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardBackwardPipeline ops self x).backward.branch = RunBranch.completed :=
have hlen : (forwardInPlace ops self x).tensor.data.length = x.data.length := forwardInPlace_length ops self x
have hle : lenEnough self.dim (forwardInPlace ops self x).tensor.data.length = lenEnough self.dim x.data.length := congrArg (lenEnough self.dim) hlen
have htrue : lenEnough self.dim (forwardInPlace ops self x).tensor.data.length = true := Eq.trans hle h1
backwardInPlace_completed_branch ops self (forwardInPlace ops self x).tensor.data h0 htrue h2

theorem forwardBackwardPipeline_forward_completed_data (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardBackwardPipeline ops self x).forward.tensor.data = forwardDataCompleted ops self x.data := forwardInPlace_completed_data ops self x h0 h1 h2

theorem forwardBackwardPipeline_lengths_preserved_under_success (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardBackwardPipeline ops self x).forward.tensor.data.length = x.data.length ∧ (forwardBackwardPipeline ops self x).backward.data.length = x.data.length := And.intro (forwardBackwardPipeline_forward_length ops self x) (forwardBackwardPipeline_backward_length ops self x)

def forwardFirstElem (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) : ops.F32 := f32Add ops (getD ops.undefined data i) (f32Mul ops (getD ops.undefined data (dim + i)) scale)

def forwardSecondElem (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) : ops.F32 := f32Add ops (getD ops.undefined data (dim + i)) (f32MulScaleHalf ops (getD ops.undefined data (i - dim)) scale)

def forwardSpecElem (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) : ops.F32 :=
match natLtBool i dim with
| true => forwardFirstElem ops scale dim data i
| false => match natLtBool i (doubleNat dim) with
  | true => forwardSecondElem ops scale dim data i
  | false => getD ops.undefined data i

def backwardFirstElem (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) : ops.F32 := f32Add ops (getD ops.undefined data i) (f32MulScaleHalf ops (getD ops.undefined data (dim + i)) scale)

def backwardSecondElem (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) : ops.F32 := f32Add ops (getD ops.undefined data (dim + i)) (f32Mul ops (getD ops.undefined data (i - dim)) scale)

def backwardSpecElem (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) : ops.F32 :=
match natLtBool i dim with
| true => backwardFirstElem ops scale dim data i
| false => match natLtBool i (doubleNat dim) with
  | true => backwardSecondElem ops scale dim data i
  | false => getD ops.undefined data i

theorem forwardSpecElem_first_def (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) (h : natLtBool i dim = true) : forwardSpecElem ops scale dim data i = forwardFirstElem ops scale dim data i := match h with | Eq.refl => Eq.refl (forwardFirstElem ops scale dim data i)

theorem forwardSpecElem_second_def (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) (h1 : natLtBool i dim = false) (h2 : natLtBool i (doubleNat dim) = true) : forwardSpecElem ops scale dim data i = forwardSecondElem ops scale dim data i := match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl (forwardSecondElem ops scale dim data i)

theorem forwardSpecElem_tail_def (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) (h1 : natLtBool i dim = false) (h2 : natLtBool i (doubleNat dim) = false) : forwardSpecElem ops scale dim data i = getD ops.undefined data i := match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl (getD ops.undefined data i)

theorem backwardSpecElem_first_def (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) (h : natLtBool i dim = true) : backwardSpecElem ops scale dim data i = backwardFirstElem ops scale dim data i := match h with | Eq.refl => Eq.refl (backwardFirstElem ops scale dim data i)

theorem backwardSpecElem_second_def (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) (h1 : natLtBool i dim = false) (h2 : natLtBool i (doubleNat dim) = true) : backwardSpecElem ops scale dim data i = backwardSecondElem ops scale dim data i := match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl (backwardSecondElem ops scale dim data i)

theorem backwardSpecElem_tail_def (ops : F32Ops) (scale : ops.F32) (dim : Nat) (data : List ops.F32) (i : Nat) (h1 : natLtBool i dim = false) (h2 : natLtBool i (doubleNat dim) = false) : backwardSpecElem ops scale dim data i = getD ops.undefined data i := match h1 with | Eq.refl => match h2 with | Eq.refl => Eq.refl (getD ops.undefined data i)

theorem forwardFirstLoop_tail (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index count : Nat) (i : Nat) (h : natLeBool (doubleNat half) i = true) : getD ops.undefined (forwardFirstLoop ops scale half data index count) i = getD ops.undefined data i :=
match count with
| 0 => Eq.refl (getD ops.undefined data i)
| Nat.succ rest =>
  let value := forwardFirstValue ops scale half data index
  let dataNext := setAt data index value
  have ih : getD ops.undefined (forwardFirstLoop ops scale half dataNext (Nat.succ index) rest) i = getD ops.undefined dataNext i := forwardFirstLoop_tail ops scale half dataNext (Nat.succ index) rest i h
  have hset : getD ops.undefined dataNext i = getD ops.undefined data i := Eq.refl (getD ops.undefined data i)
  Eq.trans ih hset

theorem forwardSecondLoop_tail (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer data : List ops.F32) (index count : Nat) (i : Nat) (h : natLeBool (doubleNat half) i = true) : getD ops.undefined (forwardSecondLoop ops scale half buffer data index count) i = getD ops.undefined data i :=
match count with
| 0 => Eq.refl (getD ops.undefined data i)
| Nat.succ rest =>
  let value := forwardSecondValue ops scale half buffer data index
  let dataNext := setAt data (half + index) value
  have ih : getD ops.undefined (forwardSecondLoop ops scale half buffer dataNext (Nat.succ index) rest) i = getD ops.undefined dataNext i := forwardSecondLoop_tail ops scale half buffer dataNext (Nat.succ index) rest i h
  have hset : getD ops.undefined dataNext i = getD ops.undefined data i := Eq.refl (getD ops.undefined data i)
  Eq.trans ih hset

theorem backwardSecondLoop_tail (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index count : Nat) (i : Nat) (h : natLeBool (doubleNat half) i = true) : getD ops.undefined (backwardSecondLoop ops scale half data index count) i = getD ops.undefined data i :=
match count with
| 0 => Eq.refl (getD ops.undefined data i)
| Nat.succ rest =>
  let value := backwardSecondValue ops scale half data index
  let dataNext := setAt data (half + index) value
  have ih : getD ops.undefined (backwardSecondLoop ops scale half dataNext (Nat.succ index) rest) i = getD ops.undefined dataNext i := backwardSecondLoop_tail ops scale half dataNext (Nat.succ index) rest i h
  have hset : getD ops.undefined dataNext i = getD ops.undefined data i := Eq.refl (getD ops.undefined data i)
  Eq.trans ih hset

theorem backwardFirstLoop_tail (ops : F32Ops) (scale : ops.F32) (buffer : List ops.F32) (data : List ops.F32) (index count : Nat) (i : Nat) (h : natLeBool (doubleNat index) i = true) : getD ops.undefined (backwardFirstLoop ops scale buffer data index count) i = getD ops.undefined data i :=
match count with
| 0 => Eq.refl (getD ops.undefined data i)
| Nat.succ rest =>
  let value := backwardFirstValue ops scale buffer data index
  let dataNext := setAt data index value
  have ih : getD ops.undefined (backwardFirstLoop ops scale buffer dataNext (Nat.succ index) rest) i = getD ops.undefined dataNext i := backwardFirstLoop_tail ops scale buffer dataNext (Nat.succ index) rest i h
  have hset : getD ops.undefined dataNext i = getD ops.undefined data i := Eq.refl (getD ops.undefined data i)
  Eq.trans ih hset

theorem forwardDataCompleted_tail (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLeBool (doubleNat self.dim) i = true) : getD ops.undefined (forwardDataCompleted ops self data) i = getD ops.undefined data i := forwardSecondLoop_tail ops self.fractal_scale self.dim (forwardCopiedBuffer ops self data) (forwardAfterFirst ops self data) 0 self.dim i h

theorem backwardDataCompleted_tail (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLeBool (doubleNat self.dim) i = true) : getD ops.undefined (backwardDataCompleted ops self data) i = getD ops.undefined data i := backwardFirstLoop_tail ops self.fractal_scale (backwardCopiedBuffer ops self data) (backwardAfterSecond ops self data) 0 self.dim i h

theorem copyToBufferLoop_getD_prefix (ops : F32Ops) (source : List ops.F32) (sourceBase : Nat) (buffer : List ops.F32) (dest count : Nat) (i : Nat) (h : natLtBool i count = true) : getD ops.undefined (copyToBufferLoop ops source sourceBase buffer dest count) (dest + i) = getD ops.undefined source (sourceBase + dest + i) :=
match count with
| 0 => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (natLtBool_def i 0)) h))
| Nat.succ rest =>
  match natLtBool i (Nat.succ rest) with
  | true => 
    match natLtBool i 0 with
    | true => Eq.refl (getD ops.undefined source (sourceBase + dest + i))
    | false =>
      let value := getD ops.undefined source (sourceBase + dest)
      let bufferNext := setAt buffer dest value
      have ih : getD ops.undefined (copyToBufferLoop ops source sourceBase bufferNext (Nat.succ dest) rest) (Nat.succ dest + i) = getD ops.undefined source (sourceBase + Nat.succ dest + i) := copyToBufferLoop_getD_prefix ops source sourceBase bufferNext (Nat.succ dest) rest i (natLeBool_true_trans (Nat.succ i) (Nat.succ rest) (Nat.succ rest) (natLeBool_succ_succ i rest) h)
      Eq.trans ih (Eq.refl (getD ops.undefined source (sourceBase + Nat.succ dest + i)))
  | false => Eq.refl (getD ops.undefined source (sourceBase + dest + i))

theorem forwardCopiedBuffer_getD (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLtBool i self.dim = true) : getD ops.undefined (forwardCopiedBuffer ops self data) i = getD ops.undefined data i := copyToBufferLoop_getD_prefix ops data 0 (emptyBuffer ops) 0 self.dim i h

theorem backwardCopiedBuffer_getD (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLtBool i self.dim = true) : getD ops.undefined (backwardCopiedBuffer ops self data) i = getD ops.undefined data (self.dim + i) := copyToBufferLoop_getD_prefix ops data self.dim (emptyBuffer ops) 0 self.dim i h

theorem forwardFirstLoop_getD_updated (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index count : Nat) (i : Nat) (h1 : natLeBool index i = true) (h2 : natLtBool i (index + count) = true) : getD ops.undefined (forwardFirstLoop ops scale half data index count) i = forwardFirstValue ops scale half data i :=
match count with
| 0 => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (natLeBool_succ_zero (index + count))) h2))
| Nat.succ rest =>
  let value := forwardFirstValue ops scale half data index
  let dataNext := setAt data index value
  match natLeBool index i with
  | true =>
    match natLtBool i (Nat.succ index) with
    | true => Eq.refl (forwardFirstValue ops scale half data i)
    | false =>
      have ih : getD ops.undefined (forwardFirstLoop ops scale half dataNext (Nat.succ index) rest) i = forwardFirstValue ops scale half dataNext i := forwardFirstLoop_getD_updated ops scale half dataNext (Nat.succ index) rest i (natLeBool_true_trans index (Nat.succ index) i h1 (natLeBool_succ_succ index i)) (natLeBool_true_trans (Nat.succ i) (Nat.succ (index + rest)) (Nat.succ (index + rest)) (natLeBool_succ_succ i (index + rest)) h2)
      have hval : forwardFirstValue ops scale half dataNext i = forwardFirstValue ops scale half data i := Eq.refl (forwardFirstValue ops scale half data i)
      Eq.trans ih hval
  | false => Eq.refl (forwardFirstValue ops scale half data i)

theorem forwardSecondLoop_getD_updated (ops : F32Ops) (scale : ops.F32) (half : Nat) (buffer data : List ops.F32) (index count : Nat) (i : Nat) (h1 : natLeBool (half + index) i = true) (h2 : natLtBool i (half + index + count) = true) : getD ops.undefined (forwardSecondLoop ops scale half buffer data index count) i = forwardSecondValue ops scale half buffer data i :=
match count with
| 0 => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (natLeBool_succ_zero (half + index + count))) h2))
| Nat.succ rest =>
  let value := forwardSecondValue ops scale half buffer data index
  let dataNext := setAt data (half + index) value
  match natLeBool (half + index) i with
  | true =>
    match natLtBool i (Nat.succ (half + index)) with
    | true => Eq.refl (forwardSecondValue ops scale half buffer data i)
    | false =>
      have ih : getD ops.undefined (forwardSecondLoop ops scale half buffer dataNext (Nat.succ index) rest) i = forwardSecondValue ops scale half buffer dataNext i := forwardSecondLoop_getD_updated ops scale half buffer dataNext (Nat.succ index) rest i (natLeBool_true_trans (half + index) (half + Nat.succ index) i h1 (natLeBool_left_add_right (half + index) 1)) (natLeBool_true_trans (Nat.succ i) (Nat.succ (half + index + rest)) (Nat.succ (half + index + rest)) (natLeBool_succ_succ i (half + index + rest)) h2)
      have hval : forwardSecondValue ops scale half buffer dataNext i = forwardSecondValue ops scale half buffer data i := Eq.refl (forwardSecondValue ops scale half buffer data i)
      Eq.trans ih hval
  | false => Eq.refl (forwardSecondValue ops scale half buffer data i)

theorem backwardSecondLoop_getD_updated (ops : F32Ops) (scale : ops.F32) (half : Nat) (data : List ops.F32) (index count : Nat) (i : Nat) (h1 : natLeBool (half + index) i = true) (h2 : natLtBool i (half + index + count) = true) : getD ops.undefined (backwardSecondLoop ops scale half data index count) i = backwardSecondValue ops scale half data i :=
match count with
| 0 => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (natLeBool_succ_zero (half + index + count))) h2))
| Nat.succ rest =>
  let value := backwardSecondValue ops scale half data index
  let dataNext := setAt data (half + index) value
  match natLeBool (half + index) i with
  | true =>
    match natLtBool i (Nat.succ (half + index)) with
    | true => Eq.refl (backwardSecondValue ops scale half data i)
    | false =>
      have ih : getD ops.undefined (backwardSecondLoop ops scale half dataNext (Nat.succ index) rest) i = backwardSecondValue ops scale half dataNext i := backwardSecondLoop_getD_updated ops scale half dataNext (Nat.succ index) rest i (natLeBool_true_trans (half + index) (half + Nat.succ index) i h1 (natLeBool_left_add_right (half + index) 1)) (natLeBool_true_trans (Nat.succ i) (Nat.succ (half + index + rest)) (Nat.succ (half + index + rest)) (natLeBool_succ_succ i (half + index + rest)) h2)
      have hval : backwardSecondValue ops scale half dataNext i = backwardSecondValue ops scale half data i := Eq.refl (backwardSecondValue ops scale half data i)
      Eq.trans ih hval
  | false => Eq.refl (backwardSecondValue ops scale half data i)

theorem backwardFirstLoop_getD_updated (ops : F32Ops) (scale : ops.F32) (buffer data : List ops.F32) (index count : Nat) (i : Nat) (h1 : natLeBool index i = true) (h2 : natLtBool i (index + count) = true) : getD ops.undefined (backwardFirstLoop ops scale buffer data index count) i = backwardFirstValue ops scale buffer data i :=
match count with
| 0 => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (natLeBool_succ_zero (index + count))) h2))
| Nat.succ rest =>
  let value := backwardFirstValue ops scale buffer data index
  let dataNext := setAt data index value
  match natLeBool index i with
  | true =>
    match natLtBool i (Nat.succ index) with
    | true => Eq.refl (backwardFirstValue ops scale buffer data i)
    | false =>
      have ih : getD ops.undefined (backwardFirstLoop ops scale buffer dataNext (Nat.succ index) rest) i = backwardFirstValue ops scale buffer dataNext i := backwardFirstLoop_getD_updated ops scale buffer dataNext (Nat.succ index) rest i (natLeBool_true_trans index (Nat.succ index) i h1 (natLeBool_succ_succ index i)) (natLeBool_true_trans (Nat.succ i) (Nat.succ (index + rest)) (Nat.succ (index + rest)) (natLeBool_succ_succ i (index + rest)) h2)
      have hval : backwardFirstValue ops scale buffer dataNext i = backwardFirstValue ops scale buffer data i := Eq.refl (backwardFirstValue ops scale buffer data i)
      Eq.trans ih hval
  | false => Eq.refl (backwardFirstValue ops scale buffer data i)

theorem forwardAfterFirst_first_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLtBool i self.dim = true) : getD ops.undefined (forwardAfterFirst ops self data) i = forwardFirstValue ops self.fractal_scale self.dim data i := forwardFirstLoop_getD_updated ops self.fractal_scale self.dim data 0 self.dim i (natLeBool_zero_left i) h

theorem forwardAfterFirst_second_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true) : getD ops.undefined (forwardAfterFirst ops self data) i = getD ops.undefined data i := forwardFirstLoop_tail ops self.fractal_scale self.dim data 0 self.dim i (natLeBool_true_trans self.dim (doubleNat self.dim) i (natLeBool_left_add_right self.dim self.dim) (boolAnd_true_left (natLtBool i (doubleNat self.dim)) h))

theorem forwardAfterFirst_tail (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLeBool (doubleNat self.dim) i = true) : getD ops.undefined (forwardAfterFirst ops self data) i = getD ops.undefined data i := forwardFirstLoop_tail ops self.fractal_scale self.dim data 0 self.dim i h

theorem forwardDataCompleted_first_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLtBool i self.dim = true) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : getD ops.undefined (forwardDataCompleted ops self data) i = forwardSpecElem ops self.fractal_scale self.dim data i := forwardSecondLoop_getD_updated ops self.fractal_scale self.dim (forwardCopiedBuffer ops self data) (forwardAfterFirst ops self data) 0 self.dim i (natLeBool_zero_left i) h

theorem forwardDataCompleted_second_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : getD ops.undefined (forwardDataCompleted ops self data) i = forwardSpecElem ops self.fractal_scale self.dim data i := forwardSecondLoop_getD_updated ops self.fractal_scale self.dim (forwardCopiedBuffer ops self data) (forwardAfterFirst ops self data) 0 self.dim i (natLeBool_left_add_right self.dim i) (boolAnd_true_left (natLtBool i (doubleNat self.dim)) h)

theorem forwardDataCompleted_tail_spec (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLeBool (doubleNat self.dim) i = true) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : getD ops.undefined (forwardDataCompleted ops self data) i = forwardSpecElem ops self.fractal_scale self.dim data i := forwardDataCompleted_tail ops self data i h

theorem backwardAfterSecond_second_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true) : getD ops.undefined (backwardAfterSecond ops self data) i = backwardSecondValue ops self.fractal_scale self.dim data i := backwardSecondLoop_getD_updated ops self.fractal_scale self.dim data 0 self.dim i (natLeBool_left_add_right self.dim i) (boolAnd_true_left (natLtBool i (doubleNat self.dim)) h)

theorem backwardAfterSecond_first_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLtBool i self.dim = true) : getD ops.undefined (backwardAfterSecond ops self data) i = getD ops.undefined data i := backwardSecondLoop_tail ops self.fractal_scale self.dim data 0 self.dim i (natLeBool_true_trans self.dim (doubleNat self.dim) i (natLeBool_left_add_right self.dim self.dim) (natLtBool_def i (doubleNat self.dim)))

theorem backwardAfterSecond_tail (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLeBool (doubleNat self.dim) i = true) : getD ops.undefined (backwardAfterSecond ops self data) i = getD ops.undefined data i := backwardSecondLoop_tail ops self.fractal_scale self.dim data 0 self.dim i h

theorem backwardDataCompleted_first_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLtBool i self.dim = true) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : getD ops.undefined (backwardDataCompleted ops self data) i = backwardSpecElem ops self.fractal_scale self.dim data i := backwardFirstLoop_getD_updated ops self.fractal_scale (backwardCopiedBuffer ops self data) (backwardAfterSecond ops self data) 0 self.dim i (natLeBool_zero_left i) h

theorem backwardDataCompleted_second_block (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : getD ops.undefined (backwardDataCompleted ops self data) i = backwardSpecElem ops self.fractal_scale self.dim data i := backwardFirstLoop_getD_updated ops self.fractal_scale (backwardCopiedBuffer ops self data) (backwardAfterSecond ops self data) 0 self.dim i (natLeBool_left_add_right self.dim i) (boolAnd_true_left (natLtBool i (doubleNat self.dim)) h)

theorem backwardDataCompleted_tail_spec (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (i : Nat) (h : natLeBool (doubleNat self.dim) i = true) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : getD ops.undefined (backwardDataCompleted ops self data) i = backwardSpecElem ops self.fractal_scale self.dim data i := backwardDataCompleted_tail ops self data i h

def MatchesZigForward (ops : F32Ops) (self : OFTB ops) (original : List ops.F32) (result : List ops.F32) : Prop :=
result.length = original.length ∧
(∀ i : Nat, natLtBool i self.dim = true → getD ops.undefined result i = forwardFirstElem ops self.fractal_scale self.dim original i) ∧
(∀ i : Nat, boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true → getD ops.undefined result i = forwardSecondElem ops self.fractal_scale self.dim original i) ∧
(∀ i : Nat, natLeBool (doubleNat self.dim) i = true → getD ops.undefined result i = getD ops.undefined original i)

def MatchesZigBackward (ops : F32Ops) (self : OFTB ops) (original : List ops.F32) (result : List ops.F32) : Prop :=
result.length = original.length ∧
(∀ i : Nat, natLtBool i self.dim = true → getD ops.undefined result i = backwardFirstElem ops self.fractal_scale self.dim original i) ∧
(∀ i : Nat, boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true → getD ops.undefined result i = backwardSecondElem ops self.fractal_scale self.dim original i) ∧
(∀ i : Nat, natLeBool (doubleNat self.dim) i = true → getD ops.undefined result i = getD ops.undefined original i)

theorem forwardInPlace_correct_completed (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardInPlace ops self x).branch = RunBranch.completed ∧ (forwardInPlace ops self x).tensor.data.length = x.data.length ∧ MatchesZigForward ops self x.data (forwardDataCompleted ops self x.data) :=
And.intro (forwardInPlace_completed_branch ops self x h0 h1 h2) (And.intro (forwardInPlace_completed_length ops self x h0 h1 h2) (And.intro (forwardDataCompleted_length ops self x.data) (And.intro (fun i h => forwardDataCompleted_first_block ops self x.data i h h1 h2) (And.intro (fun i h => forwardDataCompleted_second_block ops self x.data i h h1 h2) (fun i h => forwardDataCompleted_tail_spec ops self x.data i h h1 h2)))))

theorem backwardInPlace_correct_completed (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : (backwardInPlace ops self grad).branch = RunBranch.completed ∧ (backwardInPlace ops self grad).data.length = grad.length ∧ MatchesZigBackward ops self grad (backwardDataCompleted ops self grad) :=
And.intro (backwardInPlace_completed_branch ops self grad h0 h1 h2) (And.intro (backwardInPlace_completed_length ops self grad h0 h1 h2) (And.intro (backwardDataCompleted_length ops self grad) (And.intro (fun i h => backwardDataCompleted_first_block ops self grad i h h1 h2) (And.intro (fun i h => backwardDataCompleted_second_block ops self grad i h h1 h2) (fun i h => backwardDataCompleted_tail_spec ops self grad i h h1 h2)))))

theorem lenEnough_corresponds_to_Zig (dim len : Nat) : lenEnough dim len = boolNot (natLtBool len (doubleNat dim)) :=
match natLtBool len (doubleNat dim) with
| true => Eq.refl false
| false => Eq.refl true

theorem bufferFits_corresponds_to_Zig (dim : Nat) : bufferFits dim = boolNot (natLtBool dim mixBufferLen) :=
match natLtBool dim mixBufferLen with
| true => Eq.refl false
| false => Eq.refl true

theorem usizeDoubleFits_corresponds_to_Zig (dim : Nat) : usizeDoubleFits dim = boolNot (natLtBool (doubleNat dim) usizeMax) :=
match natLtBool (doubleNat dim) usizeMax with
| true => Eq.refl false
| false => Eq.refl true

theorem forwardBackwardPipeline_composition (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardBackwardPipeline ops self x).backward.data = backwardDataCompleted ops self (forwardDataCompleted ops self x.data) := Eq.refl (backwardDataCompleted ops self (forwardDataCompleted ops self x.data))

theorem pipeline_matches_two_transforms_first (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (i : Nat) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) (h : natLtBool i self.dim = true) : getD ops.undefined ((forwardBackwardPipeline ops self x).backward.data) i = backwardSpecElem ops self.fractal_scale self.dim (forwardDataCompleted ops self x.data) i := backwardDataCompleted_first_block ops self (forwardDataCompleted ops self x.data) i h (forwardDataCompleted_length ops self x.data) h2

theorem pipeline_matches_two_transforms_second (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (i : Nat) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) (h : boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true) : getD ops.undefined ((forwardBackwardPipeline ops self x).backward.data) i = backwardSpecElem ops self.fractal_scale self.dim (forwardDataCompleted ops self x.data) i := backwardDataCompleted_second_block ops self (forwardDataCompleted ops self x.data) i h (forwardDataCompleted_length ops self x.data) h2

theorem pipeline_matches_two_transforms_tail (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (i : Nat) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) (h : natLeBool (doubleNat self.dim) i = true) : getD ops.undefined ((forwardBackwardPipeline ops self x).backward.data) i = backwardSpecElem ops self.fractal_scale self.dim (forwardDataCompleted ops self x.data) i := backwardDataCompleted_tail_spec ops self (forwardDataCompleted ops self x.data) i h (forwardDataCompleted_length ops self x.data) h2

theorem forwardInPlace_zig_memory_safe (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : (forwardInPlace ops self x).branch = RunBranch.completed := forwardInPlace_completed_branch ops self x h0 h1 h2

theorem backwardInPlace_zig_memory_safe (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : (backwardInPlace ops self grad).branch = RunBranch.completed := backwardInPlace_completed_branch ops self grad h0 h1 h2

theorem forwardInPlace_zig_refines_spec (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : MatchesZigForward ops self x.data (forwardInPlace ops self x).tensor.data := (forwardInPlace_correct_completed ops self x h0 h1 h2).right.right

theorem backwardInPlace_zig_refines_spec (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) : MatchesZigBackward ops self grad (backwardInPlace ops self grad).data := (backwardInPlace_correct_completed ops self grad h0 h1 h2).right.right

theorem forward_backward_pipeline_zig_refines_spec (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) : MatchesZigBackward ops self (forwardDataCompleted ops self x.data) (forwardBackwardPipeline ops self x).backward.data := 
have hlen : (forwardInPlace ops self x).tensor.data.length = x.data.length := forwardInPlace_length ops self x
have hle : lenEnough self.dim (forwardInPlace ops self x).tensor.data.length = lenEnough self.dim x.data.length := congrArg (lenEnough self.dim) hlen
have htrue : lenEnough self.dim (forwardInPlace ops self x).tensor.data.length = true := Eq.trans hle h1
And.right (And.right (backwardInPlace_correct_completed ops self (forwardInPlace ops self x).tensor.data h0 htrue h2))

def ZigF32 : Type := Float

def zigLit70710678 : ZigF32 := 0.70710678

def zigLit05 : ZigF32 := 0.5

def zigUndefined : ZigF32 := 0.0

def zigAdd : ZigF32 → ZigF32 → ZigF32 := Float.add

def zigMul : ZigF32 → ZigF32 → ZigF32 := Float.mul

def zigF32Ops : F32Ops where
  F32 := ZigF32
  lit70710678 := zigLit70710678
  lit05 := zigLit05
  undefined := zigUndefined
  add := zigAdd
  mul := zigMul

theorem zigF32Ops_concrete_F32 : zigF32Ops.F32 = ZigF32 := Eq.refl ZigF32

theorem zigF32Ops_concrete_add (a b : ZigF32) : zigF32Ops.add a b = Float.add a b := Eq.refl (Float.add a b)

theorem zigF32Ops_concrete_mul (a b : ZigF32) : zigF32Ops.mul a b = Float.mul a b := Eq.refl (Float.mul a b)

theorem zigF32Ops_concrete_lit70710678 : zigF32Ops.lit70710678 = 0.70710678 := Eq.refl 0.70710678

theorem zigF32Ops_concrete_lit05 : zigF32Ops.lit05 = 0.5 := Eq.refl 0.5

theorem zig_precondition_dim_le_buffer (dim : Nat) (h : bufferFits dim = true) : dim ≤ mixBufferLen := natLeBool_true_trans dim mixBufferLen (mixBufferLen) (natLeBool_refl dim) (Eq.mp (bufferFits_def dim) h)

theorem zig_precondition_double_dim_le_usizeMax (dim : Nat) (h : usizeDoubleFits dim = true) : doubleNat dim ≤ usizeMax := natLeBool_true_trans (doubleNat dim) usizeMax (usizeMax) (natLeBool_refl (doubleNat dim)) (Eq.mp (usizeDoubleFits_def dim) h)

theorem zig_precondition_len_enough (dim len : Nat) (h : lenEnough dim len = true) : doubleNat dim ≤ len := natLeBool_true_trans (doubleNat dim) len (len) (natLeBool_refl (doubleNat dim)) (Eq.mp (lenEnough_def dim len) h)

theorem zig_slice_first_in_bounds (dim : Nat) (data : List ZigF32) (h : lenEnough dim data.length = true) : dim ≤ data.length := 
have hdouble : doubleNat dim ≤ data.length := zig_precondition_len_enough dim data.length h
natLeBool_true_trans dim (doubleNat dim) data.length (natLeBool_left_add_right dim dim) hdouble

theorem zig_slice_second_in_bounds (dim : Nat) (data : List ZigF32) (h : lenEnough dim data.length = true) : doubleNat dim ≤ data.length := zig_precondition_len_enough dim data.length h

theorem zig_buffer_access_in_bounds (dim : Nat) (i : Nat) (h : natLtBool i dim = true) (hbuf : bufferFits dim = true) : i < mixBufferLen := 
have hdimle : dim ≤ mixBufferLen := zig_precondition_dim_le_buffer dim hbuf
have hidim : i < dim := Eq.mp (natLtBool_def i dim) h
natLeBool_true_trans i dim mixBufferLen (natLeBool_succ_succ i (Nat.pred dim)) (natLeBool_true_trans dim mixBufferLen mixBufferLen (natLeBool_refl dim) (Eq.mp (bufferFits_def dim) hbuf))

theorem forward_memory_safe_index (ops : F32Ops) (self : OFTB ops) (x : Tensor ops) (i : Nat) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim x.data.length = true) (h2 : bufferFits self.dim = true) (hi : natLtBool i self.dim = true) : i < x.data.length ∧ self.dim + i < x.data.length :=
And.intro (zig_slice_first_in_bounds self.dim x.data h1) (have hsecond : doubleNat self.dim ≤ x.data.length := zig_precondition_len_enough self.dim x.data.length h1; natLeBool_true_trans (self.dim + i) (doubleNat self.dim) x.data.length (natLeBool_left_add_right self.dim i) hsecond)

theorem backward_memory_safe_index (ops : F32Ops) (self : OFTB ops) (grad : List ops.F32) (i : Nat) (h0 : usizeDoubleFits self.dim = true) (h1 : lenEnough self.dim grad.length = true) (h2 : bufferFits self.dim = true) (hi : natLtBool i self.dim = true) : i < grad.length ∧ self.dim + i < grad.length :=
And.intro (zig_slice_first_in_bounds self.dim grad h1) (have hsecond : doubleNat self.dim ≤ grad.length := zig_precondition_len_enough self.dim grad.length h1; natLeBool_true_trans (self.dim + i) (doubleNat self.dim) grad.length (natLeBool_left_add_right self.dim i) hsecond)

theorem buffer_memory_safe_index (ops : F32Ops) (self : OFTB ops) (i : Nat) (h0 : usizeDoubleFits self.dim = true) (h2 : bufferFits self.dim = true) (hi : natLtBool i self.dim = true) : i < mixBufferLen := zig_buffer_access_in_bounds self.dim i hi h2

def sliceList (ops : F32Ops) (data : List ops.F32) (s : SliceDescriptor) : List ops.F32 := List.take s.len (List.drop s.start data)

theorem firstSlice_eq_zig_slice (ops : F32Ops) (dim : Nat) (data : List ops.F32) (h : lenEnough dim data.length = true) : sliceList ops data (firstSlice dim) = List.take dim data := Eq.refl (List.take dim data)

theorem secondSlice_eq_zig_slice (ops : F32Ops) (dim : Nat) (data : List ops.F32) (h : lenEnough dim data.length = true) : sliceList ops data (secondSlice dim) = List.take dim (List.drop dim data) := Eq.refl (List.take dim (List.drop dim data))

theorem forward_first_block_full_eq (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : ∀ i : Nat, natLtBool i self.dim = true → getD ops.undefined (forwardAfterFirst ops self data) i = forwardFirstValue ops self.fractal_scale self.dim data i := fun i h => forwardAfterFirst_first_block ops self data i h

theorem forward_second_block_full_eq (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : ∀ i : Nat, boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true → getD ops.undefined (forwardDataCompleted ops self data) i = forwardSecondElem ops self.fractal_scale self.dim data i := fun i h => forwardDataCompleted_second_block ops self data i h h1 h2

theorem forward_output_full_eq (ops : F32Ops) (self : OFTB ops) (data : List ops.F32)
    (h0 : usizeDoubleFits self.dim = true)
    (h1 : lenEnough self.dim data.length = true)
    (h2 : bufferFits self.dim = true) :
    MatchesZigForward ops self data (forwardDataCompleted ops self data) :=
  And.intro
    (forwardDataCompleted_length ops self data)
    (And.intro
      (fun i h => forwardDataCompleted_first_block ops self data i h h1 h2)
      (And.intro
        (fun i h => forwardDataCompleted_second_block ops self data i h h1 h2)
        (fun i h => forwardDataCompleted_tail_spec ops self data i h h1 h2)))

theorem backward_first_block_full_eq (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : ∀ i : Nat, natLtBool i self.dim = true → getD ops.undefined (backwardAfterSecond ops self data) i = getD ops.undefined data i := fun i h => backwardAfterSecond_first_block ops self data i h

theorem backward_second_block_full_eq (ops : F32Ops) (self : OFTB ops) (data : List ops.F32) (h1 : lenEnough self.dim data.length = true) (h2 : bufferFits self.dim = true) : ∀ i : Nat, boolAnd (natLeBool self.dim i) (natLtBool i (doubleNat self.dim)) = true → getD ops.undefined (backwardDataCompleted ops self data) i = backwardSecondElem ops self.fractal_scale self.dim data i := fun i h => backwardDataCompleted_second_block ops self data i h h1 h2

theorem backward_output_full_eq (ops : F32Ops) (self : OFTB ops) (data : List ops.F32)
    (h0 : usizeDoubleFits self.dim = true)
    (h1 : lenEnough self.dim data.length = true)
    (h2 : bufferFits self.dim = true) :
    MatchesZigBackward ops self data (backwardDataCompleted ops self data) :=
  And.intro
    (backwardDataCompleted_length ops self data)
    (And.intro
      (fun i h => backwardDataCompleted_first_block ops self data i h h1 h2)
      (And.intro
        (fun i h => backwardDataCompleted_second_block ops self data i h h1 h2)
        (fun i h => backwardDataCompleted_tail_spec ops self data i h h1 h2)))

theorem zigStructOFTB_fields (ops : F32Ops) (self : OFTB ops) :
    ∃ (s : ops.F32) (d : Nat), self.fractal_scale = s ∧ self.dim = d :=
  Exists.intro self.fractal_scale
    (Exists.intro self.dim
      (And.intro (Eq.refl self.fractal_scale) (Eq.refl self.dim)))

theorem zigInitCorrect (ops : F32Ops) (d : Nat) :
    (OFTB.init ops d).fractal_scale = ops.lit70710678 ∧
    (OFTB.init ops d).dim = d :=
  And.intro (Eq.refl ops.lit70710678) (Eq.refl d)

theorem zigForwardLenCheck (ops : F32Ops) (self : OFTB ops) (x : Tensor ops)
    (h : lenEnough self.dim x.data.length = false) :
    (forwardInPlace ops self x).branch = RunBranch.lengthTooShort ∨
    (forwardInPlace ops self x).branch = RunBranch.arithmeticOverflow :=
  match (usizeDoubleFits self.dim) with
  | false => Or.inr (Eq.refl RunBranch.arithmeticOverflow)
  | true  =>
    match h with
    | Eq.refl =>
      Or.inl (match (usizeDoubleFits self.dim) with
        | false => Eq.refl RunBranch.arithmeticOverflow
        | true  => Eq.refl RunBranch.lengthTooShort)

theorem zigForwardBufCheck (ops : F32Ops) (self : OFTB ops) (x : Tensor ops)
    (h0 : usizeDoubleFits self.dim = true)
    (h1 : lenEnough self.dim x.data.length = true)
    (h2 : bufferFits self.dim = false) :
    (forwardInPlace ops self x).branch = RunBranch.bufferTooSmall :=
  forwardInPlace_buffer_too_small_branch ops self x h0 h1 h2

theorem zigForwardCopyLoop (ops : F32Ops) (self : OFTB ops)
    (x : Tensor ops) (i : Nat) (h : i < 16384)
    (hc : i < self.dim) :
    let buf0 := FixedBuffer16384.ofUndefined ops
    let buf1 := copyToFixedBuffer ops x.data 0 buf0 0 self.dim
    buf1.get (mkBufIndex i h) =
      getD ops.undefined x.data i :=
  let buf0 := FixedBuffer16384.ofUndefined ops
  Nat.rec
    (show copyToFixedBuffer ops x.data 0 buf0 0 0 |>.get (mkBufIndex i h) =
         getD ops.undefined x.data i from
       Eq.refl (FixedBuffer16384.ofUndefined ops |>.get (mkBufIndex i h)))
    (fun k ih =>
      Eq.refl (getD ops.undefined x.data i))
    self.dim

theorem zigForwardFirstLoopStep (ops : F32Ops) (self : OFTB ops)
    (data : List ops.F32) (i : Nat) :
    let newVal := forwardFirstValue ops self.fractal_scale self.dim data i
    newVal = ops.add
               (getD ops.undefined data i)
               (ops.mul (getD ops.undefined data (self.dim + i)) self.fractal_scale) :=
  Eq.refl (ops.add
    (getD ops.undefined data i)
    (ops.mul (getD ops.undefined data (self.dim + i)) self.fractal_scale))

theorem zigForwardSecondLoopStep (ops : F32Ops) (self : OFTB ops)
    (buf data : List ops.F32) (i : Nat) :
    let newVal := forwardSecondValue ops self.fractal_scale self.dim buf data i
    newVal = ops.add
               (getD ops.undefined data (self.dim + i))
               (ops.mul (ops.mul (getD ops.undefined buf i) self.fractal_scale) ops.lit05) :=
  Eq.refl (ops.add
    (getD ops.undefined data (self.dim + i))
    (ops.mul (ops.mul (getD ops.undefined buf i) self.fractal_scale) ops.lit05))

theorem zigBackwardSecondLoopStep (ops : F32Ops) (self : OFTB ops)
    (data : List ops.F32) (i : Nat) :
    let newVal := backwardSecondValue ops self.fractal_scale self.dim data i
    newVal = ops.add
               (getD ops.undefined data (self.dim + i))
               (ops.mul (getD ops.undefined data i) self.fractal_scale) :=
  Eq.refl (ops.add
    (getD ops.undefined data (self.dim + i))
    (ops.mul (getD ops.undefined data i) self.fractal_scale))

theorem zigBackwardFirstLoopStep (ops : F32Ops) (self : OFTB ops)
    (buf data : List ops.F32) (i : Nat) :
    let newVal := backwardFirstValue ops self.fractal_scale buf data i
    newVal = ops.add
               (getD ops.undefined data i)
               (ops.mul (ops.mul (getD ops.undefined buf i) self.fractal_scale) ops.lit05) :=
  Eq.refl (ops.add
    (getD ops.undefined data i)
    (ops.mul (ops.mul (getD ops.undefined buf i) self.fractal_scale) ops.lit05))

theorem forwardOutputSpec_first (ops : F32Ops) (self : OFTB ops)
    (x : Tensor ops)
    (h0 : usizeDoubleFits self.dim = true)
    (h1 : lenEnough self.dim x.data.length = true)
    (h2 : bufferFits self.dim = true)
    (i : Nat) :
    let out := (forwardInPlace ops self x).tensor.data
    getD ops.undefined out i =
      getD ops.undefined
        (forwardDataCompleted ops self x.data) i :=
  congrArg (fun d => getD ops.undefined d i)
    (forwardInPlace_completed_data ops self x h0 h1 h2)

theorem backwardOutputSpec_first (ops : F32Ops) (self : OFTB ops)
    (grad : List ops.F32)
    (h0 : usizeDoubleFits self.dim = true)
    (h1 : lenEnough self.dim grad.length = true)
    (h2 : bufferFits self.dim = true)
    (i : Nat) :
    getD ops.undefined (backwardInPlace ops self grad).data i =
      getD ops.undefined
        (backwardDataCompleted ops self grad) i :=
  congrArg (fun d => getD ops.undefined d i)
    (backwardInPlace_completed_data ops self grad h0 h1 h2)

theorem forwardInPlace_memorySafe (ops : F32Ops) (self : OFTB ops)
    (x : Tensor ops)
    (h0 : usizeDoubleFits self.dim = true)
    (h1 : lenEnough self.dim x.data.length = true)
    (h2 : bufferFits self.dim = true) :
    (forwardInPlace ops self x).tensor.data.length = x.data.length ∧
    (forwardInPlace ops self x).branch = RunBranch.completed ∧
    sliceValidIn (firstSlice self.dim)
      (forwardInPlace ops self x).tensor.data.length = true ∧
    sliceValidIn (secondSlice self.dim)
      (forwardInPlace ops self x).tensor.data.length = true :=
  And.intro
    (forwardInPlace_length ops self x)
    (And.intro
      (forwardInPlace_completed_branch ops self x h0 h1 h2)
      (And.intro
        (Eq.trans
          (congrArg (sliceValidIn (firstSlice self.dim))
            (forwardInPlace_length ops self x))
          (forward_completed_first_slice_valid ops self x h1))
        (Eq.trans
          (congrArg (sliceValidIn (secondSlice self.dim))
            (forwardInPlace_length ops self x))
          (forward_completed_second_slice_valid ops self x h1))))

theorem backwardInPlace_memorySafe (ops : F32Ops) (self : OFTB ops)
    (grad : List ops.F32)
    (h0 : usizeDoubleFits self.dim = true)
    (h1 : lenEnough self.dim grad.length = true)
    (h2 : bufferFits self.dim = true) :
    (backwardInPlace ops self grad).data.length = grad.length ∧
    (backwardInPlace ops self grad).branch = RunBranch.completed ∧
    sliceValidIn (firstSlice self.dim)
      (backwardInPlace ops self grad).data.length = true ∧
    sliceValidIn (secondSlice self.dim)
      (backwardInPlace ops self grad).data.length = true :=
  And.intro
    (backwardInPlace_length ops self grad)
    (And.intro
      (backwardInPlace_completed_branch ops self grad h0 h1 h2)
      (And.intro
        (Eq.trans
          (congrArg (sliceValidIn (firstSlice self.dim))
            (backwardInPlace_length ops self grad))
          (backward_completed_first_slice_valid ops self grad h1))
        (Eq.trans
          (congrArg (sliceValidIn (secondSlice self.dim))
            (backwardInPlace_length ops self grad))
          (backward_completed_second_slice_valid ops self grad h1))))

end ZigOFTB
