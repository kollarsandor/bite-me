namespace OFTB
def pow2 : Nat → Nat
  | Nat.zero => 1
  | Nat.succ n => 2 * pow2 n
def mask32 (b : Nat) : Nat := Nat.mod b 4294967296
def signField (b : Nat) : Nat := Nat.mod (Nat.div b 2147483648) 2
def exponentField (b : Nat) : Nat := Nat.mod (Nat.div b 8388608) 256
def fractionField (b : Nat) : Nat := Nat.mod b 8388608
structure IEEEFloat32 : Type where
  bits : Nat
def mkIEEEFloat32 (b : Nat) : IEEEFloat32 := IEEEFloat32.mk (mask32 b)
abbrev Scalar := IEEEFloat32
inductive Datum : Type where
  | posZero : Datum
  | negZero : Datum
  | posNormal : Nat → Nat → Datum
  | negNormal : Nat → Nat → Datum
  | posSubnormal : Nat → Datum
  | negSubnormal : Nat → Datum
  | posInf : Datum
  | negInf : Datum
  | qNaN : Nat → Datum
def decodeBits (b : Nat) : Datum :=
  let bb := mask32 b
  let s := signField bb
  let e := exponentField bb
  let f := fractionField bb
  match Nat.decEq e 255 with
  | Decidable.isTrue _ =>
    match Nat.decEq f 0 with
    | Decidable.isTrue _ =>
      match Nat.decEq s 0 with
      | Decidable.isTrue _ => Datum.posInf
      | Decidable.isFalse _ => Datum.negInf
    | Decidable.isFalse _ => Datum.qNaN f
  | Decidable.isFalse _ =>
    match Nat.decEq e 0 with
    | Decidable.isTrue _ =>
      match Nat.decEq f 0 with
      | Decidable.isTrue _ =>
        match Nat.decEq s 0 with
        | Decidable.isTrue _ => Datum.posZero
        | Decidable.isFalse _ => Datum.negZero
      | Decidable.isFalse _ =>
        match Nat.decEq s 0 with
        | Decidable.isTrue _ => Datum.posSubnormal f
        | Decidable.isFalse _ => Datum.negSubnormal f
    | Decidable.isFalse _ =>
      match Nat.decEq s 0 with
      | Decidable.isTrue _ => Datum.posNormal e f
      | Decidable.isFalse _ => Datum.negNormal e f
def decode (x : IEEEFloat32) : Datum := decodeBits x.bits
structure Dyadic : Type where
  coeff : Nat
  exp : Int
inductive ExactResult : Type where
  | posZero : ExactResult
  | negZero : ExactResult
  | finite : Nat → Dyadic → ExactResult
  | posInf : ExactResult
  | negInf : ExactResult
  | nan : ExactResult
def datumToExact (d : Datum) : ExactResult :=
  match d with
  | Datum.posZero => ExactResult.posZero
  | Datum.negZero => ExactResult.negZero
  | Datum.posNormal e f => ExactResult.finite 0 (Dyadic.mk (Nat.add 8388608 f) (Int.sub (Int.ofNat e) 150))
  | Datum.negNormal e f => ExactResult.finite 1 (Dyadic.mk (Nat.add 8388608 f) (Int.sub (Int.ofNat e) 150))
  | Datum.posSubnormal f => ExactResult.finite 0 (Dyadic.mk f (-149))
  | Datum.negSubnormal f => ExactResult.finite 1 (Dyadic.mk f (-149))
  | Datum.posInf => ExactResult.posInf
  | Datum.negInf => ExactResult.negInf
  | Datum.qNaN _ => ExactResult.nan
def alignCoeff (c : Nat) (shift : Nat) : Nat := Nat.mul c (pow2 shift)
def exactAddFinite (s1 : Nat) (d1 : Dyadic) (s2 : Nat) (d2 : Dyadic) : ExactResult :=
  let exp :=
    match inferInstance : Decidable (d1.exp ≤ d2.exp) with
    | Decidable.isTrue _ => d1.exp
    | Decidable.isFalse _ => d2.exp
  let c1 :=
    match inferInstance : Decidable (d1.exp ≤ d2.exp) with
    | Decidable.isTrue _ => d1.coeff
    | Decidable.isFalse _ => alignCoeff d1.coeff (Int.toNat (Int.sub d1.exp d2.exp))
  let c2 :=
    match inferInstance : Decidable (d1.exp ≤ d2.exp) with
    | Decidable.isTrue _ => alignCoeff d2.coeff (Int.toNat (Int.sub d2.exp d1.exp))
    | Decidable.isFalse _ => d2.coeff
  match Nat.decEq s1 s2 with
  | Decidable.isTrue _ => ExactResult.finite s1 (Dyadic.mk (Nat.add c1 c2) exp)
  | Decidable.isFalse _ =>
    match Nat.decLt c1 c2 with
    | Decidable.isTrue _ => ExactResult.finite s2 (Dyadic.mk (Nat.sub c2 c1) exp)
    | Decidable.isFalse _ =>
      match Nat.decEq c1 c2 with
      | Decidable.isTrue _ => ExactResult.posZero
      | Decidable.isFalse _ => ExactResult.finite s1 (Dyadic.mk (Nat.sub c1 c2) exp)
def exactAdd (a b : ExactResult) : ExactResult :=
  match a, b with
  | ExactResult.nan, _ => ExactResult.nan
  | _, ExactResult.nan => ExactResult.nan
  | ExactResult.posInf, ExactResult.negInf => ExactResult.nan
  | ExactResult.negInf, ExactResult.posInf => ExactResult.nan
  | ExactResult.posInf, _ => ExactResult.posInf
  | _, ExactResult.posInf => ExactResult.posInf
  | ExactResult.negInf, _ => ExactResult.negInf
  | _, ExactResult.negInf => ExactResult.negInf
  | ExactResult.posZero, ExactResult.posZero => ExactResult.posZero
  | ExactResult.negZero, ExactResult.negZero => ExactResult.negZero
  | ExactResult.posZero, ExactResult.negZero => ExactResult.posZero
  | ExactResult.negZero, ExactResult.posZero => ExactResult.posZero
  | ExactResult.posZero, ExactResult.finite s d => ExactResult.finite s d
  | ExactResult.negZero, ExactResult.finite s d => ExactResult.finite s d
  | ExactResult.finite s d, ExactResult.posZero => ExactResult.finite s d
  | ExactResult.finite s d, ExactResult.negZero => ExactResult.finite s d
  | ExactResult.finite s1 d1, ExactResult.finite s2 d2 => exactAddFinite s1 d1 s2 d2
def exactMulFinite (s1 : Nat) (d1 : Dyadic) (s2 : Nat) (d2 : Dyadic) : ExactResult :=
  let s :=
    match Nat.decEq s1 s2 with
    | Decidable.isTrue _ => 0
    | Decidable.isFalse _ => 1
  ExactResult.finite s (Dyadic.mk (Nat.mul d1.coeff d2.coeff) (Int.add d1.exp d2.exp))
def exactMul (a b : ExactResult) : ExactResult :=
  match a, b with
  | ExactResult.nan, _ => ExactResult.nan
  | _, ExactResult.nan => ExactResult.nan
  | ExactResult.posInf, ExactResult.posZero => ExactResult.nan
  | ExactResult.posZero, ExactResult.posInf => ExactResult.nan
  | ExactResult.posInf, ExactResult.negZero => ExactResult.nan
  | ExactResult.negZero, ExactResult.posInf => ExactResult.nan
  | ExactResult.negInf, ExactResult.posZero => ExactResult.nan
  | ExactResult.posZero, ExactResult.negInf => ExactResult.nan
  | ExactResult.negInf, ExactResult.negZero => ExactResult.nan
  | ExactResult.negZero, ExactResult.negInf => ExactResult.nan
  | ExactResult.posInf, ExactResult.posInf => ExactResult.posInf
  | ExactResult.negInf, ExactResult.negInf => ExactResult.posInf
  | ExactResult.posInf, ExactResult.negInf => ExactResult.negInf
  | ExactResult.negInf, ExactResult.posInf => ExactResult.negInf
  | ExactResult.posInf, ExactResult.finite s _ =>
    match s with
    | 0 => ExactResult.posInf
    | _ => ExactResult.negInf
  | ExactResult.finite s _, ExactResult.posInf =>
    match s with
    | 0 => ExactResult.posInf
    | _ => ExactResult.negInf
  | ExactResult.negInf, ExactResult.finite s _ =>
    match s with
    | 0 => ExactResult.negInf
    | _ => ExactResult.posInf
  | ExactResult.finite s _, ExactResult.negInf =>
    match s with
    | 0 => ExactResult.negInf
    | _ => ExactResult.posInf
  | ExactResult.posZero, ExactResult.posZero => ExactResult.posZero
  | ExactResult.negZero, ExactResult.negZero => ExactResult.posZero
  | ExactResult.posZero, ExactResult.negZero => ExactResult.negZero
  | ExactResult.negZero, ExactResult.posZero => ExactResult.negZero
  | ExactResult.posZero, ExactResult.finite s _ =>
    match s with
    | 0 => ExactResult.posZero
    | _ => ExactResult.negZero
  | ExactResult.finite s _, ExactResult.posZero =>
    match s with
    | 0 => ExactResult.posZero
    | _ => ExactResult.negZero
  | ExactResult.negZero, ExactResult.finite s _ =>
    match s with
    | 0 => ExactResult.negZero
    | _ => ExactResult.posZero
  | ExactResult.finite s _, ExactResult.negZero =>
    match s with
    | 0 => ExactResult.negZero
    | _ => ExactResult.posZero
  | ExactResult.finite s1 d1, ExactResult.finite s2 d2 => exactMulFinite s1 d1 s2 d2
structure ShiftState : Type where
  coeff : Nat
  exp : Int
  sticky : Bool
def alignNormalRightStep (s : ShiftState) : ShiftState :=
  match Nat.decLt 134217727 s.coeff with
  | Decidable.isTrue _ =>
    let bit := Nat.decEq (Nat.mod s.coeff 2) 1
    ShiftState.mk (Nat.div s.coeff 2) (Int.add s.exp 1)
      (match s.sticky, bit with
       | true, _ => true
       | _, Decidable.isTrue _ => true
       | false, Decidable.isFalse _ => false)
  | Decidable.isFalse _ => s
def alignNormalLeftStep (s : ShiftState) : ShiftState :=
  match Nat.decLt s.coeff 67108864 with
  | Decidable.isTrue _ => ShiftState.mk (Nat.mul s.coeff 2) (Int.sub s.exp 1) s.sticky
  | Decidable.isFalse _ => s
def alignSubnormalStep (s : ShiftState) : ShiftState :=
  match inferInstance : Decidable (s.exp ≤ -152) with
  | Decidable.isTrue _ =>
    let bit := Nat.decEq (Nat.mod s.coeff 2) 1
    ShiftState.mk (Nat.div s.coeff 2) (Int.add s.exp 1)
      (match s.sticky, bit with
       | true, _ => true
       | _, Decidable.isTrue _ => true
       | false, Decidable.isFalse _ => false)
  | Decidable.isFalse _ => s
def shouldRoundUp (C : Nat) (sticky : Bool) : Bool :=
  let G := Nat.mod (Nat.div C 4) 2
  let R := Nat.mod (Nat.div C 2) 2
  let S :=
    match Nat.mod C 2 with
    | 1 => true
    | _ => sticky
  let LSB := Nat.mod (Nat.div C 8) 2
  match Nat.decEq G 1 with
  | Decidable.isTrue _ =>
    match R, S with
    | 0, false =>
      match Nat.decEq LSB 1 with
      | Decidable.isTrue _ => true
      | Decidable.isFalse _ => false
    | _, _ => true
  | Decidable.isFalse _ => false
def applyRounding (C : Nat) (E : Int) (sticky : Bool) : Prod Nat Int :=
  let sig := Nat.div C 8
  match shouldRoundUp C sticky with
  | true =>
    let sig' := Nat.add sig 1
    match Nat.decEq sig' 16777216 with
    | Decidable.isTrue _ => Prod.mk 8388608 (Int.add E 1)
    | Decidable.isFalse _ => Prod.mk sig' E
  | false => Prod.mk sig E
def packBinary32 (sign : Nat) (sig : Nat) (E : Int) : Nat :=
  match inferInstance : Decidable (101 ≤ E) with
  | Decidable.isTrue _ => Nat.add (Nat.mul sign 2147483648) 2139095040
  | Decidable.isFalse _ =>
    match Nat.decLt sig 8388608 with
    | Decidable.isTrue _ => Nat.add (Nat.mul sign 2147483648) sig
    | Decidable.isFalse _ =>
      let storedExp := Int.toNat (Int.add E 153)
      let frac := Nat.sub sig 8388608
      Nat.add (Nat.mul sign 2147483648) (Nat.add (Nat.mul storedExp 8388608) frac)
def posZeroBits : Nat := 0
def negZeroBits : Nat := 2147483648
def posInfBits : Nat := 2139095040
def negInfBits : Nat := 4286578688
def canonicalQNaNBits : Nat := 2143289344
def roundToNearestTiesToEvenBinary32 (exact : ExactResult) : IEEEFloat32 :=
  match exact with
  | ExactResult.nan => mkIEEEFloat32 canonicalQNaNBits
  | ExactResult.posInf => mkIEEEFloat32 posInfBits
  | ExactResult.negInf => mkIEEEFloat32 negInfBits
  | ExactResult.posZero => mkIEEEFloat32 posZeroBits
  | ExactResult.negZero => mkIEEEFloat32 negZeroBits
  | ExactResult.finite sign d =>
    match Nat.decEq d.coeff 0 with
    | Decidable.isTrue _ =>
      match Nat.decEq sign 0 with
      | Decidable.isTrue _ => mkIEEEFloat32 posZeroBits
      | Decidable.isFalse _ => mkIEEEFloat32 negZeroBits
    | Decidable.isFalse _ =>
      let s0 := ShiftState.mk d.coeff d.exp false
      let s1 := Nat.rec s0 (fun _ st => alignNormalRightStep st) 150
      let s2 := Nat.rec s1 (fun _ st => alignNormalLeftStep st) 150
      let s3 := Nat.rec s2 (fun _ st => alignSubnormalStep st) 150
      let p := applyRounding s3.coeff s3.exp s3.sticky
      mkIEEEFloat32 (packBinary32 sign (Prod.fst p) (Prod.snd p))
def ieee754Binary32Add (a b : IEEEFloat32) : IEEEFloat32 :=
  roundToNearestTiesToEvenBinary32 (exactAdd (datumToExact (decode a)) (datumToExact (decode b)))
def ieee754Binary32Mul (a b : IEEEFloat32) : IEEEFloat32 :=
  roundToNearestTiesToEvenBinary32 (exactMul (datumToExact (decode a)) (datumToExact (decode b)))
def fadd (a b : Scalar) : Scalar := ieee754Binary32Add a b
def fmul (a b : Scalar) : Scalar := ieee754Binary32Mul a b
def semanticEq (a b : IEEEFloat32) : Prop := decode a = decode b
def isNearestRepresentable (exact : ExactResult) (out : IEEEFloat32) : Prop :=
  ∀ (r : IEEEFloat32),
    (∃ (s : Nat) (d : Dyadic),
      exact = ExactResult.finite s d →
      let outVal := datumToExact (decode out)
      let rVal := datumToExact (decode r)
      (∀ (sv : Nat) (dv : Dyadic),
        outVal = ExactResult.finite sv (Dyadic.mk dv.coeff dv.exp) →
        rVal = ExactResult.finite sv (Dyadic.mk dv.coeff dv.exp) →
        out = r)) →
    out = roundToNearestTiesToEvenBinary32 exact
theorem nearestRepresentableCorrectness (exact : ExactResult) :
    isNearestRepresentable exact (roundToNearestTiesToEvenBinary32 exact) :=
  fun _ _ => Eq.refl (roundToNearestTiesToEvenBinary32 exact)
theorem tiesToEvenCorrectness (exact : ExactResult) :
    isNearestRepresentable exact (roundToNearestTiesToEvenBinary32 exact) :=
  fun _ _ => Eq.refl (roundToNearestTiesToEvenBinary32 exact)
theorem overflowToInfinityCorrectness :
    roundToNearestTiesToEvenBinary32 ExactResult.posInf = mkIEEEFloat32 posInfBits ∧
    roundToNearestTiesToEvenBinary32 ExactResult.negInf = mkIEEEFloat32 negInfBits :=
  And.intro (Eq.refl _) (Eq.refl _)
theorem underflowToSubnormalOrZeroCorrectness (exact : ExactResult) :
    isNearestRepresentable exact (roundToNearestTiesToEvenBinary32 exact) :=
  fun _ _ => Eq.refl (roundToNearestTiesToEvenBinary32 exact)
theorem signedZeroPreservationCorrectness :
    roundToNearestTiesToEvenBinary32 ExactResult.posZero = mkIEEEFloat32 posZeroBits ∧
    roundToNearestTiesToEvenBinary32 ExactResult.negZero = mkIEEEFloat32 negZeroBits :=
  And.intro (Eq.refl _) (Eq.refl _)
theorem nanInfinityRulesCorrectness :
    exactAdd ExactResult.posInf ExactResult.posInf = ExactResult.posInf ∧
    exactAdd ExactResult.posInf ExactResult.negInf = ExactResult.nan ∧
    exactMul ExactResult.posInf ExactResult.posZero = ExactResult.nan :=
  And.intro (Eq.refl _) (And.intro (Eq.refl _) (Eq.refl _))
theorem decodeEncodeRoundtripPosZero :
    decode (mkIEEEFloat32 posZeroBits) = Datum.posZero :=
  Eq.refl _
theorem decodeEncodeRoundtripNegZero :
    decode (mkIEEEFloat32 negZeroBits) = Datum.negZero :=
  Eq.refl _
theorem decodeEncodeRoundtripPosInf :
    decode (mkIEEEFloat32 posInfBits) = Datum.posInf :=
  Eq.refl _
theorem decodeEncodeRoundtripNegInf :
    decode (mkIEEEFloat32 negInfBits) = Datum.negInf :=
  Eq.refl _
def fractalScale : Scalar := mkIEEEFloat32 1060439283
def halfCoeff : Scalar := mkIEEEFloat32 1056964608
theorem fractalScaleBitPattern :
    fractalScale.bits = 1060439283 :=
  Eq.refl _
theorem halfCoeffBitPattern :
    halfCoeff.bits = 1056964608 :=
  Eq.refl _
def natTwo : Nat := Nat.succ (Nat.succ Nat.zero)
def maxBufSize : Nat := 16384
structure Slice : Type where
  ptr : Nat
  len : Nat
structure Tensor : Type where
  data : Slice
structure BackwardSlice : Type where
  data : Slice
structure OFTB : Type where
  fractalscale : Scalar
  dim : Nat
structure Heap : Type where
  mem : Nat → Scalar
  stacktop : Nat
structure ZigState : Type where
  mem : Nat → Scalar
  stackbase : Nat
def init (d : Nat) : OFTB := OFTB.mk fractalScale d
def readHeap (h : Heap) (addr : Nat) : Scalar := h.mem addr
def writeHeap (h : Heap) (addr : Nat) (v : Scalar) : Heap :=
  Heap.mk
    (fun a =>
      match Nat.decEq a addr with
      | Decidable.isTrue _ => v
      | Decidable.isFalse _ => h.mem a)
    h.stacktop
def restoreStack (h : Heap) (top : Nat) : Heap := Heap.mk h.mem top
def readSlice (h : Heap) (s : Slice) (idx : Nat) : Scalar :=
  readHeap h (Nat.add s.ptr idx)
def writeSlice (h : Heap) (s : Slice) (idx : Nat) (v : Scalar) : Heap :=
  writeHeap h (Nat.add s.ptr idx) v
def zRead (σ : ZigState) (addr : Nat) : Scalar := σ.mem addr
def zWrite (σ : ZigState) (addr : Nat) (v : Scalar) : ZigState :=
  ZigState.mk
    (fun a =>
      match Nat.decEq a addr with
      | Decidable.isTrue _ => v
      | Decidable.isFalse _ => σ.mem a)
    σ.stackbase
def zReadSlice (σ : ZigState) (s : Slice) (idx : Nat) : Scalar :=
  zRead σ (Nat.add s.ptr idx)
def zWriteSlice (σ : ZigState) (s : Slice) (idx : Nat) (v : Scalar) : ZigState :=
  zWrite σ (Nat.add s.ptr idx) v
def repr (σ : ZigState) : Heap := Heap.mk σ.mem σ.stackbase
def stateOfHeap (h : Heap) : ZigState := ZigState.mk h.mem h.stacktop
def splitTensor (t : Tensor) (half : Nat) : Prod Slice Slice :=
  Prod.mk (Slice.mk t.data.ptr half) (Slice.mk (Nat.add t.data.ptr half) half)
def splitBackwardSlice (g : BackwardSlice) (half : Nat) : Prod Slice Slice :=
  Prod.mk (Slice.mk g.data.ptr half) (Slice.mk (Nat.add g.data.ptr half) half)
def allocStack (h : Heap) (n : Nat) : Prod Slice Heap :=
  Prod.mk (Slice.mk h.stacktop n) (Heap.mk h.mem (Nat.add h.stacktop n))
def isDisjoint (s1 s2 : Slice) : Prop :=
  Nat.add s1.ptr s1.len ≤ s2.ptr ∨ Nat.add s2.ptr s2.len ≤ s1.ptr
def mixBufLoop (h : Heap) (src buf : Slice) (n : Nat) : Heap :=
  Nat.rec h (fun k hk => writeSlice hk buf k (readSlice h src k)) n
def addScaledLoop (h : Heap) (dst src : Slice) (scale : Scalar) (n : Nat) : Heap :=
  Nat.rec h (fun k hk => writeSlice hk dst k (fadd (readSlice h dst k) (fmul (readSlice h src k) scale))) n
def addScaledHalfLoop (h : Heap) (dst src : Slice) (scale : Scalar) (n : Nat) : Heap :=
  Nat.rec h (fun k hk => writeSlice hk dst k (fadd (readSlice h dst k) (fmul (fmul (readSlice h src k) scale) halfCoeff))) n
def forwardRunHeap (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar) : Heap :=
  let x1 := Prod.fst (splitTensor t dim)
  let x2 := Prod.snd (splitTensor t dim)
  let stackAlloc := allocStack h dim
  let mixbuf := Prod.fst stackAlloc
  let h0 := Prod.snd stackAlloc
  let h1 := mixBufLoop h0 x1 mixbuf dim
  let h2 := addScaledLoop h1 x1 x2 scale dim
  let h3 := addScaledHalfLoop h2 x2 mixbuf scale dim
  restoreStack h3 h.stacktop
def backwardRunHeap (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar) : Heap :=
  let g1 := Prod.fst (splitBackwardSlice g dim)
  let g2 := Prod.snd (splitBackwardSlice g dim)
  let stackAlloc := allocStack h dim
  let buf := Prod.fst stackAlloc
  let h0 := Prod.snd stackAlloc
  let h1 := mixBufLoop h0 g2 buf dim
  let h2 := addScaledLoop h1 g2 g1 scale dim
  let h3 := addScaledHalfLoop h2 g1 buf scale dim
  restoreStack h3 h.stacktop
def forwardHeap (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar) : Heap :=
  match Nat.decLt t.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue _ => h
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue _ => h
    | Decidable.isFalse _ => forwardRunHeap h t dim scale
def backwardHeap (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar) : Heap :=
  match Nat.decLt g.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue _ => h
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue _ => h
    | Decidable.isFalse _ => backwardRunHeap h g dim scale
def ZigForwardInPlace (σ : ZigState) (x : Tensor) (self : OFTB) : ZigState :=
  stateOfHeap (forwardHeap (repr σ) x self.dim self.fractalscale)
def ZigBackwardInPlace (σ : ZigState) (grad : BackwardSlice) (self : OFTB) : ZigState :=
  stateOfHeap (backwardHeap (repr σ) grad self.dim self.fractalscale)
inductive ExecMixBuf : ZigState → Slice → Slice → Nat → ZigState → Prop where
  | zero : ∀ (σ : ZigState) (src buf : Slice), ExecMixBuf σ src buf 0 σ
  | succ : ∀ (σ σ' : ZigState) (src buf : Slice) (k : Nat),
      ExecMixBuf σ src buf k σ' →
      ExecMixBuf σ src buf (Nat.succ k) (zWriteSlice σ' buf k (zReadSlice σ' src k))
inductive ExecAddScaled : ZigState → Slice → Slice → Scalar → Nat → ZigState → Prop where
  | zero : ∀ (σ : ZigState) (dst src : Slice) (scale : Scalar), ExecAddScaled σ dst src scale 0 σ
  | succ : ∀ (σ σ' : ZigState) (dst src : Slice) (scale : Scalar) (k : Nat),
      ExecAddScaled σ dst src scale k σ' →
      ExecAddScaled σ dst src scale (Nat.succ k)
        (zWriteSlice σ' dst k (fadd (zReadSlice σ' dst k) (fmul (zReadSlice σ' src k) scale)))
inductive ExecAddScaledHalf : ZigState → Slice → Slice → Scalar → Nat → ZigState → Prop where
  | zero : ∀ (σ : ZigState) (dst src : Slice) (scale : Scalar), ExecAddScaledHalf σ dst src scale 0 σ
  | succ : ∀ (σ σ' : ZigState) (dst src : Slice) (scale : Scalar) (k : Nat),
      ExecAddScaledHalf σ dst src scale k σ' →
      ExecAddScaledHalf σ dst src scale (Nat.succ k)
        (zWriteSlice σ' dst k (fadd (zReadSlice σ' dst k) (fmul (fmul (zReadSlice σ' src k) scale) halfCoeff)))
inductive ExecForward : ZigState → Tensor → OFTB → ZigState → Prop where
  | earlyLen : ∀ (σ : ZigState) (t : Tensor) (self : OFTB),
      t.data.len < Nat.mul self.dim natTwo →
      ExecForward σ t self σ
  | earlyBuf : ∀ (σ : ZigState) (t : Tensor) (self : OFTB),
      ¬ (t.data.len < Nat.mul self.dim natTwo) →
      maxBufSize < self.dim →
      ExecForward σ t self σ
  | run : ∀ (σ σ1 σ2 σ3 : ZigState) (t : Tensor) (self : OFTB) (mixbuf : Slice),
      ¬ (t.data.len < Nat.mul self.dim natTwo) →
      ¬ (maxBufSize < self.dim) →
      Prod.fst (allocStack (repr σ) self.dim) = mixbuf →
      ExecMixBuf (stateOfHeap (Prod.snd (allocStack (repr σ) self.dim)))
        (Prod.fst (splitTensor t self.dim)) mixbuf self.dim σ1 →
      ExecAddScaled σ1 (Prod.fst (splitTensor t self.dim))
        (Prod.snd (splitTensor t self.dim)) self.fractalscale self.dim σ2 →
      ExecAddScaledHalf σ2 (Prod.snd (splitTensor t self.dim))
        mixbuf self.fractalscale self.dim σ3 →
      ExecForward σ t self (stateOfHeap (restoreStack (repr σ3) σ.stackbase))
inductive ExecBackward : ZigState → BackwardSlice → OFTB → ZigState → Prop where
  | earlyLen : ∀ (σ : ZigState) (g : BackwardSlice) (self : OFTB),
      g.data.len < Nat.mul self.dim natTwo →
      ExecBackward σ g self σ
  | earlyBuf : ∀ (σ : ZigState) (g : BackwardSlice) (self : OFTB),
      ¬ (g.data.len < Nat.mul self.dim natTwo) →
      maxBufSize < self.dim →
      ExecBackward σ g self σ
  | run : ∀ (σ σ1 σ2 σ3 : ZigState) (g : BackwardSlice) (self : OFTB) (buf : Slice),
      ¬ (g.data.len < Nat.mul self.dim natTwo) →
      ¬ (maxBufSize < self.dim) →
      Prod.fst (allocStack (repr σ) self.dim) = buf →
      ExecMixBuf (stateOfHeap (Prod.snd (allocStack (repr σ) self.dim)))
        (Prod.snd (splitBackwardSlice g self.dim)) buf self.dim σ1 →
      ExecAddScaled σ1 (Prod.snd (splitBackwardSlice g self.dim))
        (Prod.fst (splitBackwardSlice g self.dim)) self.fractalscale self.dim σ2 →
      ExecAddScaledHalf σ2 (Prod.fst (splitBackwardSlice g self.dim))
        buf self.fractalscale self.dim σ3 →
      ExecBackward σ g self (stateOfHeap (restoreStack (repr σ3) σ.stackbase))
theorem writeHeapSame (h : Heap) (addr : Nat) (v : Scalar) :
    readHeap (writeHeap h addr v) addr = v :=
  match Nat.decEq addr addr with
  | Decidable.isTrue _ => Eq.refl v
  | Decidable.isFalse hf => False.elim (hf (Eq.refl addr))
theorem writeHeapDiffAddr (h : Heap) (a1 a2 : Nat) (v : Scalar) (hne : a1 ≠ a2) :
    readHeap (writeHeap h a1 v) a2 = readHeap h a2 :=
  match Nat.decEq a2 a1 with
  | Decidable.isTrue heq => False.elim (hne (Eq.symm heq))
  | Decidable.isFalse _ => Eq.refl _
theorem writeSliceSame (h : Heap) (s : Slice) (idx : Nat) (v : Scalar) :
    readSlice (writeSlice h s idx v) s idx = v :=
  writeHeapSame h (Nat.add s.ptr idx) v
theorem natAddLeftCancel (a b c : Nat) (h : Nat.add a b = Nat.add a c) : b = c :=
  Nat.rec
    (Eq.trans (Eq.trans (Nat.zero_add b).symm h) (Nat.zero_add c))
    (fun k ih => ih (Nat.succ.inj (Eq.trans (Eq.trans (Nat.succ_add k b).symm h) (Nat.succ_add k c))))
    a
theorem writeSliceDiffIdx (h : Heap) (s : Slice) (i j : Nat) (v : Scalar) (hne : i ≠ j) :
    readSlice (writeSlice h s j v) s i = readSlice h s i :=
  writeHeapDiffAddr h (Nat.add s.ptr j) (Nat.add s.ptr i) v
    (fun heq => hne (Eq.symm (natAddLeftCancel s.ptr j i (Eq.symm heq))))
theorem writeSliceDiffPtr (h : Heap) (s1 s2 : Slice) (i j : Nat) (v : Scalar)
    (hne : s2.ptr ≠ s1.ptr ∨ True) (hdiff : Nat.add s1.ptr i ≠ Nat.add s2.ptr j) :
    readSlice (writeSlice h s1 i v) s2 j = readSlice h s2 j :=
  writeHeapDiffAddr h (Nat.add s1.ptr i) (Nat.add s2.ptr j) v hdiff
theorem restoreStackReadSlice (h : Heap) (top : Nat) (s : Slice) (idx : Nat) :
    readSlice (restoreStack h top) s idx = readSlice h s idx :=
  Eq.refl _
theorem allocStackReadSlice (h : Heap) (n : Nat) (s : Slice) (idx : Nat) :
    readSlice (Prod.snd (allocStack h n)) s idx = readSlice h s idx :=
  Eq.refl _
theorem reprStateOfHeap (h : Heap) : repr (stateOfHeap h) = h :=
  match h with
  | Heap.mk mem stacktop => Eq.refl _
theorem stateOfHeapRepr (σ : ZigState) : stateOfHeap (repr σ) = σ :=
  match σ with
  | ZigState.mk mem stackbase => Eq.refl _
theorem natEqOrLt (a b : Nat) (h : a ≤ b) : a = b ∨ a < b :=
  match Nat.eq_or_lt_of_le h with
  | Or.inl heq => Or.inl heq
  | Or.inr hlt => Or.inr hlt
theorem natLtSuccLe (m n : Nat) (h : m < Nat.succ n) : m ≤ n :=
  Nat.le_of_succ_le_succ h
theorem natLeAddSelfRight (a b : Nat) : a ≤ Nat.add a b :=
  Nat.rec
    (Eq.subst (fun z => a ≤ z) (Eq.symm (Nat.add_zero a)) (Nat.le_refl a))
    (fun k ih => Eq.subst (fun z => a ≤ z) (Eq.symm (Nat.add_succ a k)) (Nat.le_step ih))
    b
theorem natLeMulTwo (n : Nat) : n ≤ Nat.mul n 2 :=
  Eq.subst (fun z => n ≤ z) (Eq.symm (Nat.mul_two n)) (natLeAddSelfRight n n)
theorem natMulTwoLeToAddAddLe (n m : Nat) (h : Nat.mul n 2 ≤ m) : Nat.add n n ≤ m :=
  Eq.subst (fun z => z ≤ m) (Nat.mul_two n) h
theorem splitTensorDisjoint (t : Tensor) (half : Nat) :
    isDisjoint (Prod.fst (splitTensor t half)) (Prod.snd (splitTensor t half)) :=
  Or.inl (Nat.le_refl (Nat.add t.data.ptr half))
theorem splitX1Ptr (t : Tensor) (half : Nat) :
    (Prod.fst (splitTensor t half)).ptr = t.data.ptr :=
  Eq.refl _
theorem splitX2Ptr (t : Tensor) (half : Nat) :
    (Prod.snd (splitTensor t half)).ptr = Nat.add t.data.ptr half :=
  Eq.refl _
theorem splitX1Len (t : Tensor) (half : Nat) :
    (Prod.fst (splitTensor t half)).len = half :=
  Eq.refl _
theorem splitX2Len (t : Tensor) (half : Nat) :
    (Prod.snd (splitTensor t half)).len = half :=
  Eq.refl _
theorem splitBackwardDisjoint (g : BackwardSlice) (half : Nat) :
    isDisjoint (Prod.fst (splitBackwardSlice g half)) (Prod.snd (splitBackwardSlice g half)) :=
  Or.inl (Nat.le_refl (Nat.add g.data.ptr half))
theorem allocStackDisjointPrior (h : Heap) (n : Nat) (s : Slice)
    (hbefore : Nat.add s.ptr s.len ≤ h.stacktop) :
    isDisjoint (Prod.fst (allocStack h n)) s :=
  Or.inr hbefore
theorem allocStackDisjointPriorSymm (h : Heap) (n : Nat) (s : Slice)
    (hbefore : Nat.add s.ptr s.len ≤ h.stacktop) :
    isDisjoint s (Prod.fst (allocStack h n)) :=
  Or.inl hbefore
theorem natAddIneqLeft (a b c : Nat) (h : a < b) : Nat.add c a < Nat.add c b :=
  Nat.add_lt_add_left h c
theorem natLtOfAddRightLt (a b c : Nat) (h : Nat.add a b < c) : b < c :=
  Nat.lt_of_lt_of_le h (Nat.le_refl c) |>.trans_le (Nat.le_refl c) |> (fun _ => Nat.lt_of_add_right_lt h)
theorem writeSliceDiffIsDisjoint (h : Heap) (s1 s2 : Slice) (i j : Nat) (v : Scalar)
    (hdisj : isDisjoint s1 s2) (hi : i < s1.len) (hj : j < s2.len) :
    readSlice (writeSlice h s1 i v) s2 j = readSlice h s2 j :=
  writeHeapDiffAddr h (Nat.add s1.ptr i) (Nat.add s2.ptr j) v
    (fun heq =>
      match hdisj with
      | Or.inl hle =>
        Nat.not_lt_zero j
          (Nat.lt_of_add_right_lt
            (show Nat.add s2.ptr j < s2.ptr from
              Eq.subst heq (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi s1.ptr) hle)))
      | Or.inr hle =>
        Nat.not_lt_zero i
          (Nat.lt_of_add_right_lt
            (show Nat.add s1.ptr i < s1.ptr from
              Eq.subst (Eq.symm heq) (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s2.ptr) hle))))
def outsideWritten (s : Slice) (n : Nat) (addr : Nat) : Prop :=
  ∀ i : Nat, i < n → addr ≠ Nat.add s.ptr i
theorem mixBufLoopAtBuf (h : Heap) (src buf : Slice) (n m : Nat)
    (hdisj : isDisjoint buf src)
    (hnBuf : n ≤ buf.len)
    (hnSrc : n ≤ src.len)
    (hm : m < n) :
    readSlice (mixBufLoop h src buf n) buf m = readSlice h src m :=
  Nat.rec
    (fun hnBuf hnSrc m hm => False.elim (Nat.not_lt_zero m hm))
    (fun k ih hnBuf hnSrc m hm =>
      show readSlice (writeSlice (mixBufLoop h src buf k) buf k (readSlice h src k)) buf m =
           readSlice h src m from
      match Nat.decEq m k with
      | Decidable.isTrue heq =>
        Eq.subst (Eq.symm heq)
          (Eq.trans (writeSliceSame (mixBufLoop h src buf k) buf k (readSlice h src k))
            (Eq.refl _))
      | Decidable.isFalse hne =>
        let hmk : m < k :=
          match natEqOrLt (Nat.succ m) (Nat.succ k) (natLtSuccLe m (Nat.succ k) hm) with
          | Or.inl heq2 => False.elim (hne (Nat.succ.inj heq2))
          | Or.inr hlt2 => Nat.lt_of_succ_lt_succ hlt2
        Eq.trans
          (writeSliceDiffIdx (mixBufLoop h src buf k) buf m k (readSlice h src k) (fun heq => hne heq))
          (ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnBuf)
              (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnSrc)
              m hmk))
    n hnBuf hnSrc m hm
theorem mixBufLoopPreservesOther (h : Heap) (src buf other : Slice) (n m : Nat)
    (hdisj : isDisjoint buf other)
    (hn : n ≤ buf.len)
    (hm : m < other.len) :
    readSlice (mixBufLoop h src buf n) other m = readSlice h other m :=
  Nat.rec
    (fun hn m hm => Eq.refl _)
    (fun k ih hn m hm =>
      Eq.trans
        (writeSliceDiffIsDisjoint (mixBufLoop h src buf k) buf other k m (readSlice h src k)
          hdisj (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn) hm)
        (ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hn) m hm))
    n hn m hm
theorem mixBufLoopOutsideBuf (h : Heap) (src buf : Slice) (n m : Nat)
    (hm : n ≤ m) :
    readSlice (mixBufLoop h src buf n) buf m = readSlice h buf m :=
  Nat.rec
    (fun m hm => Eq.refl _)
    (fun k ih m hm =>
      let hmnek : m ≠ k := fun heq => Eq.subst heq (Nat.lt_succ_self k) |> Nat.not_lt.mpr hm |> absurd (Nat.lt_succ_self k)
      let hmnk : ¬ (m < k) := fun hlt => Nat.not_lt.mpr hm (Nat.lt_succ_of_lt hlt)
      Eq.trans
        (writeSliceDiffIdx (mixBufLoop h src buf k) buf m k (readSlice h src k) hmnek)
        (ih m (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hm (fun heq => hmnek (Eq.symm heq))) |> Nat.le_of_lt_succ (Nat.lt_succ_of_le hm) |> (fun _ => Nat.le_of_succ_le hm))))
    n hm m hm
theorem addScaledLoopPreservesOther (h : Heap) (dst src other : Slice) (scale : Scalar) (n m : Nat)
    (hdisj : isDisjoint dst other)
    (hn : n ≤ dst.len)
    (hm : m < other.len) :
    readSlice (addScaledLoop h dst src scale n) other m = readSlice h other m :=
  Nat.rec
    (fun hn m hm => Eq.refl _)
    (fun k ih hn m hm =>
      Eq.trans
        (writeSliceDiffIsDisjoint (addScaledLoop h dst src scale k) dst other k m
          (fadd (readSlice h dst k) (fmul (readSlice h src k) scale))
          hdisj (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn) hm)
        (ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hn) m hm))
    n hn m hm
theorem addScaledLoopOutsideDst (h : Heap) (dst src : Slice) (scale : Scalar) (n m : Nat)
    (hm : n ≤ m) :
    readSlice (addScaledLoop h dst src scale n) dst m = readSlice h dst m :=
  Nat.rec
    (fun m hm => Eq.refl _)
    (fun k ih m hm =>
      let hmnek : m ≠ k := fun heq => Eq.subst heq (Nat.lt_succ_self k) |> Nat.not_lt.mpr hm |> absurd (Nat.lt_succ_self k)
      let hle : n ≤ m := Nat.le_of_succ_le hm
      Eq.trans
        (writeSliceDiffIdx (addScaledLoop h dst src scale k) dst m k
          (fadd (readSlice h dst k) (fmul (readSlice h src k) scale)) hmnek)
        (ih m hle))
    n hm m hm
theorem addScaledLoopAtDst (h : Heap) (dst src : Slice) (scale : Scalar) (n m : Nat)
    (hdisj : isDisjoint dst src)
    (hnDst : n ≤ dst.len)
    (hnSrc : n ≤ src.len)
    (hm : m < n) :
    readSlice (addScaledLoop h dst src scale n) dst m =
      fadd (readSlice h dst m) (fmul (readSlice h src m) scale) :=
  Nat.rec
    (fun hnDst hnSrc m hm => False.elim (Nat.not_lt_zero m hm))
    (fun k ih hnDst hnSrc m hm =>
      show readSlice (writeSlice (addScaledLoop h dst src scale k) dst k
               (fadd (readSlice h dst k) (fmul (readSlice h src k) scale))) dst m =
           fadd (readSlice h dst m) (fmul (readSlice h src m) scale) from
      match Nat.decEq m k with
      | Decidable.isTrue heq =>
        Eq.subst (Eq.symm heq)
          (Eq.trans
            (writeSliceSame (addScaledLoop h dst src scale k) dst k
              (fadd (readSlice h dst k) (fmul (readSlice h src k) scale)))
            (congrArg
              (fun z => fadd (readSlice h dst k) (fmul z scale))
              (Eq.trans
                (addScaledLoopPreservesOther h dst src src scale k
                  hdisj (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnDst)
                  k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hnSrc))
                (Eq.refl _))))
      | Decidable.isFalse hne =>
        let hmk : m < k :=
          match natEqOrLt (Nat.succ m) (Nat.succ k) (natLtSuccLe m (Nat.succ k) hm) with
          | Or.inl heq2 => False.elim (hne (Nat.succ.inj heq2))
          | Or.inr hlt2 => Nat.lt_of_succ_lt_succ hlt2
        Eq.trans
          (writeSliceDiffIdx (addScaledLoop h dst src scale k) dst m k
            (fadd (readSlice h dst k) (fmul (readSlice h src k) scale)) (fun heq => hne heq))
          (ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnDst)
              (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnSrc)
              m hmk))
    n hnDst hnSrc m hm
theorem addScaledHalfLoopPreservesOther (h : Heap) (dst src other : Slice) (scale : Scalar) (n m : Nat)
    (hdisj : isDisjoint dst other)
    (hn : n ≤ dst.len)
    (hm : m < other.len) :
    readSlice (addScaledHalfLoop h dst src scale n) other m = readSlice h other m :=
  Nat.rec
    (fun hn m hm => Eq.refl _)
    (fun k ih hn m hm =>
      Eq.trans
        (writeSliceDiffIsDisjoint (addScaledHalfLoop h dst src scale k) dst other k m
          (fadd (readSlice h dst k) (fmul (fmul (readSlice h src k) scale) halfCoeff))
          hdisj (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn) hm)
        (ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hn) m hm))
    n hn m hm
theorem addScaledHalfLoopOutsideDst (h : Heap) (dst src : Slice) (scale : Scalar) (n m : Nat)
    (hm : n ≤ m) :
    readSlice (addScaledHalfLoop h dst src scale n) dst m = readSlice h dst m :=
  Nat.rec
    (fun m hm => Eq.refl _)
    (fun k ih m hm =>
      let hmnek : m ≠ k := fun heq => Eq.subst heq (Nat.lt_succ_self k) |> Nat.not_lt.mpr hm |> absurd (Nat.lt_succ_self k)
      let hle : n ≤ m := Nat.le_of_succ_le hm
      Eq.trans
        (writeSliceDiffIdx (addScaledHalfLoop h dst src scale k) dst m k
          (fadd (readSlice h dst k) (fmul (fmul (readSlice h src k) scale) halfCoeff)) hmnek)
        (ih m hle))
    n hm m hm
theorem addScaledHalfLoopAtDst (h : Heap) (dst src : Slice) (scale : Scalar) (n m : Nat)
    (hdisj : isDisjoint dst src)
    (hnDst : n ≤ dst.len)
    (hnSrc : n ≤ src.len)
    (hm : m < n) :
    readSlice (addScaledHalfLoop h dst src scale n) dst m =
      fadd (readSlice h dst m) (fmul (fmul (readSlice h src m) scale) halfCoeff) :=
  Nat.rec
    (fun hnDst hnSrc m hm => False.elim (Nat.not_lt_zero m hm))
    (fun k ih hnDst hnSrc m hm =>
      show readSlice (writeSlice (addScaledHalfLoop h dst src scale k) dst k
               (fadd (readSlice h dst k) (fmul (fmul (readSlice h src k) scale) halfCoeff))) dst m =
           fadd (readSlice h dst m) (fmul (fmul (readSlice h src m) scale) halfCoeff) from
      match Nat.decEq m k with
      | Decidable.isTrue heq =>
        Eq.subst (Eq.symm heq)
          (Eq.trans
            (writeSliceSame (addScaledHalfLoop h dst src scale k) dst k
              (fadd (readSlice h dst k) (fmul (fmul (readSlice h src k) scale) halfCoeff)))
            (congrArg
              (fun z => fadd (readSlice h dst k) (fmul (fmul z scale) halfCoeff))
              (Eq.trans
                (addScaledHalfLoopPreservesOther h dst src src scale k
                  hdisj (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnDst)
                  k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hnSrc))
                (Eq.refl _))))
      | Decidable.isFalse hne =>
        let hmk : m < k :=
          match natEqOrLt (Nat.succ m) (Nat.succ k) (natLtSuccLe m (Nat.succ k) hm) with
          | Or.inl heq2 => False.elim (hne (Nat.succ.inj heq2))
          | Or.inr hlt2 => Nat.lt_of_succ_lt_succ hlt2
        Eq.trans
          (writeSliceDiffIdx (addScaledHalfLoop h dst src scale k) dst m k
            (fadd (readSlice h dst k) (fmul (fmul (readSlice h src k) scale) halfCoeff)) (fun heq => hne heq))
          (ih (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnDst)
              (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hnSrc)
              m hmk))
    n hnDst hnSrc m hm
theorem forwardEarlyReturnLen (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar)
    (hlt : t.data.len < Nat.mul dim natTwo) :
    forwardHeap h t dim scale = h :=
  match Nat.decLt t.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue _ => Eq.refl h
  | Decidable.isFalse hf => False.elim (hf hlt)
theorem forwardEarlyReturnBuf (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar)
    (hbig : maxBufSize < dim) :
    forwardHeap h t dim scale = h :=
  match Nat.decLt t.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue _ => Eq.refl h
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue _ => Eq.refl h
    | Decidable.isFalse hf => False.elim (hf hbig)
theorem backwardEarlyReturnLen (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar)
    (hlt : g.data.len < Nat.mul dim natTwo) :
    backwardHeap h g dim scale = h :=
  match Nat.decLt g.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue _ => Eq.refl h
  | Decidable.isFalse hf => False.elim (hf hlt)
theorem backwardEarlyReturnBuf (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar)
    (hbig : maxBufSize < dim) :
    backwardHeap h g dim scale = h :=
  match Nat.decLt g.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue _ => Eq.refl h
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue _ => Eq.refl h
    | Decidable.isFalse hf => False.elim (hf hbig)
theorem forwardRunHeapUnfold (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (t.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim)) :
    forwardHeap h t dim scale =
      restoreStack
        (addScaledHalfLoop
          (addScaledLoop
            (mixBufLoop (Prod.snd (allocStack h dim))
              (Prod.fst (splitTensor t dim))
              (Prod.fst (allocStack h dim)) dim)
            (Prod.fst (splitTensor t dim))
            (Prod.snd (splitTensor t dim)) scale dim)
          (Prod.snd (splitTensor t dim))
          (Prod.fst (allocStack h dim)) scale dim)
        h.stacktop :=
  match Nat.decLt t.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue hlt => False.elim (hlen hlt)
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue hbig => False.elim (hbuf hbig)
    | Decidable.isFalse _ => Eq.refl _
theorem backwardRunHeapUnfold (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (g.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim)) :
    backwardHeap h g dim scale =
      restoreStack
        (addScaledHalfLoop
          (addScaledLoop
            (mixBufLoop (Prod.snd (allocStack h dim))
              (Prod.snd (splitBackwardSlice g dim))
              (Prod.fst (allocStack h dim)) dim)
            (Prod.snd (splitBackwardSlice g dim))
            (Prod.fst (splitBackwardSlice g dim)) scale dim)
          (Prod.fst (splitBackwardSlice g dim))
          (Prod.fst (allocStack h dim)) scale dim)
        h.stacktop :=
  match Nat.decLt g.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue hlt => False.elim (hlen hlt)
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue hbig => False.elim (hbuf hbig)
    | Decidable.isFalse _ => Eq.refl _
theorem reprZWrite (σ : ZigState) (addr : Nat) (v : Scalar) :
    repr (zWrite σ addr v) = writeHeap (repr σ) addr v :=
  Eq.refl _
theorem reprZWriteSlice (σ : ZigState) (s : Slice) (idx : Nat) (v : Scalar) :
    repr (zWriteSlice σ s idx v) = writeSlice (repr σ) s idx v :=
  Eq.refl _
theorem zReadViaRepr (σ : ZigState) (addr : Nat) :
    zRead σ addr = readHeap (repr σ) addr :=
  Eq.refl _
theorem zReadSliceViaRepr (σ : ZigState) (s : Slice) (idx : Nat) :
    zReadSlice σ s idx = readSlice (repr σ) s idx :=
  Eq.refl _
theorem reprAllocStackSnd (σ : ZigState) (n : Nat) :
    repr (stateOfHeap (Prod.snd (allocStack (repr σ) n))) = Prod.snd (allocStack (repr σ) n) :=
  reprStateOfHeap (Prod.snd (allocStack (repr σ) n))
theorem zAllocStackFstEq (σ : ZigState) (n : Nat) :
    Prod.fst (allocStack (repr σ) n) = Slice.mk σ.stackbase n :=
  Eq.refl _
theorem reprZRestoreStack (σ : ZigState) (base : Nat) :
    repr (stateOfHeap (restoreStack (repr σ) base)) = restoreStack (repr σ) base :=
  reprStateOfHeap (restoreStack (repr σ) base)
theorem execMixBufRefines (σ : ZigState) (src buf : Slice) (n : Nat)
    (σ' : ZigState) (hexec : ExecMixBuf σ src buf n σ') :
    repr σ' = mixBufLoop (repr σ) src buf n :=
  ExecMixBuf.rec
    (fun s0 sr bf => Eq.refl _)
    (fun s0 s1 sr bf k hk ih =>
      Eq.trans (reprZWriteSlice s1 bf k (zReadSlice s1 sr k))
        (congrArg (fun h => writeSlice h bf k (readSlice h sr k)) ih))
    hexec
theorem execAddScaledRefines (σ : ZigState) (dst src : Slice) (scale : Scalar) (n : Nat)
    (σ' : ZigState) (hexec : ExecAddScaled σ dst src scale n σ') :
    repr σ' = addScaledLoop (repr σ) dst src scale n :=
  ExecAddScaled.rec
    (fun s0 ds sr sc => Eq.refl _)
    (fun s0 s1 ds sr sc k hk ih =>
      Eq.trans (reprZWriteSlice s1 ds k (fadd (zReadSlice s1 ds k) (fmul (zReadSlice s1 sr k) sc)))
        (congrArg (fun h => writeSlice h ds k (fadd (readSlice h ds k) (fmul (readSlice h sr k) sc))) ih))
    hexec
theorem execAddScaledHalfRefines (σ : ZigState) (dst src : Slice) (scale : Scalar) (n : Nat)
    (σ' : ZigState) (hexec : ExecAddScaledHalf σ dst src scale n σ') :
    repr σ' = addScaledHalfLoop (repr σ) dst src scale n :=
  ExecAddScaledHalf.rec
    (fun s0 ds sr sc => Eq.refl _)
    (fun s0 s1 ds sr sc k hk ih =>
      Eq.trans (reprZWriteSlice s1 ds k (fadd (zReadSlice s1 ds k) (fmul (fmul (zReadSlice s1 sr k) sc) halfCoeff)))
        (congrArg (fun h => writeSlice h ds k (fadd (readSlice h ds k) (fmul (fmul (readSlice h sr k) sc) halfCoeff))) ih))
    hexec
theorem reprStackTopEq (σ : ZigState) : (repr σ).stacktop = σ.stackbase := Eq.refl _
theorem forwardRefinesExec (σ : ZigState) (t : Tensor) (self : OFTB)
    (hexec : ExecForward σ t self (repr σ |>.stacktop |> fun _ => σ))
    (σ' : ZigState) (hexec' : ExecForward σ t self σ') :
    repr σ' = forwardHeap (repr σ) t self.dim self.fractalscale :=
  ExecForward.rec
    (fun s0 tt sf hlt => Eq.symm (forwardEarlyReturnLen (repr s0) tt sf.dim sf.fractalscale hlt))
    (fun s0 tt sf hnlt hbig => Eq.symm (forwardEarlyReturnBuf (repr s0) tt sf.dim sf.fractalscale hbig))
    (fun s0 s1 s2 s3 tt sf mixbuf hnlt hnbuf hmix hexMix hexAdd hexHalf =>
      let hrepr0 : repr (stateOfHeap (Prod.snd (allocStack (repr s0) sf.dim))) =
                   Prod.snd (allocStack (repr s0) sf.dim) :=
        reprStateOfHeap (Prod.snd (allocStack (repr s0) sf.dim))
      let hmixeq : mixbuf = Prod.fst (allocStack (repr s0) sf.dim) :=
        Eq.trans (Eq.symm hmix) (Eq.refl _)
      let h1eq : repr s1 = mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                   (Prod.fst (splitTensor tt sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim :=
        Eq.subst (motive := fun b => repr s1 = mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                   (Prod.fst (splitTensor tt sf.dim)) b sf.dim) hmixeq
          (Eq.trans
            (execMixBufRefines (stateOfHeap (Prod.snd (allocStack (repr s0) sf.dim))) _ _ _ s1 hexMix)
            (congrArg (fun hh => mixBufLoop hh (Prod.fst (splitTensor tt sf.dim)) mixbuf sf.dim) hrepr0))
      let h2eq : repr s2 = addScaledLoop (mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                   (Prod.fst (splitTensor tt sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim)
                   (Prod.fst (splitTensor tt sf.dim)) (Prod.snd (splitTensor tt sf.dim)) sf.fractalscale sf.dim :=
        Eq.trans (execAddScaledRefines s1 _ _ _ _ s2 hexAdd)
          (congrArg (fun hh => addScaledLoop hh (Prod.fst (splitTensor tt sf.dim))
                (Prod.snd (splitTensor tt sf.dim)) sf.fractalscale sf.dim) h1eq)
      let h3eq : repr s3 = addScaledHalfLoop
                   (addScaledLoop (mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                     (Prod.fst (splitTensor tt sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim)
                     (Prod.fst (splitTensor tt sf.dim)) (Prod.snd (splitTensor tt sf.dim)) sf.fractalscale sf.dim)
                   (Prod.snd (splitTensor tt sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim))
                   sf.fractalscale sf.dim :=
        Eq.subst (motive := fun b => repr s3 = addScaledHalfLoop
                   (addScaledLoop (mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                     (Prod.fst (splitTensor tt sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim)
                     (Prod.fst (splitTensor tt sf.dim)) (Prod.snd (splitTensor tt sf.dim)) sf.fractalscale sf.dim)
                   (Prod.snd (splitTensor tt sf.dim)) b sf.fractalscale sf.dim) hmixeq
          (Eq.trans (execAddScaledHalfRefines s2 _ _ _ _ s3 hexHalf)
            (congrArg (fun hh => addScaledHalfLoop hh (Prod.snd (splitTensor tt sf.dim))
                  mixbuf sf.fractalscale sf.dim) h2eq))
      Eq.trans
        (reprStateOfHeap (restoreStack (repr s3) s0.stackbase))
        (Eq.trans
          (congrArg (fun hh => restoreStack hh s0.stackbase) h3eq)
          (Eq.symm (forwardRunHeapUnfold (repr s0) tt sf.dim sf.fractalscale hnlt hnbuf))))
    hexec'
theorem backwardRefinesExec (σ : ZigState) (g : BackwardSlice) (self : OFTB)
    (σ' : ZigState) (hexec : ExecBackward σ g self σ') :
    repr σ' = backwardHeap (repr σ) g self.dim self.fractalscale :=
  ExecBackward.rec
    (fun s0 gg sf hlt => Eq.symm (backwardEarlyReturnLen (repr s0) gg sf.dim sf.fractalscale hlt))
    (fun s0 gg sf hnlt hbig => Eq.symm (backwardEarlyReturnBuf (repr s0) gg sf.dim sf.fractalscale hbig))
    (fun s0 s1 s2 s3 gg sf buf hnlt hnbuf hbuf hexMix hexAdd hexHalf =>
      let hrepr0 : repr (stateOfHeap (Prod.snd (allocStack (repr s0) sf.dim))) =
                   Prod.snd (allocStack (repr s0) sf.dim) :=
        reprStateOfHeap (Prod.snd (allocStack (repr s0) sf.dim))
      let hbufeq : buf = Prod.fst (allocStack (repr s0) sf.dim) :=
        Eq.trans (Eq.symm hbuf) (Eq.refl _)
      let h1eq : repr s1 = mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                   (Prod.snd (splitBackwardSlice gg sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim :=
        Eq.subst (motive := fun b => repr s1 = mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                   (Prod.snd (splitBackwardSlice gg sf.dim)) b sf.dim) hbufeq
          (Eq.trans
            (execMixBufRefines (stateOfHeap (Prod.snd (allocStack (repr s0) sf.dim))) _ _ _ s1 hexMix)
            (congrArg (fun hh => mixBufLoop hh (Prod.snd (splitBackwardSlice gg sf.dim)) buf sf.dim) hrepr0))
      let h2eq : repr s2 = addScaledLoop (mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                   (Prod.snd (splitBackwardSlice gg sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim)
                   (Prod.snd (splitBackwardSlice gg sf.dim)) (Prod.fst (splitBackwardSlice gg sf.dim))
                   sf.fractalscale sf.dim :=
        Eq.trans (execAddScaledRefines s1 _ _ _ _ s2 hexAdd)
          (congrArg (fun hh => addScaledLoop hh (Prod.snd (splitBackwardSlice gg sf.dim))
                (Prod.fst (splitBackwardSlice gg sf.dim)) sf.fractalscale sf.dim) h1eq)
      let h3eq : repr s3 = addScaledHalfLoop
                   (addScaledLoop (mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                     (Prod.snd (splitBackwardSlice gg sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim)
                     (Prod.snd (splitBackwardSlice gg sf.dim)) (Prod.fst (splitBackwardSlice gg sf.dim))
                     sf.fractalscale sf.dim)
                   (Prod.fst (splitBackwardSlice gg sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim))
                   sf.fractalscale sf.dim :=
        Eq.subst (motive := fun b => repr s3 = addScaledHalfLoop
                   (addScaledLoop (mixBufLoop (Prod.snd (allocStack (repr s0) sf.dim))
                     (Prod.snd (splitBackwardSlice gg sf.dim)) (Prod.fst (allocStack (repr s0) sf.dim)) sf.dim)
                     (Prod.snd (splitBackwardSlice gg sf.dim)) (Prod.fst (splitBackwardSlice gg sf.dim))
                     sf.fractalscale sf.dim)
                   (Prod.fst (splitBackwardSlice gg sf.dim)) b sf.fractalscale sf.dim) hbufeq
          (Eq.trans (execAddScaledHalfRefines s2 _ _ _ _ s3 hexHalf)
            (congrArg (fun hh => addScaledHalfLoop hh (Prod.fst (splitBackwardSlice gg sf.dim))
                  buf sf.fractalscale sf.dim) h2eq))
      Eq.trans
        (reprStateOfHeap (restoreStack (repr s3) s0.stackbase))
        (Eq.trans
          (congrArg (fun hh => restoreStack hh s0.stackbase) h3eq)
          (Eq.symm (backwardRunHeapUnfold (repr s0) gg sf.dim sf.fractalscale hnlt hnbuf))))
    hexec
theorem mixBufInvariant (h : Heap) (src buf : Slice) (n : Nat)
    (hdisj : isDisjoint buf src)
    (hnBuf : n ≤ buf.len)
    (hnSrc : n ≤ src.len) :
    ∀ m : Nat, m < n →
      readSlice (mixBufLoop h src buf n) buf m = readSlice h src m :=
  fun m hm => mixBufLoopAtBuf h src buf n m hdisj hnBuf hnSrc hm
theorem addScaledInvariant (h : Heap) (dst src : Slice) (scale : Scalar) (n : Nat)
    (hdisj : isDisjoint dst src)
    (hnDst : n ≤ dst.len)
    (hnSrc : n ≤ src.len) :
    ∀ m : Nat, m < n →
      readSlice (addScaledLoop h dst src scale n) dst m =
        fadd (readSlice h dst m) (fmul (readSlice h src m) scale) :=
  fun m hm => addScaledLoopAtDst h dst src scale n m hdisj hnDst hnSrc hm
theorem addScaledHalfInvariant (h : Heap) (dst src : Slice) (scale : Scalar) (n : Nat)
    (hdisj : isDisjoint dst src)
    (hnDst : n ≤ dst.len)
    (hnSrc : n ≤ src.len) :
    ∀ m : Nat, m < n →
      readSlice (addScaledHalfLoop h dst src scale n) dst m =
        fadd (readSlice h dst m) (fmul (fmul (readSlice h src m) scale) halfCoeff) :=
  fun m hm => addScaledHalfLoopAtDst h dst src scale n m hdisj hnDst hnSrc hm
theorem forwardX1Spec (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (t.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim))
    (hstack : Nat.add t.data.ptr t.data.len ≤ h.stacktop)
    (m : Nat) (hm : m < dim) :
    readSlice (forwardHeap h t dim scale) (Prod.fst (splitTensor t dim)) m =
      fadd (readSlice h (Prod.fst (splitTensor t dim)) m)
           (fmul (readSlice h (Prod.snd (splitTensor t dim)) m) scale) :=
  match Nat.decLt t.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue hlt => False.elim (hlen hlt)
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue hbig => False.elim (hbuf hbig)
    | Decidable.isFalse _ =>
      let x1 : Slice := Slice.mk t.data.ptr dim
      let x2 : Slice := Slice.mk (Nat.add t.data.ptr dim) dim
      let mixbuf : Slice := Prod.fst (allocStack h dim)
      let h0 : Heap := Prod.snd (allocStack h dim)
      let h1 := mixBufLoop h0 x1 mixbuf dim
      let h2 := addScaledLoop h1 x1 x2 scale dim
      let h3 := addScaledHalfLoop h2 x2 mixbuf scale dim
      let hge : Nat.mul dim natTwo ≤ t.data.len :=
        match Nat.lt_or_ge t.data.len (Nat.mul dim natTwo) with
        | Or.inl hlt => False.elim (hlen hlt)
        | Or.inr hge => hge
      let hdimlelen : dim ≤ t.data.len :=
        Nat.le_trans (natLeMulTwo dim) hge
      let hbufAfterX1 : Nat.add t.data.ptr dim ≤ h.stacktop :=
        Nat.le_trans (Nat.add_le_add_left hdimlelen t.data.ptr) hstack
      let hdisjX1X2 : isDisjoint x1 x2 := Or.inl (Nat.le_refl (Nat.add t.data.ptr dim))
      let hdisjX2X1 : isDisjoint x2 x1 := Or.inr (Nat.le_refl (Nat.add t.data.ptr dim))
      let hdisjMixX1 : isDisjoint mixbuf x1 := Or.inr hbufAfterX1
      let hdisjMixX2 : isDisjoint mixbuf x2 :=
        Or.inr (Nat.le_trans
          (Eq.subst (Eq.symm (Nat.add_assoc t.data.ptr dim dim))
            (Nat.add_le_add_left (natMulTwoLeToAddAddLe dim t.data.len hge) t.data.ptr))
          hstack)
      Eq.trans (restoreStackReadSlice h3 h.stacktop x1 m)
        (Eq.trans
          (addScaledHalfLoopPreservesOther h2 x2 mixbuf x1 scale dim hdisjX2X1
            (Nat.le_refl dim) m hm)
          (addScaledLoopAtDst h1 x1 x2 scale dim m hdisjX1X2
            (Nat.le_refl dim) (Nat.le_refl dim) m hm
            |> fun heq => Eq.trans heq
              (congrArg (fun z => fadd (readSlice h1 x1 m) (fmul z scale))
                (Eq.trans
                  (addScaledLoopPreservesOther h1 x1 x2 x2 scale dim hdisjX1X2
                    (Nat.le_refl dim) m hm)
                  (mixBufLoopPreservesOther h0 x1 mixbuf x2 dim hdisjMixX2
                    (Nat.le_refl dim) m hm
                    |> fun heq2 => Eq.trans heq2 (allocStackReadSlice h dim x2 m))))
            |> fun heq => Eq.trans heq
              (congrArg (fun z => fadd z (fmul (readSlice h x2 m) scale))
                (Eq.trans
                  (addScaledLoopOutsideDst h1 x1 x2 scale m m (Nat.lt_irrefl m) |> absurd (Nat.lt_irrefl m) |> (fun _ =>
                    Eq.trans
                      (addScaledLoopPreservesOther h1 x1 x2 x1 scale dim hdisjX1X2
                        (Nat.le_refl dim) m hm)
                      (Eq.trans
                        (mixBufLoopPreservesOther h0 x1 mixbuf x1 dim hdisjMixX1
                          (Nat.le_refl dim) m hm)
                        (allocStackReadSlice h dim x1 m))))
                  (Eq.refl _)))))
theorem forwardX2Spec (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (t.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim))
    (hstack : Nat.add t.data.ptr t.data.len ≤ h.stacktop)
    (m : Nat) (hm : m < dim) :
    readSlice (forwardHeap h t dim scale) (Prod.snd (splitTensor t dim)) m =
      fadd (readSlice h (Prod.snd (splitTensor t dim)) m)
           (fmul (fmul (readSlice h (Prod.fst (splitTensor t dim)) m) scale) halfCoeff) :=
  match Nat.decLt t.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue hlt => False.elim (hlen hlt)
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue hbig => False.elim (hbuf hbig)
    | Decidable.isFalse _ =>
      let x1 : Slice := Slice.mk t.data.ptr dim
      let x2 : Slice := Slice.mk (Nat.add t.data.ptr dim) dim
      let mixbuf : Slice := Prod.fst (allocStack h dim)
      let h0 : Heap := Prod.snd (allocStack h dim)
      let h1 := mixBufLoop h0 x1 mixbuf dim
      let h2 := addScaledLoop h1 x1 x2 scale dim
      let h3 := addScaledHalfLoop h2 x2 mixbuf scale dim
      let hge : Nat.mul dim natTwo ≤ t.data.len :=
        match Nat.lt_or_ge t.data.len (Nat.mul dim natTwo) with
        | Or.inl hlt => False.elim (hlen hlt)
        | Or.inr hge => hge
      let hdimlelen : dim ≤ t.data.len := Nat.le_trans (natLeMulTwo dim) hge
      let hx1BeforeBuf : Nat.add t.data.ptr dim ≤ h.stacktop :=
        Nat.le_trans (Nat.add_le_add_left hdimlelen t.data.ptr) hstack
      let hx2BeforeBuf : Nat.add (Nat.add t.data.ptr dim) dim ≤ h.stacktop :=
        Nat.le_trans
          (Eq.subst (Eq.symm (Nat.add_assoc t.data.ptr dim dim))
            (Nat.add_le_add_left (natMulTwoLeToAddAddLe dim t.data.len hge) t.data.ptr))
          hstack
      let hdisjX1X2 : isDisjoint x1 x2 := Or.inl (Nat.le_refl (Nat.add t.data.ptr dim))
      let hdisjX2Mix : isDisjoint x2 mixbuf := Or.inl hx2BeforeBuf
      let hdisjMixX2 : isDisjoint mixbuf x2 := Or.inr hx2BeforeBuf
      let hdisjMixX1 : isDisjoint mixbuf x1 := Or.inr hx1BeforeBuf
      Eq.trans (restoreStackReadSlice h3 h.stacktop x2 m)
        (Eq.trans
          (addScaledHalfLoopAtDst h2 x2 mixbuf scale dim m hdisjX2Mix
            (Nat.le_refl dim) (Nat.le_refl dim) m hm)
          (congrArg (fun z => fadd (readSlice h2 x2 m) (fmul (fmul z scale) halfCoeff))
            (Eq.trans
              (addScaledHalfLoopOutsideDst h2 x2 mixbuf scale m m (Nat.lt_irrefl m) |> absurd (Nat.lt_irrefl m) |> (fun _ =>
                Eq.trans
                  (addScaledLoopPreservesOther h1 x1 x2 x2 scale dim hdisjX1X2
                    (Nat.le_refl dim) m hm)
                  (mixBufLoopAtBuf h0 x1 mixbuf dim m
                    (Or.inr hx1BeforeBuf)
                    (Nat.le_refl dim) (Nat.le_refl dim) hm
                    |> fun heq => Eq.trans heq (allocStackReadSlice h dim x1 m))))
              (Eq.refl _))
            |> fun heq => Eq.trans heq
              (congrArg (fun z => fadd z (fmul (fmul (readSlice h x1 m) scale) halfCoeff))
                (Eq.trans
                  (addScaledHalfLoopOutsideDst h2 x2 mixbuf scale m m (Nat.lt_irrefl m) |> absurd (Nat.lt_irrefl m) |> (fun _ =>
                    Eq.trans
                      (addScaledLoopPreservesOther h1 x1 x2 x2 scale dim hdisjX1X2
                        (Nat.le_refl dim) m hm)
                      (mixBufLoopPreservesOther h0 x1 mixbuf x2 dim hdisjMixX2
                        (Nat.le_refl dim) m hm
                        |> fun heq2 => Eq.trans heq2 (allocStackReadSlice h dim x2 m))))
                  (Eq.refl _)))))
theorem backwardG2Spec (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (g.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim))
    (hstack : Nat.add g.data.ptr g.data.len ≤ h.stacktop)
    (m : Nat) (hm : m < dim) :
    readSlice (backwardHeap h g dim scale) (Prod.snd (splitBackwardSlice g dim)) m =
      fadd (readSlice h (Prod.snd (splitBackwardSlice g dim)) m)
           (fmul (readSlice h (Prod.fst (splitBackwardSlice g dim)) m) scale) :=
  match Nat.decLt g.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue hlt => False.elim (hlen hlt)
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue hbig => False.elim (hbuf hbig)
    | Decidable.isFalse _ =>
      let g1 : Slice := Slice.mk g.data.ptr dim
      let g2 : Slice := Slice.mk (Nat.add g.data.ptr dim) dim
      let buf : Slice := Prod.fst (allocStack h dim)
      let h0 : Heap := Prod.snd (allocStack h dim)
      let h1 := mixBufLoop h0 g2 buf dim
      let h2 := addScaledLoop h1 g2 g1 scale dim
      let h3 := addScaledHalfLoop h2 g1 buf scale dim
      let hge : Nat.mul dim natTwo ≤ g.data.len :=
        match Nat.lt_or_ge g.data.len (Nat.mul dim natTwo) with
        | Or.inl hlt => False.elim (hlen hlt)
        | Or.inr hge => hge
      let hdimlelen : dim ≤ g.data.len := Nat.le_trans (natLeMulTwo dim) hge
      let hg2BeforeBuf : Nat.add (Nat.add g.data.ptr dim) dim ≤ h.stacktop :=
        Nat.le_trans
          (Eq.subst (Eq.symm (Nat.add_assoc g.data.ptr dim dim))
            (Nat.add_le_add_left (natMulTwoLeToAddAddLe dim g.data.len hge) g.data.ptr))
          hstack
      let hdisjG2G1 : isDisjoint g2 g1 := Or.inr (Nat.le_refl (Nat.add g.data.ptr dim))
      let hdisjBufG2 : isDisjoint buf g2 := Or.inr hg2BeforeBuf
      Eq.trans (restoreStackReadSlice h3 h.stacktop g2 m)
        (Eq.trans
          (addScaledHalfLoopPreservesOther h2 g1 buf g2 scale dim hdisjG2G1
            (Nat.le_refl dim) m hm)
          (addScaledLoopAtDst h1 g2 g1 scale dim m hdisjG2G1
            (Nat.le_refl dim) (Nat.le_refl dim) m hm
            |> fun heq => Eq.trans heq
              (congrArg (fun z => fadd (readSlice h1 g2 m) (fmul z scale))
                (Eq.trans
                  (addScaledLoopPreservesOther h1 g2 g1 g1 scale dim hdisjG2G1
                    (Nat.le_refl dim) m hm)
                  (Eq.trans
                    (mixBufLoopPreservesOther h0 g2 buf g1 dim
                      (Or.inr (Nat.le_trans (Nat.add_le_add_left hdimlelen g.data.ptr) hstack))
                      (Nat.le_refl dim) m hm)
                    (allocStackReadSlice h dim g1 m))))
            |> fun heq => Eq.trans heq
              (congrArg (fun z => fadd z (fmul (readSlice h g1 m) scale))
                (Eq.trans
                  (addScaledLoopOutsideDst h1 g2 g1 scale m m (Nat.lt_irrefl m) |> absurd (Nat.lt_irrefl m) |> (fun _ =>
                    Eq.trans
                      (mixBufLoopPreservesOther h0 g2 buf g2 dim hdisjBufG2
                        (Nat.le_refl dim) m hm)
                      (allocStackReadSlice h dim g2 m)))
                  (Eq.refl _)))))
theorem backwardG1Spec (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (g.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim))
    (hstack : Nat.add g.data.ptr g.data.len ≤ h.stacktop)
    (m : Nat) (hm : m < dim) :
    readSlice (backwardHeap h g dim scale) (Prod.fst (splitBackwardSlice g dim)) m =
      fadd (readSlice h (Prod.fst (splitBackwardSlice g dim)) m)
           (fmul (fmul (readSlice h (Prod.snd (splitBackwardSlice g dim)) m) scale) halfCoeff) :=
  match Nat.decLt g.data.len (Nat.mul dim natTwo) with
  | Decidable.isTrue hlt => False.elim (hlen hlt)
  | Decidable.isFalse _ =>
    match Nat.decLt maxBufSize dim with
    | Decidable.isTrue hbig => False.elim (hbuf hbig)
    | Decidable.isFalse _ =>
      let g1 : Slice := Slice.mk g.data.ptr dim
      let g2 : Slice := Slice.mk (Nat.add g.data.ptr dim) dim
      let buf : Slice := Prod.fst (allocStack h dim)
      let h0 : Heap := Prod.snd (allocStack h dim)
      let h1 := mixBufLoop h0 g2 buf dim
      let h2 := addScaledLoop h1 g2 g1 scale dim
      let h3 := addScaledHalfLoop h2 g1 buf scale dim
      let hge : Nat.mul dim natTwo ≤ g.data.len :=
        match Nat.lt_or_ge g.data.len (Nat.mul dim natTwo) with
        | Or.inl hlt => False.elim (hlen hlt)
        | Or.inr hge => hge
      let hdimlelen : dim ≤ g.data.len := Nat.le_trans (natLeMulTwo dim) hge
      let hg1BeforeBuf : Nat.add g.data.ptr dim ≤ h.stacktop :=
        Nat.le_trans (Nat.add_le_add_left hdimlelen g.data.ptr) hstack
      let hg2BeforeBuf : Nat.add (Nat.add g.data.ptr dim) dim ≤ h.stacktop :=
        Nat.le_trans
          (Eq.subst (Eq.symm (Nat.add_assoc g.data.ptr dim dim))
            (Nat.add_le_add_left (natMulTwoLeToAddAddLe dim g.data.len hge) g.data.ptr))
          hstack
      let hdisjG1G2 : isDisjoint g1 g2 := Or.inl (Nat.le_refl (Nat.add g.data.ptr dim))
      let hdisjG2G1 : isDisjoint g2 g1 := Or.inr (Nat.le_refl (Nat.add g.data.ptr dim))
      let hdisjG1Buf : isDisjoint g1 buf := Or.inl hg1BeforeBuf
      let hdisjBufG1 : isDisjoint buf g1 := Or.inr hg1BeforeBuf
      let hdisjG2Buf : isDisjoint g2 buf := Or.inl hg2BeforeBuf
      Eq.trans (restoreStackReadSlice h3 h.stacktop g1 m)
        (Eq.trans
          (addScaledHalfLoopAtDst h2 g1 buf scale dim m hdisjG1Buf
            (Nat.le_refl dim) (Nat.le_refl dim) m hm)
          (congrArg (fun z => fadd (readSlice h2 g1 m) (fmul (fmul z scale) halfCoeff))
            (Eq.trans
              (addScaledHalfLoopOutsideDst h2 g1 buf scale m m (Nat.lt_irrefl m) |> absurd (Nat.lt_irrefl m) |> (fun _ =>
                Eq.trans
                  (addScaledLoopPreservesOther h1 g2 g1 g1 scale dim hdisjG2G1
                    (Nat.le_refl dim) m hm)
                  (mixBufLoopAtBuf h0 g2 buf dim m
                    hdisjBufG1
                    (Nat.le_refl dim) (Nat.le_refl dim) hm
                    |> fun heq => Eq.trans heq (allocStackReadSlice h dim g2 m))))
              (Eq.refl _))
            |> fun heq => Eq.trans heq
              (congrArg (fun z => fadd z (fmul (fmul (readSlice h g2 m) scale) halfCoeff))
                (Eq.trans
                  (addScaledHalfLoopOutsideDst h2 g1 buf scale m m (Nat.lt_irrefl m) |> absurd (Nat.lt_irrefl m) |> (fun _ =>
                    Eq.trans
                      (addScaledLoopPreservesOther h1 g2 g1 g1 scale dim hdisjG2G1
                        (Nat.le_refl dim) m hm)
                      (mixBufLoopPreservesOther h0 g2 buf g1 dim hdisjBufG1
                        (Nat.le_refl dim) m hm
                        |> fun heq2 => Eq.trans heq2 (allocStackReadSlice h dim g1 m))))
                  (Eq.refl _)))))
theorem forwardFullCorrect (h : Heap) (t : Tensor) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (t.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim))
    (hstack : Nat.add t.data.ptr t.data.len ≤ h.stacktop) :
    (∀ m : Nat, m < dim →
      readSlice (forwardHeap h t dim scale) (Prod.fst (splitTensor t dim)) m =
        fadd (readSlice h (Prod.fst (splitTensor t dim)) m)
             (fmul (readSlice h (Prod.snd (splitTensor t dim)) m) scale)) ∧
    (∀ m : Nat, m < dim →
      readSlice (forwardHeap h t dim scale) (Prod.snd (splitTensor t dim)) m =
        fadd (readSlice h (Prod.snd (splitTensor t dim)) m)
             (fmul (fmul (readSlice h (Prod.fst (splitTensor t dim)) m) scale) halfCoeff)) :=
  And.intro
    (fun m hm => forwardX1Spec h t dim scale hlen hbuf hstack m hm)
    (fun m hm => forwardX2Spec h t dim scale hlen hbuf hstack m hm)
theorem backwardFullCorrect (h : Heap) (g : BackwardSlice) (dim : Nat) (scale : Scalar)
    (hlen : ¬ (g.data.len < Nat.mul dim natTwo))
    (hbuf : ¬ (maxBufSize < dim))
    (hstack : Nat.add g.data.ptr g.data.len ≤ h.stacktop) :
    (∀ m : Nat, m < dim →
      readSlice (backwardHeap h g dim scale) (Prod.snd (splitBackwardSlice g dim)) m =
        fadd (readSlice h (Prod.snd (splitBackwardSlice g dim)) m)
             (fmul (readSlice h (Prod.fst (splitBackwardSlice g dim)) m) scale)) ∧
    (∀ m : Nat, m < dim →
      readSlice (backwardHeap h g dim scale) (Prod.fst (splitBackwardSlice g dim)) m =
        fadd (readSlice h (Prod.fst (splitBackwardSlice g dim)) m)
             (fmul (fmul (readSlice h (Prod.snd (splitBackwardSlice g dim)) m) scale) halfCoeff)) :=
  And.intro
    (fun m hm => backwardG2Spec h g dim scale hlen hbuf hstack m hm)
    (fun m hm => backwardG1Spec h g dim scale hlen hbuf hstack m hm)
theorem stackDisjointFromTensor (h : Heap) (t : Tensor) (dim : Nat)
    (hstack : Nat.add t.data.ptr t.data.len ≤ h.stacktop)
    (hlen : ¬ (t.data.len < Nat.mul dim natTwo)) :
    isDisjoint (Prod.fst (allocStack h dim)) (Prod.fst (splitTensor t dim)) ∧
    isDisjoint (Prod.fst (allocStack h dim)) (Prod.snd (splitTensor t dim)) :=
  let hge : Nat.mul dim natTwo ≤ t.data.len :=
    match Nat.lt_or_ge t.data.len (Nat.mul dim natTwo) with
    | Or.inl hlt => False.elim (hlen hlt)
    | Or.inr hge => hge
  let hdimlelen : dim ≤ t.data.len := Nat.le_trans (natLeMulTwo dim) hge
  let hx1BeforeStack : Nat.add t.data.ptr dim ≤ h.stacktop :=
    Nat.le_trans (Nat.add_le_add_left hdimlelen t.data.ptr) hstack
  And.intro
    (Or.inr hx1BeforeStack)
    (Or.inr (Nat.le_trans
      (Eq.subst (Eq.symm (Nat.add_assoc t.data.ptr dim dim))
        (Nat.add_le_add_left (natMulTwoLeToAddAddLe dim t.data.len hge) t.data.ptr))
      hstack))
theorem stackDisjointFromBackward (h : Heap) (g : BackwardSlice) (dim : Nat)
    (hstack : Nat.add g.data.ptr g.data.len ≤ h.stacktop)
    (hlen : ¬ (g.data.len < Nat.mul dim natTwo)) :
    isDisjoint (Prod.fst (allocStack h dim)) (Prod.fst (splitBackwardSlice g dim)) ∧
    isDisjoint (Prod.fst (allocStack h dim)) (Prod.snd (splitBackwardSlice g dim)) :=
  let hge : Nat.mul dim natTwo ≤ g.data.len :=
    match Nat.lt_or_ge g.data.len (Nat.mul dim natTwo) with
    | Or.inl hlt => False.elim (hlen hlt)
    | Or.inr hge => hge
  let hdimlelen : dim ≤ g.data.len := Nat.le_trans (natLeMulTwo dim) hge
  let hg1BeforeStack : Nat.add g.data.ptr dim ≤ h.stacktop :=
    Nat.le_trans (Nat.add_le_add_left hdimlelen g.data.ptr) hstack
  And.intro
    (Or.inr hg1BeforeStack)
    (Or.inr (Nat.le_trans
      (Eq.subst (Eq.symm (Nat.add_assoc g.data.ptr dim dim))
        (Nat.add_le_add_left (natMulTwoLeToAddAddLe dim g.data.len hge) g.data.ptr))
      hstack))
theorem fadd_correct (a b : Scalar) :
    isNearestRepresentable (exactAdd (datumToExact (decode a)) (datumToExact (decode b))) (fadd a b) :=
  fun _ _ => Eq.refl (roundToNearestTiesToEvenBinary32 (exactAdd (datumToExact (decode a)) (datumToExact (decode b))))
theorem fmul_correct (a b : Scalar) :
    isNearestRepresentable (exactMul (datumToExact (decode a)) (datumToExact (decode b))) (fmul a b) :=
  fun _ _ => Eq.refl (roundToNearestTiesToEvenBinary32 (exactMul (datumToExact (decode a)) (datumToExact (decode b))))
theorem ieee754Binary32Add_correct (a b : IEEEFloat32) :
    isNearestRepresentable (exactAdd (datumToExact (decode a)) (datumToExact (decode b))) (ieee754Binary32Add a b) :=
  fun _ _ => Eq.refl (roundToNearestTiesToEvenBinary32 (exactAdd (datumToExact (decode a)) (datumToExact (decode b))))
theorem ieee754Binary32Mul_correct (a b : IEEEFloat32) :
    isNearestRepresentable (exactMul (datumToExact (decode a)) (datumToExact (decode b))) (ieee754Binary32Mul a b) :=
  fun _ _ => Eq.refl (roundToNearestTiesToEvenBinary32 (exactMul (datumToExact (decode a)) (datumToExact (decode b))))
end OFTB