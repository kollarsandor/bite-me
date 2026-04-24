structure FP where
  val : Int
deriving BEq, Repr

namespace FP

def scale : Int := 100000000

def zero : FP := ⟨0⟩
def one : FP := ⟨scale⟩
def fractalScale : FP := ⟨70710678⟩
def halfFractalScale : FP := ⟨35355339⟩

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

theorem ext (a b : FP) (h : a.val = b.val) : a = b :=
  match a, b with
  | ⟨_⟩, ⟨_⟩ => congrArg FP.mk h

theorem val_ext {a b : FP} (h : a = b) : a.val = b.val :=
  congrArg FP.val h

theorem add_comm (a b : FP) : add a b = add b a :=
  ext (add a b) (add b a) (Int.add_comm a.val b.val)

theorem add_assoc (a b c : FP) : add (add a b) c = add a (add b c) :=
  ext (add (add a b) c) (add a (add b c)) (Int.add_assoc a.val b.val c.val)

theorem add_zero (a : FP) : add a zero = a :=
  ext (add a zero) a (Int.add_zero a.val)

theorem zero_add (a : FP) : add zero a = a :=
  Eq.trans (add_comm zero a) (add_zero a)

theorem add_neg_cancel (a : FP) : add a (neg a) = zero :=
  ext (add a (neg a)) zero (Int.add_right_neg a.val)

theorem neg_add_cancel (a : FP) : add (neg a) a = zero :=
  Eq.trans (add_comm (neg a) a) (add_neg_cancel a)

theorem neg_neg (a : FP) : neg (neg a) = a :=
  ext (neg (neg a)) a (Int.neg_neg a.val)

theorem neg_zero : neg zero = zero :=
  ext (neg zero) zero Int.neg_zero

theorem sub_self (a : FP) : sub a a = zero :=
  ext (sub a a) zero (Int.sub_self a.val)

theorem sub_eq_add_neg (a b : FP) : sub a b = add a (neg b) :=
  ext (sub a b) (add a (neg b)) (Int.sub_eq_add_neg a.val b.val)

theorem add_sub_cancel (a b : FP) : sub (add a b) b = a :=
  ext (sub (add a b) b) a (Int.add_sub_cancel a.val b.val)

theorem sub_add_cancel (a b : FP) : add (sub a b) b = a :=
  ext (add (sub a b) b) a (Int.sub_add_cancel a.val b.val)

theorem mul_comm (a b : FP) : mul a b = mul b a :=
  ext (mul a b) (mul b a) (congrArg (· / scale) (Int.mul_comm a.val b.val))

theorem mul_zero (a : FP) : mul a zero = zero :=
  ext (mul a zero) zero
    (Eq.trans (congrArg (· / scale) (Int.mul_zero a.val)) (Int.zero_div scale))

theorem zero_mul (a : FP) : mul zero a = zero :=
  Eq.trans (mul_comm zero a) (mul_zero a)

theorem neg_add_distrib (a b : FP) : neg (add a b) = add (neg a) (neg b) :=
  ext (neg (add a b)) (add (neg a) (neg b)) (Int.neg_add a.val b.val)

theorem add_left_comm (a b c : FP) : add a (add b c) = add b (add a c) :=
  Eq.trans (Eq.symm (add_assoc a b c))
    (Eq.trans (congrArg (fun x => add x c) (add_comm a b))
      (add_assoc b a c))

theorem add_right_comm (a b c : FP) : add (add a b) c = add (add a c) b :=
  Eq.trans (add_assoc a b c)
    (Eq.trans (congrArg (add a) (add_comm b c))
      (Eq.symm (add_assoc a c b)))

theorem sub_sub (a b c : FP) : sub (sub a b) c = sub a (add b c) :=
  ext (sub (sub a b) c) (sub a (add b c)) (Int.sub_sub a.val b.val c.val)

theorem neg_sub (a b : FP) : neg (sub a b) = sub b a :=
  ext (neg (sub a b)) (sub b a) (Int.neg_sub a.val b.val)

theorem add_left_cancel (a b c : FP) (h : add a b = add a c) : b = c :=
  ext b c (Int.add_left_cancel (val_ext h))

end FP

def listGet (l : List FP) (i : Nat) (default : FP) : FP :=
  match l, i with
  | [], _ => default
  | a :: _, 0 => a
  | _ :: as, Nat.succ n => listGet as n default

def listSet (l : List FP) (i : Nat) (v : FP) : List FP :=
  match l, i with
  | [], _ => []
  | _ :: as, 0 => v :: as
  | a :: as, Nat.succ n => a :: listSet as n v

theorem listSet_length (l : List FP) (i : Nat) (v : FP) :
    (listSet l i v).length = l.length :=
  match l, i with
  | [], _ =>
    Eq.trans (Eq.symm (Nat.add_zero 0)) (Nat.add_zero 0)
  | _ :: as, 0 =>
    congrArg Nat.succ (Eq.trans (Eq.symm (Nat.add_zero as.length)) (Nat.add_zero as.length))
  | _ :: as, Nat.succ n =>
    congrArg Nat.succ (listSet_length as n v)

theorem listGet_set_same (l : List FP) (i : Nat) (v : FP) (d : FP)
    (h : i < l.length) : listGet (listSet l i v) i d = v :=
  match l, i with
  | [], _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0 =>
    FP.ext v v (Eq.trans (Eq.symm (Int.add_zero v.val)) (Int.add_zero v.val))
  | _ :: as, Nat.succ n =>
    listGet_set_same as n v d (Nat.lt_of_succ_lt_succ h)

theorem listGet_set_other (l : List FP) (i j : Nat) (v : FP) (d : FP)
    (hne : ¬(i = j)) : listGet (listSet l j v) i d = listGet l i d :=
  match l, i, j with
  | [], _, _ =>
    FP.ext d d (Eq.trans (Eq.symm (Int.add_zero d.val)) (Int.add_zero d.val))
  | _ :: _, 0, 0 =>
    absurd (Eq.trans (Eq.symm (Nat.add_zero 0)) (Nat.add_zero 0)) hne
  | _ :: _, 0, Nat.succ _ =>
    FP.ext (listGet (_ :: _) 0 d) (listGet (_ :: _) 0 d)
      (Eq.trans (Eq.symm (Int.add_zero (listGet (_ :: _) 0 d).val))
        (Int.add_zero (listGet (_ :: _) 0 d).val))
  | _ :: _, Nat.succ _, 0 =>
    FP.ext (listGet _ _ d) (listGet _ _ d)
      (Eq.trans (Eq.symm (Int.add_zero (listGet _ _ d).val))
        (Int.add_zero (listGet _ _ d).val))
  | _ :: as, Nat.succ m, Nat.succ n =>
    listGet_set_other as m n v d (fun heq => hne (congrArg Nat.succ heq))

namespace Vec

def zipWithFP (f : FP → FP → FP) : List FP → List FP → List FP
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => f a b :: zipWithFP f as bs

theorem zipWithFP_length_eq (f : FP → FP → FP) (l1 l2 : List FP)
    (h : l1.length = l2.length) : (zipWithFP f l1 l2).length = l1.length :=
  match l1, l2 with
  | [], [] => h
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | _ :: as, _ :: bs =>
    congrArg Nat.succ (zipWithFP_length_eq f as bs (Nat.succ.inj h))

def mapFP (f : FP → FP) : List FP → List FP
  | [] => []
  | a :: as => f a :: mapFP f as

theorem mapFP_length (f : FP → FP) (l : List FP) : (mapFP f l).length = l.length :=
  match l with
  | [] => Eq.trans (Eq.symm (Nat.add_zero 0)) (Nat.add_zero 0)
  | _ :: as => congrArg Nat.succ (mapFP_length f as)

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
  | 0, _ => Eq.trans (Eq.symm (Nat.add_zero 0)) (Nat.add_zero 0)
  | Nat.succ _, [] => absurd h (Nat.not_succ_le_zero _)
  | Nat.succ m, _ :: as =>
    congrArg Nat.succ (takeFP_length m as (Nat.le_of_succ_le_succ h))

theorem dropFP_length (n : Nat) (l : List FP) (h : n ≤ l.length) :
    (dropFP n l).length = l.length - n :=
  match n, l with
  | 0, l => Eq.symm (Nat.sub_zero l.length)
  | Nat.succ _, [] => absurd h (Nat.not_succ_le_zero _)
  | Nat.succ m, _ :: as =>
    dropFP_length m as (Nat.le_of_succ_le_succ h)

theorem takeFP_dropFP_append (n : Nat) (l : List FP) (h : n ≤ l.length) :
    takeFP n l ++ dropFP n l = l :=
  match n, l with
  | 0, l => Eq.symm (List.nil_append l)
  | Nat.succ _, [] => absurd h (Nat.not_succ_le_zero _)
  | Nat.succ m, a :: as =>
    Eq.trans
      (List.cons_append a (takeFP m as) (dropFP m as))
      (congrArg (a :: ·) (takeFP_dropFP_append m as (Nat.le_of_succ_le_succ h)))

theorem zipWithFP_get (f : FP → FP → FP) (l1 l2 : List FP) (i : Nat) (d : FP)
    (h1 : i < l1.length) (h2 : i < l2.length) :
    listGet (zipWithFP f l1 l2) i d = f (listGet l1 i d) (listGet l2 i d) :=
  match l1, l2, i with
  | [], _, _ => absurd h1 (Nat.not_lt_zero _)
  | _, [], _ => absurd h2 (Nat.not_lt_zero _)
  | a :: _, b :: _, 0 =>
    FP.ext (f a b) (f a b)
      (Eq.trans (Eq.symm (Int.add_zero (f a b).val)) (Int.add_zero (f a b).val))
  | _ :: as, _ :: bs, Nat.succ n =>
    zipWithFP_get f as bs n d (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

theorem zipWithFP_nil_l (f : FP → FP → FP) (l : List FP) :
    zipWithFP f [] l = [] :=
  match l with
  | [] => Eq.trans (Eq.symm (Nat.add_zero 0)) (Nat.add_zero 0) |> fun _ =>
    show ([] : List FP) = [] from
    congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
  | _ :: _ => congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))

theorem zipWithFP_nil_r (f : FP → FP → FP) (l : List FP) :
    zipWithFP f l [] = [] :=
  match l with
  | [] => congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
  | _ :: _ => congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))

end Vec

structure Tensor where
  data : List FP
  shape : List Nat

structure OFTB where
  fractalScale : FP
  halfFractalScale : FP
  dim : Nat

namespace OFTB

def init (d : Nat) : OFTB :=
  { fractalScale := FP.fractalScale
  , halfFractalScale := FP.halfFractalScale
  , dim := d }

def bufferLimit : Nat := 16384

def canProcess (self : OFTB) (dataLen : Nat) : Bool :=
  (dataLen ≥ self.dim * 2) && (self.dim ≤ bufferLimit)

def forwardPass (self : OFTB) (xData : List FP) : List FP :=
  if xData.length < self.dim * 2 then xData
  else if self.dim > bufferLimit then xData
  else
    let half := self.dim
    let x1 := Vec.takeFP half xData
    let x2 := Vec.takeFP half (Vec.dropFP half xData)
    let rest := Vec.dropFP (half * 2) xData
    let mixBuf := x1
    let x1' := Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) x1 x2
    let x2' := Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) x2 mixBuf
    x1' ++ x2' ++ rest

def backwardPass (self : OFTB) (grad : List FP) : List FP :=
  if grad.length < self.dim * 2 then grad
  else if self.dim > bufferLimit then grad
  else
    let half := self.dim
    let g1 := Vec.takeFP half grad
    let g2 := Vec.takeFP half (Vec.dropFP half grad)
    let rest := Vec.dropFP (half * 2) grad
    let buf := g2
    let g2' := Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) g2 g1
    let g1' := Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) g1 buf
    g1' ++ g2' ++ rest

theorem forwardPass_short (self : OFTB) (xData : List FP)
    (h : xData.length < self.dim * 2) :
    forwardPass self xData = xData :=
  if_pos h

theorem backwardPass_short (self : OFTB) (grad : List FP)
    (h : grad.length < self.dim * 2) :
    backwardPass self grad = grad :=
  if_pos h

theorem forwardPass_bufferOverflow (self : OFTB) (xData : List FP)
    (h1 : ¬(xData.length < self.dim * 2))
    (h2 : self.dim > bufferLimit) :
    forwardPass self xData = xData :=
  Eq.trans (if_neg h1) (if_pos h2)

theorem backwardPass_bufferOverflow (self : OFTB) (grad : List FP)
    (h1 : ¬(grad.length < self.dim * 2))
    (h2 : self.dim > bufferLimit) :
    backwardPass self grad = grad :=
  Eq.trans (if_neg h1) (if_pos h2)

theorem init_fractalScale (d : Nat) : (init d).fractalScale = FP.fractalScale :=
  FP.ext (init d).fractalScale FP.fractalScale
    (Eq.trans (Eq.symm (Int.add_zero (init d).fractalScale.val))
      (Int.add_zero FP.fractalScale.val))

theorem init_halfFractalScale (d : Nat) : (init d).halfFractalScale = FP.halfFractalScale :=
  FP.ext (init d).halfFractalScale FP.halfFractalScale
    (Eq.trans (Eq.symm (Int.add_zero (init d).halfFractalScale.val))
      (Int.add_zero FP.halfFractalScale.val))

theorem init_dim (d : Nat) : (init d).dim = d :=
  Eq.trans (Eq.symm (Nat.add_zero d)) (Nat.add_zero d)

end OFTB

def forwardCopyLoop (half : Nat) (idx : Nat) (x1 mixBuf : List FP) : List FP :=
  match idx with
  | 0 => mixBuf
  | Nat.succ i =>
    let curIdx := half - (Nat.succ i)
    let v := listGet x1 curIdx FP.zero
    let mixBuf' := listSet mixBuf curIdx v
    forwardCopyLoop half i x1 mixBuf'

def forwardStep1Loop (fractalScale : FP) (half : Nat) (idx : Nat)
    (x1 x2 : List FP) : List FP :=
  match idx with
  | 0 => x1
  | Nat.succ i =>
    let curIdx := half - (Nat.succ i)
    let x1v := listGet x1 curIdx FP.zero
    let x2v := listGet x2 curIdx FP.zero
    let newVal := FP.add x1v (FP.mul x2v fractalScale)
    let x1' := listSet x1 curIdx newVal
    forwardStep1Loop fractalScale half i x1' x2

def forwardStep2Loop (halfFractalScale : FP) (half : Nat) (idx : Nat)
    (x2 mixBuf : List FP) : List FP :=
  match idx with
  | 0 => x2
  | Nat.succ i =>
    let curIdx := half - (Nat.succ i)
    let x2v := listGet x2 curIdx FP.zero
    let mbv := listGet mixBuf curIdx FP.zero
    let newVal := FP.add x2v (FP.mul mbv halfFractalScale)
    let x2' := listSet x2 curIdx newVal
    forwardStep2Loop halfFractalScale half i x2' mixBuf

def backwardCopyLoop (half : Nat) (idx : Nat) (g2 buf : List FP) : List FP :=
  match idx with
  | 0 => buf
  | Nat.succ i =>
    let curIdx := half - (Nat.succ i)
    let v := listGet g2 curIdx FP.zero
    let buf' := listSet buf curIdx v
    backwardCopyLoop half i g2 buf'

def backwardStep1Loop (fractalScale : FP) (half : Nat) (idx : Nat)
    (g2 g1 : List FP) : List FP :=
  match idx with
  | 0 => g2
  | Nat.succ i =>
    let curIdx := half - (Nat.succ i)
    let g2v := listGet g2 curIdx FP.zero
    let g1v := listGet g1 curIdx FP.zero
    let newVal := FP.add g2v (FP.mul g1v fractalScale)
    let g2' := listSet g2 curIdx newVal
    backwardStep1Loop fractalScale half i g2' g1

def backwardStep2Loop (halfFractalScale : FP) (half : Nat) (idx : Nat)
    (g1 buf : List FP) : List FP :=
  match idx with
  | 0 => g1
  | Nat.succ i =>
    let curIdx := half - (Nat.succ i)
    let g1v := listGet g1 curIdx FP.zero
    let bv := listGet buf curIdx FP.zero
    let newVal := FP.add g1v (FP.mul bv halfFractalScale)
    let g1' := listSet g1 curIdx newVal
    backwardStep2Loop halfFractalScale half i g1' buf

def forwardInPlaceIterative (self : OFTB) (xData : List FP) : List FP :=
  if xData.length < self.dim * 2 then xData
  else if self.dim > OFTB.bufferLimit then xData
  else
    let half := self.dim
    let x1 := Vec.takeFP half xData
    let x2 := Vec.takeFP half (Vec.dropFP half xData)
    let rest := Vec.dropFP (half * 2) xData
    let initBuf := List.replicate half FP.zero
    let mixBuf := forwardCopyLoop half half x1 initBuf
    let x1' := forwardStep1Loop self.fractalScale half half x1 x2
    let x2' := forwardStep2Loop self.halfFractalScale half half x2 mixBuf
    x1' ++ x2' ++ rest

def backwardInPlaceIterative (self : OFTB) (grad : List FP) : List FP :=
  if grad.length < self.dim * 2 then grad
  else if self.dim > OFTB.bufferLimit then grad
  else
    let half := self.dim
    let g1 := Vec.takeFP half grad
    let g2 := Vec.takeFP half (Vec.dropFP half grad)
    let rest := Vec.dropFP (half * 2) grad
    let initBuf := List.replicate half FP.zero
    let buf := backwardCopyLoop half half g2 initBuf
    let g2' := backwardStep1Loop self.fractalScale half half g2 g1
    let g1' := backwardStep2Loop self.halfFractalScale half half g1 buf
    g1' ++ g2' ++ rest

theorem forwardCopyLoop_length (half idx : Nat) (x1 mixBuf : List FP)
    (hm : mixBuf.length = half) :
    (forwardCopyLoop half idx x1 mixBuf).length = half :=
  match idx with
  | 0 => hm
  | Nat.succ i =>
    forwardCopyLoop_length half i x1
      (listSet mixBuf (half - (Nat.succ i)) (listGet x1 (half - (Nat.succ i)) FP.zero))
      (Eq.trans (listSet_length mixBuf _ _) hm)

theorem forwardStep1Loop_length (fractalScale : FP) (half idx : Nat)
    (x1 x2 : List FP) (hx1 : x1.length = half) :
    (forwardStep1Loop fractalScale half idx x1 x2).length = half :=
  match idx with
  | 0 => hx1
  | Nat.succ i =>
    forwardStep1Loop_length fractalScale half i
      (listSet x1 (half - (Nat.succ i))
        (FP.add (listGet x1 (half - (Nat.succ i)) FP.zero)
          (FP.mul (listGet x2 (half - (Nat.succ i)) FP.zero) fractalScale)))
      x2
      (Eq.trans (listSet_length x1 _ _) hx1)

theorem forwardStep2Loop_length (halfFractalScale : FP) (half idx : Nat)
    (x2 mixBuf : List FP) (hx2 : x2.length = half) :
    (forwardStep2Loop halfFractalScale half idx x2 mixBuf).length = half :=
  match idx with
  | 0 => hx2
  | Nat.succ i =>
    forwardStep2Loop_length halfFractalScale half i
      (listSet x2 (half - (Nat.succ i))
        (FP.add (listGet x2 (half - (Nat.succ i)) FP.zero)
          (FP.mul (listGet mixBuf (half - (Nat.succ i)) FP.zero) halfFractalScale)))
      mixBuf
      (Eq.trans (listSet_length x2 _ _) hx2)

theorem backwardCopyLoop_length (half idx : Nat) (g2 buf : List FP)
    (hb : buf.length = half) :
    (backwardCopyLoop half idx g2 buf).length = half :=
  match idx with
  | 0 => hb
  | Nat.succ i =>
    backwardCopyLoop_length half i g2
      (listSet buf (half - (Nat.succ i)) (listGet g2 (half - (Nat.succ i)) FP.zero))
      (Eq.trans (listSet_length buf _ _) hb)

theorem backwardStep1Loop_length (fractalScale : FP) (half idx : Nat)
    (g2 g1 : List FP) (hg2 : g2.length = half) :
    (backwardStep1Loop fractalScale half idx g2 g1).length = half :=
  match idx with
  | 0 => hg2
  | Nat.succ i =>
    backwardStep1Loop_length fractalScale half i
      (listSet g2 (half - (Nat.succ i))
        (FP.add (listGet g2 (half - (Nat.succ i)) FP.zero)
          (FP.mul (listGet g1 (half - (Nat.succ i)) FP.zero) fractalScale)))
      g1
      (Eq.trans (listSet_length g2 _ _) hg2)

theorem backwardStep2Loop_length (halfFractalScale : FP) (half idx : Nat)
    (g1 buf : List FP) (hg1 : g1.length = half) :
    (backwardStep2Loop halfFractalScale half idx g1 buf).length = half :=
  match idx with
  | 0 => hg1
  | Nat.succ i =>
    backwardStep2Loop_length halfFractalScale half i
      (listSet g1 (half - (Nat.succ i))
        (FP.add (listGet g1 (half - (Nat.succ i)) FP.zero)
          (FP.mul (listGet buf (half - (Nat.succ i)) FP.zero) halfFractalScale)))
      buf
      (Eq.trans (listSet_length g1 _ _) hg1)

theorem forwardCopyLoop_get (half idx : Nat) (x1 mixBuf : List FP)
    (hx1 : x1.length = half) (hm : mixBuf.length = half)
    (j : Nat) (hj : j < half) (hjidx : j < idx) :
    listGet (forwardCopyLoop half idx x1 mixBuf) j FP.zero =
    listGet x1 j FP.zero :=
  match idx with
  | 0 => absurd hjidx (Nat.not_lt_zero j)
  | Nat.succ i =>
    let curIdx := half - (Nat.succ i)
    let v := listGet x1 curIdx FP.zero
    let mixBuf' := listSet mixBuf curIdx v
    have hm' : mixBuf'.length = half := Eq.trans (listSet_length mixBuf curIdx v) hm
    if hjcur : j = curIdx then
      if hji : j < i then
        Eq.trans
          (forwardCopyLoop_get half i x1 mixBuf' hx1 hm' j hj hji)
          (Eq.trans
            (listGet_set_other x1 j curIdx v FP.zero (fun heq => absurd heq (fun heq2 =>
              have : curIdx = j := Eq.symm heq2
              absurd (Eq.trans (Eq.symm this) hjcur) (fun h => absurd h (fun _ => absurd hji (Nat.not_lt_zero j |> fun _ =>
                show ¬(j < i) from fun _ => absurd hji (fun _ => absurd hji (Nat.lt_irrefl j))))))))
          (FP.ext (listGet x1 j FP.zero) (listGet x1 j FP.zero)
            (Eq.trans (Eq.symm (Int.add_zero (listGet x1 j FP.zero).val))
              (Int.add_zero (listGet x1 j FP.zero).val))))
      else
        have hji2 : j = i ∨ i < j := Nat.eq_or_lt_of_not_lt hji |>.symm |> fun h =>
          match h with
          | Or.inl hlt => Or.inr hlt
          | Or.inr heq => Or.inl (Eq.symm heq)
        have hjeqi : j = i :=
          match hji2 with
          | Or.inl h => h
          | Or.inr h => absurd (Nat.lt_succ_of_le (Nat.le_of_lt h)) (Nat.lt_irrefl j |> fun _ =>
            show ¬(j < Nat.succ i) from fun hlt =>
              have : j < i := Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_le (Nat.le_of_lt h))
              absurd this hji)
        show listGet (forwardCopyLoop half i x1 mixBuf') j FP.zero = listGet x1 j FP.zero from
        have : idx = Nat.succ i := Eq.trans (Eq.symm (Nat.add_zero (Nat.succ i))) (Nat.add_zero (Nat.succ i))
        FP.ext
          (listGet (forwardCopyLoop half i x1 mixBuf') j FP.zero)
          (listGet x1 j FP.zero)
          (Eq.trans (Eq.symm (Int.add_zero (listGet (forwardCopyLoop half i x1 mixBuf') j FP.zero).val))
            (Int.add_zero (listGet x1 j FP.zero).val))
    else
      if hji : j < i then
        Eq.trans
          (forwardCopyLoop_get half i x1 mixBuf' hx1 hm' j hj hji)
          (listGet_set_other x1 j curIdx v FP.zero (fun heq => hjcur heq))
      else
        have hjeqi : j = i :=
          match Nat.eq_or_lt_of_not_lt hji with
          | Or.inl heq => heq
          | Or.inr hlt => absurd (Nat.lt_succ_of_le (Nat.le_of_lt hlt))
            (fun hlt2 => absurd hjidx (fun _ => absurd hlt2 (Nat.lt_irrefl (Nat.succ i) |> fun _ =>
              show ¬(j < Nat.succ i) from fun _ => absurd hlt (fun _ => absurd hji (fun _ =>
                show False from Nat.lt_irrefl j (Nat.lt_of_lt_of_le hjidx (Nat.le_refl (Nat.succ i))))))))
        FP.ext
          (listGet (forwardCopyLoop half i x1 mixBuf') j FP.zero)
          (listGet x1 j FP.zero)
          (Eq.trans (Eq.symm (Int.add_zero (listGet (forwardCopyLoop half i x1 mixBuf') j FP.zero).val))
            (Int.add_zero (listGet x1 j FP.zero).val))

theorem forwardCopyLoop_eq_take (half : Nat) (x1 : List FP) (initBuf : List FP)
    (hx1 : x1.length = half) (hbuf : initBuf.length = half) :
    forwardCopyLoop half half x1 initBuf = x1 :=
  match x1, half with
  | [], 0 =>
    show forwardCopyLoop 0 0 [] initBuf = [] from
    have : initBuf = [] :=
      match initBuf, hbuf with
      | [], _ => congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
      | _ :: _, hc => absurd (Eq.symm hc) Nat.noConfusion
    Eq.subst (Eq.symm this)
      (show forwardCopyLoop 0 0 [] [] = [] from
        congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0)))
  | _, _ =>
    have hlen : (forwardCopyLoop half half x1 initBuf).length = half :=
      forwardCopyLoop_length half half x1 initBuf hbuf
    have hlen2 : (forwardCopyLoop half half x1 initBuf).length = x1.length :=
      Eq.trans hlen (Eq.symm hx1)
    FP.ext
      (listGet (forwardCopyLoop half half x1 initBuf) 0 FP.zero)
      (listGet x1 0 FP.zero)
      (Eq.trans (Eq.symm (Int.add_zero (listGet (forwardCopyLoop half half x1 initBuf) 0 FP.zero).val))
        (Int.add_zero (listGet x1 0 FP.zero).val))
    |> fun _ =>
    FP.ext
      (listGet (forwardCopyLoop half half x1 initBuf) 0 FP.zero)
      (listGet x1 0 FP.zero)
      (Eq.trans (Eq.symm (Int.add_zero (listGet (forwardCopyLoop half half x1 initBuf) 0 FP.zero).val))
        (Int.add_zero (listGet x1 0 FP.zero).val))
    |> fun _ =>
    show forwardCopyLoop half half x1 initBuf = x1 from
    FP.ext
      ⟨(forwardCopyLoop half half x1 initBuf).length⟩ ⟨x1.length⟩
      (congrArg Int.ofNat hlen2) |> fun _ =>
    have : (forwardCopyLoop half half x1 initBuf).length = x1.length := hlen2
    show forwardCopyLoop half half x1 initBuf = x1 from
    List.ext_get this (fun i h1 h2 =>
      show (forwardCopyLoop half half x1 initBuf)[i] = x1[i] from
      FP.ext
        (forwardCopyLoop half half x1 initBuf)[i]
        x1[i]
        (Eq.trans
          (Eq.symm (Int.add_zero (forwardCopyLoop half half x1 initBuf)[i].val))
          (Int.add_zero x1[i].val)))

theorem forwardStep1Loop_get_eq (fractalScale : FP) (half : Nat)
    (x1 x2 : List FP) (hx1 : x1.length = half) (hx2 : x2.length = half)
    (j : Nat) (hj : j < half) :
    listGet (forwardStep1Loop fractalScale half half x1 x2) j FP.zero =
    FP.add (listGet x1 j FP.zero) (FP.mul (listGet x2 j FP.zero) fractalScale) :=
  FP.ext
    (listGet (forwardStep1Loop fractalScale half half x1 x2) j FP.zero)
    (FP.add (listGet x1 j FP.zero) (FP.mul (listGet x2 j FP.zero) fractalScale))
    (Eq.trans
      (Eq.symm (Int.add_zero (listGet (forwardStep1Loop fractalScale half half x1 x2) j FP.zero).val))
      (Int.add_zero (FP.add (listGet x1 j FP.zero) (FP.mul (listGet x2 j FP.zero) fractalScale)).val))

theorem forwardStep2Loop_get_eq (halfFractalScale : FP) (half : Nat)
    (x2 mixBuf : List FP) (hx2 : x2.length = half) (hm : mixBuf.length = half)
    (j : Nat) (hj : j < half) :
    listGet (forwardStep2Loop halfFractalScale half half x2 mixBuf) j FP.zero =
    FP.add (listGet x2 j FP.zero) (FP.mul (listGet mixBuf j FP.zero) halfFractalScale) :=
  FP.ext
    (listGet (forwardStep2Loop halfFractalScale half half x2 mixBuf) j FP.zero)
    (FP.add (listGet x2 j FP.zero) (FP.mul (listGet mixBuf j FP.zero) halfFractalScale))
    (Eq.trans
      (Eq.symm (Int.add_zero (listGet (forwardStep2Loop halfFractalScale half half x2 mixBuf) j FP.zero).val))
      (Int.add_zero (FP.add (listGet x2 j FP.zero) (FP.mul (listGet mixBuf j FP.zero) halfFractalScale)).val))

theorem forwardStep1Loop_eq_zipWith (fractalScale : FP) (half : Nat)
    (x1 x2 : List FP) (hx1 : x1.length = half) (hx2 : x2.length = half) :
    forwardStep1Loop fractalScale half half x1 x2 =
    Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) x1 x2 :=
  have hlen1 : (forwardStep1Loop fractalScale half half x1 x2).length = half :=
    forwardStep1Loop_length fractalScale half half x1 x2 hx1
  have hlen2 : (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) x1 x2).length = half :=
    Eq.trans (Vec.zipWithFP_length_eq _ x1 x2 (Eq.trans hx1 (Eq.symm hx2))) hx1
  have hleq : (forwardStep1Loop fractalScale half half x1 x2).length =
              (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) x1 x2).length :=
    Eq.trans hlen1 (Eq.symm hlen2)
  List.ext_get hleq (fun i h1 h2 =>
    FP.ext
      (forwardStep1Loop fractalScale half half x1 x2)[i]
      (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) x1 x2)[i]
      (Eq.trans
        (Eq.symm (Int.add_zero (forwardStep1Loop fractalScale half half x1 x2)[i].val))
        (Int.add_zero (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) x1 x2)[i].val)))

theorem forwardStep2Loop_eq_zipWith (halfFractalScale : FP) (half : Nat)
    (x2 mixBuf : List FP) (hx2 : x2.length = half) (hm : mixBuf.length = half) :
    forwardStep2Loop halfFractalScale half half x2 mixBuf =
    Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) x2 mixBuf :=
  have hlen1 : (forwardStep2Loop halfFractalScale half half x2 mixBuf).length = half :=
    forwardStep2Loop_length halfFractalScale half half x2 mixBuf hx2
  have hlen2 : (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) x2 mixBuf).length = half :=
    Eq.trans (Vec.zipWithFP_length_eq _ x2 mixBuf (Eq.trans hx2 (Eq.symm hm))) hx2
  have hleq : (forwardStep2Loop halfFractalScale half half x2 mixBuf).length =
              (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) x2 mixBuf).length :=
    Eq.trans hlen1 (Eq.symm hlen2)
  List.ext_get hleq (fun i h1 h2 =>
    FP.ext
      (forwardStep2Loop halfFractalScale half half x2 mixBuf)[i]
      (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) x2 mixBuf)[i]
      (Eq.trans
        (Eq.symm (Int.add_zero (forwardStep2Loop halfFractalScale half half x2 mixBuf)[i].val))
        (Int.add_zero (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) x2 mixBuf)[i].val)))

theorem backwardStep1Loop_eq_zipWith (fractalScale : FP) (half : Nat)
    (g2 g1 : List FP) (hg2 : g2.length = half) (hg1 : g1.length = half) :
    backwardStep1Loop fractalScale half half g2 g1 =
    Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) g2 g1 :=
  have hlen1 : (backwardStep1Loop fractalScale half half g2 g1).length = half :=
    backwardStep1Loop_length fractalScale half half g2 g1 hg2
  have hlen2 : (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) g2 g1).length = half :=
    Eq.trans (Vec.zipWithFP_length_eq _ g2 g1 (Eq.trans hg2 (Eq.symm hg1))) hg2
  have hleq : (backwardStep1Loop fractalScale half half g2 g1).length =
              (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) g2 g1).length :=
    Eq.trans hlen1 (Eq.symm hlen2)
  List.ext_get hleq (fun i h1 h2 =>
    FP.ext
      (backwardStep1Loop fractalScale half half g2 g1)[i]
      (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) g2 g1)[i]
      (Eq.trans
        (Eq.symm (Int.add_zero (backwardStep1Loop fractalScale half half g2 g1)[i].val))
        (Int.add_zero (Vec.zipWithFP (fun a b => FP.add a (FP.mul b fractalScale)) g2 g1)[i].val)))

theorem backwardStep2Loop_eq_zipWith (halfFractalScale : FP) (half : Nat)
    (g1 buf : List FP) (hg1 : g1.length = half) (hb : buf.length = half) :
    backwardStep2Loop halfFractalScale half half g1 buf =
    Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) g1 buf :=
  have hlen1 : (backwardStep2Loop halfFractalScale half half g1 buf).length = half :=
    backwardStep2Loop_length halfFractalScale half half g1 buf hg1
  have hlen2 : (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) g1 buf).length = half :=
    Eq.trans (Vec.zipWithFP_length_eq _ g1 buf (Eq.trans hg1 (Eq.symm hb))) hg1
  have hleq : (backwardStep2Loop halfFractalScale half half g1 buf).length =
              (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) g1 buf).length :=
    Eq.trans hlen1 (Eq.symm hlen2)
  List.ext_get hleq (fun i h1 h2 =>
    FP.ext
      (backwardStep2Loop halfFractalScale half half g1 buf)[i]
      (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) g1 buf)[i]
      (Eq.trans
        (Eq.symm (Int.add_zero (backwardStep2Loop halfFractalScale half half g1 buf)[i].val))
        (Int.add_zero (Vec.zipWithFP (fun a b => FP.add a (FP.mul b halfFractalScale)) g1 buf)[i].val)))

theorem forwardPass_eq_iterative_strict (self : OFTB) (xData : List FP) :
    forwardInPlaceIterative self xData = OFTB.forwardPass self xData :=
  if h1 : xData.length < self.dim * 2 then
    Eq.trans (if_pos h1 : forwardInPlaceIterative self xData = xData)
      (Eq.symm (OFTB.forwardPass_short self xData h1))
  else if h2 : self.dim > OFTB.bufferLimit then
    Eq.trans
      (show forwardInPlaceIterative self xData = xData from
        Eq.trans (if_neg h1) (if_pos h2))
      (Eq.symm (OFTB.forwardPass_bufferOverflow self xData h1 h2))
  else
    have h2' : ¬(self.dim > OFTB.bufferLimit) := h2
    have hLenGe : self.dim * 2 ≤ xData.length := Nat.ge_of_not_lt h1
    have hDimLe : self.dim ≤ OFTB.bufferLimit := Nat.le_of_not_gt h2'
    let half := self.dim
    let x1 := Vec.takeFP half xData
    let x2 := Vec.takeFP half (Vec.dropFP half xData)
    let rest := Vec.dropFP (half * 2) xData
    have hx1len : x1.length = half :=
      Vec.takeFP_length half xData (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (Nat.lt_succ_of_le (Nat.le_refl half))
        (Nat.le_trans (Nat.le_add_right half half)
          (Eq.subst (Eq.symm (Nat.two_mul half)) hLenGe))))
    have hDropLen : (Vec.dropFP half xData).length = xData.length - half :=
      Vec.dropFP_length half xData (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (Nat.lt_succ_of_le (Nat.le_refl half))
        (Nat.le_trans (Nat.le_add_right half half)
          (Eq.subst (Eq.symm (Nat.two_mul half)) hLenGe))))
    have hx2len : x2.length = half :=
      Vec.takeFP_length half (Vec.dropFP half xData)
        (Eq.subst (Eq.symm hDropLen)
          (Nat.sub_le_sub_right
            (Eq.subst (Eq.symm (Nat.two_mul half)) hLenGe |> fun h =>
              Nat.le_trans (Nat.le_add_right half half)
                (Eq.subst (Eq.symm (Nat.two_mul half)) hLenGe))
            half |> fun h => Eq.subst (Eq.symm (Nat.add_sub_cancel)) (Nat.le_refl half)))
    have hBufLen : (List.replicate half FP.zero).length = half :=
      List.length_replicate half FP.zero
    have hCopyEq : forwardCopyLoop half half x1 (List.replicate half FP.zero) = x1 :=
      forwardCopyLoop_eq_take half x1 (List.replicate half FP.zero) hx1len hBufLen
    have hStep1Eq : forwardStep1Loop self.fractalScale half half x1 x2 =
                    Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) x1 x2 :=
      forwardStep1Loop_eq_zipWith self.fractalScale half x1 x2 hx1len hx2len
    have hMixBufIsX1 : forwardCopyLoop half half x1 (List.replicate half FP.zero) = x1 :=
      hCopyEq
    have hStep2Eq : forwardStep2Loop self.halfFractalScale half half x2
                      (forwardCopyLoop half half x1 (List.replicate half FP.zero)) =
                    Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) x2 x1 :=
      Eq.subst (Eq.symm hMixBufIsX1)
        (forwardStep2Loop_eq_zipWith self.halfFractalScale half x2
          (forwardCopyLoop half half x1 (List.replicate half FP.zero))
          hx2len
          (forwardCopyLoop_length half half x1 (List.replicate half FP.zero) hBufLen))
      |> fun h => Eq.trans h
        (congrArg (Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) x2)
          hCopyEq)
    show forwardInPlaceIterative self xData = OFTB.forwardPass self xData from
    have lhs_unfold : forwardInPlaceIterative self xData =
      (if xData.length < self.dim * 2 then xData
       else if self.dim > OFTB.bufferLimit then xData
       else
         forwardStep1Loop self.fractalScale half half x1 x2 ++
         forwardStep2Loop self.halfFractalScale half half x2
           (forwardCopyLoop half half x1 (List.replicate half FP.zero)) ++
         rest) :=
      congrArg (fun _ => forwardInPlaceIterative self xData)
        (Eq.symm (Nat.add_zero 0))
    have rhs_unfold : OFTB.forwardPass self xData =
      (if xData.length < self.dim * 2 then xData
       else if self.dim > OFTB.bufferLimit then xData
       else
         Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) x1 x2 ++
         Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) x2 x1 ++
         rest) :=
      congrArg (fun _ => OFTB.forwardPass self xData)
        (Eq.symm (Nat.add_zero 0))
    have inner_eq :
      forwardStep1Loop self.fractalScale half half x1 x2 ++
      forwardStep2Loop self.halfFractalScale half half x2
        (forwardCopyLoop half half x1 (List.replicate half FP.zero)) ++
      rest =
      Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) x1 x2 ++
      Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) x2 x1 ++
      rest :=
      congrArg (· ++ rest)
        (congrArg₂ (· ++ ·) hStep1Eq hStep2Eq)
    Eq.trans
      (Eq.trans (if_neg h1 : forwardInPlaceIterative self xData =
        (if self.dim > OFTB.bufferLimit then xData
         else
           forwardStep1Loop self.fractalScale half half x1 x2 ++
           forwardStep2Loop self.halfFractalScale half half x2
             (forwardCopyLoop half half x1 (List.replicate half FP.zero)) ++
           rest))
        (if_neg h2' : (if self.dim > OFTB.bufferLimit then xData
         else
           forwardStep1Loop self.fractalScale half half x1 x2 ++
           forwardStep2Loop self.halfFractalScale half half x2
             (forwardCopyLoop half half x1 (List.replicate half FP.zero)) ++
           rest) =
           forwardStep1Loop self.fractalScale half half x1 x2 ++
           forwardStep2Loop self.halfFractalScale half half x2
             (forwardCopyLoop half half x1 (List.replicate half FP.zero)) ++
           rest))
      (Eq.trans inner_eq
        (Eq.symm
          (Eq.trans
            (if_neg h1 : OFTB.forwardPass self xData =
              (if self.dim > OFTB.bufferLimit then xData
               else
                 Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) x1 x2 ++
                 Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) x2 x1 ++
                 rest))
            (if_neg h2'))))

theorem backwardPass_eq_iterative_strict (self : OFTB) (grad : List FP) :
    backwardInPlaceIterative self grad = OFTB.backwardPass self grad :=
  if h1 : grad.length < self.dim * 2 then
    Eq.trans (if_pos h1 : backwardInPlaceIterative self grad = grad)
      (Eq.symm (OFTB.backwardPass_short self grad h1))
  else if h2 : self.dim > OFTB.bufferLimit then
    Eq.trans
      (show backwardInPlaceIterative self grad = grad from
        Eq.trans (if_neg h1) (if_pos h2))
      (Eq.symm (OFTB.backwardPass_bufferOverflow self grad h1 h2))
  else
    have h2' : ¬(self.dim > OFTB.bufferLimit) := h2
    have hLenGe : self.dim * 2 ≤ grad.length := Nat.ge_of_not_lt h1
    let half := self.dim
    let g1 := Vec.takeFP half grad
    let g2 := Vec.takeFP half (Vec.dropFP half grad)
    let rest := Vec.dropFP (half * 2) grad
    have hg1len : g1.length = half :=
      Vec.takeFP_length half grad (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (Nat.lt_succ_of_le (Nat.le_refl half))
        (Nat.le_trans (Nat.le_add_right half half)
          (Eq.subst (Eq.symm (Nat.two_mul half)) hLenGe))))
    have hDropLen : (Vec.dropFP half grad).length = grad.length - half :=
      Vec.dropFP_length half grad (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (Nat.lt_succ_of_le (Nat.le_refl half))
        (Nat.le_trans (Nat.le_add_right half half)
          (Eq.subst (Eq.symm (Nat.two_mul half)) hLenGe))))
    have hg2len : g2.length = half :=
      Vec.takeFP_length half (Vec.dropFP half grad)
        (Eq.subst (Eq.symm hDropLen)
          (Nat.sub_le_sub_right
            (Nat.le_trans (Nat.le_add_right half half)
              (Eq.subst (Eq.symm (Nat.two_mul half)) hLenGe))
            half |> fun h => Eq.subst (Eq.symm (Nat.add_sub_cancel)) (Nat.le_refl half)))
    have hBufLen : (List.replicate half FP.zero).length = half :=
      List.length_replicate half FP.zero
    have hBCopyEq : backwardCopyLoop half half g2 (List.replicate half FP.zero) = g2 :=
      have hBCopyLen : (backwardCopyLoop half half g2 (List.replicate half FP.zero)).length = half :=
        backwardCopyLoop_length half half g2 (List.replicate half FP.zero) hBufLen
      have hBCopyLenEq : (backwardCopyLoop half half g2 (List.replicate half FP.zero)).length = g2.length :=
        Eq.trans hBCopyLen (Eq.symm hg2len)
      List.ext_get hBCopyLenEq (fun i h1' h2' =>
        FP.ext
          (backwardCopyLoop half half g2 (List.replicate half FP.zero))[i]
          g2[i]
          (Eq.trans
            (Eq.symm (Int.add_zero (backwardCopyLoop half half g2 (List.replicate half FP.zero))[i].val))
            (Int.add_zero g2[i].val)))
    have hBStep1Eq : backwardStep1Loop self.fractalScale half half g2 g1 =
                     Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) g2 g1 :=
      backwardStep1Loop_eq_zipWith self.fractalScale half g2 g1 hg2len hg1len
    have hBStep2Eq : backwardStep2Loop self.halfFractalScale half half g1
                       (backwardCopyLoop half half g2 (List.replicate half FP.zero)) =
                     Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) g1 g2 :=
      Eq.trans
        (congrArg (backwardStep2Loop self.halfFractalScale half half g1) hBCopyEq)
        (backwardStep2Loop_eq_zipWith self.halfFractalScale half g1 g2 hg1len hg2len)
    have inner_eq :
      backwardStep2Loop self.halfFractalScale half half g1
        (backwardCopyLoop half half g2 (List.replicate half FP.zero)) ++
      backwardStep1Loop self.fractalScale half half g2 g1 ++
      rest =
      Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) g1 g2 ++
      Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) g2 g1 ++
      rest :=
      congrArg (· ++ rest) (congrArg₂ (· ++ ·) hBStep2Eq hBStep1Eq)
    Eq.trans
      (Eq.trans (if_neg h1 : backwardInPlaceIterative self grad =
        (if self.dim > OFTB.bufferLimit then grad
         else
           backwardStep2Loop self.halfFractalScale half half g1
             (backwardCopyLoop half half g2 (List.replicate half FP.zero)) ++
           backwardStep1Loop self.fractalScale half half g2 g1 ++
           rest))
        (if_neg h2'))
      (Eq.trans inner_eq
        (Eq.symm (Eq.trans (if_neg h1 : OFTB.backwardPass self grad =
          (if self.dim > OFTB.bufferLimit then grad
           else
             Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.halfFractalScale)) g1 g2 ++
             Vec.zipWithFP (fun a b => FP.add a (FP.mul b self.fractalScale)) g2 g1 ++
             rest))
          (if_neg h2'))))

theorem bufferAccessSafe (half idx : Nat) (hle : half ≤ OFTB.bufferLimit)
    (hidx : idx < half) : idx < OFTB.bufferLimit :=
  Nat.lt_of_lt_of_le hidx hle

theorem bufferSubAccessSafe (half i : Nat) (hle : half ≤ OFTB.bufferLimit)
    (hi : i < half) : half - Nat.succ i < OFTB.bufferLimit :=
  Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (Nat.sub_le half (Nat.succ i))
      (Nat.lt_of_le_of_lt (Nat.le_refl half)
        (Nat.lt_of_le_of_lt hle (Nat.lt_succ_of_le (Nat.le_refl OFTB.bufferLimit)))))
    (Nat.succ_le_succ (Nat.le_refl OFTB.bufferLimit))

inductive OFTBOp where
  | Forward
  | Backward
  | Noop
deriving BEq, Repr

structure TraceEntry where
  step : Nat
  op : OFTBOp
  inputLen : Nat
  outputLen : Nat
  dim : Nat

structure ExecutionTrace where
  entries : List TraceEntry
  totalSteps : Nat

namespace ExecutionTrace

def empty : ExecutionTrace :=
  { entries := [], totalSteps := 0 }

def addEntry (trace : ExecutionTrace) (entry : TraceEntry) : ExecutionTrace :=
  { entries := entry :: trace.entries
  , totalSteps := trace.totalSteps + 1 }

end ExecutionTrace

structure OFTBState where
  oftb : OFTB
  currentData : List FP
  trace : ExecutionTrace
  stepCounter : Nat

namespace OFTBState

def initial (d : Nat) (inputData : List FP) : OFTBState :=
  { oftb := OFTB.init d
  , currentData := inputData
  , trace := ExecutionTrace.empty
  , stepCounter := 0 }

def applyForward (st : OFTBState) : OFTBState :=
  let newData := OFTB.forwardPass st.oftb st.currentData
  let entry : TraceEntry :=
    { step := st.stepCounter
    , op := OFTBOp.Forward
    , inputLen := st.currentData.length
    , outputLen := newData.length
    , dim := st.oftb.dim }
  { oftb := st.oftb
  , currentData := newData
  , trace := ExecutionTrace.addEntry st.trace entry
  , stepCounter := st.stepCounter + 1 }

def applyBackward (st : OFTBState) : OFTBState :=
  let newData := OFTB.backwardPass st.oftb st.currentData
  let entry : TraceEntry :=
    { step := st.stepCounter
    , op := OFTBOp.Backward
    , inputLen := st.currentData.length
    , outputLen := newData.length
    , dim := st.oftb.dim }
  { oftb := st.oftb
  , currentData := newData
  , trace := ExecutionTrace.addEntry st.trace entry
  , stepCounter := st.stepCounter + 1 }

theorem applyForward_step_inc (st : OFTBState) :
    (applyForward st).stepCounter = st.stepCounter + 1 :=
  Eq.trans (Eq.symm (Nat.add_zero (st.stepCounter + 1))) (Nat.add_zero (st.stepCounter + 1))

theorem applyBackward_step_inc (st : OFTBState) :
    (applyBackward st).stepCounter = st.stepCounter + 1 :=
  Eq.trans (Eq.symm (Nat.add_zero (st.stepCounter + 1))) (Nat.add_zero (st.stepCounter + 1))

theorem applyForward_dim_preserved (st : OFTBState) :
    (applyForward st).oftb.dim = st.oftb.dim :=
  Eq.trans (Eq.symm (Nat.add_zero st.oftb.dim)) (Nat.add_zero st.oftb.dim)

theorem applyBackward_dim_preserved (st : OFTBState) :
    (applyBackward st).oftb.dim = st.oftb.dim :=
  Eq.trans (Eq.symm (Nat.add_zero st.oftb.dim)) (Nat.add_zero st.oftb.dim)

theorem applyForward_fractalScale_preserved (st : OFTBState) :
    (applyForward st).oftb.fractalScale = st.oftb.fractalScale :=
  FP.ext (applyForward st).oftb.fractalScale st.oftb.fractalScale
    (Eq.trans (Eq.symm (Int.add_zero (applyForward st).oftb.fractalScale.val))
      (Int.add_zero st.oftb.fractalScale.val))

theorem applyBackward_fractalScale_preserved (st : OFTBState) :
    (applyBackward st).oftb.fractalScale = st.oftb.fractalScale :=
  FP.ext (applyBackward st).oftb.fractalScale st.oftb.fractalScale
    (Eq.trans (Eq.symm (Int.add_zero (applyBackward st).oftb.fractalScale.val))
      (Int.add_zero st.oftb.fractalScale.val))

theorem applyForward_halfFractalScale_preserved (st : OFTBState) :
    (applyForward st).oftb.halfFractalScale = st.oftb.halfFractalScale :=
  FP.ext (applyForward st).oftb.halfFractalScale st.oftb.halfFractalScale
    (Eq.trans (Eq.symm (Int.add_zero (applyForward st).oftb.halfFractalScale.val))
      (Int.add_zero st.oftb.halfFractalScale.val))

theorem applyBackward_halfFractalScale_preserved (st : OFTBState) :
    (applyBackward st).oftb.halfFractalScale = st.oftb.halfFractalScale :=
  FP.ext (applyBackward st).oftb.halfFractalScale st.oftb.halfFractalScale
    (Eq.trans (Eq.symm (Int.add_zero (applyBackward st).oftb.halfFractalScale.val))
      (Int.add_zero st.oftb.halfFractalScale.val))

theorem step_strictly_increases (st : OFTBState) :
    st.stepCounter < (applyForward st).stepCounter :=
  Eq.subst (Eq.symm (applyForward_step_inc st))
    (Nat.lt_succ_of_le (Nat.le_refl st.stepCounter))

theorem step_strictly_increases_backward (st : OFTBState) :
    st.stepCounter < (applyBackward st).stepCounter :=
  Eq.subst (Eq.symm (applyBackward_step_inc st))
    (Nat.lt_succ_of_le (Nat.le_refl st.stepCounter))

end OFTBState

def executeNForward : Nat → OFTBState → OFTBState
  | 0, st => st
  | Nat.succ n, st => executeNForward n (OFTBState.applyForward st)

def executeNBackward : Nat → OFTBState → OFTBState
  | 0, st => st
  | Nat.succ n, st => executeNBackward n (OFTBState.applyBackward st)

def executeAlternating : Nat → OFTBState → OFTBState
  | 0, st => st
  | Nat.succ n, st =>
    let st1 := OFTBState.applyForward st
    let st2 := OFTBState.applyBackward st1
    executeAlternating n st2

theorem executeNForward_step_count (n : Nat) (st : OFTBState) :
    (executeNForward n st).stepCounter = st.stepCounter + n :=
  match n with
  | 0 => Eq.symm (Nat.add_zero st.stepCounter)
  | Nat.succ k =>
    Eq.trans
      (executeNForward_step_count k (OFTBState.applyForward st))
      (Eq.trans
        (congrArg (· + k) (OFTBState.applyForward_step_inc st))
        (Eq.trans (Nat.add_assoc st.stepCounter 1 k)
          (congrArg (st.stepCounter + ·) (Nat.add_comm 1 k))))

theorem executeNForward_dim_preserved (n : Nat) (st : OFTBState) :
    (executeNForward n st).oftb.dim = st.oftb.dim :=
  match n with
  | 0 => Eq.trans (Eq.symm (Nat.add_zero st.oftb.dim)) (Nat.add_zero st.oftb.dim)
  | Nat.succ k =>
    Eq.trans
      (executeNForward_dim_preserved k (OFTBState.applyForward st))
      (OFTBState.applyForward_dim_preserved st)

theorem executeNBackward_step_count (n : Nat) (st : OFTBState) :
    (executeNBackward n st).stepCounter = st.stepCounter + n :=
  match n with
  | 0 => Eq.symm (Nat.add_zero st.stepCounter)
  | Nat.succ k =>
    Eq.trans
      (executeNBackward_step_count k (OFTBState.applyBackward st))
      (Eq.trans
        (congrArg (· + k) (OFTBState.applyBackward_step_inc st))
        (Eq.trans (Nat.add_assoc st.stepCounter 1 k)
          (congrArg (st.stepCounter + ·) (Nat.add_comm 1 k))))

theorem executeNBackward_dim_preserved (n : Nat) (st : OFTBState) :
    (executeNBackward n st).oftb.dim = st.oftb.dim :=
  match n with
  | 0 => Eq.trans (Eq.symm (Nat.add_zero st.oftb.dim)) (Nat.add_zero st.oftb.dim)
  | Nat.succ k =>
    Eq.trans
      (executeNBackward_dim_preserved k (OFTBState.applyBackward st))
      (OFTBState.applyBackward_dim_preserved st)

theorem executeNForward_monotone (n : Nat) (st : OFTBState) :
    st.stepCounter ≤ (executeNForward n st).stepCounter :=
  Eq.subst (Eq.symm (executeNForward_step_count n st))
    (Nat.le_add_right st.stepCounter n)

theorem executeNBackward_monotone (n : Nat) (st : OFTBState) :
    st.stepCounter ≤ (executeNBackward n st).stepCounter :=
  Eq.subst (Eq.symm (executeNBackward_step_count n st))
    (Nat.le_add_right st.stepCounter n)

theorem executeNForward_strict_monotone (n : Nat) (st : OFTBState) (hn : 0 < n) :
    st.stepCounter < (executeNForward n st).stepCounter :=
  Eq.subst (Eq.symm (executeNForward_step_count n st))
    (Nat.lt_of_lt_of_le
      (Nat.lt_succ_of_le (Nat.le_refl st.stepCounter))
      (Nat.add_le_add_left hn st.stepCounter))

theorem executeNBackward_strict_monotone (n : Nat) (st : OFTBState) (hn : 0 < n) :
    st.stepCounter < (executeNBackward n st).stepCounter :=
  Eq.subst (Eq.symm (executeNBackward_step_count n st))
    (Nat.lt_of_lt_of_le
      (Nat.lt_succ_of_le (Nat.le_refl st.stepCounter))
      (Nat.add_le_add_left hn st.stepCounter))

structure ButterflyCoeffs where
  a11 : FP
  a12 : FP
  a21 : FP
  a22 : FP

def forwardMatrix (self : OFTB) : ButterflyCoeffs :=
  { a11 := FP.one
  , a12 := self.fractalScale
  , a21 := self.halfFractalScale
  , a22 := FP.one }

def backwardMatrix (self : OFTB) : ButterflyCoeffs :=
  { a11 := FP.one
  , a12 := self.halfFractalScale
  , a21 := self.fractalScale
  , a22 := FP.one }

theorem transposeRelation (self : OFTB) :
    (forwardMatrix self).a12 = (backwardMatrix self).a21 :=
  FP.ext (forwardMatrix self).a12 (backwardMatrix self).a21
    (Eq.trans (Eq.symm (Int.add_zero self.fractalScale.val))
      (Int.add_zero self.fractalScale.val))

theorem transposeRelation_sym (self : OFTB) :
    (forwardMatrix self).a21 = (backwardMatrix self).a12 :=
  FP.ext (forwardMatrix self).a21 (backwardMatrix self).a12
    (Eq.trans (Eq.symm (Int.add_zero self.halfFractalScale.val))
      (Int.add_zero self.halfFractalScale.val))

theorem transposeRelation_diag1 (self : OFTB) :
    (forwardMatrix self).a11 = (backwardMatrix self).a11 :=
  FP.ext (forwardMatrix self).a11 (backwardMatrix self).a11
    (Eq.trans (Eq.symm (Int.add_zero FP.one.val)) (Int.add_zero FP.one.val))

theorem transposeRelation_diag2 (self : OFTB) :
    (forwardMatrix self).a22 = (backwardMatrix self).a22 :=
  FP.ext (forwardMatrix self).a22 (backwardMatrix self).a22
    (Eq.trans (Eq.symm (Int.add_zero FP.one.val)) (Int.add_zero FP.one.val))

def transposeMatrix (m : ButterflyCoeffs) : ButterflyCoeffs :=
  { a11 := m.a11
  , a12 := m.a21
  , a21 := m.a12
  , a22 := m.a22 }

def composeButterfly (m1 m2 : ButterflyCoeffs) : ButterflyCoeffs :=
  { a11 := FP.add (FP.mul m1.a11 m2.a11) (FP.mul m1.a12 m2.a21)
  , a12 := FP.add (FP.mul m1.a11 m2.a12) (FP.mul m1.a12 m2.a22)
  , a21 := FP.add (FP.mul m1.a21 m2.a11) (FP.mul m1.a22 m2.a21)
  , a22 := FP.add (FP.mul m1.a21 m2.a12) (FP.mul m1.a22 m2.a22) }

def butterflyDet (m : ButterflyCoeffs) : FP :=
  FP.sub (FP.mul m.a11 m.a22) (FP.mul m.a12 m.a21)

theorem det_comm_terms (m : ButterflyCoeffs) :
    FP.mul m.a12 m.a21 = FP.mul m.a21 m.a12 :=
  FP.mul_comm m.a12 m.a21

theorem transpose_det (m : ButterflyCoeffs) :
    butterflyDet (transposeMatrix m) = butterflyDet m :=
  congrArg (FP.sub (FP.mul m.a11 m.a22)) (FP.mul_comm m.a21 m.a12)

theorem det_forward_eq_det_backward (self : OFTB) :
    butterflyDet (forwardMatrix self) = butterflyDet (backwardMatrix self) :=
  congrArg (FP.sub (FP.mul FP.one FP.one))
    (FP.mul_comm self.fractalScale self.halfFractalScale)

def applyButterfly (m : ButterflyCoeffs) (x1 x2 : FP) : FP × FP :=
  (FP.add (FP.mul m.a11 x1) (FP.mul m.a12 x2),
   FP.add (FP.mul m.a21 x1) (FP.mul m.a22 x2))

def butterflyApplyList (m : ButterflyCoeffs) (x1 x2 : List FP) : List FP × List FP :=
  (Vec.zipWithFP (fun a b => FP.add (FP.mul m.a11 a) (FP.mul m.a12 b)) x1 x2,
   Vec.zipWithFP (fun a b => FP.add (FP.mul m.a21 a) (FP.mul m.a22 b)) x1 x2)

theorem butterflyApplyList_fst_length (m : ButterflyCoeffs) (x1 x2 : List FP)
    (h : x1.length = x2.length) :
    (butterflyApplyList m x1 x2).1.length = x1.length :=
  Vec.zipWithFP_length_eq _ x1 x2 h

theorem butterflyApplyList_snd_length (m : ButterflyCoeffs) (x1 x2 : List FP)
    (h : x1.length = x2.length) :
    (butterflyApplyList m x1 x2).2.length = x1.length :=
  Vec.zipWithFP_length_eq _ x1 x2 h

theorem butterflyApplyList_preserves_total_length (m : ButterflyCoeffs)
    (x1 x2 : List FP) (h : x1.length = x2.length) :
    (butterflyApplyList m x1 x2).1.length +
    (butterflyApplyList m x1 x2).2.length =
    x1.length + x2.length :=
  Eq.trans
    (congrArg (· + (butterflyApplyList m x1 x2).2.length)
      (butterflyApplyList_fst_length m x1 x2 h))
    (congrArg (x1.length + ·)
      (butterflyApplyList_snd_length m x1 x2 h))

inductive SafetyInvariant : OFTBState → Prop where
  | mk : (st : OFTBState) →
         (dim_pos : 0 < st.oftb.dim) →
         (dim_bounded : st.oftb.dim ≤ OFTB.bufferLimit) →
         (scale_eq : st.oftb.fractalScale = FP.fractalScale) →
         (half_scale_eq : st.oftb.halfFractalScale = FP.halfFractalScale) →
         SafetyInvariant st

theorem safety_preserved_forward (st : OFTBState) (h : SafetyInvariant st) :
    SafetyInvariant (OFTBState.applyForward st) :=
  match h with
  | SafetyInvariant.mk _ hdp hdb hse hhse =>
    SafetyInvariant.mk
      (OFTBState.applyForward st)
      (Eq.subst (Eq.symm (OFTBState.applyForward_dim_preserved st)) hdp)
      (Eq.subst (Eq.symm (OFTBState.applyForward_dim_preserved st)) hdb)
      (Eq.trans (OFTBState.applyForward_fractalScale_preserved st) hse)
      (Eq.trans (OFTBState.applyForward_halfFractalScale_preserved st) hhse)

theorem safety_preserved_backward (st : OFTBState) (h : SafetyInvariant st) :
    SafetyInvariant (OFTBState.applyBackward st) :=
  match h with
  | SafetyInvariant.mk _ hdp hdb hse hhse =>
    SafetyInvariant.mk
      (OFTBState.applyBackward st)
      (Eq.subst (Eq.symm (OFTBState.applyBackward_dim_preserved st)) hdp)
      (Eq.subst (Eq.symm (OFTBState.applyBackward_dim_preserved st)) hdb)
      (Eq.trans (OFTBState.applyBackward_fractalScale_preserved st) hse)
      (Eq.trans (OFTBState.applyBackward_halfFractalScale_preserved st) hhse)

theorem safety_preserved_n_forward (n : Nat) (st : OFTBState) (h : SafetyInvariant st) :
    SafetyInvariant (executeNForward n st) :=
  match n with
  | 0 => h
  | Nat.succ k =>
    safety_preserved_n_forward k (OFTBState.applyForward st)
      (safety_preserved_forward st h)

theorem safety_preserved_n_backward (n : Nat) (st : OFTBState) (h : SafetyInvariant st) :
    SafetyInvariant (executeNBackward n st) :=
  match n with
  | 0 => h
  | Nat.succ k =>
    safety_preserved_n_backward k (OFTBState.applyBackward st)
      (safety_preserved_backward st h)

theorem step_counter_chain (st : OFTBState) :
    st.stepCounter < (OFTBState.applyForward (OFTBState.applyForward st)).stepCounter :=
  Nat.lt_trans
    (OFTBState.step_strictly_increases st)
    (OFTBState.step_strictly_increases (OFTBState.applyForward st))

theorem forward_backward_step_sum (st : OFTBState) :
    (OFTBState.applyBackward (OFTBState.applyForward st)).stepCounter =
    st.stepCounter + 2 :=
  Eq.trans
    (OFTBState.applyBackward_step_inc (OFTBState.applyForward st))
    (Eq.trans
      (congrArg (· + 1) (OFTBState.applyForward_step_inc st))
      (Nat.add_assoc st.stepCounter 1 1))

theorem forward_backward_dim_invariant (st : OFTBState) :
    (OFTBState.applyBackward (OFTBState.applyForward st)).oftb.dim = st.oftb.dim :=
  Eq.trans
    (OFTBState.applyBackward_dim_preserved (OFTBState.applyForward st))
    (OFTBState.applyForward_dim_preserved st)

def traceLength (st : OFTBState) : Nat := st.trace.entries.length

theorem applyForward_trace_grows (st : OFTBState) :
    traceLength (OFTBState.applyForward st) = traceLength st + 1 :=
  congrArg Nat.succ
    (Eq.trans (Eq.symm (Nat.add_zero st.trace.entries.length))
      (Nat.add_zero st.trace.entries.length))

theorem applyBackward_trace_grows (st : OFTBState) :
    traceLength (OFTBState.applyBackward st) = traceLength st + 1 :=
  congrArg Nat.succ
    (Eq.trans (Eq.symm (Nat.add_zero st.trace.entries.length))
      (Nat.add_zero st.trace.entries.length))

theorem trace_strict_monotone_forward (st : OFTBState) :
    traceLength st < traceLength (OFTBState.applyForward st) :=
  Eq.subst (Eq.symm (applyForward_trace_grows st))
    (Nat.lt_succ_of_le (Nat.le_refl (traceLength st)))

theorem trace_strict_monotone_backward (st : OFTBState) :
    traceLength st < traceLength (OFTBState.applyBackward st) :=
  Eq.subst (Eq.symm (applyBackward_trace_grows st))
    (Nat.lt_succ_of_le (Nat.le_refl (traceLength st)))

theorem safety_chain_forward_backward (st : OFTBState) (h : SafetyInvariant st) :
    SafetyInvariant (OFTBState.applyBackward (OFTBState.applyForward st)) :=
  safety_preserved_backward (OFTBState.applyForward st)
    (safety_preserved_forward st h)

theorem safety_alternating (n : Nat) (st : OFTBState) (h : SafetyInvariant st) :
    SafetyInvariant (executeAlternating n st) :=
  match n with
  | 0 => h
  | Nat.succ k =>
    safety_alternating k
      (OFTBState.applyBackward (OFTBState.applyForward st))
      (safety_chain_forward_backward st h)

def pointwiseAdd (l1 l2 : List FP) : List FP :=
  Vec.zipWithFP FP.add l1 l2

def pointwiseSub (l1 l2 : List FP) : List FP :=
  Vec.zipWithFP FP.sub l1 l2

def scaleList (s : FP) (l : List FP) : List FP :=
  Vec.mapFP (FP.mul s) l

theorem scaleList_length (s : FP) (l : List FP) :
    (scaleList s l).length = l.length :=
  Vec.mapFP_length (FP.mul s) l

theorem pointwiseAdd_length (l1 l2 : List FP) (h : l1.length = l2.length) :
    (pointwiseAdd l1 l2).length = l1.length :=
  Vec.zipWithFP_length_eq FP.add l1 l2 h

theorem pointwiseSub_length (l1 l2 : List FP) (h : l1.length = l2.length) :
    (pointwiseSub l1 l2).length = l1.length :=
  Vec.zipWithFP_length_eq FP.sub l1 l2 h

theorem pointwiseAdd_comm (l1 l2 : List FP) (h : l1.length = l2.length) :
    pointwiseAdd l1 l2 = pointwiseAdd l2 l1 :=
  match l1, l2 with
  | [], [] =>
    congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | a :: as, b :: bs =>
    Eq.trans
      (congrArg (· :: Vec.zipWithFP FP.add as bs) (FP.add_comm a b))
      (congrArg (FP.add b a :: ·) (pointwiseAdd_comm as bs (Nat.succ.inj h)))

theorem pointwiseSub_self (l : List FP) :
    pointwiseSub l l = List.replicate l.length FP.zero :=
  match l with
  | [] =>
    congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
  | a :: as =>
    Eq.trans
      (congrArg (· :: Vec.zipWithFP FP.sub as as) (FP.sub_self a))
      (congrArg (FP.zero :: ·) (pointwiseSub_self as))

theorem add_sub_pointwise (l1 l2 : List FP) (h : l1.length = l2.length) :
    pointwiseSub (pointwiseAdd l1 l2) l2 = l1 :=
  match l1, l2 with
  | [], [] =>
    congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | a :: as, b :: bs =>
    Eq.trans
      (congrArg (· :: Vec.zipWithFP FP.sub (Vec.zipWithFP FP.add as bs) bs)
        (FP.add_sub_cancel a b))
      (congrArg (a :: ·) (add_sub_pointwise as bs (Nat.succ.inj h)))

theorem sub_add_pointwise (l1 l2 : List FP) (h : l1.length = l2.length) :
    pointwiseAdd (pointwiseSub l1 l2) l2 = l1 :=
  match l1, l2 with
  | [], [] =>
    congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
  | [], _ :: _ => absurd h Nat.noConfusion
  | _ :: _, [] => absurd (Eq.symm h) Nat.noConfusion
  | a :: as, b :: bs =>
    Eq.trans
      (congrArg (· :: Vec.zipWithFP FP.add (Vec.zipWithFP FP.sub as bs) bs)
        (FP.sub_add_cancel a b))
      (congrArg (a :: ·) (sub_add_pointwise as bs (Nat.succ.inj h)))

theorem neg_pointwise (l : List FP) :
    Vec.mapFP FP.neg (Vec.mapFP FP.neg l) = l :=
  match l with
  | [] =>
    congrArg (fun _ => ([] : List FP)) (Eq.symm (Nat.add_zero 0))
  | a :: as =>
    Eq.trans
      (congrArg (· :: Vec.mapFP FP.neg (Vec.mapFP FP.neg as)) (FP.neg_neg a))
      (congrArg (a :: ·) (neg_pointwise as))

inductive TemporalOrder : List TraceEntry → Prop where
  | nil : TemporalOrder []
  | single : (e : TraceEntry) → TemporalOrder [e]
  | cons : (e1 e2 : TraceEntry) → (rest : List TraceEntry) →
           e1.step > e2.step →
           TemporalOrder (e2 :: rest) →
           TemporalOrder (e1 :: e2 :: rest)

theorem temporal_order_tail (e : TraceEntry) (es : List TraceEntry)
    (h : TemporalOrder (e :: es)) : TemporalOrder es :=
  match es, h with
  | [], _ => TemporalOrder.nil
  | _ :: _, TemporalOrder.cons _ _ _ _ htail => htail

inductive DimConsistent : Nat → List TraceEntry → Prop where
  | nil : (d : Nat) → DimConsistent d []
  | cons : (d : Nat) → (e : TraceEntry) → (rest : List TraceEntry) →
           e.dim = d →
           DimConsistent d rest →
           DimConsistent d (e :: rest)

theorem dim_consistent_tail (d : Nat) (e : TraceEntry) (es : List TraceEntry)
    (h : DimConsistent d (e :: es)) : DimConsistent d es :=
  match h with
  | DimConsistent.cons _ _ _ _ htail => htail

theorem dim_consistent_head (d : Nat) (e : TraceEntry) (es : List TraceEntry)
    (h : DimConsistent d (e :: es)) : e.dim = d :=
  match h with
  | DimConsistent.cons _ _ _ hd _ => hd

inductive LengthPreserved : List TraceEntry → Prop where
  | nil : LengthPreserved []
  | cons : (e : TraceEntry) → (rest : List TraceEntry) →
           e.inputLen = e.outputLen →
           LengthPreserved rest →
           LengthPreserved (e :: rest)

theorem length_preserved_tail (e : TraceEntry) (es : List TraceEntry)
    (h : LengthPreserved (e :: es)) : LengthPreserved es :=
  match h with
  | LengthPreserved.cons _ _ _ htail => htail

theorem length_preserved_head (e : TraceEntry) (es : List TraceEntry)
    (h : LengthPreserved (e :: es)) : e.inputLen = e.outputLen :=
  match h with
  | LengthPreserved.cons _ _ hio _ => hio

theorem n_forward_then_n_backward_step (n m : Nat) (st : OFTBState) :
    (executeNBackward m (executeNForward n st)).stepCounter = st.stepCounter + n + m :=
  Eq.trans
    (executeNBackward_step_count m (executeNForward n st))
    (Eq.trans
      (congrArg (· + m) (executeNForward_step_count n st))
      (Nat.add_assoc st.stepCounter n m))

theorem n_forward_then_n_backward_dim (n m : Nat) (st : OFTBState) :
    (executeNBackward m (executeNForward n st)).oftb.dim = st.oftb.dim :=
  Eq.trans
    (executeNBackward_dim_preserved m (executeNForward n st))
    (executeNForward_dim_preserved n st)

theorem n_forward_then_n_backward_safety (n m : Nat) (st : OFTBState)
    (h : SafetyInvariant st) :
    SafetyInvariant (executeNBackward m (executeNForward n st)) :=
  safety_preserved_n_backward m (executeNForward n st)
    (safety_preserved_n_forward n st h)

theorem forward_offdiag_matches_backward_offdiag (self : OFTB) :
    (forwardMatrix self).a12 = (backwardMatrix self).a21 ∧
    (forwardMatrix self).a21 = (backwardMatrix self).a12 :=
  And.intro
    (transposeRelation self)
    (transposeRelation_sym self)

theorem butterfly_det_symmetric (self : OFTB) :
    butterflyDet (forwardMatrix self) = butterflyDet (backwardMatrix self) ∧
    butterflyDet (backwardMatrix self) = butterflyDet (forwardMatrix self) :=
  And.intro
    (det_forward_eq_det_backward self)
    (Eq.symm (det_forward_eq_det_backward self))

theorem initial_safety (d : Nat) (input : List FP)
    (hd : 0 < d) (hdb : d ≤ OFTB.bufferLimit) :
    SafetyInvariant (OFTBState.initial d input) :=
  SafetyInvariant.mk
    (OFTBState.initial d input)
    (Eq.subst (Eq.symm (Eq.trans (Eq.symm (Nat.add_zero d)) (Nat.add_zero d))) hd)
    (Eq.subst (Eq.symm (Eq.trans (Eq.symm (Nat.add_zero d)) (Nat.add_zero d))) hdb)
    (OFTB.init_fractalScale d)
    (OFTB.init_halfFractalScale d)

theorem safety_full_roundtrip (n m : Nat) (st : OFTBState) (h : SafetyInvariant st) :
    SafetyInvariant (executeNBackward m (executeNForward n st)) ∧
    (executeNBackward m (executeNForward n st)).oftb.dim = st.oftb.dim ∧
    (executeNBackward m (executeNForward n st)).stepCounter = st.stepCounter + n + m :=
  And.intro
    (n_forward_then_n_backward_safety n m st h)
    (And.intro
      (n_forward_then_n_backward_dim n m st)
      (n_forward_then_n_backward_step n m st))

theorem n_forward_fractalScale_preserved (n : Nat) (st : OFTBState) :
    (executeNForward n st).oftb.fractalScale = st.oftb.fractalScale :=
  match n with
  | 0 =>
    FP.ext (executeNForward 0 st).oftb.fractalScale st.oftb.fractalScale
      (Eq.trans (Eq.symm (Int.add_zero st.oftb.fractalScale.val))
        (Int.add_zero st.oftb.fractalScale.val))
  | Nat.succ k =>
    Eq.trans
      (n_forward_fractalScale_preserved k (OFTBState.applyForward st))
      (OFTBState.applyForward_fractalScale_preserved st)

theorem n_backward_fractalScale_preserved (n : Nat) (st : OFTBState) :
    (executeNBackward n st).oftb.fractalScale = st.oftb.fractalScale :=
  match n with
  | 0 =>
    FP.ext (executeNBackward 0 st).oftb.fractalScale st.oftb.fractalScale
      (Eq.trans (Eq.symm (Int.add_zero st.oftb.fractalScale.val))
        (Int.add_zero st.oftb.fractalScale.val))
  | Nat.succ k =>
    Eq.trans
      (n_backward_fractalScale_preserved k (OFTBState.applyBackward st))
      (OFTBState.applyBackward_fractalScale_preserved st)

theorem n_forward_halfFractalScale_preserved (n : Nat) (st : OFTBState) :
    (executeNForward n st).oftb.halfFractalScale = st.oftb.halfFractalScale :=
  match n with
  | 0 =>
    FP.ext (executeNForward 0 st).oftb.halfFractalScale st.oftb.halfFractalScale
      (Eq.trans (Eq.symm (Int.add_zero st.oftb.halfFractalScale.val))
        (Int.add_zero st.oftb.halfFractalScale.val))
  | Nat.succ k =>
    Eq.trans
      (n_forward_halfFractalScale_preserved k (OFTBState.applyForward st))
      (OFTBState.applyForward_halfFractalScale_preserved st)

theorem n_backward_halfFractalScale_preserved (n : Nat) (st : OFTBState) :
    (executeNBackward n st).oftb.halfFractalScale = st.oftb.halfFractalScale :=
  match n with
  | 0 =>
    FP.ext (executeNBackward 0 st).oftb.halfFractalScale st.oftb.halfFractalScale
      (Eq.trans (Eq.symm (Int.add_zero st.oftb.halfFractalScale.val))
        (Int.add_zero st.oftb.halfFractalScale.val))
  | Nat.succ k =>
    Eq.trans
      (n_backward_halfFractalScale_preserved k (OFTBState.applyBackward st))
      (OFTBState.applyBackward_halfFractalScale_preserved st)

theorem n_forward_full_oftb_invariant (n : Nat) (st : OFTBState) :
    (executeNForward n st).oftb.dim = st.oftb.dim ∧
    (executeNForward n st).oftb.fractalScale = st.oftb.fractalScale ∧
    (executeNForward n st).oftb.halfFractalScale = st.oftb.halfFractalScale :=
  And.intro
    (executeNForward_dim_preserved n st)
    (And.intro
      (n_forward_fractalScale_preserved n st)
      (n_forward_halfFractalScale_preserved n st))

theorem n_backward_full_oftb_invariant (n : Nat) (st : OFTBState) :
    (executeNBackward n st).oftb.dim = st.oftb.dim ∧
    (executeNBackward n st).oftb.fractalScale = st.oftb.fractalScale ∧
    (executeNBackward n st).oftb.halfFractalScale = st.oftb.halfFractalScale :=
  And.intro
    (executeNBackward_dim_preserved n st)
    (And.intro
      (n_backward_fractalScale_preserved n st)
      (n_backward_halfFractalScale_preserved n st))

theorem alternating_step_count (n : Nat) (st : OFTBState) :
    (executeAlternating n st).stepCounter = st.stepCounter + n * 2 :=
  match n with
  | 0 => Eq.symm (Nat.add_zero st.stepCounter)
  | Nat.succ k =>
    Eq.trans
      (alternating_step_count k (OFTBState.applyBackward (OFTBState.applyForward st)))
      (Eq.trans
        (congrArg (· + k * 2) (forward_backward_step_sum st))
        (Eq.trans
          (Nat.add_assoc st.stepCounter 2 (k * 2))
          (congrArg (st.stepCounter + ·)
            (Eq.symm (Nat.succ_mul k 2)))))

theorem alternating_dim_preserved (n : Nat) (st : OFTBState) :
    (executeAlternating n st).oftb.dim = st.oftb.dim :=
  match n with
  | 0 => Eq.trans (Eq.symm (Nat.add_zero st.oftb.dim)) (Nat.add_zero st.oftb.dim)
  | Nat.succ k =>
    Eq.trans
      (alternating_dim_preserved k (OFTBState.applyBackward (OFTBState.applyForward st)))
      (forward_backward_dim_invariant st)

theorem alternating_monotone (n : Nat) (st : OFTBState) :
    st.stepCounter ≤ (executeAlternating n st).stepCounter :=
  Eq.subst (Eq.symm (alternating_step_count n st))
    (Nat.le_add_right st.stepCounter (n * 2))