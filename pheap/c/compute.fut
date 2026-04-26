let clip_min : f32 = -5.0f32
let clip_max : f32 =  5.0f32
let fractal_scale : f32 = 0.7071067811865475f32

let clip (x: f32) : f32 =
  if x < clip_min then clip_min
  else if x > clip_max then clip_max
  else x

let is_clipped (x: f32) : bool =
  x <= clip_min || x >= clip_max

let matvec [m][n] (w: [m][n]f32) (x: [n]f32) : [m]f32 =
  map (\row -> f32.sum (map2 (*) row x)) w

let outer [m][n] (a: [m]f32) (b: [n]f32) : [m][n]f32 =
  map (\u -> map (\v -> u * v) b) a

let rsf_scale [d]
              (w_s: [d][d]f32) (b_s: [d]f32) (x2: [d]f32) : [d]f32 =
  map2 (\b v -> f32.exp (clip (b + v))) b_s (matvec w_s x2)

let rsf_pre_s [d]
              (w_s: [d][d]f32) (b_s: [d]f32) (x2: [d]f32) : [d]f32 =
  map2 (+) b_s (matvec w_s x2)

let rsf_trans [d]
              (w_t: [d][d]f32) (b_t: [d]f32) (y1: [d]f32) : [d]f32 =
  map2 (+) b_t (matvec w_t y1)

entry rsf_forward [d]
                  (w_s: [d][d]f32) (b_s: [d]f32)
                  (w_t: [d][d]f32) (b_t: [d]f32)
                  (x1:  [d]f32)    (x2:  [d]f32)
                : ([d]f32, [d]f32) =
  let scale = rsf_scale w_s b_s x2
  let y1    = map2 (*) x1 scale
  let trans = rsf_trans w_t b_t y1
  let y2    = map2 (+) x2 trans
  in (y1, y2)

entry rsf_inverse [d]
                  (w_s: [d][d]f32) (b_s: [d]f32)
                  (w_t: [d][d]f32) (b_t: [d]f32)
                  (y1:  [d]f32)    (y2:  [d]f32)
                : ([d]f32, [d]f32) =
  let trans = rsf_trans w_t b_t y1
  let x2    = map2 (-) y2 trans
  let scale = rsf_scale w_s b_s x2
  let x1    = map2 (/) y1 scale
  in (x1, x2)

entry rsf_backward [d]
                   (w_s: [d][d]f32) (b_s: [d]f32)
                   (w_t: [d][d]f32) (b_t: [d]f32)
                   (y1:  [d]f32)    (y2:  [d]f32)
                   (dy1: [d]f32)    (dy2: [d]f32)
                 : ([d]f32, [d]f32,
                    [d][d]f32, [d]f32,
                    [d][d]f32, [d]f32) =
  let trans   = rsf_trans w_t b_t y1
  let x2_rec  = map2 (-) y2 trans
  let pre_s   = rsf_pre_s w_s b_s x2_rec
  let scale   = map (\v -> f32.exp (clip v)) pre_s
  let x1_rec  = map2 (/) y1 scale
  let dtrans  = dy2
  let dbt     = dtrans
  let dWt     = outer dtrans y1
  let dy1_t   = matvec (transpose w_t) dtrans
  let dy1_tot = map2 (+) dy1 dy1_t
  let draw    = map2 (*) dy1_tot x1_rec
  let dpre    = map3 (\d s c -> if c then 0.0f32 else d * s)
                     draw scale (map is_clipped pre_s)
  let dbs     = dpre
  let dWs     = outer dpre x2_rec
  let dx2     = map2 (+) dy2 (matvec (transpose w_s) dpre)
  let dx1     = map2 (*) dy1_tot scale
  in (dx1, dx2, dWs, dbs, dWt, dbt)

entry rsf_scatter [d]
                  (x1: [d]f32) (x2: [d]f32)
                : ([d]f32, [d]f32) =
  let y1 = map2 (\a b -> (a + b) * fractal_scale) x1 x2
  let y2 = map2 (\a b -> (a - b) * fractal_scale) x1 x2
  in (y1, y2)

entry rsf_scatter_inverse [d]
                          (y1: [d]f32) (y2: [d]f32)
                        : ([d]f32, [d]f32) =
  let x1 = map2 (\a b -> (a + b) * fractal_scale) y1 y2
  let x2 = map2 (\a b -> (a - b) * fractal_scale) y1 y2
  in (x1, x2)

entry oftb_forward [d]
                   (x1: [d]f32) (x2: [d]f32)
                 : ([d]f32, [d]f32) =
  let buf = x1
  let y1  = map2 (\a b -> a + b * fractal_scale) x1 x2
  let y2  = map2 (\a b -> a + b * fractal_scale * 0.5f32) x2 buf
  in (y1, y2)

entry oftb_backward [d]
                    (y1: [d]f32) (y2: [d]f32)
                  : ([d]f32, [d]f32) =
  let buf = y1
  let x2  = map2 (\a b -> a - b * fractal_scale * 0.5f32) y2 buf
  let x1  = map2 (\a b -> a - b * fractal_scale) y1 x2
  in (x1, x2)

entry spectral_clip [n] (xs: [n]f32) : [n]f32 =
  map clip xs

entry dot_product [n] (a: [n]f32) (b: [n]f32) : f32 =
  f32.sum (map2 (\x y ->
                    let p = x * y
                    in if f32.isnan p then 0.0f32 else p) a b)

entry matmul_tiled [m][n][p] (a: [m][n]f32) (b: [n][p]f32) : [m][p]f32 =
  let bt = transpose b
  in map (\row -> map (\col -> f32.sum (map2 (*) row col)) bt) a

entry batched_matmul [batch][m][n][p]
                     (a: [batch][m][n]f32) (b: [batch][n][p]f32)
                   : [batch][m][p]f32 =
  map2 matmul_tiled a b

entry xavier_fill_inplace [m][n]
                          (fan_in: i64) (fan_out: i64)
                          (noise: [m][n]f32) : [m][n]f32 =
  let limit = f32.sqrt (6.0f32 / f32.i64 (fan_in + fan_out))
  in map (map (\u -> (2.0f32 * u - 1.0f32) * limit)) noise

let mse_grad [d] (y: [d]f32) (target: [d]f32) : [d]f32 =
  let inv_n = 2.0f32 / f32.i64 d
  in map2 (\a b -> inv_n * (a - b)) y target

let apply_update_mat [m][n]
                     (lr: f32) (mom: f32)
                     (w: [m][n]f32) (g: [m][n]f32) (v: [m][n]f32)
                   : ([m][n]f32, [m][n]f32) =
  let v' = map2 (\vr gr -> map2 (\a b -> mom * a + b) vr gr) v g
  let w' = map2 (\wr vr -> map2 (\a b -> a - lr * b) wr vr) w v'
  in (w', v')

let apply_update_vec [m]
                     (lr: f32) (mom: f32)
                     (b: [m]f32) (g: [m]f32) (v: [m]f32)
                   : ([m]f32, [m]f32) =
  let v' = map2 (\a gx -> mom * a + gx) v g
  let b' = map2 (\a vx -> a - lr * vx) b v'
  in (b', v')

entry training_step [d]
                    (lr: f32) (momentum: f32)
                    (w_s:  [d][d]f32) (b_s:  [d]f32)
                    (w_t:  [d][d]f32) (b_t:  [d]f32)
                    (vw_s: [d][d]f32) (vb_s: [d]f32)
                    (vw_t: [d][d]f32) (vb_t: [d]f32)
                    (x1:   [d]f32)    (x2:   [d]f32)
                    (t1:   [d]f32)    (t2:   [d]f32)
                  : ([d][d]f32, [d]f32,
                     [d][d]f32, [d]f32,
                     [d][d]f32, [d]f32,
                     [d][d]f32, [d]f32,
                     f32) =
  let (y1, y2) = rsf_forward w_s b_s w_t b_t x1 x2
  let dy1 = mse_grad y1 t1
  let dy2 = mse_grad y2 t2
  let (_, _, dWs, dbs, dWt, dbt) =
        rsf_backward w_s b_s w_t b_t y1 y2 dy1 dy2
  let (w_s', vw_s') = apply_update_mat lr momentum w_s dWs vw_s
  let (b_s', vb_s') = apply_update_vec lr momentum b_s dbs vb_s
  let (w_t', vw_t') = apply_update_mat lr momentum w_t dWt vw_t
  let (b_t', vb_t') = apply_update_vec lr momentum b_t dbt vb_t
  let inv_n = 1.0f32 / f32.i64 d
  let loss  = inv_n *
              (f32.sum (map2 (\a b -> (a - b) * (a - b)) y1 t1) +
               f32.sum (map2 (\a b -> (a - b) * (a - b)) y2 t2))
  in (w_s', b_s', w_t', b_t', vw_s', vb_s', vw_t', vb_t', loss)

entry rsf_chain_forward [layers][d]
                        (w_s: [layers][d][d]f32) (b_s: [layers][d]f32)
                        (w_t: [layers][d][d]f32) (b_t: [layers][d]f32)
                        (x1:  [d]f32)            (x2:  [d]f32)
                      : ([d]f32, [d]f32) =
  loop (a, b) = (x1, x2) for i < layers do
    let (a', b') = rsf_forward w_s[i] b_s[i] w_t[i] b_t[i] a b
    let (a2, b2) = rsf_scatter a' b'
    in (a2, b2)

entry rsf_chain_inverse [layers][d]
                        (w_s: [layers][d][d]f32) (b_s: [layers][d]f32)
                        (w_t: [layers][d][d]f32) (b_t: [layers][d]f32)
                        (y1:  [d]f32)            (y2:  [d]f32)
                      : ([d]f32, [d]f32) =
  loop (a, b) = (y1, y2) for j < layers do
    let i = layers - 1 - j
    let (a1, b1) = rsf_scatter_inverse a b
    let (a2, b2) = rsf_inverse w_s[i] b_s[i] w_t[i] b_t[i] a1 b1
    in (a2, b2)

entry mse_loss [d] (y1: [d]f32) (y2: [d]f32) (t1: [d]f32) (t2: [d]f32) : f32 =
  let inv_n = 1.0f32 / f32.i64 d
  in inv_n *
     (f32.sum (map2 (\a b -> (a - b) * (a - b)) y1 t1) +
      f32.sum (map2 (\a b -> (a - b) * (a - b)) y2 t2))
