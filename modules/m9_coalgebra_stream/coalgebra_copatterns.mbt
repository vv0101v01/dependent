///|
/// Module M9 (Part 1) — Terminal Stream Coalgebras (`νX. A × X`), Anamorphisms,
/// Lambek Even/Odd Zipping Isomorphism, and Cauchy Differential Stream Semiring.

///|
pub(all) suberror CoalgebraError {
  NegativeStreamHorizon(Int32)
  UncoveredCopatternPath(String)
  RedundantCopatternClause(Int32)
  UnguardedCorecursiveCall(Int32)
  InvalidAutomatonState(Int32)
}

///|
/// Explicit State-Space F-Coalgebra `(S, γ : S -> A × S)` for the stream functor `F(X) = A × X`.
pub(all) struct StreamCoalg[S, A] {
  seed : S
  step : (S) -> (A, S)
}

///|
/// Terminal Stream Coalgebra `InfStream[A]` defined by Copattern Observations `(hd, tl)`.
pub struct InfStream[A] {
  unfold_once : () -> (A, InfStream[A])
}

///|
/// Copattern Observation 1: `hd : InfStream[A] -> A`.
pub fn[A] stream_hd(s : InfStream[A]) -> A {
  let (h, _) = (s.unfold_once)()
  h
}

///|
/// Copattern Observation 2: `tl : InfStream[A] -> InfStream[A]`.
pub fn[A] stream_tl(s : InfStream[A]) -> InfStream[A] {
  let (_, t) = (s.unfold_once)()
  t
}

///|
/// Terminal Coalgebra Universal Morphism (Anamorphism) `ana_stream : StreamCoalg[S, A] -> InfStream[A]`:
/// Unique coalgebra homomorphism satisfying `hd(ana(s)) == (step(s)).0` and `tl(ana(s)) == ana((step(s)).1)`.
pub fn[S, A] ana_stream(coalg : StreamCoalg[S, A]) -> InfStream[A] {
  fn build(st : S) -> InfStream[A] {
    {
      unfold_once: fn() {
        let (head_val, next_st) = (coalg.step)(st)
        (head_val, build(next_st))
      },
    }
  }

  build(coalg.seed)
}

///|
/// Iterative O(n) Stack-Safe Prefix Observation `stream_take(n, s)`.
pub fn[A] stream_take(
  n : Int32,
  s : InfStream[A],
) -> Array[A] raise CoalgebraError {
  if n < 0 {
    raise CoalgebraError::NegativeStreamHorizon(n)
  }
  let out : Array[A] = []
  let mut cur = s
  for i = 0; i < n; i = i + 1 {
    let (h, next_s) = (cur.unfold_once)()
    out.push(h)
    cur = next_s
  }
  out
}

///|
/// Iterative O(n) Stack-Safe Index Projection `stream_nth(n, s)`.
pub fn[A] stream_nth(n : Int32, s : InfStream[A]) -> A raise CoalgebraError {
  if n < 0 {
    raise CoalgebraError::NegativeStreamHorizon(n)
  }
  let mut cur = s
  for i = 0; i < n; i = i + 1 {
    let (_, next_s) = (cur.unfold_once)()
    cur = next_s
  }
  stream_hd(cur)
}

///|
pub fn[A, B] stream_map(f : (A) -> B, s : InfStream[A]) -> InfStream[B] {
  ana_stream({
    seed: s,
    step: fn(cur) {
      let (h, t) = (cur.unfold_once)()
      (f(h), t)
    },
  })
}

///|
pub fn[A, B, C] stream_zip_with(
  f : (A, B) -> C,
  s1 : InfStream[A],
  s2 : InfStream[B],
) -> InfStream[C] {
  ana_stream({
    seed: (s1, s2),
    step: fn(pair) {
      let (a, b) = pair
      let (ha, ta) = (a.unfold_once)()
      let (hb, tb) = (b.unfold_once)()
      (f(ha, hb), (ta, tb))
    },
  })
}

///|
/// Lambek / Bisimulation Isomorphism `InfStream[A] ≃ InfStream[A] × InfStream[A]`:
/// Splits `s` into `(evens(s), odds(s))` and merges back via `stream_interleave`!
pub fn[A] stream_evens_odds(s : InfStream[A]) -> (InfStream[A], InfStream[A]) {
  let evens = ana_stream({
    seed: s,
    step: fn(cur) {
      let (h0, t0) = (cur.unfold_once)()
      let (_, t1) = (t0.unfold_once)()
      (h0, t1)
    },
  })
  let odds = ana_stream({
    seed: stream_tl(s),
    step: fn(cur) {
      let (h1, t1) = (cur.unfold_once)()
      let (_, t2) = (t1.unfold_once)()
      (h1, t2)
    },
  })
  (evens, odds)
}

///|
pub fn[A] stream_interleave(
  evens : InfStream[A],
  odds : InfStream[A],
) -> InfStream[A] {
  ana_stream({
    seed: (true, evens, odds),
    step: fn(state) {
      let (take_left, l, r) = state
      if take_left {
        let (hl, tl_l) = (l.unfold_once)()
        (hl, (false, tl_l, r))
      } else {
        let (hr, tl_r) = (r.unfold_once)()
        (hr, (true, l, tl_r))
      }
    },
  })
}

///|
/// Canonical Coalgebraic Fibonacci Stream `0, 1, 1, 2, 3, 5, 8, 13, ...`.
pub fn fibonacci_stream() -> InfStream[Int32] {
  ana_stream({ seed: (0, 1), step: fn(ab) { (ab.0, (ab.1, ab.0 + ab.1)) }, })
}

///|
/// Hadamard Pointwise Stream Addition `(f + g)_n = f_n + g_n`.
pub fn stream_add_int(
  s1 : InfStream[Int32],
  s2 : InfStream[Int32],
) -> InfStream[Int32] {
  stream_zip_with(fn(a, b) { a + b }, s1, s2)
}

///|
/// Coinductive Cauchy Convolution Product `(f * g)_n = ∑_{k=0}^n f_k * g_{n-k}`:
/// Satisfies Rutten's Stream Calculus Differential Equation:
/// `hd(f * g) = hd(f) * hd(g)` and `tl(f * g) = scale(hd(f), tl(g)) + (tl(f) * g)`!
pub fn stream_cauchy_mul(
  s1 : InfStream[Int32],
  s2 : InfStream[Int32],
) -> InfStream[Int32] {
  // Represent using prefix history `(idx, hist1, hist2, cur1, cur2)` so it executes in polynomial O(n^2) total steps without exponential tree blowup!
  let h1 : Array[Int32] = []
  let h2 : Array[Int32] = []
  ana_stream({
    seed: (0, s1, s2),
    step: fn(st) {
      let (n, c1, c2) = st
      let (v1, n1) = (c1.unfold_once)()
      let (v2, n2) = (c2.unfold_once)()
      if h1.length() <= n {
        h1.push(v1)
        h2.push(v2)
      }
      let mut conv = 0
      for k = 0; k <= n; k = k + 1 {
        conv = conv + h1[k] * h2[n - k]
      }
      (conv, (n + 1, n1, n2))
    },
  })
}

///|
/// Formal Stream Derivative `(D s)_n = (n + 1) * s_{n+1}`:
/// Satisfies Leibniz Derivation Law `D(f * g) == (D f) * g + f * (D g)`!
pub fn stream_derivative(s : InfStream[Int32]) -> InfStream[Int32] {
  ana_stream({
    seed: (1, stream_tl(s)),
    step: fn(st) {
      let (coeff, cur) = st
      let (h, next_cur) = (cur.unfold_once)()
      (coeff * h, (coeff + 1, next_cur))
    },
  })
}
