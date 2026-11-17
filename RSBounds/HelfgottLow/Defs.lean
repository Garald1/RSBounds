import RSBounds.HelfgottSmall.Defs
import RSBounds.HelfgottLow.Data

/-!
# The small-range walk for [H] (2.16), (2.18) and (2.19)

A walk over `n = 2, 3, …, 2 000 000` that keeps, scaled by `SC = 10¹⁵` (or `SC²`),

* upper bounds `psi` and `s` for `∑_{m ≤ n} Λ(m)` and `∑_{m ≤ n} Λ(m) m`;
* an upper bound `t` for `∑_{m ≤ n} Λ(m) / √m`;
* an upper bound `d` (scale `SC²`) for `∑ (log m)²` over the possible primes `m` in `(⌊n/2⌋, n]`,

and checks at every `n` in range

* `∑_{m ≤ n} Λ(m) m < 1.03884 n² / 2` for `663 ≤ n ≤ 1.6·10⁶` ([H] (2.16));
* `∑_{m ≤ n} Λ(m) / √m < 2.0008 √n` for every `n` ([H] (2.18));
* `∑_{n/2 < p ≤ n} (log p)² ≤ n log n / 2` for `n ≥ 117` ([H] (2.19)).

Possible primes, prime-power events and weights are those of `HelfgottSmall`. The anchors here
also carry a lower bound `lo` for `SC · log a` and an upper bound `r` for `SC / √a`; they are kept
as a list in the state, so that moving to the next anchor costs nothing. The window `(⌊n/2⌋, n]`
is kept by a second, lagging pointer at `n / 2` with its own anchor: a number leaving the window
is removed with a lower bound for its `(log m)²`.

Everything is `Nat` arithmetic written with explicit `Nat` operations, and every value is forced to
a numeral before it is passed on, so that the kernel evaluates the walk quickly.
-/

namespace RSBounds.HelfgottLow

open RSBounds.HelfgottSmall (SC isSurv weight force eventOf)

/-- An anchor `(a, l, lo, r)`. -/
abbrev Anc := Nat × Nat × Nat × Nat

/-- The walk stops after this `n`. -/
def N0 : Nat := 2000000

/-- `⌊SC / √(N0 + 1)⌋`. -/
def RHO0 : Nat := 707106604409

/-- The default anchor. -/
def dflt : Anc := (0, 0, 0, 0)

/-- `lo + ⌊(n - a) SC / n⌋`: a lower bound for `SC · log n` given `lo ≤ SC · log a`, `a ≤ n`. -/
def lowW (n a lo : Nat) : Nat := Nat.add lo (Nat.div (Nat.mul (Nat.sub n a) SC) n)

/-- `⌈inc · r · (a + n) / (2 n SC)⌉`: bounds `SC · Λ(n) / √n` from above. -/
def incR (n a r inc : Nat) : Nat :=
  force (Nat.mul (Nat.mul 2 n) SC) fun den =>
  Nat.div (Nat.add (Nat.mul (Nat.mul inc r) (Nat.add a n)) (Nat.sub den 1)) den

/-- The new `t` after adding `inc` at `n`. -/
def tNext (n a r t inc : Nat) : Nat :=
  match inc with
  | 0 => t
  | _ + 1 => Nat.add t (incR n a r inc)

/-- The (2.16) check at `n`. -/
def check16 (n s : Nat) : Bool :=
  match Nat.ble 663 n && Nat.ble n 1600000 with
  | false => true
  | true => Nat.blt (Nat.mul 200000 s) (Nat.mul (Nat.mul (Nat.mul 103884 n) n) SC)

/-- The (2.18) check at `n`: `(t / SC)² < 2.0008² n`. -/
def check18 (n t : Nat) : Bool :=
  Nat.blt (Nat.mul (Nat.mul 100000000 t) t) (Nat.mul (Nat.mul (Nat.mul 400320064 n) SC) SC)

/-- The (2.19) check at `n`, with the anchor `(a, lo)` of `n`. -/
def check19 (n d a lo : Nat) : Bool :=
  match Nat.ble 117 n with
  | false => true
  | true => Nat.ble (Nat.mul 2 d) (Nat.mul (Nat.mul n (lowW n a lo)) SC)

/-- The walk's state. `n` is the next position; `psi`, `s`, `t`, `d` the scaled sums so far;
`(a, l, lo, r)` the current anchor (number `ia`), `ra` the anchors after it and `b` the next
anchor's `a`; `(aL, loL)` the lagging pointer's anchor (number `ja`), `rl` and `bL` likewise;
`(q, k)` the next prime-power event (number `ie`). -/
structure St where
  n : Nat
  psi : Nat
  s : Nat
  t : Nat
  d : Nat
  ia : Nat
  a : Nat
  l : Nat
  lo : Nat
  r : Nat
  b : Nat
  ra : List Anc
  ja : Nat
  aL : Nat
  loL : Nat
  bL : Nat
  rl : List Anc
  ie : Nat
  q : Nat
  k : Nat

/-- Last part of a step: the checks, then move to `n + 1`. -/
def stepC (n psi s t d ia a l lo r b : Nat) (ra : List Anc) (ja aL loL bL : Nat) (rl : List Anc)
    (ie q k : Nat) : Option St :=
  match check16 n s && check18 n t && check19 n d a lo with
  | false => none
  | true => force (Nat.succ n) fun n' =>
    some ⟨n', psi, s, t, d, ia, a, l, lo, r, b, ra, ja, aL, loL, bL, rl, ie, q, k⟩

/-- The lagging pointer at `m = n / 2`, after its anchor switch: remove `m` from the window. -/
def stepL (n psi s t d ia a l lo r b : Nat) (ra : List Anc) (m ja aL loL bL : Nat)
    (rl : List Anc) (ie q k : Nat) : Option St :=
  match Nat.ble aL m && Nat.ble 2 aL with
  | false => none
  | true =>
    match isSurv m with
    | true =>
      force (lowW m aL loL) fun v =>
      force (Nat.sub d (Nat.mul v v)) fun d' =>
      stepC n psi s t d' ia a l lo r b ra ja aL loL bL rl ie q k
    | false => stepC n psi s t d ia a l lo r b ra ja aL loL bL rl ie q k

/-- Add the increments at `n` (`inc` to `psi`, `add` to `d`), then the lagging pointer. -/
def stepB (n psi s t d ia a l lo r b : Nat) (ra : List Anc) (ja aL loL bL : Nat) (rl : List Anc)
    (ie q k inc add : Nat) : Option St :=
  force (Nat.add psi inc) fun psi' =>
  force (Nat.add s (Nat.mul n inc)) fun s' =>
  force (tNext n a r t inc) fun t' =>
  force (Nat.add d add) fun d' =>
  match Nat.beq (Nat.mod n 2) 0 && Nat.ble 4 n with
  | false => stepC n psi' s' t' d' ia a l lo r b ra ja aL loL bL rl ie q k
  | true =>
    force (Nat.div n 2) fun m =>
    match Nat.beq m bL with
    | true =>
      match rl with
      | [] => none
      | (aL', _, loL', _) :: rl' =>
        force (rl'.headD dflt).1 fun bL' =>
        stepL n psi' s' t' d' ia a l lo r b ra m (Nat.succ ja) aL' loL' bL' rl' ie q k
    | false => stepL n psi' s' t' d' ia a l lo r b ra m ja aL loL bL rl ie q k

/-- A step after the main anchor switch: guards, then the weight only where it is needed. -/
def stepA (n psi s t d ia a l lo r b : Nat) (ra : List Anc) (ja aL loL bL : Nat) (rl : List Anc)
    (ie q k : Nat) : Option St :=
  match Nat.ble a n && Nat.ble 2 a && Nat.ble n N0 with
  | false => none
  | true =>
    match isSurv n with
    | true =>
      force (weight n a l) fun w =>
      match Nat.beq q n with
      | true =>
        force (Nat.add w (Nat.div (Nat.sub (Nat.add w k) 1) k)) fun inc =>
        force (eventOf (Nat.succ ie)).1 fun q' => force (eventOf (Nat.succ ie)).2 fun k' =>
        stepB n psi s t d ia a l lo r b ra ja aL loL bL rl (Nat.succ ie) q' k' inc (Nat.mul w w)
      | false => stepB n psi s t d ia a l lo r b ra ja aL loL bL rl ie q k w (Nat.mul w w)
    | false =>
      match Nat.beq q n with
      | true =>
        force (weight n a l) fun w =>
        force (Nat.div (Nat.sub (Nat.add w k) 1) k) fun inc =>
        force (eventOf (Nat.succ ie)).1 fun q' => force (eventOf (Nat.succ ie)).2 fun k' =>
        stepB n psi s t d ia a l lo r b ra ja aL loL bL rl (Nat.succ ie) q' k' inc 0
      | false => stepB n psi s t d ia a l lo r b ra ja aL loL bL rl ie q k 0 0

/-- One step of the walk. -/
def step : St → Option St
  | ⟨n, psi, s, t, d, ia, a, l, lo, r, b, ra, ja, aL, loL, bL, rl, ie, q, k⟩ =>
    match Nat.beq n b with
    | true =>
      match ra with
      | [] => none
      | (a', l', lo', r') :: ra' =>
        force (ra'.headD dflt).1 fun b' =>
        stepA n psi s t d (Nat.succ ia) a' l' lo' r' b' ra' ja aL loL bL rl ie q k
    | false => stepA n psi s t d ia a l lo r b ra ja aL loL bL rl ie q k

/-- `fuel` steps of the walk. -/
def walk (fuel : Nat) : St → Option St :=
  Nat.rec (motive := fun _ => St → Option St) some
    (fun _ ih st =>
      match step st with
      | none => none
      | some st' => ih st')
    fuel

/-! ## Chunk boundaries -/

/-- What a chunk boundary records: `(n, psi, s, t, d, ia, ja, ie)`. -/
abbrev Ext := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

/-- The full state at a boundary: anchors and events are looked up by their numbers. -/
def attach : Ext → St
  | (n, psi, s, t, d, ia, ja, ie) =>
    let A := anchorsAll.getD ia dflt
    let ra := anchorsAll.drop (ia + 1)
    let L := anchorsAll.getD ja dflt
    let rl := anchorsAll.drop (ja + 1)
    ⟨n, psi, s, t, d, ia, A.1, A.2.1, A.2.2.1, A.2.2.2, (ra.headD dflt).1, ra,
      ja, L.1, L.2.2.1, (rl.headD dflt).1, rl, ie, (eventOf ie).1, (eventOf ie).2⟩

/-- Equality of anchor lists. -/
def ancListEq : List Anc → List Anc → Bool
  | [], [] => true
  | (a, l, lo, r) :: L, (a', l', lo', r') :: L' =>
    Nat.beq a a' && Nat.beq l l' && Nat.beq lo lo' && Nat.beq r r' && ancListEq L L'
  | _, _ => false

/-- Equality of states. -/
def stEq (x y : St) : Bool :=
  Nat.beq x.n y.n && Nat.beq x.psi y.psi && Nat.beq x.s y.s && Nat.beq x.t y.t &&
    Nat.beq x.d y.d && Nat.beq x.ia y.ia && Nat.beq x.a y.a && Nat.beq x.l y.l &&
    Nat.beq x.lo y.lo && Nat.beq x.r y.r && Nat.beq x.b y.b && ancListEq x.ra y.ra &&
    Nat.beq x.ja y.ja && Nat.beq x.aL y.aL && Nat.beq x.loL y.loL && Nat.beq x.bL y.bL &&
    ancListEq x.rl y.rl && Nat.beq x.ie y.ie && Nat.beq x.q y.q && Nat.beq x.k y.k

/-- `fuel` steps from `attach e` succeed and end at `attach e'`. -/
def chunkOK (fuel : Nat) (e e' : Ext) : Bool :=
  match walk fuel (attach e) with
  | some r => stEq r (attach e')
  | none => false

/-- The closing check at the end of the walk (`n = N0 + 1`), for the summation by parts above
`N0`: `(SC t - RHO0 psi) / SC² < 1.0004 √N0`. -/
def finalB (psi t : Nat) : Bool :=
  Nat.blt (Nat.mul 100000000 (Nat.sub (Nat.mul SC t) (Nat.mul RHO0 psi) ^ 2))
    (Nat.mul (Nat.mul 100080016 N0) (SC ^ 4))

/-! ## Properties of the data, checked by the kernel in `DataChecks.lean` -/

/-- `exp (V / SC) ≤ b / a`, through `exp x ≤ ∑_{i ≤ 8} x^i / i! + 10 x⁹ / (9 · 9!)` for
`0 ≤ x ≤ 1`; this gives `log a + V / SC ≤ log b`. -/
def expCheckLo (a b V : Nat) : Bool :=
  Nat.ble V SC &&
    Nat.ble (a * (81 * SC * RSBounds.HelfgottSmall.expPoly V + 10 * V ^ 9))
      (b * (81 * 40320 * SC ^ 9))

/-- Consecutive anchors. -/
def pairOK : Anc → Anc → Bool
  | (a, l, lo, _), (b, l', lo', _) =>
    Nat.blt a b && Nat.ble l l' && RSBounds.HelfgottSmall.expCheck a b (l' - l) &&
      Nat.ble lo lo' && expCheckLo a b (lo' - lo)

/-- All consecutive anchors are related by `pairOK`. -/
def chainOK : List Anc → Bool
  | x :: y :: rest => pairOK x y && chainOK (y :: rest)
  | _ => true

/-- Every anchor's `r` bounds `SC / √a`: `SC² ≤ r² a`. -/
def rOK (L : List Anc) : Bool :=
  L.all fun x => Nat.ble (SC * SC) (x.2.2.2 * x.2.2.2 * x.1)

end RSBounds.HelfgottLow
