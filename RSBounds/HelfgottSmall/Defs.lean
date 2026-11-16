import RSBounds.HelfgottSmall.Data

/-!
# The small-range walk for [H] (2.14) and (2.17)

A walk over `n = 2, 3, …, 25 000 000` that keeps upper bounds, scaled by `SC = 10¹⁵`, for
`∑_{m ≤ n} Λ(m)` and `∑_{m ≤ n} Λ(m) m`, and checks at every `n` in range

* `ψ(n) ≤ 1.0004 n` for `2·10⁶ ≤ n ≤ 4·10⁶` ([H] (2.14));
* `∑_{m ≤ n} Λ(m) m < 1.0008 n² / 2` for `1.6·10⁶ ≤ n ≤ 2.5·10⁷` ([H] (2.17)).

Only upper bounds are needed, so nothing is proved prime. A number counts as a possible prime when
it passes trial division (`n ≤ 5000`) or is coprime to `bigP` (`n > 5000`); every prime does.
Prime powers `p ^ k` with `k ≥ 2` come from the list `eventsAll`. The weight of `n` is
`l + ⌈(n - a) SC / a⌉`, an upper bound for `SC · log n` given an anchor `(a, l)` with
`a ≤ n` and `log a ≤ l / SC`.

Everything here is `Nat` arithmetic written with explicit `Nat` operations, and every value is
forced to a numeral before it is passed on, so that the kernel evaluates the walk quickly.
-/

namespace RSBounds.HelfgottSmall

/-- Fixed-point scale. -/
def SC : Nat := 1000000000000000

/-- The walk stops at this `n`. -/
def NMAX : Nat := 25000000

/-- `trialAux n fuel d`: no `d' ≥ d` with `d' * d' ≤ n` divides `n` (trying at most `fuel`). -/
def trialAux (n : Nat) (fuel : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih d =>
      match Nat.blt n (Nat.mul d d) with
      | true => true
      | false =>
        match Nat.beq (Nat.mod n d) 0 with
        | true => false
        | false => ih (Nat.succ d))
    fuel

/-- Trial division by every `d ≥ 2` with `d * d ≤ n`. -/
def trialSurvives (n : Nat) : Bool := trialAux n n 2

/-- The numbers `2 ≤ m ≤ 5000` that pass trial division: the primes up to 5000. -/
def smallD : List Nat :=
  (List.range 5001).filter (fun m => Nat.ble 2 m && trialSurvives m)

/-- `n` may be prime. -/
def isSurv (n : Nat) : Bool :=
  match Nat.ble n 5000 with
  | true => trialSurvives n
  | false => Nat.beq (Nat.gcd n bigP) 1

/-- The `i`-th anchor, or `(0, 0)`. -/
def anchorOf (i : Nat) : Nat × Nat := anchorsAll.getD i (0, 0)

/-- The `i`-th event, or `(0, 0)`. -/
def eventOf (i : Nat) : Nat × Nat := eventsAll.getD i (0, 0)

/-- Pass `x` on as a numeral. -/
def force {α : Sort _} (x : Nat) (k : Nat → α) : α :=
  match x with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem force_eq {α : Sort _} (x : Nat) (k : Nat → α) : force x k = k x := by
  cases x <;> rfl

/-- The (2.14) check at `n`. -/
def check14 (n psi : Nat) : Bool :=
  match Nat.ble 2000000 n && Nat.ble n 4000000 with
  | false => true
  | true => Nat.ble (Nat.mul 10000 psi) (Nat.mul (Nat.mul 10004 n) SC)

/-- The (2.17) check at `n`. -/
def check17 (n s : Nat) : Bool :=
  match Nat.ble 1600000 n && Nat.ble n 25000000 with
  | false => true
  | true => Nat.blt (Nat.mul 20000 s) (Nat.mul (Nat.mul (Nat.mul 10008 n) n) SC)

/-- The walk's state: `(n, psi, s, ia, a, l, b, ie, q, k)`. `n` is the next position, `psi` and
`s` the scaled sums so far, `(a, l)` the current anchor (number `ia`), `b` the next anchor's
`a`, and `(q, k)` the next event (number `ie`). -/
abbrev St := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

/-- The weight `l + ⌈(n - a) SC / a⌉`. -/
def weight (n a l : Nat) : Nat :=
  Nat.add l (Nat.div (Nat.add (Nat.mul (Nat.sub n a) SC) (Nat.sub a 1)) a)

/-- Add the increment `inc` at `n`, check, and move to `n + 1`. -/
def stepB (n psi s ia a l b ie q k inc : Nat) : Option St :=
  force (Nat.add psi inc) fun psi' =>
  force (Nat.add s (Nat.mul n inc)) fun s' =>
  match check14 n psi' && check17 n s' with
  | false => none
  | true => force (Nat.succ n) fun n' => some (n', psi', s', ia, a, l, b, ie, q, k)

/-- A step after the anchor switch: guards, then the weight only where it is needed. -/
def stepA (n psi s ia a l b ie q k : Nat) : Option St :=
  match Nat.ble a n && Nat.ble 2 a && Nat.ble n NMAX with
  | false => none
  | true =>
    match Nat.beq q n with
    | true =>
      force (weight n a l) fun w =>
      force (Nat.add (match isSurv n with | true => w | false => 0)
        (Nat.div (Nat.sub (Nat.add w k) 1) k)) fun inc =>
      force (eventOf (Nat.succ ie)).1 fun q' => force (eventOf (Nat.succ ie)).2 fun k' =>
      stepB n psi s ia a l b (Nat.succ ie) q' k' inc
    | false =>
      match isSurv n with
      | true => force (weight n a l) fun w => stepB n psi s ia a l b ie q k w
      | false => stepB n psi s ia a l b ie q k 0

/-- One step of the walk. -/
def step : St → Option St
  | (n, psi, s, ia, a, l, b, ie, q, k) =>
    match Nat.beq n b with
    | true =>
      force (anchorOf (Nat.succ ia)).2 fun l' =>
      force (anchorOf (Nat.succ (Nat.succ ia))).1 fun b' =>
      stepA n psi s (Nat.succ ia) b l' b' ie q k
    | false => stepA n psi s ia a l b ie q k

/-- `fuel` steps of the walk. -/
def walk (fuel : Nat) : St → Option St :=
  Nat.rec (motive := fun _ => St → Option St) some
    (fun _ ih st =>
      match step st with
      | none => none
      | some st' => ih st')
    fuel

/-- Componentwise equality of states. -/
def stEq : St → St → Bool
  | (n, psi, s, ia, a, l, b, ie, q, k), (n', psi', s', ia', a', l', b', ie', q', k') =>
    Nat.beq n n' && Nat.beq psi psi' && Nat.beq s s' && Nat.beq ia ia' && Nat.beq a a' &&
      Nat.beq l l' && Nat.beq b b' && Nat.beq ie ie' && Nat.beq q q' && Nat.beq k k'

/-- `fuel` steps from `st` succeed and end at `st'`. -/
def chunkOK (fuel : Nat) (st st' : St) : Bool :=
  match walk fuel st with
  | some r => stEq r st'
  | none => false

/-! ## Properties of the data, checked by the kernel in `Sound.lean` -/

/-- `8! · ∑_{i ≤ 8} (U / SC)^i / i!`, times `SC ^ 8`. -/
def expPoly (U : Nat) : Nat :=
  40320 * SC ^ 8 + 40320 * U * SC ^ 7 + 20160 * U ^ 2 * SC ^ 6 + 6720 * U ^ 3 * SC ^ 5 +
    1680 * U ^ 4 * SC ^ 4 + 336 * U ^ 5 * SC ^ 3 + 56 * U ^ 6 * SC ^ 2 + 8 * U ^ 7 * SC + U ^ 8

/-- `b / a ≤ ∑_{i ≤ 8} (U / SC)^i / i!`, which gives `log b ≤ log a + U / SC`. -/
def expCheck (a b U : Nat) : Bool := Nat.ble (b * (40320 * SC ^ 8)) (a * expPoly U)

/-- Consecutive anchors. -/
def pairOK : Nat × Nat → Nat × Nat → Bool
  | (a, l), (b, l') => Nat.blt a b && Nat.ble l l' && expCheck a b (l' - l)

/-- All consecutive anchors are related by `pairOK`. -/
def chainOK : List (Nat × Nat) → Bool
  | x :: y :: rest => pairOK x y && chainOK (y :: rest)
  | _ => true

/-- Strictly increasing first components. -/
def sortedStrict : List (Nat × Nat) → Bool
  | x :: y :: rest => Nat.blt x.1 y.1 && sortedStrict (y :: rest)
  | _ => true

/-- Every `m ^ k` with `m ∈ smallD`, `2 ≤ k < 25` and `m ^ k ≤ NMAX` is an event `(m ^ k, k)`. -/
def eventsComplete : Bool :=
  smallD.all fun m => (List.range 25).all fun k =>
    !(Nat.ble 2 k && Nat.ble (m ^ k) NMAX) || eventsAll.contains (m ^ k, k)

end RSBounds.HelfgottSmall
