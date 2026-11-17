import TernaryGoldbach.MinorArcs.Eta2DDTaylor

/-!
# (B.6) with `31.521`: the exact rational checks

Kernel-evaluable functions for the two bisections; their soundness is proved in
`RSBounds.HelfgottB6.Sound`.
-/

namespace RSBounds.HelfgottB6

open TernaryGoldbach.MinorArcs

/-- `iⁿ` as a pair of rationals. -/
def ipowQ : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => cmul (ipowQ n) (0, 1)

/-- The coefficient of `wⁿ` in `Φ`: `b` for `n = 0`, `4 n! r(n) iⁿ` for `n ≥ 1`. -/
def cQ (b : ℚ) (r : ℕ → ℚ) : ℕ → ℚ × ℚ
  | 0 => (b, 0)
  | n + 1 => smulQ (4 * ((n + 1).factorial : ℚ) * r (n + 1)) (ipowQ (n + 1))

/-- The weights of `z²`, `z`, `z⁴`. -/
def r2 (n : ℕ) : ℚ := 2 ^ (n + 2)
def r1 (n : ℕ) : ℚ := -(4 ^ (n + 1))
def r4 (_ : ℕ) : ℚ := -1

/-- `∑_{n<m} f(i + n) wⁿ`, by Horner's rule. -/
def hornQ (f : ℕ → ℚ × ℚ) (w : ℚ) : ℕ → ℕ → ℚ × ℚ
  | 0, _ => (0, 0)
  | m + 1, i => cadd (f i) (smulQ w (hornQ f w m (i + 1)))

/-- The coefficients of the derivative: `(n + 1) f(n + 1)`. -/
def dQ (f : ℕ → ℚ × ℚ) (n : ℕ) : ℚ × ℚ := smulQ ((n : ℚ) + 1) (f (n + 1))

/-- `|Re| + |Im|`. -/
def ab1 (p : ℚ × ℚ) : ℚ := |p.1| + |p.2|

/-- `∑_{n<L} (|Re fₙ| + |Im fₙ|) · n(n − 1)/2 · W^{n−2}`. -/
def c2Q (f : ℕ → ℚ × ℚ) (W : ℚ) : ℕ → ℚ
  | 0 => 0
  | L + 1 => c2Q f W L + ab1 (f L) * ((L : ℚ) * ((L : ℚ) - 1) / 2) * W ^ (L - 2)

/-- The number of integrations by parts. -/
def KB : ℕ := 10

/-- The bound. -/
def BB : ℚ := 31521 / 1000

/-- `4 K! (4^{K+1} − 1) wᴷ`. -/
def RKQ (w : ℚ) : ℚ := 4 * (KB.factorial : ℚ) * (4 ^ (KB + 1) - 1) * w ^ KB

def f1 : ℕ → ℚ × ℚ := cQ (-16) r1
def f2 : ℕ → ℚ × ℚ := cQ 16 r2
def f4 : ℕ → ℚ × ℚ := cQ (-4) r4

/-- The point `s · zm(m)` of the unit circle. -/
def zQ (s m : ℚ) : ℚ × ℚ := (s * (1 - m ^ 2) / (1 + m ^ 2), s * (2 * m) / (1 + m ^ 2))

/-- `Re(conj A · B)`. -/
def dotQ (A B : ℚ × ℚ) : ℚ := A.1 * B.1 + A.2 * B.2

/-- `|A|²`. -/
def nsqQ (A : ℚ × ℚ) : ℚ := A.1 ^ 2 + A.2 ^ 2

/-- `c₁ a₁ z + c₂ a₂ z² + c₄ a₄ z⁴`. -/
def sq3 (z a1 a2 a4 : ℚ × ℚ) (c1 c2 c4 : ℚ) : ℚ × ℚ :=
  cadd (cadd (smulQ c1 (cmul a1 z)) (smulQ c2 (cmul a2 (cmul z z))))
    (smulQ c4 (cmul a4 (cmul (cmul z z) (cmul z z))))

/-- The second-order error of a cell of half-widths `hθ/2` (in `m`) and `h_w` (in `w`), with
centre values `aₖ = Φₖ(w_c)` and derivatives `bₖ = Φₖ'(w_c)`, `w ≤ W`. -/
def eB (ht hw W : ℚ) (a1 a2 a4 b1 b2 b4 : ℚ × ℚ) : ℚ :=
  ab1 a1 * ht ^ 2 + ab1 a2 * (2 * ht) ^ 2 + ab1 a4 * (4 * ht) ^ 2 +
    hw * (ab1 b1 * ht + ab1 b2 * (2 * ht) + ab1 b4 * (4 * ht)) +
    (c2Q f1 W (KB + 1) + c2Q f2 W (KB + 1) + c2Q f4 W (KB + 1)) * hw ^ 2

/-- An upper bound for `|F₀ + iδF_θ + d F_w|²` for `|δ| ≤ hθ`, `|d| ≤ h_w`. -/
def qB (ht hw : ℚ) (F0 Ft Fw : ℚ × ℚ) : ℚ :=
  nsqQ F0 + 2 * ht * |dotQ F0 (-Ft.2, Ft.1)| + 2 * hw * |dotQ F0 Fw| +
    2 * ht ^ 2 * nsqQ Ft + 2 * hw ^ 2 * nsqQ Fw

/-- The test of a cell, given the centre `z₁` and the centre values. -/
def cellB' (ht hw W : ℚ) (z1 a1 a2 a4 b1 b2 b4 : ℚ × ℚ) : Bool :=
  let E := eB ht hw W a1 a2 a4 b1 b2 b4
  let M := BB - RKQ W - E
  decide (4 * ht ≤ 1) && decide (0 ≤ M) &&
    decide (qB ht hw (sq3 z1 a1 a2 a4 1 1 1) (sq3 z1 a1 a2 a4 1 2 4) (sq3 z1 b1 b2 b4 1 1 1) ≤
      M ^ 2)

def cellB (s m0 m1 w0 w1 : ℚ) : Bool :=
  let wc := (w0 + w1) / 2
  cellB' (m1 - m0) ((w1 - w0) / 2) w1 (zQ s ((m0 + m1) / 2))
    (hornQ f1 wc (KB + 1) 0) (hornQ f2 wc (KB + 1) 0) (hornQ f4 wc (KB + 1) 0)
    (hornQ (dQ f1) wc KB 0) (hornQ (dQ f2) wc KB 0) (hornQ (dQ f4) wc KB 0)

/-- Recursive bisection of `[m₀, m₁] × [w₀, w₁]`. -/
def chkB : ℕ → ℚ → ℚ → ℚ → ℚ → ℚ → Bool
  | 0, s, m0, m1, w0, w1 => cellB s m0 m1 w0 w1
  | n + 1, s, m0, m1, w0, w1 =>
    cellB s m0 m1 w0 w1 ||
      (if w1 - w0 ≤ m1 - m0 then
        chkB n s m0 ((m0 + m1) / 2) w0 w1 && chkB n s ((m0 + m1) / 2) m1 w0 w1
      else chkB n s m0 m1 w0 ((w0 + w1) / 2) && chkB n s m0 m1 ((w0 + w1) / 2) w1)

/-- The `i`-th of the chunks `[a + iδ, a + (i+1)δ] × [0, W]` (each checked in its own declaration,
to bound the kernel's memory). -/
def chunkB (s a δ W : ℚ) (i : ℕ) : Bool := chkB 40 s (a + i * δ) (a + (i + 1) * δ) 0 W

/-! ## Region A: Taylor polynomials in `x = 2πt ∈ [0, 28]` -/

def NA : ℕ := 90
def XA : ℚ := 28

/-- `120 Xᴺ/N!`. -/
def errA : ℚ := 120 * XA ^ NA / NA.factorial

def cellA (x0 x1 : ℚ) : Bool :=
  let F := PQ NA ((x0 + x1) / 2)
  let M := BB - 12 * (x1 - x0) - errA
  decide (0 ≤ M) && decide (F.1 ^ 2 + F.2 ^ 2 ≤ M ^ 2)

def chkA : ℕ → ℚ → ℚ → Bool
  | 0, x0, x1 => cellA x0 x1
  | n + 1, x0, x1 => cellA x0 x1 || (chkA n x0 ((x0 + x1) / 2) && chkA n ((x0 + x1) / 2) x1)

/-- The `i`-th of the chunks `[a + iδ, a + (i+1)δ]` of region A. -/
def chunkA (a δ : ℚ) (i : ℕ) : Bool := chkA 20 (a + i * δ) (a + (i + 1) * δ)

end RSBounds.HelfgottB6
