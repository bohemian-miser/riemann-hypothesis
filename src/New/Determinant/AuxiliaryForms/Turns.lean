module

import Mathlib.Data.Rat.Cast.OfScientific
import Std.Tactic.BVDecide.Normalize.BitVec
public import New.Determinant.AuxiliaryForms.PathData
public import New.Determinant.Chain.Moduli
import Lib.General.Algebra.MultivariatePolynomials
import New.Determinant.Exchange.OneSquare

/-!
# Turning path data, and turns off the diagonal

A turn of a path replaces two sides of a square by the two other sides, whether off the diagonal or
on it. The `m`-fold twist is `ϑ`, the characters of the edges are built from
`D.untwistedLiftChar j`, of weight `-D.liftWeight j`, and the vertical edges, whose character
carries a power of `ϑ`, go from `Y^i_j` to `Y^i_(j+1)` and from `Ỹ^i_j` to `Ỹ^i_(j+1)`. The forms
that move in the grid of the `Y` are conjugate forms.

Rather than maintaining recursive pointwise path-datum tables and a separate diagonal-turn module,
we represent a path datum as a linear functional `Λ : GridDatum ϑ` and turn corners by a single
monadic transition `IsPathDatum.exists_square_move` built from `GridDatum.bind` and the partner
graph kernel `graphKernel`. Climbing from stage `j` to stage `j + 1` pushes the descent in each
grid past `j` lifts (`descent_past_gridPathMap`) and then crosses the diagonal square `(j, j)` via
two seesaws and line reversal (`hasRoute_succ`), yielding the full route from stage `0` to stage
`m` (`exists_hasRoute_zero_last`).

## Main definitions and results

* `New.Data.graphKernel`, `New.Data.exists_partner_kernel`: the graph kernel on matched matrix
  blocks over a finite valuation-pair ring, its equivariance, and its root-of-unity representative.
* `New.Data.IsPathDatum.exists_square_move`: turning a monadic path datum across any square (with
  or without a Fourier transform in the added line) increases the order by `2` and transfers sums
  through a `SquareLaw`.
* `New.Data.exists_squareLaw_grid_hasAbsUpToNormPower`: the exchange
  `New.Exchange.one_square_identity_of_isEdgeFamily` on a square of a grid, with a constant
  `κ / c ϑ` whose denominator has, up to a power of the norm, the absolute value
  `New.Data.turnRatio`.
* `New.Data.HasRoute`: path data pass forwards from stage `i` to stage `j` with order increased by
  `k`, and proportionality of periods passes backwards with denominator `c`.
* `New.Data.descent_past_gridPathMap`: pushing a descent past `a` lifts on row `b` via interior
  square moves.
* `New.Data.hasRoute_succ`, `New.Data.exists_hasRoute_zero_last`: crossing stage `j → j + 1` via
  two seesaws and line reversal, and composing all `m` stages from the first path to the last.

Notions from other files:
* `New.Data.GridNode`: a triple `(z, a, b)`, the node `Y^a_b` if `z = false` and `Ỹ^b_a` if
  `z = true`. Its index set is `D.NodeIndex`, which is `D.GridIndex z a b`.
* `New.Data.EdgeTuple`, `New.Data.GridDatum`, `New.Data.GridDatum.bind`: tuples of matrices modulo
  `gridModulus ϑ`, linear functionals on functions of tuples, and their monadic composition.
* `New.Data.IsPathDatum n w Λ`: a linear functional `Λ : GridDatum ϑ` scaled by `edgeCharProd g w`
  under admissible families `g` and given by a short root-of-unity sum (`IsShortSum n w Λ`) on
  tuples whose vertical edges in `w` carry left-invertible matrices.
* `New.AreMatched`, `New.Exchange.SquareLaw`: matched functions over a finite ring and the square
  law `∑ Ψ L' = C ∑ Φ L`.
-/

@[expose] public section

noncomputable section

namespace New.Data

/-!
## Turning a path datum

A turn of a path replaces the edges `p → v`, `Q → U` of a square by `v → r`, `U → R`, where
`Q = p` and `R = r` unless the turn is on the diagonal, at which a line indexed by `T = Unit` is
added to both.

The form that crosses the square goes from `v` to `U`. For a turn at `(a, b)` in grid `z` off the
diagonal, `v = (z, a, b + 1)` and `U = (z, a + 1, b)`; on the diagonal at `(j, j)`, `v = Y^j_(j+1)`
and `U = Ỹ^(j+1)_j ≅ Y^(j+1)_j`, and the line sits on the edges `Q → U` and `U → R`. Using the
partner graph kernel `graphKernel` inside `GridDatum.bind`, both interior and diagonal turns are
handled by the single lemma `IsPathDatum.exists_square_move`.
-/

section PartnerKernel

open Matrix Fintype Finset Function Exchange MulChar

variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
  {a b N n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype N] [DecidableEq N] [Fintype n] [DecidableEq n]

/-- The partner graph kernel `δ(x, y)` over a finite ring `R` for `χ` and `e : b ⊕ a ≃ n`: it takes
the value `χ (det k) / #GL_b(R)` at `(invLastRows e k, firstCols e k)` for `k ∈ GL_n(R)`, and `0`
elsewhere. -/
def graphKernel (χ : MulChar R ℂ) (e : b ⊕ a ≃ n) (x : Matrix a n R) (y : Matrix n b R) : ℂ :=
  Function.extend (fun k : GL n R ↦ (invLastRows e k, firstCols e k))
    (fun k : GL n R ↦ χ k.val.det / card (GL b R)) 0 (x, y)

omit [DecidableEq a] in
lemma graphKernel_invLastRows_firstCols (χ : MulChar R ℂ) (e : b ⊕ a ≃ n) (k : GL n R) :
    graphKernel χ e (invLastRows e k) (firstCols e k) = χ k.val.det / card (GL b R) := by
  refine FactorsThrough.extend_apply (fun k₁ k₂ h_eq ↦ ?_) _ k
  obtain ⟨h_rows, h_cols⟩ := Prod.mk.inj h_eq
  obtain ⟨h, h_mul, h_det⟩ := exists_firstCols_eq_mul_of_invLastRows_eq h_rows
  have hh : h.val = 1 := by
    have := congrArg (invFirstRows e k₁ * ·) (h_cols.trans h_mul)
    simpa [← Matrix.mul_assoc, invFirstRows_mul_firstCols] using this.symm
  rw [h_det, hh, det_one, mul_one]

omit [Fintype a] [DecidableEq a] in
lemma exists_eq_of_graphKernel_ne_zero {χ : MulChar R ℂ} {e : b ⊕ a ≃ n}
    {x : Matrix a n R} {y : Matrix n b R} (h_ne : graphKernel χ e x y ≠ 0) :
    ∃ k : GL n R, invLastRows e k = x ∧ firstCols e k = y := by
  by_contra h_none
  exact h_ne (Function.extend_apply' _ _ (x, y) fun ⟨k, hk⟩ ↦ h_none ⟨k, Prod.mk.inj hk⟩)

/-- Equivariance of `graphKernel`: multiplying `x` on the left by `f⁻¹` and right by `g`, and `y`
on the left by `g⁻¹` and right by `q`, multiplies `graphKernel χ e x y` by
`(χ (det g) / χ (det f) / χ (det q))⁻¹`. -/
lemma graphKernel_equivariant (χ : MulChar R ℂ) (e : b ⊕ a ≃ n)
    (g : GL n R) (f : GL a R) (q : GL b R) (x : Matrix a n R) (y : Matrix n b R) :
    graphKernel χ e x y =
      χ g.val.det / χ f.val.det / χ q.val.det *
        graphKernel χ e (f⁻¹.val * x * g.val) (g⁻¹.val * y * q.val) := by
  wlog h_ne : graphKernel χ e x y ≠ 0
  · push Not at h_ne
    suffices graphKernel χ e (f⁻¹.val * x * g.val) (g⁻¹.val * y * q.val) = 0 by
      rw [h_ne, this, mul_zero]
    by_contra h_nz
    have h_eq := this χ e g⁻¹ f⁻¹ q⁻¹ _ _ h_nz
    simp only [inv_inv, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
      Matrix.mul_assoc _ g.val, Matrix.mul_one, Matrix.mul_assoc _ q.val, h_ne] at h_eq
    exact h_nz (by simpa [((isUnits_det_units _).map χ).ne_zero] using h_eq)
  obtain ⟨k, rfl, rfl⟩ := exists_eq_of_graphKernel_ne_zero h_ne
  let k' : GL n R := g⁻¹ * k * reindexGL e (blockGL (q, f))
  have hk'_rows : invLastRows e k' = f⁻¹.val * invLastRows e k * g.val := by
    rw [Matrix.mul_assoc]; ext i j; simp [k', Matrix.mul_apply, reindex_equiv e, ← map_inv]
  have hk'_cols : firstCols e k' = g⁻¹.val * firstCols e k * q.val := by
    ext i j; simp [k', Matrix.mul_apply, reindex_equiv e]
  have h_inv_g : χ g⁻¹.val.det = (χ g.val.det)⁻¹ := eq_inv_of_mul_eq_one_left <| by
    rw [← map_mul, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, map_one]
  rw [← hk'_rows, ← hk'_cols, graphKernel_invLastRows_firstCols,
    graphKernel_invLastRows_firstCols]
  simp only [k', Units.val_mul, det_mul, map_mul, h_inv_g,
    show ((reindexGL e) (blockGL (q, f))).val.det = q.val.det * f.val.det by
      simp [reindexGL, blockGL]]
  field_simp [((isUnits_det_units _).map χ).ne_zero]

lemma graphKernel_mul_right (χ : MulChar R ℂ) (e : b ⊕ a ≃ n)
    (x : Matrix a n R) (y : Matrix n b R) (q : GL b R) :
    graphKernel χ e x (y * q.val) = χ q.val.det * graphKernel χ e x y := by
  have h := graphKernel_equivariant χ e 1 1 q x y
  simp only [inv_one, Units.val_one, det_one, map_one, Matrix.one_mul, Matrix.mul_one, div_one,
    one_div] at h
  rw [h, mul_inv_cancel_left₀ ((isUnits_det_units q).map χ).ne_zero]

/-- Integrating `graphKernel χ e (invLastRows e k)` against any right-`χ⁻¹`-equivariant function
`Ψ` recovers `χ (det k) * Ψ (firstCols e k)`. -/
lemma sum_graphKernel_mul (χ : MulChar R ℂ) (e : b ⊕ a ≃ n) (Ψ : Matrix n b R → ℂ)
    (hΨ : ∀ (y : Matrix n b R) (q : GL b R), Ψ (y * q.val) = χ⁻¹ q.val.det * Ψ y) (k : GL n R) :
    ∑ y : Matrix n b R, graphKernel χ e (invLastRows e k) y * Ψ y =
      χ k.val.det * Ψ (firstCols e k) := by
  have h_inj : Injective (fun q : GL b R ↦ firstCols e k * q.val) :=
    (mul_right_injective_of_inv _ _ (invFirstRows_mul_firstCols e k)).comp Units.val_injective
  rw [← sum_of_injective _ h_inj _ _ (fun y hy ↦ by
    by_contra h_ne
    obtain ⟨l, hl_r, hl_c⟩ := exists_eq_of_graphKernel_ne_zero (left_ne_zero_of_mul h_ne)
    obtain ⟨q, hq, -⟩ := exists_firstCols_eq_mul_of_invLastRows_eq hl_r.symm
    exact hy ⟨q, (hl_c.symm.trans hq).symm⟩) fun _ ↦ rfl]
  have h_term (q : GL b R) :
      graphKernel χ e (invLastRows e k) (firstCols e k * q.val) * Ψ (firstCols e k * q.val) =
        χ k.val.det / card (GL b R) * Ψ (firstCols e k) := by
    rw [graphKernel_mul_right, graphKernel_invLastRows_firstCols, hΨ, inv_apply_eq_inv']
    field_simp [((isUnits_det_units q).map χ).ne_zero]
  simp only [h_term, sum_const, card_univ, nsmul_eq_mul]
  field_simp [show (card (GL b R) : ℂ) ≠ 0 from Nat.cast_ne_zero.2 card_ne_zero]

/-- Over a finite valuation-pair ring `R`, `graphKernel χ e` admits a `GL_b(R)`-orbit selector `d`
whose nonzero weighted entries `d y * graphKernel χ e x y` are roots of unity passing left
inverses from row blocks of `y` to opposite column blocks of `x`, whose `GL_b(R)`-orbit sum
recovers `#GL_b(R) * graphKernel χ e x y`, and which implements any `SquareLaw` pointwise on
matrices `y` with a left-invertible row block. -/
lemma exists_partner_kernel (χ : MulChar R ℂ) (e : b ⊕ a ≃ N ⊕ n)
    (hR : IsValuationPair (⊤ : Subring R)) :
    ∃ d : Matrix (N ⊕ n) b R → ℂ,
      (∀ (x : Matrix a (N ⊕ n) R) (y : Matrix (N ⊕ n) b R),
        (d y * graphKernel χ e x y ≠ 0 →
          IsOfFinOrder (d y * graphKernel χ e x y) ∧
          (HasLeftInv y.toRows₁ → HasLeftInv x.toCols₂) ∧
          (HasLeftInv y.toRows₂ → HasLeftInv x.toCols₁)) ∧
        ∑ q : GL b R, d (y * q.val) * graphKernel χ e x y =
          (card (GL b R) : ℂ) * graphKernel χ e x y) ∧
      ∀ {c : ℂ} {L : Matrix a (N ⊕ n) R → ℂ} {L' : Matrix (N ⊕ n) b R → ℂ},
        SquareLaw χ e c L L' → ∀ y : Matrix (N ⊕ n) b R,
          HasLeftInv y.toRows₁ ∨ HasLeftInv y.toRows₂ →
          L' y = c * ∑ x : Matrix a (N ⊕ n) R, graphKernel χ e x y * L x := by
  let rep (y : Matrix (N ⊕ n) b R) := (Set.range_nonempty (fun q : GL b R ↦ y * q.val)).some
  let d (y : Matrix (N ⊕ n) b R) : ℂ := if y = rep y then (card (GL b R) : ℂ) else 0
  have h_rep_mul (y : Matrix (N ⊕ n) b R) (q : GL b R) : rep (y * q.val) = rep y := by
    dsimp only [rep]; congr 1
    exact Set.ext fun _ ↦ ⟨fun ⟨l, hl⟩ ↦ ⟨q * l, by simpa [Matrix.mul_assoc] using hl⟩,
      fun ⟨l, hl⟩ ↦ ⟨q⁻¹ * l, by simpa [← Matrix.mul_assoc] using hl⟩⟩
  refine ⟨d, fun x y ↦ ?_, fun {c L L'} hL y hy ↦ ?_⟩
  · by_cases h_zero : graphKernel χ e x y = 0
    · simp [h_zero]
    obtain ⟨k, rfl, rfl⟩ := exists_eq_of_graphKernel_ne_zero h_zero
    refine ⟨fun h_ne ↦ ?_, ?_⟩
    · have hd : d (firstCols e k) = card (GL b R) := by
        dsimp only [d]; split_ifs with h <;> [rfl; exact absurd (by simp [d, h]) h_ne]
      rw [hd, graphKernel_invLastRows_firstCols,
        mul_div_cancel₀ _ (Nat.cast_ne_zero.2 card_ne_zero)]
      exact ⟨χ.isOfFinOrder (isUnits_det_units k).isOfFinOrder,
        hasLeftInv_toCols_of_hasLeftInv_toRows e k⟩
    · obtain ⟨q₀, hq₀⟩ := (Set.range_nonempty (fun q : GL b R ↦ firstCols e k * q.val)).some_mem
      have h_inj : Injective (fun q : GL b R ↦ firstCols e k * q.val) :=
        (mul_right_injective_of_inv _ _ (invFirstRows_mul_firstCols e k)).comp Units.val_injective
      have h_eq (q : GL b R) :
          d (firstCols e k * q.val) = if q = q₀ then (card (GL b R) : ℂ) else 0 := by
        simp only [d, h_rep_mul, rep, ← hq₀, h_inj.eq_iff]
      simp [h_eq]
  · obtain ⟨j, rfl⟩ := exists_eq_firstCols hR e hy
    let Ψ (y' : Matrix (N ⊕ n) b R) : ℂ := graphKernel χ⁻¹ e (invLastRows e j) y'
    let Φ (x : Matrix a (N ⊕ n) R) : ℂ := ∑ y', graphKernel χ e x y' * Ψ y'
    have h_law := hL.sum_eq_of_areMatched Φ Ψ ⟨fun x hx ↦ by
      obtain ⟨_, -, ht⟩ := exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨k, hk, -⟩ := exists_eq_of_graphKernel_ne_zero (left_ne_zero_of_mul ht)
      exact ⟨k, by simp [mem_intGL], hk.symm⟩,
      fun y' hy' ↦ by
        obtain ⟨k, -, hk⟩ := exists_eq_of_graphKernel_ne_zero hy'
        exact ⟨k, by simp [mem_intGL], hk.symm⟩,
      fun k _ ↦ sum_graphKernel_mul χ e Ψ (graphKernel_mul_right χ⁻¹ e _) k⟩
    let M (y' : Matrix (N ⊕ n) b R) : ℂ := ∑ x, graphKernel χ e x y' * L x
    have h_rhs : ∑ x, Φ x * L x = χ⁻¹ j.val.det * M (firstCols e j) := by
      rw [show ∑ x, Φ x * L x = ∑ y', Ψ y' * M y' by
        simp only [Φ, M, sum_mul, mul_sum]; rw [Finset.sum_comm]
        exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring]
      exact sum_graphKernel_mul χ⁻¹ e M
        (fun _ _ ↦ by simp [M, graphKernel_mul_right, mul_sum, mul_assoc]) j
    rw [sum_graphKernel_mul χ⁻¹ e L' (fun _ _ ↦ by simp [hL.right_mul]) j, h_rhs] at h_law
    exact mul_left_cancel₀ ((isUnits_det_units j).map χ⁻¹).ne_zero (by linear_combination h_law)

end PartnerKernel

/-! ### The turned datum and the sum over a square -/

section GridMove

open Matrix Fintype Finset Function Exchange MulChar

variable {P : Parameters} {D : Data P}

/-- Turning a monadic path datum across a square. Suppose `L i, M i` satisfy `SquareLaw χ ε C`
where `χ⁻¹` is the product of the characters of the old edges `(p, v)` and `(Q, U)` and opposite
edges have equal characters. Under the admissibility, vertical-edge and disjointness hypotheses on
`w` and the six nodes, every path datum `Λ : GridDatum ϑ` of order `n` on `w ∪ {(p, v), (Q, U)}`
gives a path datum `Φ : GridDatum ϑ` of order `n + 2` on `w ∪ {(U, R), (v, r)}` such that `Λ`
applied to the `ψ`-Fourier transform of `M` in the block `T` equals `C * Φ` applied to `L`. -/
lemma IsPathDatum.exists_square_move {ϑ : D.MFoldTwist} {B T J : Type}
    [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]
    {n : ℕ} {w : Finset (GridNode × GridNode)} {Λ : D.GridDatum ϑ}
    {p v Q U R r : GridNode}
    (τ : B ≃ D.NodeIndex U)
    (σ : D.NodeIndex p ⊕ T ≃ D.NodeIndex Q)
    (ρ : D.NodeIndex r ⊕ T ≃ D.NodeIndex R)
    (ψ : AddChar (gridModulus ϑ).ResidueRing ℂ)
    {χ : MulChar (gridModulus ϑ).ResidueRing ℂ}
    {ε : D.NodeIndex p ⊕ D.NodeIndex r ≃ D.NodeIndex v ⊕ B}
    {C : ℂ}
    {L : J → Matrix (D.NodeIndex r) (D.NodeIndex v ⊕ B) (gridModulus ϑ).ResidueRing → ℂ}
    {M : J → Matrix (D.NodeIndex v ⊕ B) (D.NodeIndex p) (gridModulus ϑ).ResidueRing → ℂ}
    (h_law : ∀ i : J, SquareLaw χ ε C (L i) (M i))
    (hQ : ∀ g : NodeFamily ϑ, IsAdmissibleFamily g →
      g R = blockInlGL ρ (g r) ∧
      ∀ k : GL (D.NodeIndex p) (gridModulus ϑ).ResidueRing,
        let u : NodeFamily ϑ := update (update g p k) Q (blockInlGL σ k)
        IsAdmissibleFamily u ∧ u p = k)
    (h_uv : U ≠ v)
    (h_vert : IsVerticalEdge Q U ∧ ¬IsVerticalEdge U R ∨ IsVerticalEdge p v ∧ ¬IsVerticalEdge v r)
    (h_nodes : ∀ q ∈ [U, R, v, r], q.2 ≤ (D.m, D.m) ∧ q ∉ [p, Q])
    (h_w : ∀ e ∈ w, e.1 ∉ [p, Q] ∧ e.2 ∉ [p, Q, R, r])
    (hΛ : D.IsPathDatum n (insert (p, v) (insert (Q, U) w)) Λ)
    (h_char : χ = (edgeChar ϑ (p, v) * edgeChar ϑ (Q, U))⁻¹ ∧
      edgeChar ϑ (U, R) = edgeChar ϑ (p, v) ∧ edgeChar ϑ (v, r) = edgeChar ϑ (Q, U)) :
    ∃ Φ : D.GridDatum ϑ,
      D.IsPathDatum (n + 2) (insert (U, R) (insert (v, r) w)) Φ ∧
      ∀ (f : EdgeTuple ϑ → Matrix T B (gridModulus ϑ).ResidueRing → J),
        DependsOn f w →
        Λ (fun S ↦
            let x := (S (Q, U)).submatrix τ σ
            ∑ k : Matrix T B (gridModulus ϑ).ResidueRing,
              ψ (k * x.toCols₂).trace * M (f S k) (fromRows (S (p, v)) x.toCols₁)) =
          C * Φ fun S ↦
            let x := (S (U, R)).submatrix ρ τ
            L (f S x.toRows₂) (fromCols (S (v, r)) x.toRows₁) := by
  let R₀ := (gridModulus ϑ).ResidueRing
  obtain ⟨d, hd_prop, hd_law⟩ := exists_partner_kernel χ ε (Modulus.isValuationPair_residueRing _)
  obtain ⟨Y, W, c, s, -, hc, hΛ_sum⟩ := hΛ.isShortSum
  have h_nodes' : (U.2 ≤ (D.m, D.m) ∧ U ≠ p ∧ U ≠ Q) ∧ (R.2 ≤ (D.m, D.m) ∧ R ≠ p ∧ R ≠ Q) ∧
      (v.2 ≤ (D.m, D.m) ∧ v ≠ p ∧ v ≠ Q) ∧ (r.2 ≤ (D.m, D.m) ∧ r ≠ p ∧ r ≠ Q) := by
    simpa [and_assoc] using h_nodes
  have h_notMem : (p, v) ∉ w ∧ (Q, U) ∉ w ∧ (U, R) ∉ w ∧ (v, r) ∉ w :=
    ⟨fun h ↦ (h_w _ h).1 (by simp), fun h ↦ (h_w _ h).1 (by simp),
      fun h ↦ (h_w _ h).2 (by simp), fun h ↦ (h_w _ h).2 (by simp)⟩
  have h_pv_ne_QU : (p, v) ≠ (Q, U) := fun h ↦ h_uv (Prod.mk.inj h).2.symm
  have h_UR_ne_vr : (U, R) ≠ (v, r) := fun h ↦ h_uv (Prod.mk.inj h).1
  -- Pack the old edges into `oldY` and the new edges into `newX`.
  let oldY (S : EdgeTuple ϑ) : Matrix (D.NodeIndex v ⊕ B) (D.NodeIndex p) R₀ :=
    fromRows (S (p, v)) ((S (Q, U)).submatrix τ σ).toCols₁
  let newX (M : Matrix (D.NodeIndex R) (D.NodeIndex U) R₀ ×
      Matrix (D.NodeIndex r) (D.NodeIndex v) R₀) :=
    fromCols M.2 (M.1.submatrix ρ τ).toRows₁
  let t (S : EdgeTuple ϑ) (M : Matrix (D.NodeIndex R) (D.NodeIndex U) R₀ ×
      Matrix (D.NodeIndex r) (D.NodeIndex v) R₀) : EdgeTuple ϑ :=
    fun e ↦ if e ∈ w then S e else update (update (0 : EdgeTuple ϑ) (U, R) M.1) (v, r) M.2 e
  let G (wt : Matrix (D.NodeIndex v ⊕ B) (D.NodeIndex p) R₀ → ℂ) : D.GridDatum ϑ :=
    Λ.bind (fun S M ↦ wt (oldY S) * graphKernel χ ε (newX M) (oldY S) *
      ψ ((M.1 * S (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr)).trace) t
  -- Equivariance of `G wt` under admissible families `g` and inner changes of basis `k` at `p`.
  have h_equiv (g : NodeFamily ϑ) (hg : IsAdmissibleFamily g)
      (k : GL (D.NodeIndex p) R₀) (wt : Matrix (D.NodeIndex v ⊕ B) (D.NodeIndex p) R₀ → ℂ)
      (f : EdgeTuple ϑ → ℂ) :
      G (fun y ↦ wt ((blockGL (g v, reindexGL τ.symm (g U)))⁻¹.val * y * k.val))
          (fun S ↦ f (tupleAction g S)) =
        edgeCharProd g (insert (U, R) (insert (v, r) w)) * G wt f := by
    let u : NodeFamily ϑ := update (update g p k) Q (blockInlGL σ k)
    obtain ⟨hgR, hu_spec⟩ := hQ g hg
    obtain ⟨hu, hup⟩ := hu_spec k
    change u p = k at hup
    have huQ : u Q = blockInlGL σ k := update_self ..
    have huU : u U = g U := by simp [u, h_nodes'.1.2.1, h_nodes'.1.2.2]
    have huv : u v = g v := by simp [u, h_nodes'.2.2.1.2.1, h_nodes'.2.2.1.2.2]
    have hu_w {e : GridNode × GridNode} (he : e ∈ w) : u e.1 = g e.1 ∧ u e.2 = g e.2 := by
      have ⟨h1, h2⟩ := h_w e he
      simp [u] at h1 h2 ⊢; exact ⟨by simp [h1.1, h1.2], by simp [h2.1, h2.2.1]⟩
    let G_sum : GL (D.NodeIndex v ⊕ B) R₀ := blockGL (g v, reindexGL τ.symm (g U))
    have h_char_eq :
        edgeCharProd g (insert (U, R) (insert (v, r) w)) =
          χ G_sum.val.det / χ (g r).val.det / χ k.val.det *
            edgeCharProd u (insert (p, v) (insert (Q, U) w)) := by
      have h_ne {ι : Type} [Fintype ι] [DecidableEq ι] (e' : GridNode × GridNode) (m : GL ι R₀) :
          edgeChar ϑ e' m.val.det ≠ 0 := ((isUnits_det_units m).map _).ne_zero
      have h_det_blk {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
          [Fintype ι₃] [DecidableEq ι₃] (e₀ : ι₁ ⊕ ι₂ ≃ ι₃) (m : GL ι₁ R₀) :
          (blockInlGL e₀ m).det = m.det := by ext; simp [blockInlGL, reindexGL, blockGL]
      have h_toUnit (e' : GridNode × GridNode) (m₁ m₂ : R₀ˣ) :
          ((edgeChar ϑ e').toUnitHom (m₁ / m₂) : ℂ) =
            edgeChar ϑ e' m₁.val / edgeChar ϑ e' m₂.val := by
        rw [map_div, Units.val_div_eq_div_val]; rfl
      simp only [edgeCharProd, prod_insert (show (U, R) ∉ insert (v, r) w by
          simp [h_UR_ne_vr, h_notMem]), prod_insert h_notMem.2.2.2,
        prod_insert (show (p, v) ∉ insert (Q, U) w by simp [h_pv_ne_QU, h_notMem]),
        prod_insert h_notMem.2.1]
      rw [Finset.prod_congr rfl (fun e he ↦ by rw [← (hu_w he).1, ← (hu_w he).2]),
        hup, huQ, huU, huv, hgR, h_char.1, h_char.2.1, h_char.2.2]
      simp only [show G_sum.val.det = (g v).val.det * (g U).val.det by simp [G_sum, blockGL,
          reindexGL], h_det_blk, h_toUnit, MulChar.inv_apply_eq_inv', MulChar.mul_apply,
        map_mul, GeneralLinearGroup.val_det_apply]
      field_simp [h_ne]
    rw [h_char_eq, mul_assoc]
    have h_act := hΛ.equivariant u hu
      (fun S ↦ ∑ M, wt (oldY S) * graphKernel χ ε (newX M) (oldY S) *
        ψ ((M.1 * S (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr)).trace * f (t S M))
    change _ = χ G_sum.val.det / χ (g r).val.det / χ k.val.det * _
    rw [show G wt f = _ from GridDatum.bind_apply .., ← h_act, GridDatum.bind_apply,
      ← smul_eq_mul, ← LinearMap.map_smul]
    congr 1; funext S
    rw [Pi.smul_apply, smul_eq_mul, mul_sum]
    let bijM := Prod.map
      (fun A : Matrix (D.NodeIndex R) (D.NodeIndex U) R₀ ↦ (g R)⁻¹.val * A * (g U).val)
      (fun B : Matrix (D.NodeIndex r) (D.NodeIndex v) R₀ ↦ (g r)⁻¹.val * B * (g v).val)
    have h_bij : Bijective bijM :=
      ((mul_left_injective_of_invertible (g U).val).comp
        (mul_right_injective_of_invertible (g R)⁻¹.val)).bijective_of_finite.prodMap
      ((mul_left_injective_of_invertible (g v).val).comp
        (mul_right_injective_of_invertible (g r)⁻¹.val)).bijective_of_finite
    conv_rhs => rw [← h_bij.sum_comp]
    refine sum_congr rfl fun M _ ↦ ?_
    have h_oldY : oldY (tupleAction u S) = G_sum⁻¹.val * oldY S * k.val := by
      ext (i | i) j
      · simp [oldY, tupleAction, G_sum, hup, huv, Matrix.mul_apply, ← map_inv]
      · simp [oldY, tupleAction, G_sum, huQ, huU, Matrix.mul_apply, reindex_equiv τ,
          reindex_equiv σ, ← map_inv, Finset.sum_mul, mul_assoc]
    have h_newX : newX (bijM M) = (g r)⁻¹.val * newX M * G_sum.val := by
      ext i (j | j)
      · simp [newX, bijM, G_sum, Matrix.mul_apply]
      · simp [newX, bijM, G_sum, hgR, Matrix.mul_apply, reindex_equiv ρ, reindex_equiv τ,
          ← map_inv, Finset.sum_mul, mul_assoc]
    have h_trace : ((bijM M).1 * tupleAction u S (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr) =
        (M.1 * S (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr) := by
      ext i j; simp [bijM, tupleAction, hgR, huQ, huU, Matrix.mul_apply, ← Matrix.mul_assoc,
        reindex_equiv ρ, reindex_equiv σ, ← map_inv, Matrix.one_apply]
    have h_t : t (tupleAction u S) (bijM M) = tupleAction g (t S M) := funext fun e ↦ by
      by_cases he : e ∈ w
      · simp [t, he, tupleAction, (hu_w he).1, (hu_w he).2]
      · rcases eq_or_ne e (v, r) with rfl | h1
        · simp [t, he, tupleAction, bijM]
        · rcases eq_or_ne e (U, R) with rfl | h2
          · simp [t, he, tupleAction, bijM, h1]
          · simp [t, he, tupleAction, update, h1, h2]
    rw [h_oldY, h_newX, h_trace, h_t]
    linear_combination wt (G_sum⁻¹.val * oldY S * k.val) *
      ψ ((M.1 * S (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr)).trace * f (tupleAction g (t S M)) *
      graphKernel_equivariant χ ε G_sum (g r) k (newX M) (oldY S)
  -- Averaging `h_equiv` at `g = 1` over `k ∈ GL_p(R₀)` identifies `G 1` with `G d`.
  have hG_eq : G 1 = G d := LinearMap.ext fun f ↦ (mul_left_cancel₀
      (Nat.cast_ne_zero.2 (card_ne_zero (α := GL (D.NodeIndex p) R₀))) <| by
    have hg1 : IsAdmissibleFamily (1 : NodeFamily ϑ) := ⟨fun _ ↦ one_mem _, fun _ ↦ by
      simp [← Prod.one_eq_mk]⟩
    have h_const (k : GL (D.NodeIndex p) R₀) : G (fun y ↦ d (y * k.val)) f = G d f := by
      simpa [tupleAction_one, edgeCharProd, ← Prod.one_eq_mk] using h_equiv 1 hg1 k d f
    rw [show (card (GL (D.NodeIndex p) R₀) : ℂ) * G d f =
        ∑ k : GL (D.NodeIndex p) R₀, G (fun y ↦ d (y * k.val)) f by simp [h_const]]
    simp only [G, GridDatum.bind_apply, hΛ_sum, Pi.one_apply, one_mul]
    rw [mul_sum, Finset.sum_comm]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [← mul_sum, mul_left_comm]
    congr 1
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun M _ ↦ ?_
    simp only [← sum_mul]; rw [sum_mul, (hd_prop _ _).2]; ring).symm
  have h_leftInv_rows₂ (S : EdgeTuple ϑ) (hS : HasLeftInv (S (Q, U))) :
      HasLeftInv (oldY S).toRows₂ := by
    obtain ⟨L₀, hL₀⟩ := hS
    refine ⟨L₀.submatrix (σ ∘ .inl) τ, Matrix.ext fun i j ↦ ?_⟩
    simpa [oldY, Matrix.mul_apply, reindex_equiv τ, Matrix.one_apply] using
      congrFun₂ hL₀ (σ (.inl i)) (σ (.inl j))
  refine ⟨G 1, ⟨fun g hg f ↦ by simpa [← Pi.one_def] using h_equiv g hg 1 1 f, ?_⟩, fun f hf ↦ ?_⟩
  -- Short-sum bound and vertical left-invertibility via `IsShortSum.bind`.
  · rw [hG_eq]
    have h_card : card (Matrix (D.NodeIndex R) (D.NodeIndex U) R₀ ×
        Matrix (D.NodeIndex r) (D.NodeIndex v) R₀) ≤ edgeMatrixCountBound ϑ ^ 2 := by
      rw [card_prod, sq]
      exact Nat.mul_le_mul (card_matrix_le_edgeMatrixCountBound h_nodes'.2.1.1 h_nodes'.1.1)
        (card_matrix_le_edgeMatrixCountBound h_nodes'.2.2.2.1 h_nodes'.2.2.1.1)
    refine hΛ.isShortSum.bind h_card fun S M hM_ne hS_inv ↦ ?_
    obtain ⟨h_fin, h_inv₂, h_inv₁⟩ := (hd_prop (newX M) (oldY S)).1 (left_ne_zero_of_mul hM_ne)
    refine ⟨h_fin.mul (ψ.toMonoidHom.isOfFinOrder (isMulTorsion_of_finite _)), fun e he h_ev ↦ ?_⟩
    rcases mem_insert.1 he with rfl | he'
    · obtain ⟨L₀, hL₀⟩ := h_inv₂ (by simpa [oldY] using hS_inv (p, v) (by simp) (by grind))
      refine ⟨(fromCols L₀ 0).submatrix τ.symm ρ.symm, Matrix.ext fun i j ↦ ?_⟩
      simpa [t, h_notMem, h_UR_ne_vr, newX, Matrix.mul_apply, reindex_equiv ρ, reindex_equiv τ,
        toRows₁, Matrix.one_apply] using congrFun₂ hL₀ (τ.symm i) (τ.symm j)
    · rcases mem_insert.1 he' with rfl | he_w
      · simpa [t, h_notMem, newX] using
          h_inv₁ (h_leftInv_rows₂ S (hS_inv (Q, U) (by simp) (by grind)))
      · simpa [t, he_w] using hS_inv e (by simp [he_w]) h_ev
  -- Pointwise `SquareLaw` transfer on each root-of-unity support tuple `s y`.
  · rw [GridDatum.bind_apply, hΛ_sum, hΛ_sum, mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    by_cases hcy : c y = 0
    · simp [hcy]
    have h_inv : HasLeftInv (oldY (s y)).toRows₁ ∨ HasLeftInv (oldY (s y)).toRows₂ :=
      h_vert.elim (fun h ↦ .inr (h_leftInv_rows₂ (s y) ((hc y hcy).2 (Q, U) (by simp) h.1)))
        (fun h ↦ .inl (by simpa [oldY] using (hc y hcy).2 (p, v) (by simp) h.1))
    have h_f_eq (M) : f (t (s y) M) = f (s y) := hf fun _ he ↦ by simp [t, Finset.mem_coe.1 he]
    have h_tr (M₁ : Matrix (D.NodeIndex R) (D.NodeIndex U) R₀) :
        ((M₁ * s y (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr)).trace =
          ((M₁.submatrix ρ τ).toRows₂ * ((s y (Q, U)).submatrix τ σ).toCols₂).trace := by
      simp [trace, Matrix.mul_apply, ← τ.sum_comp]
    have h_sub (A : Matrix (D.NodeIndex r ⊕ T) B R₀) :
        ((Matrix.reindex ρ τ) A).submatrix ρ τ = A := by
      ext (i | i) j <;> simp [Matrix.reindex_apply]
    simp only [Pi.one_apply, one_mul, h_f_eq, t, h_notMem, ↓reduceIte, update_self,
      update_of_ne h_UR_ne_vr, h_tr]
    rw [mul_left_comm C (c y), Fintype.sum_prod_type, ← (Matrix.reindex ρ τ).sum_comp]
    simp only [newX, h_sub]
    congr 1
    rw [sum_eq_sum_fromRows, Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [hd_law (h_law (f (s y) k)) (oldY (s y)) h_inv, sum_eq_sum_fromCols, mul_sum]
    simp only [toRows₁_fromRows, toRows₂_fromRows, mul_sum]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

end GridMove

/-! ## The exchange on a square of the grids -/

section GridSquare

open Fintype Exchange

variable {P : Parameters} {D : Data P} {a b : ℕ}

variable (D) in
/-- The ratio of the turn at `(i, j)`: the product over `1 ≤ s ≤ D.t` of the ratios of Hecke values
at `s` of the character `untwistedLiftChar (i + 1) * untwistedLiftChar (j + 1)` at the twist
`ϑ ^ (j + 1)`. -/
noncomputable def turnRatio (i j : ℕ) (ϑ : D.MFoldTwist) : ℝ :=
  D.lRatioProd (D.untwistedLiftChar (i + 1) * D.untwistedLiftChar (j + 1)) D.t (ϑ.pow (j + 1))

/-- The critical pair of a square: the character `ν = untwistedLiftChar (a + 1) * untwistedLiftChar
(b + 1)`, of weight `-(D.liftWeight (a + 1) + D.liftWeight (b + 1))`, with its tame part `tamePart`
and the integer `z = D.t`. In a critical pair (`D.CriticalPair`) minus the weight is at least `z`
and at most `4 * D.b` at every infinite place. -/
noncomputable def squarePair (ha : a < D.m) (hb : b < D.m) : D.CriticalPair where
  character := D.untwistedLiftChar (a + 1) * D.untwistedLiftChar (b + 1)
  negWeight := D.liftWeight (b + 1) + D.liftWeight (a + 1)
  tamePart := D.chiMLocal ^ (a + 1 + (b + 1) : ℤ)
  z := D.t
  hasWeight := by
    -- the weights add, and the tame parts multiply
    simpa [← zpow_add] using! (D.untwistedLiftChar_hasWeight a.succ).mul
      (D.untwistedLiftChar_hasWeight b.succ)
  tamePart_eq_one := by simp_all
  z_mem := by grind
  le_negWeight := by grind [Pi.add_apply]
  negWeight_le v := by
    simp only [Pi.add_apply]
    grind [liftWeight_le_two_mul_b]

/-- The pair `squarePair ha hb` of the square `(a, b)` is ramified: its tame part is nontrivial
exactly at the chosen places. -/
lemma isRamified_squarePair (ha : a < D.m) (hb : b < D.m) : (squarePair ha hb).IsRamified :=
  D.chiMLocal_zpow_ne_one_iff_isChosen (a + 1 + (b + 1)) (by omega) (by omega)

/-- For `i, j < D.m` the ratio `turnRatio i j` of a turn is the product of the ratios of Hecke
values of a ramified critical pair at the powers `ϑ ^ (j + 1)` of the twists. -/
lemma isRamifiedRatio_turnRatio {i j : ℕ} (hi : i < D.m) (hj : j < D.m) :
    D.IsRamifiedRatio (D.turnRatio i j) :=
  ⟨squarePair hi hj, ⟨j + 1, by omega, by omega⟩, isRamified_squarePair hi hj, fun _ ↦ rfl⟩

lemma isRamifiedRatio_turnRatio_of_mem (s : ℕ × ℕ)
    (hs : s ∈ Finset.range D.m ×ˢ Finset.range D.m) : D.IsRamifiedRatio (D.turnRatio s.1 s.2) :=
  isRamifiedRatio_turnRatio (by grind) (by grind)

/-- The character of the residue ring with given tame parts is multiplicative in the tame parts. -/
lemma charOfTamePart_gridModulus_mul {ϑ : D.MFoldTwist}
    (ψ ψ' : ∀ w : FinPlace D.E, MulChar (ResField w) ℂ) :
    (gridModulus ϑ).charOfTamePart (ψ * ψ') =
      (gridModulus ϑ).charOfTamePart ψ * (gridModulus ϑ).charOfTamePart ψ' := by
  ext
  apply finprod_mul_distrib <;> toFinite_tac

/-- The characters of the two edges at the node `(a, b)` of the grid `z` multiply to the character
with components `(squarePair ha hb).tamePart * ϑ.tamePart ^ n`, for `n = a + 1` if `z` and
`n = b + 1` otherwise. -/
lemma edgeChar_columnEdge_mul_rowEdge (z : Bool) (ha : a < D.m) (hb : b < D.m) (ϑ : D.MFoldTwist) :
    edgeChar ϑ (columnEdge z a b) * edgeChar ϑ (rowEdge z a b) =
      (gridModulus ϑ).charOfTamePart ((squarePair ha hb).tamePart * ϑ.tamePart ^
        ((if z then a else b) + 1)) := by
  rw [edgeChar, edgeChar, ← charOfTamePart_gridModulus_mul]
  congr 1
  -- One of the two tame parts carries a power of the twist, the other the trivial twist.
  have h_one : (1 : D.Twist).tamePart = 1 := rfl
  cases z <;> simp [squarePair, liftTamePart, TameChar.pow, h_one, zpow_add, mul_assoc, mul_comm,
    mul_left_comm]

/-- Let `a, b < D.m`, let `r` be the sum of the ranks of the corners `(a, b + 1)` and `(a + 1, b)`
of the grid `z`, and let `p`, `q` be index types with `card p + card q = r`. The character
`gridChar ϑ z a p` of the edges of the lifts times `gridChar ϑ (!z) b q`, that of the edges of the
transposed lifts, is `rankTwist` of the product `ν * ϑ.toAutChar ^ n` in the rank `r`. Here
`ν = (squarePair ha hb).character = D.untwistedLiftChar (a + 1) * D.untwistedLiftChar (b + 1)`, with
`D.untwistedLiftChar j` the untwisted character of the `j`-th lift, `ϑ.toAutChar` is the character
of the twist `ϑ`, and `n = a + 1` if `z`, `n = b + 1` otherwise. -/
lemma gridChar_mul_gridChar_eq_rankTwist (z : Bool) (ha : a < D.m) (hb : b < D.m) (ϑ : D.MFoldTwist)
    {p q : Type} [Fintype p] [Fintype q]
    (hpq : card p + card q = card (D.GridIndex z a (b + 1)) + card (D.GridIndex z (a + 1) b)) :
    gridChar ϑ z a p * gridChar ϑ (!z) b q =
      rankTwist ((squarePair ha hb).character * ϑ.toAutChar ^ ((if z then a else b) + 1))
        (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
  -- The sum of the two ranks is even, so the rounded halves of `card p` and `card q` add up.
  have h_half : (card p + (!z).toNat) / 2 + (card q + z.toNat) / 2 =
      card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) / 2 := by
    cases z <;> simp_all [card_gridIndex] <;> grind
  rw [rankTwist, ← h_half]
  cases z <;> simp only [squarePair, gridChar, liftChar, TameChar.pow, TameChar.one, Bool.cond_true,
    Bool.cond_false, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, ite_true,
    ite_false, Bool.false_eq_true, pow_add] <;> ac_rfl

/-- For the sum `W` of the corners `(a, b + 1)` and `(a + 1, b)` of the square, half the rank of
`W` minus its number of negative signs is at most `(squarePair ha hb).negWeight τ`, minus the
weight of the pair of the square at the infinite place `τ`. The signs are `D.gridSigns z 0`, those
of the nodes of the grid `z` (offset `0`). -/
lemma card_gridIndex_square_le (z : Bool) (ha : a < D.m) (hb : b < D.m)
    (τ : NumberField.InfinitePlace D.E) :
    (card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) : ℤ) ≤
      2 * ((squarePair ha hb).negWeight τ : ℤ) +
        2 * (negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) : ℤ) := by
  -- both ranks are at most `2 * D.n D.m ≤ 2 * D.halfGap`, and both weights are at least `D.halfGap`
  have h_n : D.n D.m ≤ D.halfGap := D.nat_le_of_hasLogBound
  simp only [squarePair, Fintype.card_sum, Pi.add_apply, negCount_sumElim, Nat.cast_add]
  grw [card_gridIndex_le, card_gridIndex_le, h_n] <;> grind

/-- Crossing the square `(a, b)` of the grid `z`, for `a, b < m`: there are a constant `κ`, a
bijection `σ` between the indices of the two pairs of opposite corners and numbers `c ϑ ≠ 0` with
the following property. Let `f` be a form at the node `(a, b + 1)` and `l` a functional on the forms
at the node `(a + 1, b)`. Then the values of `l` at the images of `f` through `(a + 1, b + 1)`, by a
lift and a transposed lift, each by a matrix modulo `gridModulus ϑ`, and through `(a, b)`, by a
transposed lift and a lift, satisfy the square law with constant `κ / c ϑ`; the constant `κ` may be
`0`. The character of the law is the inverse of the product of the characters `edgeChar` of the
edges from `(a, b)` to `(a, b + 1)` (`columnEdge`) and to `(a + 1, b)` (`rowEdge`). The numbers
`c ϑ` have absolute value `turnRatio` up to a constant and a power of the norm of the modulus of
`ϑ`. -/
lemma exists_squareLaw_grid_hasAbsUpToNormPower (z : Bool) (ha : a < D.m) (hb : b < D.m) :
    ∃ (κ : ℂ) (σ : D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1) ≃
        D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (c : D.MFoldTwist → ℂˣ),
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (if z then D.turnRatio b a else D.turnRatio a b) ∧
      ∀ (ϑ : D.MFoldTwist) (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
        SquareLaw (edgeChar ϑ (columnEdge z a b) * edgeChar ϑ (rowEdge z a b))⁻¹ σ (κ / c ϑ)
          -- the lift of `f`, then the transposed lift
          (fun x : Matrix (D.GridIndex z (a + 1) (b + 1))
              (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) (gridModulus ϑ).ResidueRing ↦
            l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
          -- the transposed lift of `f`, then the lift
          (fun y : Matrix (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b)
              (D.GridIndex z a b) (gridModulus ϑ).ResidueRing ↦
            l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))) := by
  -- The character of the square is `(ν * ϑ.toAutChar ^ n)⁻¹` for `ν = pair.character`, with
  -- `n = a + 1` if `z` and `n = b + 1` otherwise. It is tame, and a function `c` of `ϑ` with
  -- `‖c ϑ‖ ^ 2` a constant times `lValueProd` of this character has the absolute value
  -- `turnRatio` up to a constant and a power of the norm.
  let pair : D.CriticalPair := squarePair ha hb
  let n : D.LiftIndex := ⟨(if z then a else b) + 1, by grind⟩
  have h_signs : negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) =
      negCount (D.gridSigns z 0 (a + 1) (b + 1)) + negCount (D.gridSigns z 0 a b) := by
    simp [negCount_gridSigns]
  have h_rank : card (D.GridIndex z (a + 1) (b + 1)) = card (D.GridIndex z a b) + 2 * D.t := by
    cases z <;> simp [card_gridIndex] <;> grind
  have h_ratio : (fun ϑ : D.MFoldTwist ↦ D.lRatioProd pair.character pair.z (ϑ.pow n)) =
      if z then D.turnRatio b a else D.turnRatio a b := by
    funext ϑ
    cases z <;> simp [pair, n, squarePair, turnRatio, mul_comm (D.untwistedLiftChar (b + 1))]
  have h_card : card (D.GridIndex z a b ⊕ D.GridIndex z (a + 1) (b + 1)) =
      card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
    cases z <;> simp [card_gridIndex] <;> grind
  -- On the two kept corners together at least two more signs are positive than negative.
  have h_few_neg :
      2 * negCount (Sum.elim (D.gridSigns z 0 a (b + 1)) (D.gridSigns z 0 (a + 1) b)) + 2 ≤
        card (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
    cases z <;> simp [card_gridIndex, negCount_gridSigns] <;> grind
  have h_chars (ϑ : D.MFoldTwist) {p q : Type} [Fintype p] [Fintype q]
      (hpq : card p + card q = card (D.GridIndex z a (b + 1)) + card (D.GridIndex z (a + 1) b)) :
      gridChar ϑ z a p * gridChar ϑ (!z) b q =
        rankTwist (pair.character * ϑ.toAutChar ^ n.val)⁻¹⁻¹
          (D.GridIndex z a (b + 1) ⊕ D.GridIndex z (a + 1) b) := by
    simpa only [inv_inv] using gridChar_mul_gridChar_eq_rankTwist z ha hb ϑ hpq
  have h_square : ∃ (C : ℝ) (κ : ℂ), ∀ ϑ : D.MFoldTwist, ∃ c ≠ (0 : ℂ),
      ‖c‖ ^ 2 = C * lValueProd (D.twistModulus ϑ D.natB).places
        (pair.character * ϑ.toAutChar ^ n.val)⁻¹ D.t ∧
      ∀ (f : D.GridForm z a (b + 1)) (l : D.GridForm z (a + 1) b →ₗ[ℂ] ℂ),
        SquareLaw ((gridModulus ϑ).charOfTamePart (pair.tamePart * ϑ.tamePart ^ n.val))⁻¹
          (equivOfCardEq h_card)
          (κ / c) (fun x ↦ l (transposedMove x.toCols₂ (liftMove x.toCols₁ f)))
          (fun y ↦ l (liftMove y.toRows₂ (transposedMove y.toRows₁ f))) :=
    one_square_identity_of_isEdgeFamily (D.gridSpace 0 z a b) (D.gridSpace 0 z (a + 1) (b + 1))
      (D.gridSpace 0 z a (b + 1))
      (D.gridSpace 0 z (a + 1) b) (isEdgeFamily_grid_succ_right id ha hb)
      (isEdgeFamily_grid_succ_left id ha hb) (isEdgeFamily_grid_succ_left id ha hb.le)
      (isEdgeFamily_grid_succ_right id ha.le hb) (equivOfCardEq h_card) h_signs D.t h_rank h_few_neg
      (card_gridIndex_square_le z ha hb)
      (pair.isTameFor_inv_mul_pow (isRamified_squarePair ha hb) D.natB n) h_chars
  choose C κ c hc_ne hc_norm h_law using h_square
  refine ⟨κ, equivOfCardEq h_card, fun ϑ ↦ Units.mk0 (c ϑ) (hc_ne ϑ), ?_, fun ϑ f l ↦ ?_⟩
  · simpa only [h_ratio, Units.val_mk0] using
      pair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd D.natB n hc_norm
  · rw [edgeChar_columnEdge_mul_rowEdge z ha hb ϑ]
    exact h_law ϑ f l

end GridSquare

/-!
## Transfers of periods, and turns off the diagonal

Pushing a descent past a row of lifts (`descent_past_gridPathMap`), crossing a diagonal square via
two seesaws and line reversal (`hasRoute_succ`), and composing the `m` stages from the first path
(`stageEdges 0`) to the last (`stageEdges m`) via `HasRoute`.
-/

section RowLadder

open MeasureTheory Fintype Finset Matrix Function Exchange Space Submodule

variable {P : Parameters} {D : Data P} {a b j : ℕ}

variable (D) in
/-- A route of order cost `k` and twist factor `c` from stage `i` to stage `j`: path data `Λ` of
order `n` on `stageEdges i` yield path data `Φ` of order `n + k` on `stageEdges j`, and if `Φ` is
proportional to `Ξ` at stage `j`, then `Λ` is proportional to `Ξ / c` at stage `i`. -/
def HasRoute {i j : ℕ} (hi : i ≤ D.m) (hj : j ≤ D.m) (k : ℕ) (c : D.MFoldTwist → ℂˣ) : Prop :=
  ∀ (n : ℕ) (Λ : ∀ ϑ : D.MFoldTwist, D.GridDatum ϑ),
    (∀ ϑ : D.MFoldTwist, D.IsPathDatum n (D.stageEdges i) (Λ ϑ)) →
    ∃ Φ : ∀ ϑ : D.MFoldTwist, D.GridDatum ϑ,
      (∀ ϑ : D.MFoldTwist, D.IsPathDatum (n + k) (D.stageEdges j) (Φ ϑ)) ∧
      ∀ Ξ : D.PeriodTriple → ℂ, D.IsProportional hj Φ Ξ →
        D.IsProportional hi Λ fun x : D.PeriodTriple ↦ Ξ x / c x.1

/-- Pushing a descent past `a` lifts along row `b` in grid `z`. For `a ≤ b < m`, there are a
constant `κ` and nonzero factors `c ϑ` whose modulus up to a norm power is the product of the
`turnRatio`s of the `a` interior squares on row `b`, such that whenever `w` avoids grid `z` except
possibly on row edges `(i, b) → (i + 1, b)` with `i ≥ a`, every path datum `Λ` of order `n` on
`w ∪ gridPath z a b` yields a path datum `Φ` of order `n + 2 * a` on
`insert (columnEdge z a b) (gridPath z a (b + 1)) ∪ w` exchanging the path to `(a, b)` for the path
to `(a, b + 1)` followed by a single descent. -/
lemma descent_past_gridPathMap (hb : b < D.m) (z : Bool) (hab : a ≤ b) :
    ∃ (κ : ℂ) (c : D.MFoldTwist → ℂˣ),
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (∏ i ∈ range a, if z then D.turnRatio b i else D.turnRatio i b) ∧
      ∀ (ϑ : D.MFoldTwist) (n : ℕ) (w : Finset (GridNode × GridNode)) (Λ : D.GridDatum ϑ),
        (∀ e ∈ w, z ∉ [e.1.1, e.2.1] ∨ ∃ i ≥ a, e = rowEdge z i b) →
        D.IsPathDatum n (w ∪ D.gridPath z a b) Λ →
        ∃ Φ : D.GridDatum ϑ,
          D.IsPathDatum (n + 2 * a) (insert (columnEdge z a b) (D.gridPath z a (b + 1)) ∪ w) Φ ∧
          ∀ (F : D.GridForm z 0 D.m) (l : EdgeTuple ϑ → D.GridForm z a b →ₗ[ℂ] ℂ),
            DependsOn l w →
            Λ (fun S ↦ l S (gridPathMap S z a b F)) =
              κ / c ϑ * Φ fun S ↦
                l S (transposedMove (S (columnEdge z a b)) (gridPathMap S z a (b + 1) F)) := by
  induction a with
  | zero =>
    refine ⟨1, 1, by simpa [Pi.one_def] using HasAbsUpToNormPower.one, fun ϑ n w Λ _ hΛ ↦ ?_⟩
    have h_edges :
        insert (columnEdge z 0 b) (D.gridPath z 0 (b + 1)) ∪ w = w ∪ D.gridPath z 0 b := by
      rw [union_comm]; congr 1
      simp [gridPath, legEdges, ← insert_Ico_add_one_left_eq_Ico hb]
    exact ⟨Λ, by simpa [h_edges] using hΛ,
      fun F l _ ↦ by simp [gridPathMap, legDescents_of_lt _ z hb]⟩
  | succ a ih =>
    obtain ⟨κ', c', hc', h_prev⟩ := ih (Nat.le_of_succ_le hab)
    obtain ⟨κ, σ, c, hc, h_law⟩ :=
      exists_squareLaw_grid_hasAbsUpToNormPower z ((Nat.lt_of_succ_le hab).trans hb) hb
    refine ⟨κ' * κ, c' * c, ?_, fun ϑ n w Λ hw hΛ ↦ ?_⟩
    · rw [show (fun ϑ : D.MFoldTwist ↦ ((c' * c) ϑ : ℂ)) =
          (fun ϑ ↦ (c' ϑ : ℂ)) * fun ϑ ↦ (c ϑ : ℂ) from funext fun _ ↦ Units.val_mul ..,
        prod_range_succ]
      exact hc'.mul hc
    have h_edges_prev :
        insert (rowEdge z a b) w ∪ D.gridPath z a b = w ∪ D.gridPath z (a + 1) b := by
      ext e; simp [gridPath, range_add_one]
    obtain ⟨Φ, hΦ, h_step₁⟩ := h_prev ϑ n (insert (rowEdge z a b) w) Λ
      (fun e he ↦ (mem_insert.1 he).elim (fun h ↦ .inr ⟨a, le_rfl, h⟩) fun h ↦
        (hw e h).imp_right fun ⟨i, hi, heq⟩ ↦ ⟨i, Nat.le_of_succ_le hi, heq⟩)
      (h_edges_prev.symm ▸ hΛ)
    let w' : Finset (GridNode × GridNode) := D.gridPath z a (b + 1) ∪ w
    have h_old : insert (columnEdge z a b) (insert (rowEdge z a b) w') =
        insert (columnEdge z a b) (D.gridPath z a (b + 1)) ∪ insert (rowEdge z a b) w := by
      ext e; simp [w']; tauto
    have h_new : insert (columnEdge z (a + 1) b) (insert (rowEdge z a (b + 1)) w') =
        insert (columnEdge z (a + 1) b) (D.gridPath z (a + 1) (b + 1)) ∪ w := by
      ext e; simp [w', gridPath, range_add_one]
    obtain ⟨Φ', hΦ', h_step₂⟩ :=
      (h_old.symm ▸ hΦ).exists_square_move
        (J := D.GridForm z a (b + 1) × (D.GridForm z (a + 1) b →ₗ[ℂ] ℂ))
        (R := (z, a + 1, b + 1)) (r := (z, a + 1, b + 1))
        (Equiv.refl _) (.sumEmpty _ Empty) (.sumEmpty _ Empty) 1
        (fun i ↦ h_law ϑ i.1 i.2)
        (fun g hg ↦ ⟨(blockInlGL_sumEmpty _).symm, fun k ↦ by
          rw [blockInlGL_sumEmpty, update_idem]
          exact ⟨⟨fun z' ↦ by rw [update_of_ne (by grind)]; exact hg.1 z',
            fun k' ↦ by rw [update_of_ne (by grind), update_of_ne (by grind)]; exact hg.2 k'⟩,
            update_self ..⟩⟩)
        (by simp) (by cases z <;> simp [IsVerticalEdge])
        (by intro q hq; rcases (by simpa using hq) with rfl | rfl | rfl | rfl <;>
              simp [Prod.le_def] <;> omega)
        (by intro e he
            rcases mem_union.1 he with he_p | he_w
            · simp only [gridPath, legEdges, mem_union, mem_image, mem_range, mem_Ico] at he_p
              rcases he_p with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> simp <;> grind
            · rcases hw e he_w with h1 | ⟨i, hi, rfl⟩ <;> [simp at h1 ⊢; simp] <;> grind)
        (by simp [edgeChar, IsVerticalEdge])
    refine ⟨Φ', by simpa [h_new, Nat.mul_add, ← add_assoc] using hΦ', fun F l hl ↦ ?_⟩
    have h_first := h_step₁ F (fun S ↦ l S ∘ₗ liftMove (S (rowEdge z a b))) fun S S' h_eq ↦ by
      dsimp only; rw [hl fun e he ↦ h_eq e (by simp [he]), h_eq (rowEdge z a b) (by simp)]
    have h_second := h_step₂ (fun S _ ↦ (gridPathMap S z a (b + 1) F, l S)) fun S S' h_eq ↦
      funext fun _ ↦ Prod.ext
        (congrArg (· F) (gridPathMap_congr (a := a) (b := b + 1)
          fun e he ↦ h_eq e (by simp [w', he])))
        (hl fun e he ↦ h_eq e (by simp [w', he]))
    have h_sum_empty (f : Matrix Empty (D.NodeIndex (z, a + 1, b))
        (gridModulus ϑ).ResidueRing → ℂ) : ∑ k, f k = f 0 :=
      Finset.sum_eq_single 0 (fun k _ hk ↦ absurd (Matrix.ext fun i _ ↦ i.elim) hk) (by simp)
    have h_sub₁ (A : Matrix (D.NodeIndex (z, a + 1, b)) (D.NodeIndex (z, a, b))
        (gridModulus ϑ).ResidueRing) :
        (A.submatrix (Equiv.refl _) (Equiv.sumEmpty _ Empty)).toCols₁ = A := rfl
    have h_sub₂ (A : Matrix (D.NodeIndex (z, a + 1, b + 1)) (D.NodeIndex (z, a + 1, b))
        (gridModulus ϑ).ResidueRing) :
        (A.submatrix (Equiv.sumEmpty _ Empty) (Equiv.refl _)).toRows₁ = A := rfl
    simp only [h_sum_empty, one_apply, one_mul, toRows₁_fromRows, toRows₂_fromRows,
      toCols₁_fromCols, toCols₂_fromCols, h_sub₁, h_sub₂] at h_second
    exact h_first.trans <| by
      dsimp only [LinearMap.comp_apply, gridPathMap, rowEdge, columnEdge]
      rw [h_second]; simp [Pi.mul_apply, Units.val_mul]; ring

private def subdiagEquiv (D : Data P) (j : ℕ) :
    D.GridIndex true j (j + 1) ≃ D.GridIndex false (j + 1) j :=
  (gridSpace_subdiag (D := D) j).choose

private lemma gridSigns_subdiagEquiv (D : Data P) (j : ℕ) :
    D.gridSigns false 0 (j + 1) j ∘ (D.subdiagEquiv j).symm.symm =
      D.gridSigns true 0 j (j + 1) :=
  (gridSpace_subdiag (D := D) j).choose_spec.choose

private lemma gridSpace_subdiagEquiv (D : Data P) (j : ℕ) :
    D.gridSpace 0 true j (j + 1) =
      (D.gridSpace 0 false (j + 1) j).reindex (D.subdiagEquiv j).symm
        (D.gridSigns_subdiagEquiv j) :=
  (gridSpace_subdiag (D := D) j).choose_spec.choose_spec

private def subdiagMap (D : Data P) (j : ℕ) :
    C(New.G D.E (D.gridSigns true 0 j (j + 1)), New.G D.E (D.gridSigns false 0 (j + 1) j)) where
  toFun := (G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j)).symm
  continuous_toFun := G.continuous_reindex _ (by simp [← D.gridSigns_subdiagEquiv j, comp_def])

private lemma reindex_subdiagMap (D : Data P) (j : ℕ)
    (x : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j) (D.subdiagMap j x) = x :=
  (G.reindex (D.subdiagEquiv j).symm (D.gridSigns_subdiagEquiv j)).apply_symm_apply x

private lemma height_subdiagMap (D : Data P) (j : ℕ)
    (x : New.G D.E (D.gridSigns true 0 j (j + 1))) :
    (D.gridSpace 0 false (j + 1) j).height (D.subdiagMap j x) =
      (D.gridSpace 0 true j (j + 1)).height x := by
  rw [D.gridSpace_subdiagEquiv j, ← Space.height_reindex _ (D.gridSigns_subdiagEquiv j),
    D.reindex_subdiagMap j]

private lemma gridChar_subdiag (D : Data P) (j : ℕ) (ϑ : D.MFoldTwist) (b' : Bool) (l : ℕ) :
    gridChar ϑ b' l (D.GridIndex true j (j + 1)) =
      gridChar ϑ b' l (D.GridIndex false (j + 1) j) := by
  simp only [gridChar, card_congr (D.subdiagEquiv j)]

private def diagWeight (D : Data P) (ϑ : D.MFoldTwist) {j : ℕ} (h : j ≤ D.m) :
    ModerateWeight (D.gridSpace 0 false j j) (D.gridSpace 0 true j j) where
  weightFn := 1
  comparisonMap := ⟨fun z ↦ .reindex (D.gridDiagEquiv j)
    (D.sumElim_gridSigns_comp_gridDiagEquiv_symm h)
    (.sum (z, 1, (gridModulus ϑ).flipScalar ^ j)), by fun_prop⟩
  isModerate := ⟨1, 0, by simp⟩
  height_le := ⟨_, fun _ ↦ gridSpace_diag h ▸ (height_reindex ..).trans_le (height_sum_le ..)⟩

private def diagLineWeight (D : Data P) (j : ℕ) (ϑ : D.MFoldTwist) (scale : ℂ)
    (Ψ : Matrix Unit (D.GridIndex false (j + 1) j) (gridModulus ϑ).ResidueRing → ℂ)
    (q : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ) :
    ModerateWeight (D.gridSpace 0 true j (j + 1)) (D.gridSpace 0 false (j + 1) j) where
  weightFn := ⟨fun x ↦ scale * modKernel (D.gridSpace 0 false (j + 1) j)
      (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
      (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1
      (gridModulus ϑ) Ψ q (D.subdiagMap j x) (1, (gridModulus ϑ).flipScalar ^ (j + 1)),
    by fun_prop [modKernel]⟩
  comparisonMap := D.subdiagMap j
  isModerate := by
    obtain ⟨C, M, hCM⟩ : (D.gridSpace 0 false (j + 1) j).IsModerate
        (fun x ↦ modKernel (D.gridSpace 0 false (j + 1) j)
          (signedSpace D.E fun _ : Unit ↦ (-1) ^ (j + 1))
          (gridChar ϑ true j (D.GridIndex false (j + 1) j)) WeilData.upsilonU1
          (gridModulus ϑ) Ψ q x (1, (gridModulus ϑ).flipScalar ^ (j + 1))) :=
      (pairThetaKer ..).isModerate ..
    exact ⟨‖scale‖ * C, M, fun x ↦ by
      simpa [height_subdiagMap, mul_assoc] using
        mul_le_mul_of_nonneg_left (hCM (D.subdiagMap j x)) (norm_nonneg scale)⟩
  height_le := ⟨1, by simp [height_subdiagMap]⟩

private lemma seesaw_row_line_diagonal (D : Data P) {j : ℕ} (hj : j < D.m)
    {Φ₀ : ∀ ϑ : D.MFoldTwist, D.GridDatum ϑ} {X₀ : D.MFoldTwist → Type}
    {W₀ : ∀ ϑ, Finset (X₀ ϑ)} {u₀ : ∀ ϑ, X₀ ϑ → ℂ} {s₀ : ∀ ϑ, X₀ ϑ → EdgeTuple ϑ}
    (hΦ₀_sum : ∀ ϑ f, Φ₀ ϑ f = ∑ i ∈ W₀ ϑ, u₀ ϑ i * f (s₀ ϑ i))
    {Ξ : D.PeriodTriple → ℂ} (hΞ : D.IsProportional hj Φ₀ Ξ)
    (q : MvPolynomial (D.Φ × Unit × D.GridIndex false (j + 1) j) ℂ)
    (r : GInf D.E (D.gridSigns false 0 (j + 1) j)) :
    ∃ β₀ : ℂ, ∀ x : D.PeriodTriple,
      Φ₀ x.1 (fun S ↦ periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
        (D.diagLineWeight j x.1 1 (Pi.single ((S (rowEdge true j (j + 1))).submatrix
          (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₂ 1) q) r
        (gridPathMap S true j (j + 1) x.2.2)
        (transposedMove ((S (rowEdge true j (j + 1))).submatrix
          (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₁
          (liftMove (S (rowEdge false j (j + 1))) (gridPathMap S false j (j + 1) x.2.1)))) =
        β₀ * Ξ x := by
  obtain ⟨t, ht⟩ := D.t_odd
  have hΞ' (g' : GInf D.E (D.gridSigns true 0 (j + 1) (j + 1))) :
      ∃ β₀ : ℂ, ∀ x : D.PeriodTriple,
        ∑ i ∈ W₀ x.1, u₀ x.1 i *
          periodPairing (isConjKernelPair_gridKernel ⟨hj, hj⟩) (D.diagWeight x.1 hj) g'
            (liftMove (s₀ x.1 i (rowEdge false j (j + 1)))
              (gridPathMap (s₀ x.1 i) false j (j + 1) x.2.1))
            (liftMove (s₀ x.1 i (rowEdge true j (j + 1)))
              (gridPathMap (s₀ x.1 i) true j (j + 1) x.2.2)) =
          β₀ * Ξ x :=
    (hΞ g').imp fun β₀ hβ₀ x ↦ by
      simpa only [gridPeriod, diagonalPeriodForm, diagWeight, gridPathMap, LinearMap.comp_apply,
        hΦ₀_sum x.1] using hβ₀ x
  dsimp only [liftMove] at hΞ'
  -- Second seesaw on the row-line period at `(j, j + 1) → (j + 1, j + 1)`.
  have h_seesaw := seesaw_periods D.PeriodTriple
    (S := D.gridSpace 0 true j (j + 1)) (T := D.gridSpace 0 true (j + 1) (j + 1))
    (T' := D.gridSpace 0 false (j + 1) j) (S' := D.gridSpace 0 false (j + 1) (j + 1))
    (𝔪 := fun x ↦ gridModulus x.1) (W := fun x ↦ W₀ x.1) (u := fun x ↦ u₀ x.1) (c := Ξ) (r := r)
    (y := fun x i ↦ gridPathMap (s₀ x.1 i) true j (j + 1) x.2.2)
    (f := fun x i ↦ liftMove (s₀ x.1 i (rowEdge false j (j + 1)))
      (gridPathMap (s₀ x.1 i) false j (j + 1) x.2.1))
    (N := fun x i ↦ D.diagLineWeight j x.1 1
      (Pi.single ((s₀ x.1 i (rowEdge true j (j + 1))).submatrix
        (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₂ 1) q)
    (Ψ' := fun x i ↦ Pi.single ((s₀ x.1 i (rowEdge true j (j + 1))).submatrix
      (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₁ 1)
    (isEdgeFamily_grid_succ_left (z := true) (i := j) (j := j + 1) Prod.fst hj hj)
    (isEdgeFamily_grid_succ_right (z := false) (i := j + 1) (j := j) Prod.fst hj hj)
    (by
      intro A' _
      refine subset_span ⟨renameRowsCols (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm
          (renameRowsCols .inl id A' * renameRowsCols .inr id q),
        fun x i ↦ Pi.single (s₀ x.1 i (rowEdge true j (j + 1))) 1, fun x _ ↦ D.diagWeight x.1 hj,
        hΞ', fun x i g₁ g₂ ↦ ?_⟩
      have h_char_succ : gridChar x.1 true j (D.GridIndex true (j + 1) (j + 1)) =
          gridChar x.1 true j (D.GridIndex false (j + 1) (j + 1)) * WeilData.upsilonU1 := by
        have h_rk : card (D.GridIndex true (j + 1) (j + 1)) / 2 =
            card (D.GridIndex false (j + 1) (j + 1)) / 2 + 1 := by
          simp only [card_gridIndex, ht, Bool.toNat_true, Bool.toNat_false]; grind
        simp [gridChar, h_rk, mul_assoc, pow_succ]
      have h_dat := single_one_eq_mul_of_coordinates (s₀ x.1 i (rowEdge true j (j + 1)))
        (fun Y ↦ (Y.submatrix (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₁)
        (fun Y ↦ (Y.submatrix (D.gridDiagEquiv (j + 1)) (D.subdiagEquiv j).symm).toRows₂)
        fun _ ↦ by
          simp only [← fromRows_ext_iff, fromRows_toRows]
          exact (Matrix.reindex (D.gridDiagEquiv (j + 1)).symm (D.subdiagEquiv j)).injective.eq_iff
      change (D.diagLineWeight j x.1 1 _ q).weightFn g₁ * _ = (1 : ℂ) * _
      simp only [diagLineWeight, diagWeight, one_mul, ContinuousMap.coe_mk, Bool.not_false]
      rw [mul_comm, ← modKernel_sum_right, ← modKernel_reindex (D.subdiagEquiv j).symm
        (D.gridSigns_subdiagEquiv j) (D.gridDiagEquiv (j + 1))
        (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj),
        D.reindex_subdiagMap j, h_char_succ, D.gridChar_subdiag j, h_dat, gridSpace_diag hj,
        D.gridSpace_subdiagEquiv j])
  exact h_seesaw.imp fun β₀ hβ₀ x ↦ by
    rw [hΦ₀_sum x.1]; dsimp only [transposedMove] at hβ₀ ⊢; exact hβ₀ x

/-- Climbing one stage along the diagonal (`j → j + 1`) for `j < m`: push the descent past `j`
lifts in each grid, then cross the diagonal square `(j, j)` via two seesaws and line reversal. The
order increases by `4 * j + 2`, and the twist factor has modulus up to a norm power equal to the
product of `turnRatio` over the L-shaped shell of squares at index `j`. -/
lemma hasRoute_succ (D : Data P) {j : ℕ} (hj : j < D.m) :
    ∃ c : D.MFoldTwist → ℂˣ,
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        ((∏ i ∈ range j, D.turnRatio i j) * (∏ i ∈ range j, D.turnRatio j i) *
          D.turnRatio j j) ∧
      D.HasRoute hj.le hj (4 * j + 2) c := by
  obtain ⟨t, ht⟩ := D.t_odd
  obtain ⟨κ₀, σ, c₃, hc₃, h_law⟩ := exists_squareLaw_grid_hasAbsUpToNormPower (D := D) false hj hj
  obtain ⟨κ₁, c₁, hc₁, h_desc₁⟩ := descent_past_gridPathMap (D := D) hj false le_rfl
  obtain ⟨κ₂, c₂, hc₂, h_desc₂⟩ := descent_past_gridPathMap (D := D) hj true le_rfl
  let N := D.GridIndex false (j + 1) j
  let τ := flipPoly (E := D.E) (fun _ : Unit ↦ (-1) ^ (j + 1)) (D.gridSigns false 0 (j + 1) j)
  have h_flip_all (ϑ : D.MFoldTwist) := by
    have h := exists_modKernel_flip_line (D.gridSpace 0 false (j + 1) j) ((-1) ^ (j + 1))
      (gridModulus ϑ) (gridChar ϑ false j N) (gridChar ϑ true j N) ((gridModulus ϑ).flipScalar ^ j)
    rwa [← show (-1 : ℤˣ) ^ j = -(-1) ^ (j + 1) by simp [pow_succ],
      ← pow_succ ((gridModulus ϑ).flipScalar Unit)] at h
  choose ψ c_line hc_line_norm h_flip using h_flip_all
  let c_tot : D.MFoldTwist → ℂˣ := c₁ * c₂ * c₃ * c_line⁻¹
  have hc_tot : D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ (c_tot ϑ : ℂ))
      ((∏ i ∈ range j, D.turnRatio i j) * (∏ i ∈ range j, D.turnRatio j i) * D.turnRatio j j) := by
    rw [show (fun ϑ : D.MFoldTwist ↦ (c_tot ϑ : ℂ)) =
          ((((fun ϑ ↦ (c₁ ϑ : ℂ)) * fun ϑ ↦ (c₂ ϑ : ℂ)) * fun ϑ ↦ (c₃ ϑ : ℂ)) *
            fun ϑ ↦ (c_line ϑ : ℂ)⁻¹) from
        funext fun _ ↦ by simp [c_tot, Units.val_mul, Units.val_inv_eq_inv_val],
      ← mul_one (_ * _ * D.turnRatio j j)]
    exact (((show D.HasAbsUpToNormPower (fun ϑ ↦ (c₁ ϑ : ℂ)) _ by simpa using hc₁).mul
      (by simpa using hc₂)).mul (by simpa using hc₃)).mul
      (.of_norm_sq_eq_mul_card_zpow _ 1 (card N) (by simpa [field, eq_comm] using hc_line_norm))
  refine ⟨c_tot, hc_tot, fun n Λ hΛ ↦ ?_⟩
  -- Push the descents past `j` lifts in both grids, then cross the diagonal square `(j, j)`.
  choose Φ₁ hΦ₁ h_eq₁ using fun ϑ ↦ h_desc₁ ϑ n (D.gridPath true j j) (Λ ϑ)
    (fun e he ↦ .inl <| by
      simp only [gridPath, legEdges, mem_union, mem_image] at he
      rcases he with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp)
    (by simpa [stageEdges, union_comm] using hΛ ϑ)
  let w₁ : Finset (GridNode × GridNode) :=
    insert (columnEdge false j j) (D.gridPath false j (j + 1))
  choose Φ₂ hΦ₂ h_eq₂ using fun ϑ ↦ h_desc₂ ϑ (n + 2 * j) w₁ (Φ₁ ϑ)
    (fun e he ↦ .inl <| by
      simp only [w₁, gridPath, legEdges, mem_insert, mem_union, mem_image] at he
      rcases he with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp)
    (hΦ₁ ϑ)
  let w₀ : Finset (GridNode × GridNode) := D.gridPath false j (j + 1) ∪ D.gridPath true j (j + 1)
  have h_old_diag : insert (columnEdge false j j) (insert (columnEdge true j j) w₀) =
      insert (columnEdge true j j) (D.gridPath true j (j + 1)) ∪ w₁ := by
    ext e; simp [w₀, w₁]; tauto
  have h_new_diag : insert (rowEdge true j (j + 1)) (insert (rowEdge false j (j + 1)) w₀) =
      D.stageEdges (j + 1) := by ext e; simp [w₀, stageEdges, gridPath, range_add_one]
  choose Φ₀ hΦ₀ h_eq₀ using fun ϑ : D.MFoldTwist ↦
    (show D.IsPathDatum _ (insert (columnEdge false j j) (insert (columnEdge true j j) w₀))
        (Φ₂ ϑ) by rw [h_old_diag]; exact hΦ₂ ϑ).exists_square_move
      (J := D.GridForm false j (j + 1) × (D.GridForm false (j + 1) j →ₗ[ℂ] ℂ))
      (R := (true, j + 1, j + 1)) (r := (false, j + 1, j + 1))
      (D.subdiagEquiv j).symm (D.gridDiagEquiv j) (D.gridDiagEquiv (j + 1)) (ψ ϑ)
      (fun i ↦ h_law ϑ i.1 i.2)
      (fun g hg ↦ ⟨hg.2 (j + 1), fun k ↦ ⟨⟨fun z ↦ by
          rw [update_of_ne (by grind), update_of_ne (by grind)]; exact hg.1 z,
        fun a ↦ by obtain rfl | ha := eq_or_ne a j <;> [simp; simpa [ha] using hg.2 a]⟩, by simp⟩⟩)
      (by simp) (by simp [IsVerticalEdge])
      (by intro q hq; rcases (by simpa using hq) with rfl | rfl | rfl | rfl <;>
            simp [Prod.le_def] <;> omega)
      (by intro e he
          simp only [w₀, gridPath, legEdges, mem_union, mem_image, mem_range, mem_Ico] at he
          rcases he with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;>
            simp <;> grind)
      (by simp [edgeChar, IsVerticalEdge])
  have hΦ₀' (ϑ : D.MFoldTwist) :
      D.IsPathDatum (n + (4 * j + 2)) (D.stageEdges (j + 1)) (Φ₀ ϑ) := by
    rw [h_new_diag, show n + 2 * j + 2 * j + 2 = n + (4 * j + 2) by omega] at hΦ₀; exact hΦ₀ ϑ
  refine ⟨Φ₀, hΦ₀', fun Ξ hΞ g ↦ ?_⟩
  choose X₂ W₂ u₂ s₂ _ _ hΦ₂_sum using fun ϑ ↦ (hΦ₂ ϑ).isShortSum
  choose X₀ W₀ u₀ s₀ _ _ hΦ₀_sum using fun ϑ ↦ (hΦ₀' ϑ).isShortSum
  -- Pull the finite Fourier sum on the added line outside `periodPairing`.
  have h_fourier_pair (ϑ : D.MFoldTwist) (scale : ℂ) (v : Matrix N Unit (gridModulus ϑ).ResidueRing)
      (q : MvPolynomial (D.Φ × Unit × N) ℂ) (r : GInf D.E (D.gridSigns false 0 (j + 1) j))
      (F : D.GridForm true j (j + 1)) (y : D.GridForm false (j + 1) j) :
      periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
          (D.diagLineWeight j ϑ scale (matrixFourier (ψ ϑ) (Pi.single v 1)) q) r F y =
        scale * ∑ k, ψ ϑ (k * v).trace * periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
          (D.diagLineWeight j ϑ 1 (Pi.single k 1) q) r F y := by
    have h_wt (x) :
        (D.diagLineWeight j ϑ scale (matrixFourier (ψ ϑ) (Pi.single v 1)) q).weightFn x =
          scale * ∑ k, ψ ϑ (k * v).trace *
            (D.diagLineWeight j ϑ 1 (Pi.single k 1) q).weightFn x := by
      simp [diagLineWeight, modKernel, pairTheta, modDatum_eq_sum _ _ (matrixFourier _ _),
        matrixFourier, Pi.single_apply, Finset.mul_sum]
    have h_cmp (s' : ℂ) (Ψ' : Matrix Unit N (gridModulus ϑ).ResidueRing → ℂ) :
        (D.diagLineWeight j ϑ s' Ψ' q).comparisonMap = D.subdiagMap j := rfl
    simp only [periodPairing, LinearMap.mk₂_apply, h_wt, h_cmp, sum_mul, mul_assoc,
      integral_const_mul]
    exact congrArg (scale * ·) <| by
      simpa [h_cmp, integral_const_mul, mul_assoc] using
        integral_finsetSum (μ := (D.gridSpace 0 true j (j + 1)).quotMeasure) univ fun k _ ↦
          (integrable_moderate_mul_forms (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
            (D.diagLineWeight j ϑ 1 (Pi.single k 1) q) F y).const_mul (ψ ϑ (k * v).trace)
  -- First seesaw across the diagonal square `(j, j)`, splitting the polynomial on the added line.
  have h_seesaw := seesaw_periods D.PeriodTriple
    (S := D.gridSpace 0 false j j) (T := D.gridSpace 0 false (j + 1) j)
    (T' := D.gridSpace 0 true j j) (S' := D.gridSpace 0 true j (j + 1))
    (𝔪 := fun x ↦ gridModulus x.1) (W := fun x ↦ W₂ x.1) (u := fun x ↦ u₂ x.1)
    (c := fun x ↦ Ξ x / (c₃ / c_line) x.1) (r := g)
    (y := fun x i ↦ transposedMove (s₂ x.1 i (columnEdge false j j))
      (gridPathMap (s₂ x.1 i) false j (j + 1) x.2.1))
    (f := fun x i ↦ gridPathMap (s₂ x.1 i) true j (j + 1) x.2.2)
    (N := fun x _ ↦ D.diagWeight x.1 hj.le)
    (Ψ' := fun x i ↦ Pi.single (s₂ x.1 i (columnEdge true j j)) 1)
    (isEdgeFamily_grid_succ_left (z := false) (i := j) (j := j) Prod.fst hj hj.le)
    (isEdgeFamily_grid_succ_right (z := true) (i := j) (j := j) Prod.fst hj.le hj)
    (by
      intro P _
      have h_cover : ∀ i : D.Φ × D.GridIndex true j (j + 1) × D.GridIndex true j j,
          i ∈ Set.range (Prod.map id (Prod.map (D.subdiagEquiv j).symm
                (D.gridDiagEquiv j ∘ .inl))) ∪
              Set.range (Prod.map id (Prod.map (D.subdiagEquiv j).symm
                (D.gridDiagEquiv j ∘ .inr))) := by
        simp [reindex_equiv (D.gridDiagEquiv j)]
      refine mul_le.2 ?_ (mem_rename_range_mul _ _ h_cover P)
      rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
      refine subset_span ⟨A,
        fun x i ↦ Pi.single ((s₂ x.1 i (columnEdge true j j)).submatrix (D.subdiagEquiv j).symm
          (D.gridDiagEquiv j)).toCols₁ 1,
        fun x i ↦ D.diagLineWeight j x.1 (c_line x.1) (matrixFourier (ψ x.1) (Pi.single
          ((s₂ x.1 i (columnEdge true j j)).submatrix (D.subdiagEquiv j).symm
            (D.gridDiagEquiv j)).toCols₂ 1)) (τ B),
        fun r ↦ ?_, fun x i g₁ g₂ ↦ ?_⟩
      · obtain ⟨β₀, hβ₀⟩ := D.seesaw_row_line_diagonal hj hΦ₀_sum hΞ (τ B) r
        refine ⟨κ₀ * β₀, fun x ↦ ?_⟩
        dsimp only
        have h_move := h_eq₀ x.1
          (fun S k ↦ (gridPathMap S false j (j + 1) x.2.1,
            periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
              (D.diagLineWeight j x.1 1 (Pi.single k 1) (τ B)) r
              (gridPathMap S true j (j + 1) x.2.2)))
          fun S S' h_eq ↦ funext fun _ ↦ by
            dsimp only
            rw [gridPathMap_congr (z := false) fun e he ↦ h_eq e (by simp [w₀, he]),
              gridPathMap_congr (z := true) fun e he ↦ h_eq e (by simp [w₀, he])]
        simp only [toRows₁_fromRows, toRows₂_fromRows, toCols₁_fromCols,
          toCols₂_fromCols] at h_move
        have h_goal :
            Φ₂ x.1 (fun S ↦ periodPairing (isConjKernelPair_gridKernel ⟨hj.le, hj⟩)
              (D.diagLineWeight j x.1 (c_line x.1) (matrixFourier (ψ x.1)
                (Pi.single ((S (columnEdge true j j)).submatrix
                  (D.subdiagEquiv j).symm (D.gridDiagEquiv j)).toCols₂ 1)) (τ B)) r
              (gridPathMap S true j (j + 1) x.2.2)
              (liftMove ((S (columnEdge true j j)).submatrix (D.subdiagEquiv j).symm
                (D.gridDiagEquiv j)).toCols₁
                (transposedMove (S (columnEdge false j j))
                  (gridPathMap S false j (j + 1) x.2.1)))) =
            κ₀ * β₀ * (Ξ x / (c₃ / c_line) x.1) := by
          simp_rw [h_fourier_pair, ← smul_eq_mul (c_line x.1 : ℂ)]
          rw [← Pi.smul_def, map_smul, smul_eq_mul, h_move, hβ₀ x]
          simp only [Pi.div_apply, Units.val_div_eq_div_val]
          field_simp [(c_line x.1).ne_zero, (c₃ x.1).ne_zero]
        rw [hΦ₂_sum x.1] at h_goal
        dsimp only [liftMove] at h_goal
        exact h_goal
      · have h_char_j : gridChar x.1 false j (D.GridIndex true j j) =
            gridChar x.1 false j (D.GridIndex false j j) * 1 := by
          have h_rk : (card (D.GridIndex true j j) + 1) / 2 =
              (card (D.GridIndex false j j) + 1) / 2 := by
            simp only [card_gridIndex, ht, Bool.toNat_true, Bool.toNat_false]; grind
          simp [gridChar, h_rk]
        have h_dat := single_one_eq_mul_of_coordinates (s₂ x.1 i (columnEdge true j j))
          (fun Y ↦ (Y.submatrix (D.subdiagEquiv j).symm (D.gridDiagEquiv j)).toCols₁)
          (fun Y ↦ (Y.submatrix (D.subdiagEquiv j).symm (D.gridDiagEquiv j)).toCols₂) fun _ ↦ by
            simp only [← fromCols_ext_iff, fromCols_toCols]
            exact (Matrix.reindex (D.subdiagEquiv j) (D.gridDiagEquiv j).symm).injective.eq_iff
        have h_poly :
            (MvPolynomial.rename (Prod.map id (Prod.map (D.subdiagEquiv j).symm
              (D.gridDiagEquiv j ∘ .inl)))).toRingHom A *
              (MvPolynomial.rename (Prod.map id (Prod.map (D.subdiagEquiv j).symm
                (D.gridDiagEquiv j ∘ .inr)))).toRingHom B =
            renameRowsCols (D.subdiagEquiv j).symm (D.gridDiagEquiv j)
              (renameRowsCols id .inl A * renameRowsCols id .inr B) := by
          simp [renameRowsCols, Prod.map_comp_map]
        change (1 : ℂ) * _ = (D.diagLineWeight j x.1 _ _ _).weightFn g₂ * _
        simp only [diagLineWeight, diagWeight, one_mul, ContinuousMap.coe_mk, Bool.not_true]
        rw [← h_flip x.1 B _ (D.subdiagMap j g₂), eq_comm, mul_comm, ← modKernel_sum_left,
          ← modKernel_reindex (D.gridDiagEquiv j)
            (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj.le) (D.subdiagEquiv j).symm
            (D.gridSigns_subdiagEquiv j),
          D.reindex_subdiagMap j, h_char_j, D.gridChar_subdiag j, h_dat, h_poly,
          gridSpace_diag hj.le, D.gridSpace_subdiagEquiv j])
  -- Combine the two interior row-descent transfers with the diagonal seesaw proportionality.
  obtain ⟨β, hβ⟩ := h_seesaw
  refine ⟨κ₁ * κ₂ * β, fun x ↦ ?_⟩
  have h₁ := h_eq₁ x.1 x.2.1
    (fun S ↦ (diagonalPeriodForm x.1 hj.le g).flip (gridPathMap S true j j x.2.2))
    fun S S' h_eq ↦ by dsimp only; rw [gridPathMap_congr h_eq]
  simp only [LinearMap.flip_apply] at h₁
  have h₂ := h_eq₂ x.1 x.2.2
    (fun S ↦ diagonalPeriodForm x.1 hj.le g
      (transposedMove (S (columnEdge false j j)) (gridPathMap S false j (j + 1) x.2.1)))
    fun S S' h_eq ↦ by
      dsimp only
      rw [h_eq (columnEdge false j j) (by simp [w₁]),
        gridPathMap_congr fun e he ↦ h_eq e (by simp [w₁, he])]
  have hβ' : Φ₂ x.1 (fun S ↦ diagonalPeriodForm x.1 hj.le g
      (transposedMove (S (columnEdge false j j)) (gridPathMap S false j (j + 1) x.2.1))
      (transposedMove (S (columnEdge true j j)) (gridPathMap S true j (j + 1) x.2.2))) =
      β * (Ξ x / (c₃ / c_line) x.1) := by
    rw [hΦ₂_sum x.1]
    dsimp only [diagonalPeriodForm, diagWeight, transposedMove] at hβ ⊢
    exact hβ x
  calc D.gridPeriod hj.le Λ g x
    _ = κ₁ / c₁ x.1 * _ := h₁
    _ = κ₁ / c₁ x.1 * (κ₂ / c₂ x.1 * _) := by rw [h₂]
    _ = κ₁ * κ₂ * β * (Ξ x / c_tot x.1) := by
        rw [hβ']
        simp [c_tot, Pi.mul_apply, Units.val_mul, Units.val_div_eq_div_val, field]

/-- Composing the diagonal climbs from stage `0` to stage `j ≤ m`: there are nonzero factors `c ϑ`
whose modulus up to a norm power is `∏ i ∈ range j, ∏ k ∈ range j, D.turnRatio i k` giving a route
of order cost `2 * j ^ 2` from `stageEdges 0` to `stageEdges j`. -/
lemma exists_hasRoute_zero_stage (D : Data P) {j : ℕ} (hj : j ≤ D.m) :
    ∃ c : D.MFoldTwist → ℂˣ,
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (∏ i ∈ range j, ∏ k ∈ range j, D.turnRatio i k) ∧
      D.HasRoute zero_le hj (2 * j ^ 2) c := by
  induction j with
  | zero =>
    refine ⟨1, by simpa [Pi.one_def] using HasAbsUpToNormPower.one,
      fun n Λ hΛ ↦ ⟨Λ, by simpa using hΛ, fun Ξ hΞ g ↦ by simpa using hΞ g⟩⟩
  | succ j ih =>
    obtain ⟨c_prev, hc_prev, h_prev⟩ := ih (Nat.le_of_succ_le hj)
    obtain ⟨c_step, hc_step, h_step⟩ := D.hasRoute_succ hj
    refine ⟨c_prev * c_step, ?_, fun n Λ hΛ ↦ ?_⟩
    · rw [show (fun ϑ : D.MFoldTwist ↦ ((c_prev * c_step) ϑ : ℂ)) =
          (fun ϑ ↦ (c_prev ϑ : ℂ)) * fun ϑ ↦ (c_step ϑ : ℂ) from funext fun _ ↦ Units.val_mul ..,
        ← show (∏ i ∈ range j, ∏ k ∈ range j, D.turnRatio i k) *
            ((∏ i ∈ range j, D.turnRatio i j) * (∏ i ∈ range j, D.turnRatio j i) *
              D.turnRatio j j) =
          ∏ i ∈ range (j + 1), ∏ k ∈ range (j + 1), D.turnRatio i k from funext fun _ ↦ by
            simp only [Pi.mul_apply, Finset.prod_apply, prod_range_succ, prod_mul_distrib]; ring]
      exact hc_prev.mul hc_step
    · obtain ⟨Φ₁, hΦ₁, h_back₁⟩ := h_prev n Λ hΛ
      obtain ⟨Φ₂, hΦ₂, h_back₂⟩ := h_step (n + 2 * j ^ 2) Φ₁ hΦ₁
      refine ⟨Φ₂, (show n + 2 * j ^ 2 + (4 * j + 2) = n + 2 * (j + 1) ^ 2 by ring) ▸ hΦ₂,
        fun Ξ hΞ ↦ ?_⟩
      simpa only [Pi.mul_apply, Units.val_mul, div_div, mul_comm] using h_back₁ _ (h_back₂ Ξ hΞ)

/-- There are nonzero factors `c ϑ` whose modulus up to a norm power is the product of
`D.turnRatio i j` over all `i, j < m`, giving a route of order cost `2 * m ^ 2` from the first path
(`stageEdges 0`) to the last (`stageEdges m`). -/
theorem exists_hasRoute_zero_last (D : Data P) :
    ∃ c : D.MFoldTwist → ℂˣ,
      D.HasAbsUpToNormPower (fun ϑ : D.MFoldTwist ↦ c ϑ)
        (∏ i ∈ range D.m, ∏ j ∈ range D.m, D.turnRatio i j) ∧
      D.HasRoute zero_le le_rfl (2 * D.m ^ 2) c :=
  D.exists_hasRoute_zero_stage le_rfl

end RowLadder

end New.Data

end
