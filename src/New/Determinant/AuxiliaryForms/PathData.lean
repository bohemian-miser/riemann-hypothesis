module

import Mathlib.Data.Rat.Cast.OfScientific
import Std.Tactic.BVDecide.Normalize.Bool
public import Lib.Weil.DualPair.Flip
public import New.Determinant.Chain.SquareLaw
public import Lib.ClassField.HeckeCharacter.TameModulus
public import Lib.Weil.Seesaw
public import New.UpperBound.Objects.Rows
public import Lib.Adelic.Unitary.RationalPoints -- shake: keep (needed public by an exposed definition)
import New.OneLift.ComparisonOperator.ExchangeData

/-!
# Moduli, spaces, moves, monadic grid data and periods on the two grids

This file sets up the two grids of hermitian spaces attached to admissible data `D` and an `m`-fold
twist `ϑ`, together with the linear integration functionals that carry periods from the first path
to the last. A node is a triple `(z, a, b)`: the space `Y^a_b` for `z = false` and `Ỹ^b_a` for
`z = true`. The element `ϖ = π_M = New.Data.piM`, of norm `M`, generates the product of the chosen
places, and `Q` is the product of the places of `ϑ`.

Rather than encoding path weights as pointwise functions `EdgeTuple ϑ → ℂ` summed over
finite-support slices, we represent a path datum directly as its **linear integration functional**
`GridDatum ϑ := (EdgeTuple ϑ → ℂ) →ₗ[ℂ] ℂ`. Extending a datum along an edge, symmetrizing over
cosets of node levels, and turning a corner across a grid square (whether in the interior or on the
diagonal) are all instances of a single monadic operation `GridDatum.bind`, which composes a datum
with a finite root-of-unity-weighted family of edge-tuple updates. Likewise, paths need only follow
L-shaped routes `gridPath z a b` that descend down the first column from `(0, m)` to `(0, b)` and
then lift along row `b` to `(a, b)`.

## Main definitions and results

* `New.Data.gridModulus`: the modulus `𝔪 = 𝔟 Q` with `𝔟 = ϖ ^ D.natB`. For the twist `1` it is `𝔟`
  (`New.Data.gridModulus_one_ideal`).
* `New.Data.liftMove`, `New.Data.transposedMove`: the theta lift `(a, b) → (a + 1, b)` and the
  transposed lift `(a, b + 1) → (a, b)` with a single matrix as finite datum.
* `New.Data.GridDatum`, `New.Data.GridDatum.bind`, `New.Data.IsShortSum`, `New.Data.IsPathDatum`:
  linear functionals on functions of edge tuples, their monadic composition, short root-of-unity
  combinations supported on left-invertible vertical edges (`New.Data.IsShortSum.bind`), and
  equivariant path data.
* `New.Data.legDescents`, `New.Data.gridPathMap`, `New.Data.stageEdges`: L-shaped paths through the
  two grids and the composite maps on forms along them.
* `New.Data.gridPeriod`, `New.Data.IsProportional`: the diagonal period at stage `j` and the
  proportionality relation `Λ ∝ Ξ`.

Notions from other files:
* `New.Modulus`: a nonzero ideal of `O_E` prime to its complex conjugate.
* `New.Data.MFoldTwist`: a twist `ϑ` whose tame part has `ψ_wⁿ` non-trivial for all `w` in `Q` and
  `1 ≤ n ≤ m`.
* `New.Data.GridIndex`, `New.Data.gridSigns`, `New.Data.gridParam`: the index set of a basis, the
  signs of the hermitian form and twice the parameter of the type at a node with an offset `o`; the
  grids have `o = 0`.
* `New.Exchange.IsEdgeFamily`: a family of characters over two pairs of conjugate cuspidal types
  which, with a polynomial, form an edge for the real Weil representation.
-/

@[expose] public section

noncomputable section

namespace New.Data

/-!
## The moduli and levels of the grids

* `New.Data.triangleModulus`: the modulus of the transposed lifts between the nodes `(0, b)`, whose
  datum is the indicator of an inclusion matrix: `𝔪₀ = ϖ Q` in grid `Y` and `𝔟 = ϖ ^ D.natB` in
  grid `Ỹ`. It divides the grid modulus (`New.Data.gridModulus_ideal_le_triangleModulus_ideal`).
-/

section GridModuli

open Ideal Quotient

variable {P : Parameters} {D : Data P} (ϑ : D.MFoldTwist)

/-- `D.natB` is nonzero. -/
instance instNeZeroNatB : NeZero D.natB := .of_pos D.nat_le_of_hasLogBound

/-- The element `ϖ ^ D.natB` of the ring of integers of `E`, with `ϖ = D.piM` the generator of
the product of the chosen places. -/
abbrev gridLevelGen : NumberField.RingOfIntegers D.E := D.piM ^ D.natB

/-- The modulus `ϖ^{natB} Q` of the twist `ϑ`: the product of the chosen places to the power
`D.natB`, times the product of the places of `ϑ`. -/
abbrev gridModulus : Modulus D.E := D.twistModulus ϑ D.natB

lemma gridModulus_one_ideal : (D.gridModulus 1).ideal = span {D.gridLevelGen} := by
  -- the trivial twist has no places, so its modulus is the untwisted one
  rw [show (D.gridModulus 1).ideal = (D.untwistedModulus D.natB).ideal by rfl',
    D.ideal_untwistedModulus_eq_span]

/-- The twist whose places divide `New.Data.triangleModulus`: `ϑ` in the grid `false`, the trivial
twist in the grid `true`. -/
abbrev triangleTwist (ϑ : D.MFoldTwist) : Bool → D.MFoldTwist
  | false => ϑ
  | true => 1

variable (D) in
/-- The exponent of the chosen places in `New.Data.triangleModulus`: `1` in the grid `false`,
`D.natB` in the grid `true`. -/
abbrev triangleExponent : Bool → ℕ
  | false => 1
  | true => D.natB

/-- The exponent `D.triangleExponent z` is nonzero in both grids. -/
instance instNeZeroTriangleExponent (z : Bool) : NeZero (D.triangleExponent z) := by
  cases z <;> infer_instance

/-- The modulus at the nodes `(0, b)` of grid `z` (the triangle of that grid), used for the
transposed lifts `New.Data.pointTransposedLift` between them: `𝔪₀ = ϖ Q`, with `Q` the product of
the places of `ϑ`, if `z` is false, and `𝔟 = ϖ ^ D.natB` if `z` is true. Here `ϖ = D.piM`. -/
abbrev triangleModulus (z : Bool) (ϑ : D.MFoldTwist) : Modulus D.E :=
  D.twistModulus (triangleTwist ϑ z) (D.triangleExponent z)

/-- Let `ϑ` be an `m`-fold twist, `Q` the product of its places, `ϖ = D.piM` the generator of the
product of the chosen places, and `b = D.natB ≥ 1`. The triangle modulus of grid `z`, which is
`ϖ Q` for `z = false` (grid `Y`) and `ϖ ^ b` for `z = true` (grid `Ỹ`), divides the grid modulus
`ϖ ^ b Q`; this is stated as an inclusion of ideals. -/
lemma gridModulus_ideal_le_triangleModulus_ideal (ϑ : D.MFoldTwist) (z : Bool) :
    (gridModulus ϑ).ideal ≤ (triangleModulus z ϑ).ideal := by
  let M : Ideal (NumberField.RingOfIntegers D.E) :=
    ∏ i : (k : Fin 2) × D.ChosenPlace k, (D.chosenPlace i).asIdeal
  let Q : Ideal (NumberField.RingOfIntegers D.E) := ∏ w : ϑ.Q, w.val.asIdeal
  cases z with
  | false =>
    change M ^ D.natB * Q ≤ M ^ 1 * Q
    exact mul_mono_left (pow_le_pow_right NeZero.one_le)
  | true =>
    -- the trivial twist has no places, so its factor is the empty product `1`
    change M ^ D.natB * Q ≤ M ^ D.natB * 1
    rw [mul_one]
    exact Ideal.mul_le_left

/-- Reduction from the residue ring of `New.Data.gridModulus` = ϖ^b Q to that of
`New.Data.triangleModulus`, which is ϖQ for z false and ϖ^b for z true, with b = `D.natB`. -/
abbrev reduceToTriangle (z : Bool) :
    NumberField.RingOfIntegers D.E ⧸ (gridModulus ϑ).ideal →+*
      NumberField.RingOfIntegers D.E ⧸ (triangleModulus z ϑ).ideal :=
  factor (gridModulus_ideal_le_triangleModulus_ideal ϑ z)

lemma piM_dvd_gridLevelGen : D.piM ∣ D.gridLevelGen := dvd_pow_self _ (NeZero.ne _)

end GridModuli

/-!
## Spaces, characters, levels and moves of the two grids

The node `(false, a, b)` is `Y^a_b`, the node `(true, a, b)` is `Ỹ^b_a`, and `Y^0_j` is the space
`Y_j`. Throughout, `ϖ` generates the product of the chosen places, `𝔟 = ϖ ^ D.natB`, and `Q` is the
product of the places of the twist `ϑ`.
-/

section GridDefs

open Matrix Fintype Exchange Space

variable {P : Parameters} {D : Data P} (ϑ : D.MFoldTwist) {z : Bool} {i j a b : ℕ} (c : Bool)
  (l : ℕ) (n : Type) [Fintype n]

/-! ### Spaces, types, characters and levels -/

/-- The hermitian spaces at the nodes `(z, i, j)` with offset `o`: the triangles are `i = 0` and the
grids `o = 0`. For `o = 0` they are `Y_j` along the first column of grid `Y` and `Y₀` plus a line
at the corner of grid `Ỹ`. At `i = j = 0` offset `o` multiplies the space by `(-1) ^ o`. All other
spaces are orthogonal sums of lines with the signs `gridSigns`. -/
def gridSpace : ∀ (o : ℕ) (z : Bool) (i j : ℕ), Space D.E (D.GridIndex z i j) (D.gridSigns z o i j)
  | 0, true, 0, 0 =>
    ((D.spaceY 0).sum (signedSpace D.E 1)).reindex (Equiv.refl (D.Y 0 ⊕ Unit))
      D.gridSigns_true_zero.symm
  | 0, false, 0, j => D.spaceY j
  | o + 1, z, 0, 0 => (gridSpace o z 0 0).neg
  | o, z, i, j => signedSpace D.E (D.gridSigns z o i j)

/-- The pair of kernels of the types at a node: at `false` that of the parameter `gridParam` and at
`true` that of its negative. -/
def gridKernel (z : Bool) (i j : ℕ) : Bool → GInf D.E (D.gridSigns z 0 i j) → ℂ :=
  kernelPair (D.gridParam z 0 i j) (D.gridSigns z 0 i j)

/-- The forms of the kernel `gridKernel` at `true` at a node, that is of the parameter `-gridParam`:
conjugate forms in grid `Y`, and forms in grid `Ỹ`, whose `gridParam` carries the opposite sign. -/
abbrev GridForm (z : Bool) (a b : ℕ) : Type := (D.gridSpace 0 z a b).Form (D.gridKernel z a b true)

/-- The character of U(1)(𝔸) of an edge of index `l` at an end of index type `n`. Write
`μ = D.untwistedLiftChar (l + 1)`, so that `D.liftChar ξ (l + 1) = μ ξ` for a tame character `ξ`,
and `υ = WeilData.upsilonU1` for the splitting character restricted to the norm-one ideles. For a
vertical edge (`c = true`) the character is `μ ϑ ^ (l + 1) υ ^ ⌊card n / 2⌋`. For a horizontal edge
(`c = false`) it is `μ υ ^ ⌈card n / 2⌉`, without twist. -/
def gridChar : AutChar D.E :=
  D.liftChar (bif c then ϑ.pow (l + 1) else TameChar.one) (l + 1) *
    WeilData.upsilonU1 ^ ((card n + (!c).toNat) / 2)

/-- The tame part of `gridChar`: that of `liftChar` with the twist `ϑ ^ (l + 1)` if `c`, and with
the trivial twist otherwise. -/
abbrev gridTamePart : ∀ w : New.FinPlace D.E, MulChar (ResField w) ℂ :=
  D.liftTamePart (bif c then ϑ.pow (l + 1) else .one) (l + 1)

/-- The order of the general linear group of the node `(0, n)` modulo `triangleModulus z ϑ`. -/
abbrev triangleGLCard (z : Bool) (ϑ : D.MFoldTwist) (n : ℕ) : ℕ :=
  card (GL (D.GridIndex z 0 n) (D.triangleModulus z ϑ).ResidueRing)

/-- The nodes of the two grids: `(false, i, j)` is the space `Y^i_j` of grid `Y`, and
`(true, i, j)` is the space `Ỹ^j_i` of grid `Ỹ`. -/
abbrev GridNode : Type := Bool × ℕ × ℕ

/-- The index set of a node. -/
abbrev NodeIndex (p : GridNode) : Type := D.GridIndex p.1 p.2.1 p.2.2

/-- The level at node p, a subgroup of GL over the residue ring of 𝔪 = 𝔟Q: trivial at the nodes
(false, 0, b), that is at Y_b = Y^{0}_{b}, and the kernel of reduction modulo 𝔟 elsewhere. -/
def nodeLevel (p : GridNode) :
    Subgroup (GL (NodeIndex (P := P) (D := D) p)
      (NumberField.RingOfIntegers D.E ⧸ (gridModulus ϑ).ideal)) :=
  if !p.1 ∧ p.2.1 = 0 then
    ⊥
  else
    (GeneralLinearGroup.map (n := D.NodeIndex p) (reduceToTriangle ϑ true)).ker

/-- The index of the level `New.Data.nodeLevel` at node (a, b) of grid z in the general linear
group, as a complex number. -/
abbrev levelIndex (z : Bool) (a b : ℕ) : ℂ := ((nodeLevel ϑ (z, a, b)).index : ℂ)

/-- The forms of level `𝔟`, the principal level of `New.Data.gridLevelGen`, at the node
`(true, 0, i)`, the space `Ỹ^i_0`. For `i = m` these are the forms at the start of every path. -/
abbrev gridLevelForms (i : ℕ) :
    Submodule ℂ (Form (E := D.E) (gridSpace 0 true 0 i) (gridKernel true 0 i true)) :=
  levelSpace ((D.gridSpace 0 true 0 i).formRep (D.gridKernel true 0 i true))
    (principalLevel (D.GridIndex true 0 i) D.gridLevelGen)

/-! ### Edges and identifications of spaces -/

/-- At a node with i, j ≤ m the two types with kernels `New.Data.gridKernel` are cuspidal and
complex conjugates of each other. -/
lemma isConjKernelPair_gridKernel (h_le : i ≤ D.m ∧ j ≤ D.m) :
    IsConjKernelPair (D.gridKernel z i j) := by
  refine isConjKernelPair_kernelPair (d := false) fun τ ↦ (D.hasGap_gridParam τ z 0 i j).mono ?_
  -- the parameter has gap `D.gap`, and the rank is at most `2 * D.n D.m`
  grw [gapThreshold, D.card_gridIndex_le h_le.1 h_le.2]
  simpa using D.nat_le_of_hasLogBound

/-- The character `New.Data.gridChar` has weight `D.gridWeight c l n`, which is the exponent of `υ`
in it (`⌊card n / 2⌋` or `⌈card n / 2⌉`) minus `D.liftWeight (l + 1)`. Its tame part
`New.Data.gridTamePart` is the family of residue characters `ω ^ (l + 1)`, `ω = D.chiMLocal`, times
the tame part of `ϑ ^ (l + 1)` if `c` is true. -/
instance gridChar_hasWeight :
    (gridChar ϑ c l n).HasWeight (D.gridWeight c l n) (gridTamePart ϑ c l) :=
  D.hasWeight_liftChar.mul_upsilonU1_pow _

/-- The step from the node `(i, j)` to `(i + 1, j)` of grid `z`, for `i + 1, j ≤ m` and a family
`ϑ x` of `m`-fold twists, is an edge family (`IsEdgeFamily`). The real Schwartz datum is the Fock
vector of `gridHarmonic`, a harmonic polynomial that is a highest weight vector for the lowest
`K`-types of both parameters. -/
lemma isEdgeFamily_grid_succ_left {z : Bool} {i j : ℕ} {I : Type} (ϑ : I → D.MFoldTwist)
    (hi : i + 1 ≤ D.m) (hj : j ≤ D.m) :
    IsEdgeFamily (fun x : I ↦ gridChar (ϑ x) z i) (D.gridKernel z i j)
      (D.gridKernel z (i + 1) j) true (D.gridHarmonic 0 true z i z i j (i + 1) j) :=
  isEdgeFamily_of_paramsCorrespond (fun x : I ↦ gridChar (ϑ x) z i) true
    (fun x : I ↦ gridChar_hasWeight (ϑ x) z i (D.GridIndex z i j))
    (fun x : I ↦ gridChar_hasWeight (ϑ x) z i (D.GridIndex z (i + 1) j))
    (D.paramsCorrespond_grid_succ_left z i j hi hj)

/-- The step from the node `(i, j)` to `(i, j + 1)` of grid `z`, for `i, j + 1 ≤ m` and a family
`ϑ x` of `m`-fold twists, is an edge family (`IsEdgeFamily`). -/
lemma isEdgeFamily_grid_succ_right {z : Bool} {i j : ℕ} {I : Type} (ϑ : I → D.MFoldTwist)
    (hi : i ≤ D.m) (hj : j + 1 ≤ D.m) :
    IsEdgeFamily (fun x : I ↦ gridChar (ϑ x) (!z) j) (D.gridKernel z i j)
      (D.gridKernel z i (j + 1)) false (D.gridHarmonic 0 false (!z) j z i j i (j + 1)) :=
  isEdgeFamily_of_paramsCorrespond (fun x : I ↦ gridChar (ϑ x) (!z) j) false
    (fun x : I ↦ gridChar_hasWeight (ϑ x) (!z) j (D.GridIndex z i j))
    (fun x : I ↦ gridChar_hasWeight (ϑ x) (!z) j (D.GridIndex z i (j + 1)))
    (D.paramsCorrespond_grid_succ_right z 0 i j hi hj (.inl rfl))

/-- For j ≤ m, the space Ỹ^{j}_{j} equals the orthogonal sum of Y^{j}_{j} and the standard line of
sign (−1)^j, with the basis relabelled by the bijection `New.Data.gridDiagEquiv`. -/
lemma gridSpace_diag (hj : j ≤ D.m) :
    D.gridSpace 0 true j j =
      ((D.gridSpace 0 false j j).sum (signedSpace D.E fun _ : Unit ↦ (-1) ^ j)).reindex
        (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj) := by
  cases j
  · rfl
  · -- a sum of two diagonal forms is the diagonal form of the combined signs
    refine signedSpace_eq_reindex _ (Units.ext ((fromBlocks_diagonal ..).trans ?_))
    exact congrArg diagonal (funext fun x ↦ by rcases x with _ | _ <;> rfl)

/-- The hermitian space `Ỹ^{j+1}_j` is the node `(j, j + 1)` of the grid `true`, and `Y^{j+1}_j` is
the node `(j + 1, j)` of the grid `false`; the first argument `0` of `gridSpace` is the offset,
which is `0` on the grids. There is a bijection `τ` of their basis indices that keeps the signs
`gridSigns` of the hermitian forms and such that `Ỹ^{j+1}_j` is `Y^{j+1}_j` with its basis
relabelled along `τ⁻¹`. -/
lemma gridSpace_subdiag (j : ℕ) :
    ∃ (τ : D.GridIndex true j (j + 1) ≃ D.GridIndex false (j + 1) j)
        (h_signs : D.gridSigns false 0 (j + 1) j ∘ τ.symm.symm = D.gridSigns true 0 j (j + 1)),
      D.gridSpace 0 true j (j + 1) = (D.gridSpace 0 false (j + 1) j).reindex τ.symm h_signs := by
  -- equal ranks and equal numbers of signs `-1` give a bijection that keeps signs
  have h_card : card (D.GridIndex true j (j + 1)) = card (D.GridIndex false (j + 1) j) := by
    obtain ⟨k, hk⟩ := D.t_odd
    simp only [card_gridIndex, hk, Bool.toNat_true, Bool.toNat_false]
    lia
  have h_neg :
      negCount (D.gridSigns true 0 j (j + 1)) = negCount (D.gridSigns false 0 (j + 1) j) := by
    rw [negCount_gridSigns, negCount_gridSigns]
    simp only [Bool.toNat_true, Bool.toNat_false]
    omega
  obtain ⟨τ, hτ⟩ := exists_equiv_comp_eq_of_negCount_eq (a := D.gridSigns true 0 j (j + 1))
    (b := D.gridSigns false 0 (j + 1) j) h_card h_neg
  -- both spaces are the diagonal forms `signedSpace` of their signs
  refine ⟨τ, hτ, ?_⟩
  cases j <;> exact signedSpace_eq_reindex _ rfl

/-! ### Transposed lifts and lifts -/

/-- The transposed lift, from forms at `(0, b + 1)` to forms at `(0, b)` of grid z, with the datum
`New.Exchange.pointDatum` (the indicator of the inclusion matrix), times the cardinality
`triangleGLCard z ϑ b`. -/
def pointTransposedLift (z : Bool) (b : ℕ) : D.GridForm z 0 (b + 1) →ₗ[ℂ] D.GridForm z 0 b :=
  (triangleGLCard z ϑ b : ℂ) •
    modTransposedLift (D.gridSpace 0 z 0 b) (D.gridSpace 0 z 0 (b + 1)) (gridChar ϑ (!z) b)
      (D.gridHarmonic 0 false (!z) b z 0 b 0 (b + 1))
      (pointDatum (triangleModulus z ϑ).ResidueRing)
      (D.gridKernel z 0 (b + 1) true) (D.gridKernel z 0 b true)

/-- The composite of the transposed lifts `New.Data.pointTransposedLift` of grid z from the node
`(0, m)` to `(0, b)`: the identity for `b = m`, and zero by convention for `b > m`. It takes
conjugate forms from `Y_m` to `Y_b` in grid `Y`, and forms from `Ỹ^m_0` to `Ỹ^b_0` in grid `Ỹ`. -/
def transposedChain (z : Bool) (b : ℕ) : D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z 0 b :=
  if b < D.m then
    pointTransposedLift ϑ z b ∘ₗ transposedChain z (b + 1)
  else if h : D.m = b then by
    subst h
    exact LinearMap.id
  else
    0

lemma transposedChain_of_lt (hb : b < D.m) :
    transposedChain ϑ z b = pointTransposedLift ϑ z b ∘ₗ transposedChain ϑ z (b + 1) := by
  rw [transposedChain, ite_eq_left hb]

lemma transposedChain_self : transposedChain ϑ z D.m = LinearMap.id := by
  rw [transposedChain, ite_eq_right (lt_irrefl _), dite_eq_left rfl]

variable {ϑ}

/-- The transposed theta lift (`New.Exchange.modTransposedLift`) from forms at `(a, b + 1)` to forms
at `(a, b)` in grid `z`, for the characters `gridChar ϑ (!z) b`. Its Schwartz datum is the indicator
of the matrix `y` modulo `𝔪` at the finite places, and at the infinite places it is given by the
joint harmonic polynomial `gridHarmonic` of the two nodes. -/
def transposedMove
    (y : Matrix (D.GridIndex z a (b + 1)) (D.GridIndex z a b) (gridModulus ϑ).ResidueRing) :
    D.GridForm z a (b + 1) →ₗ[ℂ] D.GridForm z a b :=
  modTransposedLift (D.gridSpace 0 z a b) (D.gridSpace 0 z a (b + 1)) (gridChar ϑ (!z) b)
    (D.gridHarmonic 0 false (!z) b z a b a (b + 1))
    (Pi.single y 1) (D.gridKernel z a (b + 1) true) (D.gridKernel z a b true)

/-- The theta lift (`New.Exchange.modLift`) from forms at `(a, b)` to forms at `(a + 1, b)` in grid
`z`, for the characters `gridChar ϑ z a`. Its Schwartz datum is the indicator of the matrix `y`
modulo `𝔪` at the finite places, and at the infinite places it is given by the joint harmonic
polynomial `gridHarmonic` of the two nodes. -/
def liftMove
    (y : Matrix (D.GridIndex z (a + 1) b) (D.GridIndex z a b) (gridModulus ϑ).ResidueRing) :
    D.GridForm z a b →ₗ[ℂ] D.GridForm z (a + 1) b :=
  modLift (D.gridSpace 0 z a b) (D.gridSpace 0 z (a + 1) b) (gridChar ϑ z a)
    (D.gridHarmonic 0 true z a z a b (a + 1) b)
    (Pi.single y 1) (D.gridKernel z a b true) (D.gridKernel z (a + 1) b true)

/-- Let `k` lie in `stdLevel D.E n'`, the stabiliser of the standard lattice in the finite adelic
unitary group of index type `n'`. The pair `(1, k)` is the point of the adelic unitary group of
signs `s` with real part `1` and finite part `k`, and `G.det` is its determinant. The character
`gridChar ϑ c l n` of U(1)(𝔸) at this determinant is `∏_{w ∣ 𝔪} ψ_w(det k mod w)`. Here
`𝔪 = gridModulus ϑ` is the product of the chosen places to the power `D.natB` times the product of
the places of the twist `ϑ`. The family `ψ = gridTamePart ϑ c l` of characters of the residue
fields is `ω ^ (l + 1)`, times the tame part of `ϑ ^ (l + 1)` if `c` is true, where
`ω = D.chiMLocal` is a fixed family that is trivial outside the chosen places. The index type `n`
of the character is unrelated to `n'` and does not affect the value. -/
lemma gridChar_det {ϑ : D.MFoldTwist} (c : Bool) (l : ℕ) (n : Type) [Fintype n]
    {n' : Type} [Fintype n'] [DecidableEq n'] (s : n' → ℤˣ) (k : stdLevel D.E n') :
    (gridChar ϑ c l n).val (G.det (s := s) (1, k.val)) =
      (gridModulus ϑ).charOfTamePart (gridTamePart ϑ c l)
        ((gridModulus ϑ).reductionGL k).val.det := by
  refine (gridChar_hasWeight ϑ c l n).apply_det_eq_charOfTamePart (fun w hw ↦ ?_) _
  -- outside the modulus `w` is neither a chosen place nor in `ϑ.Q`, so the tame part is trivial
  obtain ⟨hw_chosen, hw_twist⟩ : ¬D.IsChosen w ∧ w ∉ ϑ.Q := by
    simpa [places_twistModulus] using hw
  have h_one : TameChar.one.tamePart w = (1 : MulChar (ResField w) ℂ) := rfl
  cases c <;> simp [liftTamePart, TameChar.pow, hw_chosen, h_one, ϑ.tamePart_eq_one w hw_twist]

/-- Let `𝔪 = 𝔟 Q` be the grid modulus of the twist `ϑ`, with `𝔟 = ϖ ^ D.natB` the grid modulus of
the trivial twist, and let `n` be the basis index set of the node `(z, a, b)`. The number
`levelIndex ϑ z a b` is the index in `GL_n(O_E / 𝔪)` of the level `nodeLevel` of the node. In the
grid `Ỹ` (`z = true`), and in the grid `Y` for `a ≠ 0`, this level is the kernel of reduction modulo
`𝔟`, and the index is the order of `GL_n(O_E / 𝔟)`. -/
lemma levelIndex_eq_card_GL_untwisted {ϑ : D.MFoldTwist} {z : Bool} {a b : ℕ}
    (h_node : z = true ∨ a ≠ 0) :
    levelIndex ϑ z a b = card (GL (D.GridIndex z a b) (D.gridModulus 1).ResidueRing) := by
  -- away from the `Y_b` the level is the kernel of reduction modulo `𝔟`, which is onto,
  -- so the index is the order of the target
  have h_onto :
      (GeneralLinearGroup.map (n := D.NodeIndex (z, a, b)) (reduceToTriangle ϑ true)).range = ⊤ :=
    MonoidHom.range_eq_top.2 fun y ↦ by
      obtain ⟨k, rfl⟩ := Rows.reductionGL_surjective y
      exact ⟨(gridModulus ϑ).reductionGL k, Units.ext Modulus.factor_reductionGL⟩
  have h_level : nodeLevel ϑ (z, a, b) =
      (GeneralLinearGroup.map (n := D.NodeIndex (z, a, b)) (reduceToTriangle ϑ true)).ker := by
    rcases h_node with rfl | ha
    · simp [nodeLevel]
    · simp [nodeLevel, ha]
  rw [levelIndex, h_level, Subgroup.index_ker, h_onto, Subgroup.card_top, Nat.card_eq_fintype_card]

end GridDefs

/-!
## Path data and periods on the two grids

Tuples of matrices modulo `𝔪` on the edges of a path, monadic path data, L-shaped maps on forms
along a path, and periods with the relation `Λ ∝ Ξ`. The groups of integral points act through
their quotients, the invertible matrices modulo `𝔪`.

A `GridDatum ϑ` is a complex linear functional on functions `EdgeTuple ϑ → ℂ`. Instead of tracking
pointwise support sets and multiset sums of roots of unity on raw functions of edge tuples, we
package both into `IsShortSum`: a datum of order `n` on an edge set `w` is a sum of at most
`edgeMatrixCountBound ϑ ^ n` point evaluations weighted by single roots of unity at tuples whose
vertical edges in `w` carry left-invertible matrices. Composing a datum with a finite family of
edge-tuple transitions (`GridDatum.bind`) preserves `IsShortSum` in one step (`IsShortSum.bind`),
allowing single-edge point data, coset averages, interior square moves and diagonal square moves to
share a single algebra.
-/

section GridData

open Fintype Finset Function Exchange Space

variable {P : Parameters} {D : Data P} (ϑ : D.MFoldTwist)

/-- A matrix modulo `𝔪` for each ordered pair of nodes, where `𝔪` is `New.Data.gridModulus` of the
twist `ϑ`. -/
abbrev EdgeTuple : Type :=
  ∀ e : GridNode × GridNode, Matrix (D.NodeIndex e.2) (D.NodeIndex e.1) (gridModulus ϑ).ResidueRing

/-- An invertible matrix modulo `𝔪` for each node. -/
abbrev NodeFamily : Type := ∀ p : GridNode, GL (D.NodeIndex p) (gridModulus ϑ).ResidueRing

variable (D) in
/-- A linear integration functional on complex functions of `EdgeTuple ϑ`. Representing path
weights as linear functionals `(EdgeTuple ϑ → ℂ) →ₗ[ℂ] ℂ` eliminates manual finite-support slices
and unifies edge extensions, coset symmetrizations and square turns under `GridDatum.bind`. -/
abbrev GridDatum : Type := (EdgeTuple (D := D) ϑ → ℂ) →ₗ[ℂ] ℂ

/-- The vertical edges, whose character carries the twist: from `p` to `q` the first index changes
if `p` is in the grid of the `Ỹ`, and stays if it is in that of the `Y`. -/
abbrev IsVerticalEdge (p q : GridNode) : Prop := p.1 ↔ p.2.1 ≠ q.2.1

/-- The character modulo `𝔪` of an edge `e = ((z, a, b), (z', a', b'))`: the character of the tame
part `New.Data.gridTamePart`, with the twist if the edge is vertical, at the index that changes
along the edge (`b` if `a = a'`, else `a`). -/
def edgeChar (e : GridNode × GridNode) : MulChar (gridModulus ϑ).ResidueRing ℂ :=
  (gridModulus ϑ).charOfTamePart
    (gridTamePart ϑ (IsVerticalEdge e.1 e.2) (if e.1.2.1 = e.2.2.1 then e.1.2.2 else e.1.2.1))

/-- A bound for the number of matrices of an edge between nodes with indices at most `D.m`: the
order of the residue ring of `𝔪` to the power `(2 * D.n D.m) ^ 2`, where `2 * D.n D.m` bounds the
ranks of such nodes. -/
abbrev edgeMatrixCountBound : ℕ := card (D.gridModulus ϑ).ResidueRing ^ (2 * D.n D.m) ^ 2

variable {ϑ}

/-- For nodes `p` and `q` whose indices `p.2` and `q.2` are at most `(D.m, D.m)`, the number of
matrices from `NodeIndex q` to `NodeIndex p` (rows indexed by `p`, columns by `q`) over the residue
ring of `𝔪 = gridModulus ϑ` is at most `edgeMatrixCountBound ϑ`, the order of that residue ring to
the power `(2 * D.n D.m) ^ 2`. -/
lemma card_matrix_le_edgeMatrixCountBound {p q : GridNode} (hp : p.2 ≤ (D.m, D.m))
    (hq : q.2 ≤ (D.m, D.m)) :
    card (Matrix (D.NodeIndex p) (D.NodeIndex q) (gridModulus ϑ).ResidueRing) ≤
      edgeMatrixCountBound ϑ := by
  have hp_card : card (D.NodeIndex p) ≤ 2 * D.n D.m := D.card_gridIndex_le hp.1 hp.2
  have hq_card : card (D.NodeIndex q) ≤ 2 * D.n D.m := D.card_gridIndex_le hq.1 hq.2
  rw [card_congr Matrix.of.symm, card_fun, card_fun, ← pow_mul, edgeMatrixCountBound, sq]
  exact Nat.pow_le_pow_right Fintype.card_pos (Nat.mul_le_mul hq_card hp_card)

/-- The families that must fix a path datum up to edge characters. At the ends `Y^0_m` and `Ỹ^m_0`
the element lies in the level of the node (which is trivial modulo `𝔪` at `Y^0_m`), at `Ỹ^a_a` it is
`g ⊕ 1` for the element `g` at `Y^a_a`, and elsewhere it is free. -/
def IsAdmissibleFamily (g : NodeFamily ϑ) : Prop :=
  (∀ z : Bool, g (z, 0, D.m) ∈ nodeLevel ϑ (z, 0, D.m)) ∧
    ∀ a : ℕ, g (true, a, a) = blockInlGL (D.gridDiagEquiv a) (g (false, a, a))

/-- The action of a family `g` of invertible matrices at the nodes on tuples: the matrix at the edge
from `p` to `q` becomes `(g q)⁻¹ * S (p, q) * g p`. -/
def tupleAction (g : NodeFamily ϑ) (S : EdgeTuple ϑ) : EdgeTuple ϑ :=
  fun e : GridNode × GridNode ↦ ((g e.2)⁻¹).val * S e * (g e.1).val

/-- The action `New.Data.tupleAction` on tuples is a right action. -/
lemma tupleAction_mul (g g' : NodeFamily ϑ) (S : EdgeTuple ϑ) :
    tupleAction (g * g') S = tupleAction g' (tupleAction g S) := by
  funext e
  simp [tupleAction, Matrix.mul_assoc]

lemma tupleAction_one (S : EdgeTuple ϑ) : tupleAction 1 S = S := by
  funext e
  simp [tupleAction]

/-- The factor in the action on functions of the matrices of the edges `w`: the product over the
edges from `p` to `q` of the characters `New.Data.edgeChar` at `det (g q) / det (g p)`. -/
def edgeCharProd (g : NodeFamily ϑ) (w : Finset (GridNode × GridNode)) : ℂ :=
  ∏ e ∈ w, (edgeChar ϑ e).toUnitHom ((g e.2).det / (g e.1).det)

/-- The factor `New.Data.edgeCharProd` of the edge characters is multiplicative in the family of
invertible matrices. -/
lemma edgeCharProd_mul (g g' : NodeFamily ϑ) (w : Finset (GridNode × GridNode)) :
    edgeCharProd (g * g') w = edgeCharProd g w * edgeCharProd g' w := by
  simp [edgeCharProd, prod_mul_distrib, field]

lemma isOfFinOrder_edgeCharProd (g : NodeFamily ϑ) (w : Finset (GridNode × GridNode)) :
    IsOfFinOrder (edgeCharProd g w) :=
  (CommMonoid.torsion ℂ).prod_mem fun e _ ↦
    show IsOfFinOrder (((edgeChar ϑ e).toUnitHom ((g e.2).det / (g e.1).det) : ℂˣ) : ℂ) from
      (edgeChar ϑ e).isOfFinOrder (Units.isUnit _).isOfFinOrder

/-- Every vertical edge in `w` carries a matrix of `S` with a left inverse over the residue ring of
`gridModulus ϑ`. -/
abbrev LeftInvOnVerticalEdges (S : EdgeTuple ϑ) (w : Finset (GridNode × GridNode)) : Prop :=
  ∀ e ∈ w, IsVerticalEdge e.1 e.2 → HasLeftInv (S e)

/-- A functional `Λ : GridDatum ϑ` is a short sum of order `n` on the edge set `w` if it is a
combination of at most `edgeMatrixCountBound ϑ ^ n` point evaluations, each nonzero coefficient
being a root of unity at a tuple whose vertical edges in `w` carry left-invertible matrices. -/
def IsShortSum (n : ℕ) (w : Finset (GridNode × GridNode)) (Λ : D.GridDatum ϑ) : Prop :=
  ∃ (X : Type) (W : Finset X) (c : X → ℂ) (s : X → EdgeTuple ϑ),
    #W ≤ edgeMatrixCountBound ϑ ^ n ∧
    (∀ x : X, c x ≠ 0 → IsOfFinOrder (c x) ∧ LeftInvOnVerticalEdges (s x) w) ∧
    ∀ f : EdgeTuple ϑ → ℂ, Λ f = ∑ x ∈ W, c x * f (s x)

/-- Monadic composition of a grid datum `Λ` with a finite family of weights `κ S x` and updated
edge tuples `t S x`, sending `f` to `Λ (fun S ↦ ∑ x, κ S x * f (t S x))`. -/
def GridDatum.bind (Λ : D.GridDatum ϑ) {X : Type} [Fintype X]
    (κ : EdgeTuple ϑ → X → ℂ) (t : EdgeTuple ϑ → X → EdgeTuple ϑ) : D.GridDatum ϑ :=
  Λ ∘ₗ LinearMap.pi fun S ↦ ∑ x : X, κ S x • LinearMap.proj (t S x)

@[simp]
lemma GridDatum.bind_apply (Λ : D.GridDatum ϑ) {X : Type} [Fintype X]
    (κ : EdgeTuple ϑ → X → ℂ) (t : EdgeTuple ϑ → X → EdgeTuple ϑ) (f : EdgeTuple ϑ → ℂ) :
    Λ.bind κ t f = Λ fun S ↦ ∑ x : X, κ S x * f (t S x) :=
  congrArg Λ (funext fun S ↦ by simp)

/-- Composing a short sum of order `n` on `w` with a transition indexed by `X` of cardinality at
most `edgeMatrixCountBound ϑ ^ k`, whose nonzero weights are roots of unity carrying
left-invertibility on vertical edges from `w` to `w'`, yields a short sum of order `n + k` on
`w'`. -/
lemma IsShortSum.bind {n k : ℕ} {w w' : Finset (GridNode × GridNode)} {X : Type} [Fintype X]
    {κ : EdgeTuple ϑ → X → ℂ} {t : EdgeTuple ϑ → X → EdgeTuple ϑ} {Λ : D.GridDatum ϑ}
    (h_card : card X ≤ edgeMatrixCountBound ϑ ^ k)
    (hκ : ∀ (S : EdgeTuple ϑ) (x : X), κ S x ≠ 0 → LeftInvOnVerticalEdges S w →
      IsOfFinOrder (κ S x) ∧ LeftInvOnVerticalEdges (t S x) w')
    (hΛ : IsShortSum n w Λ) :
    IsShortSum (n + k) w' (Λ.bind κ t) := by
  obtain ⟨Y, W, c, s, hW, hc, h_sum⟩ := hΛ
  refine ⟨Y × X, W ×ˢ univ, fun p ↦ c p.1 * κ (s p.1) p.2, fun p ↦ t (s p.1) p.2, ?_, ?_, ?_⟩
  · rw [card_product, card_univ, pow_add]
    exact Nat.mul_le_mul hW h_card
  · rintro ⟨y, x⟩ h_ne
    obtain ⟨hc_root, hs_inv⟩ := hc y (left_ne_zero_of_mul h_ne)
    obtain ⟨hκ_root, ht_inv⟩ := hκ (s y) x (right_ne_zero_of_mul h_ne) hs_inv
    exact ⟨hc_root.mul hκ_root, ht_inv⟩
  · intro f
    simp [GridDatum.bind_apply, h_sum, sum_product, mul_sum, mul_assoc]

/-- A linear functional `Λ` on functions of `EdgeTuple ϑ` is a path datum of order `n` for the
edge set `w` if admissible families scale `Λ` by `edgeCharProd g w` and `Λ` is a short root-of-unity
sum (`IsShortSum n w Λ`) supported on tuples whose vertical edges in `w` carry left-invertible
matrices. -/
structure IsPathDatum (n : ℕ) (w : Finset (GridNode × GridNode)) (Λ : D.GridDatum ϑ) : Prop where
  /-- Admissible families scale `Λ` by the product of the characters of the edges in `w`. -/
  equivariant (g : NodeFamily ϑ) (hg : IsAdmissibleFamily g) (f : EdgeTuple ϑ → ℂ) :
    Λ (fun S ↦ f (tupleAction g S)) = edgeCharProd g w * Λ f
  /-- `Λ` is a short root-of-unity combination of point evaluations with split-injective vertical
  matrices on `w`. -/
  isShortSum : IsShortSum n w Λ

/-! ### L-shaped paths, composite moves and diagonal periods -/

/-- The edge from `(a, b)` to `(a, b + 1)` in the grid `z`: the vertical edge `Y^a_b → Y^a_(b+1)`
or the horizontal edge `Ỹ^b_a → Ỹ^(b+1)_a`. -/
abbrev columnEdge (z : Bool) (a b : ℕ) : GridNode × GridNode := ((z, a, b), z, a, b + 1)

/-- The edge from `(a, b)` to `(a + 1, b)` in the grid `z`: the horizontal edge `Y^a_b → Y^(a+1)_b`
or the vertical edge `Ỹ^b_a → Ỹ^b_(a+1)`. -/
abbrev rowEdge (z : Bool) (a b : ℕ) : GridNode × GridNode := ((z, a, b), z, a + 1, b)

variable (D) in
/-- The edges of the first column of grid `z` between `(0, b)` and `(0, m)`: `(0, i) → (0, i + 1)`
for `b ≤ i < m`. -/
def legEdges (z : Bool) (b : ℕ) : Finset (GridNode × GridNode) :=
  (Ico b D.m).image (columnEdge z 0)

variable (D) in
/-- The edges of the L-shaped path from `(0, m)` to `(a, b)` in grid `z`: first the column edges
from `(0, b)` to `(0, m)`, then the row edges `(i, b) → (i + 1, b)` for `i < a`. -/
def gridPath (z : Bool) (a b : ℕ) : Finset (GridNode × GridNode) :=
  (range a).image (fun i ↦ rowEdge z i b) ∪ D.legEdges z b

variable (D) in
/-- The edges of the two-grid staircase path at stage `j`, meeting the diagonal at `(j, j)`. For
`j = 0` this is the first path along both first columns; for `j = D.m` it is the last path along
row `D.m` in both grids. -/
abbrev stageEdges (j : ℕ) : Finset (GridNode × GridNode) :=
  D.gridPath false j j ∪ D.gridPath true j j

/-- The composite of the single-matrix transposed lifts `transposedMove` down the first column of
grid `z` from `(0, m)` to `(0, b)`, using the matrices that `S` places on `legEdges`; the identity
for `b = m`, and zero for `b > m`. -/
def legDescents (S : EdgeTuple ϑ) (z : Bool) (b : ℕ) : D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z 0 b :=
  if b < D.m then
    transposedMove (S (columnEdge z 0 b)) ∘ₗ legDescents S z (b + 1)
  else if h : D.m = b then by
    subst h
    exact LinearMap.id
  else
    0

lemma legDescents_of_lt (S : EdgeTuple ϑ) (z : Bool) {b : ℕ} (hb : b < D.m) :
    legDescents S z b = transposedMove (S (columnEdge z 0 b)) ∘ₗ legDescents S z (b + 1) := by
  rw [legDescents, ite_eq_left hb]

lemma legDescents_self (S : EdgeTuple ϑ) (z : Bool) : legDescents S z D.m = LinearMap.id := by
  rw [legDescents, ite_eq_right (lt_irrefl _), dite_eq_left rfl]

/-- The map `legDescents` down the first column depends only on the matrices at `legEdges`. -/
lemma legDescents_congr {S S' : EdgeTuple ϑ} {z : Bool} {b : ℕ}
    (h_edges : ∀ e ∈ D.legEdges z b, S e = S' e) :
    legDescents S z b = legDescents S' z b := by
  fun_induction legDescents S z b with
  | case1 b hb ih =>
    have h_head : S (columnEdge z 0 b) = S' (columnEdge z 0 b) :=
      h_edges _ (mem_image.2 ⟨b, mem_Ico.2 ⟨le_rfl, hb⟩, rfl⟩)
    have h_tail : legDescents S z (b + 1) = legDescents S' z (b + 1) :=
      ih fun e he ↦ h_edges e (image_subset_image (Ico_subset_Ico_left (Nat.le_succ b)) he)
    rw [legDescents_of_lt S' z hb, h_head, h_tail]
  | case2 =>
    rw [legDescents_self]
  | case3 b hb hne =>
    rw [legDescents, ite_eq_right hb, dite_eq_right hne]

/-- The composite map on forms along the L-shaped path from `(0, m)` to `(a, b)` in grid `z`:
descend to `(0, b)` by `legDescents`, then lift `a` times along row `b` by `liftMove`. -/
def gridPathMap (S : EdgeTuple ϑ) (z : Bool) :
    ∀ a b : ℕ, D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z a b
  | 0, b => legDescents S z b
  | a + 1, b => liftMove (S (rowEdge z a b)) ∘ₗ gridPathMap S z a b

/-- The map `gridPathMap` along `gridPath z a b` depends only on the matrices on those edges. -/
lemma gridPathMap_congr {S S' : EdgeTuple ϑ} {z : Bool} {a b : ℕ}
    (h_edges : ∀ e ∈ D.gridPath z a b, S e = S' e) :
    gridPathMap S z a b = gridPathMap S' z a b := by
  induction a with
  | zero =>
    exact legDescents_congr fun e he ↦ h_edges e (mem_union_right _ he)
  | succ a ih =>
    have h_row : S (rowEdge z a b) = S' (rowEdge z a b) :=
      h_edges _ (mem_union_left _ (mem_image.2 ⟨a, mem_range.2 (Nat.lt_succ_self a), rfl⟩))
    have h_prev : gridPathMap S z a b = gridPathMap S' z a b :=
      ih fun e he ↦ h_edges e <| by
        rcases mem_union.1 he with h_left | h_right
        · exact mem_union_left _ (image_subset_image (range_mono (Nat.le_succ a)) h_left)
        · exact mem_union_right _ h_right
    simp only [gridPathMap, h_row, h_prev]

/-- The period of a conjugate form on `Y^j_j` and a form on `Ỹ^j_j` along `U(Y^j_j) → U(Ỹ^j_j)`. The
second form is translated by a real point `g` of `U(Ỹ^j_j)` and, on the added line, by the `j`-th
power of `New.Modulus.flipScalar`, the finite idele `ū / u` with `u` a fixed multiple of the chosen
idele generating `𝔪 = gridModulus ϑ`. -/
@[simp] def diagonalPeriodForm (ϑ : D.MFoldTwist) {j : ℕ} (h : j ≤ D.m)
    (g : GInf D.E (D.gridSigns true 0 j j)) :
    D.GridForm false j j →ₗ[ℂ] D.GridForm true j j →ₗ[ℂ] ℂ :=
  periodPairing (isConjKernelPair_gridKernel ⟨h, h⟩)
    { weightFn := 1
      comparisonMap := ⟨fun x ↦ .reindex (D.gridDiagEquiv j)
        (D.sumElim_gridSigns_comp_gridDiagEquiv_symm h)
        (.sum (x, 1, (gridModulus ϑ).flipScalar ^ j)),
        (G.continuous_reindex _ _).comp <| G.continuous_iff.2 <| continuous_pi fun i ↦
          continuous_pi fun k ↦ by
            simp only [G.adeleMatrix_sum]
            rcases i with i | i <;> rcases k with k | k
            · exact (continuous_apply k).comp ((continuous_apply i).comp G.continuous_adeleMatrix)
            · exact continuous_const
            · exact continuous_const
            · exact continuous_const⟩
      isModerate := ⟨1, 0, by simp⟩
      -- the space at Ỹ^j_j is the sum with a line (gridSpace_diag), and the line contributes a
      -- constant factor to the height of the orthogonal sum
      height_le := ⟨_, fun _ ↦ gridSpace_diag h ▸ (height_reindex ..).trans_le (height_sum_le ..)⟩ }
    g

variable (D) in
/-- A twist, a conjugate form on `Y_m` and a form on `Ỹ^m_0`, of any levels. -/
abbrev PeriodTriple : Type := D.MFoldTwist × D.GridForm false 0 D.m × D.GridForm true 0 D.m

variable (D) in
/-- The period at stage `j` of a family `Λ` of grid data, as a function of a triple
`x = (ϑ, y', φ)` of a twist, a conjugate form on `Y_m` and a form on `Ỹ^m_0`: `Λ ϑ` applied to the
diagonal pairing at `(j, j)` of the images of `y'` and `φ` along the two L-shaped halves
`gridPathMap`. Here `g` is a real point of `U(Ỹ^j_j)`. -/
def gridPeriod {j : ℕ} (hj : j ≤ D.m) (Λ : ∀ ϑ : D.MFoldTwist, D.GridDatum ϑ)
    (g : GInf D.E (D.gridSigns true 0 j j)) (x : D.PeriodTriple) : ℂ :=
  Λ x.1 fun S ↦ diagonalPeriodForm x.1 hj g
    (gridPathMap S false j j x.2.1)
    (gridPathMap S true j j x.2.2)

variable (D) in
/-- Proportionality at stage `j`: at each real point `g` of `U(Ỹ^j_j)`, the period `gridPeriod` of
`Λ` is a scalar multiple of `Ξ`, with a scalar independent of the twist and the forms. -/
def IsProportional {j : ℕ} (hj : j ≤ D.m) (Λ : ∀ ϑ : D.MFoldTwist, D.GridDatum ϑ)
    (Ξ : D.PeriodTriple → ℂ) : Prop :=
  ∀ g : GInf D.E (D.gridSigns true 0 j j), ∃ β : ℂ,
    ∀ x : D.PeriodTriple, D.gridPeriod hj Λ g x = β * Ξ x

end GridData

end New.Data

end
