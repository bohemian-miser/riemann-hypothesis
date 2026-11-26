module

import Std.Tactic.BVDecide.Normalize.Bool
public import New.Determinant.AuxiliaryForms.PathData
import Lib.Adelic.AutomorphicForms.Cuspidality
import New.Determinant.Chain.Moduli
import New.OneLift.ComparisonOperator.ExchangeData
import New.OneLift.ComparisonOperator.GluedLattices
import New.UpperBound.Seesaw.LevelIdeles

/-!
# Periods on the diagonal and monadic path data on the first path

The first path goes from `Ỹ^m_0` to `Ỹ^0_0 = Y₀ ⊕ E ẽ₀` and from `Y₀` to `Y_m`. Its spaces are the
nodes `(z, 0, i)`, the first columns of the two grids: `(false, 0, i)` is `Y_i` and `(true, 0, i)`
is `Ỹ^i_0`. A form on `Ỹ^m_0` and a conjugate form on `Y_m` move down these columns by transposed
lifts and meet at `i = 0`.

Starting from the point evaluation at the zero tuple, extending one first-column edge at a time by
`GridDatum.bind` with `edgePointDatum` builds a level-equivariant functional `Φ` of order `2 m` that
computes the period of the two iterated transposed lifts `New.Data.transposedChain`. Composing `Φ`
once more via `GridDatum.bind` with the coset translates `LevelCosets` weighted by `edgeCharProd`
yields an equivariant `GridDatum` of order `4 m` on `stageEdges 0` whose period is a constant
multiple of that of `Φ`.

## Main definitions and results

* `New.Data.exists_petersson_eq_diagonalPeriodForm`: the period with a form on `Ỹ^0_0`, as a
  functional of the form on `Y₀`, is a Petersson product.
* `New.Data.diagonalPeriodForm_tupleAction`: translating the matrices by a family that is `1` at
  the ends and `diag(g, 1)` at `(0, 0)` of the `Ỹ`, `g` being its member at `(0, 0)` of the `Y`,
  multiplies the period by the characters of the edges.
* `New.Data.IsLevelPathDatum`, `New.Data.exists_isLevelPathDatum_transposedChain_eq`: building the
  first-column functional edge by edge via `GridDatum.bind`.
* `New.Data.exists_isPathDatum_diagonalPeriodForm_eq`: symmetrizing over `LevelCosets` via
  `GridDatum.bind` expresses the period of the iterated transposed lifts as a constant times the
  period of a path datum on `stageEdges 0`.

Notions from other files:
* `New.Data.triangleModulus`: the modulus `𝔪₀ = π_M Q` for the chain of the `Y` and `𝔟 = π_M ^ b`
  for that of the `Ỹ`, with `π_M = D.piM`. `New.Data.gridModulus` is `𝔪 = 𝔟Q`, where `Q` comes
  from the twist `ϑ`. `New.Data.triangleGLCard` is the index `n_𝔪₀(Y_i)` or `n_𝔟(Ỹ^i_0)`.
* `New.Data.levelIndex`: the index of the level `New.Data.nodeLevel` at a node, which is the level
  `𝔪` at the `Y_i` and the level `𝔟` elsewhere.
* `New.Data.diagonalPeriodForm`: the period of a conjugate form on `Y^j_j` and a form on `Ỹ^j_j`
  along the embedding of unitary groups, shifted on the line by a scalar from the twist, at a real
  point.
* `New.Data.EdgeTuple`: a matrix modulo `𝔪` for each pair of nodes. A `NodeFamily` of invertible
  matrices acts on it by `New.Data.tupleAction`; `New.Data.edgeCharProd` is the product of the
  characters of the edges at the determinants of such a family.
* `New.Data.legDescents`, `New.Data.gridPathMap`: the composite of the maps by the matrices of a
  tuple along a first column or L-shaped path.
-/

@[expose] public section

noncomputable section

namespace New.Data

/-!
## Periods on the diagonal and translates along the first column

The period of a conjugate form on `Y^j_j` and a form on `Ỹ^j_j` does not see a common translation.
-/

section GridStart

open Function Matrix Fintype Finset Exchange Rows Ideal Quotient Space Gf LevelPlaces

variable {P : Parameters}

/-- The mean of the indicator of the invertible matrices over a finite ring is the share of
invertible matrices. -/
lemma finMean_isUnit_indicator {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] [Fintype R]
    [DecidablePred fun x : Matrix n n R ↦ IsUnit x] [Fintype (GL n R)] :
    finMean (fun x : Matrix n n R ↦ if IsUnit x then (1 : ℂ) else 0) =
      card (GL n R) / card R ^ card n ^ 2 := by
  simp [finMean, card_congr of.symm, sq, pow_mul, ↓finsum_eq_sum_of_fintype,
    (card_congr (.ofInjective _ Units.val_injective)).trans (card_subtype IsUnit)]

/-- The edges of the first columns in the two grids are disjoint. -/
lemma disjoint_legEdges {D : Data P} {b : ℕ} :
    Disjoint (D.legEdges false b) (D.legEdges true b) := by
  rw [disjoint_left]
  intro e hf ht
  simp only [legEdges, mem_image, mem_Ico] at hf ht
  grind

/-- Reduction modulo `𝔪₀ = π_M Q` from the residue ring of `𝔪 = 𝔟Q` (`reduceToTriangle ϑ false`, for
the grid of the `Y`) is a local homomorphism, because the two moduli have the same primes. -/
instance (D : Data P) (ϑ : D.MFoldTwist) : IsLocalHom (reduceToTriangle ϑ false) where
  -- A unit modulo an ideal `I` is a unit modulo `I ^ D.natB`, which lies in the ideal of `𝔪`.
  map_nonunit := Quot.ind fun _ h ↦
    ((isUnit_mk_pow_iff_isUnit_mk _ (NeZero.ne D.natB)).2 h).map
      (factor (by simp [levelModulus, mul_pow, mul_mono, pow_le_self NeZero.out]))

/-- Let `π_M = D.piM`, let `Q` be the product of the places of a twist `ϑ`, and put `𝔪₀ = π_M Q` and
`𝔪 = π_M ^ D.natB * Q` (`gridModulus ϑ`). For the space `Y_j` at the node `(false, 0, j)`, the order
`triangleGLCard false ϑ j` of `GL(Y_j)` modulo `𝔪₀` is a number `C`, the same for all `ϑ`, times
`levelIndex ϑ false 0 j`. -/
lemma exists_triangleGLCard_eq_mul_levelIndex (D : Data P) (j : ℕ) :
    ∃ C : ℂ, ∀ ϑ : D.MFoldTwist, D.triangleGLCard false ϑ j = C * levelIndex ϑ false 0 j := by
  -- Both sides count invertible matrices, the left one modulo `𝔪₀` and the right one modulo `𝔪`.
  refine ⟨(card (D.triangleModulus false 1).ResidueRing / card (D.gridModulus 1).ResidueRing) ^
    card (D.Y j) ^ 2, fun ϑ ↦ ?_⟩
  let R₀ : Type := (D.triangleModulus false ϑ).ResidueRing
  let R : Type := (gridModulus ϑ).ResidueRing
  -- The level at `Y_j` is trivial by definition.
  have h_index : levelIndex ϑ false 0 j = card (GL (D.Y j) R) :=
    congrArg Nat.cast (Subgroup.index_bot.trans Nat.card_eq_fintype_card)
  -- The reduction from `𝔪` to `𝔪₀` is onto and local, so it keeps the share of invertible
  -- matrices, which is the mean of their indicator.
  have h_share : (D.triangleGLCard false ϑ j : ℂ) / card R₀ ^ card (D.Y j) ^ 2 =
      card (GL (D.Y j) R) / card R ^ card (D.Y j) ^ 2 := by
    let π := (reduceToTriangle ϑ false).mapMatrix (m := D.Y j)
    have h_surj : Surjective (reduceToTriangle ϑ false) := factor_surjective _
    have h_unit (x : Matrix (D.Y j) (D.Y j) R) : IsUnit (π x) ↔ IsUnit x := by
      simp [π, isUnit_iff_isUnit_det, ← RingHom.map_det, -RingHom.mapMatrix_apply]
    calc _ = finMean fun x ↦ if IsUnit (π x) then (1 : ℂ) else 0 :=
        finMean_isUnit_indicator.symm.trans (finMean_comp_surjective π.toAddMonoidHom
          h_surj.comp_left.comp_left fun x ↦ if IsUnit x then 1 else 0).symm
      _ = _ := by simpa only [h_unit] using finMean_isUnit_indicator
  -- In the ratio of the norms of `𝔪₀` and `𝔪` the factor from the primes of `ϑ` cancels.
  have h_ratio : (card (D.triangleModulus false 1).ResidueRing / card
    (D.gridModulus 1).ResidueRing : ℂ) =
      card R₀ / card R := by simp [R₀, R, card_residueRing_twistModulus, mul_div_mul_right,
        prod_eq_zero_iff, IsDedekindDomain.HeightOneSpectrum.ne_bot]
  rw [h_index, h_ratio, div_pow, div_mul_comm, ← h_share, div_mul_cancel₀ _ (by simp)]

/-- The period of a conjugate form `y` on `Y^j_j` (grid `false`) and a form `φ` on `Ỹ^j_j` (grid
`true`) at the real point `g` does not change when `y` is translated by a finite adelic point `u` of
the unitary group and `φ` by the block matrix `diag(u, 1)`. -/
lemma diagonalPeriodForm_formRep (D : Data P) (ϑ : D.MFoldTwist) {j : ℕ} {hj : j ≤ D.m}
    {g : GInf D.E (D.gridSigns true 0 j j)} (u : Gf D.E (D.GridIndex false j j))
    (y : D.GridForm false j j) (φ : D.GridForm true j j) :
    diagonalPeriodForm ϑ hj g
        ((D.gridSpace 0 false j j).formRep (D.gridKernel false j j true) u y)
        ((D.gridSpace 0 true j j).formRep (D.gridKernel true j j true)
          (U.block (D.gridDiagEquiv j) (u, 1)) φ) =
      diagonalPeriodForm ϑ hj g y φ := by
  -- Both periods are integrals of `F`, the left one translated by `u`; `F` is invariant under the
  -- rational points, so its integral does not change.
  let ι (x : New.G D.E (D.gridSigns false 0 j j)) : New.G D.E (D.gridSigns true 0 j j) :=
    .reindex (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj)
      (.sum (x, 1, (gridModulus ϑ).flipScalar ^ j))
  let F (x : New.G D.E (D.gridSigns false 0 j j)) : ℂ := y.val x * φ.val (ι x * (g, 1))
  have h_rat : (gridSpace 0 false j j).Γ.FixesLeft F := fun γ hγ x ↦ by
    let γ' : New.G D.E (D.gridSigns true 0 j j) :=
      .reindex (D.gridDiagEquiv j) (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj) (.sum (γ, 1))
    -- Membership in `Γ` is rationality; the block sum with `1` keeps it.
    have hγ' : γ' ∈ (gridSpace 0 true j j).Γ := by
      simp only [γ', gridSpace_diag hj, mem_Gamma_iff_range, Space.reindex, Space.sum, ← map_inv,
        reindex_equiv (D.gridDiagEquiv j)] at hγ ⊢
      simpa [-coe_units_inv, -RingHom.mem_range, fromBlocks_multiply] using hγ
    have h_mul : ι (γ * x) = γ' * ι x := by
      have h_pair : (γ * x, ((1, (gridModulus ϑ).flipScalar ^ j) :
            G D.E (fun _ : Unit ↦ (-1) ^ j))) =
          (γ, 1) * (x, (1, (gridModulus ϑ).flipScalar ^ j)) :=
        Prod.ext rfl (one_mul _).symm
      exact (congrArg (G.reindex (D.gridDiagEquiv j)
          (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj))
        ((congrArg G.sum h_pair).trans (G.sum.map_mul _ _))).trans
        ((G.reindex (D.gridDiagEquiv j)
          (D.sumElim_gridSigns_comp_gridDiagEquiv_symm hj)).map_mul _ _)
    simp only [F, h_mul, mul_assoc, y.property.rat_mul _ hγ, φ.property.rat_mul _ hγ']
  have h_cont : Continuous F :=
    y.property.continuous.mul (φ.property.continuous.comp
      (((G.continuous_reindex _ _).comp
        (G.isClosedEmbedding_sum.continuous.comp
          (continuous_id.prodMk continuous_const))).mul_const _))
  have h_int (y : D.GridForm false j j) (φ : D.GridForm true j j) : diagonalPeriodForm ϑ hj g y φ =
      ∫ x, y.val x * φ.val (ι x * (g, 1)) ∂(D.gridSpace 0 false j j).quotMeasure := by
    simp [periodPairing, ι]
  have h_mul (x) : ι (x * (1, u)) = ι x * (1, U.block (D.gridDiagEquiv j) (u, 1)) := by
    refine Prod.ext ?_ ?_
    · simp [ι, Prod.mul_def]
      rfl
    · refine .trans ?_ ((U.block _).map_mul (x.2, (gridModulus ϑ).flipScalar Unit ^ j) (u, 1))
      simp
      rfl
  rw [h_int, h_int, ← (integral_comp_mul_right u h_rat h_cont).1]
  -- before `Prod.mul_def` takes the product in `h_mul` apart
  simp only [F, h_mul]
  simp [Prod.mul_def]

/-- Let `𝔟` be `D.gridLevelGen = D.piM ^ D.natB`. A form `φ` in `D.gridLevelForms 0`, that is of
level `𝔟` on `Ỹ^0_0`, is fixed under `formRep` by the block matrix
`U.block (D.gridDiagEquiv 0) (u, 1)`, written `diag(u, 1)`, for every `u` on `Y₀` in
`principalLevel` of `𝔟`. -/
lemma formRep_block_one_eq_self (D : Data P) (φ : D.gridLevelForms 0)
    {u : Gf D.E (D.GridIndex false 0 0)}
    (hu : u ∈ principalLevel (D.GridIndex false 0 0) D.gridLevelGen) :
    (D.gridSpace 0 true 0 0).formRep (D.gridKernel true 0 0 true)
      (U.block (D.gridDiagEquiv 0) (u, 1)) φ.val = φ.val := by
  have h_mem : U.block (D.gridDiagEquiv 0) (u, 1) ∈
      principalLevel (D.GridIndex true 0 0) D.gridLevelGen := by
    obtain ⟨hu_Kf, hu_entry⟩ := hu
    refine ⟨by simpa [mem_stdLevel, reindex_equiv (D.gridDiagEquiv 0), Matrix.one_apply]
      using hu_Kf, (D.gridDiagEquiv 0).surjective.forall₂.2 ?_⟩
    -- Off the block of `u` the entries are those of the identity, so there the witness is `0`.
    rintro (i | i) (j | j)
    · simpa [Matrix.one_apply] using hu_entry i j
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
  exact (φ.property ⟨_, h_mem⟩).trans (one_smul ℂ φ.val)

/-- At the node `Y^0_0` of grid `Y`, the kernel `gridKernel false 0 0 true`, that of the conjugate
forms `GridForm false 0 0`, is the complex conjugate (`star`) of `gridKernel false 0 0 false`, the
kernel of the forms on `Y^0_0`. -/
lemma gridKernel_zero_true_eq_star (D : Data P) :
    D.gridKernel false 0 0 true = star (D.gridKernel false 0 0 false) :=
  (isConjKernelPair_gridKernel ⟨D.m.zero_le, D.m.zero_le⟩ false).right

/-- The period with a form `φ` on `Ỹ^0_0`, as a functional of the forms `y` on `Y₀`, is a Petersson
product. The chosen places are the prime divisors of `π_M = D.piM`, and `J_M = D.chosenLevel` is the
group of integral points that reduce to `1` at them. The family `(D.levelPlaces ϑ).placeAt` adds the
places of the modulus `Q` of a twist `ϑ`, so its level `levelOf … ⊥` is the level `𝔪₀ = π_M Q`. The
space `gridLevelForms 0` consists of the forms on `Ỹ^0_0` of principal level `𝔟 = π_M ^ D.natB`. At
a real point `g` there is a linear map `periodRepr` from it to the forms on `Y₀` of level `J_M` such
that, for every `ϑ` and every form `y` on `Y₀` of level `𝔪₀`, the Petersson product of `y` and
`periodRepr φ` is the period at `g` of the conjugate of `y` and `φ`. -/
lemma exists_petersson_eq_diagonalPeriodForm (D : Data P)
    (g : GInf D.E (D.gridSigns true 0 0 0)) :
    ∃ periodRepr : D.gridLevelForms 0 →ₗ[ℂ]
        levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false)) D.chosenLevel,
      ∀ (φ : D.gridLevelForms 0) (ϑ : D.MFoldTwist),
        ∀ y ∈ levelSpace ((D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false))
          (levelOf (D.levelPlaces ϑ).placeAt ⊥),
        (D.gridSpace 0 false 0 0).petersson y (periodRepr φ) =
          diagonalPeriodForm ϑ zero_le g (conjForm D.gridKernel_zero_true_eq_star y) φ := by
  -- `periodRepr φ` represents the functional `conjPeriod φ`, the conjugate of the period, on the
  -- finite-dimensional space of forms of level `J_M`. For `y` of level `𝔪₀`, translation by `J_M`
  -- changes neither side of the identity, so `y` may be replaced by its mean over `J_M`.
  let ρ := (D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 false)
  have he_cusp : IsCuspKernel 0 (D.gridKernel false 0 0 false) :=
    (isConjKernelPair_gridKernel ⟨D.m.zero_le, D.m.zero_le⟩ false).left
  have he_star : D.gridKernel false 0 0 true = star (D.gridKernel false 0 0 false) :=
    D.gridKernel_zero_true_eq_star
  have : IsSmoothRep ρ := ⟨fun y ↦ by
    obtain ⟨K, hK⟩ := y.property.exists_level
    filter_upwards [K.mem_nhds_one] with k hk using Subtype.ext (funext (hK k hk))⟩
  have : Module.Finite ℂ (levelSpace ρ D.chosenLevel) :=
    finite_levelSpace he_cusp ⟨D.chosenLevel, isOpen_levelOf⟩
  let conjPeriod := (diagonalPeriodForm 1 zero_le g ∘ₛₗ conjForm he_star).flip.compr₂ₛₗ
    (starLinearEquiv ℂ).toLinearMap
  have conjPeriod_apply (φ : D.GridForm true 0 0) (y) :
      conjPeriod φ y = star (diagonalPeriodForm 1 zero_le g (conjForm he_star y) φ) := rfl
  let periodRepr : D.gridLevelForms 0 →ₗ[ℂ] levelSpace ρ D.chosenLevel :=
    LinearMap.applyₗ 1 ∘ₗ LinearMap.adjoint.toLinearMap ∘ₛₗ
      conjPeriod.domRestrict₁₂ (D.gridLevelForms 0) (levelSpace ρ D.chosenLevel)
  -- `periodRepr φ` is the value at `1` of the adjoint of the functional `conjPeriod φ`.
  have h_repr (φ : D.gridLevelForms 0) (y : levelSpace ρ D.chosenLevel) :
      innerₛₗ ℂ (periodRepr φ).val y = conjPeriod φ y :=
    (((conjPeriod φ).domRestrict (levelSpace ρ D.chosenLevel)).adjoint_inner_left y 1).trans
      (by simp)
  refine ⟨periodRepr, fun φ ϑ y hy ↦ star_injective ?_⟩
  have h_petersson (u : Gf D.E (D.GridIndex false 0 0)) (hu : u ∈ D.chosenLevel) :
      innerₛₗ ℂ (periodRepr φ).val (ρ u y) =
        star ((D.gridSpace 0 false 0 0).petersson y (periodRepr φ)) := by
    have h_fix : ρ u (periodRepr φ).val = (periodRepr φ).val :=
      ((periodRepr φ).property ⟨u, hu⟩).trans (one_smul ℂ (periodRepr φ).val)
    simpa [ρ, h_fix] using! inner_formRep u (periodRepr φ).val y
  -- Translation by `J_M` does not change the period of the conjugate of `y` and `φ`.
  have h_period (u : Gf D.E (D.GridIndex false 0 0)) (hu : u ∈ D.chosenLevel) :
      conjPeriod φ (ρ u y) = star (diagonalPeriodForm ϑ zero_le g (conjForm he_star y) φ) := by
    lift u to stdLevel D.E (D.GridIndex false 0 0) using levelOf_le_stdLevel hu
    -- Take `v` supported on the places of `𝔟` and their conjugates, with `u * v` of level `𝔟`.
    -- Then `v` lies in `J_M` and is trivial at the places of `ϑ`, so it has level `𝔪₀` and fixes
    -- `y`, and `(u * v, 1)` fixes `φ`.
    obtain ⟨v, hv_supp, hv_red⟩ := exists_reductionGL_eq ((D.gridModulus 1).reductionGL u)⁻¹
    have huv : (u * v).val ∈ principalLevel (D.GridIndex false 0 0) D.gridLevelGen :=
      (Modulus.mem_principalLevel_iff gridModulus_one_ideal (u * v)).2 (by simp [hv_red])
    have hv_chosen : v.val ∈ D.chosenLevel := (D.chosenLevel.mul_mem_cancel_left hu).1
      (D.principalLevel_le_chosenLevel piM_dvd_gridLevelGen huv)
    have hv : v.val ∈ levelOf (D.levelPlaces ϑ).placeAt ⊥ := by
      refine D.chosenLevel_inf_trivialOn_le ϑ ⟨hv_chosen, ?_⟩
      -- At the primes of `ϑ` it is trivial: they are none of those on which it is supported.
      have h_notMem (w : FinPlace D.E) (hw : w ∈ ϑ.Q ∨ star w ∈ ϑ.Q) :
          w ∉ (D.gridModulus 1).places := by
        simp [places_twistModulus, IsChosen, toAutChar_one_and_toTwist_one_and_Q_one,
          (normQ_mem_and_notMem_of_mem_Q D ϑ.toTwist.toTameChar hw).2]
      simpa using fun w hw ↦ mem_supportedOn.1 hv_supp w (h_notMem w (.inl hw))
        (h_notMem (star w) (.inr (by simpa using hw)))
    calc conjPeriod φ (ρ u y)
      _ = star (diagonalPeriodForm ϑ zero_le g ((D.gridSpace 0 false 0 0).formRep
            (D.gridKernel false 0 0 true) (u * v).val (conjForm he_star y)) φ) := by
        have h_form : conjForm he_star (ρ u y) =
            (D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 true) (u * v).val
              (conjForm he_star y) := by
          refine Subtype.ext (funext fun x ↦ ?_)
          have h_g : (x * (1, u.val)) * (1, v.val) = x * (1, u.val * v.val) := by
            rw [mul_assoc]
            exact congrArg (x * ·) (Prod.ext (one_mul 1) rfl)
          exact congrArg star ((mem_levelSpace_formRep_iff.1 hy v.1 hv (x * (1, u.1))).symm.trans
            (congrArg y.val h_g))
        have h_diag : diagonalPeriodForm 1 zero_le g = diagonalPeriodForm ϑ zero_le g := by
          simp only [diagonalPeriodForm, pow_zero]
        rw [conjPeriod_apply, h_diag, h_form]
      _ = _ := by rw [← diagonalPeriodForm_formRep D ϑ (u * v).val (conjForm he_star y),
        formRep_block_one_eq_self D φ huv]
  calc
    _ = innerₛₗ ℂ (periodRepr φ).val (compactMean ρ D.chosenLevel y) :=
      (map_compactMean_of_const _ h_petersson).symm
    _ = conjPeriod φ (compactMean ρ D.chosenLevel y) := h_repr φ ⟨_, compactMean_mem_levelSpace y⟩
    _ = _ := map_compactMean_of_const _ h_period

/-- Put `m = D.m` and `𝔪 = gridModulus ϑ`. Let `S` be a tuple of matrices modulo `𝔪`, one for each
pair of nodes, and `F` a form at the end `(z, 0, m)` of the first column. Let the family `g` of
invertible matrices modulo `𝔪` be `1` at that end, and let `k` be an integral lift of `g (z, 0, b)`,
equal to `1` if `b = m`. Translate `S` by `g`, map `F` down the column to `(z, 0, b)` by
`legDescents`, and translate the image on the right by `k`. The result is the image of `F` for `S`
times `edgeCharProd g`, the product over the edges from `p` to `q` of the column of their characters
at `det (g q) / det (g p)`. -/
lemma formRep_legDescents_tupleAction {D : Data P} {ϑ : D.MFoldTwist} {g : NodeFamily ϑ}
    {z : Bool} {b : ℕ} (hb : b ≤ D.m)
    (hg_end : g (z, 0, D.m) = 1) (S : EdgeTuple ϑ) (F : D.GridForm z 0 D.m)
    (k : stdLevel D.E (D.NodeIndex (z, 0, b))) (hk : g (z, 0, b) = (gridModulus ϑ).reductionGL k)
    (hk_end : b = D.m → k = 1) :
    (D.gridSpace 0 z 0 b).formRep (D.gridKernel z 0 b true) k.val
        (legDescents (tupleAction g S) z b F) =
      edgeCharProd g (D.legEdges z b) • legDescents S z b F := by
  -- Downward induction on `b`: across the edge from `(0, b)` to `(0, b + 1)` the translation by
  -- `k` becomes one by a lift `u` of `g (z, 0, b + 1)`, at the price of the character of the edge.
  induction hb using Nat.decreasingInduction with
  | self =>
    rw [legDescents_self, legDescents_self, legEdges, Ico_self, image_empty, edgeCharProd,
      Finset.prod_empty, one_smul, hk_end rfl, OneMemClass.coe_one, map_one]
    rfl
  | of_succ b hb ih =>
    let u : stdLevel D.E (D.NodeIndex (z, 0, b + 1)) :=
      if b + 1 = D.m then 1 else Rows.liftMod (g (z, 0, b + 1))
    have hu : g (z, 0, b + 1) = (gridModulus ϑ).reductionGL u := by
      dsimp only [u]
      split_ifs with h
      · rw [h, hg_end, map_one]
      · exact (reductionGL_liftMod _).symm
    have h_edge (x : D.GridForm z 0 (b + 1)) :
        (D.gridSpace 0 z 0 b).formRep (D.gridKernel z 0 b true) k.val
            (transposedMove (tupleAction g S (columnEdge z 0 b)) x) =
          edgeCharProd g {columnEdge z 0 b} • transposedMove (S (columnEdge z 0 b))
            ((D.gridSpace 0 z 0 (b + 1)).formRep (D.gridKernel z 0 (b + 1) true) u.val x) := by
      simp only [tupleAction, hk, hu]
      -- The Weil representation moves the translations from the matrix to the two forms.
      refine ((D.isEdgeFamily_grid_succ_right (z := z) id zero_le hb).isArrow_modDatum.2
        |>.formRep_formLift_of_eq_smul (pairWeil_modDatum_single k u) _).trans ?_
      simp [gridChar_det, edgeCharProd, hk, hu, div_eq_mul_inv]
      rfl
    have he : columnEdge z 0 b ∉ D.legEdges z (b + 1) := by simp [legEdges]
    have h_edges : D.legEdges z b = insert (columnEdge z 0 b) (D.legEdges z (b + 1)) := by
      simp [legEdges, ← insert_Ico_add_one_left_eq_Ico hb]
    have h_char_step :
        edgeCharProd g {columnEdge z 0 b} * edgeCharProd g (D.legEdges z (b + 1)) =
          edgeCharProd g (D.legEdges z b) := by
      simp [h_edges, edgeCharProd, prod_insert he]
    rw [legDescents_of_lt _ z hb, legDescents_of_lt _ z hb, LinearMap.comp_apply,
      LinearMap.comp_apply, h_edge, ih u hu (ite_eq_left ·), map_smul, smul_smul, h_char_step]

/-- Let `g` be a family of invertible matrices modulo `gridModulus ϑ`, one at each node, that is `1`
at the ends `(z, 0, D.m)` of both first columns and is the block matrix `diag(g (false, 0, 0), 1)`
at `(true, 0, 0)`. Map a conjugate form `y'` on `Y_m` and a form `φ` on `Ỹ^m_0` down these columns
by `legDescents`, and take the period at the real point `gInf`. Replacing the matrix from `p` to `q`
by `(g q)⁻¹ * S (p, q) * g p` multiplies this period by `edgeCharProd`, the product over the edges
of both columns (`D.stageEdges 0`) of their characters at `det (g q) / det (g p)`. -/
lemma diagonalPeriodForm_tupleAction {D : Data P} {ϑ : D.MFoldTwist} {g : NodeFamily ϑ}
    (hg_end : ∀ z : Bool, g (z, 0, D.m) = 1)
    (hg_diag : g (true, 0, 0) = blockInlGL (D.gridDiagEquiv 0) (g (false, 0, 0)))
    (gInf : GInf D.E (D.gridSigns true 0 0 0)) (y' : D.GridForm false 0 D.m)
    (φ : D.GridForm true 0 D.m) (S : EdgeTuple ϑ) :
    diagonalPeriodForm ϑ zero_le gInf
        (legDescents (tupleAction g S) false 0 y')
        (legDescents (tupleAction g S) true 0 φ) =
      edgeCharProd g (D.stageEdges 0) * diagonalPeriodForm ϑ zero_le gInf
        (legDescents S false 0 y')
        (legDescents S true 0 φ) := by
  -- A lift `u` of `g (false, 0, 0)` translates both forms, and the period does not see it.
  let u : stdLevel D.E (D.GridIndex false 0 0) := Rows.liftMod (g (false, 0, 0))
  have hu : (gridModulus ϑ).reductionGL u = g (false, 0, 0) := reductionGL_liftMod _
  obtain ⟨h_block, h_red⟩ := map_block_eq_blockGL (gridModulus ϑ).reduction (D.gridDiagEquiv 0) u 1
  let u' : stdLevel D.E (D.GridIndex true 0 0) :=
    ⟨U.block (D.gridDiagEquiv 0) (u.val, 1), h_block⟩
  have hu' : g (true, 0, 0) = (gridModulus ϑ).reductionGL u' := by
    refine hg_diag.trans (.trans ?_ h_red.symm)
    simp [← hu, Modulus.reductionGL]
  have hm : 0 ≠ D.m := by simp [m_eq_two_mul_varrho_add_two]
  have h_stage : D.stageEdges 0 = D.legEdges false 0 ∪ D.legEdges true 0 := by
    simp [stageEdges, gridPath]
  have h_char : edgeCharProd g (D.stageEdges 0) =
      edgeCharProd g (D.legEdges false 0) * edgeCharProd g (D.legEdges true 0) := by
    rw [h_stage]
    exact prod_union disjoint_legEdges
  have h_false : (D.gridSpace 0 false 0 0).formRep (D.gridKernel false 0 0 true) u.val
        (legDescents (tupleAction g S) false 0 y') =
      edgeCharProd g (D.legEdges false 0) • legDescents S false 0 y' :=
    formRep_legDescents_tupleAction D.m.zero_le (hg_end false) S y' u hu.symm (absurd · hm)
  have h_true : (D.gridSpace 0 true 0 0).formRep (D.gridKernel true 0 0 true)
        (U.block (D.gridDiagEquiv 0) (u.val, 1))
        (legDescents (tupleAction g S) true 0 φ) =
      edgeCharProd g (D.legEdges true 0) • legDescents S true 0 φ :=
    formRep_legDescents_tupleAction D.m.zero_le (hg_end true) S φ u' hu' (absurd · hm)
  rw [← diagonalPeriodForm_formRep D ϑ u.val, h_false, h_true, h_char,
    LinearMap.map_smul₂, map_smul, smul_smul, smul_eq_mul]

end GridStart

/-!
## Monadic path data on the first path

Starting from the point evaluation at `0`, `GridDatum.bind` attaches the single-edge point data
`edgePointDatum` down both first columns to form a level-equivariant functional `Φ`, and a final
`GridDatum.bind` over `LevelCosets` symmetrizes `Φ` into an equivariant `IsPathDatum` on
`stageEdges 0`.
-/

section GridFirstColumns

open Function Matrix Fintype Finset Exchange Rows Subgroup MulAction Equiv

variable {P : Parameters} {D : Data P}

/-! ### The point data -/

/-- The point datum of the edge from `(0, b)` to `(0, b + 1)`, regarded modulo `𝔪`: the
indicator of the matrices that reduce to the standard inclusion modulo `𝔪₀` in the grid of the
`Y` and modulo `𝔟` in that of the `Ỹ`. -/
def edgePointDatum {ϑ : D.MFoldTwist} (z : Bool) (b : ℕ)
    (y : Matrix (D.NodeIndex (z, 0, b + 1)) (D.NodeIndex (z, 0, b)) (gridModulus ϑ).ResidueRing) :
    ℂ :=
  pointDatum (triangleModulus z ϑ).ResidueRing (y.map (reduceToTriangle ϑ z))

/-- Let `y` be a matrix modulo `𝔪 = gridModulus ϑ` from the space `Y_b` at the node `(false, 0, b)`
to `Y_(b+1)`. If `edgePointDatum false b y` is nonzero, that is, `y` reduces to the standard
inclusion modulo `𝔪₀ = triangleModulus false ϑ`, then `y` has a left inverse modulo `𝔪`, because
`𝔪₀` and `𝔪` have the same primes. -/
lemma hasLeftInv_of_edgePointDatum_ne_zero {ϑ : D.MFoldTwist} {b : ℕ}
    {y : Matrix (D.NodeIndex (false, 0, b + 1)) (D.NodeIndex (false, 0, b))
      (gridModulus ϑ).ResidueRing} (hy : edgePointDatum false b y ≠ 0) : HasLeftInv y := by
  -- The transposed inclusion times `y` reduces to `1`, so it is invertible.
  let u : D.NodeIndex (false, 0, b) ↪ D.NodeIndex (false, 0, b + 1) := .inl
  let J : Matrix (D.NodeIndex (false, 0, b + 1)) (D.NodeIndex (false, 0, b))
      (gridModulus ϑ).ResidueRing := inclMatrix _ u
  have h_red : y.map (reduceToTriangle ϑ false) = inclMatrix _ u := Pi.support_single_subset hy
  have h_unit : IsUnit (Jᵀ * y) := isUnit_of_mapMatrix (reduceToTriangle ϑ false) <| by
    simp only [J, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map]
    rw [h_red, map_inclMatrix, inclMatrix_transpose_mul_self u]
    exact isUnit_one
  exact ⟨_ * Jᵀ, (Matrix.mul_assoc ..).trans h_unit.val_inv_mul⟩

/-! ### The period -/

/-- Both `pointTransposedLift` and `transposedMove y` are transposed theta lifts from forms at
`(0, b + 1)` to forms at `(0, b)` of the grid `z`. The datum of the first is the indicator of the
inclusion matrix modulo `triangleModulus z ϑ`, scaled by the order `triangleGLCard z ϑ b`; that of
the second is the indicator of the single matrix `y` modulo `𝔪`. The first is `triangleGLCard z ϑ b`
times the sum of the second over `y`, weighted by the point datum `edgePointDatum` of the edge. -/
lemma pointTransposedLift_eq_sum {ϑ : D.MFoldTwist} {z : Bool} {b : ℕ} :
    pointTransposedLift ϑ z b = (triangleGLCard z ϑ b : ℂ) •
      ∑ y : Matrix (D.NodeIndex (z, 0, b + 1)) (D.NodeIndex (z, 0, b)) (gridModulus ϑ).ResidueRing,
        edgePointDatum z b y • transposedMove (ϑ := ϑ) y := by
  -- Pull the datum back along the reduction from `𝔪`, then expand it in indicator functions;
  -- `rfl` identifies the pullback with `edgePointDatum` and each summand with `transposedMove`.
  have h_datum (v) :
      modDatum (D.gridSpace 0 z 0 b) (D.gridSpace 0 z 0 (b + 1)) (triangleModulus z ϑ)
          (pointDatum (triangleModulus z ϑ).ResidueRing) v =
        ∑ y : Matrix (D.NodeIndex (z, 0, b + 1)) (D.NodeIndex (z, 0, b))
            (gridModulus ϑ).ResidueRing,
          edgePointDatum z b y •
            modDatum (D.gridSpace 0 z 0 b) (D.gridSpace 0 z 0 (b + 1)) (gridModulus ϑ)
              (Pi.single y 1) v :=
    (modDatum_factor (gridModulus_ideal_le_triangleModulus_ideal ϑ z)
      (pointDatum (triangleModulus z ϑ).ResidueRing) v).symm.trans
      (modDatum_eq_sum (D.gridSpace 0 z 0 b) (D.gridSpace 0 z 0 (b + 1)) (edgePointDatum z b) v)
  dsimp only [pointTransposedLift, modTransposedLift]
  rw [h_datum, map_sum]
  simp only [map_smul]
  rfl

/-- In the grid of the `Ỹ`, the single-step transposed lift `pointTransposedLift` along the first
column does not depend on the twist. -/
lemma pointTransposedLift_one_true_eq {b : ℕ} (ϑ : D.MFoldTwist) :
    D.pointTransposedLift 1 true b = D.pointTransposedLift ϑ true b := by
  have h_char : gridChar 1 (!true) b = gridChar ϑ (!true) b := by
    funext n _
    simp only [gridChar, Bool.not_true, Bool.cond_false]
  dsimp only [pointTransposedLift, triangleGLCard, triangleModulus, triangleTwist,
    Bool.cond_true, Bool.cond_false]
  rw [h_char]

/-! ### Invariance -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `k` be an invertible matrix modulo `gridModulus ϑ = 𝔟Q` in the level `nodeLevel` at a node
`(z, 0, i)` of the first column: the trivial subgroup for `z = false`, the kernel of reduction
modulo `𝔟` for `z = true`. Then `k` reduces to `1` under `reduceToTriangle ϑ z`, the reduction
modulo `π_M Q` for `z = false` and modulo `𝔟` for `z = true`, and for any `b` the character
`edgeChar` of the edge from `(z, 0, b)` to `(z, 0, b + 1)` is `1` at the determinant of `k`. -/
lemma map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel {ϑ : D.MFoldTwist} {z : Bool} {b i : ℕ}
    {k : GL (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing}
    (hk : k ∈ nodeLevel ϑ (z, 0, i)) :
    k.map (reduceToTriangle ϑ z) = 1 ∧ edgeChar ϑ (columnEdge z 0 b) k.val.det = 1 := by
  cases z
  -- For `z = false` the level is trivial.
  · simp [show k = 1 by simpa [nodeLevel] using hk]
  -- For `z = true` the character is untwisted, so it may be read at the modulus of the trivial
  -- twist, where `k` is `1`.
  replace hk : k.map (reduceToTriangle ϑ true) = 1 := by simpa [nodeLevel] using hk
  obtain ⟨k₀, rfl⟩ := reductionGL_surjective k
  have hk₀ : (D.gridModulus 1).reductionGL k₀ = 1 :=
    (Units.ext Modulus.factor_reductionGL).symm.trans hk
  -- Both sides are the value at `k₀` of the adelic character `gridChar`, in which the twist
  -- does not enter.
  have h_char : edgeChar ϑ (columnEdge true 0 b) ((gridModulus ϑ).reductionGL k₀).val.det =
      (D.gridModulus 1).charOfTamePart (gridTamePart 1 false b)
        ((D.gridModulus 1).reductionGL k₀).val.det :=
    (gridChar_det (ϑ := ϑ) false b Unit 1 k₀).symm.trans (gridChar_det (ϑ := 1) false b Unit 1 k₀)
  exact ⟨hk, by simp [h_char, hk₀]⟩

variable (D) in
/-- A functional `Λ : GridDatum ϑ` is level-equivariant of order `n` on `w` if it is a short sum
(`IsShortSum n w Λ`) and is scaled by `edgeCharProd g w` under every family `g` whose entries along
both first columns `(z, 0, i)`, `i ≤ m`, lie in `nodeLevel`. -/
structure IsLevelPathDatum {ϑ : D.MFoldTwist} (n : ℕ) (w : Finset (GridNode × GridNode))
    (Λ : D.GridDatum ϑ) : Prop where
  /-- `Λ` is a short root-of-unity combination with split-injective vertical edges on `w`. -/
  isShortSum : IsShortSum n w Λ
  /-- Families in `nodeLevel` along the first columns scale `Λ` by `edgeCharProd`. -/
  equivariant (g : NodeFamily ϑ) (hg : ∀ z : Bool, ∀ i ≤ D.m, g (z, 0, i) ∈ nodeLevel ϑ (z, 0, i))
    (f : EdgeTuple ϑ → ℂ) :
    Λ (fun S ↦ f (tupleAction g S)) = edgeCharProd g w * Λ f

/-- Extending a level-equivariant datum `Λ` on `w` across a single first-column edge
`columnEdge z 0 b` (`b < D.m`) not in `w`, weighted by `edgePointDatum z b`, yields a
level-equivariant datum of order `n + 1` on `insert (columnEdge z 0 b) w`. -/
lemma IsLevelPathDatum.bind_columnEdge {ϑ : D.MFoldTwist} {n b : ℕ} {z : Bool}
    {w : Finset (GridNode × GridNode)} {Λ : D.GridDatum ϑ} (hb : b < D.m)
    (hw : columnEdge z 0 b ∉ w) (hΛ : D.IsLevelPathDatum n w Λ) :
    D.IsLevelPathDatum (n + 1) (insert (columnEdge z 0 b) w)
      (Λ.bind (fun _ ↦ edgePointDatum z b)
        (fun S y ↦ update S (columnEdge z 0 b) y)) where
  isShortSum := by
    let e : GridNode × GridNode := columnEdge z 0 b
    have h_card : card (Matrix (D.NodeIndex e.2) (D.NodeIndex e.1) (gridModulus ϑ).ResidueRing) ≤
        edgeMatrixCountBound ϑ ^ 1 := by
      simpa [e] using card_matrix_le_edgeMatrixCountBound (p := e.2) (q := e.1)
        ⟨zero_le, hb⟩ ⟨zero_le, hb.le⟩
    refine hΛ.isShortSum.bind h_card fun S y hy hS_inv ↦ ?_
    have hy_one : edgePointDatum z b y = 1 :=
      (congrArg (pointDatum (triangleModulus z ϑ).ResidueRing) (Pi.support_single_subset hy)).trans
        (Pi.single_eq_same _ _)
    refine ⟨hy_one ▸ .one, fun e' he' h_vert ↦ ?_⟩
    rcases mem_insert.1 he' with rfl | he'_w
    · obtain rfl : z = false := by simpa [IsVerticalEdge] using h_vert
      simpa using hasLeftInv_of_edgePointDatum_ne_zero hy
    · rw [update_of_ne (ne_of_mem_of_not_mem he'_w hw)]
      exact hS_inv e' he'_w h_vert
  equivariant g hg f := by
    let e : GridNode × GridNode := columnEdge z 0 b
    obtain ⟨h_red₀, h_char₀⟩ :=
      map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel (b := b) (hg z b hb.le)
    obtain ⟨h_red₁, h_char₁⟩ :=
      map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel (b := b) (hg z (b + 1) hb)
    have h_bij : Bijective (fun y : Matrix (D.NodeIndex e.2) (D.NodeIndex e.1)
        (gridModulus ϑ).ResidueRing ↦ (g e.2).val * y * (g e.1)⁻¹.val) :=
      ((mul_left_injective_of_invertible (g e.1)⁻¹.val).comp
        (mul_right_injective_of_invertible (g e.2).val)).bijective_of_finite
    have h_sum (S : EdgeTuple ϑ) :
        (∑ y, edgePointDatum z b y * f (tupleAction g (update S e y))) =
          ∑ y', edgePointDatum z b y' * f (update (tupleAction g S) e y') := by
      rw [← h_bij.sum_comp]
      refine sum_congr rfl fun y' _ ↦ congrArg₂ (· * ·)
        (by simp [e, edgePointDatum, Matrix.map_mul, -coe_units_inv,
          ← GeneralLinearGroup.val_map_apply, h_red₀, h_red₁])
        (congrArg f <| funext fun e' ↦ by
          rcases eq_or_ne e' e with rfl | hne
          · simp [tupleAction, ← Matrix.mul_assoc]
          · simp [tupleAction, hne])
    simp only [GridDatum.bind_apply]
    have h_fn : (fun S ↦ ∑ x, edgePointDatum z b x * f (tupleAction g (update S e x))) =
        fun S ↦ ∑ y', edgePointDatum z b y' * f (update (tupleAction g S) e y') := funext h_sum
    change Λ (fun S ↦ ∑ x, edgePointDatum z b x * f (tupleAction g (update S e x))) = _
    rw [h_fn, hΛ.equivariant g hg (fun T ↦ ∑ y', edgePointDatum z b y' * f (update T e y'))]
    simp [e, edgeCharProd, prod_insert hw, h_char₀, h_char₁]

/-- For `b ≤ m`, downward induction along both first columns produces a level-equivariant functional
`Φ` of order `2 * (m - b)` on `legEdges false b ∪ legEdges true b` that expands any bilinear pairing
of `transposedChain` into the weighted pairing of `legDescents`. -/
lemma exists_isLevelPathDatum_transposedChain_eq {ϑ : D.MFoldTwist} {b : ℕ} (hb : b ≤ D.m) :
    ∃ Φ : D.GridDatum ϑ,
      D.IsLevelPathDatum (2 * (D.m - b)) (D.legEdges false b ∪ D.legEdges true b) Φ ∧
      ∀ (B : D.GridForm false 0 b →ₗ[ℂ] D.GridForm true 0 b →ₗ[ℂ] ℂ)
        (y' : D.GridForm false 0 D.m) (φ : D.GridForm true 0 D.m),
        B (transposedChain ϑ false b y') (D.transposedChain 1 true b φ) =
          (∏ i ∈ Ico b D.m, (triangleGLCard false ϑ i : ℂ) * triangleGLCard true ϑ i) *
            Φ fun S ↦ B (legDescents S false b y') (legDescents S true b φ) := by
  induction hb using Nat.decreasingInduction with
  | self =>
    have h_empty : D.legEdges false D.m ∪ D.legEdges true D.m = ∅ := by simp [legEdges]
    refine ⟨LinearMap.proj (0 : EdgeTuple ϑ), ⟨?_, fun g _ f ↦ by
      simp [h_empty, edgeCharProd, show tupleAction g (0 : EdgeTuple ϑ) = 0 from
        funext fun _ ↦ by simp [tupleAction]]⟩,
      fun _ _ _ ↦ by simp [transposedChain_self, legDescents_self]⟩
    rw [Nat.sub_self, mul_zero, h_empty]
    exact ⟨Unit, univ, fun _ ↦ 1, fun _ ↦ 0, by simp,
      fun _ _ ↦ ⟨.one, by simp [LeftInvOnVerticalEdges]⟩, fun _ ↦ by simp⟩
  | of_succ b hb ih =>
    obtain ⟨Φ, hΦ, h_eq⟩ := ih
    let u₀ : GridNode × GridNode := columnEdge false 0 b
    let u₁ : GridNode × GridNode := columnEdge true 0 b
    let w₁ : Finset (GridNode × GridNode) := D.legEdges false (b + 1) ∪ D.legEdges true (b + 1)
    let Φ' : D.GridDatum ϑ :=
      (Φ.bind (fun _ ↦ edgePointDatum true b) (fun S y ↦ update S u₁ y)).bind
        (fun _ ↦ edgePointDatum false b) (fun S y ↦ update S u₀ y)
    refine ⟨Φ', ?_, fun B y' φ ↦ ?_⟩
    · rw [← show 2 * (D.m - (b + 1)) + 1 + 1 = 2 * (D.m - b) by omega,
        ← show insert u₀ (insert u₁ w₁) = D.legEdges false b ∪ D.legEdges true b by
          ext e; simp [u₀, u₁, w₁, legEdges]; grind]
      exact (hΦ.bind_columnEdge hb (by simp [legEdges])).bind_columnEdge hb
        (by simp [u₁, w₁, legEdges])
    · let B' := (B.comp (pointTransposedLift ϑ false b)).compl₂ (D.pointTransposedLift 1 true b)
      have h_inner (S : EdgeTuple ϑ) :
          B' (legDescents S false (b + 1) y') (legDescents S true (b + 1) φ) =
            ((triangleGLCard false ϑ b : ℂ) * triangleGLCard true ϑ b) *
              ∑ y₁, edgePointDatum true b y₁ * ∑ y₀, edgePointDatum false b y₀ *
                B (legDescents (update (update S u₁ y₁) u₀ y₀) false b y')
                  (legDescents (update (update S u₁ y₁) u₀ y₀) true b φ) := by
        have h_congr (y₁) (y₀) (z : Bool) :
            legDescents (update (update S u₁ y₁) u₀ y₀) z (b + 1) = legDescents S z (b + 1) :=
          legDescents_congr fun e he ↦ by
            rw [update_of_ne (by rintro rfl; simp [u₀, legEdges] at he),
              update_of_ne (by rintro rfl; simp [u₁, legEdges] at he)]
        change B (pointTransposedLift ϑ false b (legDescents S false (b + 1) y'))
            (D.pointTransposedLift 1 true b (legDescents S true (b + 1) φ)) = _
        rw [pointTransposedLift_one_true_eq ϑ, pointTransposedLift_eq_sum,
          pointTransposedLift_eq_sum]
        simp only [legDescents_of_lt _ _ hb, LinearMap.comp_apply, h_congr,
          show ∀ y₁ y₀, update (update S u₁ y₁) u₀ y₀ (columnEdge false 0 b) = y₀ from
            fun _ _ ↦ update_self ..,
          show ∀ y₁ y₀, update (update S u₁ y₁) u₀ y₀ (columnEdge true 0 b) = y₁ from
            fun _ _ ↦ by rw [update_of_ne (by simp [u₀]), update_self],
          LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul, mul_sum]
        exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
      have h_step := h_eq B' y' φ
      rw [show B' (transposedChain ϑ false (b + 1) y') (D.transposedChain 1 true (b + 1) φ) =
          B (transposedChain ϑ false b y') (D.transposedChain 1 true b φ) by
        rw [transposedChain_of_lt ϑ hb, transposedChain_of_lt 1 hb]; rfl] at h_step
      rw [h_step, prod_eq_prod_Ico_succ_bot hb]
      simp_rw [h_inner, ← smul_eq_mul ((triangleGLCard false ϑ b : ℂ) * _)]
      rw [← Pi.smul_def, Φ.map_smul, smul_eq_mul]
      simp only [Φ', GridDatum.bind_apply]; ring

/-- The cosets of the level `nodeLevel` at a node form a finite type. -/
instance fintypeQuotientNodeLevel {ϑ : D.MFoldTwist} (z : Bool) (a b : ℕ) :
    Fintype (GL (D.GridIndex z a b) (gridModulus ϑ).ResidueRing ⧸ nodeLevel ϑ (z, a, b)) :=
  .ofFinite _

/-- A coset of the level `nodeLevel` for each of the spaces `Y_i` and `Ỹ^i_0` with `i < m`: of the
level `𝔪` at `Y_i` and of the level `𝔟` at `Ỹ^i_0`. -/
abbrev LevelCosets (ϑ : D.MFoldTwist) : Type :=
  ∀ p : Bool × Fin D.m,
    GL (D.NodeIndex (p.1, 0, p.2)) (gridModulus ϑ).ResidueRing ⧸ nodeLevel ϑ (p.1, 0, p.2)

/-- Representatives of the cosets `x`, extended by `1` to the other spaces. -/
def LevelCosets.out {ϑ : D.MFoldTwist} (x : LevelCosets ϑ) : NodeFamily ϑ
  | (z, 0, i) => if h : i < D.m then (x (z, ⟨i, h⟩)).out else 1
  | _ => 1

private lemma LevelCosets.out_zero {ϑ : D.MFoldTwist} (x : LevelCosets ϑ) (z : Bool) (i : ℕ) :
    x.out (z, 0, i) = if h : i < D.m then (x (z, ⟨i, h⟩)).out else 1 := rfl

/-- The family by which the cosets `x` translate: the representatives, except that `Ỹ^0_0`
moves with `Y^0_0`. -/
def LevelCosets.family {ϑ : D.MFoldTwist} (x : LevelCosets ϑ) : NodeFamily ϑ :=
  update x.out (true, 0, 0) (blockInlGL (D.gridDiagEquiv 0) (x.out (false, 0, 0)))

/-- The number of coset families `LevelCosets ϑ` is at most `edgeMatrixCountBound ϑ ^ (2 * D.m)`.
`edgeMatrixCountBound ϑ` bounds the number of matrices modulo `gridModulus ϑ` of an edge between
nodes of index at most `D.m`. -/
lemma card_levelCosets_le {ϑ : D.MFoldTwist} :
    card (LevelCosets ϑ) ≤ edgeMatrixCountBound ϑ ^ (2 * D.m) := by
  rw [Fintype.card_pi]
  refine (prod_le_pow_card univ _ (edgeMatrixCountBound ϑ) fun ⟨z, i⟩ _ ↦ ?_).trans_eq (by simp)
  calc _ ≤ card (GL (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing) :=
        card_le_of_surjective _ QuotientGroup.mk_surjective
    _ ≤ card (Matrix (D.NodeIndex (z, 0, i)) (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing) :=
        card_le_of_injective _ Units.val_injective
    _ ≤ edgeMatrixCountBound ϑ := card_matrix_le_edgeMatrixCountBound (by simp) (by simp)

/-- The number of coset families `LevelCosets` is the product of the indices `levelIndex` of the
levels of the nodes `(0, i)` in the grid of the `Y` and of the orders `triangleGLCard` in that of
the `Ỹ`, over `i < m`. -/
lemma card_levelCosets_eq (ϑ : D.MFoldTwist) : (card (LevelCosets ϑ) : ℂ) =
    ∏ i ∈ range D.m, levelIndex ϑ false 0 i * triangleGLCard true ϑ i := by
  have h_index (z : Bool) (i : ℕ) : (card (GL (D.NodeIndex (z, 0, i)) (gridModulus ϑ).ResidueRing ⧸
      nodeLevel ϑ (z, 0, i)) : ℂ) = levelIndex ϑ z 0 i := by
    rw [levelIndex, index_eq_card, Nat.card_eq_fintype_card]
  have h_true (i : ℕ) : levelIndex ϑ true 0 i = triangleGLCard true ϑ i :=
    levelIndex_eq_card_GL_untwisted (Or.inl rfl)
  rw [Fintype.card_pi, Nat.cast_prod, Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]
  simp only [h_index, h_true, prod_range, prod_mul_distrib]

/-- For an admissible family `g` and cosets `x`, let `y` be `x` translated on the left by `g`. Then
`y.family⁻¹ * (g * x.family)` lies in `nodeLevel` at every node `(z, 0, i)` with `i ≤ m`. -/
lemma LevelCosets.inv_family_mul_mem_nodeLevel {ϑ : D.MFoldTwist} {g : NodeFamily ϑ}
    (hg : IsAdmissibleFamily g) (x : LevelCosets ϑ) :
    let y : LevelCosets ϑ := piCongrRight (fun p ↦ toPerm (g (p.1, 0, p.2))) x
    ∀ z : Bool, ∀ i ≤ D.m, (y.family⁻¹ * (g * x.family)) (z, 0, i) ∈ nodeLevel ϑ (z, 0, i) := by
  intro y z i hi
  obtain ⟨hg_end, hg_diag⟩ := hg
  have h_coset (z' : Bool) (j : ℕ) (hj : j ≤ D.m) :
      (y.out (z', 0, j))⁻¹ * (g (z', 0, j) * x.out (z', 0, j)) ∈ nodeLevel ϑ (z', 0, j) := by
    obtain rfl | hj := hj.eq_or_lt
    · rw [LevelCosets.out_zero, LevelCosets.out_zero, dite_eq_right (lt_irrefl _),
        dite_eq_right (lt_irrefl _), inv_one, one_mul, mul_one]
      exact hg_end z'
    · rw [LevelCosets.out_zero, LevelCosets.out_zero, dite_eq_left hj, dite_eq_left hj,
        ← QuotientGroup.eq]
      exact (QuotientGroup.out_eq' (y (z', ⟨j, hj⟩))).trans
        (Quotient.mk_smul_out (nodeLevel ϑ (z', 0, j)) (g (z', 0, j)) (x (z', ⟨j, hj⟩))).symm
  -- The level at `Y^0_0` is trivial, so the component at `Ỹ^0_0` is `1`.
  have h_zero : (y.out (false, 0, 0))⁻¹ * (g (false, 0, 0) * x.out (false, 0, 0)) = 1 :=
    mem_bot.1 (h_coset false 0 D.m.zero_le)
  by_cases h_corner : ((z, 0, i) : GridNode) = (true, 0, 0)
  · cases h_corner
    rw [Pi.mul_apply, Pi.inv_apply, Pi.mul_apply, LevelCosets.family, LevelCosets.family,
      update_self, update_self, hg_diag 0, ← MonoidHom.map_mul (blockInlGL (D.gridDiagEquiv 0)),
      ← MonoidHom.map_inv (blockInlGL (D.gridDiagEquiv 0)),
      ← MonoidHom.map_mul (blockInlGL (D.gridDiagEquiv 0)), h_zero, MonoidHom.map_one]
    exact one_mem _
  · rw [Pi.mul_apply, Pi.inv_apply, Pi.mul_apply, LevelCosets.family, LevelCosets.family,
      update_of_ne h_corner, update_of_ne h_corner]
    exact h_coset z i hi

/-- Symmetrizing a level-equivariant datum `Φ` of order `2 m` on `stageEdges 0` across `LevelCosets`
via `GridDatum.bind` produces an equivariant `IsPathDatum` of order `4 m` on `stageEdges 0`. -/
lemma IsLevelPathDatum.bind_levelCosets {ϑ : D.MFoldTwist} {Φ : D.GridDatum ϑ}
    (hΦ : D.IsLevelPathDatum (2 * D.m) (D.stageEdges 0) Φ) :
    D.IsPathDatum (4 * D.m) (D.stageEdges 0)
      (Φ.bind (fun _ (x : LevelCosets ϑ) ↦ edgeCharProd x.family (D.stageEdges 0))
        (fun S x ↦ tupleAction x.family⁻¹ S)) where
  isShortSum := by
    rw [show 4 * D.m = 2 * D.m + 2 * D.m by omega]
    refine hΦ.isShortSum.bind card_levelCosets_le fun S x _ hS_inv ↦
      ⟨isOfFinOrder_edgeCharProd _ _, fun e he h_vert ↦ ?_⟩
    obtain ⟨L, hL⟩ := hS_inv e he h_vert
    refine ⟨(x.family e.1).val * L * (x.family e.2)⁻¹.val, ?_⟩
    simp only [tupleAction, Pi.inv_apply, inv_inv, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc _ (x.family e.2)⁻¹.val, Units.inv_mul, Matrix.mul_one,
      Matrix.mul_assoc (x.family e.1).val, hL, Matrix.mul_one, Units.mul_inv]
  equivariant g hg f := by
    let τ : LevelCosets ϑ ≃ LevelCosets ϑ := piCongrRight fun p ↦ toPerm (g (p.1, 0, p.2))
    have h_lin (F : LevelCosets ϑ → EdgeTuple ϑ → ℂ) :
        Φ (fun S ↦ ∑ x : LevelCosets ϑ, edgeCharProd x.family (D.stageEdges 0) * F x S) =
          ∑ x : LevelCosets ϑ, edgeCharProd x.family (D.stageEdges 0) * Φ (F x) := by
      rw [show (fun S ↦ ∑ x, edgeCharProd x.family (D.stageEdges 0) * F x S) =
          ∑ x, edgeCharProd x.family (D.stageEdges 0) • F x from funext fun _ ↦ by simp, map_sum]
      simp [map_smul]
    simp only [GridDatum.bind_apply, h_lin]
    rw [← τ.sum_comp, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    let y : LevelCosets ϑ := τ x
    let k : NodeFamily ϑ := y.family⁻¹ * (g * x.family)
    have h_act (S : EdgeTuple ϑ) :
        tupleAction g (tupleAction y.family⁻¹ S) = tupleAction x.family⁻¹ (tupleAction k S) := by
      rw [← tupleAction_mul, ← tupleAction_mul,
        show y.family⁻¹ * g = k * x.family⁻¹ from
          funext fun p ↦ by simp only [k, Pi.mul_apply, Pi.inv_apply]; group]
    have h_prod : edgeCharProd y.family (D.stageEdges 0) * edgeCharProd k (D.stageEdges 0) =
        edgeCharProd g (D.stageEdges 0) * edgeCharProd x.family (D.stageEdges 0) := by
      rw [← edgeCharProd_mul, ← edgeCharProd_mul,
        show y.family * k = g * x.family from
          funext fun p ↦ by simp only [k, Pi.mul_apply, Pi.inv_apply]; group]
    change edgeCharProd y.family (D.stageEdges 0) *
        Φ (fun S ↦ f (tupleAction g (tupleAction y.family⁻¹ S))) = _
    simp_rw [h_act]
    rw [hΦ.equivariant k (x.inv_family_mul_mem_nodeLevel hg) (fun T ↦ f (tupleAction x.family⁻¹ T)),
      ← mul_assoc, h_prod, mul_assoc]

/-- Put `m = D.m`; the first path `D.stageEdges 0` consists of the edges from `(z, 0, i)` to
`(z, 0, i + 1)` with `i < m`. There are a constant `C` and, for each `m`-fold twist `ϑ`, an
equivariant path datum `Λ ϑ : GridDatum ϑ` of order `4 * m` on the first path. They satisfy the
following for a conjugate form `y'` on `Y^0_m`, a form `φ` on `Ỹ^m_0` (`GridForm true 0 m`) and a
point `g` of the archimedean unitary group `GInf` of `Ỹ^0_0`. Move `y'` and `φ` down the first
columns by the composites `transposedChain` of transposed theta lifts, `y'` at `ϑ` and `φ` at the
trivial twist `1`. The period `diagonalPeriodForm` at `g` of the images is `C` times `gridPeriod`:
`Λ ϑ` applied to the period at `g` of the images of `y'` and `φ` under `legDescents`. -/
lemma exists_isPathDatum_diagonalPeriodForm_eq :
    ∃ (C : ℂ) (Λ : ∀ ϑ : D.MFoldTwist, D.GridDatum ϑ), ∀ ϑ : D.MFoldTwist,
      D.IsPathDatum (4 * D.m) (D.stageEdges 0) (Λ ϑ) ∧
      ∀ (g : GInf D.E (D.gridSigns true 0 0 0)) (y' : D.GridForm false 0 D.m)
        (φ : D.GridForm true 0 D.m),
        diagonalPeriodForm ϑ zero_le g (transposedChain ϑ false 0 y')
            (D.transposedChain 1 true 0 φ) =
          C * D.gridPeriod zero_le Λ g (ϑ, y', φ) := by
  choose κ hκ using (D.exists_triangleGLCard_eq_mul_levelIndex :
    ∀ j : ℕ, ∃ C : ℂ, ∀ ϑ : D.MFoldTwist, D.triangleGLCard false ϑ j = C * levelIndex ϑ false 0 j)
  choose Φ hΦ h_eq using fun ϑ : D.MFoldTwist ↦
    exists_isLevelPathDatum_transposedChain_eq (D := D) (ϑ := ϑ) D.m.zero_le
  simp only [Nat.sub_zero,
    ← show D.stageEdges 0 = D.legEdges false 0 ∪ D.legEdges true 0 by simp [stageEdges, gridPath]]
    at hΦ
  let Λ (ϑ : D.MFoldTwist) : D.GridDatum ϑ :=
    (Φ ϑ).bind (fun _ (x : LevelCosets ϑ) ↦ edgeCharProd x.family (D.stageEdges 0))
      (fun S x ↦ tupleAction x.family⁻¹ S)
  refine ⟨∏ i ∈ range D.m, κ i, Λ, fun ϑ ↦ ⟨(hΦ ϑ).bind_levelCosets, fun gInf y' φ ↦ ?_⟩⟩
  let P (S : EdgeTuple ϑ) : ℂ := diagonalPeriodForm ϑ zero_le gInf
    (legDescents S false 0 y') (legDescents S true 0 φ)
  have h_term (x : LevelCosets ϑ) (S : EdgeTuple ϑ) :
      edgeCharProd x.family (D.stageEdges 0) * P (tupleAction x.family⁻¹ S) = P S := by
    have h_end (z : Bool) : x.family⁻¹ (z, 0, D.m) = 1 := by
      have hne : ((z, 0, D.m) : GridNode) ≠ (true, 0, 0) := fun h ↦ by
        have := congrArg (fun p : GridNode ↦ p.2.2) h; simp [m_eq_two_mul_varrho_add_two] at this
      rw [Pi.inv_apply, LevelCosets.family, update_of_ne hne, LevelCosets.out_zero,
        dite_eq_right (lt_irrefl _), inv_one]
    dsimp only [P]
    rw [diagonalPeriodForm_tupleAction h_end (by simp [LevelCosets.family, ← map_inv]) gInf y' φ S,
      ← mul_assoc, ← edgeCharProd_mul, mul_inv_cancel]
    simp [edgeCharProd]
  have h_period : D.gridPeriod zero_le Λ gInf (ϑ, y', φ) = card (LevelCosets ϑ) * Φ ϑ P := by
    change Λ ϑ P = _
    rw [GridDatum.bind_apply, show (fun S ↦ ∑ x : LevelCosets ϑ,
        edgeCharProd x.family (D.stageEdges 0) * P (tupleAction x.family⁻¹ S)) =
      (card (LevelCosets ϑ) : ℂ) • P from funext fun _ ↦ by simp [h_term],
      (Φ ϑ).map_smul, smul_eq_mul]
  rw [h_period, card_levelCosets_eq, h_eq ϑ (diagonalPeriodForm ϑ zero_le gInf) y' φ,
    ← range_eq_Ico]
  simp only [P, hκ, prod_mul_distrib, mul_assoc]

end GridFirstColumns

end New.Data

end
