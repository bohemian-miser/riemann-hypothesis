module

public import New.Spanning.MainTerm.FillingLevel
public import New.Spanning.Unfolding.Climbing
public import New.Spanning.Frames.BesselVector
import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.General.LinearAlgebra.TensorChains
import New.Spanning.Frames.FiniteDepth
import New.Spanning.Frames.FiniteShells

/-!
# Groups that fix given vectors at chosen places have a small mass integral

Let `S` be an admissible filling with base `b = S.b`, and `T` a finite set of finite places of `E`
stable under conjugation. The product `LocProd T` of the completions at `T` is read as one ring,
with integers `R` (`New.Floors.IntegralPlace`), and `F` is a filling datum on it, of modulus
`g = F.levelUnit`. An `F.IntermediateGroup` is a group `Z` with `K(g) ≤ Z ≤ K`, for the integral
unitary group `K` and its congruence subgroup `K(g)` (both `New.unitaryLevel`). `F.groupMeasure` is
a Haar measure on the unitary group, and `F.massIntegral Z` is the mass integral, the number ∫ |∫_Z
χ_g(y x y⁻¹) dy|² dx, where χ_g is `New.Floors.IntegralPlace.extendedBesselChar g`.

* `New.Filling.volume_integers_diff_intUnits_le`: at the chosen places and their conjugates
  (`New.Filling.chosenPlacesAndConj`), few integers are not units.
* `New.Filling.IsFillingData.exists_intermediateGroup_one_place`: for one place `w`, some group `Z`
  contains the elements that fix the given vector, and `F.massIntegral Z / F.groupMeasure Z` is
  smaller than `F.massIntegral K / F.groupMeasure K` by at least the factor `b ^ (6 * 𝔰.k)`. Here
  `𝔰.k` is the rank of the block `X₀` of the shape `𝔰`. The proof takes the stabiliser of the
  vector at `w`, which has large index in `K`.
* `New.Filling.IsFillingData.exists_intermediateGroup_places`: for several places, induct on `Sg`
  using the binary product law across a conjugation-stable split of `T` into disjoint parts
  `T₁` and `T₂`; the factors multiply via `New.Filling.restrictPlaces`, `New.Filling.toPlacesProd`,
  and `New.Filling.IsFillingData.exists_intermediateGroup_prod`.

Notions from other files:
* `New.Filling`: `S.levelPrime 0` and `S.levelPrime 1` are the level primes `p₀` and `p₁`,
  `S.chosenPlaces i` is the finite set of chosen places of norm `pᵢ`, and `S.ideleM` is the level
  `M = p₀ p₁` as a finite idele.
* `New.Filling.IsFillingData`: `F` is a large lattice datum on `LocProd T` whose modulus is the
  component of `M` at `T` and whose character is `S.charOnPlaces T`.
* `New.Filling.latticeStabilizer`: the integral elements of the finite adelic unitary group;
  `S.reduction` reduces them modulo the chosen places, `S.toPlaces T` takes components at `T`.
* `New.Filling.vectorFixer`: for a chosen place `w` and `d = (ε, v)`, the elements of `S.ResidueGL`
  (the product of the general linear groups over the residue fields) that fix the vector of the span
  of the frame with coordinates `v ≠ 0`, modulo `w` if `ε` is false and modulo its conjugate if `ε`
  is true; `S.fixer Sg d` is the intersection of these groups over `w ∈ Sg`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

@[expose] public section

namespace New.Filling

open NumberField Matrix Finset Fintype MeasureTheory Valued Floors ENNReal Subgroup Pi
  IntegralPlace

section OnePlace

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-! ### Few integers are not units -/

open scoped Classical in
/-- The chosen places of the filling `S`, above both level primes, and their conjugates. -/
noncomputable def chosenPlacesAndConj (S : Filling E 𝔰) : Finset (FinPlace E) :=
  univ.biUnion fun p : Σ i : Fin 2, S.chosenPlaces i ↦
    {(p.2 : FinPlace E), star (p.2 : FinPlace E)}

theorem mem_chosenPlacesAndConj {S : Filling E 𝔰} {w : FinPlace E} :
    w ∈ S.chosenPlacesAndConj ↔
      ∃ (i : Fin 2) (s : FinPlace E), s ∈ S.chosenPlaces i ∧ (w = s ∨ w = star s) := by
  simp [chosenPlacesAndConj]

/-- Let `S` be a filling over `E` (the data of the filling theorem), whose chosen places
`S.chosenPlaces` lie above its two level primes. Suppose every place of `T` is a chosen place of `S`
or the conjugate of one. Then for each `w ∈ T` the residue field order `w.q` is at least
`S.b ^ 10`. -/
theorem b_pow_ten_le_q {S : Filling E 𝔰} {T : Finset (FinPlace E)}
    (hT : T ⊆ S.chosenPlacesAndConj) {w : FinPlace E} (hw : w ∈ T) :
    S.b ^ 10 ≤ w.q := by
  obtain ⟨i, s, hs, hws⟩ : ∃ (i : Fin 2) (s : FinPlace E),
      s ∈ S.chosenPlaces i ∧ (w = s ∨ w = star s) :=
    mem_chosenPlacesAndConj.1 (hT hw)
  have h_conj : w.q = s.q := by
    obtain rfl | rfl := hws
    · rfl
    · exact q_star s
  rw [h_conj, S.chosenPlaces_q i s hs]
  exact S.le_levelPrime i

/-- If every place of `T` is a chosen place of the filling `S` or the conjugate of one, then `T` has
at most `S.b` elements. -/
theorem card_le_b_of_subset_chosenPlacesAndConj {S : Filling E 𝔰} {T : Finset (FinPlace E)}
    (hT : T ⊆ S.chosenPlacesAndConj) :
    (#T : ℝ) ≤ S.b := by
  classical
  have h_chosen : card (Σ i : Fin 2, S.chosenPlaces i) = 2 * numInfPlaces E := by
    simp [S.card_chosenPlaces]
  have h_pairs : #T ≤ 2 * numInfPlaces E * 2 := by
    grw [hT, chosenPlacesAndConj, card_biUnion_le_card_mul _ _ 2 fun _ _ ↦ card_le_two, card_univ,
      h_chosen]
  have h_real : (#T : ℝ) ≤ 2 * numInfPlaces E * 2 := mod_cast h_pairs
  linarith [S.numInfPlaces_le_div, S.one_le_b]

/-- Let `S` be an admissible filling with base `b = S.b`, let every place of `T` be a chosen place
of `S` or the conjugate of one, and let `P.integers` be the ring of integers of the product
`LocProd T` of the completions at `T`, with units `P.intUnits`. Then (a) `2 ≤ b ^ 9`, and (b) the
integers that are not units have volume at most `(b ^ 9)⁻¹`. -/
theorem volume_integers_diff_intUnits_le {S : Filling E 𝔰}
    {T : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)]
    (hT : T ⊆ S.chosenPlacesAndConj) :
    2 ≤ ENNReal.ofReal (S.b ^ 9) ∧
    volume (P.integers \ P.intUnits : Set (LocProd T)) ≤ (ENNReal.ofReal (S.b ^ 9))⁻¹ := by
  -- Almost every element of `LocProd T` is a unit (`P.ae_isUnit`), and an integer that is a unit of
  -- `LocProd T` but not of `P.integers` is divisible by the uniformiser `c w` at some `w`. Each
  -- such set of multiples has volume `1 / q ≤ b⁻¹⁰`, and `T` has at most `4 * numInfPlaces E ≤ b`
  -- places.
  classical
  let c (w : T) : (LocProd T)ˣ :=
    MulEquiv.piUnits.symm (mulSingle w (uniformizer (w : FinPlace E)))
  have hb : 1000 ≤ S.b := S.thousand_le_b
  constructor
  · grw [← hb]
    bound
  have h_sub : (P.integers \ P.intUnits : Set (LocProd T)) ≤ᵐ[volume]
      ⋃ w : T, {x : LocProd T | (c w)⁻¹.val * x ∈ integers} := by
    filter_upwards [P.ae_isUnit]
    rintro _ ⟨y, rfl⟩ ⟨hy_int, hy_nonunit⟩
    -- Some component of `y` lies in the maximal ideal, or `y⁻¹` would be integral.
    obtain ⟨j, hj⟩ : ∃ j : T, v (y.val j) < 1 := by
      by_contra! h_one_le
      refine hy_nonunit ⟨hy_int, y, mem_O_locProd.2 fun j ↦ ?_, rfl⟩
      have h_inv : y⁻¹.val j = (y.val j)⁻¹ := by simp
      rw [h_inv, map_inv₀]
      exact inv_le_one_of_one_le₀ (h_one_le j)
    refine Set.mem_iUnion.2 ⟨j, mem_O_locProd.2 fun i ↦ ?_⟩
    obtain rfl | hij : i = j ∨ i ≠ j := eq_or_ne i j
    · have h_comp : ((c i)⁻¹.val * y.val) i = (uniformizer (i : FinPlace E)).val⁻¹ * y.val i := by
        simp [c]
      rw [h_comp]
      exact v_uniformizer_inv_mul_le_one_iff.2 hj
    · have h_comp : ((c j)⁻¹.val * y.val) i = y.val i := by simp [c, hij]
      rw [h_comp]
      exact mem_O_locProd.1 hy_int i
  have h_vol (w : T) :
      volume {x : LocProd T | (c w)⁻¹.val * x ∈ integers} ≤ ENNReal.ofReal (S.b ^ 10)⁻¹ := by
    have h_q : S.b ^ 10 ≤ (w : FinPlace E).q := b_pow_ten_le_q hT w.prop
    have h_eq : volume {x : LocProd T | (c w)⁻¹.val * x ∈ integers} =
        ENNReal.ofReal ((w : FinPlace E).q : ℝ)⁻¹ := by
      rw [volume_setOf_mul_mem, modulus_eq_inv_genIndex, genIndex_eq_inv_prod_norm,
        Fintype.prod_eq_single w]
      · simp [c, norm_locField_eq_q_zpow]
      · intro i hi
        simp [c, hi]
    rw [h_eq]
    gcongr
  have h_card : (#T : ℝ) ≤ S.b := card_le_b_of_subset_chosenPlacesAndConj hT
  calc volume (P.integers \ P.intUnits : Set (LocProd T))
    _ ≤ ∑ w : T, volume {x : LocProd T | (c w)⁻¹.val * x ∈ integers} :=
      (measure_mono_ae h_sub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _ : T, ENNReal.ofReal (S.b ^ 10)⁻¹ := sum_le_sum fun w _ ↦ h_vol w
    _ = ENNReal.ofReal (#T * (S.b ^ 10)⁻¹) := by
      rw [sum_const, card_univ, card_coe, ← ofReal_nsmul, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (S.b * (S.b ^ 10)⁻¹) := by gcongr
    _ = (ENNReal.ofReal (S.b ^ 9))⁻¹ := by
      rw [← ofReal_inv_of_pos (by positivity)]
      congr 1
      field_simp

/-! ### One place -/

/-- If `2 ≤ B` and `B ^ (t + 1) * z ≤ k` in `ℝ≥0∞`, then `(z + B⁻¹ ^ (t + 1) * k) * B ^ t ≤ k`. -/
theorem add_inv_pow_mul_mul_pow_le {B z k : ℝ≥0∞} {t : ℕ} (hB : 2 ≤ B) (hz : B ^ (t + 1) * z ≤ k) :
    (z + B⁻¹ ^ (t + 1) * k) * B ^ t ≤ k := by
  -- Both terms times `B ^ (t + 1)` are at most `k`; the spare factor `B ≥ 2` pays for the sum.
  rw [← ENNReal.mul_le_mul_iff_left two_ne_zero ofNat_ne_top]
  calc (z + B⁻¹ ^ (t + 1) * k) * B ^ t * 2
    _ ≤ (z + B⁻¹ ^ (t + 1) * k) * B ^ t * B := by gcongr
    _ = B ^ (t + 1) * z + (B⁻¹ * B) ^ (t + 1) * k := by ring
    _ ≤ k * 2 := by grw [hz, ENNReal.inv_mul_le_one, one_pow, one_mul, mul_two]

/-- Let `S` be a filling of shape `𝔰` over `E` (the data of the filling theorem, with `𝔰.ϱ`
hyperbolic planes, a definite space X₀ and a vector z). Let `T` be a finite set of places stable
under conjugation, and `P.integers` the ring of integers of the product `LocProd T` of the
completions at `T`. The form `(S.latticeMiddle A).splitGram` over a ring `A` consists of `𝔰.ϱ`
hyperbolic planes and the Gram matrix `S.latticeMiddle A` of X₀ ⊕ Ez in the lattice basis. Taking
components at `T` (`S.toPlaces T`) maps the integral elements `S.latticeStabilizer` of the finite
adelic unitary group of `S` onto `unitaryLevel P.integers 1`. -/
theorem range_toPlaces_latticeStabilizer {S : Filling E 𝔰} {T : Finset (FinPlace E)}
    [fT : T.StarStable] [P : IntegralPlace (LocProd T)] :
    ((S.toPlaces T).comp S.latticeStabilizer.subtype).range =
      unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨-, hk_int⟩ : S.IsIntegralOff T k ∧
        S.toPlaces T k ∈ unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram :=
      S.mem_latticeStabilizer_iff.1 k.prop
    exact hk_int
  · intro hy
    obtain ⟨x, rfl, hx_off, -⟩ := exists_isIntegralOff_toPlaces_eq y
    have hx_int : x ∈ S.latticeStabilizer := S.mem_latticeStabilizer_iff.2 ⟨hx_off, hy⟩
    exact ⟨⟨x, hx_int⟩, rfl⟩

section Reduction

variable {S : Filling E 𝔰}

/-- The level `M = S.ideleM`, the product of the two level primes as a finite idele, lies in the
maximal ideal at every chosen place `w`. -/
theorem v_ideleM_lt_one {i : Fin 2} (w : S.chosenPlaces i) : v (S.ideleM.val w) < 1 := by
  obtain ⟨h_zero, -⟩ : New.reduceAt w (S.M : Ô E) = 0 ∧ New.reduceAt w (star (S.M : Ô E)) = 0 :=
    (S.M_dvd_iff S.M).1 dvd_rfl ⟨i, w⟩
  rw [reduceAt_eq_zero, SubringClass.coe_natCast] at h_zero
  rwa [ideleM_val]

/-- Let `w` be a chosen place and `r` an integral finite adele. If `M⁻¹ r` is integral at `w`, for
the level `M = S.ideleM`, then `r` vanishes modulo `w`. -/
theorem reduceAt_eq_zero_of_inv_ideleM_smul {i : Fin 2} (w : S.chosenPlaces i) {r : Ô E}
    (hr : v ((S.ideleM⁻¹ • (r : 𝔸f E)) w) ≤ 1) :
    New.reduceAt w r = 0 := by
  have h_adele : (r : 𝔸f E) = S.ideleM.val * S.ideleM⁻¹ • (r : 𝔸f E) := by simp [Units.smul_def]
  have h_factor : (r : 𝔸f E) w = S.ideleM.val w * (S.ideleM⁻¹ • (r : 𝔸f E)) w := by
    simpa only [map_mul, evalAt_apply] using congrArg (evalAt (w : FinPlace E)) h_adele
  rw [reduceAt_eq_zero, h_factor, map_mul]
  exact (mul_le_of_le_one_right' hr).trans_lt (v_ideleM_lt_one w)

/-- If the inverse of the level `M = S.ideleM` is integral at all places outside `T₀`, then `T₀`
contains every chosen place. -/
theorem mem_of_inv_ideleM_mem_integralOff {T₀ : Finset (FinPlace E)}
    (hT : (↑S.ideleM⁻¹ : 𝔸f E) ∈ integralOff T₀) {i : Fin 2} (w : S.chosenPlaces i) :
    (w : FinPlace E) ∈ T₀ := by
  -- Otherwise `M⁻¹` is integral at `w`, and `1` vanishes modulo `w`.
  by_contra hw
  have h_int : v ((S.ideleM⁻¹ • ((1 : Ô E) : 𝔸f E)) w) ≤ 1 := by
    simpa [Units.smul_def] using (mem_integralOff T₀).1 hT w hw
  have h_zero : New.reduceAt w (1 : Ô E) = 0 := reduceAt_eq_zero_of_inv_ideleM_smul w h_int
  simp at h_zero

/-- Let `F` be a filling datum at `T`: a large lattice datum on the product of the completions at
`T` whose modulus `g` is the component of the level `S.ideleM = p₀ p₁`. Let `w ∈ T` be a chosen
place. An integral element `k` of the adelic unitary group whose component at `T` lies in the
congruence subgroup `K(g) = F.congruenceSubgroup` has reduction `S.reduction k i w = 1` modulo
`w`. -/
theorem IsFillingData.reduction_eq_one {T : Finset (FinPlace E)} [fT : T.StarStable]
    [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (h : S.IsFillingData T F) {i : Fin 2}
    {w : S.chosenPlaces i} (hw : (w : FinPlace E) ∈ T) {k : S.latticeStabilizer}
    (hk : S.toPlaces T k ∈ F.congruenceSubgroup) :
    S.reduction k i w = 1 := by
  -- Each entry of `M⁻¹ (k - 1)` is integral at `w`, so each entry of `k - 1` vanishes modulo `w`.
  let x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (k : S.GFin).val
  let y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T) := (S.toPlaces T k).val
  have hy : y = x.map (evalPlaces T) := rfl
  have h_map : F.levelUnit⁻¹ • (y - 1) = (S.ideleM⁻¹ • (x - 1)).map (evalPlaces T) := by
    ext1 a b
    simp [h.levelUnit_eq, hy, Units.smul_def, Matrix.one_apply]
  have h_cong : IsIntMatrix integers (F.levelUnit⁻¹ • (y - 1)) := (mem_unitaryLevel_def.1 hk).right
  rw [h_map] at h_cong
  refine intGL.map_eq_one.2 fun a b ↦ reduceAt_eq_zero_of_inv_ideleM_smul w ?_
  change v (evalPlaces T ((S.ideleM⁻¹ • (x - 1)) a b) ⟨w, hw⟩) ≤ 1
  exact mem_O_locProd.1 (h_cong a b) ⟨w, hw⟩

/-- Let `S` be an admissible filling, `w` a chosen place above the level prime
`p = S.levelPrime i`, and `d` a nonzero vector modulo `w` or its conjugate. The integral elements
whose reduction fixes `d` (lies in `S.vectorFixer w d`) have index `p ^ r - 1` in the integral group
`S.latticeStabilizer`, where `r = 𝔰.r` is the size of the matrices. -/
theorem index_comap_vectorFixer [S.IsAdmissible] {i : Fin 2} (w : S.chosenPlaces i)
    (d : S.FrameVector w) :
    ((S.vectorFixer w d).comap S.reduction).index = S.levelPrime i ^ 𝔰.r - 1 := by
  classical
  -- `S.reduction` and the component at `w` are onto, and the stabiliser of a nonzero vector has as
  -- index the number of nonzero vectors.
  obtain ⟨ε, u, hu⟩ := d
  have h_inj :
      Function.Injective (inclMatrix (ResField (w : FinPlace E)) 𝔰.besselFrame).mulVecLin :=
    inclMatrix_mulVecLin_injective ⟨𝔰.besselFrame, besselFrame_injective⟩ _
  have h_ne : inclMatrix (ResField (w : FinPlace E)) 𝔰.besselFrame *ᵥ u ≠ 0 := by
    simpa using h_inj.ne hu
  have h_surj : Function.Surjective fun s : S.ResidueGL ↦ S.idOrInvAdjoint ε (s i w) :=
    fun g ↦ ⟨mulSingle i (mulSingle w ((S.idOrInvAdjoint ε).symm g)), by simp⟩
  rw [index_comap_of_surjective _ IsAdmissible.reduction_surjective, vectorFixer,
    index_comap_of_surjective _ h_surj, index_stabilizer_GL_vector h_ne,
    card_resField_eq_levelPrime]

/-- Let `𝔰` be the shape of a filling, with the numbers `k = 𝔰.k`, `n = 𝔰.n` and the matrix size
`r = 𝔰.r`. Some `t` has `t + 1 + n + 2 · 10⁹ n⁴ ≤ k`, `6 k ≤ 9 t` and `t + 1 < r`. -/
theorem exists_exponent_le_k (S : Filling E 𝔰) :
    ∃ t : ℕ, t + 1 + 𝔰.n + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k ∧ 6 * 𝔰.k ≤ 9 * t ∧ t + 1 < 𝔰.r := by
  have h_pow : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 ∧ 3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k :=
    S.pow_chain
  have h_size : 𝔰.r = 𝔰.ϱ + (𝔰.k + 1 + 𝔰.ϱ) := by simp
  have h_pos : 0 < 𝔰.n ^ 4 := by positivity
  have h_le : 𝔰.n ≤ 𝔰.n ^ 4 := Nat.le_self_pow (by norm_num) _
  exact ⟨𝔰.k - 10 ^ 10 * 𝔰.n ^ 4, by omega⟩

end Reduction

variable {S : Filling E 𝔰}
  {T : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)]
  {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

/-- Let `S` be an admissible filling with base `b = S.b`, and `F` a filling datum at `T`, where
every place of `T` is a chosen place or the conjugate of one. Let `K = unitaryLevel P.integers 1 _`
be the integral unitary group over the completions at `T` and `K(g) = F.congruenceSubgroup` its
subgroup of elements congruent to `1` modulo `g`. Let `Z` with `K(g) ≤ Z ≤ K` have index
`p₀ ^ r - 1` in `K`, for the first level prime `p₀` and the size `r = 𝔰.r` of the matrices. Then
`ϰ(Z) vol(K) b ^ (6 k) ≤ ϰ(K) vol(Z)`. Here `vol = F.groupMeasure` is a Haar measure,
`ϰ(Z) = F.massIntegral Z` is ∫ |∫_Z χ_g(y x y⁻¹) dy|² dx for the function
χ_g = `extendedBesselChar g`, and `k = 𝔰.k` is the rank of the block `X₀` of the shape `𝔰`. -/
theorem IsFillingData.massIntegral_mul_le_of_relIndex_eq (h : S.IsFillingData T F)
    (hT : T ⊆ S.chosenPlacesAndConj) (Z : F.IntermediateGroup)
    (h_index : Z.val.relIndex (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) =
      S.levelPrime 0 ^ 𝔰.r - 1) :
    F.massIntegral Z *
          F.groupMeasure (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
        ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ≤
      F.massIntegral (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
        F.groupMeasure Z := by
  -- The large index makes the volume of `Z` small; then
  -- `IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error` bounds the mass integral of
  -- `Z` from above, `IntegralPlace.IsLargeLatticeData.setLIntegral_congruenceSubgroup_integral_sq`
  -- that of `K` from below.
  set μ : Measure (U (S.latticeMiddle (LocProd T)).splitGram) := F.groupMeasure
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram with hK
  -- With `B = b ^ 9` the non-units have volume at most `B⁻¹`; the gain is `B ^ t`, `6 k ≤ 9 t`.
  set B : ℝ≥0∞ := ENNReal.ofReal (S.b ^ 9) with hB
  obtain ⟨hB_two, h_vol⟩ : 2 ≤ B ∧ volume (P.integers \ P.intUnits : Set (LocProd T)) ≤ B⁻¹ :=
    S.volume_integers_diff_intUnits_le hT
  have hb : 1 ≤ S.b := S.one_le_b
  obtain ⟨t, ht_le, ht_gain, ht_lt⟩ :
      ∃ t : ℕ, t + 1 + 𝔰.n + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k ∧ 6 * 𝔰.k ≤ 9 * t ∧ t + 1 < 𝔰.r :=
    S.exists_exponent_le_k
  have h_rare : B ^ (t + 1) * μ Z ≤ μ K := by
    have hB_le : B ≤ S.levelPrime 0 := by
      grw [hB, pow_le_pow_right₀ hb (Nat.le_succ 9), S.le_levelPrime 0, ofReal_natCast]
    have h_prime : (S.levelPrime 0).Prime := (S.levelPrime_prime_and_ne 0).left
    have h_pow_le : S.levelPrime 0 ^ (t + 1) ≤ Z.val.relIndex K := by
      rw [h_index]
      exact Nat.le_sub_one_of_lt (pow_lt_pow_right₀ h_prime.one_lt ht_lt)
    calc B ^ (t + 1) * μ Z
      _ ≤ (S.levelPrime 0 ^ (t + 1) : ℕ) * μ Z := by grw [hB_le, Nat.cast_pow]
      _ ≤ Z.val.relIndex K * μ Z := by gcongr
      _ = μ K := by
        rw [hK, ← relIndex_mul_measure_inf unitaryLevel_open_compact.right Z.isOpen,
          inf_of_le_left Z.prop.right]
  have h_K : 2⁻¹ ^ 𝔰.n ≤ μ K := by
    rw [hK]
    exact h.inv_two_pow_le_groupMeasure ⟨hB_two, h_vol⟩
  have h_upper : F.massIntegral Z ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1) * μ K) := by
    have h_modulus (c : (LocProd T)ˣ) (hc : c.val ∈ integers) (hc_inv : c⁻¹.val ∉ integers) :
        P.modulus c ≤ B⁻¹ := (IsLargeLatticeData.modulus_le_volume_nonunits c hc hc_inv).trans h_vol
    have h_half : B⁻¹ ^ 𝔰.n ≤ 2⁻¹ ^ 𝔰.n := by gcongr
    calc F.massIntegral Z
      _ ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1 + 𝔰.n)) :=
        h.massIntegral_le_main_add_error Z hB_two h_modulus ht_le
      _ ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1) * μ K) := by
        grw [pow_add B⁻¹ (t + 1), h_half, h_K]
  have h_lower : μ K ^ 2 * μ F.congruenceSubgroup ≤ F.massIntegral K := by
    have hK_mem : K ∈ Set.Icc F.congruenceSubgroup K := ⟨unitaryLevel_le_unitaryLevel_one, le_rfl⟩
    -- The left side is the part of the outer integral over `K(g)`.
    rw [← h.setLIntegral_congruenceSubgroup_integral_sq ⟨K, hK_mem⟩]
    exact setLIntegral_le_lintegral _ _
  have h_gain : ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ≤ B ^ t := by
    grw [pow_le_pow_right₀ hb ht_gain, pow_mul, ofReal_pow (by positivity)]
  calc F.massIntegral Z * μ K * ENNReal.ofReal (S.b ^ (6 * 𝔰.k))
    _ ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1) * μ K) * μ K * B ^ t := by
      grw [h_upper, h_gain]
    _ = μ Z * μ F.congruenceSubgroup * μ K * ((μ Z + B⁻¹ ^ (t + 1) * μ K) * B ^ t) := by ring
    _ ≤ μ Z * μ F.congruenceSubgroup * μ K * μ K := by
      grw [add_inv_pow_mul_mul_pow_le hB_two h_rare]
    _ = μ K ^ 2 * μ F.congruenceSubgroup * μ Z := by ring
    _ ≤ F.massIntegral K * μ Z := by grw [h_lower]

/-- Let `S` be an admissible filling with base `b = S.b` and `F` a filling datum at `T`, of modulus
`g = F.levelUnit`, where every place of `T` is a chosen place or the conjugate of one. Let `w ∈ T`
be a chosen place above the first level prime and `d` a nonzero frame vector modulo `w` or its
conjugate. Then some group `Z` with `K(g) ≤ Z ≤ K`, for the integral unitary group
`K = unitaryLevel P.integers 1 _` and its congruence subgroup `K(g) = F.congruenceSubgroup`, has
two properties. (a) `Z` contains the `T`-component of every integral element whose reduction fixes
`d` at `w` (lies in `S.vectorFixer w d`). (b) With the mass integral `ϰ = F.massIntegral` and Haar
volume `vol = F.groupMeasure`, `ϰ(Z) vol(K) b ^ (6 * 𝔰.k) ≤ ϰ(K) vol(Z)`, where `𝔰.k` is the rank
of the block `X₀` of the shape `𝔰`. -/
theorem IsFillingData.exists_intermediateGroup_one_place [S.IsAdmissible] (h : S.IsFillingData T F)
    (w : S.chosenPlaces 0) (d : S.FrameVector w) (hwT : (w : FinPlace E) ∈ T)
    (hT_sub : T ⊆ S.chosenPlacesAndConj) :
    ∃ Z : F.IntermediateGroup,
      -- (a)
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.vectorFixer w d → S.toPlaces T k ∈ Z.val) ∧
      -- (b)
      F.massIntegral Z *
            F.groupMeasure (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ≤
        F.massIntegral (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          F.groupMeasure Z := by
  -- Take for `Z` the image of the group `H` of those `k` whose reduction at `w` fixes `d`;
  -- its index in `K` is that of `H` in `S.latticeStabilizer`.
  let p : S.latticeStabilizer →* U (S.latticeMiddle (LocProd T)).splitGram :=
    (S.toPlaces T).comp S.latticeStabilizer.subtype
  have h_range : p.range = unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram :=
    range_toPlaces_latticeStabilizer
  let H : Subgroup S.latticeStabilizer := (S.vectorFixer w d).comap S.reduction
  have h_cong : F.congruenceSubgroup.comap p ≤ H := by
    intro k hk
    have h_one : S.reduction k 0 w = 1 := h.reduction_eq_one hwT hk
    simp [H, vectorFixer, h_one]
  have h_lower : F.congruenceSubgroup ≤ H.map p := by
    have h_le_range : F.congruenceSubgroup ≤ p.range :=
      unitaryLevel_le_unitaryLevel_one.trans h_range.ge
    rw [← map_comap_eq_self h_le_range]
    exact map_mono h_cong
  have h_upper : H.map p ≤ unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram :=
    (H.map_le_range p).trans h_range.le
  have h_index :
      (H.map p).relIndex (unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram) =
        S.levelPrime 0 ^ 𝔰.r - 1 := by
    have h_ker : p.ker ≤ H := (p.ker_le_comap F.congruenceSubgroup).trans h_cong
    rw [← h_range, ← index_comap, comap_map_eq_self h_ker]
    exact index_comap_vectorFixer w d
  let Z : F.IntermediateGroup := ⟨H.map p, h_lower, h_upper⟩
  exact ⟨Z, fun k hk ↦ ⟨k, hk, rfl⟩, h.massIntegral_mul_le_of_relIndex_eq hT_sub Z h_index⟩

end OnePlace

/-!
### Product law across a split of the places

When a conjugation-stable set `T` of finite places splits into two disjoint conjugation-stable
subsets `T₁` and `T₂`, `LocProd T` and its unitary group factor via `restrictPlaces` and
`toPlacesProd`, and both `F.groupMeasure` and `F.massIntegral` multiply up to a Haar scaling
constant (`IsFillingData.exists_intermediateGroup_prod`).
-/

section Rings

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-- Restriction from the product of the completions at `T` to the completions at a subset `T'`. -/
@[simps!]
noncomputable def restrictPlaces {T' T : Finset (FinPlace E)} (h_sub : T' ⊆ T) :
    LocProd T →+* LocProd T' :=
  RingHom.pi fun w : T' ↦ evalRingHom _ (⟨w, h_sub w.prop⟩ : T)

omit [CMType E] in
/-- A property holds at all places of `T` if and only if it holds on both parts `T₁` and `T₂` of a
cover of `T`. -/
private lemma forall_cov {T T₁ T₂ : Finset (FinPlace E)} (h₁ : T₁ ⊆ T) (h₂ : T₂ ⊆ T)
    (h_cov : ∀ w ∈ T, w ∈ T₁ ∨ w ∈ T₂) {q : T → Prop} :
    (∀ w : T, q w) ↔ (∀ w : T₁, q ⟨w, h₁ w.prop⟩) ∧ (∀ w : T₂, q ⟨w, h₂ w.prop⟩) :=
  ⟨fun h ↦ ⟨fun _ ↦ h _, fun _ ↦ h _⟩,
    fun ⟨hq₁, hq₂⟩ ⟨w, hw⟩ ↦ (h_cov w hw).elim (fun h ↦ hq₁ ⟨w, h⟩) (fun h ↦ hq₂ ⟨w, h⟩)⟩

/-- When `T` is split into two disjoint subsets `T₁` and `T₂` covering `T`, the additive character
`S.charOnPlaces T` of the product of the completions at `T`, which is the character of the finite
adeles of `S` after extension by zero, is the product of the characters of `T₁` and `T₂`. -/
theorem charOnPlaces_eq_mul_restrictPlaces {S : Filling E 𝔰} {T T₁ T₂ : Finset (FinPlace E)}
    (h₁_sub : T₁ ⊆ T) (h₂_sub : T₂ ⊆ T) (h_disj : Disjoint T₁ T₂)
    (h_cov : ∀ w ∈ T, w ∈ T₁ ∨ w ∈ T₂) (x : LocProd T) :
    S.charOnPlaces T x =
      S.charOnPlaces T₁ (restrictPlaces h₁_sub x) *
        S.charOnPlaces T₂ (restrictPlaces h₂_sub x) := by
  -- An adele supported on `T` is the sum of its parts on `T₁` and `T₂`.
  have h_sum : adeleOfLocal T x =
      adeleOfLocal T₁ (restrictPlaces h₁_sub x) +
        adeleOfLocal T₂ (restrictPlaces h₂_sub x) := by
    ext w
    -- A place of `T` lies in exactly one of `T₁`, `T₂`; both sides vanish at the other places.
    by_cases hw₁ : w ∈ T₁
    · simp [adeleOfLocal_apply, h₁_sub hw₁, hw₁, disjoint_left.1 h_disj hw₁]
    · by_cases hw₂ : w ∈ T₂
      · simp [adeleOfLocal_apply, h₂_sub hw₂, hw₁, hw₂]
      · simp [adeleOfLocal_apply, mt (h_cov w) (by tauto), hw₁, hw₂]
  simp only [charOnPlaces, AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_ofClass, h_sum,
    AddChar.map_add_eq_mul]

end Rings

section Groups

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-- For conjugation-stable subsets `T₁`, `T₂` of `T`, the product map from the unitary group over
`LocProd T` to the unitary groups over `LocProd T₁` and `LocProd T₂`. -/
noncomputable def toPlacesProd (S : Filling E 𝔰) {T T₁ T₂ : Finset (FinPlace E)} [T.StarStable]
    [T₁.StarStable] [T₂.StarStable] (h₁ : T₁ ⊆ T) (h₂ : T₂ ⊆ T) :
    U (S.latticeMiddle (LocProd T)).splitGram →*
      U (S.latticeMiddle (LocProd T₁)).splitGram × U (S.latticeMiddle (LocProd T₂)).splitGram :=
  (U.map (restrictPlaces h₁) (fun _ ↦ rfl) (S.map_splitGram_latticeMiddle _)).prod
    (U.map (restrictPlaces h₂) (fun _ ↦ rfl) (S.map_splitGram_latticeMiddle _))

variable {S : Filling E 𝔰} {T T₁ T₂ : Finset (FinPlace E)} [T.StarStable] [T₁.StarStable]
  [T₂.StarStable] (h₁_sub : T₁ ⊆ T) (h₂_sub : T₂ ⊆ T)

/-- For an adelic unitary matrix `x`, restricting its components at `T` to `T₁` and `T₂` gives the
pair of components of `x` at `T₁` and `T₂`. -/
lemma toPlacesProd_toPlaces (x : U (S.latticeMiddle (𝔸f E)).splitGram) :
    S.toPlacesProd h₁_sub h₂_sub (S.toPlaces T x) = (S.toPlaces T₁ x, S.toPlaces T₂ x) :=
  rfl

variable (h_disj : Disjoint T₁ T₂) (h_cov : ∀ w ∈ T, w ∈ T₁ ∨ w ∈ T₂)

include h_disj h_cov in
/-- Unitary matrices over disjoint subsets `T₁` and `T₂` covering `T` glue to a unitary matrix over
`T`, that is, the map `S.toPlacesProd h₁_sub h₂_sub` to the product of the unitary groups over `T₁`
and `T₂` is onto. -/
lemma toPlacesProd_surjective : Function.Surjective (S.toPlacesProd h₁_sub h₂_sub) := by
  classical
  rintro ⟨y₁, y₂⟩
  let M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T) := of fun a b w ↦
    if hw : (w : FinPlace E) ∈ T₁ then y₁.val a b ⟨w, hw⟩
    else y₂.val a b ⟨w, (h_cov w w.prop).resolve_left hw⟩
  have hM₁ : M.map (restrictPlaces h₁_sub) = y₁.val :=
    Matrix.ext fun _ _ ↦ funext fun w ↦ dite_eq_left w.prop
  have hM₂ : M.map (restrictPlaces h₂_sub) = y₂.val :=
    Matrix.ext fun _ _ ↦ funext fun w ↦ dite_eq_right (disjoint_right.1 h_disj w.prop)
  have h_res {T' : Finset (FinPlace E)} [T'.StarStable] (hs : T' ⊆ T)
      {y : U (S.latticeMiddle (LocProd T')).splitGram} (hM : M.map (restrictPlaces hs) = y.val) :
      (Mᴴ * (S.latticeMiddle (LocProd T)).splitGram * M).map (restrictPlaces hs) =
        (S.latticeMiddle (LocProd T)).splitGram.map (restrictPlaces hs) := by
    rw [map_conjTranspose_mul_mul _ fun _ ↦ rfl, hM, S.map_splitGram_latticeMiddle]
    exact mem_unitaryGroupOf_iff.1 y.prop
  have h_unitary : Mᴴ * (S.latticeMiddle (LocProd T)).splitGram * M =
      (S.latticeMiddle (LocProd T)).splitGram := by
    ext a b : 1
    exact funext_iff.2 <| (forall_cov h₁_sub h₂_sub h_cov).2
      ⟨congr_fun (congr_fun₂ (h_res h₁_sub hM₁) a b),
        congr_fun (congr_fun₂ (h_res h₂_sub hM₂) a b)⟩
  exact ⟨U.of IsHermitianUnit.isUnit M h_unitary,
    Prod.ext (Subtype.ext (Units.ext hM₁)) (Subtype.ext (Units.ext hM₂))⟩

include h_cov in
/-- The group `unitaryLevel SemilocalField.O u` for the Gram matrix `splitGram` over the completions
at `T` is the preimage under `S.toPlacesProd h₁_sub h₂_sub` of the product of the same groups over
`T₁` and `T₂`, with moduli `u` projected by `restrictPlaces h₁_sub` and `restrictPlaces h₂_sub`. -/
lemma unitaryLevel_eq_comap_toPlacesProd (u : (LocProd T)ˣ) :
    unitaryLevel SemilocalField.O u (S.latticeMiddle (LocProd T)).splitGram =
      ((unitaryLevel SemilocalField.O (u.map (restrictPlaces h₁_sub))
          (S.latticeMiddle (LocProd T₁)).splitGram).prod
        (unitaryLevel SemilocalField.O (u.map (restrictPlaces h₂_sub))
          (S.latticeMiddle (LocProd T₂)).splitGram)).comap (S.toPlacesProd h₁_sub h₂_sub) := by
  -- Each of the three conditions asks for a matrix to be integral, which is read on `T₁` and `T₂`.
  have h_int (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) :
      IsIntMatrix SemilocalField.O M ↔
        IsIntMatrix SemilocalField.O (M.map (restrictPlaces h₁_sub)) ∧
        IsIntMatrix SemilocalField.O (M.map (restrictPlaces h₂_sub)) := by
    simp only [IsIntMatrix, mem_O_locProd, Matrix.map_apply, restrictPlaces_apply,
      forall_cov h₁_sub h₂_sub h_cov, forall_and]
  have h_cong {T' : Finset (FinPlace E)} (f : LocProd T →+* LocProd T')
      (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) :
      (u⁻¹ • (M - 1)).map f = (u.map (f : LocProd T →* LocProd T'))⁻¹ • (M.map f - 1) := by
    ext a b : 1
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Units.smul_def, smul_eq_mul,
      map_mul, map_sub, Units.coe_map_inv, MonoidHom.coe_ofClass, Matrix.one_apply,
      apply_ite f, map_one, map_zero]
  have h_map₁ (y : (S.latticeMiddle (LocProd T)).G) :
      (S.toPlacesProd h₁_sub h₂_sub y).1.val.val = y.val.val.map (restrictPlaces h₁_sub) := rfl
  have h_map₂ (y : (S.latticeMiddle (LocProd T)).G) :
      (S.toPlacesProd h₁_sub h₂_sub y).2.val.val = y.val.val.map (restrictPlaces h₂_sub) := rfl
  ext x
  have h_map_inv₁ : (S.toPlacesProd h₁_sub h₂_sub x).1.val⁻¹.val =
      x.val⁻¹.val.map (restrictPlaces h₁_sub) := h_map₁ x⁻¹
  have h_map_inv₂ : (S.toPlacesProd h₁_sub h₂_sub x).2.val⁻¹.val =
      x.val⁻¹.val.map (restrictPlaces h₂_sub) := h_map₂ x⁻¹
  simp only [Subgroup.mem_comap, Subgroup.mem_prod, mem_unitaryLevel_def, mem_intGL,
    h_map₁ x, h_map₂ x, h_map_inv₁, h_map_inv₂, ← h_cong (restrictPlaces h₁_sub),
    ← h_cong (restrictPlaces h₂_sub)]
  -- The congruences agree; `x` and `x⁻¹` are integral when they are so on `T₁` and `T₂`.
  exact (((and_congr (h_int x.val.val) (h_int x.val⁻¹.val)).and (h_int _)).trans
    (and_congr_left' and_and_and_comm)).trans and_and_and_comm

include h_cov in
/-- A unitary matrix over the completions at `T` lies in `besselU`, the group of unitary matrices
that are unitriangular for the levels of the indices, if and only if this holds on both `T₁` and
`T₂`. -/
lemma mem_besselU_iff_toPlacesProd {x : U (S.latticeMiddle (LocProd T)).splitGram} :
    x ∈ besselU ↔
      (S.toPlacesProd h₁_sub h₂_sub x).1 ∈ besselU ∧
      (S.toPlacesProd h₁_sub h₂_sub x).2 ∈ besselU := by
  simp only [mem_besselU, funext_iff, Matrix.one_apply, apply_ite (fun z : LocProd _ ↦ z _),
    forall_cov h₁_sub h₂_sub h_cov, forall_and]
  rfl

end Groups

section Measures

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {T : Finset (FinPlace E)} [T.StarStable] [P : IntegralPlace (LocProd T)]
  {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
    (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

/-- Let `F` be a filling datum at `T` and `F'` a filling datum at a conjugation-stable subset `T'`
of `T`. Then the modulus `F'.levelUnit` is the projection of the modulus `F.levelUnit` to `T'`. -/
lemma IsFillingData.levelUnit_eq_map_restrictPlaces {T' : Finset (FinPlace E)} [T'.StarStable]
    [P' : IntegralPlace (LocProd T')]
    {F' : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T'))
      (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}
    (h_sub : T' ⊆ T) (h : S.IsFillingData T F) (h' : S.IsFillingData T' F') :
    F'.levelUnit = F.levelUnit.map (restrictPlaces h_sub) := by
  rw [h.levelUnit_eq, h'.levelUnit_eq]
  rfl

variable {T₁ T₂ : Finset (FinPlace E)} [T₁.StarStable] [T₂.StarStable]
  [P₁ : IntegralPlace (LocProd T₁)] [P₂ : IntegralPlace (LocProd T₂)]
  (h₁_sub : T₁ ⊆ T) (h₂_sub : T₂ ⊆ T) (h_disj : Disjoint T₁ T₂)
  (h_cov : ∀ w ∈ T, w ∈ T₁ ∨ w ∈ T₂)

include h_cov in
/-- The map `S.toPlacesProd h₁_sub h₂_sub` from the unitary group over the completions at `T` to the
product of the unitary groups over `T₁` and `T₂` is a measurable embedding. -/
lemma measurableEmbedding_toPlacesProd : MeasurableEmbedding (S.toPlacesProd h₁_sub h₂_sub) := by
  -- The projections to `T₁` and `T₂` are continuous entry by entry, and the map is injective.
  have h_cont : Continuous (S.toPlacesProd h₁_sub h₂_sub) :=
    (U.continuous_map (continuous_pi fun _ ↦ continuous_apply _)).prodMk
      (U.continuous_map (continuous_pi fun _ ↦ continuous_apply _))
  refine h_cont.measurableEmbedding fun x y hxy ↦ ?_
  ext a b : 2
  exact funext_iff.2 <| (forall_cov h₁_sub h₂_sub h_cov).2
    ⟨congr_fun (congr_fun₂ (congrArg (fun z ↦ z.1.val.val) hxy) a b),
      congr_fun (congr_fun₂ (congrArg (fun z ↦ z.2.val.val) hxy) a b)⟩

include h_disj h_cov

/-- Let `T` split into disjoint conjugation-stable subsets `T₁` and `T₂`, and let the additive
characters of the integral places `P`, `P₁`, `P₂` at `T`, `T₁`, `T₂` be those of `S`. The function
`extendedBesselChar a` is the product of the same functions on `T₁` and `T₂`. -/
lemma extendedBesselChar_eq_mul_toPlacesProd (hψ : P.ψ = S.charOnPlaces T)
    (hψ₁ : P₁.ψ = S.charOnPlaces T₁) (hψ₂ : P₂.ψ = S.charOnPlaces T₂)
    (a : (LocProd T)ˣ) (x : U (S.latticeMiddle (LocProd T)).splitGram) :
    extendedBesselChar a x =
      extendedBesselChar (a.map (restrictPlaces h₁_sub)) (S.toPlacesProd h₁_sub h₂_sub x).1 *
        extendedBesselChar (a.map (restrictPlaces h₂_sub)) (S.toPlacesProd h₁_sub h₂_sub x).2 := by
  set e := S.toPlacesProd h₁_sub h₂_sub with he
  have h_mem (u : (S.latticeMiddle (LocProd T)).G) :
      u⁻¹ * x ∈ unitaryLevel integers a (S.latticeMiddle (LocProd T)).splitGram ↔
        (e u).1⁻¹ * (e x).1 ∈ unitaryLevel integers (a.map (restrictPlaces h₁_sub))
            (S.latticeMiddle (LocProd T₁)).splitGram ∧
          (e u).2⁻¹ * (e x).2 ∈ unitaryLevel integers (a.map (restrictPlaces h₂_sub))
            (S.latticeMiddle (LocProd T₂)).splitGram := by
    rw [unitaryLevel_eq_comap_toPlacesProd h₁_sub h₂_sub h_cov]
    simp only [he, Subgroup.mem_comap, Subgroup.mem_prod, MonoidHom.map_mul, MonoidHom.map_inv,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  -- On `besselU` times the congruence subgroup `extendedBesselChar` is a value of the character,
  -- which is a product.
  by_cases hx : ∃ u ∈ besselU,
      u⁻¹ * x ∈ unitaryLevel integers a (S.latticeMiddle (LocProd T)).splitGram
  · obtain ⟨u, hu, hux⟩ := hx
    have h_srs₁ : simpleRootSum (e u).1 = restrictPlaces h₁_sub (simpleRootSum u) := by
      simp only [simpleRootSum, map_sum]
      rfl
    have h_srs₂ : simpleRootSum (e u).2 = restrictPlaces h₂_sub (simpleRootSum u) := by
      simp only [simpleRootSum, map_sum]
      rfl
    have hu_bessel : (e u).1 ∈ besselU ∧ (e u).2 ∈ besselU :=
      (mem_besselU_iff_toPlacesProd h₁_sub h₂_sub h_cov).1 hu
    rw [extendedBesselChar_eq hu hux, extendedBesselChar_eq hu_bessel.1 ((h_mem u).1 hux).1,
      extendedBesselChar_eq hu_bessel.2 ((h_mem u).1 hux).2, hψ, hψ₁, hψ₂, h_srs₁, h_srs₂,
      charOnPlaces_eq_mul_restrictPlaces h₁_sub h₂_sub h_disj h_cov]
    simp only [Units.coe_map_inv, MonoidHom.coe_ofClass, map_mul]
  · -- If no factor vanished, the unipotent elements on `T₁` and `T₂` would glue to one over `T`.
    rw [extendedBesselChar_eq_zero hx, eq_comm, mul_eq_zero]
    contrapose! hx
    obtain ⟨u₁, hu₁, hx₁⟩ := exists_besselU_of_extendedBesselChar_ne_zero hx.1
    obtain ⟨u₂, hu₂, hx₂⟩ := exists_besselU_of_extendedBesselChar_ne_zero hx.2
    -- The elements `u₁` and `u₂` on `T₁` and `T₂` are the components of one element `u` over `T`.
    obtain ⟨u, hu_eq⟩ := toPlacesProd_surjective h₁_sub h₂_sub h_disj h_cov (u₁, u₂)
    have hu_bessel : u ∈ besselU :=
      (mem_besselU_iff_toPlacesProd h₁_sub h₂_sub h_cov).2 (by simpa only [hu_eq] using ⟨hu₁, hu₂⟩)
    have hu_cong : u⁻¹ * x ∈ unitaryLevel integers a (S.latticeMiddle (LocProd T)).splitGram :=
      (h_mem u).2 (by simpa only [he, hu_eq] using ⟨hx₁, hx₂⟩)
    exact ⟨u, hu_bessel, hu_cong⟩

variable
  {F₁ : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T₁))
    (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}
  {F₂ : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T₂))
    (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

/-- Let `F`, `F₁`, `F₂` be filling data at `T`, `T₁`, `T₂`, where `T₁` and `T₂` are disjoint
conjugation-stable subsets covering `T`. Then there is a constant `t` with the following property.
For any subgroups `A₁`, `A₂` of the unitary groups over `T₁`, `T₂`, let `Z` be their product, read
in the group over `T` through `S.toPlacesProd h₁_sub h₂_sub`. Then the volume `F.groupMeasure Z` is
`t` times the product of the volumes `F₁.groupMeasure A₁` and `F₂.groupMeasure A₂`. The mass
integral, `F.massIntegral Z` = ∫ |∫_Z χ_g(y x y⁻¹) dy|² dx, is `‖t.toReal‖ₑ ^ 2 * t` times the
product of the mass integrals of `A₁` and `A₂`.

This factor is `t ^ 3` for finite `t`. -/
lemma IsFillingData.exists_massIntegral_prod_eq
    (h : S.IsFillingData T F) (h₁ : S.IsFillingData T₁ F₁) (h₂ : S.IsFillingData T₂ F₂) :
    ∃ t : ℝ≥0∞, ∀ (A₁ : Subgroup (S.latticeMiddle (LocProd T₁)).G)
        (A₂ : Subgroup (S.latticeMiddle (LocProd T₂)).G),
      F.massIntegral ((A₁.prod A₂).comap (S.toPlacesProd h₁_sub h₂_sub)) =
        ‖t.toReal‖ₑ ^ 2 * t * (F₁.massIntegral A₁ * F₂.massIntegral A₂) ∧
      F.groupMeasure ((A₁.prod A₂).comap (S.toPlacesProd h₁_sub h₂_sub)) =
        t * (F₁.groupMeasure A₁ * F₂.groupMeasure A₂) := by
  set e := S.toPlacesProd h₁_sub h₂_sub
  have h_emb : MeasurableEmbedding e := measurableEmbedding_toPlacesProd h₁_sub h₂_sub h_cov
  have h_surj : Function.Surjective e := toPlacesProd_surjective h₁_sub h₂_sub h_disj h_cov
  -- The image of `F.groupMeasure` is right invariant, so a multiple of the product Haar measure.
  have _ : Measure.IsHaarMeasure F₁.groupMeasure := h₁.isHaarMeasure_groupMeasure
  have _ : Measure.IsHaarMeasure F₂.groupMeasure := h₂.isHaarMeasure_groupMeasure
  have _ : SigmaFinite F₁.groupMeasure := h₁.isHaarMeasure_groupMeasure.sigmaFinite
  have _ : SigmaFinite F₂.groupMeasure := h₂.isHaarMeasure_groupMeasure.sigmaFinite
  have h_inv : (F.groupMeasure.map e).IsMulRightInvariant :=
    ⟨h_surj.forall.2 fun x ↦ ((h_emb.measurable.measurePreserving _).of_semiconj
      (measurePreserving_mul_right _ x) (fun y ↦ e.map_mul y x) (by fun_prop)).map_eq⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0∞, F.groupMeasure.map e = t • F₁.groupMeasure.prod F₂.groupMeasure :=
    exists_eq_smul_haar _ h_inv
  refine ⟨t, fun A₁ A₂ ↦ ⟨?_, by rw [coe_comap, Subgroup.coe_prod, ← h_emb.map_apply, ht,
    smul_apply, Measure.prod_prod, smul_eq_mul]⟩⟩
  have h_phase (y : (S.latticeMiddle (LocProd T)).G) :
      extendedBesselChar F.levelUnit y =
        extendedBesselChar F₁.levelUnit (e y).1 * extendedBesselChar F₂.levelUnit (e y).2 := by
    rw [extendedBesselChar_eq_mul_toPlacesProd h₁_sub h₂_sub h_disj h_cov h.psi_eq h₁.psi_eq
      h₂.psi_eq, ← h.levelUnit_eq_map_restrictPlaces h₁_sub h₁,
      ← h.levelUnit_eq_map_restrictPlaces h₂_sub h₂]
  -- The inner integral gives the factor `t`: transport along `e`, then Fubini.
  have h_inner (x : (S.latticeMiddle (LocProd T)).G) :
      ∫ y in (A₁.prod A₂).comap e, extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure =
        t.toReal • ((∫ y₁ in A₁, extendedBesselChar F₁.levelUnit (y₁ * (e x).1 * y₁⁻¹)
            ∂F₁.groupMeasure) *
          ∫ y₂ in A₂, extendedBesselChar F₂.levelUnit (y₂ * (e x).2 * y₂⁻¹)
            ∂F₂.groupMeasure) := by
    rw [← integral_prod_mul, ← integral_smul_measure, Measure.prod_restrict,
      ← Measure.restrict_smul, ← ht, h_emb.setIntegral_map]
    simp only [coe_comap, Subgroup.coe_prod, h_phase, MonoidHom.map_mul, MonoidHom.map_inv,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  let f₁ (z : (S.latticeMiddle (LocProd T₁)).G) : ℝ≥0∞ :=
    ‖∫ y in A₁, extendedBesselChar F₁.levelUnit (y * z * y⁻¹) ∂F₁.groupMeasure‖ₑ ^ 2
  let f₂ (z : (S.latticeMiddle (LocProd T₂)).G) : ℝ≥0∞ :=
    ‖∫ y in A₂, extendedBesselChar F₂.levelUnit (y * z * y⁻¹) ∂F₂.groupMeasure‖ₑ ^ 2
  -- The outer integral gives one more factor `t`: transport, then Tonelli.
  have hf₁ : Measurable f₁ := (measurable_integral (by fun_prop)).eNorm.pow_const 2
  have hf₂ : Measurable f₂ := (measurable_integral (by fun_prop)).eNorm.pow_const 2
  rw [PlaceData.massIntegral]
  simp only [h_inner, mul_pow, eNorm_smul, eNorm_mul]
  rw [lintegral_const_mul' _ _ (by simp), ← h_emb.lintegral_map (f := fun z ↦ f₁ z.1 * f₂ z.2),
    ht, lintegral_smul_measure, lintegral_prod_mul hf₁.aemeasurable hf₂.aemeasurable,
    smul_eq_mul, mul_assoc]
  rfl

/-- Product law for intermediate groups across a disjoint conjugation-stable split `T = T₁ ⊔ T₂`
(expressed via `h₁_sub`, `h₂_sub`, `h_disj`, and `h_cov` rather than `T₁ ∪ T₂ = T` to avoid a
`DecidableEq (FinPlace E)` hypothesis in the signature). Given filling data `F`, `F₁`, `F₂` on `T`,
`T₁`, `T₂` and intermediate groups `Z₁`, `Z₂` on `T₁`, `T₂` with mass-ratio gains `c₁`, `c₂`,
pulling back `Z₁ × Z₂` along `S.toPlacesProd h₁_sub h₂_sub` gives an intermediate group `Z` on `T`
whose mass-ratio gain is `c₁ * c₂`. -/
lemma IsFillingData.exists_intermediateGroup_prod
    (h : S.IsFillingData T F) (h₁ : S.IsFillingData T₁ F₁) (h₂ : S.IsFillingData T₂ F₂)
    (Z₁ : F₁.IntermediateGroup) (Z₂ : F₂.IntermediateGroup) {c₁ c₂ : ℝ≥0∞}
    (h_le₁ : F₁.massIntegral Z₁ *
        F₁.groupMeasure (unitaryLevel P₁.integers 1 (S.latticeMiddle (LocProd T₁)).splitGram) *
        c₁ ≤
      F₁.massIntegral (unitaryLevel P₁.integers 1 _) * F₁.groupMeasure Z₁)
    (h_le₂ : F₂.massIntegral Z₂ *
        F₂.groupMeasure (unitaryLevel P₂.integers 1 (S.latticeMiddle (LocProd T₂)).splitGram) *
        c₂ ≤
      F₂.massIntegral (unitaryLevel P₂.integers 1 _) * F₂.groupMeasure Z₂) :
    ∃ Z : F.IntermediateGroup,
      Z.val = (Z₁.val.prod Z₂.val).comap (S.toPlacesProd h₁_sub h₂_sub) ∧
      F.massIntegral Z *
          F.groupMeasure (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
        (c₁ * c₂) ≤ F.massIntegral (unitaryLevel P.integers 1 _) * F.groupMeasure Z := by
  set e := S.toPlacesProd h₁_sub h₂_sub with he
  let K₁ := unitaryLevel P₁.integers 1 (S.latticeMiddle (LocProd T₁)).splitGram
  let K₂ := unitaryLevel P₂.integers 1 (S.latticeMiddle (LocProd T₂)).splitGram
  have hK : unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram =
      (K₁.prod K₂).comap e := by
    simpa only [he, K₁, K₂, map_one] using
      unitaryLevel_eq_comap_toPlacesProd h₁_sub h₂_sub h_cov (1 : (LocProd T)ˣ)
  have h_cong : F.congruenceSubgroup =
      (F₁.congruenceSubgroup.prod F₂.congruenceSubgroup).comap e := by
    simp only [he, PlaceData.congruenceSubgroup,
      unitaryLevel_eq_comap_toPlacesProd h₁_sub h₂_sub h_cov F.levelUnit,
      h.levelUnit_eq_map_restrictPlaces h₁_sub h₁, h.levelUnit_eq_map_restrictPlaces h₂_sub h₂]
  have h_between : (Z₁.val.prod Z₂.val).comap e ∈ Set.Icc F.congruenceSubgroup
      (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) := by
    rw [hK, h_cong]
    exact ⟨fun _ hx ↦ ⟨Z₁.prop.1 hx.1, Z₂.prop.1 hx.2⟩,
      fun _ hx ↦ ⟨Z₁.prop.2 hx.1, Z₂.prop.2 hx.2⟩⟩
  refine ⟨⟨(Z₁.val.prod Z₂.val).comap e, h_between⟩, rfl, ?_⟩
  dsimp only
  rw [hK]
  -- Mass integral and volume of a product are products, up to constants that agree on both sides.
  obtain ⟨t, h_prod⟩ := h.exists_massIntegral_prod_eq h₁_sub h₂_sub h_disj h_cov h₁ h₂
  calc F.massIntegral ((Z₁.val.prod Z₂.val).comap e) *
        F.groupMeasure ((K₁.prod K₂).comap e) * (c₁ * c₂)
    _ = ‖t.toReal‖ₑ ^ 2 * t * t *
        ((F₁.massIntegral Z₁ * F₁.groupMeasure K₁ * c₁) *
          (F₂.massIntegral Z₂ * F₂.groupMeasure K₂ * c₂)) := by
      rw [he, (h_prod Z₁ Z₂).1, (h_prod K₁ K₂).2]
      ring
    _ ≤ ‖t.toReal‖ₑ ^ 2 * t * t *
        ((F₁.massIntegral K₁ * F₁.groupMeasure Z₁) *
          (F₂.massIntegral K₂ * F₂.groupMeasure Z₂)) := by gcongr
    _ = F.massIntegral ((K₁.prod K₂).comap e) *
        F.groupMeasure ((Z₁.val.prod Z₂.val).comap e) := by
      rw [he, (h_prod K₁ K₂).1, (h_prod Z₁ Z₂).2]
      ring

end Measures

/-! ### Several places -/

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-- Let `S` be an admissible filling, `F` a filling datum at `T`, and let the inverse of the level
`S.ideleM` be integral off `T`. Let `Sg` be a set of chosen places above the first level prime
(index `0`) and let `d w = (ε, v)` prescribe, for each such place `w`, the frame vector with nonzero
coordinates `v` modulo `w` if `ε` is false and modulo its conjugate if `ε` is true; `S.fixer Sg d`
is the group that fixes these vectors for all `w` in `Sg`. Then some group `Z` between the
congruence subgroup `F.congruenceSubgroup` and the integral unitary group
`K = unitaryLevel P.integers 1 _` has two properties. (a) `Z` contains the `T`-component of every
integral element `k` whose reduction modulo the chosen places lies in `S.fixer Sg d`. (b) With
`ϰ = F.massIntegral` (the mass integral), `vol = F.groupMeasure` (a Haar measure) and `b = S.b`,
`ϰ(Z) vol(K) (b ^ (6 * 𝔰.k)) ^ #Sg ≤ ϰ(K) vol(Z)`. -/
theorem IsFillingData.exists_intermediateGroup_places [WeilData E] {S : Filling E 𝔰}
    [S.IsAdmissible] {T : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (h : S.IsFillingData T F)
    (Sg : Finset (S.chosenPlaces 0)) (d : ∀ w : S.chosenPlaces 0, S.FrameVector w)
    (hT : (↑S.ideleM⁻¹ : 𝔸f E) ∈ integralOff T) :
    ∃ Z : F.IntermediateGroup,
      -- (a)
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d → S.toPlaces T k ∈ Z.val) ∧
      -- (b)
      F.massIntegral Z *
            F.groupMeasure (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ^ #Sg ≤
        F.massIntegral (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          F.groupMeasure Z := by
  classical
  -- Induct on `Sg`, keeping only `∀ w ∈ Sg, (w : FinPlace E) ∈ T` so the complement inherits the
  -- hypothesis. In the base case take `Z = K`.
  have hw_mem : ∀ w ∈ Sg, (w : FinPlace E) ∈ T :=
    fun w _ ↦ mem_of_inv_ideleM_mem_integralOff hT w
  clear hT
  induction Sg using Finset.induction generalizing T with
  | empty =>
    exact ⟨⟨unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram,
      unitaryLevel_le_unitaryLevel_one, le_rfl⟩,
      fun k _ ↦ range_toPlaces_latticeStabilizer.le ⟨k, rfl⟩, by simp⟩
  | @insert w Sg hw ih =>
    -- Split `T` into `T₁ = T ∩ {w, star w}` and its complement `T₂` in `T`; both are
    -- conjugation-stable and disjoint.
    let p (j : FinPlace E) : Prop := j = (w : FinPlace E) ∨ star j = (w : FinPlace E)
    let T₁ := {j ∈ T | p j}
    let T₂ := {j ∈ T | ¬p j}
    have hp_star (j : FinPlace E) : p (star j) ↔ p j := by simp [p, or_comm]
    have _ : T₁.StarStable := ⟨by simp +contextual [T₁, fT.out, hp_star]⟩
    have _ : T₂.StarStable := ⟨by simp +contextual [T₂, fT.out, hp_star]⟩
    have h₁_sub : T₁ ⊆ T := filter_subset p T
    have h₂_sub : T₂ ⊆ T := filter_subset (¬p ·) T
    have h_disj : Disjoint T₁ T₂ := disjoint_filter_filter_not T T p
    have h_cov (j : FinPlace E) (hj : j ∈ T) : j ∈ T₁ ∨ j ∈ T₂ :=
      (Classical.em (p j)).imp (fun hpj ↦ mem_filter.2 ⟨hj, hpj⟩)
        (fun hpj ↦ mem_filter.2 ⟨hj, hpj⟩)
    -- Build filling data on `T₁` and `T₂`, then apply the one-place bound and the induction step.
    obtain ⟨P₁, F₁, h₁⟩ := S.exists_isFillingData T₁
    obtain ⟨P₂, F₂, h₂⟩ := S.exists_isFillingData T₂
    have hwT₁ : (w : FinPlace E) ∈ T₁ := mem_filter.2 ⟨hw_mem w (mem_insert_self w Sg), .inl rfl⟩
    have hT₁_sub : T₁ ⊆ S.chosenPlacesAndConj := fun j hj ↦
      mem_chosenPlacesAndConj.2 ⟨0, w, w.prop,
        (mem_filter.1 hj).2.imp_right fun h_eq ↦ by simp [← h_eq]⟩
    have hs_mem : ∀ s ∈ Sg, (s : FinPlace E) ∈ T₂ := by
      intro s hs
      refine mem_filter.2 ⟨hw_mem s (mem_insert_of_mem hs), ?_⟩
      rintro (h_eq | h_conj)
      · have hs_eq : s = w := Subtype.ext h_eq
        rw [hs_eq] at hs
        exact hw hs
      · have h_mem : star (s : FinPlace E) ∈ S.chosenPlaces 0 := by
          rw [h_conj]
          exact w.prop
        exact S.star_notMem_chosenPlaces s.prop h_mem
    obtain ⟨Z₁, hZ₁_mem, hZ₁_le⟩ := h₁.exists_intermediateGroup_one_place w (d w) hwT₁ hT₁_sub
    obtain ⟨Z₂, hZ₂_mem, hZ₂_le⟩ := ih h₂ hs_mem
    -- Pull back `Z₁ × Z₂` along `S.toPlacesProd` and multiply the one-place and induction gains.
    -- The product group contains `S.toPlaces T k` whenever `S.reduction k` fixes the vectors at
    -- `w` and at the places of `Sg`.
    obtain ⟨Z, hZ_eq, hZ_le⟩ :=
      h.exists_intermediateGroup_prod h₁_sub h₂_sub h_disj h_cov h₁ h₂ Z₁ Z₂ hZ₁_le hZ₂_le
    refine ⟨Z, fun k hk ↦ ?_, ?_⟩
    · rw [hZ_eq, Subgroup.mem_comap, toPlacesProd_toPlaces]
      exact ⟨hZ₁_mem k (mem_fixer.1 hk w (mem_insert_self w Sg)),
        hZ₂_mem k (mem_fixer.2 fun s hs ↦ mem_fixer.1 hk s (mem_insert_of_mem hs))⟩
    · rwa [card_insert_of_notMem hw, pow_succ']

end New.Filling
