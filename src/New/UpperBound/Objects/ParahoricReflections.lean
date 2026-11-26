module

public import Lib.LocalGL.Green.TauFunctions
public import New.UpperBound.Objects.AuxiliaryPair
import Lib.LocalGL.Green.LabelCharacters

/-!
# Parahoric block actions and hyperplane reflection sums

Let `O` be a descent pair (`New.DescentPair`) with index embedding `O.incl : r ↪ n`, chosen places,
twist places `Q`, and residue characters `χ_w = O.tamePart w`. Its level subgroup `O.levelGroup`
consists of the elements of the maximal level `stdLevel E n` whose reductions fix `(1, 0)ᵀ`
(`New.inclMatrix`) at the chosen places and lie in the opposite parabolic
`New.rangeParabolic O.incl` at the places of `Q`.

This file develops the finite-field hyperplane reflection sums and the parahoric block-triangular
action law of `O` independently of theta kernels, Weil representations, or `New.OneLift`, decoupling
Galois-representation parahoric type identification
(`New.Congruences.GaloisRepresentations.BaseLevelOfLabel`) from false-lift period vanishing
(`New.OneLift.FalseLifts`):

* Block extraction along `ι : r ↪ n` (`New.submatrix_inclMatrix`,
  `New.submatrix_eq_of_transpose_mul_inclMatrix`, `New.apply_eq_zero_of_transpose_mul_inclMatrix`).
* Finite-field hyperplane reflection groups `New.hyperplaneGroup l` of invertible matrices
  `1 + v l`, vanishing of twisted determinant sums `New.sum_inv_det_hyperplaneGroup_eq_zero`, and
  annihilation of the rank-`r` label idempotent of `X - 1` by `New.hyperplaneSum`
  (`New.hyperplaneSum_mul_labelIdem_X_sub_one`).
* The parahoric block-triangular action law
  `New.DescentPair.smul_chosenGLRep_eq_apply_of_triangular`, together with
  `New.DescentPair.blockAction`, `New.DescentPair.HyperplaneSumsAnnihilate`, and
  `New.DescentPair.sum_blockAction_eq_zero`.
-/

@[expose] public section

noncomputable section

namespace New

open Matrix NumberField Finset IsLocalRing Space stdLevel Gf Rows

section Blocks

variable {R r n : Type} [CommRing R] [Fintype r] [DecidableEq n] (ι : r ↪ n)

omit [Fintype r] in
/-- The rows `ι` of the matrix `inclMatrix R ι = (1, 0)ᵀ` form the identity matrix. -/
lemma submatrix_inclMatrix [DecidableEq r] [Fintype n] : (inclMatrix R ι).submatrix ι id = 1 := by
  rw [← inclMatrix_transpose_mul, inclMatrix_transpose_mul_self]

omit [Fintype r] in
lemma inclMatrix_apply_of_notMem_range {a : n} (ha : a ∉ Set.range ι) (b : r) :
    inclMatrix R ι a b = 0 :=
  one_apply_ne fun h : a = ι b ↦ ha ⟨b, h.symm⟩

variable [Fintype n]

/-- If `tᵀ e = e sᵀ` for `e = inclMatrix R ι = (1, 0)ᵀ`, the first block of `t` is `s`. -/
lemma submatrix_eq_of_transpose_mul_inclMatrix [DecidableEq r]
    {ι : r ↪ n} {t : Matrix n n R} {s : Matrix r r R}
    (hts : tᵀ * inclMatrix R ι = inclMatrix R ι * sᵀ) : t.submatrix ι ι = s := by
  have h_block : (tᵀ * inclMatrix R ι).submatrix ι id = sᵀ := by
    simp [hts, ← inclMatrix_transpose_mul, ← Matrix.mul_assoc]
  exact transpose_injective (by simpa [mul_inclMatrix] using h_block)

/-- If `tᵀ e = e sᵀ` for `e = inclMatrix R ι = (1, 0)ᵀ`, the upper right block of `t` is zero. -/
lemma apply_eq_zero_of_transpose_mul_inclMatrix {ι : r ↪ n} {t : Matrix n n R} {s : Matrix r r R}
    (hts : tᵀ * inclMatrix R ι = inclMatrix R ι * sᵀ) (a : r) {b : n} (hb : b ∉ Set.range ι) :
    t (ι a) b = 0 :=
  calc t (ι a) b = (inclMatrix R ι * sᵀ) b a := by simp [← hts, mul_inclMatrix]
    _ = 0 := by simp [Matrix.mul_apply, inclMatrix_apply_of_notMem_range ι hb]

end Blocks

section Hyperplane

variable {k r : Type} [Field k] [Fintype r] [DecidableEq r]

/-- The group of the invertible matrices `1 + v λ`, for a given row `λ = l` and all columns `v`. -/
def hyperplaneGroup (l : r → k) : Subgroup (GL r k) where
  carrier := {s : GL r k | ∃ v : r → k, s.val = 1 + vecMulVec v l}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro s t ⟨v, hv⟩ ⟨v', hv'⟩
    refine ⟨v + s.val *ᵥ v', ?_⟩
    rw [Units.val_mul, hv', mul_add, mul_one, mul_vecMulVec, add_vecMulVec, ← add_assoc, ← hv]
  inv_mem' := by
    rintro s ⟨v, hv⟩
    refine ⟨-(s⁻¹.val *ᵥ v), ?_⟩
    rw [neg_vecMulVec, ← mul_vecMulVec, eq_add_neg_iff_add_eq, ← s.inv_mul, hv, mul_add, mul_one]

lemma mem_hyperplaneGroup {l : r → k} {s : GL r k} :
    s ∈ hyperplaneGroup l ↔ ∃ v : r → k, (s : Matrix r r k) = 1 + vecMulVec v l := .rfl

/-- Over a finite field the group of the invertible `1 + v λ` is finite. -/
instance [Finite k] (l : r → k) : Fintype (hyperplaneGroup l) := .ofFinite _

/-- If the row `λ = l` is not zero and `χ ≠ 1`, the sum of `χ(det s)⁻¹` over the invertible matrices
`s = 1 + v λ` is zero. -/
lemma sum_inv_det_hyperplaneGroup_eq_zero [Finite k] {χ : MulChar k ℂ} (hχ : χ ≠ 1) {l : r → k}
    (hl : l ≠ 0) : ∑ s : hyperplaneGroup l, χ⁻¹ ((s : GL r k) : Matrix r r k).det = 0 := by
  -- The determinant `1 + λ v` is a homomorphism onto `kˣ`, so `χ⁻¹ ∘ det` is not trivial.
  let f : hyperplaneGroup l →* ℂ := χ⁻¹.toMonoidHom.comp
    (detMonoidHom.comp ((Units.coeHom (Matrix r r k)).comp (hyperplaneGroup l).subtype))
  have f_apply (s : hyperplaneGroup l) : f s = χ⁻¹ ((s : GL r k) : Matrix r r k).det := rfl
  refine sum_hom_units_eq_zero f fun hf : f = 1 ↦ ?_
  obtain ⟨τ, hτ⟩ : ∃ τ : kˣ, χ⁻¹ τ ≠ 1 := MulChar.ne_one_iff.1 (inv_ne_one.2 hχ)
  obtain ⟨b, hb⟩ : ∃ b : r, l b ≠ 0 := Function.ne_iff.1 hl
  let v : r → k := Pi.single b ((τ.val - 1) / l b)
  have h_det : (1 + vecMulVec v l).det = τ := by
    simp [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, v, mul_div_cancel₀ _ hb]
  let s : hyperplaneGroup l := ⟨.mk'' (1 + vecMulVec v l) (by simp [h_det]), v, rfl⟩
  have hs : f s = χ⁻¹ τ := by rw [f_apply, GeneralLinearGroup.val_mk'', h_det]
  exact hτ (by simp [← hs, hf])

open scoped Classical in
/-- The hyperplane sum `hyperplaneSum χ l` has the coefficient `χ(det s)⁻¹` at the invertible
matrices `s = 1 + v λ` for the row `λ = l`, and `0` elsewhere. -/
lemma coeff_hyperplaneSum_eq_ite [Finite k] (χ : MulChar k ℂ) (l : r → k) (s : GL r k) :
    (hyperplaneSum χ l).coeff s =
      if s ∈ hyperplaneGroup l then χ⁻¹ (s : Matrix r r k).det else 0 := by
  simp [hyperplaneSum, mem_hyperplaneGroup]

/-- The hyperplane sum `∑ χ(det s)⁻¹ s` over the invertible `s = 1 + v λ` is `1` for the zero row
`λ = 0`. -/
lemma hyperplaneSum_zero [Finite k] (χ : MulChar k ℂ) : hyperplaneSum χ (0 : r → k) = 1 := by
  ext s
  obtain rfl | hs := eq_or_ne s 1
  · simp [hyperplaneSum]
  · simp [hyperplaneSum, hs, MonoidAlgebra.one_def]

/-- In a representation `σ`, the hyperplane sum of a row `λ = l` acts as `∑ χ(det s)⁻¹ σ(s)` over
the invertible matrices `s = 1 + v λ`. -/
lemma asAlgebraHom_hyperplaneSum [Finite k] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL r k) V) (χ : MulChar k ℂ) (l : r → k) (y : V) :
    σ.asAlgebraHom (hyperplaneSum χ l) y =
      ∑ s : hyperplaneGroup l, χ⁻¹ ((s : GL r k) : Matrix r r k).det • σ (s : GL r k) y := by
  classical
  let : Fintype (GL r k) := .ofFinite _
  calc _ = ∑ s : GL r k, (hyperplaneSum χ l).coeff s • σ s y := by
        simp [Representation.asAlgebraHom_eq_sum]
    _ = ∑ s : GL r k with s ∈ hyperplaneGroup l, χ⁻¹ (s : Matrix r r k).det • σ s y := by
      simp [coeff_hyperplaneSum_eq_ite, sum_filter]
    _ = _ := sum_subtype _ (fun s ↦ mem_filter_univ s) _

/-- Let `k` be a finite field, `χ ≠ 1` a character of `kˣ` and `l ≠ 0` a row indexed by `r`. The
hyperplane sum `∑ χ(det s)⁻¹ s` over the invertible `s = 1 + u l`, an element of the group algebra
of `GL_r(k)`, annihilates the idempotent `labelIdem r (X - 1)` of the label `X - 1`. -/
lemma hyperplaneSum_mul_labelIdem_X_sub_one [Finite k] {χ : MulChar k ℂ} (hχ : χ ≠ 1)
    {l : r → k} (hl : l ≠ 0) :
    hyperplaneSum χ l * labelIdem r (Polynomial.X - 1 : Polynomial k) = 0 := by
  -- The character name of a nontrivial `χ` is not `1`, hence not a root of `X - 1`.
  refine hyperplaneSum_mul_labelIdem (fun h_root ↦ hχ ?_) hl
  have h_one : charName (faithfulChar k) χ = charName (faithfulChar k) 1 := by
    rw [map_one]
    exact Units.ext (sub_eq_zero.1 (by simpa using h_root))
  exact (charName (faithfulChar k)).injective h_one

end Hyperplane

namespace DescentPair

variable {E r n : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] {O : DescentPair E r n}

omit [DecidableEq n] in
/-- Let `O` be a descent pair, with two families of split finite places: the chosen places, indexed
by `O.ChosenIndex`, and the places of a second set `Q`, indexed by `O.TwistIndex`. Invertible
matrices `g j` at these places are the components of a finite adelic point `k` of the unitary group
that is `1` away from them and their conjugates. -/
lemma exists_atPlace_eq {m : Type*} [Fintype m] [DecidableEq m]
    (g : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL m (LocField (O.placeAt j))) :
    ∃ k ∈ supportedOn m O.places,
      ∀ j : O.ChosenIndex ⊕ O.TwistIndex, k.atPlace (O.placeAt j) = g j := by
  classical
  suffices h_mem : g ∈ (supportedOn m O.places).map (.pi fun j ↦ atPlace (O.placeAt j)) by
    simpa [funext_iff] using h_mem
  -- It suffices to reach the tuples with one non-trivial entry `g i`; these come from
  -- `ofSplitPlace`.
  refine Subgroup.pi_mem_of_mulSingle_mem g fun i ↦ ?_
  let k : Gf E m := ofSplitPlace (O.apart.star_ne i i) (g i)
  have hk_on : k ∈ supportedOn m O.places :=
    supportedOn_mono (Set.singleton_subset_iff.2 (Set.mem_range_self i))
      (ofSplitPlace_mem_supportedOn _ (g i))
  -- The other places `O.placeAt j` differ from `O.placeAt i` and from its conjugate.
  have hk_other (j) (hj : j ≠ i) : k.atPlace (O.placeAt j) = 1 :=
    atPlace_ofSplitPlace_of_ne _ (g i) (O.apart.injective.ne hj) (O.apart.star_ne j i)
  exact ⟨k, hk_on, Function.eq_update_iff.2 ⟨atPlace_ofSplitPlace _ (g i), hk_other⟩⟩

/-- Matrices `τ j` that are invertible over the local integers at the places `O.placeAt j` of `O`
are the components of an element of the maximal level `stdLevel E n`. -/
lemma exists_stdLevel_atPlace_eq
    (τ : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL n (LocInt (O.placeAt j))) :
    ∃ k : stdLevel E n, ∀ j : O.ChosenIndex ⊕ O.TwistIndex, k.val.atPlace (O.placeAt j) =
      GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype (τ j) := by
  obtain ⟨k, hk_on, hk_at⟩ := exists_atPlace_eq (O := O) fun j ↦
    GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype (τ j)
  have hk_int (j) : k.atPlace (O.placeAt j) ∈ localIntGL n (O.placeAt j) := ⟨τ j, (hk_at j).symm⟩
  exact ⟨⟨k, (mem_stdLevel_iff_of_supportedOn hk_on).2 (Set.forall_mem_range.2 hk_int)⟩, hk_at⟩

/-- Let `π` be a representation of `Gf E n`, the unitary group in `n` variables over the finite
adeles, and `y` a vector on which the group `O.levelGroup` acts by `O.levelChar`. Let `k` be in the
maximal level `stdLevel E n`, and let its reductions `τ_w` at the places of `O` be block triangular
with first block `s_w`: with `e = (1, 0)ᵀ = inclMatrix _ O.incl`, they are upper triangular at the
chosen places, `τ_w e = e s_w`, and lower triangular at `Q`, `τ_wᵀ e = e s_wᵀ`. Then
`π(k) y = χ(s)⁻¹ s̄ y`. Here the product `χ(s) = ∏ χ_w(det s_w)` is over both families, and `s̄` is
the part of `s` at the chosen places, which `O.chosenGLRep π` lets act by `∏ χ_w(det s_w)` times `π`
of a lift of `diag(s_w, 1)`. -/
lemma smul_chosenGLRep_eq_apply_of_triangular {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Gf E n) V} (y : levelSpace π O.levelGroup O.levelChar) (k : stdLevel E n)
    (s : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL r (ResField (O.placeAt j)))
    (h_upper : ∀ i : O.ChosenIndex, (stdLevel.reduceAt (O.placeAt (.inl i)) k).val *
      inclMatrix (ResField (O.placeAt (.inl i))) O.incl =
        inclMatrix (ResField (O.placeAt (.inl i))) O.incl * (s (.inl i)).val)
    (h_lower : ∀ i : O.TwistIndex, (stdLevel.reduceAt (O.placeAt (.inr i)) k).valᵀ *
      inclMatrix (ResField (O.placeAt (.inr i))) O.incl =
        inclMatrix (ResField (O.placeAt (.inr i))) O.incl * (s (.inr i)).valᵀ) :
    (∏ j : O.ChosenIndex ⊕ O.TwistIndex, (O.tamePart (O.placeAt j))⁻¹ (s j).val.det) •
      (O.chosenGLRep π (fun i : O.ChosenIndex ↦ s (.inl i)) y).val = π k y := by
  -- Let `τ` be the family of reductions of `k`, and let `σ` be `diag (s j, 1)` at the chosen
  -- places and `1` at `Q`. Then `σ⁻¹ * τ` lies in the level, so for the lift `k₀` of `σ` the
  -- element `k₀⁻¹ * k` acts on `y` by the level character.
  let τ : ∀ j, GL n (ResField (O.placeAt j)) := reduceFamily O.placeAt k
  let σ : ∀ j, GL n (ResField (O.placeAt j)) :=
    firstBlockHom O.toLevelPlaces O.incl fun i ↦ s (.inl i)
  have h_twist (i : O.TwistIndex) : (σ⁻¹ * τ) (.inr i) = τ (.inr i) := by
    rw [Pi.mul_apply, Pi.inv_apply, show σ (.inr i) = 1 from rfl, inv_one, one_mul]
  have h_level : σ⁻¹ * τ ∈ descentResidueLevel O.toLevelPlaces O.incl := by
    rintro (i | i) -
    · -- At a chosen place both `τ` and `σ` send `(1, 0)ᵀ` to its product with `s`.
      let e : Matrix n r (ResField (O.placeAt (.inl i))) := inclMatrix _ O.incl
      have h_eq : (τ (.inl i)).val * e = (σ (.inl i)).val * e :=
        (h_upper i).trans (extendGL_mul_inclMatrix O.incl (s (.inl i))).symm
      have h_fix : (σ (.inl i))⁻¹.val * (τ (.inl i)).val * e = e := by
        rw [Matrix.mul_assoc, h_eq, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      exact mem_stabilizer_col_iff.2 h_fix
    · rw [h_twist]
      exact (mem_rangeParabolic_iff O.incl).2 fun a b hb ↦
        apply_eq_zero_of_transpose_mul_inclMatrix (h_lower i) a hb
  let k₀ : stdLevel E n := liftResidue σ
  let c : ℂ := ∏ i : O.TwistIndex, (O.tamePart (O.placeAt (.inr i)))⁻¹ (s (.inr i)).val.det
  have h_char : O.residueLevelChar ⟨σ⁻¹ * τ, h_level⟩ = c := by
    refine prod_congr rfl fun i _ ↦ ?_
    have h_first : (τ (.inr i)).val.submatrix O.incl O.incl = (s (.inr i)).val :=
      submatrix_eq_of_transpose_mul_inclMatrix (h_lower i)
    change (O.tamePart (O.placeAt (.inr i)))⁻¹
      (((σ⁻¹ * τ) (.inr i)).val.submatrix O.incl O.incl).det = _
    rw [h_twist, h_first]
  have h_act : π (k₀⁻¹ * k).val y = O.residueLevelChar ⟨σ⁻¹ * τ, h_level⟩ • y.val :=
    levelSpace_levelOf_apply y.prop _ _ (by simp [k₀, τ, reduceFamily_liftResidue])
  -- The factors at the chosen places cancel the scalar `d` in the definition of `chosenGLRep`.
  let d : ℂ := ∏ i : O.ChosenIndex, O.tamePart (O.placeAt (.inl i)) (s (.inl i)).val.det
  have h_rep : (O.chosenGLRep π (fun i ↦ s (.inl i)) y).val = d • π k₀ y := rfl
  have h_cancel : (∏ j, (O.tamePart (O.placeAt j))⁻¹ (s j).val.det) * d = c := by
    rw [Fintype.prod_sum_type, mul_right_comm, ← prod_mul_distrib, prod_eq_one, one_mul]
    intro i _
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (s (.inl i)).det_ne_zero.isUnit]
  calc _ = c • π k₀ y := by rw [h_rep, smul_smul, h_cancel]
    _ = π k₀ (π (k₀⁻¹ * k).val y) := by rw [h_act, h_char, map_smul]
    _ = π k y := by simp

/-- The form `χ(s)⁻¹ s̄ y` for blocks `s` at the chosen places and the places of `Q`, where
`χ(s) = ∏ χ_w(det s_w)` over all these places and `s̄` is the part of `s` at the chosen places. -/
def blockAction (O : DescentPair E r n)
    (s : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL r (ResField (O.placeAt j))) (y : O.FormV) :
    O.FormV :=
  (∏ j : O.ChosenIndex ⊕ O.TwistIndex, (O.tamePart (O.placeAt j))⁻¹ (s j).val.det) •
    O.formAction (fun i : O.ChosenIndex ↦ s (Sum.inl i)) y

/-- The hyperplane sums annihilate the form `y`: for rows `λ_w` at the chosen places `w`, not all
zero, the product of the sums `∑ χ_w(det s)⁻¹ s` over the invertible `s = 1 + v λ_w` kills `y`. -/
def HyperplaneSumsAnnihilate (O : DescentPair E r n) [DecidableEq O.ChosenIndex] (y : O.FormV) :
    Prop :=
  ∀ (i : O.ChosenIndex) (l : ∀ j : O.ChosenIndex, r → ResField (O.chosenPlace j)),
    l i ≠ 0 → O.formAction.asAlgebraHom
      (piTensorElem fun j : O.ChosenIndex ↦ hyperplaneSum (O.tamePart (O.chosenPlace j)) (l j)) y =
        0

section

variable [DecidableEq O.ChosenIndex]

/-- A descent pair `O` has two families of split places, the chosen places and a set `Q`, residue
characters `χ_w = O.tamePart w`, and a space `O.FormV` of forms on its space `V` of rank `n` with a
fixed weight and level. For a row `λ` over the residue field `k_w` of a chosen place `w`, the
hyperplane sum is `∑ χ_w(det s)⁻¹ s` over the group `hyperplaneGroup λ` of the invertible matrices
`s = 1 + v λ`, with `v` any column. The group `∏_w GL_r(k_w)` acts on these forms by
`O.formAction`: `(s_w)` acts as `∏_w χ_w(det s_w)` times right translation by an element of the
maximal level whose reductions are `diag(s_w, 1)` at the chosen places and `1` at `Q`. Suppose that
the product of the hyperplane sums of rows `λ_w`, not all zero, always kills `y`. Then the
hyperplane sum of `l ≠ 0` at the place of index `i` alone kills `y`. -/
lemma sum_formAction_mulSingle_eq_zero {y : O.FormV} (h_sums : O.HyperplaneSumsAnnihilate y)
    (i : O.ChosenIndex) {l : r → ResField (O.chosenPlace i)} (hl : l ≠ 0) :
    ∑ s : hyperplaneGroup l,
      (O.tamePart (O.chosenPlace i))⁻¹ s.val.val.det • O.formAction (Pi.mulSingle i s.val) y =
        0 := by
  -- Take the row `l` at the place `O.chosenPlace i` and the zero row, whose hyperplane sum is `1`,
  -- at the other chosen places.
  let rows : ∀ j : O.ChosenIndex, r → ResField (O.chosenPlace j) := Pi.single i l
  have h_family : (fun j ↦ hyperplaneSum (O.tamePart (O.chosenPlace j)) (rows j)) =
      Pi.mulSingle i (hyperplaneSum (O.tamePart (O.chosenPlace i)) l) := by
    ext1 j
    obtain rfl | hj := eq_or_ne j i <;> simp [rows, hyperplaneSum_zero, *]
  have h_sum : O.formAction.asAlgebraHom
      (piTensorElem fun j ↦ hyperplaneSum (O.tamePart (O.chosenPlace j)) (rows j)) y = 0 :=
    h_sums i rows (by simpa [rows] using hl)
  rwa [h_family, asAlgebraHom_piTensorElem_mulSingle, asAlgebraHom_hyperplaneSum] at h_sum

/-- For a block `s` at the single place `O.placeAt j` of index `j`, `O.blockAction` sends `y` to
`χ_w(det s)⁻¹` times `O.formAction` of the chosen-place part of `Pi.mulSingle j s` applied to `y`,
where `χ_w = O.tamePart (O.placeAt j)`. -/
lemma blockAction_mulSingle [DecidableEq O.TwistIndex] (j : O.ChosenIndex ⊕ O.TwistIndex)
    (s : GL r (ResField (O.placeAt j))) (y : O.FormV) :
    O.blockAction (Pi.mulSingle j s) y = (O.tamePart (O.placeAt j))⁻¹ s.val.det •
      O.formAction (fun i : O.ChosenIndex ↦
        Pi.mulSingle (M := fun j' : O.ChosenIndex ⊕ O.TwistIndex ↦ GL r (ResField (O.placeAt j')))
          j s (Sum.inl i)) y := by
  rw [blockAction, Fintype.prod_eq_single j fun i hi ↦ by simp [Pi.mulSingle_eq_of_ne hi],
    Pi.mulSingle_eq_same]

/-- Let `w = O.placeAt (.inl i)` be the chosen place of index `i`, and `s` in `GL_r` of its residue
field. Then `O.blockAction` of the block `s` at `w` (and `1` elsewhere) on the form `y` is
`χ_w(det s)⁻¹` times `O.formAction` of `s` at `w` on `y`. -/
lemma blockAction_mulSingle_inl [DecidableEq O.TwistIndex] (i : O.ChosenIndex)
    (s : GL r (ResField (O.placeAt (.inl i)))) (y : O.FormV) :
    O.blockAction (Pi.mulSingle (.inl i) s) y =
      (O.tamePart (O.placeAt (.inl i)))⁻¹ s.val.det • O.formAction (Pi.mulSingle i s) y := by
  -- `Pi.mulSingle` is an update of `1`, and updates commute with restriction along `Sum.inl`.
  have h_part : (fun i' : O.ChosenIndex ↦ Pi.mulSingle
      (M := fun j ↦ GL r (ResField (O.placeAt j))) (.inl i) s (.inl i')) = Pi.mulSingle i s :=
    Function.update_comp_eq_of_injective' (β := fun j ↦ GL r (ResField (O.placeAt j))) 1
      Sum.inl_injective i s
  rw [blockAction_mulSingle, h_part]
  rfl

/-- For a block `s` at the place `O.placeAt (.inr i)` of `Q` and the identity at the other places,
`O.blockAction` sends `y` to `(O.tamePart (O.placeAt (.inr i)))⁻¹ (det s) • y`. -/
lemma blockAction_mulSingle_inr [DecidableEq O.TwistIndex] (i : O.TwistIndex)
    (s : GL r (ResField (O.placeAt (.inr i)))) (y : O.FormV) :
    O.blockAction (Pi.mulSingle (.inr i) s) y = (O.tamePart (O.placeAt (.inr i)))⁻¹ s.val.det •
      y := by
  have h_one : (fun i' : O.ChosenIndex ↦ Pi.mulSingle
      (M := fun j ↦ GL r (ResField (O.placeAt j))) (.inr i) s (.inl i')) = (1 : O.ChosenGL r) :=
    funext fun _ ↦ Pi.mulSingle_eq_of_ne Sum.inl_ne_inr _
  rw [blockAction_mulSingle, h_one, map_one, one_apply_eq_self]

/-- Assume `χ_w ≠ 1` for `w ∈ Q`. Assume also `O.HyperplaneSumsAnnihilate y`: for rows `λ_w` at the
chosen places, not all zero, the product of the sums `∑ χ_w(det s)⁻¹ s` kills `y`, with
`s = 1 + v λ_w` invertible and `v` any column. Then at `w = O.placeAt j` and for a row `l ≠ 0`, the
sum of `O.blockAction s y = χ_w(det s)⁻¹ s̄ y` over `s` in `hyperplaneGroup l` is zero. Here `s̄` is
`s` at a chosen place and `1` at a place of `Q`. -/
lemma sum_blockAction_eq_zero {y : O.FormV} [DecidableEq O.TwistIndex]
    (hQ : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    (h_sums : O.HyperplaneSumsAnnihilate y) (j : O.ChosenIndex ⊕ O.TwistIndex)
    {l : r → ResField (O.placeAt j)} (hl : l ≠ 0) :
    ∑ s : hyperplaneGroup l, O.blockAction (Pi.mulSingle j s.val) y = 0 := by
  obtain i | i := j
  · simp_rw [blockAction_mulSingle_inl]
    exact sum_formAction_mulSingle_eq_zero h_sums i hl
  · -- At a place of `Q` a character sum remains.
    have hχ : O.tamePart (O.placeAt (.inr i)) ≠ 1 := hQ i
    simp_rw [blockAction_mulSingle_inr]
    rw [← sum_smul, sum_inv_det_hyperplaneGroup_eq_zero hχ hl, zero_smul]

end

end DescentPair

end New

end
