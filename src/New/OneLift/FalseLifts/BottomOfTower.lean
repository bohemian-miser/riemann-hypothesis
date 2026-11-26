module

import Mathlib.NumberTheory.MulChar.Lemmas
public import Lib.Weil.Periods.DescentVanishing
public import New.UpperBound.Objects.ParahoricReflections
import Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic
import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.General.LinearAlgebra.HermiteForm

/-!
# The bottom of the tower: from the block datum to all data

Let `O` be a descent pair with spaces `W` and `V`, and let `y` be a form on `V` whose descents to
`W` by the data `v_P ⊗ Ψ_bl ⊗ vac` vanish, where `v_P` is the Fock vector of a polynomial `P` and
`Ψ_bl` is the block datum. Suppose that the characters `χ_w` at the places of `Q` are not trivial
and that the hyperplane sums at the chosen places annihilate `y`. This file proves that the descents
vanish for all data that are the vacuum at the finite places other than the chosen places, the
places of `Q` and their conjugates (`DescentPair.descentsVanish_of_hyperplaneSumsAnnihilate`). By
the descents of `y` we mean those of the matrix coefficient of `y` for a fixed linear form `u`.

By `New.IsSchwartzBruhat.mem_of_cosets` it suffices to treat the indicator
`cosetIndicator O.places t z` of the class around each point `z` modulo any integral idele `t`:
* At each place `w = O.placeAt j`, stack `z_w` (with rows outside `O.incl` scaled by a uniformiser
  when `w ∈ Q`) above `t_w I_r` and apply Hermite reduction
  (`exists_annihilator_or_congr_inclMatrix`, `DescentPair.exists_annihilator_or_congr_at_places`).
* In the congruent case (`DescentPair.descentPairing_eq_zero_of_congr`), right-multiplying by an
  invertible `A` makes `Ψ₀ = O.translatedBlockFn A` equal `1` at `z` and constant on `t`-cosets
  (`IsSchwartzBruhat.eq_sum_cosetIndicator`); column completions (`completeColumns`) lift every
  nonzero coset in the support of `Ψ₀` back to the base coset `e A⁻¹` via `O.levelGroup`
  (`DescentPair.exists_leftMul_eq_of_translatedBlockFn_ne_zero`).
* Otherwise (`DescentPair.descentPairing_eq_zero_of_annihilatingRow`), an integral row `l`
  annihilating `z` modulo `t` yields row shears (`rowShear`) preserving the `t`-coset of `z` whose
  sum over `hyperplaneGroup` annihilates `y`.

The pair `O` carries two families of split finite places, the chosen places and the places of `Q`,
indexed by `O.ChosenIndex` and `O.TwistIndex`. The family `O.placeAt` lists all these places, and
`O.places` is their set. The pair also carries the space `W = O.W` of rank `r`, an embedding
`O.incl : r ↪ n` and the residue characters `χ_w = O.tamePart w`. The space `V` is `stdSpace E n`,
and `O.FormV` are the forms on `V` of the level of `O`. The level group `O.levelGroup` consists of
the elements of the maximal level whose reductions fix `(1, 0)ᵀ` at the chosen places and are block
lower triangular at the places of `Q`. For an `n × r` matrix `x` we write `x'` for the square block
of the rows `O.incl` and `x''` for the block of the other rows.

The field `E` is CM and carries Weil data (`WeilData E`): a purely imaginary element, a finite idele
and a splitting character, from which the Weil representation is defined.

Notions from other files:
* `New.Space.lift` for the swapped kernel goes from `U(V)` to `U(W)`; the descent of `y` is the
  conjugate of this lift of the conjugate of `y`.
* `New.Space.schrodingerOp`: for a set `S` of split places, `schrodingerOp V S Ψ f` is the vector of
  the Weil representation with the function `Ψ` of finite adelic vectors above `S` and `f`
  elsewhere; `New.Space.integrated` sets the component at infinity, and `New.Space.vacElem` is the
  vacuum.
* `New.cosetIndicator`: `cosetIndicator S t z` is the indicator function of the `x` such that
  `t⁻¹ (x - z)` is integral at every place of `S`.
* `New.DescentPair.blockDatum` is the vector `Ψ_bl ⊗ vac`. The function `Ψ_bl` of a finite adelic
  `n × r` matrix `x` is `∏_{w ∈ Q} χ_w(det x' mod w)` if `x` is integral at all places of `O` and
  `≡ (1, 0)ᵀ` (`New.inclMatrix`) at the chosen places, and `0` otherwise.
* `New.DescentPair.formAction` is the action `s̄ y` on forms of the product of the groups `GL r`
  over the residue fields of the chosen places.
-/

@[expose] public section

noncomputable section

namespace New

open Matrix NumberField Finset IsLocalRing Valued Space stdLevel Gf SiegelWeil Fock Rows

section Blocks

variable {R R' r n : Type} [CommRing R] [CommRing R'] [Fintype r] [DecidableEq n] (ι : r ↪ n)

/-- The vector `inclMatrix R ι *ᵥ μ = (μ, 0)` has the entry `μ b` at the index `ι b`. -/
lemma inclMatrix_mulVec_apply_embedding [DecidableEq r] (μ : r → R) (b : r) :
    (inclMatrix R ι *ᵥ μ) (ι b) = μ b := by
  simp [inclMatrix, mulVec, dotProduct, Matrix.one_apply]

lemma inclMatrix_mulVec_apply_of_notMem_range (μ : r → R) {a : n} (ha : a ∉ Set.range ι) :
    (inclMatrix R ι *ᵥ μ) a = 0 := by
  simp [mulVec, dotProduct, inclMatrix_apply_of_notMem_range ι ha]

/-- The row `inclMatrix R ι *ᵥ μ`, which is `μ` at the indices `ι` and `0` elsewhere, times `x`
equals `μ` times the rows `ι` of `x`, that is, `μ ᵥ* x.submatrix ι id`. -/
lemma inclMatrix_mulVec_vecMul [Fintype n] (μ : r → R) (x : Matrix n r R) :
    (inclMatrix R ι *ᵥ μ) ᵥ* x = μ ᵥ* x.submatrix ι id := by
  rw [← vecMul_transpose, vecMul_vecMul, inclMatrix_transpose_mul]

/-- The square matrix `(u' 0; u'' 1)`: its columns `ι` are the columns of `u`, and its other columns
are those of the identity matrix. -/
def completeColumns (u : Matrix n r R) : Matrix n n R :=
  1 + (u - inclMatrix R ι) * (inclMatrix R ι)ᵀ

/-- The columns `ι` of `(u' 0; u'' 1)` are the columns of `u`. -/
lemma completeColumns_mul_inclMatrix [DecidableEq r] [Fintype n] (u : Matrix n r R) :
    completeColumns ι u * inclMatrix R ι = u := by
  simp [completeColumns, Matrix.add_mul, Matrix.mul_assoc]

/-- The determinant of `completeColumns ι u = (u' 0; u'' 1)` is that of `u' = u.submatrix ι id`, the
block of the rows `ι` of `u`. -/
lemma det_completeColumns [DecidableEq r] [Fintype n] (u : Matrix n r R) :
    (completeColumns ι u).det = (u.submatrix ι id).det := by
  rw [completeColumns, det_one_add_mul_comm, Matrix.mul_sub, inclMatrix_transpose_mul_self,
    add_sub_cancel, inclMatrix_transpose_mul]

/-- The upper right block of `completeColumns ι u = (u' 0; u'' 1)` is zero: its entry at row `ι a`
and column `b` outside the range of `ι` is `0`. -/
lemma completeColumns_apply_of_notMem [DecidableEq r]
    (u : Matrix n r R) (a : r) {b : n} (hb : b ∉ Set.range ι) :
    completeColumns ι u (ι a) b = 0 := by
  have h_ne (c : r) : ι c ≠ b := fun h ↦ hb ⟨c, h⟩
  simp [completeColumns, inclMatrix, Matrix.mul_apply, Matrix.one_apply, h_ne]

lemma map_completeColumns (f : R →+* R') (u : Matrix n r R) :
    (completeColumns ι u).map f = completeColumns ι (u.map f) := by
  ext a b
  simp [completeColumns, inclMatrix, Matrix.mul_apply, Matrix.one_apply, apply_ite f]

variable [Fintype n]

omit [Fintype r] in
lemma vecMul_inclMatrix (l : n → R) : l ᵥ* inclMatrix R ι = l ∘ ι := by
  ext b
  simp [inclMatrix, vecMul, dotProduct, Matrix.one_apply]

/-- The matrix `h_v = (1 + v λ, v λ'; 0, 1)` of a column `v` and a row `l = (λ, λ')`, where `λ` has
the entries of `l` indexed by `ι` and `λ'` has the other entries. -/
def rowShear (v : r → R) (l : n → R) : Matrix n n R := 1 + vecMulVec (inclMatrix R ι *ᵥ v) l

/-- Multiplying `x` on the left by `rowShear ι v l` adds the rank-one matrix
`vecMulVec (inclMatrix R ι *ᵥ v) (l ᵥ* x)` to `x`. -/
lemma rowShear_mul (v : r → R) (l : n → R) (x : Matrix n r R) :
    rowShear ι v l * x = x + vecMulVec (inclMatrix R ι *ᵥ v) (l ᵥ* x) := by
  simp [rowShear, Matrix.add_mul, vecMulVec_mul]

/-- The matrix `rowShear ι v l` is block upper triangular with first block `1 + v λ`, where
`λ = l ∘ ι`. -/
lemma rowShear_mul_inclMatrix [DecidableEq r] (v : r → R) (l : n → R) :
    rowShear ι v l * inclMatrix R ι = inclMatrix R ι * (1 + vecMulVec v (l ∘ ι)) := by
  simp [rowShear, Matrix.add_mul, Matrix.mul_add, vecMulVec_mul, mul_vecMulVec, vecMul_inclMatrix]

/-- The matrix `rowShear ι v l` is `1 + (v, 0)ᵀ l`, the identity plus the product of the column `v`,
extended by zero along `ι`, with the row `l`. If `l` vanishes outside the range of `ι`, it is block
lower triangular with first block `1 + v λ`, where `λ = l ∘ ι` and `inclMatrix R ι = (1, 0)ᵀ`. -/
lemma transpose_rowShear_mul_inclMatrix [DecidableEq r] (v : r → R) {l : n → R}
    (hl : ∀ a : n, a ∉ Set.range ι → l a = 0) :
    (rowShear ι v l)ᵀ * inclMatrix R ι = inclMatrix R ι * (1 + vecMulVec v (l ∘ ι))ᵀ := by
  have h_col : (inclMatrix R ι *ᵥ v) ᵥ* inclMatrix R ι = v := by
    rw [inclMatrix_mulVec_vecMul, submatrix_inclMatrix, vecMul_one]
  have h_row : inclMatrix R ι *ᵥ (l ∘ ι) = l := by
    ext a
    obtain ⟨b, rfl⟩ | ha : a ∈ Set.range ι ∨ a ∉ Set.range ι := Classical.em _
    · simp [inclMatrix_mulVec_apply_embedding]
    · rw [inclMatrix_mulVec_apply_of_notMem_range ι _ ha, hl a ha]
  calc
    _ = inclMatrix R ι + vecMulVec l v := by simp [rowShear, Matrix.add_mul, vecMulVec_mul, h_col]
    _ = _ := by simp [Matrix.mul_add, mul_vecMulVec, h_row]

/-- The determinant of `rowShear ι v l` is that of its first block `1 + v λ`, where `λ = l ∘ ι`. -/
lemma det_rowShear [DecidableEq r] (v : r → R) (l : n → R) :
    (rowShear ι v l).det = (1 + vecMulVec v (l ∘ ι)).det := by
  simp [rowShear, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_mulVec,
    vecMul_inclMatrix]

omit [Fintype n] in
lemma map_rowShear (f : R →+* R') (v : r → R) (l : n → R) :
    (rowShear ι v l).map f = rowShear ι (f ∘ v) (f ∘ l) := by
  ext a b
  simp [rowShear, inclMatrix, mulVec, dotProduct, vecMulVec_apply, Matrix.one_apply, apply_ite f]

end Blocks

section LocalAnnihilator

variable {E r m : Type} [Field E] [NumberField E] [Fintype r] [DecidableEq r] [Fintype m]
  [DecidableEq m] {w : FinPlace E}

/-- Let `x` be a left-invertible `m × r` matrix over `LocField w` and `ι : r ↪ m` an embedding of
row indices. By Hermite reduction over `LocInt w`, there is an integral `m × m` matrix `l` with
`l x = 0` such that if the `ι`-columns of every row of `l` vanish modulo `w`, then `x a` is
congruent modulo `w` to `inclMatrix _ ι` for some `a ∈ GL_r(LocField w)`. -/
lemma exists_annihilator_or_congr_inclMatrix (ι : r ↪ m) (x : Matrix m r (LocField w))
    (hx : HasLeftInv x) :
    ∃ l : Matrix m m (LocInt w), l.map (LocInt w).subtype * x = 0 ∧
      ((∀ c : m, (fun d : r ↦ residue (LocInt w) (l c (ι d))) = 0) →
        ∃ a : GL r (LocField w), ∀ (c : m) (d : r),
          v ((x * a.val) c d - inclMatrix (LocField w) ι c d) < 1) := by
  -- Factor `x` over `LocInt w` into a primitive integral matrix `P = x b` with integral left
  -- inverse `L`; then `M = P L - 1` is an integral annihilator of `x`.
  obtain ⟨b, -, hX_int, L', hL_int, hL'⟩ :=
    (isValuationPair_valuationSubring (LocInt w)).exists_isPrimitiveMatrix_mul hx
  let P : Matrix m r (LocInt w) := fun i j ↦ ⟨(x * b.val) i j, hX_int i j⟩
  let L : Matrix r m (LocInt w) := fun i j ↦ ⟨L' i j, hL_int i j⟩
  have hP : P.map (LocInt w).subtype = x * b.val := rfl
  have hL : L.map (LocInt w).subtype = L' := rfl
  have hLP : L * P = 1 :=
    Matrix.map_injective (LocInt w).subtype_injective <| by
      dsimp only
      rw [Matrix.map_mul, hL, hP, hL', Matrix.map_one _ (map_zero _) (map_one _)]
  let M : Matrix m m (LocInt w) := P * L - 1
  refine ⟨M, ?_, fun h_zero ↦ ?_⟩
  · have h_sub : M.map (LocInt w).subtype * P.map (LocInt w).subtype = 0 := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, ← Matrix.map_mul, Matrix.mul_assoc, hLP,
        Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, sub_self]
    rw [show x = P.map (LocInt w).subtype * b⁻¹.val by
      rw [hP, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one], ← Matrix.mul_assoc, h_sub,
      Matrix.zero_mul]
  · -- The block `L₀ = L.submatrix id ι` is invertible over `LocInt w` because
    -- `(P.submatrix ι id) * L₀` reduces to the identity over `ResField w`.
    let L₀ : Matrix r r (LocInt w) := L.submatrix id ι
    have h_res (c : m) (d : r) :
        residue (LocInt w) ((P * L₀) c d) = residue (LocInt w) (inclMatrix (LocInt w) ι c d) := by
      have h0 : residue (LocInt w) (M c (ι d)) = 0 := congrFun (h_zero c) d
      rw [show M c (ι d) = (P * L₀) c d - inclMatrix (LocInt w) ι c d by
        simp [M, L₀, Matrix.mul_apply, inclMatrix, Matrix.one_apply], map_sub, sub_eq_zero] at h0
      exact h0
    have h_top : (P.submatrix ι id * L₀).map (residue (LocInt w)) = 1 := by
      ext d₁ d₂
      simpa [L₀, Matrix.mul_apply, inclMatrix, Matrix.one_apply] using h_res (ι d₁) d₂
    have h_det_one : residue (LocInt w) (P.submatrix ι id).det * residue (LocInt w) L₀.det = 1 := by
      simpa [← RingHom.mapMatrix_apply, ← RingHom.map_det] using congrArg Matrix.det h_top
    -- Lift `L₀` to `T ∈ GL_r(LocInt w)`, so `a = b * T` sends `x` to `P * L₀ ≡ inclMatrix mod w`.
    let T : GL r (LocInt w) := .mk'' L₀
      ((isUnit_map_iff (residue (LocInt w)) L₀.det).1 (.of_mul_eq_one_right _ h_det_one))
    refine ⟨b * GeneralLinearGroup.map (LocInt w).subtype T, fun c d ↦ ?_⟩
    have h_mat : x * (b * GeneralLinearGroup.map (LocInt w).subtype T).val =
        (P * L₀).map (LocInt w).subtype := by
      change x * (b.val * L₀.map (LocInt w).subtype) = _
      rw [← Matrix.mul_assoc, ← hP, ← Matrix.map_mul]
    rw [congrFun₂ h_mat c d, ← map_inclMatrix (LocInt w).subtype]
    exact residue_eq_iff_valuation_sub_lt_one.1 (h_res c d)

/-- Two finite adelic matrices whose local differences at all places `w i` have valuation `< 1`
have the same `residueDatum`. -/
lemma residueDatum_eq_of_valuation_sub_lt_one {ι n' n : Type*} [Fintype n'] [Fintype n]
    (w : ι → FinPlace E) (f : ((i : ι) → Matrix n' n (ResField (w i))) → ℂ)
    {x y : n' × n → 𝔸f E}
    (h_close : ∀ (i : ι) (p : n' × n), v (y p (w i) - x p (w i)) < 1) :
    residueDatum w f y = residueDatum w f x := by
  have h_mem (i : ι) (p : n' × n) : y p (w i) ∈ LocInt (w i) ↔ x p (w i) ∈ LocInt (w i) := by
    rw [← add_sub_cancel (x p (w i)) (y p (w i))]
    exact add_mem_cancel_right (h_close i p).le
  by_cases hx : ∀ (i : ι) (p : n' × n), x p (w i) ∈ LocInt (w i)
  · have hy : ∀ (i : ι) (p : n' × n), y p (w i) ∈ LocInt (w i) := fun i p ↦ (h_mem i p).2 (hx i p)
    rw [residueDatum, residueDatum, ite_eq_left hy, ite_eq_left hx]
    congr with i a b
    let ya : LocInt (w i) := ⟨y (a, b) (w i), hy i (a, b)⟩
    let xa : LocInt (w i) := ⟨x (a, b) (w i), hx i (a, b)⟩
    change residueOrZero ya.val = residueOrZero xa.val
    rw [residueOrZero_coe, residueOrZero_coe]
    exact residue_eq_iff_valuation_sub_lt_one.2 (h_close i (a, b))
  · have hy : ¬∀ (i : ι) (p : n' × n), y p (w i) ∈ LocInt (w i) :=
      fun h ↦ hx fun i p ↦ (h_mem i p).1 (h i p)
    rw [residueDatum, residueDatum, ite_eq_right hy, ite_eq_right hx]

end LocalAnnihilator

namespace DescentPair

variable {E r n : Type} [Field E] [CMType E]

/-- The component at `w` of a finite adelic `n × r` matrix. -/
def matrixAt (w : FinPlace E) (x : n × r → 𝔸f E) : Matrix n r (LocField w) :=
  (vecToMatrix x).map (evalAt w)

lemma matrixAt_apply (w : FinPlace E) (x : n × r → 𝔸f E) (a : n) (b : r) :
    matrixAt w x a b = x (a, b) w := rfl

/-- The component of `x A` at `w` is the product of the components of `x` and `A`. -/
lemma matrixAt_mul [Fintype r] [DecidableEq r] (w : FinPlace E) (x : n × r → 𝔸f E) (A : Gf E r) :
    matrixAt w (matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E)))) =
      matrixAt w x * (A.atPlace w).val := Matrix.map_mul

variable [DecidableEq n]

/-- The component of `(1, 0)ᵀ A` at `w` is `(1, 0)ᵀ` times the component of `A`; the rows `ι` carry
the identity block. -/
lemma matrixAt_inclMatrix_mul [Fintype r] [DecidableEq r]
    (w : FinPlace E) (ι : r ↪ n) (A : Gf E r) :
    matrixAt w (matrixToVec (inclMatrix (𝔸f E) ι * (A : Matrix r r (𝔸f E)))) =
      inclMatrix (LocField w) ι * (A.atPlace w).val := by
  rw [← map_inclMatrix (evalAt w)]
  exact Matrix.map_mul

variable [Fintype n]

variable (E r n) in
/-- The action `x ↦ h x` of the finite adelic points of `U(V)` on finite adelic `n × r` matrices. -/
def leftMul : Representation (𝔸f E) (Gf E n) (n × r → 𝔸f E) where
  toFun h :=
    { toFun x := matrixToVec ((h : Matrix n n (𝔸f E)) * vecToMatrix x)
      map_add' x y := congrArg matrixToVec (Matrix.mul_add _ (vecToMatrix x) (vecToMatrix y))
      map_smul' c x := congrArg matrixToVec (Matrix.mul_smul _ c (vecToMatrix x)) }
  map_one' := LinearMap.ext fun x ↦ congrArg matrixToVec (vecToMatrix x).one_mul
  map_mul' h k := LinearMap.ext fun x ↦ congrArg matrixToVec
    (Matrix.mul_assoc (h : Matrix n n (𝔸f E)) (k : Matrix n n (𝔸f E)) (vecToMatrix x))

lemma leftMul_apply (h : Gf E n) (x : n × r → 𝔸f E) :
    leftMul E r n h x = matrixToVec ((h : Matrix n n (𝔸f E)) * vecToMatrix x) := rfl

/-- The component of `h x` at `w` is the product of the components of `h` and `x`. -/
lemma matrixAt_leftMul (w : FinPlace E) (h : Gf E n) (x : n × r → 𝔸f E) :
    matrixAt w (leftMul E r n h x) = (h.atPlace w).val * matrixAt w x := Matrix.map_mul

/-- An element `k` of the maximal level preserves the matrices that are integral at `S`. -/
lemma leftMul_mem_integralBox_iff {S : Set (FinPlace E)} (k : stdLevel E n) {x : n × r → 𝔸f E} :
    leftMul E r n k x ∈ integralBox (n × r) S ↔ x ∈ integralBox (n × r) S := by
  have h_le (k : stdLevel E n) {x : n × r → 𝔸f E} (hx : x ∈ integralBox (n × r) S) :
      leftMul E r n k x ∈ integralBox (n × r) S := by
    rintro ⟨a, b⟩
    have h_entry : idem S * leftMul E r n k x (a, b) =
        ∑ c : n, (k.val : Matrix n n (𝔸f E)) a c * (idem S * x (c, b)) := by
      simp [leftMul_apply, matrixToVec, vecToMatrix, Matrix.mul_apply, mul_sum, mul_left_comm]
    refine Set.mem_of_eq_of_mem h_entry (sum_mem (S := Ô E) fun c _ ↦ ?_)
    exact mul_mem (mem_stdLevel.1 k.prop a c) (hx (c, b))
  exact ⟨fun h ↦ by simpa using h_le k⁻¹ h, h_le k⟩

/-- For `k` in the maximal level `stdLevel E n`, the indicator `cosetIndicator S t z` of the class
of `z` modulo `t` at the places of `S`, evaluated at `k⁻¹ x`, equals `cosetIndicator S t (k z)`
evaluated at `x`. -/
lemma cosetIndicator_leftMul_inv {S : Set (FinPlace E)} (t : (𝔸f E)ˣ) (k : stdLevel E n)
    (z x : n × r → 𝔸f E) :
    cosetIndicator S t z (leftMul E r n k.val⁻¹ x) = cosetIndicator S t (leftMul E r n k z) x := by
  classical
  have h_move : leftMul E r n k (t⁻¹.val • (leftMul E r n k.val⁻¹ x - z)) =
      t⁻¹.val • (x - leftMul E r n k z) := by simp
  exact if_congr (by rw [← h_move, leftMul_mem_integralBox_iff]) rfl rfl

omit [DecidableEq n] [Fintype n] in
/-- Two matrices with the same components at `S` define the same `t`-coset indicator at `S`. -/
lemma cosetIndicator_eq_of_idem_smul_eq {S : Set (FinPlace E)} (t : (𝔸f E)ˣ)
    {z₁ z₂ : n × r → 𝔸f E} (h_eq : idem S • z₁ = idem S • z₂) :
    cosetIndicator S t z₁ = cosetIndicator S t z₂ := by
  classical
  refine funext fun x ↦ if_congr ?_ rfl rfl
  change idem S • t⁻¹.val • (x - z₁) ∈ stdLattice E (n × r) ↔
    idem S • t⁻¹.val • (x - z₂) ∈ stdLattice E (n × r)
  simp only [smul_comm (idem S) t⁻¹.val, smul_sub (idem S), h_eq]

/-- An element `k` of the maximal level that moves `z` by an integral multiple of `t` at `S`
preserves the class of `z` modulo the idele `t` at the places of `S`. -/
lemma cosetIndicator_leftMul_inv_of_sub_mem {S : Set (FinPlace E)} (t : (𝔸f E)ˣ) {k : stdLevel E n}
    {z : n × r → 𝔸f E} (h_sub : t⁻¹.val • (leftMul E r n k z - z) ∈ integralBox (n × r) S) :
    (fun x : n × r → 𝔸f E ↦ cosetIndicator S t z (leftMul E r n k.val⁻¹ x)) =
      cosetIndicator S t z := by
  classical
  refine funext fun x ↦ (cosetIndicator_leftMul_inv t k z x).trans (if_congr ?_ rfl rfl)
  have h_split : t⁻¹.val • (x - leftMul E r n k z) =
      t⁻¹.val • (x - z) + t⁻¹.val • (z - leftMul E r n k z) := by
    rw [← smul_add, sub_add_sub_cancel]
  have h_neg : t⁻¹.val • (z - leftMul E r n k z) ∈ integralBox (n × r) S := by
    simpa [← smul_neg] using neg_mem h_sub
  rw [h_split]
  exact add_mem_cancel_right h_neg

variable [Fintype r] [DecidableEq r] {O : DescentPair E r n}

/-- An element `k` of the maximal level `stdLevel E n` lies in `O.levelGroup` if its reductions fix
`inclMatrix O.incl = (1, 0)ᵀ` at the chosen places `O.placeAt (.inl i)`, and at the places
`O.placeAt (.inr i)` of `Q` have zero entries in rows `O.incl` outside the columns `O.incl`. -/
lemma mem_levelGroup_of_reduceAt {k : stdLevel E n}
    (h_chosen : ∀ i : O.ChosenIndex, (stdLevel.reduceAt (O.placeAt (.inl i)) k).val *
      inclMatrix (ResField (O.placeAt (.inl i))) O.incl =
        inclMatrix (ResField (O.placeAt (.inl i))) O.incl)
    (h_twist : ∀ (i : O.TwistIndex) (a : r) (b : n), b ∉ Set.range O.incl →
      (stdLevel.reduceAt (O.placeAt (.inr i)) k).val (O.incl a) b = 0) :
    k.val ∈ O.levelGroup := by
  refine mem_levelOf.2 ⟨k.prop, ?_⟩
  rintro (i | i) -
  exacts [mem_stabilizer_col_iff.2 (h_chosen i), (mem_rangeParabolic_iff O.incl).2 (h_twist i)]

/-- The function `Ψ_bl(· A)`: the block datum of `O` as a function of an adelic `n × r` matrix,
translated on the right by `A`. -/
def translatedBlockFn (O : DescentPair E r n) (A : Gf E r) (x : n × r → 𝔸f E) : ℂ :=
  residueDatum O.placeAt O.residueBlockDatum (matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E))))

/-- The function `residueDatum O.placeAt O.residueBlockDatum`, the block datum Ψ_bl read on finite
adelic matrices through their reductions at the places `O.placeAt`, is Schwartz–Bruhat above
`O.places`. -/
lemma isSchwartzBruhat_residueDatum_residueBlockDatum :
    IsSchwartzBruhat O.places (residueDatum O.placeAt O.residueBlockDatum) :=
  isSchwartzBruhat_residueDatum O.residueBlockDatum O.apart.star_ne

instance (A : Gf E r) : IsSchwartzBruhat O.places (O.translatedBlockFn A) := by
  -- The map `x ↦ x A` is given by an invertible matrix `T` on the entries of `x`.
  let T : GL (n × r) (𝔸f E) := (G.onHom (s := 1) (s' := (1 : n → ℤˣ)) ((1, A), 1)).2⁻¹.val
  have h_eq (x : n × r → 𝔸f E) :
      residueDatum O.placeAt O.residueBlockDatum (T.val *ᵥ x) = O.translatedBlockFn A x := by
    simp [T, translatedBlockFn, onHom_snd_inv_mulVec]
  simpa only [h_eq] using (isSchwartzBruhat_residueDatum_residueBlockDatum (O := O)).comp_mulVec T

/-- The function `Ψ = O.residueBlockDatum` of families `X` of residue matrices is
`∏_{w ∈ Q} χ_w(det X_w')` if `X_w = (1, 0)ᵀ` at all chosen places, and `0` otherwise. Let `τ` lie in
`descentResidueLevel`: it fixes `(1, 0)ᵀ` at the chosen places and is block lower triangular at `Q`.
Then `Ψ(τ X) = c Ψ(X)`, where `c` is the conjugate of
`O.residueLevelChar τ = ∏_{w ∈ Q} χ_w(det τ_w')⁻¹`, with `τ_w'` the block of `τ_w` of the rows and
columns `O.incl`. -/
lemma residueBlockDatum_mul (τ : descentResidueLevel O.toLevelPlaces O.incl)
    (X : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt j))) :
    (O.residueBlockDatum fun j : O.ChosenIndex ⊕ O.TwistIndex ↦ (τ.val j).val * X j) =
      star (O.residueLevelChar τ) * O.residueBlockDatum X := by
  classical
  -- At a chosen place `τ` fixes `(1, 0)ᵀ`. At a place of `Q` the upper block of `τ X` is `s X'`,
  -- where `s` is the first diagonal block of `τ`.
  have h_chosen (i : O.ChosenIndex) : (τ.val (.inl i)).val * X (.inl i) = inclMatrix _ O.incl ↔
      X (.inl i) = inclMatrix _ O.incl := by
    have h_fix : (τ.val (.inl i)).val * inclMatrix _ O.incl = inclMatrix _ O.incl :=
      mem_stabilizer_col_iff.1 (τ.prop (.inl i) trivial)
    conv_lhs => rw [← h_fix]
    exact Matrix.mul_right_inj_of_invertible _
  have h_twist (i : O.TwistIndex) : ((τ.val (.inr i)).val * X (.inr i)).submatrix O.incl id =
      (τ.val (.inr i)).val.submatrix O.incl O.incl * (X (.inr i)).submatrix O.incl id :=
    submatrix_mul_of_mem_rangeParabolic _ (τ.prop (.inr i) trivial)
  have h_char : O.residueLevelChar τ = ∏ i : O.TwistIndex, (O.tamePart (O.placeAt (.inr i)))⁻¹
      ((τ.val (.inr i)).val.submatrix O.incl O.incl).det := rfl
  simp only [residueBlockDatum, h_chosen, h_twist, h_char, star_prod, MulChar.star_apply', inv_inv,
    det_mul, map_mul, prod_mul_distrib, mul_ite, mul_zero]

section

omit [DecidableEq n]

/-- Suppose the component of the adelic matrix `x` at each `O.placeAt j` is a matrix `Z j` over the
local integers. Let `f` be a function of families of residue matrices. Then
`residueDatum O.placeAt f`, which reads `f` on the reductions of a matrix integral at these places,
takes at `x` the value of `f` at the reductions of the `Z j`. -/
lemma residueDatum_of_eq_map {x : n × r → 𝔸f E}
    (f : (∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt j))) → ℂ)
    (Z : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (LocInt (O.placeAt j)))
    (hZ : ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      matrixAt (O.placeAt j) x = (Z j).map (LocInt (O.placeAt j)).subtype) :
    residueDatum O.placeAt f x =
      f fun j : O.ChosenIndex ⊕ O.TwistIndex ↦ (Z j).map (residue (LocInt (O.placeAt j))) := by
  have h_entry (j : O.ChosenIndex ⊕ O.TwistIndex) (p : n × r) :
      x p (O.placeAt j) = (Z j p.1 p.2).val := by
    rw [← matrixAt_apply, hZ j, Matrix.map_apply, ValuationSubring.subtype_apply]
  rw [residueDatum, ite_eq_left fun j p ↦ by simp [h_entry]]
  congr with j a b
  change residueOrZero (x (a, b) (O.placeAt j)) = residue _ (Z j a b)
  rw [h_entry, residueOrZero_coe]

/-- Two matrices with the same components at the places of `O` have the same product with the adele
`idem O.places`, which is `1` at these places and `0` elsewhere. -/
lemma idem_smul_eq_of_matrixAt_eq {x y : n × r → 𝔸f E}
    (h_eq : ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      matrixAt (O.placeAt j) x = matrixAt (O.placeAt j) y) :
    idem O.places • x = idem O.places • y := by
  ext ⟨a, b⟩ w : 2
  change idem O.places w * x (a, b) w = idem O.places w * y (a, b) w
  obtain ⟨j, rfl⟩ | hw := Classical.em (w ∈ O.places)
  · rw [← matrixAt_apply, ← matrixAt_apply (x := y), h_eq j]
  · rw [idem_of_notMem hw, zero_mul, zero_mul]

/-- The components of a matrix that is integral at the places of `O` are integral matrices. -/
lemma exists_eq_map_of_mem_integralBox {x : n × r → 𝔸f E} (hx : x ∈ integralBox (n × r) O.places) :
    ∃ Z : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (LocInt (O.placeAt j)),
      ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
        matrixAt (O.placeAt j) x = (Z j).map (LocInt (O.placeAt j)).subtype :=
  ⟨fun j a b ↦ ⟨x (a, b) (O.placeAt j), idem_mul_mem_Ô.1 (hx (a, b)) _ ⟨j, rfl⟩⟩, fun _ ↦ rfl⟩

/-- The function `residueDatum O.placeAt f` vanishes at a matrix `x` that is not integral at some
place of `O`. -/
lemma residueDatum_of_notMem {x : n × r → 𝔸f E}
    (f : (∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt j))) → ℂ)
    (hx : x ∉ integralBox (n × r) O.places) : residueDatum O.placeAt f x = 0 :=
  ite_eq_right fun h_int ↦ hx fun p ↦ idem_mul_mem_Ô.2 (Set.forall_mem_range.2 fun j ↦ h_int j p)

end

/-- Let `Ψ = O.translatedBlockFn A`, that is `Ψ(x) = Ψ_bl(x A)`. For `h` in `O.levelGroup` we have
`Ψ(h x) = c Ψ(x)`, where `leftMul` is the action `x ↦ h x` and `c` is the conjugate of
`O.levelChar h = ∏_{w ∈ Q} χ_w(det h')⁻¹`, with `h'` the block of the rows and columns `O.incl` of
the reduction of `h` at `w`. -/
lemma translatedBlockFn_leftMul (A : Gf E r) (h : O.levelGroup) (x : n × r → 𝔸f E) :
    O.translatedBlockFn A (leftMul E r n h x) = star (O.levelChar h) * O.translatedBlockFn A x := by
  -- Both sides vanish unless `u = x A` is integral at the places of `O`; then the rule holds for
  -- the reductions.
  let k : stdLevel E n := ⟨h, levelOf_le_stdLevel h.prop⟩
  let u : n × r → 𝔸f E := matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E)))
  have h_assoc : matrixToVec (vecToMatrix (leftMul E r n h x) * (A : Matrix r r (𝔸f E))) =
      leftMul E r n k u := congrArg matrixToVec (Matrix.mul_assoc _ (vecToMatrix x) _)
  rw [translatedBlockFn, translatedBlockFn, h_assoc]
  by_cases! hu : u ∉ integralBox (n × r) O.places
  · rw [residueDatum_of_notMem _ hu, mul_zero,
      residueDatum_of_notMem _ ((leftMul_mem_integralBox_iff k).not.2 hu)]
  obtain ⟨Z, hZ⟩ := exists_eq_map_of_mem_integralBox hu
  have h_int (j) : ∃ τ : GL n (LocInt (O.placeAt j)),
      GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype τ = k.val.atPlace (O.placeAt j) :=
    mem_stdLevel_iff.1 k.prop (O.placeAt j)
  choose τ hτ using h_int
  have h_mul (j) : matrixAt (O.placeAt j) (leftMul E r n k u) =
      ((τ j).val * Z j).map (LocInt (O.placeAt j)).subtype := by
    rw [matrixAt_leftMul, hZ, ← hτ, Matrix.map_mul]
    rfl
  let τ₀ : descentResidueLevel O.toLevelPlaces O.incl := levelOf.reduction _ _ h
  have h_red (j) :
      ((τ j).val * Z j).map (residue _) = (τ₀.val j).val * (Z j).map (residue _) := by
    have h_at : τ₀.val j = GeneralLinearGroup.map (residue _) (τ j) :=
      reduceAt_eq_of_atPlace (hτ j).symm
    rw [Matrix.map_mul, h_at]
    rfl
  have h_char : O.levelChar h = O.residueLevelChar τ₀ := rfl
  rw [residueDatum_of_eq_map _ Z hZ, residueDatum_of_eq_map _ _ h_mul, funext h_red, h_char]
  exact residueBlockDatum_mul τ₀ _

/-- If the block datum of `O`, translated on the right by `A` (`translatedBlockFn`), is nonzero at
the finite adelic `n × r` matrix `x`, then at the places of `O` the matrix `x` equals `h ι A⁻¹` for
some `h` in the level group of `O`. Here `ι` is the inclusion matrix of `O.incl`, and
multiplication by `idem O.places` keeps only the components at the places of `O`. -/
lemma exists_leftMul_eq_of_translatedBlockFn_ne_zero {A : Gf E r} {x : n × r → 𝔸f E}
    (hx : O.translatedBlockFn A x ≠ 0) :
    ∃ h : O.levelGroup, idem O.places • x = idem O.places • leftMul E r n h
      (matrixToVec (inclMatrix (𝔸f E) O.incl * ((A⁻¹ : Gf E r) : Matrix r r (𝔸f E)))) := by
  classical
  -- The point `x A` of the support of the block datum has integral components `u j` at the places
  -- of `O`. They are `≡ (1, 0)ᵀ` at the chosen places, and their upper block `u'` is invertible
  -- modulo the places of `Q`.
  let xA : n × r → 𝔸f E := matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E)))
  have h_int : xA ∈ integralBox (n × r) O.places :=
    by_contra fun h ↦ hx (residueDatum_of_notMem O.residueBlockDatum h)
  obtain ⟨u, hu⟩ : ∃ u : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (LocInt (O.placeAt j)),
      ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
        matrixAt (O.placeAt j) xA = (u j).map (LocInt (O.placeAt j)).subtype :=
    exists_eq_map_of_mem_integralBox h_int
  obtain ⟨h_chosen, h_twist⟩ :
      (∀ i : O.ChosenIndex, (u (.inl i)).map (residue _) = inclMatrix _ O.incl) ∧
      ∀ i ∈ (univ : Finset O.TwistIndex), O.tamePart (O.placeAt (.inr i))
        (((u (.inr i)).map (residue _)).submatrix O.incl id).det ≠ 0 := by
    rwa [translatedBlockFn, residueDatum_of_eq_map _ u hu, residueBlockDatum, ite_ne_right_iff,
      prod_ne_zero_iff] at hx
  have h_unit (j) : IsUnit (completeColumns O.incl (u j)).det := by
    rw [det_completeColumns, ← isUnit_map_iff (residue (LocInt _)), RingHom.map_det]
    change IsUnit (((u j).map (residue _)).submatrix O.incl id).det
    obtain i | i := j
    · simp only [h_chosen i, submatrix_inclMatrix, det_one, isUnit_one]
    · exact MulChar.apply_ne_zero_iff.1 (h_twist i (mem_univ i))
  -- An element `h` with the components `(u' 0; u'' 1)` lies in the level group and carries
  -- `(1, 0)ᵀ` to `u j` at each place of `O`.
  obtain ⟨h, h_at⟩ : ∃ h : stdLevel E n, ∀ j : O.ChosenIndex ⊕ O.TwistIndex,
      h.val.atPlace (O.placeAt j) = GeneralLinearGroup.map (LocInt (O.placeAt j)).subtype
        (.mk'' (completeColumns O.incl (u j)) (h_unit j)) :=
    exists_stdLevel_atPlace_eq _
  have h_red (j) :
      (stdLevel.reduceAt (O.placeAt j) h).val = completeColumns O.incl ((u j).map (residue _)) := by
    rw [reduceAt_eq_of_atPlace (h_at j)]
    exact map_completeColumns O.incl (residue _) (u j)
  have h_mem : h.val ∈ O.levelGroup := by
    refine mem_levelGroup_of_reduceAt (fun i ↦ ?_) fun i a b hb ↦ ?_
    · rw [h_red, h_chosen]
      exact completeColumns_mul_inclMatrix O.incl _
    · rw [h_red, completeColumns_apply_of_notMem _ _ a hb]
  refine ⟨⟨h, h_mem⟩, idem_smul_eq_of_matrixAt_eq fun j ↦ ?_⟩
  have h_comp : (h.val.atPlace (O.placeAt j)).val =
      completeColumns O.incl (matrixAt (O.placeAt j) x * (A.atPlace (O.placeAt j)).val) := by
    rw [← matrixAt_mul, hu j, h_at j]
    exact map_completeColumns O.incl (LocInt (O.placeAt j)).subtype (u j)
  rw [matrixAt_leftMul, matrixAt_inclMatrix_mul, ← Matrix.mul_assoc, h_comp,
    completeColumns_mul_inclMatrix, map_inv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- The translation `Ψ ↦ c Ψ(h⁻¹ ·)` by an element `h` of the level group of `O`, where `c` is the
conjugate of the level character `O.levelChar h`: the product over the places `w ∈ Q` of
`χ_w(det h_w')⁻¹`, for the first diagonal block `h_w'` of the reduction of `h` at `w`. -/
def levelTranslate (O : DescentPair E r n) :
    Representation ℂ O.levelGroup ((n × r → 𝔸f E) → ℂ) where
  toFun h := star (O.levelChar h) • LinearMap.funLeft ℂ ℂ (leftMul E r n h.val⁻¹)
  map_one' := LinearMap.ext fun Ψ ↦ funext fun x ↦ by simp
  map_mul' h k := LinearMap.ext fun Ψ ↦ funext fun x ↦ by
    simpa [mul_assoc] using mul_left_comm (star (O.levelChar h)) (star (O.levelChar k)) _

lemma levelTranslate_apply (h : O.levelGroup) (Ψ : (n × r → 𝔸f E) → ℂ) (x : n × r → 𝔸f E) :
    O.levelTranslate h Ψ x = star (O.levelChar h) * Ψ (leftMul E r n h.val⁻¹ x) := rfl

/-- The complex conjugate of the matrix coefficient `algFormCoeff 1 u y` of a form `y` on `V`, for a
linear functional `u` on the weight space, is automorphic on `U(V)`. -/
lemma isAutomorphic_star_algFormCoeff (u : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ) (y : O.FormV) :
    (stdSpace E n).IsAutomorphic (star (algFormCoeff 1 u y.val)) :=
  (isAutomorphic_algFormCoeff y.val).conj

omit [DecidableEq n] in
/-- No place of the descent pair `O` is the conjugate of itself or of another place of `O`. -/
lemma isConjDisjoint_places : O.places.IsConjDisjoint := by
  grind [O.apart.star_ne]

variable [WeilData E] (u : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ)
  (P : MvPolynomial (InfinitePlace E × n × r) ℂ) (g : G E O.signs)

/-- The conjugate of the value at `g` of the descent of the matrix coefficient `u` of a form `y` by
the datum `v_P ⊗ Ψ ⊗ vac`, where `v_P` is the Fock vector of the polynomial `P`. It is linear in
`Ψ` and conjugate linear in `y`; below it is written `B(Ψ, y)`. -/
def descentPairing : ((n × r → 𝔸f E) → ℂ) →ₗ[ℂ] O.FormV →ₗ⋆[ℂ] ℂ :=
  let datum : ((n × r → 𝔸f E) → ℂ) →ₗ[ℂ] 𝒮 (O.W.hom (stdSpace E n)) :=
    ((O.W.hom (stdSpace E n)).integrated (polyVector (realSigns E (homSigns O.signs 1)) P) ∘L
      .apply ℂ (𝒮 (O.W.hom (stdSpace E n))) (vacElem (O.W.hom (stdSpace E n)))).toLinearMap ∘ₗ
      schrodingerOp (O.W.hom (stdSpace E n)) O.places
  let coeff : O.FormV →ₗ⋆[ℂ] (stdSpace E n).rapidFunctions.toSubmodule :=
    .codRestrict (stdSpace E n).rapidFunctions.toSubmodule
      ((starLinearEquiv ℂ).toLinearMap ∘ₛₗ (algFormCoeff 1 u).domRestrict _)
      fun y : O.FormV ↦ (isAutomorphic_star_algFormCoeff u y).mem_rapidFunctions fun _ _ ↦ rfl
  (((pairThetaKer O.W (stdSpace E n) O.charW 1).swap.liftBilin ∘ₗ datum).compr₂ (.proj g)).compl₂
    coeff

/-- The pairing `B(Ψ, y)` is the value at `g` of the theta lift from `U(V)` to `U(W)`, with datum
`v_P ⊗ Ψ ⊗ vac`, of the conjugate of the matrix coefficient `u` of `y`. -/
lemma descentPairing_apply (Ψ : (n × r → 𝔸f E) → ℂ) (y : O.FormV) :
    descentPairing u P g Ψ y = lift (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
      (integrated (O.W.hom (stdSpace E n)) (polyVector (realSigns E (homSigns O.signs 1)) P)
        (schrodingerOp (O.W.hom (stdSpace E n)) O.places Ψ (vacElem (O.W.hom (stdSpace E n)))))
      (star (algFormCoeff 1 u y.val)) g := rfl

/-- The descent to `W` of the matrix coefficient `u` of the form `y` by the datum
`v_P ⊗ Ψ_bl ⊗ vac` vanishes, where `Ψ_bl ⊗ vac` is the block datum `O.blockDatum`. -/
def BlockDescentVanishes (y : O.FormV) : Prop :=
  lift (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
    (integrated (O.W.hom (stdSpace E n)) (polyVector (realSigns E (homSigns O.signs 1)) P)
      O.blockDatum.val) (star (algFormCoeff 1 u y.val)) = 0

/-- Let `O` be a descent pair with spaces `W` and `V`, and `O.FormV` the forms on `V` of weight
`(O.columnCount, O.detExp)` and of the level of `O`. For a linear functional `u` on the values of
these forms, a polynomial `P` and an adelic point `g` of `U(W)`, let
`B(Ψ, y) = descentPairing u P g Ψ y`. It is the conjugate of the value at `g` of the descent of the
matrix coefficient `u` of `y` by a datum: the Fock vector of `P` at infinity, `Ψ` at the places
`O.places`, and the vacuum elsewhere. Let `k` be in the maximal level `stdLevel E n`, let `Ψ` be
Schwartz–Bruhat at `O.places`, and let `y'` be the right translate of `y` by `k` (the action
`algFormRep`). Then `B(Ψ(k⁻¹ ·), y') = B(Ψ, y)`. -/
lemma descentPairing_translate (k : stdLevel E n) (Ψ : (n × r → 𝔸f E) → ℂ)
    [IsSchwartzBruhat O.places Ψ] {y y' : O.FormV}
    (h_translate : y'.val = algFormRep O.columnCount O.detExp k y.val) :
    descentPairing u P g (fun x : n × r → 𝔸f E ↦ Ψ (leftMul E r n k.val⁻¹ x)) y' =
      descentPairing u P g Ψ y := by
  -- The lift is equivariant under `k`, which moves `Ψ` and fixes `v_P` and the vacuum. The element
  -- `((1, 1), 1, k)` of `U(W) × U(V)` is `k` at the finite places of `U(V)` and `1` elsewhere.
  let K := (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
  let v : fockSpace (realSigns E (homSigns O.signs 1)) := polyVector _ P
  let vac : 𝒮 (O.W.hom (stdSpace E n)) := vacElem _
  have h_form : star (algFormCoeff 1 u y'.val) =
      fun x ↦ star (algFormCoeff 1 u y.val) (x * (1, k.val)) :=
    funext fun x ↦ by simp [h_translate, algFormCoeff_algFormRep]
  have h_vac : pairWeil O.W (stdSpace E n) O.charW 1 ((1, 1), 1, k.val) vac = vac := by
    rw [pairWeil_eq_smul_of_projOn_eq ⊤ (by simp [vac]) (one_mem _) (by simp)]
    simp
  have h_datum : K.ω ((1, k.val), 1) (integrated _ v (schrodingerOp _ O.places Ψ vac)) =
      integrated _ v (schrodingerOp _ O.places (fun x ↦ Ψ (leftMul E r n k.val⁻¹ x)) vac) := by
    change pairWeil O.W (stdSpace E n) O.charW 1 ((1, 1), 1, k.val) _ = _
    rw [pairWeil_integrated_fin, pairWeil_schrodingerOp_of_mem isConjDisjoint_places (one_mem _)
      k.prop, h_vac]
    simp [leftMul_apply]
  rw [descentPairing_apply, descentPairing_apply, h_form, ← h_datum,
    ← K.lift_equivariant (isAutomorphic_star_algFormCoeff u y), mul_one]

/-- The rule `B(c Ψ(h⁻¹ ·), y) = B(Ψ, y)` for the pairing `B = descentPairing u P g` and `h` in the
level group. Here `c` is the conjugate of the level character at `h`, and `O.levelTranslate h Ψ` is
the function `c Ψ(h⁻¹ ·)`. -/
lemma descentPairing_levelTranslate (h : O.levelGroup) (Ψ : (n × r → 𝔸f E) → ℂ)
    [IsSchwartzBruhat O.places Ψ] (y : O.FormV) :
    descentPairing u P g (O.levelTranslate h Ψ) y = descentPairing u P g Ψ y := by
  let Ψ' (x : n × r → 𝔸f E) : ℂ := Ψ (leftMul E r n h.val⁻¹ x)
  let k : stdLevel E n := ⟨h, levelOf_le_stdLevel h.prop⟩
  have h_level : (O.levelChar h • y).val = algFormRep O.columnCount O.detExp k y.val :=
    (y.prop h).symm
  calc _ = descentPairing u P g (star (O.levelChar h) • Ψ') y := rfl
    _ = descentPairing u P g Ψ' (O.levelChar h • y) := by simp
    _ = descentPairing u P g Ψ y := descentPairing_translate u P g k Ψ h_level

/-- The block datum `O.blockDatum` is the vector `Ψ_bl ⊗ vac` with the function
`Ψ_bl = residueDatum O.placeAt O.residueBlockDatum` at the places of `O` and the vacuum
elsewhere. -/
lemma blockDatum_val :
    O.blockDatum.val = schrodingerOp (O.W.hom (stdSpace E n)) O.places
      (residueDatum O.placeAt O.residueBlockDatum) (vacElem (O.W.hom (stdSpace E n))) := by
  have h_places : (O.levelModulus 2).places = O.places := places_levelModulus
  rw [← liftFn_eq_residueDatum h_places, ← h_places]
  rfl

/-- Let `O` be a descent pair, `W = O.W` its hermitian space of rank `r` and `V = stdSpace E n` the
standard space of rank `n`. The group `U(W) × U(V)` acts by the Weil representation `pairWeil`,
twisted by the character `O.charW` of `U(1)`, on data on `Hom(W, V)`; the argument `((1, A), 1, 1)`
is the finite adelic point `A` of `U(W)`. The block datum `O.blockDatum` is `Ψ_bl ⊗ vac`, that is
`schrodingerOp` of a function `Ψ_bl` of the components at the places of `O` applied to the vacuum
`vacElem`. If `A` is `1` away from these places and their conjugates, it sends `Ψ_bl ⊗ vac` to a
nonzero multiple of `Ψ_bl(· A) ⊗ vac`, with `Ψ_bl(· A) = O.translatedBlockFn A`. -/
lemma exists_pairWeil_blockDatum_eq_smul {A : Gf E r} (hA : A ∈ supportedOn r O.places) :
    ∃ c : ℂ, c ≠ 0 ∧ pairWeil O.W (stdSpace E n) O.charW 1 ((1, A), 1, 1) O.blockDatum.val =
      c • schrodingerOp (O.W.hom (stdSpace E n)) O.places (O.translatedBlockFn A)
        (vacElem (O.W.hom (stdSpace E n))) := by
  have := isSchwartzBruhat_residueDatum_residueBlockDatum (O := O)
  -- The multiple is a character value at `det A` times a power of the idele norm of `det A`.
  refine ⟨(((1 : AutChar E).spaceChar (Fintype.card n)).val (detOn O.places A.val) : ℂ)⁻¹ *
    √(ideleAbs (detOn O.places A.val)) ^ Fintype.card n, by simp, ?_⟩
  rw [blockDatum_val, pairWeil_schrodingerOp_of_mem_supportedOn isConjDisjoint_places hA
    (one_mem _)]
  unfold translatedBlockFn
  simp

/-- Let `O` be a descent pair with spaces `W` (rank `r`) and `V` (rank `n`), `u` a linear functional
on the values of the forms on `V`, `P` a polynomial with Fock vector `v_P`, and `g` an adelic point
of `U(W)`. For a form `y` on `V`, the number `B(Ψ, y) = descentPairing u P g Ψ y` is the value at
`g` of the theta lift to `U(W)`, with datum `v_P ⊗ Ψ ⊗ vac` (`vac` is the vacuum), of the conjugate
of the matrix coefficient `algFormCoeff 1 u y`. The function `Ψ_bl` of `O.blockDatum = Ψ_bl ⊗ vac`
is supported on the matrices that are integral at the places of `O` and, at the chosen places,
`≡ (1, 0)ᵀ` (rows `O.incl` the identity, other rows zero). There it is
`∏_{w ∈ Q} χ_w(det x' mod w)`, for `Q` the other places of `O`, `χ_w = O.tamePart w` and `x'` the
rows `O.incl`. Suppose that the lift for `Ψ = Ψ_bl` is zero at all points, and that the finite
adelic point `A` of `U(W)` is `1` away from the places of `O` and their conjugates. Then
`B(Ψ_bl(· A), y) = 0`. -/
lemma descentPairing_translatedBlockFn_eq_zero {y : O.FormV}
    (h_datum : BlockDescentVanishes u P y) {A : Gf E r} (hA : A ∈ supportedOn r O.places) :
    descentPairing u P g (O.translatedBlockFn A) y = 0 := by
  -- The descent by the block datum at `g A` is a nonzero multiple of `B(Ψ_bl(· A), y)`.
  let K := (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
  let v : fockSpace (realSigns E (homSigns O.signs 1)) := polyVector _ P
  let Y : G E (1 : n → ℤˣ) → ℂ := star (algFormCoeff 1 u y.val)
  obtain ⟨c, hc, h_move⟩ := exists_pairWeil_blockDatum_eq_smul hA
  obtain ⟨L, hL⟩ : ∃ L : G E O.signs → 𝒮 (O.W.hom (stdSpace E n)) →L[ℂ] ℂ,
      ∀ φ h, lift K φ Y h = L h φ :=
    K.exists_clm_lift ((isAutomorphic_star_algFormCoeff u y).mem_rapidFunctions fun _ _ ↦ rfl)
  have h_act : K.ω (1, (1, A)) (integrated _ v O.blockDatum.val) =
      c • integrated _ v (schrodingerOp _ O.places (O.translatedBlockFn A) (vacElem _)) := by
    change pairWeil O.W (stdSpace E n) O.charW 1 ((1, A), 1, 1) _ = _
    rw [pairWeil_integrated_fin, h_move, map_smul]
  refine (mul_eq_zero_iff_left hc).1 ?_
  calc c * descentPairing u P g (O.translatedBlockFn A) y
      = lift K (K.ω (1, (1, A)) (integrated _ v O.blockDatum.val)) Y g := by
        rw [h_act, descentPairing_apply, hL, hL, map_smul, smul_eq_mul]
    _ = lift K (integrated _ v O.blockDatum.val) Y (g * (1, A)) := by rw [lift_mul_right]
    _ = 0 := congrFun h_datum _

open scoped Classical in
/-- On any point `q` where `Ψ₀ = O.translatedBlockFn A` is nonzero, `Ψ₀ q` times the descent pairing
on the `t`-coset of `q` equals the descent pairing on the `t`-coset of `(1, 0)ᵀ A⁻¹`: an element of
`O.levelGroup` carries `(1, 0)ᵀ A⁻¹` to `q` at the places of `O`. -/
lemma translatedBlockFn_mul_descentPairing_cosetIndicator (t : (𝔸f E)ˣ) (A : Gf E r)
    {q : n × r → 𝔸f E} (hq : O.translatedBlockFn A q ≠ 0) (y : O.FormV) :
    O.translatedBlockFn A q * descentPairing u P g (cosetIndicator O.places t q) y =
      descentPairing u P g (cosetIndicator O.places t
        (matrixToVec (inclMatrix (𝔸f E) O.incl * ((A⁻¹ : Gf E r) : Matrix r r (𝔸f E))))) y := by
  let base : n × r → 𝔸f E :=
    matrixToVec (inclMatrix (𝔸f E) O.incl * ((A⁻¹ : Gf E r) : Matrix r r (𝔸f E)))
  -- At the base point `e A⁻¹`, the translated block datum evaluates to `1`.
  have h_base : O.translatedBlockFn A base = 1 := by
    have h_mat (j : O.ChosenIndex ⊕ O.TwistIndex) :
        matrixAt (O.placeAt j) (matrixToVec (vecToMatrix base * (A : Matrix r r (𝔸f E)))) =
          (inclMatrix (LocInt (O.placeAt j)) O.incl).map (LocInt (O.placeAt j)).subtype := by
      rw [matrixAt_mul, matrixAt_inclMatrix_mul, Matrix.mul_assoc, map_inv, Units.inv_mul,
        Matrix.mul_one, map_inclMatrix]
    have h_map (j : O.ChosenIndex ⊕ O.TwistIndex) :
        (inclMatrix (LocInt (O.placeAt j)) O.incl).map (residue (LocInt (O.placeAt j))) =
          inclMatrix (ResField (O.placeAt j)) O.incl :=
      map_inclMatrix (residue (LocInt (O.placeAt j))) O.incl
    rw [translatedBlockFn, residueDatum_of_eq_map _ _ h_mat, residueBlockDatum,
      ite_eq_left fun i ↦ h_map (.inl i)]
    exact prod_eq_one fun i _ ↦ by
      rw [h_map (.inr i), submatrix_inclMatrix, det_one, map_one]
  -- Lift `q` from `base` via `h ∈ O.levelGroup`; `Ψ₀ q` equals `star (O.levelChar h)`.
  obtain ⟨h, h_eq⟩ := exists_leftMul_eq_of_translatedBlockFn_ne_zero hq
  have hq_val : O.translatedBlockFn A q = star (O.levelChar h) := by
    have h_idem := IsSchwartzBruhat.idem_smul (S := O.places) (Ψ := O.translatedBlockFn A)
    rw [← h_idem q, h_eq, h_idem, translatedBlockFn_leftMul, h_base, mul_one]
  have h_ind : O.translatedBlockFn A q • cosetIndicator O.places t q =
      O.levelTranslate h (cosetIndicator O.places t base) := by
    ext x
    have h_coset : cosetIndicator O.places t q x =
        cosetIndicator O.places t (leftMul E r n h base) x :=
      congrFun (cosetIndicator_eq_of_idem_smul_eq t h_eq) x
    rw [Pi.smul_apply, smul_eq_mul, hq_val, h_coset,
      ← cosetIndicator_leftMul_inv t ⟨h, levelOf_le_stdLevel h.prop⟩ base x, levelTranslate_apply]
  calc O.translatedBlockFn A q * descentPairing u P g (cosetIndicator O.places t q) y
      = descentPairing u P g (O.translatedBlockFn A q • cosetIndicator O.places t q) y := by simp
    _ = descentPairing u P g (O.levelTranslate h (cosetIndicator O.places t base)) y := by
        rw [h_ind]
    _ = descentPairing u P g (cosetIndicator O.places t base) y :=
        descentPairing_levelTranslate u P g h (cosetIndicator O.places t base) y

section

omit [WeilData E]

/-- The diagonal weight `twistScale j a` over `LocInt (O.placeAt j)`: equal to a uniformiser when
`j` is a twist place and `a ∉ Set.range O.incl`, and `1` otherwise. -/
def twistScale (j : O.ChosenIndex ⊕ O.TwistIndex) (a : n) : LocInt (O.placeAt j) :=
  if j.isRight ∧ a ∉ Set.range O.incl then
    ⟨(uniformizer (O.placeAt j)).val, by simp [mem_LocInt, v_uniformizer]⟩
  else 1

/-- A finite adelic point `A` of `U(W)` makes `z` congruent to `(1, 0)ᵀ` at scale `t` if `A` is
supported on `O.places`, `diag(twistScale j) * z_w * A_w ≡ (1, 0)ᵀ (mod w)` at every place
`w = O.placeAt j`, and `v (t_w * A_w) < 1` entrywise at every place of `O`. -/
structure IsCongruentAt (O : DescentPair E r n) (t : (𝔸f E)ˣ) (z : n × r → 𝔸f E) (A : Gf E r) :
    Prop where
  /-- `A` is trivial away from `O.places` and their conjugates. -/
  supportedOn : A ∈ supportedOn r O.places
  /-- `diag(twistScale j) * z_w * A_w` reduces modulo `w` to `inclMatrix _ O.incl`. -/
  top_lt_one : ∀ (j : O.ChosenIndex ⊕ O.TwistIndex) (c : n) (d : r),
    v ((diagonal (fun c' ↦ (twistScale (O := O) j c').val) * matrixAt (O.placeAt j) z *
      (A.atPlace (O.placeAt j)).val) c d -
        inclMatrix (LocField (O.placeAt j)) O.incl c d) < 1
  /-- `t_w * A_w` has entries of valuation strictly less than `1`. -/
  bot_lt_one : ∀ (j : O.ChosenIndex ⊕ O.TwistIndex) (b d : r),
    v (t.val (O.placeAt j) * (A.atPlace (O.placeAt j)).val b d) < 1

/-- An integral row `l` at `w = O.placeAt j` that annihilates `z` modulo `t`, is nonzero modulo `w`
on `O.incl`, and vanishes modulo `w` outside `O.incl` when `w ∈ Q`. -/
structure IsAnnihilatingRowMod (O : DescentPair E r n) (t : (𝔸f E)ˣ) (z : n × r → 𝔸f E)
    (j : O.ChosenIndex ⊕ O.TwistIndex) (l : n → LocInt (O.placeAt j)) : Prop where
  /-- The row `l` annihilates `z` modulo `t` at `w`. -/
  ann_mem : ∀ b : r, t⁻¹.val (O.placeAt j) *
    ((fun a : n ↦ (l a).val) ᵥ* matrixAt (O.placeAt j) z) b ∈ LocInt (O.placeAt j)
  /-- The part `l ∘ O.incl` of the row is not zero modulo `w`. -/
  residue_ne_zero : (fun d : r ↦ residue (LocInt (O.placeAt j)) (l (O.incl d))) ≠ 0
  /-- At a place of `Q`, the entries of `l` outside `O.incl` vanish modulo `w`. -/
  residue_eq_zero : ¬j.isLeft → ∀ a : n, a ∉ Set.range O.incl →
    residue (LocInt (O.placeAt j)) (l a) = 0

/-- At scale `t`, applying Hermite reduction to the stacked local matrices
`(diag(twistScale j) * z_w; t_w I_r)` yields a dichotomy: either there is `A` making `z` congruent
to `(1, 0)ᵀ` at scale `t` (`IsCongruentAt`), or at some place `w = O.placeAt j` there is an
integral row `l` annihilating `z_w` modulo `t_w` (`IsAnnihilatingRowMod`). -/
lemma exists_annihilator_or_congr_at_places (t : (𝔸f E)ˣ) (z : n × r → 𝔸f E) :
    (∃ A : Gf E r, O.IsCongruentAt t z A) ∨
      (∃ (j : O.ChosenIndex ⊕ O.TwistIndex) (l : n → LocInt (O.placeAt j)),
        O.IsAnnihilatingRowMod t z j l) := by
  have ht_inv (j : O.ChosenIndex ⊕ O.TwistIndex) :
      t⁻¹.val (O.placeAt j) * t.val (O.placeAt j) = 1 := by
    simpa only [evalAt_apply, map_mul, map_one] using congrArg (evalAt (O.placeAt j)) t.inv_mul
  -- Stack `diag(twistScale) * z_w` above `t_w I_r` at each place and apply Hermite reduction.
  let emb : r ↪ n ⊕ r := O.incl.trans ⟨Sum.inl, Sum.inl_injective⟩
  let stacked (j : O.ChosenIndex ⊕ O.TwistIndex) : Matrix (n ⊕ r) r (LocField (O.placeAt j)) :=
    fromRows (diagonal (fun a ↦ (twistScale (O := O) j a).val) * matrixAt (O.placeAt j) z)
      (scalar r (t.val (O.placeAt j)))
  have h_left_inv (j : O.ChosenIndex ⊕ O.TwistIndex) : HasLeftInv (stacked j) :=
    ⟨fromCols 0 (scalar r (t⁻¹.val (O.placeAt j))), by
      simp [stacked, fromCols_mul_fromRows, ht_inv j]⟩
  choose E_mat hE_ann hE_congr using
    fun j ↦ exists_annihilator_or_congr_inclMatrix emb (stacked j) (h_left_inv j)
  by_cases! h_all_zero : ∀ (j : O.ChosenIndex ⊕ O.TwistIndex) (c : n ⊕ r),
      (fun d : r ↦ residue (LocInt (O.placeAt j)) (E_mat j c (emb d))) = 0
  · choose a ha using fun j ↦ hE_congr j (h_all_zero j)
    obtain ⟨A, hA_on, hA⟩ := exists_atPlace_eq a
    refine Or.inl ⟨A, hA_on, fun j c d ↦ ?_, fun j b d ↦ ?_⟩
    · rw [hA j]
      simpa [stacked, emb, inclMatrix, Matrix.one_apply] using ha j (.inl c) d
    · rw [hA j]
      simpa [stacked, emb, inclMatrix, Matrix.one_apply, scalar_apply, diagonal_mul] using
        ha j (.inr b) d
  · obtain ⟨j, c, h_ne⟩ := h_all_zero
    let l (a : n) : LocInt (O.placeAt j) := E_mat j c (.inl a) * twistScale (O := O) j a
    refine Or.inr ⟨j, l, fun b ↦ ?_, ?_, fun hj a ha ↦ ?_⟩
    · have h_row : ((fun a : n ↦ (l a).val) ᵥ* matrixAt (O.placeAt j) z) b =
          -(t.val (O.placeAt j) * (E_mat j c (.inr b)).val) := by
        have h_zero : ((E_mat j).map (LocInt (O.placeAt j)).subtype * stacked j) c b = 0 :=
          congrFun₂ (hE_ann j) c b
        rw [Matrix.mul_apply, Fintype.sum_sum_type] at h_zero
        simpa [stacked, l, vecMul, dotProduct, diagonal_mul, scalar_apply, diagonal_apply,
          mul_assoc, mul_comm (t.val _), add_eq_zero_iff_eq_neg] using h_zero
      rw [h_row, mul_neg, ← mul_assoc, ht_inv j, one_mul]
      exact neg_mem (E_mat j c (.inr b)).prop
    · have h_eq : (fun d : r ↦ residue (LocInt (O.placeAt j)) (l (O.incl d))) =
          fun d : r ↦ residue (LocInt (O.placeAt j)) (E_mat j c (emb d)) := by
        ext d
        simp [l, twistScale, emb]
      rwa [h_eq]
    · obtain i | i := j
      · exact absurd rfl hj
      · have h_uni : residue _ (twistScale (O := O) (.inr i) a) = 0 := by
          rw [twistScale, ite_eq_left ⟨rfl, ha⟩, ← map_zero (residue _)]
          refine residue_eq_iff_valuation_sub_lt_one.2 ?_
          rw [ZeroMemClass.coe_zero, sub_zero, v_uniformizer]
          exact WithZero.exp_lt_exp.2 (by decide)
        dsimp only [l]
        rw [map_mul, h_uni, mul_zero]

/-- If `A` makes `z` congruent to `(1, 0)ᵀ` at scale `t` (`IsCongruentAt`), then `z A` is integral
at every place of `O` and `O.translatedBlockFn A z = 1`. -/
lemma translatedBlockFn_eq_one_of_congr {t : (𝔸f E)ˣ} {z : n × r → 𝔸f E} {A : Gf E r}
    (hA : O.IsCongruentAt t z A) : O.translatedBlockFn A z = 1 := by
  -- Entries of `z A` are integral at every place of `O` (using `v(ϖ * ·) < 1 ⇒ v(·) ≤ 1` for
  -- twist-place rows outside `O.incl`).
  have h_int (j : O.ChosenIndex ⊕ O.TwistIndex) (c : n) (d : r) :
      (matrixAt (O.placeAt j) z * (A.atPlace (O.placeAt j)).val) c d ∈ LocInt (O.placeAt j) := by
    have h_entry := hA.top_lt_one j c d
    rw [Matrix.mul_assoc, diagonal_mul] at h_entry
    by_cases hc : j.isRight ∧ c ∉ Set.range O.incl
    · rw [show (twistScale (O := O) j c).val = (uniformizer (O.placeAt j)).val from
        congrArg Subtype.val (ite_eq_left hc), inclMatrix_apply_of_notMem_range O.incl hc.2 d,
        sub_zero] at h_entry
      have hv := v_uniformizer_inv_mul_le_one_iff.2 h_entry
      rwa [inv_mul_cancel_left₀ (uniformizer (O.placeAt j)).ne_zero] at hv
    · rw [show (twistScale (O := O) j c).val = 1 from congrArg Subtype.val (ite_eq_right hc),
        one_mul] at h_entry
      simpa using add_mem h_entry.le (show inclMatrix (LocField (O.placeAt j)) O.incl c d ∈
        LocInt (O.placeAt j) by simp [inclMatrix, Matrix.one_apply, ite_mem])
  let Z (j) : Matrix n r (LocInt (O.placeAt j)) :=
    .of fun c d ↦ ⟨(matrixAt (O.placeAt j) z * (A.atPlace (O.placeAt j)).val) c d, h_int j c d⟩
  have hZ (j) : matrixAt (O.placeAt j) (matrixToVec (vecToMatrix z * (A : Matrix r r (𝔸f E)))) =
      (Z j).map (LocInt (O.placeAt j)).subtype := by
    rw [matrixAt_mul]
    rfl
  -- At all unscaled rows, `Z j` reduces modulo `w` to `(1, 0)ᵀ`.
  have h_res_eq (j) (c : n) (d : r) (hc : ¬(j.isRight ∧ c ∉ Set.range O.incl)) :
      (Z j).map (residue _) c d = inclMatrix (ResField (O.placeAt j)) O.incl c d := by
    have h_entry := hA.top_lt_one j c d
    rw [Matrix.mul_assoc, diagonal_mul, show (twistScale (O := O) j c).val = 1 from
      congrArg Subtype.val (ite_eq_right hc), one_mul] at h_entry
    have h_incl : (inclMatrix (LocInt (O.placeAt j)) O.incl c d).val =
        inclMatrix (LocField (O.placeAt j)) O.incl c d :=
      congrFun₂ (map_inclMatrix (LocInt (O.placeAt j)).subtype O.incl) c d
    have h_map : residue _ (inclMatrix (LocInt (O.placeAt j)) O.incl c d) =
        inclMatrix (ResField (O.placeAt j)) O.incl c d :=
      congrFun₂ (map_inclMatrix (residue (LocInt (O.placeAt j))) O.incl) c d
    rw [Matrix.map_apply, ← h_map]
    refine residue_eq_iff_valuation_sub_lt_one.2 ?_
    rw [h_incl]
    exact h_entry
  rw [translatedBlockFn, residueDatum_of_eq_map _ Z hZ, residueBlockDatum,
    ite_eq_left fun i ↦ ext fun c d ↦ h_res_eq (.inl i) c d (by simp)]
  refine prod_eq_one fun i _ ↦ ?_
  have h_sub : ((Z (.inr i)).map (residue _)).submatrix O.incl id = 1 := by
    ext b d
    change ((Z (.inr i)).map (residue _)) (O.incl b) d = (1 : Matrix r r _) b d
    rw [h_res_eq (.inr i) (O.incl b) d (by simp)]
    exact congrFun₂ (submatrix_inclMatrix (R := ResField (O.placeAt (.inr i))) O.incl) b d
  rw [h_sub, det_one, map_one]

/-- If `A` satisfies `IsCongruentAt t z A`, then `O.translatedBlockFn A` is constant on `t`-cosets
at `O.places`. -/
lemma translatedBlockFn_const_of_congr {t : (𝔸f E)ˣ} {z : n × r → 𝔸f E} {A : Gf E r}
    (hA : O.IsCongruentAt t z A) {x x' : n × r → 𝔸f E}
    (hx' : t⁻¹.val • (x' - x) ∈ integralBox (n × r) O.places) :
    O.translatedBlockFn A x' = O.translatedBlockFn A x := by
  have ht_inv (j : O.ChosenIndex ⊕ O.TwistIndex) :
      t⁻¹.val (O.placeAt j) * t.val (O.placeAt j) = 1 := by
    simpa only [evalAt_apply, map_mul, map_one] using congrArg (evalAt (O.placeAt j)) t.inv_mul
  refine residueDatum_eq_of_valuation_sub_lt_one O.placeAt O.residueBlockDatum fun j ⟨c, d⟩ ↦ ?_
  have h_diff : matrixToVec (vecToMatrix x' * (A : Matrix r r (𝔸f E))) (c, d) (O.placeAt j) -
      matrixToVec (vecToMatrix x * (A : Matrix r r (𝔸f E))) (c, d) (O.placeAt j) =
      ∑ b : r, (t⁻¹.val • (x' - x)) (c, b) (O.placeAt j) *
        (t.val (O.placeAt j) * (A.atPlace (O.placeAt j)).val b d) := by
    rw [← matrixAt_apply, ← matrixAt_apply, matrixAt_mul, matrixAt_mul, ← Matrix.sub_apply,
      ← Matrix.sub_mul, Matrix.mul_apply]
    refine sum_congr rfl fun b _ ↦ ?_
    change (x' (c, b) (O.placeAt j) - x (c, b) (O.placeAt j)) * (A.atPlace (O.placeAt j)).val b d =
      (t⁻¹.val (O.placeAt j) * (x' (c, b) (O.placeAt j) - x (c, b) (O.placeAt j))) *
        (t.val (O.placeAt j) * (A.atPlace (O.placeAt j)).val b d)
    linear_combination (x' (c, b) (O.placeAt j) - x (c, b) (O.placeAt j)) *
      (A.atPlace (O.placeAt j)).val b d * (ht_inv j).symm
  rw [h_diff]
  exact v.map_sum_lt one_ne_zero fun b _ ↦ (map_mul v _ _).trans_lt
    (mul_lt_of_le_one_of_lt (idem_mul_mem_Ô.1 (hx' (c, b)) _ ⟨j, rfl⟩) (hA.bot_lt_one j b d))

end

/-- **Congruent cosets.** If `A` makes `z` congruent to `(1, 0)ᵀ` at scale `t` (`IsCongruentAt`)
and the descent of `y` by the block datum vanishes, then `B(cosetIndicator O.places t z, y) = 0`. -/
lemma descentPairing_eq_zero_of_congr {y : O.FormV} (h_datum : BlockDescentVanishes u P y)
    {t : (𝔸f E)ˣ} {z : n × r → 𝔸f E} {A : Gf E r} (hA : O.IsCongruentAt t z A) :
    descentPairing u P g (cosetIndicator O.places t z) y = 0 := by
  have hz_one : O.translatedBlockFn A z = 1 := translatedBlockFn_eq_one_of_congr hA
  -- Decompose `Ψ₀ = O.translatedBlockFn A` as a finite sum of `t`-coset indicators; each nonzero
  -- term shifts to the base coset `e A⁻¹`, so `(#F) * B(1_{e A⁻¹ + t Ô}, y) = B(Ψ₀, y) = 0`.
  obtain ⟨F, hF, h_sum_eq⟩ :=
    (inferInstance : IsSchwartzBruhat O.places (O.translatedBlockFn A)).eq_sum_cosetIndicator t
      (fun _ _ _ hx' ↦ translatedBlockFn_const_of_congr hA hx')
  have hF_ne : (#F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 <| card_ne_zero.2 <|
    ne_empty_iff_nonempty.1 fun h_empty ↦
      one_ne_zero (hz_one.symm.trans (by simp [congrFun h_sum_eq z, h_empty]))
  let base : n × r → 𝔸f E :=
    matrixToVec (inclMatrix (𝔸f E) O.incl * ((A⁻¹ : Gf E r) : Matrix r r (𝔸f E)))
  have h_total : (#F : ℂ) * descentPairing u P g (cosetIndicator O.places t base) y = 0 := by
    calc (#F : ℂ) * descentPairing u P g (cosetIndicator O.places t base) y
        = ∑ q ∈ F, O.translatedBlockFn A q *
            descentPairing u P g (cosetIndicator O.places t q) y := by
          rw [← nsmul_eq_mul, ← sum_eq_card_nsmul fun q hq ↦
            translatedBlockFn_mul_descentPairing_cosetIndicator u P g t A (hF q hq) y]
      _ = descentPairing u P g (O.translatedBlockFn A) y := by
          conv_rhs => rw [h_sum_eq]
          simp [map_sum, LinearMap.sum_apply]
      _ = 0 := descentPairing_translatedBlockFn_eq_zero u P g h_datum hA.supportedOn
  simpa [hz_one] using
    (translatedBlockFn_mul_descentPairing_cosetIndicator u P g t A (hz_one.trans_ne one_ne_zero)
      y).trans ((mul_eq_zero.1 h_total).resolve_left hF_ne)

variable [DecidableEq O.ChosenIndex]

omit [WeilData E] in
/-- Let `l` be an integral row at `w = O.placeAt j` that annihilates `z` modulo `t`
(`IsAnnihilatingRowMod`). For any invertible `s = 1 + v λ` in `hyperplaneGroup (res ∘ l ∘ O.incl)`,
there is an element `h` of `stdLevel E n` that shifts `z` by an integral multiple of `t` at
`O.places` and acts on `y` as `O.blockAction (Pi.mulSingle j s) y`. -/
lemma exists_leftMul_sub_mem_and_blockAction_eq [DecidableEq O.TwistIndex] {t : (𝔸f E)ˣ}
    {z : n × r → 𝔸f E} {j : O.ChosenIndex ⊕ O.TwistIndex} {l : n → LocInt (O.placeAt j)}
    (hl : O.IsAnnihilatingRowMod t z j l) {s : GL r (ResField (O.placeAt j))}
    (hs : s ∈ hyperplaneGroup fun b : r ↦ residue (LocInt (O.placeAt j)) (l (O.incl b)))
    (y : O.FormV) :
    ∃ h : stdLevel E n, t⁻¹.val • (leftMul E r n h z - z) ∈ integralBox (n × r) O.places ∧
      (O.blockAction (Pi.mulSingle j s) y).val = algFormRep O.columnCount O.detExp h y.val := by
  -- Lift the column `v`, and let `h` be the matrix `rowShear O.incl v l` at `w` and `1` at the
  -- other places of `O`.
  let res : LocInt (O.placeAt j) →+* ResField (O.placeAt j) := residue _
  obtain ⟨v₀, hs⟩ : ∃ v₀, s.val = 1 + vecMulVec v₀ ((res ∘ l) ∘ O.incl) := hs
  obtain ⟨v, rfl⟩ : ∃ v, res ∘ v = v₀ := residue_surjective.comp_left _
  have h_det : res (rowShear O.incl v l).det = s.val.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_rowShear, det_rowShear, hs]
  have h_unit : IsUnit (rowShear O.incl v l).det :=
    (isUnit_map_iff (residue _) _).1 (h_det.trans_ne s.det_ne_zero).isUnit
  let τ : ∀ i, GL n (LocInt (O.placeAt i)) := Pi.mulSingle j (.mk'' (rowShear O.incl v l) h_unit)
  obtain ⟨h, h_at⟩ := exists_stdLevel_atPlace_eq τ
  have h_red_self : (stdLevel.reduceAt (O.placeAt j) h).val =
      rowShear O.incl (res ∘ v) (res ∘ l) := by
    simp only [reduceAt_eq_of_atPlace (h_at j), τ, Pi.mulSingle_eq_same]
    exact map_rowShear O.incl res v l
  have h_red_ne {i : O.ChosenIndex ⊕ O.TwistIndex} (hi : i ≠ j) :
      stdLevel.reduceAt (O.placeAt i) h = 1 := by simp [reduceAt_eq_of_atPlace (h_at i), τ, hi]
  refine ⟨h, mem_integralBox.2 fun ⟨a, b⟩ ↦ idem_mul_mem_Ô.2 <| Set.forall_mem_range.2 fun i ↦ ?_,
    smul_chosenGLRep_eq_apply_of_triangular y h (Pi.mulSingle j s) (fun i ↦ ?_) fun i ↦ ?_⟩
  · -- The row `l` annihilates `z` modulo `t` at `w`, so the shear moves `z` by a multiple of `t`.
    change t⁻¹.val (O.placeAt i) *
      (matrixAt (O.placeAt i) (leftMul E r n h z) a b - matrixAt (O.placeAt i) z a b) ∈
        LocInt (O.placeAt i)
    rw [matrixAt_leftMul, h_at]
    obtain rfl | hi := eq_or_ne i j
    · simp only [τ, Pi.mulSingle_eq_same]
      change t⁻¹.val (O.placeAt i) *
        (((rowShear O.incl v l).map (LocInt _).subtype * matrixAt (O.placeAt i) z) a b -
          matrixAt (O.placeAt i) z a b) ∈ LocInt (O.placeAt i)
      rw [map_rowShear, rowShear_mul, Matrix.add_apply, add_sub_cancel_left, vecMulVec_apply,
        mul_left_comm]
      have hv_int : (inclMatrix (LocField (O.placeAt i)) O.incl *ᵥ ((LocInt _).subtype ∘ v)) a ∈
          LocInt (O.placeAt i) := by
        obtain ⟨d, rfl⟩ | ha := Classical.em (a ∈ Set.range O.incl)
        · rw [inclMatrix_mulVec_apply_embedding]
          exact (v d).prop
        · rw [inclMatrix_mulVec_apply_of_notMem_range O.incl _ ha]
          exact zero_mem _
      exact mul_mem hv_int (hl.ann_mem b)
    · simp [τ, hi, zero_mem]
  · -- The reduction of the shear is block upper triangular with first block `s`.
    obtain rfl | hi := eq_or_ne (Sum.inl i) j
    · rw [h_red_self, Pi.mulSingle_eq_same, hs, rowShear_mul_inclMatrix]
    · simp only [h_red_ne hi, Pi.mulSingle_eq_of_ne hi, Units.val_one, Matrix.one_mul,
        Matrix.mul_one]
  · -- At a place of `Q` the entries of `l` outside `O.incl` reduce to `0`, so the reduction of the
    -- shear is block lower triangular.
    obtain rfl | hi := eq_or_ne (Sum.inr i) j
    · rw [h_red_self, Pi.mulSingle_eq_same, hs]
      exact transpose_rowShear_mul_inclMatrix _ _ (hl.residue_eq_zero Bool.false_ne_true)
    · simp only [h_red_ne hi, Pi.mulSingle_eq_of_ne hi, Units.val_one, transpose_one,
        Matrix.one_mul, Matrix.mul_one]

/-- **Cosets with an annihilating row.** If at some place `w = O.placeAt j` there is an integral
row `l` annihilating `z` modulo `t` (`IsAnnihilatingRowMod`), then
`B(cosetIndicator O.places t z, y) = 0`. -/
lemma descentPairing_eq_zero_of_annihilatingRow {y : O.FormV}
    (hQ : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    (h_sums : O.HyperplaneSumsAnnihilate y) {t : (𝔸f E)ˣ} {z : n × r → 𝔸f E}
    {j : O.ChosenIndex ⊕ O.TwistIndex} {l : n → LocInt (O.placeAt j)}
    (hl : O.IsAnnihilatingRowMod t z j l) :
    descentPairing u P g (cosetIndicator O.places t z) y = 0 := by
  classical
  let l₀ (b : r) : ResField (O.placeAt j) := residue _ (l (O.incl b))
  let B : O.FormV →ₗ⋆[ℂ] ℂ := descentPairing u P g (cosetIndicator O.places t z)
  -- For each `s = 1 + v λ` some element `h` of the maximal level preserves the `t`-coset of `z`
  -- and acts on `y` through `s`. So each term of the vanishing sum over `s` pairs as `y` does.
  have h_term (s : hyperplaneGroup l₀) : B (O.blockAction (Pi.mulSingle j s.val) y) = B y := by
    obtain ⟨h, h_sub, h_act⟩ := exists_leftMul_sub_mem_and_blockAction_eq hl s.prop y
    simpa only [cosetIndicator_leftMul_inv_of_sub_mem t h_sub] using
      descentPairing_translate u P g h (cosetIndicator O.places t z) h_act
  refine (smul_eq_zero_iff_right (Fintype.card_ne_zero (α := hyperplaneGroup l₀))).1 ?_
  calc Fintype.card (hyperplaneGroup l₀) • B y
      = ∑ s : hyperplaneGroup l₀, B (O.blockAction (Pi.mulSingle j s.val) y) := by simp [h_term]
    _ = 0 := by rw [← map_sum, sum_blockAction_eq_zero hQ h_sums j hl.residue_ne_zero, map_zero]

/-- **The bottom of the tower.** Let `O` be a descent pair: spaces `W = O.W` and `V = stdSpace E n`
of ranks `r` and `n`, two families of split places and residue characters `χ_w = O.tamePart w`. Let
`y` be a form on `V` and `u` a linear functional on its values. Assume that `χ_w` is nontrivial for
`w ∈ Q`, and that the hyperplane sums annihilate `y`: for rows `λ_w` at the chosen places, not all
zero, the product of the sums `∑ χ_w(det s)⁻¹ s` over the invertible `s = 1 + v λ_w`, with `v` any
column, kills `y`. Assume that the descents of the conjugate of the matrix coefficient
`algFormCoeff 1 u y` by the data `v_P ⊗ Ψ_bl ⊗ vac` vanish for all polynomials `P`. Then its
descents, for the character `O.charW` of `U(1)` attached to `W`, vanish for all data that are the
vacuum at the finite places other than the chosen places, the places of `Q` and their conjugates. -/
theorem descentsVanish_of_hyperplaneSumsAnnihilate {y : O.FormV}
    (hQ : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    (h_sums : O.HyperplaneSumsAnnihilate y)
    (h_datum : ∀ P : MvPolynomial (InfinitePlace E × n × r) ℂ, BlockDescentVanishes u P y) :
    DescentsVanish O.W (stdSpace E n) O.charW O.places.conjClosureᶜ
      (star (algFormCoeff 1 u y.val)) := by
  -- It suffices to treat the data `v_P ⊗ Ψ ⊗ vac`, and then the coset indicators modulo any `t`.
  refine .of_schrodingerOp isConjDisjoint_places (isAutomorphic_star_algFormCoeff u y)
    fun P Ψ hΨ ↦ funext fun g ↦ ?_
  change Ψ ∈ ((descentPairing u P g).flip y).ker
  refine hΨ.mem_of_cosets _ fun _ _ ↦ ⟨⊤, Filter.univ_mem, fun t z _ _ ↦ ?_⟩
  change descentPairing u P g (cosetIndicator O.places t z) y = 0
  rcases exists_annihilator_or_congr_at_places (O := O) t z with ⟨A, hA⟩ | ⟨j, l, hl⟩
  · exact descentPairing_eq_zero_of_congr u P g (h_datum P) hA
  · exact descentPairing_eq_zero_of_annihilatingRow u P g hQ h_sums hl

end DescentPair

end New

end
